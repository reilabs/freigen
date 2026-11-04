import Freigen.Ast.Cert

/-!
The lifting macro: `lift_program foo := src using [helpers…] ops [wrappers…]`
translates the source program `src` into an AST program `foo.ast`, together
with `foo.cert`, its program certificate against `src`.

The source is read as elaborated. The traversal handles the structural forms
directly: bind, return, `let`, and join points. Everything else is
dispatched through a table from source head symbol to stage 4 rule. An entry
is data: a source pattern, the rule and its tail-position variant, and the
rule's arguments as functions of the pattern variables. Applying an entry is
the same for every entry: match the pattern, bind operands that are not
variables first, instantiate the rule, and discharge its premises by emitting
holes and the continuation recursively.

Only the certificate is built. The AST is read off the certificate's
conclusion, where it appears specialized to the evaluator's instance, and
generalized back over the variable type.

First version: the identity handler; helpers and the entry point take one
argument. Listed operation wrappers are unfolded to raw operations.
-/

namespace Freigen.Ast.Macro

open Lean Meta Elab Command

/-! ## Rule instances -/

/-- A rule constant applied to metavariables for all its arguments. -/
structure RuleInst where
  name : Name
  term : Lean.Expr
  args : Array (Name × Lean.Expr × BinderInfo)
  concl : Lean.Expr

def RuleInst.new (c : Name) : MetaM RuleInst := do
  let ci ← getConstInfo c
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  let mut ty := ci.type.instantiateLevelParams ci.levelParams us
  let mut term := mkConst c us
  let mut args := #[]
  repeat
    let .forallE n d b bi := ty | break
    let m ← mkFreshExprMVar d
    args := args.push (n, m, bi)
    term := mkApp term m
    ty := b.instantiate1 m
  return { name := c, term, args, concl := ty }

def RuleInst.arg (r : RuleInst) (n : Name) : MetaM Lean.Expr := do
  let some (_, m, _) := r.args.find? (·.1 == n) |
    throwError "lift: rule `{r.name}` has no argument `{n}`"
  return m

/-- Set a named argument, checking its type. -/
def RuleInst.set (r : RuleInst) (n : Name) (v : Lean.Expr) : MetaM Unit := do
  let m ← r.arg n
  unless ← isDefEq m v do
    throwError "lift: argument `{n}` of `{r.name}`{indentExpr v}\nhas type{indentExpr (← inferType v)}\n\
      but is expected to have type{indentExpr (← instantiateMVars (← inferType m))}"

/-- Synthesize the instance arguments whose types are known. -/
def RuleInst.synthInstances (r : RuleInst) : MetaM Unit := do
  for (_, m, bi) in r.args do
    if bi.isInstImplicit && !(← m.mvarId!.isAssigned) then
      let ty ← instantiateMVars (← inferType m)
      unless ty.hasExprMVar do
        unless ← isDefEq m (← synthInstance ty) do
          throwError "lift: instance mismatch in `{r.name}`"

def RuleInst.finish (r : RuleInst) : MetaM Lean.Expr := do
  r.synthInstances
  let t ← instantiateMVars r.term
  if t.hasExprMVar then
    let missing ← r.args.filterMapM fun (n, m, _) => do
      return if (← instantiateMVars m).hasExprMVar then some n else none
    throwError "lift: could not determine the arguments {missing.toList} of `{r.name}`"
  return t

/-- Apply a rule to named arguments; the others are inferred. -/
def mkRule (c : Name) (args : List (Name × Lean.Expr)) : MetaM Lean.Expr := do
  let r ← RuleInst.new c
  for (n, v) in args do
    r.set n v
    r.synthInstances
  r.finish

/-! ## Types and shapes -/

partial def reflectTp (ty : Lean.Expr) : MetaM Lean.Expr := do
  let ty ← whnf ty
  match ty.getAppFn.constName?, ty.getAppArgs with
  | some ``UInt32, #[] => return mkConst ``Tp.uInt32
  | some ``Bool, #[] => return mkConst ``Tp.bool
  | some ``PUnit, #[] => return mkConst ``Tp.unit
  | some ``Prod, #[a, b] => return mkApp2 (mkConst ``Tp.prod) (← reflectTp a) (← reflectTp b)
  | some ``Array, #[a] => return mkApp (mkConst ``Tp.array) (← reflectTp a)
  | _, _ => throwError "lift: unsupported type{indentExpr ty}"

partial def reflectAbi (ty : Lean.Expr) : MetaM Lean.Expr := do
  let ty ← whnf ty
  match ty.getAppFn.constName?, ty.getAppArgs with
  | some ``UInt32, #[] => return mkConst ``AbiTp.uInt32
  | some ``Bool, #[] => return mkConst ``AbiTp.bool
  | some ``PUnit, #[] => return mkConst ``AbiTp.unit
  | some ``Prod, #[a, b] =>
    return mkApp2 (mkConst ``AbiTp.prod) (← reflectAbi a) (← reflectAbi b)
  | some ``Array, #[a] => return mkApp (mkConst ``AbiTp.array) (← reflectAbi a)
  | _, _ => throwError "lift: not an ABI type{indentExpr ty}"

def isObjType (ty : Lean.Expr) : MetaM Bool := do
  try discard <| reflectTp ty; return true catch _ => return false

/-- Split `Free E γ α`, unfolding abbreviations. -/
partial def asFree (ty : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Lean.Expr) := do
  let ty ← whnfCore ty
  if ty.isAppOfArity ``Free 5 then
    let as := ty.getAppArgs
    return (as[1]!, as[3]!, as[4]!)
  match ← unfoldDefinition? ty with
  | some ty => asFree ty
  | none => throwError "lift: expected a `Free` computation, got{indentExpr ty}"

def isFree (ty : Lean.Expr) : MetaM Bool := do
  try discard <| asFree ty; return true catch _ => return false

def isEmptyType (ty : Lean.Expr) : MetaM Bool := do
  let ty ← whnf ty
  return ty.isConstOf ``Empty || ty.isConstOf ``PEmpty

/-- `fun b => nomatch b` over an empty type `bt`, into `C b`. -/
def absurdLam (n : Name) (bt : Lean.Expr) (C : Lean.Expr → MetaM Lean.Expr) :
    MetaM Lean.Expr :=
  withLocalDeclD n bt fun b => do
    let elim := if (← whnf bt).isConstOf ``Empty then ``Empty.elim else ``PEmpty.elim
    mkLambdaFVars #[b] (← mkAppOptM elim #[← C b, b])

/-! ## The rule table -/

/-- A table entry: how a source construct maps to a stage 4 rule. -/
structure Entry where
  /-- A closed lambda over the pattern variables. Its body is matched against
  the source; its head symbol is the entry's key. -/
  pattern : Lean.Expr
  /-- Values (literals, builtins) are bound to a variable for the rest of the
  computation; computations are followed by a continuation, or are in tail
  position. -/
  isValue : Bool
  rule : Name
  tailRule : Option Name := none
  /-- Rule arguments as functions of the pattern variables, where a variable
  ranging over `Type` is passed as the corresponding object type. -/
  args : List (Name × Lean.Expr)
  tailArgs : List (Name × Lean.Expr) := args
  /-- Shown when the head symbol matches but the pattern does not. -/
  hint : Option String := none

def Entry.head (e : Entry) : MetaM Name := do
  lambdaTelescope e.pattern fun _ body => do
    let some n := body.getAppFn.constName? | throwError "lift: entry pattern without a head"
    return n

/-- The variables of an entry's argument functions: those ranging over `Type`
become object types, and types mentioning them become denotations. -/
def withArgVars (xs : Array Lean.Expr) (k : Array Lean.Expr → Array Lean.Expr → MetaM α) :
    MetaM α := do
  let rec go (i : Nat) (ys subst : Array Lean.Expr) : MetaM α := do
    if h : i < xs.size then
      let x := xs[i]
      let ty ← inferType x
      let n ← x.fvarId!.getUserName
      if ty.isType then
        withLocalDeclD n (mkConst ``Tp) fun s =>
          go (i + 1) (ys.push s) (subst.push (mkApp (mkConst ``Tp.denote) s))
      else
        withLocalDeclD n (ty.replaceFVars (xs.extract 0 i) subst) fun y =>
          go (i + 1) (ys.push y) (subst.push y)
    else k ys subst
  go 0 #[] #[]

/-- An argument function over the pattern variables `xs`, given its body in
terms of the new variables and the substitution for the old ones. -/
def argFn (xs : Array Lean.Expr) (f : Array Lean.Expr → Array Lean.Expr → MetaM Lean.Expr) :
    MetaM Lean.Expr :=
  withArgVars xs fun ys subst => do mkLambdaFVars ys (← f ys subst)

/-- A builtin: a source pattern, and the builtin as a function of the object
types of the pattern's type variables. Its operands are the pattern's other
variables, in order. -/
def builtinEntry (pat b : Lean.Expr) : MetaM Entry := do
  lambdaTelescope pat fun xs body => do
    let isTyVar ← xs.mapM fun x => return (← inferType x).isType
    let builtin (ys : Array Lean.Expr) : Lean.Expr :=
      (mkAppN b ((ys.zip isTyVar).filterMap fun (y, t) => if t then some y else none)).headBeta
    let bArg ← argFn xs fun ys _ => return builtin ys
    let argsArg ← argFn xs fun ys _ => do
      let bb := builtin ys
      let .app (.app _ inp) _ ← whnf (← inferType bb) |
        throwError "lift: not a builtin{indentExpr bb}"
      let some tps := inp.listLit? | throwError "lift: builtin inputs{indentExpr inp}"
      let vs := (ys.zip isTyVar).filterMap fun (y, t) => if t then none else some y
      let tpT := mkConst ``Tp
      let V := mkConst ``Tp.denote
      let mut h ← mkAppOptM ``HList.nil #[tpT, V]
      let mut rest ← mkAppOptM ``List.nil #[tpT]
      for (tp, v) in (tps.2.zip vs.toList).reverse do
        h ← mkAppOptM ``HList.cons #[tpT, V, tp, rest, v, h]
        rest ← mkAppOptM ``List.cons #[tpT, tp, rest]
      return h
    let rArg ← argFn xs fun _ subst => return body.replaceFVars xs subst
    return { pattern := pat, isValue := true, rule := ``ExprCert.builtin
             args := [(`b, bArg), (`args, argsArg), (`r, rArg)] }

/-- A literal of an ABI type. -/
def literalEntry (pat abi : Lean.Expr) : MetaM Entry := do
  lambdaTelescope pat fun xs body => do
    return { pattern := pat, isValue := true, rule := ``ExprCert.lit
             args := [(`tp, ← mkLambdaFVars xs abi), (`v, ← mkLambdaFVars xs body)] }

/-- The built-in entries for literals and builtins. -/
def staticEntries : Term.TermElabM (Array Entry) := do
  let elabE (stx : Term) : Term.TermElabM Lean.Expr := do
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasMVar then throwError "lift: ill-formed table entry{indentExpr e}"
    return e
  let lit (p a : Term) : Term.TermElabM Entry := do literalEntry (← elabE p) (← elabE a)
  let bi (p b : Term) : Term.TermElabM Entry := do builtinEntry (← elabE p) (← elabE b)
  return #[
    ← lit (← `(fun (n : Nat) => (OfNat.ofNat n : UInt32))) (← `(AbiTp.uInt32)),
    ← lit (← `(true)) (← `(AbiTp.bool)),
    ← lit (← `(false)) (← `(AbiTp.bool)),
    ← lit (← `(())) (← `(AbiTp.unit)),
    ← bi (← `(fun (a b : UInt32) => a + b)) (← `(Builtin.uAdd)),
    ← bi (← `(fun (a b : UInt32) => a - b)) (← `(Builtin.uSub)),
    ← bi (← `(fun (a b : UInt32) => a * b)) (← `(Builtin.uMul)),
    ← bi (← `(fun (a b : UInt32) => a / b)) (← `(Builtin.uDiv)),
    ← bi (← `(fun (a b : UInt32) => a % b)) (← `(Builtin.uMod)),
    ← bi (← `(fun (a b : UInt32) => a == b)) (← `(Builtin.uEq)),
    ← bi (← `(fun (a b : UInt32) => decide (a < b))) (← `(Builtin.uLt)),
    ← bi (← `(fun (a b : UInt32) => decide (a ≤ b))) (← `(Builtin.uLe)),
    ← bi (← `(fun (a : Bool) => !a)) (← `(Builtin.not)),
    ← bi (← `(fun (a b : Bool) => a && b)) (← `(Builtin.and)),
    ← bi (← `(fun (a b : Bool) => a || b)) (← `(Builtin.or)),
    ← bi (← `(fun (a b : Bool) => a == b)) (← `(Builtin.bEq)),
    ← bi (← `(fun {α β : Type} (a : α) (b : β) => (a, b)))
      (← `(fun (a b : Tp) => @Builtin.pair a b)),
    ← bi (← `(fun {α β : Type} (p : α × β) => p.1)) (← `(fun (a b : Tp) => @Builtin.fst a b)),
    ← bi (← `(fun {α β : Type} (p : α × β) => p.2)) (← `(fun (a b : Tp) => @Builtin.snd a b)),
    ← bi (← `(fun {α : Type} => (#[] : Array α))) (← `(fun (a : Tp) => @Builtin.arrEmpty a)),
    ← bi (← `(fun {α : Type} (xs : Array α) (x : α) => xs.push x))
      (← `(fun (a : Tp) => @Builtin.arrPush a)),
    ← bi (← `(fun {α : Type} (xs : Array α) => xs.size.toUInt32))
      (← `(fun (a : Tp) => @Builtin.arrLen a))]

/-- Raw operations of the signature `eff`. -/
def opEntry (eff : Lean.Expr) : MetaM Entry := do
  let tagIn (γ : Lean.Expr) := mkAppM ``EffSig.tag #[eff, γ]
  let inpOf (γ e : Lean.Expr) : MetaM Lean.Expr := do
    return mkApp (mkConst ``Tp.denote) (← mkAppM ``Subtype.val #[← mkAppM ``EffSig.input #[eff, γ, e]])
  withLocalDecl `γ .implicit (← mkAppM ``EffSig.Ctx #[eff]) fun γ => do
  withLocalDeclD `e (← tagIn γ) fun e => do
  withLocalDeclD `inp (← inpOf γ e) fun inp => do
  let fam ← withLocalDeclD `e (← tagIn γ) fun e' => do mkLambdaFVars #[e'] (← inpOf γ e')
  let sig ← mkAppOptM ``Sigma.mk #[← tagIn γ, fam, e, inp]
  let opFn ← mkAppOptM ``Free.op #[none, mkApp (mkConst ``EffSig.denote) eff, none, γ, sig]
  let .forallE _ sbTy _ _ ← whnfR (← inferType opFn) | throwError "lift: unexpected operation type"
  withLocalDeclD `sb sbTy fun sb => do
  let xs := #[γ, e, inp, sb]
  let arg (i : Nat) := argFn xs fun ys _ => return ys[i]!
  return { pattern := ← mkLambdaFVars xs (mkApp opFn sb), isValue := false
           rule := ``ExprCert.op, tailRule := ``ExprCert.op_tail
           args := [(`e, ← arg 1), (`inp, ← arg 2), (`sb, ← arg 3)] }

/-- Branches on a boolean, in the signature `eff`. -/
def iteEntry (eff : Lean.Expr) : MetaM Entry := do
  withLocalDecl `γ .implicit (← mkAppM ``EffSig.Ctx #[eff]) fun γ => do
  withLocalDecl `σ .implicit (mkSort Level.one) fun σ => do
  withLocalDeclD `c (mkConst ``Bool) fun c => do
  let fr ← mkAppOptM ``Free #[none, mkApp (mkConst ``EffSig.denote) eff, none, γ, σ]
  withLocalDeclD `t fr fun t => do
  withLocalDeclD `e fr fun e => do
  let xs := #[γ, σ, c, t, e]
  let body ← mkAppOptM ``ite #[fr, ← mkEq c (mkConst ``Bool.true), none, t, e]
  let arg (i : Nat) := argFn xs fun ys _ => return ys[i]!
  let common := [(`c, ← arg 2), (`st, ← arg 3), (`se, ← arg 4)]
  return { pattern := ← mkLambdaFVars xs body, isValue := false
           rule := ``ExprCert.ite, tailRule := ``ExprCert.ite_tail
           args := (`out, ← arg 1) :: common, tailArgs := common
           hint := "conditions must be booleans: write `decide (x < y)` rather than `x < y`" }

/-- Calls to a function in scope: a helper definition or a join point. -/
def callEntry (key inp out : Lean.Expr) : MetaM Entry := do
  let .forallE n τ _ _ ← whnfR (← inferType key) | throwError "lift: not a function{indentExpr key}"
  withLocalDeclD n τ fun x => do
    let xs := #[x]
    let const (v : Lean.Expr) := argFn xs fun _ _ => return v
    let common := [(`inp, ← const inp), (`src, ← const key), (`x, ← argFn xs fun ys _ => return ys[0]!)]
    return { pattern := ← mkLambdaFVars xs (mkApp key x), isValue := false
             rule := ``ExprCert.app, tailRule := ``ExprCert.app_tail
             args := (`out, ← const out) :: common, tailArgs := common }

/-! ## Traversal state -/

/-- A function in scope, with its function certificate at the current heap. -/
structure FnInfo where
  src : Lean.Expr
  cert : Lean.Expr
  inp : Lean.Expr
  out : Lean.Expr

structure Ctx where
  eff : Lean.Expr
  F : Lean.Expr
  handler : Lean.Expr
  heap : Lean.Expr
  /-- Source variables standing for AST variables. -/
  atoms : Array Lean.Expr := #[]
  fns : Array FnInfo := #[]
  /-- Entries, by head symbol. -/
  table : Std.HashMap Name (Array Entry)
  /-- Operation wrappers, unfolded to raw operations. -/
  wrappers : Array Name
  /-- Definitions matching may unfold besides reducible ones and instances: the
  signature and the handler, with their auxiliary definitions. -/
  unfoldable : Array Name

abbrev M := ReaderT Ctx MetaM

/-- Unification for matching the source. It may unfold the signature, the
handler, reducible definitions, instances and structure projections, together
with their auxiliary definitions (such as compiled pattern matches), but
never user definitions. -/
def matchDefEq (a b : Lean.Expr) : M Bool := do
  let allowed := (← read).unfoldable
  let ok (n : Name) : CoreM Bool := do
    let mut n := n
    while !n.isAnonymous do
      let env ← getEnv
      if allowed.contains n || isInstanceCore env n || env.isProjectionFn n then return true
      if (← getReducibilityStatus n) == .reducible then return true
      n := n.getPrefix
    return false
  withCanUnfoldPred (fun _ ci => ok ci.name) (isDefEq a b)

def isAtom (x : Lean.Expr) : M Bool := return (← read).atoms.contains x.consumeMData

def withAtom (x : Lean.Expr) (k : M α) : M α :=
  withReader (fun c => { c with atoms := c.atoms.push x }) k

/-- Move to a larger heap: every function certificate is moved along. -/
def withHeap (h' hle : Lean.Expr) (k : M α) : M α := do
  let fns ← (← read).fns.mapM fun i => do
    let cert ← mkRule ``FnCert.mono [(`hf, i.cert), (`h', h'), (`hle, hle)]
    return { i with cert }
  withReader (fun c => { c with heap := h', fns }) k

def entriesFor (f : Lean.Expr) : M (Array Entry) := do
  let c ← read
  let calls ← c.fns.filterMapM fun i => do
    if i.src == f then return some (← callEntry i.src i.inp i.out) else return none
  let static := match f.constName? with
    | some n => c.table.getD n #[]
    | none => #[]
  return calls ++ static

/-- Set the arguments every certificate rule shares: the context, and the
result type when the rule states it. -/
def setBase (r : RuleInst) (γ o : Lean.Expr) : M Unit := do
  let c ← read
  r.set `eff c.eff
  r.set `F c.F
  r.synthInstances
  r.set `handler c.handler
  r.set `h c.heap
  r.set `γ γ
  if r.args.any (·.1 == `o) then r.set `o o

/-- Fix the context and result type of a rule's conclusion. -/
def concludeIn (r : RuleInst) (γ o : Lean.Expr) : MetaM Unit := do
  let as := r.concl.getAppArgs
  unless (← isDefEq as[4]! γ) && (← isDefEq as[5]! o) do
    throwError "lift: `{r.name}` concludes in the wrong context or result type"

def unsupported (what : String) (e : Lean.Expr) : MetaM α :=
  throwError "lift: unsupported {what}{indentExpr e}"

/-- Report a head symbol whose entries do not match. -/
def noMatch (entries : Array Entry) (x : Lean.Expr) : MetaM Unit := do
  unless entries.isEmpty do
    let hints := entries.filterMap (·.hint)
    let hint := if hints.isEmpty then "" else s!"; {hints[0]!}"
    throwError "lift: no rule matches this form{hint}{indentExpr x}"

/-- The binder name the source gives a continuation's argument, if any. -/
def sourceBinder (body : Lean.Expr) : Option Name :=
  match body.getAppArgs.back? with
  | some (.app (.lam n ..) (.bvar 0)) => some n
  | _ => none

/-! ## Emission -/

mutual

/-- Certify the computation `s` in context `γ`, returning object type `o`. -/
partial def trComp (s γ o : Lean.Expr) : M Lean.Expr := do
  let s := (← instantiateMVars s).consumeMData.headBeta
  if let .letE n ty v b _ := s then
    if v.isLambda && (← isFree (← inferType (← etaExpand v)).getForallBody) then
      return ← trJoin n ty v b s γ o
    if ← isAtom v then
      return ← trComp (b.instantiate1 v) γ o
    return ← bindValue v (b.instantiate1 ·) γ o
  let f := s.getAppFn
  let as := s.getAppArgs
  if f.isConstOf ``Pure.pure && as.size == 4 then
    let v := as[3]!
    unless ← isAtom v do return ← bindValue v (mkAppN f <| as.set! 3 ·) γ o
    let r ← RuleInst.new ``ExprCert.ret
    setBase r γ o
    r.set `v v
    concludeIn r γ o
    return ← r.finish
  if f.isConstOf ``Bind.bind && as.size == 6 then
    let x := as[4]!.consumeMData.headBeta
    -- Monadic padding: binding a return is definitionally its continuation.
    if x.isAppOfArity ``Pure.pure 4 then
      return ← trComp (mkApp as[5]! x.appArg!) γ o
    return ← trHead x (some as[5]!) (mkAppN f <| as.set! 4 ·) γ o
  trHead s none id γ o

/-- Certify the computation `x`, followed by `cont` if present. `rebuild`
puts a replacement for `x` back into the whole source. -/
partial def trHead (x : Lean.Expr) (cont : Option Lean.Expr) (rebuild : Lean.Expr → Lean.Expr)
    (γ o : Lean.Expr) : M Lean.Expr := do
  let x := x.consumeMData.headBeta
  let f := x.getAppFn
  if (← read).wrappers.any f.isConstOf then
    let some x' ← unfoldDefinition? x | unsupported "operation wrapper" x
    return ← trHead x' cont rebuild γ o
  let entries := (← entriesFor f).filter (!·.isValue)
  for e in entries do
    if let some p ← applyEntry e x rebuild cont γ o then return p
  noMatch entries x
  if let some c := f.constName? then
    if ← isMatcher c then
      throwError "lift: pattern matching (including destructuring) is not supported{indentExpr x}"
    throwError "lift: call to `{c}`, which is neither a listed helper nor an operation{indentExpr x}"
  unsupported "construct" x

/-- Bind the value `v` to a variable, then continue with `rebuild` applied to
it. -/
partial def bindValue (v : Lean.Expr) (rebuild : Lean.Expr → Lean.Expr) (γ o : Lean.Expr) :
    M Lean.Expr := do
  let v := v.consumeMData
  let entries := (← entriesFor v.getAppFn).filter (·.isValue)
  for e in entries do
    if let some p ← applyEntry e v rebuild none γ o then return p
  noMatch entries v
  unsupported "value" v

/-- Apply a table entry to the source term `x`, or fail to match. -/
partial def applyEntry (e : Entry) (x : Lean.Expr) (rebuild : Lean.Expr → Lean.Expr)
    (cont : Option Lean.Expr) (γ o : Lean.Expr) : M (Option Lean.Expr) := do
  let (ms, _, body) ← lambdaMetaTelescope e.pattern
  unless ← matchDefEq body x do return none
  let vals ← ms.mapM instantiateMVars
  -- Operands that are not variables are bound first, one at a time.
  for i in [:vals.size] do
    let ty ← instantiateMVars (← inferType ms[i]!)
    if (← isObjType ty) && !(← isAtom vals[i]!) then
      let swap (y : Lean.Expr) := rebuild (e.pattern.beta (vals.set! i y))
      return some (← bindValue vals[i]! swap γ o)
  let (rule, args) ← match e.isValue, cont with
    | false, none =>
      let some r := e.tailRule | throwError "lift: `{e.rule}` has no tail-position variant"
      pure (r, e.tailArgs)
    | _, _ => pure (e.rule, e.args)
  let r ← RuleInst.new rule
  setBase r γ o
  let argVals ← vals.mapM fun v => do
    if (← inferType v).isType then reflectTp v else pure v
  for (n, f) in args do
    r.set n (f.beta argVals)
    r.synthInstances
  concludeIn r γ o
  if e.isValue then
    let tk ← withLocalDeclD `x (← inferType x) fun y => do mkLambdaFVars #[y] (rebuild y)
    r.set `tk tk
  -- The conclusion's source must be the source.
  let .app _ src := r.concl | unreachable!
  unless ← matchDefEq src (rebuild x) do
    throwError "lift: `{rule}` does not match the source{indentExpr (rebuild x)}"
  discharge r
  return some (← r.finish)

/-- Discharge the explicit premises of a rule instance. -/
partial def discharge (r : RuleInst) : M Unit := do
  for (n, m, bi) in r.args do
    if !bi.isExplicit || (← m.mvarId!.isAssigned) then continue
    let ty ← instantiateMVars (← inferType m)
    let p ← premise ty
    unless ← isDefEq m p do
      throwError "lift: premise `{n}` of `{r.name}` has type{indentExpr ty}\n\
        but its proof has type{indentExpr (← inferType p)}"
  -- AST holes over empty types: blocks of operations that have none.
  for (_, m, bi) in r.args do
    if bi.isInstImplicit || (← m.mvarId!.isAssigned) then continue
    let ty ← instantiateMVars (← inferType m)
    if let .forallE n d body _ := ty then
      if ← isEmptyType d then
        unless ← isDefEq m (← absurdLam n d fun b => return body.instantiate1 b) do
          throwError "lift: cannot fill an empty hole of `{r.name}`"

/-- Prove a premise: an expression certificate for a hole or continuation,
under binders; a function certificate in scope; or a builtin's result. -/
partial def premise (ty : Lean.Expr) : M Lean.Expr := do
  match ty with
  | .forallE n d b _ =>
    if ← isEmptyType d then
      return ← absurdLam n d fun x => return b.instantiate1 x
    let n := (sourceBinder b).getD n
    withLocalDeclD n d fun x => do
      let p ← (if d.isAppOf ``Tp.denote then withAtom x else id) (premise (b.instantiate1 x))
      mkLambdaFVars #[x] p
  | _ =>
    if ty.isAppOfArity ``ExprCert 9 then
      let as := ty.getAppArgs
      return ← trComp as[8]! as[4]! as[5]!
    if ty.isAppOfArity ``FnCert 10 then
      let src := ty.appArg!
      let some i := (← read).fns.find? (·.src == src) |
        throwError "lift: no function certificate for{indentExpr src}"
      return i.cert
    if ty.isAppOfArity ``Eq 3 then
      return ← mkEqRefl ty.appFn!.appArg!
    throwError "lift: cannot discharge the premise{indentExpr ty}"

/-- A join point `let jp := fun y => body; rest`: a local closure. -/
partial def trJoin (n : Name) (ty v b s γ o : Lean.Expr) : M Lean.Expr := do
  let ctx ← read
  let .lam _ yTy yBody _ := v | unsupported "join point" v
  if yBody.isLambda then
    throwError "lift: join points with several arguments are not supported; they come \
      from mutable variables{indentExpr v}"
  let inp ← reflectTp yTy
  let σ ← withLocalDeclD `y yTy fun y => do
    let (_, _, σ) ← asFree (← inferType (yBody.instantiate1 y))
    return σ
  let out ← reflectTp σ
  let fnTp := mkApp2 (mkConst ``Tp.fn) inp out
  let r ← RuleInst.new ``ExprCert.lam
  setBase r γ o
  r.set `inp inp
  r.set `out out
  r.set `src v
  concludeIn r γ o
  r.set `t s
  r.set `hb (← premise (← instantiateMVars (← inferType (← r.arg `hb))))
  -- The rest is certified with the join point as a plain local, substituted
  -- by a single beta-redex, so its definition is never duplicated.
  let hk ← withLocalDeclD n ty fun jS =>
    withLocalDeclD `h' (mkApp (mkConst ``Heap) ctx.eff) fun h' =>
    withLocalDeclD n (mkApp (mkConst ``Tp.denote) fnTp) fun ref => do
    withLocalDeclD `hle (← mkAppM ``LE.le #[ctx.heap, h']) fun hle => do
    let certTy ← mkAppOptM ``FnCert #[ctx.eff, ctx.F, none, ctx.handler, γ, inp, out, h', ref, jS]
    withLocalDeclD `hjp certTy fun hc => do
      let p ← withHeap h' hle <|
        withReader (fun c => { c with fns := c.fns.push { src := jS, cert := hc, inp, out } })
          (trComp (b.instantiate1 jS) γ o)
      return mkApp (← mkLambdaFVars #[jS] (← mkLambdaFVars #[h', ref, hle, hc] p)) v
  r.set `hk hk
  r.finish

end

/-! ## Programs -/

/-- A source definition `c : τ → Free E γ σ`. -/
def sourceFn (c : Name) : MetaM (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := do
  let ci ← getConstInfo c
  let .forallE _ τ body _ ← whnfR ci.type |
    throwError "lift: `{c}` must take exactly one argument"
  let (_, γ, σ) ← asFree body
  let some val := ci.value? | throwError "lift: `{c}` has no definition"
  return (τ, γ, σ, val)

def binderName (f : Lean.Expr) : Name :=
  if let .lam n .. := f then n else `x

structure ProgCtx where
  entry : Name
  γ : Lean.Expr
  iT : Lean.Expr
  oT : Lean.Expr

def setProgBase (r : RuleInst) (p : ProgCtx) : M Unit := do
  let c ← read
  r.set `eff c.eff
  r.set `F c.F
  r.synthInstances
  r.set `handler c.handler
  r.set `γ p.γ
  r.set `h c.heap
  r.set `iT p.iT
  r.set `oT p.oT
  r.set `t (mkConst p.entry)

/-- Certify a body premise `∀ x, ExprCert h (body x) (c x)` by unfolding `c`
once. -/
def trBody (val ty : Lean.Expr) : M Lean.Expr := do
  let .forallE _ d b _ := ty | throwError "lift: unexpected body premise{indentExpr ty}"
  withLocalDeclD (binderName val) d fun x => withAtom x do
    let as := (b.instantiate1 x).getAppArgs
    mkLambdaFVars #[x] (← trComp (mkApp val x) as[4]! as[5]!)

partial def trProgram (p : ProgCtx) : List Name → M Lean.Expr
  | [] => do
    let r ← RuleInst.new ``ProgCert.main
    setProgBase r p
    let (_, _, _, val) ← sourceFn p.entry
    r.set `hb (← trBody val (← instantiateMVars (← inferType (← r.arg `hb))))
    r.finish
  | c :: cs => do
    let ctx ← read
    let (τ, γ', σ, val) ← sourceFn c
    let inp ← reflectTp τ
    let out ← reflectTp σ
    let fnTp := mkApp2 (mkConst ``Tp.fn) inp out
    let r ← RuleInst.new ``ProgCert.define
    setProgBase r p
    r.set `γ' γ'
    r.set `inp inp
    r.set `out out
    r.set `src (mkConst c)
    let .forallE _ selfTy b _ ← instantiateMVars (← inferType (← r.arg `hb)) | unreachable!
    r.set `hb (← withLocalDeclD `self selfTy fun self => do
      mkLambdaFVars #[self] (← trBody val (b.instantiate1 self)))
    let hk ←
      withLocalDeclD `h' (mkApp (mkConst ``Heap) ctx.eff) fun h' =>
      withLocalDeclD (.mkSimple c.lastComponentAsString) (mkApp (mkConst ``Tp.denote) fnTp) fun ref => do
      withLocalDeclD `hle (← mkAppM ``LE.le #[ctx.heap, h']) fun hle => do
      let certTy ← mkAppOptM ``FnCert #[ctx.eff, ctx.F, none, ctx.handler, γ', inp, out, h', ref,
        mkConst c]
      withLocalDeclD `hc certTy fun hc => do
        let rest ← withHeap h' hle <|
          withReader (fun x => { x with fns := x.fns.push { src := mkConst c, cert := hc, inp, out } })
            (trProgram p cs)
        mkLambdaFVars #[h', ref, hle, hc] rest
    r.set `hk hk
    r.finish

/-- Lift `entry`, with the given helpers in dependency order and operation
wrappers, adding `name.ast` and `name.cert`. -/
def liftProgram (name entry : Name) (helpers wrappers : Array Name) : Term.TermElabM Unit := do
  let (τ, γ, σ, _) ← sourceFn entry
  let .forallE _ _ body _ ← whnfR (← getConstInfo entry).type | unreachable!
  let (E, _, _) ← asFree body
  unless E.isAppOfArity ``EffSig.denote 1 do
    throwError "lift: the source must be over an AST signature, got{indentExpr E}"
  let eff := E.appArg!
  let p : ProgCtx := { entry, γ, iT := ← reflectAbi τ, oT := ← reflectAbi σ }
  let entries := (← staticEntries) ++ #[← opEntry eff, ← iteEntry eff]
  let mut table : Std.HashMap Name (Array Entry) := {}
  for e in entries do
    let n ← e.head
    table := table.insert n ((table.getD n #[]).push e)
  let handler := mkApp (mkConst ``idHandler) eff
  let unfoldable := #[``idHandler] ++ eff.getAppFn.constName?.toArray
  let ctx : Ctx :=
    { eff, F := E, handler, heap := mkApp (mkConst ``Heap.empty) eff, table, wrappers, unfoldable }
  let prf ← instantiateMVars (← (trProgram p helpers.toList).run ctx)
  -- The AST, read off the certificate and generalized over the variable type.
  let .app (.app _ astSpec) _ ← instantiateMVars (← inferType prf) | unreachable!
  let (astVal, astTy) ←
    withLocalDecl `V .implicit (← mkArrow (mkConst ``Tp) (mkSort Level.one)) fun V => do
      let ast := astSpec.replace fun e => if e.isConstOf ``Tp.denote then some V else none
      let ty ← mkAppOptM ``Program #[eff, γ, p.iT, p.oT, V]
      return (← mkLambdaFVars #[V] ast, ← mkForallFVars #[V] ty)
  unless (← isTypeCorrect astVal) && (← isDefEq (← inferType astVal) astTy) do
    throwError "lift: internal error, the generated AST does not type-check{indentExpr astVal}"
  let astName := name ++ `ast
  addDecl <| .defnDecl
    { name := astName, levelParams := [], type := astTy, value := astVal
      hints := .regular 0, safety := .safe }
  let thm ← mkRule ``ProgramCert.of_progCert [(`eff, eff), (`F, E), (`handler, handler),
    (`γ, γ), (`iT, p.iT), (`oT, p.oT), (`p, mkConst astName), (`t, mkConst entry), (`hp, prf)]
  let thmTy ← instantiateMVars (← inferType thm)
  try
    addDecl <| .thmDecl { name := name ++ `cert, levelParams := [], type := thmTy, value := thm }
  catch ex =>
    throwError "lift: internal error, the generated certificate does not check:\n{ex.toMessageData}"

syntax liftUsing := " using " "[" ident,* "]"
syntax liftOps := &" ops " "[" ident,* "]"

/-- `lift_program foo := src using [helpers…] ops [wrappers…]` lifts `src` to an
AST program `foo.ast`, with `foo.cert : ProgramCert (idHandler _) foo.ast src`.
Helpers are listed callees first; both lists are optional. -/
syntax (name := liftProgramCmd) "lift_program " ident " := " ident (liftUsing)? (liftOps)? : command

def identsOf (stx : Option Syntax) : Term.TermElabM (Array Name) := do
  let some stx := stx | return #[]
  stx[2].getSepArgs.mapM fun i => realizeGlobalConstNoOverloadWithInfo i

elab_rules : command
  | `(lift_program $n := $e $[$u]? $[$o]?) => do
    let ns ← getCurrNamespace
    liftTermElabM do
      let entry ← realizeGlobalConstNoOverloadWithInfo e
      liftProgram (ns ++ n.getId) entry (← identsOf (u.map (·.raw))) (← identsOf (o.map (·.raw)))

end Freigen.Ast.Macro
