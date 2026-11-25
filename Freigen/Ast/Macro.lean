import Freigen.Ast.Loop

/-!
The lifting macro: `lift_program foo := src using [helpers…] ops [wrappers…]`
translates the source program `src` into an AST program `foo.ast`, together
with `foo.cert`, its program certificate against `src`.

The source is read as elaborated. The traversal handles the structural forms
directly: bind, return, `let`, and join points. Everything else is
dispatched through a table from source head symbol to certificate rule. An entry
is data: a source pattern, the rule and its tail-position variant, and the
rule's arguments as functions of the pattern variables. Applying an entry is
the same for every entry: match the pattern, bind operands that are not
variables first, instantiate the rule, and discharge its premises by emitting
holes and the continuation recursively.

Only the certificate is built. The AST is read off the certificate's
conclusion, where it appears specialized to the evaluator's instance, and
generalized back over the variable type.

Without a lift, sources are over a language's own operations and lifted with
the identity lift; listed operation wrappers are unfolded to raw operations.
With a lift (`via ℓ`, for `ℓ : … → Lift L M`), sources are over the lift's
source operations and may take its parameters; the certificate is stated for
all of them. Rules for the source's operations and primitives, and the
language's base types, are registered with `@[lift_rule ℓ]` and
`@[lift_base ℓ]`. A rule's
source pattern is read off its conclusion: `src >>= tk` for an operation
followed by code, `src` alone in tail position, `tk v` for a value `v`.
Helpers and the entry point take one argument.

Source values of object types are AST values. Values of other types
(proofs of `Prop`s, values paired with proofs) are represented by their
erasure: a source type is reflected into the lift's representation of it
(`Lift.Rep`, indexed by the AST type and the source type), and the erasure
at the representation relates the two. The certificate states the
representation of the entry point's result. Source variables of such types
have no AST variable of their own: their representative is their erasure (an
atom, a
value bound first, or a premise's AST value), and a projection that equals
it (`w.val`) is replaced by it throughout the source.

Values are bound by `let`, so the source's proofs about them (a bounds
check's outcome) stay valid.
-/

namespace Freigen.Ast.Macro

open Lean Meta Elab Command

/-! ## Registration -/

/-- What a declaration registered for a language is. -/
inductive RegKind
/-- A certificate rule. -/
| rule
/-- A base type, possibly with parameters. -/
| base
deriving BEq, Inhabited

structure Registered where
  lift : Name
  decl : Name
  kind : RegKind
  deriving Inhabited

initialize registeredExt : SimplePersistentEnvExtension Registered (Array Registered) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[] }

/-- The declarations of a kind registered for `lift`. -/
def registered (lift : Name) (kind : RegKind) : CoreM (Array Name) := do
  return (registeredExt.getState (← getEnv)).filterMap fun r =>
    if r.lift == lift && r.kind == kind then some r.decl else none

/-- `@[lift_rule ℓ]`: a certificate rule the macro applies when lifting by
`ℓ`. -/
syntax (name := lift_rule) "lift_rule " ident : attr
/-- `@[lift_base ℓ]`: a base type of the language `ℓ` lifts into, possibly with
parameters; source types are reflected into it by unification. -/
syntax (name := lift_base) "lift_base " ident : attr


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

/-! ## The language -/

/-- The language a program is lifted into, its model, and the lift. -/
structure Lang where
  L : Lean.Expr
  model : Lean.Expr
  /-- Registered base types: constants of the language's `Base`, or functions
  into it. -/
  bases : Array Name := #[]
  /-- The lift: how source values and operations are represented. -/
  lift : Lean.Expr

def Lang.base (l : Lang) : Lean.Expr := mkApp (mkConst ``Language.Base) l.L
def Lang.abi (l : Lang) : Lean.Expr := mkApp (mkConst ``Language.abi) l.L
def Lang.tp (l : Lang) : Lean.Expr := mkApp (mkConst ``Language.Tp) l.L
/-- The values of an object type in the model. -/
def Lang.val (l : Lang) (tp : Lean.Expr) : Lean.Expr :=
  mkApp3 (mkConst ``Language.Model.V) l.L l.model tp
def Lang.tpC (l : Lang) (c : Name) : Lean.Expr := mkApp (mkConst c) l.base
def Lang.abiC (l : Lang) (c : Name) : Lean.Expr := mkApp2 (mkConst c) l.base l.abi

/-- Whether `ty` is the type of values of some object type: a variable of it
stands for an AST variable. -/
def isValType (ty : Lean.Expr) : Bool :=
  ty.isAppOf ``Language.Model.V || ty.isAppOf ``Tp.denote

/-! ## Types and shapes -/

/-- Reflect `ty` into a base type of the language, by unifying it with the
values of each registered base type. -/
def reflectBase (l : Lang) (ty : Lean.Expr) : MetaM (Option Lean.Expr) := do
  for b in l.bases do
    let c ← mkConstWithFreshMVarLevels b
    let (args, _, _) ← forallMetaTelescopeReducing (← inferType c)
    let bv := mkAppN c args
    if ← isDefEq (l.val (mkApp (l.tpC ``Tp.base) bv)) ty then
      let bv ← instantiateMVars bv
      unless bv.hasExprMVar do return some bv
  return none

partial def reflectTp (l : Lang) (ty : Lean.Expr) : MetaM Lean.Expr := do
  if let some b ← reflectBase l ty then return mkApp (l.tpC ``Tp.base) b
  let ty ← whnf ty
  match ty.getAppFn.constName?, ty.getAppArgs with
  | some ``UInt32, #[] => return l.tpC ``Tp.uInt32
  | some ``Bool, #[] => return l.tpC ``Tp.bool
  | some ``PUnit, #[] => return l.tpC ``Tp.unit
  | some ``Prod, #[a, b] =>
    return mkApp2 (l.tpC ``Tp.prod) (← reflectTp l a) (← reflectTp l b)
  | some ``Array, #[a] => return mkApp (l.tpC ``Tp.array) (← reflectTp l a)
  | some ``Vector, #[a, n] => return mkApp2 (l.tpC ``Tp.vec) n (← reflectTp l a)
  | _, _ => throwError "lift: unsupported type{indentExpr ty}"

partial def reflectAbi (l : Lang) (ty : Lean.Expr) : MetaM Lean.Expr := do
  if let some b ← reflectBase l ty then
    unless ← isDefEq (mkApp l.abi b) (mkConst ``Bool.true) do
      throwError "lift: not an ABI type{indentExpr ty}"
    let h := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)
    return mkApp4 (mkConst ``AbiTp.base) l.base l.abi b h
  let ty ← whnf ty
  match ty.getAppFn.constName?, ty.getAppArgs with
  | some ``UInt32, #[] => return l.abiC ``AbiTp.uInt32
  | some ``Bool, #[] => return l.abiC ``AbiTp.bool
  | some ``PUnit, #[] => return l.abiC ``AbiTp.unit
  | some ``Prod, #[a, b] =>
    return mkApp2 (l.abiC ``AbiTp.prod) (← reflectAbi l a) (← reflectAbi l b)
  | some ``Array, #[a] => return mkApp (l.abiC ``AbiTp.array) (← reflectAbi l a)
  | some ``Vector, #[a, n] => return mkApp2 (l.abiC ``AbiTp.vec) n (← reflectAbi l a)
  | _, _ => throwError "lift: not an ABI type{indentExpr ty}"

def isObjType (l : Lang) (ty : Lean.Expr) : MetaM Bool := do
  try discard <| reflectTp l ty; return true catch _ => return false

/-- The ABI type of an object type, if it is one. -/
partial def abiOfTp (l : Lang) (t : Lean.Expr) : MetaM Lean.Expr := do
  let t ← whnfR t
  let as := t.getAppArgs
  match t.getAppFn.constName? with
  | some ``Tp.base =>
    let b := as.back!
    unless ← isDefEq (mkApp l.abi b) (mkConst ``Bool.true) do
      throwError "lift: not an ABI type{indentExpr t}"
    let h := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)
    return mkApp4 (mkConst ``AbiTp.base) l.base l.abi b h
  | some ``Tp.uInt32 => return l.abiC ``AbiTp.uInt32
  | some ``Tp.bool => return l.abiC ``AbiTp.bool
  | some ``Tp.unit => return l.abiC ``AbiTp.unit
  | some ``Tp.prod =>
    return mkApp2 (l.abiC ``AbiTp.prod) (← abiOfTp l as[as.size - 2]!) (← abiOfTp l as.back!)
  | some ``Tp.array => return mkApp (l.abiC ``AbiTp.array) (← abiOfTp l as.back!)
  | some ``Tp.vec => return mkApp2 (l.abiC ``AbiTp.vec) as[as.size - 2]! (← abiOfTp l as.back!)
  | _ => throwError "lift: not an ABI type{indentExpr t}"

/-- A projection applied to a variable, as the projection function's
application, as the source writes it. -/
partial def projToApp (e : Lean.Expr) : MetaM Lean.Expr := do
  match e with
  | .proj S i s => mkProjection (← projToApp s) (getStructureFields (← getEnv) S)[i]!
  | _ => return e

/-- The representative a relation `x = rhs` names. For an erasure
`erase s a`, the erasure is unfolded until it is `a`, a projection of `a` (as
the source writes it), or a value no longer mentioning `a` (`()`, a field of
a constructor application); nothing beyond it is unfolded. -/
partial def repOf (rhs : Lean.Expr) : MetaM Lean.Expr := do
  let isProjApp ← match rhs.getAppFn.constName? with
    | some f => pure (← getProjectionFnInfo? f).isSome
    | none => pure false
  unless rhs.isAppOf ``Lift.erase || isProjApp do return rhs
  let a := rhs.appArg!
  -- Bound variables stay: they are the AST's atoms.
  let whnfCore (e : Lean.Expr) := withConfig (fun c => { c with zetaDelta := false }) (whnfCore e)
  let rec go (e : Lean.Expr) (fuel : Nat) : MetaM Lean.Expr := do
    let e := e.headBeta
    if e == a || !(e.find? (· == a)).isSome then return e
    if let .proj _ _ s := e then
      if s == a then return ← projToApp e
    if let some f := e.getAppFn.constName? then
      if let some info ← getProjectionFnInfo? f then
        if e.getAppNumArgs == info.numParams + 1 && e.appArg! == a then
          -- A projection of a constructor application reduces; of a variable,
          -- it is the representative.
          let S := (← getConstInfoCtor info.ctorName).induct
          let e' ← whnfCore (.proj S info.i a)
          unless e'.isProj do return ← go e' (fuel - 1)
          return e
    if fuel == 0 then return e
    let e' ← whnfCore e
    if e' != e then return ← go e' (fuel - 1)
    -- A field of the erasure, which is a definition.
    if let .proj .. := e.getAppFn then
      if let some f ← reduceProj? e.getAppFn then return ← go (mkAppN f e.getAppArgs) (fuel - 1)
    match ← unfoldDefinition? e with
    | some e' => go e' (fuel - 1)
    | none => return e
  go rhs 64

/-- `Lift.Rep ℓ t σ`. -/
def Lang.rep (l : Lang) (t σ : Lean.Expr) : MetaM Lean.Expr :=
  mkAppOptM ``Lift.Rep #[none, none, l.lift, t, σ]

/-- The representation of the source type `σ` in the lift: the one
constructor of the lift's representation type that represents `σ`. For an
ABI object type, its AST type is the type's own, found first: unification
cannot solve `M.V ?t = σ` for `?t`. -/
def reflectRep (l : Lang) (σ : Lean.Expr) : MetaM Lean.Expr := do
  let t ← if ← isObjType l σ then reflectAbi l σ
    else mkFreshExprMVar (← mkAppM ``Language.AbiTp #[l.L])
  let repTy ← whnf (← l.rep t σ)
  let mut found := #[]
  if let some I := repTy.getAppFn.constName? then
    if let .inductInfo ii ← getConstInfo I then
      for ctor in ii.ctors do
        let saved ← saveState
        let c ← mkConstWithFreshMVarLevels ctor
        let (args, _, cty) ← forallMetaTelescopeReducing (← inferType c)
        if ← isDefEq cty repTy then
          let s ← instantiateMVars (mkAppN c args)
          unless s.hasExprMVar do found := found.push s
        saved.restore
  match found with
  | #[s] => return s
  | #[] => throwError "lift: no representation of the source type{indentExpr σ}"
  | _ => throwError "lift: several representations of the source type{indentExpr σ}\n\
      {found.toList.map indentExpr}"

/-- The AST type a representation is indexed by. -/
def repAbi (l : Lang) (s : Lean.Expr) : MetaM Lean.Expr := do
  let t ← mkFreshExprMVar (← mkAppM ``Language.AbiTp #[l.L])
  let σ ← mkFreshExprMVar (mkSort Level.one)
  unless ← isDefEq (← inferType s) (← l.rep t σ) do
    throwError "lift: internal error, not a representation{indentExpr s}"
  instantiateMVars t

/-- How source values of type `σ` are represented: an object type `t` and a
relation `M.V t → σ → Prop`. Equality for object types; otherwise the graph
of the erasure. -/
def relFor (l : Lang) (σ : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  if ← isObjType l σ then
    let t ← reflectTp l σ
    return (t, ← mkAppOptM ``Eq #[l.val t])
  let s ← reflectRep l σ
  let t ← whnf (← mkAppM ``Subtype.val #[← repAbi l s])
  let R ← withLocalDeclD `v (l.val t) fun v => withLocalDeclD `a σ fun a => do
    mkLambdaFVars #[v, a] (← mkEq v (← mkAppOptM ``Lift.erase #[none, none, l.lift, none, none, s, a]))
  return (t, R)

/-- `relFor` for a result type `σ y` that may depend on a source argument
`y : τ`: the object type, which may not, and the relation as a function of
`y`. -/
def relForDep (l : Lang) (τ σ : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let n := if let .lam n .. := σ then n else `y
  withLocalDeclD n τ fun y => do
    let (t, R) ← relFor l (σ.beta #[y])
    let t ← instantiateMVars t
    if t.containsFVar y.fvarId! then
      throwError "lift: the AST type of{indentExpr (σ.beta #[y])}
depends on the argument"
    return (t, ← mkLambdaFVars #[y] (← instantiateMVars R))

/-- The representation of a result type `σ y` that may depend on a source
argument `y : τ`: its ABI type, which may not, the representation as a
function of `y`, and the eraser, unfolded. -/
def eraserForDep (l : Lang) (τ σ : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Lean.Expr) := do
  let n := if let .lam n .. := σ then n else `y
  withLocalDeclD n τ fun y => do
    let s ← reflectRep l (σ.beta #[y])
    let t ← repAbi l s
    if t.containsFVar y.fvarId! then
      throwError "lift: the AST type of{indentExpr (σ.beta #[y])}
depends on the argument"
    -- Over the source's own types, which matching need not unfold, and
    -- unfolded (`w.val`), so relations match the rules'.
    let eo ← withLocalDeclD `b (σ.beta #[y]) fun b => do
      mkLambdaFVars #[y, b] (← repOf (← mkAppOptM ``Lift.erase #[none, none, l.lift, none, none, s, b]))
    return (t, ← mkLambdaFVars #[y] s, eo)

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

/-- The shape of a registered rule's source: a value bound for the rest
(`tk v`), an operation followed by code (`src >>= tk`), or one in tail
position. -/
inductive RuleKind
| value
| bind
| tail
deriving BEq, Inhabited

/-- A table entry: how a source construct maps to a certificate rule. -/
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
  /-- For a registered rule: the shape of its source. Its pattern is its
  conclusion, so `pattern` and `args` are unused. -/
  kind : Option RuleKind := none

def Entry.head (e : Entry) : MetaM Name := do
  lambdaTelescope e.pattern fun _ body => do
    let some n := body.getAppFn.constName? | throwError "lift: entry pattern without a head"
    return n

/-- The variables of an entry's argument functions: those ranging over `Type`
become object types, and types mentioning them become denotations. -/
def withArgVars (l : Lang) (xs : Array Lean.Expr)
    (k : Array Lean.Expr → Array Lean.Expr → MetaM α) : MetaM α := do
  let rec go (i : Nat) (ys subst : Array Lean.Expr) : MetaM α := do
    if h : i < xs.size then
      let x := xs[i]
      let ty ← inferType x
      let n ← x.fvarId!.getUserName
      if ty.isType then
        withLocalDeclD n l.tp fun s =>
          go (i + 1) (ys.push s) (subst.push (l.val s))
      else
        withLocalDeclD n (ty.replaceFVars (xs.extract 0 i) subst) fun y =>
          go (i + 1) (ys.push y) (subst.push y)
    else k ys subst
  go 0 #[] #[]

/-- An argument function over the pattern variables `xs`, given its body in
terms of the new variables and the substitution for the old ones. -/
def argFn (l : Lang) (xs : Array Lean.Expr)
    (f : Array Lean.Expr → Array Lean.Expr → MetaM Lean.Expr) : MetaM Lean.Expr :=
  withArgVars l xs fun ys subst => do mkLambdaFVars ys (← f ys subst)

/-- The elements of a list of known length (`List.replicate 2 a`), by
reducing it a cell at a time. -/
partial def listElems? (e : Lean.Expr) : MetaM (Option (List Lean.Expr)) := do
  let e ← whnf e
  if e.isAppOfArity ``List.nil 1 then return some []
  if e.isAppOfArity ``List.cons 3 then
    return (← listElems? e.appArg!).map (e.appFn!.appArg! :: ·)
  return none

/-- A builtin: a source pattern, and the builtin as a function of the
pattern's static variables: its type variables (as object types), natural
numbers (lengths, indices), and proofs about these alone. Its operands are
the pattern's other variables that are not proofs, in order. -/
def builtinEntry (l : Lang) (pat b : Lean.Expr) : MetaM Entry := do
  lambdaTelescope pat fun xs body => do
    let mut isStatic : Array Bool := #[]
    -- Proofs (bounds) are not operands.
    let isProof ← xs.mapM fun x => do isProp (← inferType x)
    for x in xs, p in isProof do
      let ty ← inferType x
      let static ← if ty.isType || ty.isConstOf ``Nat then pure true
        else if p then
          -- A proof about static variables only (`i < n`).
          pure <| (xs.zip isStatic).all fun (y, st) => st || !ty.containsFVar y.fvarId!
        else pure false
      isStatic := isStatic.push static
    let static := isStatic
    let builtin (ys : Array Lean.Expr) : Lean.Expr :=
      (mkAppN b ((ys.zip static).filterMap fun (y, t) => if t then some y else none)).headBeta
    let bArg ← argFn l xs fun ys _ => return builtin ys
    let argsArg ← argFn l xs fun ys _ => do
      let bb := builtin ys
      let .app (.app _ inp) _ ← whnf (← inferType bb) |
        throwError "lift: not a builtin{indentExpr bb}"
      let some tps ← listElems? inp | throwError "lift: builtin inputs{indentExpr inp}"
      let vs := ((ys.zip static).zip isProof).filterMap fun ((y, t), p) =>
        if t || p then none else some y
      let tpT := l.tp
      let V := mkApp2 (mkConst ``Language.Model.V) l.L l.model
      let mut h ← mkAppOptM ``HList.nil #[tpT, V]
      let mut rest ← mkAppOptM ``List.nil #[tpT]
      for (tp, v) in (tps.zip vs.toList).reverse do
        h ← mkAppOptM ``HList.cons #[tpT, V, tp, rest, v, h]
        rest ← mkAppOptM ``List.cons #[tpT, tp, rest]
      return h
    let rArg ← argFn l xs fun _ subst => return body.replaceFVars xs subst
    return { pattern := pat, isValue := true, rule := ``ExprCert.builtin
             args := [(`b, bArg), (`args, argsArg), (`r, rArg)] }

/-- A literal of an ABI type. -/
def literalEntry (pat abi : Lean.Expr) : MetaM Entry := do
  lambdaTelescope pat fun xs body => do
    return { pattern := pat, isValue := true, rule := ``ExprCert.lit
             args := [(`tp, ← mkLambdaFVars xs abi), (`v, ← mkLambdaFVars xs body)] }

/-- The built-in entries for literals and builtins. Builtins and literal types
are written as functions of the language. -/
def staticEntries (l : Lang) : Term.TermElabM (Array Entry) := do
  let elabE (stx : Term) : Term.TermElabM Lean.Expr := do
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasMVar then throwError "lift: ill-formed table entry{indentExpr e}"
    return e
  let lit (p a : Term) : Term.TermElabM Entry := do
    literalEntry (← elabE p) ((← elabE a).beta #[l.L])
  let bi (p b : Term) : Term.TermElabM Entry := do
    builtinEntry l (← elabE p) ((← elabE b).beta #[l.L])
  return #[
    ← lit (← `(fun (n : Nat) => (OfNat.ofNat n : UInt32))) (← `(fun (L : Language) => (AbiTp.uInt32 : L.AbiTp))),
    ← lit (← `(true)) (← `(fun (L : Language) => (AbiTp.bool : L.AbiTp))),
    ← lit (← `(false)) (← `(fun (L : Language) => (AbiTp.bool : L.AbiTp))),
    ← lit (← `(())) (← `(fun (L : Language) => (AbiTp.unit : L.AbiTp))),
    ← lit (← `(PUnit.unit.{1})) (← `(fun (L : Language) => (AbiTp.unit : L.AbiTp))),
    ← bi (← `(fun (a b : UInt32) => a + b)) (← `(fun (L : Language) => @Builtin.uAdd L)),
    ← bi (← `(fun (a b : UInt32) => a - b)) (← `(fun (L : Language) => @Builtin.uSub L)),
    ← bi (← `(fun (a b : UInt32) => a * b)) (← `(fun (L : Language) => @Builtin.uMul L)),
    ← bi (← `(fun (a b : UInt32) => a / b)) (← `(fun (L : Language) => @Builtin.uDiv L)),
    ← bi (← `(fun (a b : UInt32) => a % b)) (← `(fun (L : Language) => @Builtin.uMod L)),
    ← bi (← `(fun (a b : UInt32) => a == b)) (← `(fun (L : Language) => @Builtin.uEq L)),
    ← bi (← `(fun (a b : UInt32) => decide (a < b))) (← `(fun (L : Language) => @Builtin.uLt L)),
    ← bi (← `(fun (a b : UInt32) => decide (a ≤ b))) (← `(fun (L : Language) => @Builtin.uLe L)),
    ← bi (← `(fun (a : Bool) => !a)) (← `(fun (L : Language) => @Builtin.not L)),
    ← bi (← `(fun (a b : Bool) => a && b)) (← `(fun (L : Language) => @Builtin.and L)),
    ← bi (← `(fun (a b : Bool) => a || b)) (← `(fun (L : Language) => @Builtin.or L)),
    ← bi (← `(fun (a b : Bool) => a == b)) (← `(fun (L : Language) => @Builtin.bEq L)),
    ← bi (← `(fun {α β : Type} (a : α) (b : β) => (a, b)))
      (← `(fun (L : Language) (a b : L.Tp) => @Builtin.pair L a b)),
    ← bi (← `(fun {α β : Type} (p : α × β) => p.1)) (← `(fun (L : Language) (a b : L.Tp) => @Builtin.fst L a b)),
    ← bi (← `(fun {α β : Type} (p : α × β) => p.2)) (← `(fun (L : Language) (a b : L.Tp) => @Builtin.snd L a b)),
    ← bi (← `(fun {α : Type} => (#[] : Array α))) (← `(fun (L : Language) (a : L.Tp) => @Builtin.arrEmpty L a)),
    ← bi (← `(fun {α : Type} (xs : Array α) (x : α) => xs.push x))
      (← `(fun (L : Language) (a : L.Tp) => @Builtin.arrPush L a)),
    ← bi (← `(fun {α : Type} (xs : Array α) => xs.size.toUInt32))
      (← `(fun (L : Language) (a : L.Tp) => @Builtin.arrLen L a)),
    ← bi (← `(fun {α : Type} (xs : Array α) (i : UInt32) (h : i.toNat < xs.size) => xs[i.toNat]'h))
      (← `(fun (L : Language) (a : L.Tp) => @Builtin.arrGet L a)),
    ← bi (← `(fun {α : Type} (xs : Array α) (i : UInt32) (x : α) (h : i.toNat < xs.size) =>
        xs.set i.toNat x h))
      (← `(fun (L : Language) (a : L.Tp) => @Builtin.arrSet L a)),
    ← bi (← `(fun {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (h : i < n) => v[i]'h))
      (← `(fun (L : Language) (a : L.Tp) (n i : Nat) (h : i < n) => @Builtin.vecGet L a n i h))]

/-- The elements of a vector literal `#v[x₁, …, xₖ]`, if `v` is one. -/
def vecLitElems? (v : Lean.Expr) : Option (Array Lean.Expr) := do
  guard (v.isAppOfArity ``Vector.mk 4)
  let arr := v.getArg! 2
  guard (arr.isAppOfArity ``List.toArray 2)
  let (_, xs) ← arr.appArg!.listLit?
  return xs.toArray

/-- Vector literals of length `k`: `fun {α} (x₁ … xₖ : α) => #v[x₁, …, xₖ]`, by
`vecLit k`. -/
def vecLitEntry (l : Lang) (k : Nat) : MetaM Entry := do
  let b ← withLocalDeclD `L (mkConst ``Language) fun L =>
    withLocalDeclD `a (mkApp (mkConst ``Language.Tp) L) fun a =>
      mkLambdaFVars #[L, a] (mkApp3 (mkConst ``Builtin.vecLit) L a (mkNatLit k))
  let pat ← withLocalDecl `α .implicit (mkSort Level.one) fun α => do
    let rec go (i : Nat) (xs : Array Lean.Expr) : MetaM Lean.Expr := do
      if i < k then
        withLocalDeclD (.mkSimple s!"x{i}") α fun x => go (i + 1) (xs.push x)
      else
        let arr ← mkAppM ``List.toArray #[← mkListLit α xs.toList]
        let size ← mkEqRefl (← mkAppM ``Array.size #[arr])
        let v := mkApp4 (mkConst ``Vector.mk [Level.zero]) α (mkNatLit k) arr size
        mkLambdaFVars (#[α] ++ xs) v
    go 0 #[]
  builtinEntry l pat (b.beta #[l.L])

/-- Raw operations of the language, for the identity lift. -/
def opEntry (l : Lang) : MetaM Entry := do
  let L := l.L
  let tagIn (γ : Lean.Expr) := mkAppM ``Language.Op #[L, γ]
  let inpOf (γ e : Lean.Expr) : MetaM Lean.Expr := do
    return l.val (← mkAppM ``Subtype.val #[← mkAppM ``Language.input #[L, γ, e]])
  withLocalDecl `γ .implicit (← mkAppM ``Language.Ctx #[L]) fun γ => do
  withLocalDeclD `e (← tagIn γ) fun e => do
  withLocalDeclD `inp (← inpOf γ e) fun inp => do
  let fam ← withLocalDeclD `e (← tagIn γ) fun e' => do mkLambdaFVars #[e'] (← inpOf γ e')
  let sig ← mkAppOptM ``Sigma.mk #[← tagIn γ, fam, e, inp]
  let opFn ← mkAppOptM ``Free.op #[none, mkApp2 (mkConst ``Language.denote) L l.model, none, γ, sig]
  let .forallE _ sbTy _ _ ← whnfR (← inferType opFn) | throwError "lift: unexpected operation type"
  withLocalDeclD `sb sbTy fun sb => do
  let xs := #[γ, e, inp, sb]
  let arg (i : Nat) := argFn l xs fun ys _ => return ys[i]!
  return { pattern := ← mkLambdaFVars xs (mkApp opFn sb), isValue := false
           rule := ``ExprCert.op_eq, tailRule := ``ExprCert.op_eq_tail
           args := [(`e, ← arg 1), (`inp, ← arg 2), (`sb, ← arg 3)] }

/-- Branches on a boolean, with sources over `F`. -/
def iteEntry (l : Lang) (Γ' F : Lean.Expr) : MetaM Entry := do
  withLocalDecl `γ' .implicit Γ' fun γ => do
  withLocalDecl `σ .implicit (mkSort Level.one) fun σ => do
  withLocalDeclD `c (mkConst ``Bool) fun c => do
  let fr ← mkAppOptM ``Free #[none, F, none, γ, σ]
  withLocalDeclD `t fr fun t => do
  withLocalDeclD `e fr fun e => do
  let xs := #[γ, σ, c, t, e]
  let body ← mkAppOptM ``ite #[fr, ← mkEq c (mkConst ``Bool.true), none, t, e]
  let arg (i : Nat) := argFn l xs fun ys _ => return ys[i]!
  let common := [(`c, ← arg 2), (`st, ← arg 3), (`se, ← arg 4)]
  return { pattern := ← mkLambdaFVars xs body, isValue := false
           rule := ``ExprCert.ite, tailRule := ``ExprCert.ite_tail
           args := (`out, ← arg 1) :: common, tailArgs := common
           hint := "conditions must be booleans: write `decide (x < y)` rather than `x < y`" }

/-- A registered rule, keyed by the head symbol of its source. -/
def ruleEntry (c : Name) : MetaM (Name × Entry) := do
  let r ← RuleInst.new c
  unless r.concl.isAppOfArity ``ExprCert 14 do
    throwError "lift: `{c}` is not an expression certificate rule"
  let src ← instantiateMVars r.concl.appArg!
  let (kind, v) :=
    if src.getAppFn.isMVar then (RuleKind.value, src.appArg!)
    else if src.isAppOfArity ``Bind.bind 6 then (.bind, src.getArg! 4)
    else (.tail, src)
  let some head := v.getAppFn.constName? |
    throwError "lift: the source of rule `{c}` has no head symbol{indentExpr v}"
  return (head, { pattern := mkConst c, isValue := kind == .value, rule := c, args := []
                  kind := some kind })

/-- Calls to a function in scope: a helper definition or a join point. -/
def callEntry (l : Lang) (key inp out αo Ro : Lean.Expr) : MetaM Entry := do
  let .forallE n τ _ _ ← whnfR (← inferType key) | throwError "lift: not a function{indentExpr key}"
  withLocalDeclD n τ fun x => do
    let xs := #[x]
    let const (v : Lean.Expr) := argFn l xs fun _ _ => return v
    -- The AST argument `x` is left to the relation premise.
    -- The result type and relation may depend on the argument; they are taken
    -- from the function certificate, not inferred.
    let common := [(`inp, ← const inp), (`src, ← const key), (`αo, ← const αo), (`Ro, ← const Ro),
      (`y, ← argFn l xs fun ys _ => return ys[0]!)]
    return { pattern := ← mkLambdaFVars xs (mkApp key x), isValue := false
             rule := ``ExprCert.app, tailRule := ``ExprCert.app_tail
             args := (`out, ← const out) :: common, tailArgs := common }


/-! ## Traversal state -/

/-- A function in scope, with its certificate at the current heap. -/
structure FnInfo where
  src : Lean.Expr
  cert : Lean.Expr

/-- A source variable with no AST variable of its own (a proof, a
value paired with a proof): the atom representing it, and a proof that the registered
relation holds between them. -/
structure Ghost where
  var : Lean.Expr
  rep : Lean.Expr
  proof : Lean.Expr

structure Ctx where
  lang : Lang
  /-- The source effects, over the language's contexts `Γ'`. -/
  Γ' : Lean.Expr
  F : Lean.Expr
  sim : Lean.Expr
  heap : Lean.Expr
  /-- Source variables standing for AST variables. -/
  atoms : Array Lean.Expr := #[]
  /-- Hypotheses from rule premises, about source variables. -/
  hyps : Array Lean.Expr := #[]
  ghosts : Array Ghost := #[]
  fns : Array FnInfo := #[]
  /-- Entries, by head symbol. -/
  table : Std.HashMap Name (Array Entry)
  /-- Operation wrappers, unfolded to raw operations. -/
  wrappers : Array Name
  /-- Definitions matching may unfold besides reducible ones and instances: the
  language and the lift, with their auxiliary definitions. -/
  unfoldable : Array Name
  /-- Whether the lift is the identity, over the language's own operations. -/
  identity : Bool

abbrev M := ReaderT Ctx MetaM

/-- Unification for matching the source. It may unfold the language, the lift,
reducible definitions, instances and structure projections, together with
their auxiliary definitions (such as compiled pattern matches), and type
synonyms, but never user definitions of values. -/
def matchDefEq (a b : Lean.Expr) : M Bool := do
  let allowed := (← read).unfoldable
  let ok (n : Name) : CoreM Bool := do
    let mut n := n
    while !n.isAnonymous do
      let env ← getEnv
      if allowed.contains n || isInstanceCore env n || env.isProjectionFn n then return true
      -- Type synonyms (`Circuit P`) are seen through; values are not.
      if let some ci := env.find? n then
        if ci.type.getForallBody.isSort then return true
      if (← getReducibilityStatus n) == .reducible then return true
      n := n.getPrefix
    return false
  withCanUnfoldPred (fun _ ci => ok ci.name) (isDefEq a b)

def isAtom (x : Lean.Expr) : M Bool := return (← read).atoms.contains x.consumeMData

def withAtom (x : Lean.Expr) (k : M α) : M α :=
  withReader (fun c => { c with atoms := c.atoms.push x }) k

/-- Whether source values of type `ty` are AST values themselves. -/
def isObj (ty : Lean.Expr) : M Bool := do
  return isValType ty || (← isObjType (← read).lang ty)

/-- Move to a larger heap: every function certificate is moved along. -/
def withHeap (h' hle : Lean.Expr) (k : M α) : M α := do
  let fns ← (← read).fns.mapM fun i => do
    let cert ← mkRule ``FnCert.mono [(`hf, i.cert), (`h', h'), (`hle, hle)]
    return { i with cert }
  withReader (fun c => { c with heap := h', fns }) k

def entriesFor (f : Lean.Expr) : M (Array Entry) := do
  let c ← read
  let calls ← c.fns.filterMapM fun i => do
    if i.src.getAppFn == f then
      let ty ← instantiateMVars (← inferType i.cert)
      unless ty.isAppOfArity ``FnCert 17 do return none
      let as := ty.getAppArgs
      return some (← callEntry c.lang i.src as[8]! as[9]! as[11]! as[15]!)
    else return none
  let static := match f.constName? with
    | some n => c.table.getD n #[]
    | none => #[]
  return calls ++ static

/-- Set the arguments every certificate rule shares: the context, and the
result type when the rule states it. -/
def setShared (r : RuleInst) : M Unit := do
  let c ← read
  r.set `L c.lang.L
  r.set `M c.lang.model
  -- Rules over the identity lift state no source effects of their own.
  for (n, v) in [(`Γ', c.Γ'), (`F, c.F)] do
    if r.args.any (·.1 == n) then r.set n v
  r.synthInstances
  if r.args.any (·.1 == `spec) then r.set `spec c.sim

/-- The result relation is fixed later, by `concludeIn`: its type may mention
operation results that are only known once the rule is matched. -/
def setBase (r : RuleInst) (γ o _R : Lean.Expr) : M Unit := do
  let c ← read
  setShared r
  r.set `h c.heap
  r.set `γ γ
  if r.args.any (·.1 == `γ') then r.set `γ' (γ)
  if r.args.any (·.1 == `o) then r.set `o o

/-- Fix the context, result type and result relation of a rule's conclusion. -/
def concludeIn (r : RuleInst) (γ o R : Lean.Expr) : MetaM Unit := do
  let as := r.concl.getAppArgs
  unless (← isDefEq as[6]! γ) && (← isDefEq as[8]! o) && (← isDefEq as[12]! R) do
    throwError "lift: `{r.name}` concludes in the wrong context, result type or relation"

/-- Choose the relations of a rule's intermediate results that are still
open (`Ri`, `Ro`, and `Rb` for what an operation's blocks return), from their
source types. An AST type the rule leaves open (a hint's result type) is the
source type's representation. -/
def setRels (r : RuleInst) : M Unit := do
  let l := (← read).lang
  for n in [`Ri, `Ro, `Rb] do
    let some (_, m, _) := r.args.find? (·.1 == n) | continue
    if ← m.mvarId!.isAssigned then continue
    let .forallE _ vt (.forallE _ σ _ _) _ ← whnf (← instantiateMVars (← inferType m)) | continue
    let σ ← instantiateMVars σ
    if σ.hasExprMVar then continue
    let (t, R) ← relFor l σ
    let vt ← instantiateMVars vt
    if vt.isAppOfArity ``Language.Model.V 3 then
      let a := vt.appArg!
      if a.isAppOfArity ``Subtype.val 3 && a.appArg!.isMVar then
        discard <| isDefEq a.appArg! (← abiOfTp l t)
      else if a.isMVar then
        discard <| isDefEq a t
    r.set n R

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

/-- Drop unused `let`s and `have`s at the head of a continuation's body: what
the elaborator leaves of `let _ ← x` when `x` returns a structure. -/
partial def dropDeadLets (k : Lean.Expr) : Lean.Expr :=
  match k with
  | .lam n t b bi => .lam n t (go b) bi
  | _ => k
where
  go (b : Lean.Expr) : Lean.Expr :=
    match b with
    | .letE _ _ _ body _ => if body.hasLooseBVar 0 then b else go (body.lowerLooseBVars 1 1)
    | .mdata _ e => go e
    | _ => b

/-- A premise `v = y` between an atom `v` and another variable `y`, up to
reduction. -/
def substEq (d : Lean.Expr) : M (Option (Lean.Expr × Lean.Expr)) := do
  let d ← whnfR d
  unless d.isAppOfArity ``Eq 3 do return none
  let v := d.appFn!.appArg!.consumeMData
  let y ← whnf d.appArg!
  unless v.isFVar && y.isFVar && v != y && (← isAtom v) do return none
  return some (v, y)

/-- `Eq.ndrec p h : motive y`, for `p : motive v` and `h : v = y`, assigning
the AST holes of `motive v` from `p` (which `mkAppM` would not). -/
def mkNdrec (v y motive p h : Lean.Expr) : MetaM Lean.Expr := do
  unless ← isDefEq (← inferType p) (motive.beta #[v]) do
    throwError "lift: internal error, cannot transport{indentExpr p}"
  let α ← inferType v
  let u ← getLevel α
  let w ← getLevel (motive.beta #[v])
  return mkApp6 (mkConst ``Eq.ndrec [w, u]) α v motive p y h

/-- Prove `x = erase y` (or `x = y`), relating the source term `y` to an AST
atom `x` that the proof chooses: from what is known of a ghost, a hypothesis,
or the erasure itself, when it is an atom or a unit value. If the erasure is
a source term that is not yet an atom, returns it to be bound first. -/
def represent (goal : Lean.Expr) : M (Except Lean.Expr Lean.Expr) := do
  let c ← read
  let goal := (← instantiateMVars goal).headBeta
  -- The source value represented: what a ghost or hypothesis must be about.
  let rhs := goal.appArg!
  let isProjApp ← match rhs.getAppFn.constName? with
    | some f => pure (← getProjectionFnInfo? f).isSome
    | none => pure false
  let y := if rhs.isAppOf ``Lift.erase || isProjApp then rhs.appArg! else rhs
  for g in c.ghosts do
    if g.var == y then
      if ← isDefEq goal (← inferType g.proof) then return .ok g.proof
  if y.isFVar then
    for h in c.hyps do
      let hty ← inferType h
      if hty.containsFVar y.fvarId! then
        if ← isDefEq hty goal then return .ok h
  let goal ← whnfR goal
  if goal.isAppOfArity ``Eq 3 then
    let xm := goal.appFn!.appArg!
    let r ← repOf goal.appArg!
    if ← isAtom r then
      if ← isDefEq xm r then return .ok (← mkEqRefl r)
    else if !r.hasFVar then
      -- A closed value (`()`): any atom equal to it represents it.
      for a in c.atoms.reverse do
        let saved ← (saveState : MetaM Meta.SavedState)
        if (← isDefEq a r) && (← isDefEq xm a) then return .ok (← mkEqRefl a)
        (saved.restore : MetaM Unit)
    else if !(← (c.ghosts.map (·.var)).anyM fun g => return r.containsFVar g.fvarId!) then
      return .error r
  throwError "lift: cannot represent the source term as required by{indentExpr goal}"

/-! ## Builtins -/

/-- Prove that a builtin succeeds: by computation, unfolding the values of
bound variables, or from the source's bounds proof. -/
def builtinSucceeds (ty : Lean.Expr) : MetaM Lean.Expr := do
  if ← withConfig (fun c => { c with zetaDelta := true }) (isDefEq ty.appFn!.appArg! ty.appArg!) then
    return ← mkEqRefl ty.appArg!
  for n in [``Builtin.denote_arrGet, ``Builtin.denote_arrSet] do
    let saved ← saveState
    let c ← mkConstWithFreshMVarLevels n
    let (args, _, concl) ← forallMetaTelescopeReducing (← inferType c)
    if ← withConfig (fun c => { c with zetaDelta := true }) (isDefEq concl ty) then
      let p ← instantiateMVars (mkAppN c args)
      unless p.hasExprMVar do return p
    saved.restore
  throwError "lift: cannot show that this builtin succeeds{indentExpr ty}"

/-! ## Registration attributes -/

/-- A value rule (whose source is `tk v`) certifies its continuation `hk` at
the value, not for every value: the source's facts about the value must stay
available. -/
def checkValueRule (c : Name) : MetaM Unit := do
  forallTelescope (← getConstInfo c).type fun xs concl => do
    unless concl.isAppOfArity ``ExprCert 14 && concl.appArg!.getAppFn.isFVar do return
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.userName == `hk && (← whnfR d.type).isForall then
        throwError "lift: the value rule `{c}` must certify its continuation at its value: \
          `hk : ExprCert … (k v) R (tk v)`, not for every value"

private def registerAttr (attr : Name) (kind : RegKind) (descr : String) : IO Unit :=
  registerBuiltinAttribute {
    name := attr
    descr
    add := fun decl stx _ => do
      let lift ← realizeGlobalConstNoOverload stx[1]
      if kind == .rule then (checkValueRule decl).run'
      modifyEnv (registeredExt.addEntry · { lift, decl, kind }) }

initialize registerAttr `lift_rule .rule "a certificate rule of a lift"
initialize registerAttr `lift_base .base "a base type of a lift's language, for reflecting source types"

/-! ## Emission -/

/-- AST holes over empty types: blocks of operations that have none. -/
def fillEmptyHoles (r : RuleInst) : MetaM Unit := do
  for (_, m, bi) in r.args do
    if bi.isInstImplicit || (← m.mvarId!.isAssigned) then continue
    let ty ← instantiateMVars (← inferType m)
    if let .forallE n d body _ := ty then
      if ← isEmptyType d then
        unless ← isDefEq m (← absurdLam n d fun b => return body.instantiate1 b) do
          throwError "lift: cannot fill an empty hole of `{r.name}`"

mutual

/-- Certify the computation `s` in context `γ`, returning object type `o`,
with results related by `R`. -/
partial def trComp (s γ o R : Lean.Expr) : M Lean.Expr := do
  let s := (← instantiateMVars s).consumeMData.headBeta
  if let .letE n ty v b nd := s then
    if v.isLambda && (← isFree (← inferType (← etaExpand v)).getForallBody) then
      return ← trJoin n ty v b s γ o R
    -- Atoms, and values that are not AST values (proofs), are substituted.
    if (← isAtom v) || !(← isObj ty) then
      return ← trComp (b.instantiate1 v) γ o R
    -- The `let` stays until its value is a variable, so the value is bound once
    -- even when its own operands must be bound first.
    return ← bindValue v (fun v' => .letE n ty v' b nd) γ o R
  let f := s.getAppFn
  let as := s.getAppArgs
  if f.isConstOf ``Pure.pure && as.size == 4 then
    let v := as[3]!
    if v.isAppOfArity ``ForInStep.yield 2 || v.isAppOfArity ``ForInStep.done 2 then
      return ← trStep v (fun v' => mkAppN f (as.set! 3 v')) γ o R
    let obj ← isObj (← inferType v)
    if obj && !(← isAtom v) then return ← bindValue v (mkAppN f <| as.set! 3 ·) γ o R
    let r ← RuleInst.new ``ExprCert.ret
    setBase r γ o R
    r.set `a v
    concludeIn r γ o R
    unless obj do
      match ← represent (← instantiateMVars (← inferType (← r.arg `hR))) with
      | .ok p => r.set `hR p
      | .error t =>
        let swap (y : Lean.Expr) := mkAppN f <| as.set! 3 (v.replace fun e => if e == t then some y else none)
        return ← bindValue t swap γ o R
    discharge r
    return ← r.finish
  if f.isConstOf ``Bind.bind && as.size == 6 then
    let x := as[4]!.consumeMData.headBeta
    -- Monadic padding: binding a return is definitionally its continuation.
    if x.isAppOfArity ``Pure.pure 4 then
      return ← trComp (mkApp as[5]! x.appArg!) γ o R
    let as := as.set! 5 (dropDeadLets as[5]!)
    return ← trHead x (some as[5]!) (mkAppN f <| as.set! 4 ·) γ o R
  trHead s none id γ o R

/-- A loop body's last step, `pure (.yield a)` or `pure (.done a)`: the next
state, and whether to continue. `rebuild` puts a replacement for the step
back into the source. -/
partial def trStep (v : Lean.Expr) (rebuild : Lean.Expr → Lean.Expr) (γ o R : Lean.Expr) :
    M Lean.Expr := do
  let a := v.appArg!
  let withA (y : Lean.Expr) := rebuild (mkApp v.appFn! y)
  if (← isObj (← inferType a)) && !(← isAtom a) then return ← bindValue a withA γ o R
  let r ← RuleInst.new
    (if v.isAppOf ``ForInStep.yield then ``ExprCert.yield else ``ExprCert.done)
  setBase r γ o R
  r.set `a a
  concludeIn r γ o R
  match ← represent (← instantiateMVars (← inferType (← r.arg `hR))) with
  | .ok p => r.set `hR p
  | .error t =>
    return ← bindValue t (fun y => withA (a.replace fun e => if e == t then some y else none)) γ o R
  discharge r
  r.finish

/-- Certify the computation `x`, followed by `cont` if present. `rebuild`
puts a replacement for `x` back into the whole source. -/
partial def trHead (x : Lean.Expr) (cont : Option Lean.Expr) (rebuild : Lean.Expr → Lean.Expr)
    (γ o R : Lean.Expr) : M Lean.Expr := do
  let x := x.consumeMData.headBeta
  let f := x.getAppFn
  if (← read).wrappers.any f.isConstOf then
    let some x' ← unfoldDefinition? x | unsupported "operation wrapper" x
    return ← trHead x' cont rebuild γ o R
  if f.isConstOf ``dite && x.getAppNumArgs == 5 then
    return ← trDite x cont rebuild γ o R
  let entries := (← entriesFor f).filter fun e => !e.isValue && match e.kind with
    | some .bind => cont.isSome
    | some .tail => cont.isNone
    | _ => true
  for e in entries do
    if let some p ← applyEntry e x rebuild cont γ o R then return p
  noMatch entries x
  if let some c := f.constName? then
    if ← isMatcher c then
      throwError "lift: pattern matching (including destructuring) is not supported{indentExpr x}"
    throwError "lift: call to `{c}`, which is neither a listed helper nor an operation{indentExpr x}"
  unsupported "construct" x

/-- Bind the value `v` to a variable, then continue with `rebuild` applied to
it. -/
partial def bindValue (v : Lean.Expr) (rebuild : Lean.Expr → Lean.Expr) (γ o R : Lean.Expr) :
    M Lean.Expr := do
  let v := v.consumeMData
  let mut entries := (← entriesFor v.getAppFn).filter (·.isValue)
  if let some xs := vecLitElems? v then
    entries := entries.push (← vecLitEntry (← read).lang xs.size)
  for e in entries do
    if let some p ← applyEntry e v rebuild none γ o R then return p
  noMatch entries v
  unsupported "value" v

/-- Apply a table entry to the source term `x`, or fail to match. -/
partial def applyEntry (e : Entry) (x : Lean.Expr) (rebuild : Lean.Expr → Lean.Expr)
    (cont : Option Lean.Expr) (γ o R : Lean.Expr) : M (Option Lean.Expr) := do
  if let some kind := e.kind then return ← applyRule e.rule kind x rebuild γ o R
  let (ms, _, body) ← lambdaMetaTelescope e.pattern
  unless ← matchDefEq body x do return none
  let vals ← ms.mapM instantiateMVars
  -- Operands that are not variables are bound first, one at a time.
  for i in [:vals.size] do
    let ty ← instantiateMVars (← inferType ms[i]!)
    if (← isObjType (← read).lang ty) && !(← isAtom vals[i]!) then
      let swap (y : Lean.Expr) := rebuild (e.pattern.beta (vals.set! i y))
      return some (← bindValue vals[i]! swap γ o R)
  let (rule, args) ← match e.isValue, cont with
    | false, none =>
      let some r := e.tailRule | throwError "lift: `{e.rule}` has no tail-position variant"
      pure (r, e.tailArgs)
    | _, _ => pure (e.rule, e.args)
  let r ← RuleInst.new rule
  setBase r γ o R
  -- Type variables become object types, but only where an argument uses them
  -- (a tail branch's result type is never reflected, so it may be any type).
  let used ← vals.mapIdxM fun i _ => args.anyM fun (_, f) =>
    lambdaTelescope f fun xs _ => do
      if h : i < xs.size then
        return (← instantiateMVars (f.beta xs)).containsFVar xs[i].fvarId!
      return false
  let argVals ← vals.mapIdxM fun i v => do
    if (← inferType v).isType && used[i]! then reflectTp (← read).lang v else pure v
  for (n, f) in args do
    r.set n (f.beta argVals)
    r.synthInstances
  if e.isValue then r.set `t (rebuild x)
  concludeIn r γ o R
  -- The conclusion's source must be the source.
  let .app _ src := r.concl | unreachable!
  unless ← matchDefEq src (rebuild x) do
    throwError "lift: `{rule}` does not match the source{indentExpr (rebuild x)}"
  setRels r
  if e.isValue then return some (← bindLet r x rebuild γ o R)
  discharge r
  return some (← r.finish)

/-- Bind the value `x` of a builtin, literal or value rule by a `let`, so that the
source's proofs about it (an array's size) stay valid, and certify the rest
at it: its premise `hk` is proved under the `let`. -/
partial def bindLet (r : RuleInst) (x : Lean.Expr) (rebuild : Lean.Expr → Lean.Expr)
    (γ o R : Lean.Expr) : M Lean.Expr := do
  discharge r (skip := #[`hk])
  let k ← r.arg `k
  let .forallE kn dom _ _ ← whnfR (← instantiateMVars (← inferType k)) |
    throwError "lift: internal error, `{r.name}` has no continuation"
  -- Named after the source's `let`, if the value is one.
  let n := if let .letE n .. := rebuild x then n else `x
  withLetDecl n (← inferType x) x fun y => do
    let p ← withAtom y (trComp (rebuild y) γ o R)
    let e := (← instantiateMVars (← inferType p)).getArg! 11
    unless ← isDefEq k (.lam kn dom (e.abstract #[y]) .default) do
      throwError "lift: internal error, cannot close the continuation of `{r.name}`"
    r.set `hk (← mkLetFVars #[y] p)
  r.finish

/-- A branch on a decidable proposition `if h : p then … else …`. Its
condition is computed by the builtin that decides `p`, and each branch is
certified under its side of `p`. -/
partial def trDite (x : Lean.Expr) (cont : Option Lean.Expr) (rebuild : Lean.Expr → Lean.Expr)
    (γ o R : Lean.Expr) : M Lean.Expr := do
  let as := x.getAppArgs
  let c ← mkAppOptM ``decide #[as[1]!, as[2]!]
  let entries := (← entriesFor (mkConst ``decide)).filter (·.isValue)
  for e in entries do
    let (ms, _, body) ← lambdaMetaTelescope e.pattern
    unless ← matchDefEq body c do continue
    let vals ← ms.mapM instantiateMVars
    for i in [:vals.size] do
      let ty ← instantiateMVars (← inferType ms[i]!)
      if (← isObjType (← read).lang ty) && !(← isAtom vals[i]!) then
        let v := vals[i]!
        let swap (y : Lean.Expr) := rebuild (x.replace fun t => if t == v then some y else none)
        return ← bindValue v swap γ o R
    let r ← RuleInst.new (if cont.isSome then ``ExprCert.dite else ``ExprCert.dite_tail)
    setBase r γ o R
    let argVals ← vals.mapM fun v => do
      if (← inferType v).isType then reflectTp (← read).lang v else pure v
    for (n, f) in e.args do
      if n == `b || n == `args then r.set n (f.beta argVals)
    concludeIn r γ o R
    let .app _ src := r.concl | unreachable!
    unless ← matchDefEq src (rebuild x) do
      throwError "lift: `{r.name}` does not match the source{indentExpr (rebuild x)}"
    setRels r
    discharge r
    return ← r.finish
  throwError "lift: no builtin decides the condition{indentExpr as[1]!}"

/-- Apply a registered rule to the source term `x`, or fail to match. The
rule's conclusion fixes the language, context, result type and heap; its
source is matched against the source. -/
partial def applyRule (rule : Name) (kind : RuleKind) (x : Lean.Expr)
    (rebuild : Lean.Expr → Lean.Expr) (γ o R : Lean.Expr) : M (Option Lean.Expr) := do
  let c ← read
  let l := c.lang
  let r ← RuleInst.new rule
  let as := r.concl.getAppArgs
  let fixed := #[(0, l.L), (1, l.model), (2, c.Γ'), (3, c.F), (5, c.sim), (6, γ), (7, γ),
    (8, o), (10, c.heap), (12, R)]
  for (i, v) in fixed do
    unless ← isDefEq as[i]! v do return none
  r.synthInstances
  if kind == .value then
    -- The rule's value, matched against the source's. The continuation is
    -- the source itself: abstracting the value out of it is ill-typed where
    -- the source's proofs mention the value, which is only bound later, by a
    -- `let`. Rules sharing a head symbol (`+` on fields and on wires) differ
    -- in the continuation's domain.
    let pat := r.concl.appArg!.appArg!
    let tk ← withLocalDeclD `x (← inferType x) fun y => do mkLambdaFVars #[y] (rebuild x)
    unless ← isDefEq (← r.arg `tk) tk do return none
    unless ← matchDefEq pat x do return none
  else
    let src ← instantiateMVars r.concl.appArg!
    reflectResult r (if kind == .bind then src.getArg! 4 else src) x
  let src ← instantiateMVars r.concl.appArg!
  unless ← matchDefEq src (rebuild x) do return none
  -- Operands that are not variables are bound first.
  for (_, m, _) in r.args do
    let v ← instantiateMVars m
    if v.hasExprMVar then continue
    if (← isObjType l (← instantiateMVars (← inferType m))) && !(← isAtom v) then
      unless (x.find? (· == v)).isSome do
        throwError "lift: cannot bind the operand{indentExpr v}\nof `{rule}`"
      let swap (y : Lean.Expr) := rebuild (x.replace fun t => if t == v then some y else none)
      return some (← bindValue v swap γ o R)
  setRels r
  if kind == .value then return some (← bindLet r x rebuild γ o R)
  discharge r
  return some (← r.finish)

/-- Types the rule leaves to the source, such as a hint's result type: if the
rule's source returns a type it leaves open, reflect the source's result type
into the rule's representation of it; if it returns the values of an unknown
object type, into that type. Types that cannot be reflected are rejected. -/
partial def reflectResult (r : RuleInst) (ruleSrc x : Lean.Expr) : M Unit := do
  let l := (← read).lang
  let (_, _, σR) ← asFree (← instantiateMVars (← inferType ruleSrc))
  let (_, _, σX) ← asFree (← inferType x)
  let σR ← instantiateMVars σR
  if σR.isMVar then
    for (_, m, _) in r.args do
      if ← m.mvarId!.isAssigned then continue
      let ty ← instantiateMVars (← inferType m)
      if ty.isAppOf ``Lift.Rep && ty.appArg! == σR then
        let s ← reflectRep l σX
        if ← isDefEq (← inferType m) (← inferType s) then
          discard <| isDefEq m s
    return
  unless σR.isAppOfArity ``Language.Model.V 3 do return
  let t := σR.appArg!
  if t.isMVar then
    discard <| isDefEq t (← reflectTp l σX)
  else if t.isAppOfArity ``Subtype.val 3 && t.appArg!.isMVar then
    discard <| isDefEq t.appArg! (← reflectAbi l σX)

/-- Discharge the explicit premises of a rule instance. -/
partial def discharge (r : RuleInst) (skip : Array Name := #[]) : M Unit := do
  for (n, m, bi) in r.args do
    if !bi.isExplicit || skip.contains n || (← m.mvarId!.isAssigned) then continue
    let ty ← instantiateMVars (← inferType m)
    let p ← premise ty
    unless ← isDefEq m p do
      throwError "lift: premise `{n}` of `{r.name}` has type{indentExpr ty}\n\
        but its proof has type{indentExpr (← inferType p)}"
  fillEmptyHoles r

/-- Prove a premise: an expression certificate for a hole or continuation,
under binders; a function certificate in scope; a builtin's result; or a
relation between an AST value and a source term. Binders are AST variables
(atoms), hypotheses, or source variables without AST variables of their own
(ghosts), which are represented once all binders are known. An equation
between an atom and a variable is substituted. `unfold` rewrites the source
at the leaf (a definition's body for its name). -/
partial def premise (ty : Lean.Expr) (unfold : Lean.Expr → Lean.Expr := id)
    (pending : Array Lean.Expr := #[]) (rename : Name → Option Name := fun _ => none) :
    M Lean.Expr := do
  match ty with
  | .forallE n d b _ =>
    if ← isEmptyType d then
      return ← absurdLam n d fun x => return b.instantiate1 x
    let n := (rename n).getD ((sourceBinder b).getD n)
    withLocalDeclD n d fun x => do
      let rest := b.instantiate1 x
      if ← isProp d then
        if let some (v, y) ← substEq d then
          let p ← premise (rest.replaceFVar y v) unfold (pending.erase y) rename
          let motive ← mkLambdaFVars #[y] rest
          return ← mkLambdaFVars #[x] (← mkNdrec v y motive p x)
        let p ← withReader (fun c => { c with hyps := c.hyps.push x })
          (premise rest unfold pending rename)
        return ← mkLambdaFVars #[x] p
      if ← isObj d then
        return ← mkLambdaFVars #[x] (← withAtom x (premise rest unfold pending rename))
      mkLambdaFVars #[x] (← premise rest unfold (pending.push x) rename)
  | _ =>
    -- The source is unfolded first, so ghosts' projections in it are seen.
    let ty ← instantiateMVars ty
    let ty := if ty.isAppOfArity ``ExprCert 14 then mkApp ty.appFn! (unfold ty.appArg!) else ty
    let unfold := id
    let some y := pending[0]? | leaf ty unfold
    -- Represent the first ghost, then the others.
    let l := (← read).lang
    let (t, Rel) ← relFor l (← inferType y)
    let x ← mkFreshExprMVar (l.val t)
    let .ok p ← represent (mkApp2 Rel x y).headBeta |
      throwError "lift: cannot represent{indentExpr y}"
    let g : Ghost := { var := y, rep := ← instantiateMVars x, proof := p }
    withReader (fun c => { c with ghosts := c.ghosts.push g }) do
      -- A relation that equates the representative with a projection of the
      -- ghost (`x = w.val`): the projection is replaced by the atom throughout
      -- the source, types included.
      let fty ← whnf (← inferType p)
      if fty.isAppOfArity ``Eq 3 then
        let lhs := fty.appFn!.appArg!
        let rhs ← repOf fty.appArg!
        if ← isAtom lhs then
          let ty ← instantiateMVars ty
          let body ← kabstract ty rhs
          if body.hasLooseBVars then
            let motive ← withLocalDeclD `z (← inferType rhs) fun z => do
              mkLambdaFVars #[z] (body.instantiate1 z)
            let q ← premise (body.instantiate1 lhs) unfold pending[1:] rename
            return ← mkNdrec lhs rhs motive q p
      premise ty unfold pending[1:] rename

/-- The conclusion of a premise, once its binders are introduced. -/
partial def leaf (ty : Lean.Expr) (unfold : Lean.Expr → Lean.Expr) : M Lean.Expr := do
  if ty.isAppOfArity ``ExprCert 14 then
    let as := ty.getAppArgs
    return ← trComp (unfold as[13]!) as[6]! as[8]! as[12]!
  if ty.isAppOfArity ``FnCert 17 then
    let src := ty.appArg!
    let some i := (← read).fns.find? (·.src == src) |
      throwError "lift: no function certificate for{indentExpr src}"
    return i.cert
  if ty.isAppOfArity ``Eq 3 then
    let lhs ← instantiateMVars ty.appFn!.appArg!
    -- An AST value to choose (`?x = erase a`) is the erasure's representative.
    unless lhs.isMVar do return ← builtinSucceeds ty
  match ← represent ty with
  | .ok p => return p
  | .error t => throwError "lift: cannot bind{indentExpr t}\nto relate it by{indentExpr ty}"

/-- A join point `let jp := fun y => body; rest`: a local closure. -/
partial def trJoin (n : Name) (ty v b s γ o R : Lean.Expr) : M Lean.Expr := do
  let ctx ← read
  let .lam _ yTy yBody _ := v | unsupported "join point" v
  if yBody.isLambda then
    throwError "lift: join points with several arguments are not supported; they come \
      from mutable variables{indentExpr v}"
  let l := ctx.lang
  let (inp, Ri) ← relFor l yTy
  let σ ← withLocalDeclD `y yTy fun y => do
    let (_, _, σ) ← asFree (← inferType (yBody.instantiate1 y))
    mkLambdaFVars #[y] σ
  let (out, Ro) ← relForDep l yTy σ
  let fnTp := mkApp2 (l.tpC ``Tp.fn) inp out
  let r ← RuleInst.new ``ExprCert.lam
  setBase r γ o R
  r.set `inp inp
  r.set `out out
  r.set `Ri Ri
  r.set `Ro Ro
  r.set `src v
  concludeIn r γ o R
  r.set `t s
  r.set `hb (← premise (← instantiateMVars (← inferType (← r.arg `hb))))
  -- The rest is certified with the join point as a plain local, substituted
  -- by a single beta-redex, so its definition is never duplicated.
  let hk ← withLocalDeclD n ty fun jS =>
    withLocalDeclD `h' (mkApp2 (mkConst ``Heap) l.L l.model) fun h' =>
    withLocalDeclD n (l.val fnTp) fun ref => do
    withLocalDeclD `hle (← mkAppM ``LE.le #[ctx.heap, h']) fun hle => do
    let certTy ← mkAppOptM ``FnCert
      #[l.L, l.model, ctx.Γ', ctx.F, none, ctx.sim, γ, γ, inp, out, yTy, σ, h', ref,
        Ri, Ro, jS]
    withLocalDeclD `hjp certTy fun hc => do
      let c ← withHeap h' hle <|
        withReader (fun x => { x with fns := x.fns.push { src := jS, cert := hc } })
          (trComp (b.instantiate1 jS) γ o R)
      let c ← instantiateMVars c
      return mkApp (← mkLambdaFVars #[jS] (← mkLambdaFVars #[h', ref, hle, hc] c)) v
  r.set `hk hk
  r.finish

end


/-! ## Programs -/

/-- A source definition `c`, instantiated at the language's parameters: the
term, its input type, its context, its result type as a function of the
argument, and its body. Parameters
are the binders before the argument; they are found by unifying the source's
effects with the language's `F`. -/
def sourceFn (c : Name) (F : Option Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := do
  let ci ← getConstInfo c
  unless ci.levelParams.isEmpty do throwError "lift: `{c}` is universe polymorphic"
  let mut ty := ci.type
  let mut ps := #[]
  repeat
    let .forallE n d b bi ← whnfR ty | break
    if bi.isExplicit then break
    let m ← mkFreshExprMVar d (userName := n)
    ps := ps.push m
    ty := b.instantiate1 m
  let .forallE n τ body _ ← whnfR ty |
    throwError "lift: `{c}` must take exactly one argument"
  -- The result type may depend on the argument; the effects and context may not.
  let (E, γ, σ) ← withLocalDeclD n τ fun x => do
    let (E, γ, σ) ← asFree (body.instantiate1 x)
    if E.containsFVar x.fvarId! || γ.containsFVar x.fvarId! then
      throwError "lift: the effects or context of `{c}` depend on its argument"
    return (E, γ, ← mkLambdaFVars #[x] σ)
  match F with
  | some F =>
    unless ← isDefEq E F do
      throwError "lift: `{c}` is not over the language's effects{indentExpr E}"
  | none =>
    unless ps.isEmpty do throwError "lift: `{c}` takes parameters, but no language is given"
  let args ← ps.mapM instantiateMVars
  if args.any (·.hasExprMVar) then
    throwError "lift: cannot determine the parameters of `{c}` from the language"
  let some val := ci.value? | throwError "lift: `{c}` has no definition"
  return (mkAppN (mkConst c) args, ← instantiateMVars τ, ← instantiateMVars γ,
    ← instantiateMVars σ, val.beta args)

/-- The context of a source: the same as the AST's. -/
def astCtx (γs : Lean.Expr) : M Lean.Expr := do
  let ctxTy := mkApp (mkConst ``Language.Ctx) (← read).lang.L
  unless ← isDefEq (← inferType γs) ctxTy do
    throwError "lift: the source's context{indentExpr γs}\nis not a context of the language"
  return γs

structure ProgCtx where
  /-- The entry point, at the language's parameters, and its body. -/
  entry : Lean.Expr
  val : Lean.Expr
  γ : Lean.Expr
  iT : Lean.Expr
  oT : Lean.Expr
  /-- The representation of the entry point's results, and its eraser,
  unfolded. -/
  rep : Lean.Expr
  eo : Lean.Expr

def setProgBase (r : RuleInst) (p : ProgCtx) : M Unit := do
  let c ← read
  setShared r
  r.set `γ p.γ
  r.set `γ' p.γ
  r.set `h c.heap
  r.set `iT p.iT
  r.set `oT p.oT
  r.set `eo p.eo
  r.set `t p.entry

def binderName (f : Lean.Expr) : Name :=
  if let .lam n .. := f then n else `x

/-- Binder names of a definition's premise: the source's for its argument. -/
def defNames (val : Lean.Expr) : Name → Option Name
  | `r => some `self
  | `x | `y | `i => some (binderName val)
  | _ => none

/-- Replace a source definition applied to an argument by its body. -/
def unfoldSrc (src val : Lean.Expr) (t : Lean.Expr) : Lean.Expr :=
  if t.isApp && t.appFn! == src then val.beta #[t.appArg!] else t

partial def trProgram (p : ProgCtx) : List Name → M Lean.Expr
  | [] => do
    let r ← RuleInst.new ``ProgCert.main
    setProgBase r p
    r.set `hb (← premise (← instantiateMVars (← inferType (← r.arg `hb))) (unfoldSrc p.entry p.val)
      (rename := defNames p.val))
    r.finish
  | c :: cs => do
    let ctx ← read
    let l := ctx.lang
    let (src, τ, γs, σ, val) ← sourceFn c (if ctx.identity then none else some ctx.F)
    let δ ← astCtx γs
    let (inp, Ri) ← relFor l τ
    let (out, Ro) ← relForDep l τ σ
    let fnTp := mkApp2 (l.tpC ``Tp.fn) inp out
    let r ← RuleInst.new ``ProgCert.define
    setProgBase r p
    r.set `δ δ
    r.set `δ' γs
    r.set `inp inp
    r.set `out out
    r.set `Ri Ri
    r.set `Ro Ro
    r.set `src src
    r.set `hb (← premise (← instantiateMVars (← inferType (← r.arg `hb))) (unfoldSrc src val)
      (rename := defNames val))
    let hk ←
      withLocalDeclD `h' (mkApp2 (mkConst ``Heap) l.L l.model) fun h' =>
      withLocalDeclD (.mkSimple c.lastComponentAsString) (l.val fnTp) fun ref => do
      withLocalDeclD `hle (← mkAppM ``LE.le #[ctx.heap, h']) fun hle => do
      let certTy ← mkAppOptM ``FnCert #[l.L, l.model, ctx.Γ', ctx.F, none, ctx.sim,
        δ, γs, inp, out, τ, σ, h', ref, Ri, Ro, src]
      withLocalDeclD `hc certTy fun hc => do
        let rest ← withHeap h' hle <|
          withReader (fun x => { x with fns := x.fns.push { src, cert := hc } })
            (trProgram p cs)
        mkLambdaFVars #[h', ref, hle, hc] rest
    r.set `hk hk
    r.finish

/-- The constant at the head of `e`, if any. -/
def headConst (e : Lean.Expr) : Array Name := e.getAppFn.constName?.toArray

/-- Lift `entry`, with the given helpers in dependency order and operation
wrappers, by the lift `l.lift` (with its parameters `ps` as free variables),
or the identity lift. Adds `name.ast` and `name.cert`. -/
def liftWith (name entry : Name) (helpers wrappers : Array Name) (l : Lang)
    (F : Lean.Expr) (identity : Bool) (ps : Array Lean.Expr)
    (extra : Array Entry) (keyed : Array (Name × Entry)) (unfoldable : Array Name) :
    Term.TermElabM Unit := do
  let (src, τ, γs, σ, val) ← sourceFn entry (if identity then none else some F)
  -- The language's contexts, as the source's effects state them, so their
  -- instances are found.
  let Γ' := (← whnf (← inferType F)).bindingDomain!
  let entries := (← staticEntries l) ++ #[← iteEntry l Γ' F] ++ extra
  let mut table : Std.HashMap Name (Array Entry) := {}
  for e in entries do
    let n ← e.head
    table := table.insert n ((table.getD n #[]).push e)
  -- Counted loops, for every language.
  let loops ← [``ExprCert.forIn', ``ExprCert.forIn'_tail, ``ExprCert.forIn,
    ``ExprCert.forIn_tail].toArray.mapM fun r => (ruleEntry r : MetaM _)
  for (n, e) in keyed ++ loops do
    table := table.insert n ((table.getD n #[]).push e)
  let sim ← mkAppOptM ``Lift.simSpec #[none, none, l.lift]
  let ctx : Ctx :=
    { lang := l, Γ', F, sim, identity
      heap := mkApp2 (mkConst ``Heap.empty) l.L l.model, table, wrappers, unfoldable }
  let (p, prf) ← (show M _ from do
    let (oT, rep, eo) ← eraserForDep l τ σ
    let p : ProgCtx :=
      { entry := src, val, γ := ← astCtx γs, iT := ← reflectAbi l τ, oT, rep, eo }
    return (p, ← instantiateMVars (← trProgram p helpers.toList))).run ctx
  -- The AST, read off the certificate and generalized over the variable type.
  let .app (.app (.app _ astSpec) _) _ ← instantiateMVars (← inferType prf) | unreachable!
  let (astVal, astTy) ←
    withLocalDecl `V .implicit (← mkArrow l.tp (mkSort Level.one)) fun V => do
      -- Values of the model, also where `Language.Model.V` was unfolded.
      let ast := astSpec.replace fun e =>
        if e.isAppOfArity ``Language.Model.V 2 then some V
        else if e.isAppOfArity ``Tp.denote 2 && e.appArg!.isAppOfArity ``Language.Model.denote 2 then
          some V
        else none
      if ast.find? (· == l.model) |>.isSome then
        throwError "lift: internal error, the generated AST depends on the model{indentExpr ast}"
      let ty ← mkAppOptM ``Program #[l.L, p.γ, p.iT, p.oT, V]
      return (← mkLambdaFVars #[V] ast, ← mkForallFVars #[V] ty)
  if astVal.hasFVar || astTy.hasFVar then
    throwError "lift: internal error, the generated AST depends on the language's \
      parameters{indentExpr astVal}"
  unless (← isTypeCorrect astVal) && (← isDefEq (← inferType astVal) astTy) do
    throwError "lift: internal error, the generated AST does not type-check{indentExpr astVal}"
  let astName := name ++ `ast
  -- Compiled too, so the AST can be evaluated, e.g. printed.
  addAndCompile <| .defnDecl
    { name := astName, levelParams := [], type := astTy, value := astVal
      hints := .regular 0, safety := .safe }
  let thm ← mkRule ``ProgramCert.of_progCert [(`L, l.L), (`M, l.model), (`ℓ, l.lift),
    (`γ, p.γ), (`iT, p.iT), (`oT, p.oT),
    (`r, p.rep), (`p, mkConst astName), (`t, src), (`hp, prf)]
  let thmTy ← instantiateMVars (← inferType thm)
  let thm ← mkLambdaFVars ps thm
  let thmTy ← mkForallFVars ps thmTy
  try
    addDecl <| .thmDecl { name := name ++ `cert, levelParams := [], type := thmTy, value := thm }
  catch ex =>
    throwError "lift: internal error, the generated certificate does not check:\n{ex.toMessageData}"

/-- Lift with the identity lift: the source is over a language's own
operations. -/
def liftIdentity (name entry : Name) (helpers wrappers : Array Name) :
    Term.TermElabM Unit := do
  let (_, _, _, _, _) ← sourceFn entry none
  let .forallE _ _ body _ ← whnfR (← getConstInfo entry).type | unreachable!
  let (E, _, _) ← asFree body
  unless E.isAppOfArity ``Language.denote 2 do
    throwError "lift: the source must be over a language's operations, got{indentExpr E}"
  let l : Lang := { L := E.getArg! 0, model := E.getArg! 1
                    lift := mkApp2 (mkConst ``Lift.id) (E.getArg! 0) (E.getArg! 1) }
  let unfoldable := headConst l.L ++ headConst l.model ++ #[``Lift.id, ``Lift.simSpec]
  liftWith name entry helpers wrappers l E true #[] #[← opEntry l] #[] unfoldable

/-- The head of a structure instance and of its fields' values, which
matching may unfold (the lift's `erase`, say). -/
def structFieldHeads (e : Lean.Expr) : MetaM (Array Name) := do
  let mut v ← whnfCore e
  if let some v' ← unfoldDefinition? v then v ← whnfCore v'
  return v.getAppArgs.foldl (fun acc a => acc ++ headConst a) (headConst e)

/-- Lift by `lift`: a definition of type `… → Lift L M`, whose parameters the
certificate is stated for. -/
def liftBy (name entry lift : Name) (helpers wrappers : Array Name) :
    Term.TermElabM Unit := do
  let ci ← getConstInfo lift
  unless ci.levelParams.isEmpty do throwError "lift: the lift `{lift}` is universe polymorphic"
  forallTelescopeReducing ci.type fun ps _ => do
    let some lv ← unfoldDefinition? (mkAppN (mkConst lift) ps) |
      throwError "lift: cannot unfold the lift `{lift}`"
    let lv ← whnfCore lv
    unless lv.isAppOf ``Lift.mk && lv.getAppNumArgs == 14 do
      throwError "lift: the lift `{lift}` must be a structure instance{indentExpr lv}"
    let as := lv.getAppArgs
    let l : Lang := { L := as[0]!, model := as[1]!, bases := ← registered lift .base
                      lift := mkAppN (mkConst lift) ps }
    let F := as[2]!
    let keyed ← (← registered lift .rule).mapM fun r => (ruleEntry r : MetaM _)
    let unfoldable := headConst l.L ++ headConst l.model ++ #[``Lift.simSpec] ++
      (← structFieldHeads l.lift)
    liftWith name entry helpers wrappers l F false ps #[] keyed unfoldable

syntax liftVia := &" via " ident
syntax liftUsing := " using " "[" ident,* "]"
syntax liftOps := &" ops " "[" ident,* "]"

/-- `lift_program foo := src [via ℓ] [using [helpers…]] [ops [wrappers…]]`
lifts `src` to an AST program `foo.ast`, with `foo.cert` its program
certificate against `src`: by the identity lift, or by the lift `ℓ` for all
of `ℓ`'s parameters. Helpers are listed callees first; the lists are
optional. -/
syntax (name := liftProgramCmd)
  "lift_program " ident " := " ident (liftVia)? (liftUsing)? (liftOps)? : command

def identsOf (stx : Option Syntax) : Term.TermElabM (Array Name) := do
  let some stx := stx | return #[]
  stx[2].getSepArgs.mapM fun i => realizeGlobalConstNoOverloadWithInfo i

elab_rules : command
  | `(lift_program $n := $e $[$v]? $[$u]? $[$o]?) => do
    let ns ← getCurrNamespace
    liftTermElabM do
      let entry ← realizeGlobalConstNoOverloadWithInfo e
      let helpers ← identsOf (u.map (·.raw))
      let wrappers ← identsOf (o.map (·.raw))
      match v with
      | some v =>
        let lift ← realizeGlobalConstNoOverloadWithInfo v.raw[1]
        liftBy (ns ++ n.getId) entry lift helpers wrappers
      | none => liftIdentity (ns ++ n.getId) entry helpers wrappers

end Freigen.Ast.Macro
