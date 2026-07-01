import Freigen.Scoped
import Freigen.Tp
import Freigen.ITree

/-!
# Wiring `FreeH` into a **dumb, typed** imperative AST with first-order functions

The `FreeH Op SOp α` program is the source of truth.  `Code`/`Prog` is a dumb imperative AST indexed
by `Tp`: instructions, reified arithmetic (`un`/`bin`), boolean branches, **calls to top-level
function definitions** (`call`/`Prog.def_`), and scoped blocks.  Functions denote as **FreeH-Kleisli
subroutines** (`HList Tp.denote as → FreeH Op SOp b.denote`).  The whole thing denotes **faithfully**
back into `FreeH` (`denoteProg (reflect foo) = foo`, `rfl`); its ITree meaning is `ofFreeH` of that,
and soundness is the uniform `≈` (`ITree.Eutt`) — `Eutt.of_eq` on the faithful denotation.
-/

namespace Freigen.Scoped

open Freigen.ITree

/-- ITree semantics of a source `FreeH` program: a scoped block is *run* inline (`bind`). -/
def ofFreeH {Op : Type → Type → Type 1} {SOp : Type → Type} :
    {α : Type} → FreeH Op SOp α → Comp Op α
  | _, .pure a    => ret a
  | _, .op o i k  => vis (Effect.mk o i) (fun r => ofFreeH (k r))
  | _, .hop _ b k => ITree.bind (ofFreeH b) (fun x => ofFreeH (k x))

/-- `ofFreeH` is a **monad morphism**: it commutes with `bind`. -/
theorem ofFreeH_bind {Op : Type → Type → Type 1} {SOp : Type → Type} {α β}
    (m : FreeH Op SOp α) (k : α → FreeH Op SOp β) :
    ofFreeH (FreeH.bind m k) = ITree.bind (ofFreeH m) (fun x => ofFreeH (k x)) := by
  induction m with
  | pure a => simp only [FreeH.bind, ofFreeH, ITree.bind_ret]
  | op o i c ih =>
      simp only [FreeH.bind, ofFreeH, ITree.bind_vis]
      exact congrArg (vis (Effect.mk o i)) (funext fun r => ih r k)
  | hop s b c _ ihc =>
      simp only [FreeH.bind, ofFreeH, ITree.bind_assoc]
      exact congrArg (ITree.bind (ofFreeH b)) (funext fun x => ihc x k)

/-- `ofFreeH` distributes over a boolean branch (needed to align `denote`'s `ite`/`cond` with the
    source, without splitting the surrounding equality). -/
theorem ofFreeH_cond {Op : Type → Type → Type 1} {SOp : Type → Type} {α}
    (c : Bool) (a b : FreeH Op SOp α) :
    ofFreeH (cond c a b) = cond c (ofFreeH a) (ofFreeH b) := by cases c <;> rfl

/-- The dumb, typed imperative AST.  `F as b` names a top-level function `as → b`; `V α` an atom. -/
inductive Code (Op : Type → Type → Type 1) (SOp : Type → Type)
    (F : List Tp → Tp → Type 1) (V : Tp → Type) : Tp → Type 1
  | ret   {α} : V α → Code Op SOp F V α
  | lit   {α β} : α.denote → (V α → Code Op SOp F V β) → Code Op SOp F V β
  | un    {α a b} : Un a b → V a → (V b → Code Op SOp F V α) → Code Op SOp F V α
  | bin   {α a b c} : Bin a b c → V a → V b → (V c → Code Op SOp F V α) → Code Op SOp F V α
  | op    {α I R} : Op I.denote R.denote → V I → (V R → Code Op SOp F V α) → Code Op SOp F V α
  | ite   {α} : V .bool → Code Op SOp F V α → Code Op SOp F V α → Code Op SOp F V α
  | call  {α as b} : F as b → HList V as → (V b → Code Op SOp F V α) → Code Op SOp F V α
  | scope {α β} : SOp β.denote → Code Op SOp F V β → (V β → Code Op SOp F V α) → Code Op SOp F V α

/-- A whole program: a telescope of pulled-out function **definitions** (`def_`) ending in `main`.
    Each `def_` binds a function name `F as b` the rest may `call`. -/
inductive Prog (Op : Type → Type → Type 1) (SOp : Type → Type)
    (F : List Tp → Tp → Type 1) (V : Tp → Type) (mainArgs : List Tp) (α : Tp) : Type 2
  | main : (HList V mainArgs → Code Op SOp F V α) → Prog Op SOp F V mainArgs α
  | def_ {as b} : (HList V as → Code Op SOp F V b) →
      (F as b → Prog Op SOp F V mainArgs α) → Prog Op SOp F V mainArgs α
  /-- A **recursive** function definition `arg → res`.  Its body lives over the **call-extended
      signature** `CallOp Op` — a self-call is the `CallOp.call` operation — so it may recur in any
      position; it is denoted by `mrec`.  The body is parametric in `F` (it reaches the recursive
      knot through `call`, not through a name).  This node's very existence makes a total `Prog →
      FreeH` map **impossible to define** (no `mrec` in an inductive monad): the AST can't promise
      termination. -/
  | rec_ {arg res} :
      (∀ F', V arg → Code (CallOp Op arg.denote res.denote) SOp F' V res) →
      (F [arg] res → Prog Op SOp F V mainArgs α) → Prog Op SOp F V mainArgs α

/-- A closed program, parametric in the function/value representations. -/
def Closed (Op : Type → Type → Type 1) (SOp : Type → Type) (mainArgs : List Tp) (α : Tp) : Type 2 :=
  ∀ F V, Prog Op SOp F V mainArgs α

/-- Comp-Kleisli: a function `as → b` denotes as a **subroutine in the interaction-tree domain**. -/
abbrev KC (Op : Type → Type → Type 1) : List Tp → Tp → Type 1 :=
  fun as b => HList Tp.denote as → Comp Op b.denote

/-- **The AST's meaning** — denote a `Code` *uniformly* into the interaction-tree domain `Comp`
    (`V := Tp.denote`, `F := KC`).  A `call` binds a subroutine's result, a scoped block runs inline;
    nothing here knows or cares whether the program (or a callee) is recursive. -/
def denote {Op : Type → Type → Type 1} {SOp : Type → Type} :
    {α : Tp} → Code Op SOp (KC Op) Tp.denote α → Comp Op α.denote
  | _, .ret v      => ret v
  | _, .lit a k    => denote (k a)
  | _, .un o a k   => denote (k (Un.denote o a))
  | _, .bin o a b k => denote (k (Bin.denote o a b))
  | _, .op o i k   => vis (Effect.mk o i) (fun r => denote (k r))
  | _, .ite c t e  => cond c (denote t) (denote e)
  | _, .call cf args k => ITree.bind (cf args) (fun r => denote (k r))
  | _, .scope _ b k => ITree.bind (denote b) (fun x => denote (k x))

/-- Denote a whole program into `Comp` — **uniformly**: `main` denotes to a function of the inputs,
    a `def_` binds its body's `Comp`-subroutine, and a **`rec_` ties the recursive knot with `mrec`**.
    There is deliberately no `FreeH`-valued analogue: `mrec` has no inductive counterpart, so a `Prog`
    cannot be denoted into a finite monad — the AST does not (and cannot) assume termination. -/
def denoteProg {Op : Type → Type → Type 1} {SOp : Type → Type} {mainArgs : List Tp} {α : Tp} :
    Prog Op SOp (KC Op) Tp.denote mainArgs α → HList Tp.denote mainArgs → Comp Op α.denote
  | .main body   => fun args => denote (body args)
  | .def_ body k => denoteProg (k (fun a => denote (body a)))
  | @Prog.rec_ _ _ _ _ _ _ arg res body k =>
      denoteProg (k (fun args =>
        mrec (fun s => denote (body (KC (CallOp Op arg.denote res.denote)) s)) (HList.head args)))

/-! ## A pretty-printer -/

abbrev PpV : Tp → Type := fun _ => String
abbrev PpF : List Tp → Tp → Type 1 := fun _ _ => ULift String
private def ppIndent (d : Nat) : String := String.join (List.replicate d "  ")

private def hlistStrings : {as : List Tp} → HList PpV as → List String
  | [],    .nil       => []
  | _::_,  .cons x xs => x :: hlistStrings xs

private def freshHList : (as : List Tp) → Nat → HList PpV as × Nat
  | [],    i => (.nil, i)
  | _::as, i => let (xs, j) := freshHList as (i + 1); (.cons s!"x{i}" xs, j)

private def ppBinders (as : List Tp) (argv : HList PpV as) : String :=
  String.intercalate ", " ((hlistStrings argv).zip (as.map Tp.toTypeStr) |>.map
    (fun (n, t) => s!"{n} : {t}"))

private def ppCode {Op : Type → Type → Type 1} {SOp : Type → Type} {α : Tp}
    (name : {I R : Type} → Op I R → String) (sname : {β : Type} → SOp β → String) :
    Nat → Nat → Code Op SOp PpF PpV α → (String × Nat)
  | d, i, .ret v      => (s!"{ppIndent d}{v}", i)
  | d, i, @Code.lit _ _ _ _ α _ a k =>
      let v := s!"v{i}"; let (r, j) := ppCode name sname d (i+1) (k v)
      (s!"{ppIndent d}let {v} := {Tp.toStr α a}\n{r}", j)
  | d, i, .un o a k =>
      let v := s!"v{i}"; let (r, j) := ppCode name sname d (i+1) (k v)
      (s!"{ppIndent d}let {v} := {Un.sym o}{a}\n{r}", j)
  | d, i, .bin o a b k =>
      let v := s!"v{i}"
      let rhs := if Bin.sym o == "," then s!"({a}, {b})"
                 else if Bin.sym o == "[]" then s!"{a}[{b}]" else s!"{a} {Bin.sym o} {b}"
      let (r, j) := ppCode name sname d (i+1) (k v)
      (s!"{ppIndent d}let {v} := {rhs}\n{r}", j)
  | d, i, .op o inp k =>
      let v := s!"v{i}"; let (r, j) := ppCode name sname d (i+1) (k v)
      (s!"{ppIndent d}let {v} ← {name o}({inp})\n{r}", j)
  | d, i, .ite c t e =>
      let (ts, j) := ppCode name sname (d+1) i t; let (es, j) := ppCode name sname (d+1) j e
      (s!"{ppIndent d}if {c} then\n{ts}\n{ppIndent d}else\n{es}", j)
  | d, i, .call cf args k =>
      let v := s!"v{i}"; let (r, j) := ppCode name sname d (i+1) (k v)
      (s!"{ppIndent d}let {v} := {cf.down}({String.intercalate ", " (hlistStrings args)})\n{r}", j)
  | d, i, .scope s b k =>
      let (bs, j) := ppCode name sname (d+1) i b
      let v := s!"v{j}"; let (r, l) := ppCode name sname d (j+1) (k v)
      (s!"{ppIndent d}let {v} ← {sname s} unconstrained\n{bs}\n{r}", l)

private def ppProg {Op : Type → Type → Type 1} {SOp : Type → Type} {mainArgs : List Tp} {α : Tp}
    (name : {I R : Type} → Op I R → String) (sname : {β : Type} → SOp β → String) :
    Nat → Prog Op SOp PpF PpV mainArgs α → (String × Nat)
  | i, @Prog.main _ _ _ _ mainArgs _ body =>
      let (argv, i) := freshHList mainArgs i
      let (b, i) := ppCode name sname 1 i (body argv)
      (s!"def main({ppBinders mainArgs argv}) =>\n{b}", i)
  | i, @Prog.def_ _ _ _ _ _ _ as _ body k =>
      let f := s!"f{i}"; let i := i + 1
      let (argv, i) := freshHList as i
      let (b, i) := ppCode name sname 1 i (body argv)
      let (rest, i) := ppProg name sname i (k (ULift.up f))
      (s!"def {f}({ppBinders as argv}) =>\n{b}\n{rest}", i)
  | i, @Prog.rec_ _ _ _ _ _ _ arg res body k =>
      let f := s!"f{i}"; let x := s!"x{i+1}"; let i := i + 2
      let callName : {I R : Type} → Freigen.ITree.CallOp Op arg.denote res.denote I R → String :=
        fun o => match o with | .base o' => name o' | .call => s!"{f} (self-call)"
      let (b, i) := ppCode callName sname 1 i (body PpF x)
      let (rest, i) := ppProg name sname i (k (ULift.up f))
      (s!"rec {f}({x} : {arg.toTypeStr}) =>\n{b}\n{rest}", i)

/-- Pretty-print a closed program. -/
def pp {Op : Type → Type → Type 1} {SOp : Type → Type}
    (name : {I R : Type} → Op I R → String) (sname : {β : Type} → SOp β → String)
    {mainArgs : List Tp} {α : Tp} (c : Closed Op SOp mainArgs α) : String :=
  (ppProg name sname 0 (c PpF PpV)).1

end Freigen.Scoped

/-! ## The `reflect%` reflector — value arm

Reflects a `FreeH Op SOp α` program (which may call top-level helper functions) into a `Prog`: pure
computation is A-normalised into `un`/`bin`/`lit`; effects/scoped blocks pass through; **calls to
helper functions become `call` nodes, monomorphised and spilled as `def_`s** (a two-pass
discovery/build). -/

namespace Freigen.Scoped
open Lean Lean.Meta Lean.Elab.Term

/-- Reify a Lean type into a `Tp` (matching the head *before* `whnf`, so `ZMod n` stays `ZMod n`). -/
partial def reifyTp (T : Expr) : MetaM (Option Expr) := do
  match_expr T with
  | Bool     => return some (.const ``Tp.bool [])
  | Nat      => return some (.const ``Tp.nat [])
  | ZMod n   => return some (mkApp (.const ``Tp.zmod []) n)
  | PUnit    => return some (.const ``Tp.unit [])
  | Unit     => return some (.const ``Tp.unit [])
  | Prod A B =>
      let some a ← reifyTp A | return none
      let some b ← reifyTp B | return none
      return some (mkApp2 (.const ``Tp.prod []) a b)
  | Vector A n =>
      let some a ← reifyTp A | return none
      return some (mkApp2 (.const ``Tp.vec []) a n)
  | Array A =>
      let some a ← reifyTp A | return none
      return some (mkApp (.const ``Tp.array []) a)
  | Sum A B =>
      let some a ← reifyTp A | return none
      let some b ← reifyTp B | return none
      return some (mkApp2 (.const ``Tp.sum []) a b)
  | _ =>
      if let .forallE _ A B _ := T then
        if B.hasLooseBVars then return none
        let some a ← reifyTp A | return none
        let some b ← reifyTp B | return none
        return some (mkApp2 (.const ``Tp.fn []) a b)
      else match ← unfoldDefinition? T with
        | some T' => reifyTp T'
        | none    => return none

/-- Reify a Lean type into a `Tp`, aborting if unsupported. -/
def reifyTpOrThrow (T : Expr) : MetaM Expr := do
  match ← reifyTp T with
  | some tp => return tp
  | none    => throwError "reflect%: type not expressible as a `Tp`:{indentExpr T}"

/-- `Bin.add`/`Bin.addZ` picking on the (reified) arithmetic result type. -/
def arithOp (natC zmodC : Name) (resTy : Expr) : MetaM (Expr × Expr) := do
  let cTp ← reifyTpOrThrow resTy
  match_expr cTp with
  | Tp.nat    => return (.const natC [], cTp)
  | Tp.zmod n => return (mkApp (.const zmodC []) n, cTp)
  | _         => throwError "reflect%: unsupported arithmetic result type{indentExpr cTp}"

/-- `Un.fst`/`Un.snd` for a value of product type. -/
def prodUn (ctor : Name) (p : Expr) : MetaM Expr := do
  match_expr ← reifyTpOrThrow (← inferType p) with
  | Tp.prod a b => return mkApp2 (.const ctor []) a b
  | _           => throwError "reflect%: projection applied to a non-product{indentExpr p}"

/-- Project the `j`-th element out of an `HList` atom (`head ∘ tailʲ`). -/
def projHList (hargs : Expr) (j : Nat) : MetaM Expr := do
  let mut h := hargs
  for _ in [0:j] do h ← mkAppM ``HList.tail #[h]
  mkAppM ``HList.head #[h]

/-- A discovered (monomorphised) function spill: name, argument object-types, result object-type,
    and the reflected body `HList V as → Code …`. -/
structure DefEntry where
  name    : Name
  asList  : Expr
  retTp   : Expr
  bodyLam : Expr
  deriving Inhabited

/-- The reflection environment: the abstract `Op`/`SOp`/`F`/`V` we build against, a substitution
    from continuation-bound host placeholders to object atoms, the running spill cache, whether we
    are inside a function body (bodies may not call), and — on the build pass — the resolved names. -/
structure Env where
  Op : Expr
  SOp : Expr
  F : Expr
  V : Expr
  subst : List (FVarId × Expr)
  defs : IO.Ref (Array DefEntry)
  /-- Every source definition the reflector unfolds (helpers, smart-constructors, the program itself).
      Emitted into the soundness `simp` set so the source side unfolds to the same tree the AST does. -/
  defsUsed : IO.Ref (Array Name)
  inBody : Bool := false
  resolved : Option (Array (DefEntry × Expr)) := none

/-- Emit a `ret` node returning the atom. -/
def Env.mkRet (env : Env) (atom : Expr) : MetaM Expr :=
  mkAppOptM ``Code.ret #[env.Op, env.SOp, env.F, env.V, none, atom]

/-- Bind a host literal `a : αTp.denote` as an atom. -/
def Env.mkLitBind (env : Env) (a αTp : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
  withLocalDeclD `v (mkApp env.V αTp) fun vx => do
    let lam ← mkLambdaFVars #[vx] (← k vx)
    mkAppOptM ``Code.lit #[env.Op, env.SOp, env.F, env.V, αTp, none, a, lam]

/-- Build the argument tuple `HList V [tps]` from already-reflected atoms. -/
def Env.mkArgHList (env : Env) (atoms : List Expr) : MetaM Expr := do
  let mut h ← mkAppOptM ``HList.nil #[none, env.V]
  for a in atoms.reverse do h ← mkAppM ``HList.cons #[a, h]
  pure h

/-- Emit a `call cf args k`, binding the result atom for the continuation. -/
def Env.emitCall (env : Env) (cf asList retTp hl : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
  let contLam ← withLocalDeclD `r (mkApp env.V retTp) fun vr => do mkLambdaFVars #[vr] (← k vr)
  mkAppOptM ``Code.call #[env.Op, env.SOp, env.F, env.V, none, asList, retTp, cf, hl, contLam]

mutual
  /-- Reflect a *pure* host value into a `Code` atom, A-normalising arithmetic into `un`/`bin`/`lit`
      chains, then feed the atom to `k`. -/
  partial def Env.reflectAtom (env : Env) (a : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
    let a ← instantiateMVars a
    if let .fvar fid := a then
      if let some atom := env.subst.lookup fid then return ← k atom
    if !(a.hasAnyFVar fun fid => (env.subst.lookup fid).isSome) then
      return ← env.mkLitBind a (← reifyTpOrThrow (← inferType a)) k
    match_expr a with
    | HMul.hMul _ _ _ _ x y => let (o,c) ← arithOp ``Bin.mul ``Bin.mulZ (← inferType a); env.reflectBin o c x y k
    | HAdd.hAdd _ _ _ _ x y => let (o,c) ← arithOp ``Bin.add ``Bin.addZ (← inferType a); env.reflectBin o c x y k
    | HSub.hSub _ _ _ _ x y => let (o,c) ← arithOp ``Bin.sub ``Bin.subZ (← inferType a); env.reflectBin o c x y k
    | HPow.hPow _ _ _ _ x y => env.reflectBin (.const ``Bin.pow []) (.const ``Tp.nat []) x y k
    | BEq.beq _ _ x y       => env.reflectBin (.const ``Bin.eq []) (.const ``Tp.bool []) x y k
    | Bool.and x y          => env.reflectBin (.const ``Bin.and []) (.const ``Tp.bool []) x y k
    | Bool.or  x y          => env.reflectBin (.const ``Bin.or []) (.const ``Tp.bool []) x y k
    | Bool.not x            => env.reflectUn (.const ``Un.not []) (.const ``Tp.bool []) x k
    | Prod.mk _ _ x y =>
        let aTp ← reifyTpOrThrow (← inferType x); let bTp ← reifyTpOrThrow (← inferType y)
        env.reflectBin (mkApp2 (.const ``Bin.pair []) aTp bTp) (mkApp2 (.const ``Tp.prod []) aTp bTp) x y k
    | Prod.fst _ _ p => env.reflectUn (← prodUn ``Un.fst p) (← reifyTpOrThrow (← inferType a)) p k
    | Prod.snd _ _ p => env.reflectUn (← prodUn ``Un.snd p) (← reifyTpOrThrow (← inferType a)) p k
    | Sum.inl A B x =>
        let aTp ← reifyTpOrThrow A; let bTp ← reifyTpOrThrow B
        env.reflectUn (mkApp2 (.const ``Un.inl []) aTp bTp) (mkApp2 (.const ``Tp.sum []) aTp bTp) x k
    | Sum.inr A B x =>
        let aTp ← reifyTpOrThrow A; let bTp ← reifyTpOrThrow B
        env.reflectUn (mkApp2 (.const ``Un.inr []) aTp bTp) (mkApp2 (.const ``Tp.sum []) aTp bTp) x k
    | _ => throwError "reflect%: cannot reflect operand (not an atom or supported primitive):{indentExpr a}"

  /-- Reflect a binary primitive: reflect both operands to atoms, emit a `bin` node. -/
  partial def Env.reflectBin (env : Env) (binOp cTp x y : Expr) (k : Expr → MetaM Expr) : MetaM Expr :=
    env.reflectAtom x fun ax =>
    env.reflectAtom y fun ay =>
    withLocalDeclD `v (mkApp env.V cTp) fun vc => do
      let lam ← mkLambdaFVars #[vc] (← k vc)
      mkAppOptM ``Code.bin #[env.Op, env.SOp, env.F, env.V, none, none, none, none, binOp, ax, ay, lam]

  /-- Reflect a unary primitive: reflect the operand to an atom, emit a `un` node. -/
  partial def Env.reflectUn (env : Env) (unOp cTp x : Expr) (k : Expr → MetaM Expr) : MetaM Expr :=
    env.reflectAtom x fun ax =>
    withLocalDeclD `v (mkApp env.V cTp) fun vc => do
      let lam ← mkLambdaFVars #[vc] (← k vc)
      mkAppOptM ``Code.un #[env.Op, env.SOp, env.F, env.V, none, none, none, unOp, ax, lam]

  /-- Reflect a list of argument values into their atoms. -/
  partial def Env.reflectArgList (env : Env) : List Expr → (List Expr → MetaM Expr) → MetaM Expr
    | [],      k => k []
    | a :: as, k => env.reflectAtom a (fun atom => env.reflectArgList as (fun atoms => k (atom :: atoms)))

  /-- Reflect a `FreeH Op SOp _` computation into a `Code`; `k` consumes the result atom. -/
  partial def Env.walkProg (env : Env) (e : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
    let e := e.consumeMData.headBeta
    if let .letE _ _ v b _ := e then return ← env.walkProg (b.instantiate1 v) k
    match_expr e with
    | FreeH.pure _ _ _ a       => env.reflectAtom a k
    | Pure.pure _ _ _ a        => env.reflectAtom a k
    | Bind.bind _ _ _ _ x f    => env.walkBind x f k
    | FreeH.bind _ _ _ _ x f   => env.walkBind x f k
    | cond _ c t e             => env.walkIte c t e k
    | FreeH.op _ _ _ I R o i cont =>
        env.reflectAtom i (fun ia => env.walkOp I R o ia cont k)
    | FreeH.hop _ _ _ β s b cont => env.walkScope β s b cont k
    | _ =>
        match ← env.tryCall e k with
        | some prog => pure prog
        | none => match ← unfoldDefinition? e with
          | some e' =>
              if let some n := e.getAppFn.constName? then env.defsUsed.modify (·.push n)
              env.walkProg e' k
          | none    => throwError "reflect%: don't know how to reflect computation{indentExpr e}"

  /-- Reflect a `bind x f`; a pure `x` is inlined via left-identity. -/
  partial def Env.walkBind (env : Env) (x f : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
    match_expr x.consumeMData.headBeta with
    | FreeH.pure _ _ _ a => env.walkProg (f.beta #[a]) k
    | Pure.pure _ _ _ a  => env.walkProg (f.beta #[a]) k
    | _                  => env.walkProg x (fun xa => env.walkBindCont f xa k)

  /-- Continue a `bind`: apply the binder to a host placeholder rewritten to the bound atom. -/
  partial def Env.walkBindCont (env : Env) (f xa : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
    let .forallE _ X _ _ := (← whnf (← inferType f))
      | throwError "reflect%: expected a continuation function{indentExpr f}"
    withLocalDeclD `h X fun hx =>
      { env with subst := (hx.fvarId!, xa) :: env.subst }.walkProg (f.beta #[hx]) k

  /-- Emit an `op` node. -/
  partial def Env.walkOp (env : Env) (I R o ia cont : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
    let ITp ← reifyTpOrThrow I
    let RTp ← reifyTpOrThrow R
    let .forallE _ Rt _ _ := (← whnf (← inferType cont))
      | throwError "reflect%: expected an op continuation{indentExpr cont}"
    withLocalDeclD `v (mkApp env.V RTp) fun vx =>
    withLocalDeclD `h Rt fun hx => do
      let env' := { env with subst := (hx.fvarId!, vx) :: env.subst }
      let lam ← mkLambdaFVars #[vx] (← env'.walkProg (cont.beta #[hx]) k)
      mkAppOptM ``Code.op #[env.Op, env.SOp, env.F, env.V, none, ITp, RTp, o, ia, lam]

  /-- Emit a `scope` node: reflect the block into a `Code` (ending in `ret`), then the tail. -/
  partial def Env.walkScope (env : Env) (β s b cont : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
    let βTp ← reifyTpOrThrow β
    let blockCode ← env.walkProg b (env.mkRet ·)
    let .forallE _ Xt _ _ := (← whnf (← inferType cont))
      | throwError "reflect%: expected a scope continuation{indentExpr cont}"
    withLocalDeclD `v (mkApp env.V βTp) fun vx =>
    withLocalDeclD `h Xt fun hx => do
      let env' := { env with subst := (hx.fvarId!, vx) :: env.subst }
      let lam ← mkLambdaFVars #[vx] (← env'.walkProg (cont.beta #[hx]) k)
      mkAppOptM ``Code.scope #[env.Op, env.SOp, env.F, env.V, none, βTp, s, blockCode, lam]

  /-- Emit an `ite`: reflect the scrutinee atom, walk both branches with the same continuation. -/
  partial def Env.walkIte (env : Env) (c t e : Expr) (k : Expr → MetaM Expr) : MetaM Expr :=
    env.reflectAtom c fun ca => do
      let t' ← env.walkProg t k
      let e' ← env.walkProg e k
      mkAppOptM ``Code.ite #[env.Op, env.SOp, env.F, env.V, none, ca, t', e']

  /-- Try to reflect `e` as a **call** to a top-level helper function: classify binders into type
      parameters vs value arguments, monomorphise on `(name, arg-tps, ret-tp)`, spill the specialised
      body as a `def_` (discovery pass) or emit a `call` to its resolved name (build pass). -/
  partial def Env.tryCall (env : Env) (e : Expr) (k : Expr → MetaM Expr) : MetaM (Option Expr) := do
    if env.inBody then return none
    let fn := e.getAppFn
    let some cName := fn.constName? | return none
    let some ci := (← getEnv).find? cName | return none
    let some cVal := ci.value? | return none
    let fArgs := e.getAppArgs
    let cValInst := cVal.instantiateLevelParams ci.levelParams fn.constLevels!
    match_expr ← whnf (cValInst.beta fArgs) with
    | FreeH.op _ _ _ _ _ _ _ _ => return none      -- effect smart-constructors (→ `op`) inline
    | FreeH.hop _ _ _ _ _ _ _   => return none      -- scoped constructs (→ `scope`) inline
    | _ => pure ()
    let valuePos ← forallTelescope (← inferType fn) fun xs cod => do
      let mut vps : Array Nat := #[]
      for i in [0:xs.size] do
        let mut dep := cod.containsFVar xs[i]!.fvarId!
        for j in [i+1:xs.size] do
          if (← inferType xs[j]!).containsFVar xs[i]!.fvarId! then dep := true
        unless dep do vps := vps.push i
      pure vps
    if valuePos.size == 0 then return none
    env.defsUsed.modify (·.push cName)     -- the helper is `call`-spilled; unfold it on the source side
    let valueArgs := valuePos.toList.map (fArgs[·]!)
    let mut argTps : Array Expr := #[]
    for va in valueArgs do
      let some t ← reifyTp (← inferType va) | return none
      argTps := argTps.push t
    let asList ← mkListLit (.const ``Tp []) argTps.toList
    let some retTp ← (match_expr (← whnf (← inferType e)) with
                        | FreeH _ _ R => reifyTp R | _ => pure none) | return none
    let sigMatches (d : DefEntry) : MetaM Bool :=
      return d.name == cName && (← isDefEq d.asList asList) && (← isDefEq d.retTp retTp)
    let emit (cf : Expr) : MetaM Expr :=
      env.reflectArgList valueArgs (fun atoms => do
        env.emitCall cf asList retTp (← env.mkArgHList atoms) k)
    match env.resolved with
    | some resolved =>
        let some (_, cf) ← resolved.findM? (fun de => sigMatches de.1) | return none
        some <$> emit cf
    | none =>
        unless (← (← env.defs.get).findM? sigMatches).isSome do
          let hlistTy ← mkAppM ``HList #[env.V, asList]
          let bodyLam ← withLocalDeclD `args hlistTy fun hargs => do
            let decls : Array (Name × (Array Expr → MetaM Expr)) :=
              valueArgs.toArray.map (fun va => (`x, fun _ => inferType va))
            withLocalDeclsD decls fun hxs => do
              let mut subst := env.subst
              for j in [0:hxs.size] do
                subst := (hxs[j]!.fvarId!, ← projHList hargs j) :: subst
              let mut fullArgs := fArgs
              for j in [0:valuePos.size] do
                fullArgs := fullArgs.set! (valuePos[j]!) hxs[j]!
              let env' := { env with subst, inBody := true }
              mkLambdaFVars #[hargs] (← env'.walkProg (cValInst.beta fullArgs) (env.mkRet ·))
          env.defs.modify (·.push { name := cName, asList, retTp, bodyLam })
        some <$> emit (← mkFreshExprMVar (mkApp2 env.F asList retTp))
end

/-- Reflect a program `foo : A₁ → … → Aₙ → FreeH Op SOp X` (`n ≥ 0`; each `Aᵢ` a non-dependent
    `Tp`-type) into `{ g : Closed // ∀ args, ofFreeH (denoteProg (g KF Tp.denote) ⟨args⟩) ≈
    ofFreeH (foo args) }` — the `Prog` whose `main` is a function of the program's inputs (delivered
    as an `HList`), with a `def_` per monomorphised helper.  The non-recursive arm of `reflect%`. -/
def reflectMain (foo : Expr) : TermElabM Expr := do
  forallTelescope (← inferType foo) fun args codom => do
    let_expr FreeH Op SOp X := (← whnf codom)
      | throwError "reflect%: the body must have type `FreeH Op SOp _`, got{indentExpr codom}"
    let _ ← reifyTpOrThrow X
    -- `main`'s inputs must be monomorphic and non-dependent (no type-parameter arguments)
    for i in [0:args.size] do
      if X.containsFVar args[i]!.fvarId! then
        throwError "reflect%: `main`'s result type may not depend on its arguments"
      for j in [i+1:args.size] do
        if (← inferType args[j]!).containsFVar args[i]!.fvarId! then
          throwError "reflect%: `main` may not take a type-parameter argument\
                      {indentExpr (← inferType args[i]!)}"
    let mut mainArgTps : Array Expr := #[]
    for a in args do mainArgTps := mainArgTps.push (← reifyTpOrThrow (← inferType a))
    let tpTy := (.const ``Tp [] : Expr)
    let mainArgsList ← mkListLit tpTy mainArgTps.toList
    let fTy ← mkArrow (← mkAppM ``List #[tpTy]) (← mkArrow tpTy (mkSort (.succ (.succ .zero))))
    let vTy ← mkArrow tpTy (mkSort (.succ .zero))
    let defs ← IO.mkRef (#[] : Array DefEntry)
    let defsUsed ← IO.mkRef (#[] : Array Name)
    let denoteV := Lean.mkConst ``Tp.denote []
    let topBody := (← unfoldDefinition? (foo.beta args)).getD (foo.beta args)
    let g ← withLocalDeclD `F fTy fun F => withLocalDeclD `V vTy fun V => do
      let hlistTy ← mkAppM ``HList #[V, mainArgsList]
      -- walk `main` under an argument tuple `hargs`, substituting each host argument for its atom
      let walkMain (resolved : Option (Array (DefEntry × Expr))) (hargs : Expr) : MetaM Expr := do
        let mut subst : List (FVarId × Expr) := []
        for i in [0:args.size] do subst := (args[i]!.fvarId!, ← projHList hargs i) :: subst
        let env : Env := { Op, SOp, F, V, subst, defs, defsUsed, resolved }
        env.walkProg topBody (env.mkRet ·)
      let _ ← withLocalDeclD `args hlistTy fun h => walkMain none h    -- pass 1: discovery
      let entries ← defs.get
      let prog ← withLocalDeclsD (entries.map fun d => (`f, fun _ => pure (mkApp2 F d.asList d.retTp)))
        fun cfs => do                                                  -- pass 2: build
          let resolved := entries.zip cfs
          let mainLam ← withLocalDeclD `args hlistTy fun h => do
            mkLambdaFVars #[h] (← walkMain (some resolved) h)
          let mut prog ← mkAppOptM ``Prog.main #[Op, SOp, F, V, mainArgsList, none, mainLam]
          for j in [0:entries.size] do
            let (d, cf) := resolved[entries.size - 1 - j]!
            prog ← mkAppOptM ``Prog.def_
              #[Op, SOp, F, V, mainArgsList, none, d.asList, d.retTp, d.bodyLam, ← mkLambdaFVars #[cf] prog]
          pure prog
      mkLambdaFVars #[F, V] prog
    let gTy ← inferType g
    let kc ← mkAppM ``KC #[Op]
    -- the actual arguments as an `HList Tp.denote mainArgs`, for the soundness statement
    let mut argHList ← mkAppOptM ``HList.nil #[none, denoteV]
    for (a, t) in (args.zip mainArgTps).reverse do
      argHList ← mkAppOptM ``HList.cons #[none, denoteV, t, none, a, argHList]
    let ofFreeHead ← mkAppOptM ``ofFreeH #[Op, SOp, X]
    -- soundness  fun g => ∀ args, denoteProg (g KC Tp.denote) ⟨args⟩ ≈ ofFreeH (foo args)
    -- — `denoteProg` lands in `Comp` *directly*; `ofFreeH` only embeds the source `FreeH`.
    let pred ← withLocalDeclD `g gTy fun gv => do
      let lhs ← mkAppOptM ``denoteProg #[Op, SOp, none, none, mkAppN gv #[kc, denoteV], argHList]
      let eutt ← mkAppM ``ITree.Eutt #[lhs, mkApp ofFreeHead (foo.beta args)]
      mkLambdaFVars #[gv] (← mkForallFVars args eutt)
    -- proof: `denoteProg (g KC ⟨args⟩) = ofFreeH (foo args)` directly — `denote`/`denoteProg` and
    -- `ofFreeH` unfold to the same tree, the `call`-binds fusing via `bind_ret`/`bind_vis`.
    let dpC ← mkAppOptM ``denoteProg #[Op, SOp, none, none, mkAppN g #[kc, denoteV], argHList]
    let eqTy ← mkEq dpC (mkApp ofFreeHead (foo.beta args))
    -- compositional bisimulation: unfold `denoteProg`/`denote` and `ofFreeH`/`ofFreeH_bind` on *both*
    -- sides, plus every source definition the reflector touched, so scope- and call-binds fuse
    -- consistently and the two `Comp` trees converge.
    if let some n := foo.getAppFn.constName? then defsUsed.modify (·.push n)
    let usedIdents := (← defsUsed.get).toList.eraseDups.toArray.map (Lean.mkIdent ·)
    let eqPrf ← elabTermEnsuringType (← `(by
      simp only [Freigen.Scoped.denoteProg, Freigen.Scoped.denote, Freigen.Scoped.ofFreeH,
        Freigen.Scoped.ofFreeH_bind, Freigen.Scoped.ofFreeH_cond, Freigen.ITree.bind_ret,
        Freigen.ITree.bind_vis, Freigen.ITree.bind_assoc, Freigen.Scoped.HList.head,
        Freigen.Scoped.HList.tail, Freigen.Scoped.Bin.denote, Freigen.Scoped.Un.denote,
        Freigen.Scoped.FreeH.bind, Freigen.Scoped.FreeH.perform, bind, pure, Bind.bind, Pure.pure,
        $[$usedIdents:ident],*])) (some eqTy)
    let prf ← mkLambdaFVars args (← mkAppM ``ITree.Eutt.of_eq #[eqPrf])
    mkAppOptM ``Subtype.mk #[gTy, pred, g, prf]

end Freigen.Scoped
