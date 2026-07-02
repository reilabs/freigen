import Freigen.Ast
import Freigen.Free
import Freigen.ITree
import Freigen.Reflect.Sound
/-! ## The `reflect%` reflector — value arm

Reflects a `Free Op SOp α` program (which may call top-level helper functions) into a `Prog`: pure
computation is A-normalised into `un`/`bin`/`lit`; effects/scoped blocks pass through; **calls to
helper functions — `Free`-valued *or pure* — become `call` nodes, monomorphised and spilled as
`def_`s** (definitions are *kept folded*; helper bodies may call other helpers, spilled in
dependency order — a two-pass discovery/build).  A reifiable pure `let` keeps its sharing.

**One walk, two modes.**  A single walk (`Env.walk`/`Env.atom`) serves both jobs, selected by
`Env.pf`:

* **Abstract mode** (`pf := false`): build the `Code` against opaque `F`/`V` — the parametric `g`
  and (in `tryCall`) the spilled helper bodies.  A closed value must be bound via `Code.lit` (a host
  value is not a `V α`).  No proofs are produced.
* **Proof mode** (`pf := true`, at `V := Tp.denote`, `F := KC Op`): re-walk the source and *also*
  return, at every node, the equation of the invariant

  ```
  denote code = bind (ofFree e) Kf        -- (★)   Kf = the reflected continuation's denotation
  ```

  assembled from the sub-terms' equations by that node's congruence lemma (`sc_op`, `sc_bind`, …).
  Every non-`get`/`set` atom step is *definitional* (`denote (Code.bin …) = denote (k …)` is `rfl`),
  so a proof-erased get/set/cast contributes the only real step: `sc_vget … h` = `dif_pos h`, the
  **source's own** in-bounds proof taken straight from the term — no `simp`, no decidability, sound
  for a symbolic index at any depth.  A closed value is fed *directly* (no `Code.lit` node —
  denotationally identical, and a literal index/collection keeps the source proof fitting).  The
  proof-mode code is definitionally the concrete specialisation of the abstract `g`, so the
  top-level (★) (`k = ret`, `Kf = ret`) *is* `denoteProg (g KC Tp.denote) ⟨args⟩ = ofFree (foo args)`.

Supporting a new source form is therefore **one** arm in `Env.atom` (or `Env.walk`) calling **one**
emitter — both modes share the code path, so they cannot drift apart. -/

namespace Freigen
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
  | Fin n => return some (mkApp (.const ``Tp.fin []) n)
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

/-- A call-site analysis of a **spillable helper** — a `Free`-valued function or a *pure* function
    of reifiable signature (definitions are **kept folded**: both spill as `def_`s).  Carries
    everything needed to *rebuild* the helper's body at fresh binders (bodies are rebuilt on the
    resolution pass, since they may themselves call earlier-spilled helpers). -/
structure CallSig where
  cName     : Name
  cValInst  : Expr
  fArgs     : Array Expr
  valuePos  : Array Nat
  valueArgs : List Expr
  /-- Host types of the value arguments (fresh-binder types for body rebuilds). -/
  argTys    : Array Expr
  argTps    : Array Expr
  asList    : Expr
  retTp     : Expr
  /-- A pure helper (result reifies to a `Tp` directly) vs a `Free` computation. -/
  isPure    : Bool
  deriving Inhabited

/-- The proof-mode helper cache entry: a helper's concrete subroutine `cf` and its parametric
    equation `bodyProof : ∀ hargs, cf hargs = ofFree …` (Free) / `… = ret …` (pure), built **once**
    per monomorphised signature and reused at every call site. -/
structure PfDefEntry where
  name      : Name
  asList    : Expr
  retTp     : Expr
  cf        : Expr
  bodyProof : Expr
  deriving Inhabited

/-- The reflection environment: the `Op`/`SOp`/`F`/`V` we build against, a substitution from
    continuation-bound host placeholders to object atoms, the running spill cache (in dependency
    post-order — callees precede callers, as `Prog.def_` scoping requires), the in-flight set (for
    cycle detection), on the build pass the resolved `F`-names, and the walk **mode** (`pf`). -/
structure Env where
  Op : Expr
  SOp : Expr
  F : Expr
  V : Expr
  subst : List (FVarId × Expr)
  defs : IO.Ref (Array CallSig)
  /-- Proof-mode helper cache (`cf` + body equation per monomorphised signature). -/
  pfDefs : IO.Ref (Array PfDefEntry)
  /-- Helpers whose bodies are currently being walked — a name re-entering is a recursive helper,
      which cannot spill (no `μ`); reported as an error. -/
  inFlight : IO.Ref (Array Name)
  /-- No `def_` telescope is available (the recursion arm): helper calls inline instead of
      spilling. -/
  noSpill : Bool := false
  resolved : Option (Array (CallSig × Expr)) := none
  /-- **Proof mode**: the walk runs at the concrete representation (`V := Tp.denote`, `F := KC Op`)
      and every step also returns its (★)-equation. -/
  pf : Bool := false

/-- One step of the walk: the built `Code`, and — in proof mode — its (★)-equation. -/
abbrev CodePf := Expr × Option Expr

/-- Bind a host literal `a : αTp.denote` as an atom (abstract mode only — proof mode feeds closed
    values directly). -/
def Env.mkLitBind (env : Env) (a αTp : Expr) (k : Expr → MetaM CodePf) : MetaM CodePf := do
  withLocalDeclD `v (mkApp env.V αTp) fun vx => do
    let (kcode, _) ← k vx
    let lam ← mkLambdaFVars #[vx] kcode
    return (← mkAppOptM ``Code.lit #[env.Op, env.SOp, env.F, env.V, αTp, none, a, lam], none)

/-- Build the argument tuple `HList V [tps]` from already-reflected atoms. -/
def Env.mkArgHList (env : Env) (atoms : List Expr) : MetaM Expr := do
  let mut h ← mkAppOptM ``HList.nil #[none, env.V]
  for a in atoms.reverse do h ← mkAppM ``HList.cons #[a, h]
  pure h

/-- Extract the elements of a `List` literal (`e₀ :: … :: []`). -/
partial def listLitElems : Expr → Option (List Expr)
  | e => match e.getAppFnArgs with
    | (``List.nil, _)            => some []
    | (``List.cons, #[_, x, xs]) => (listLitElems xs).map (x :: ·)
    | _                          => none

/-- Extract elements of a `List`/`Array` literal (`#[…]` = `List.toArray […]`). -/
def seqLitElems (e : Expr) : Option (List Expr) :=
  match e.getAppFnArgs with
  | (``List.toArray, #[_, lst]) => listLitElems lst
  | _                           => listLitElems e

/-- Build a `Vector (V a) n` atom-vector from element atoms (`⟨#[atoms], rfl⟩`). -/
def mkVecOfAtoms (V aTp nExpr : Expr) (atoms : List Expr) : MetaM Expr := do
  let elemTy := mkApp V aTp
  let arrExpr ← mkAppM ``List.toArray #[← mkListLit elemTy atoms]
  let proof ← mkExpectedTypeHint (← mkEqRefl nExpr) (← mkEq (← mkAppM ``Array.size #[arrExpr]) nExpr)
  mkAppOptM ``Vector.mk #[elemTy, nExpr, arrExpr, proof]

/-- Extract a `Nat` literal — raw (`.lit`), `OfNat.ofNat`-wrapped, or wrapping a raw literal. -/
def natLitOf (e : Expr) : Option Nat :=
  e.rawNatLit? <|> e.nat? <|> (match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_, n, _]) => n.rawNatLit? <|> n.nat?
    | _                          => none)

/-- The `Fin n` literal `⟨k, by decide⟩`. -/
def mkFinLit (nExpr : Expr) (k : Nat) : MetaM Expr := do
  mkAppOptM ``Fin.mk #[nExpr, mkNatLit k, ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit k, nExpr])]

/-- Normalise a collection index to `(Nat-index, optional in-bounds proof)`: a `Fin n` index becomes
    `i.val` with `i.isLt`; a `Nat` index passes through unchanged. -/
def finIndexToNat (i : Expr) : MetaM (Expr × Option Expr) := do
  match_expr ← whnf (← inferType i) with
  | Fin _ => return (← mkAppM ``Fin.val #[i], some (← mkAppM ``Fin.isLt #[i]))
  | _     => return (i, none)

/-- Emit a `call cf args k`, binding the result atom for the continuation. -/
def Env.emitCall (env : Env) (cf asList retTp hl : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
  let contLam ← withLocalDeclD `r (mkApp env.V retTp) fun vr => do mkLambdaFVars #[vr] (← k vr)
  mkAppOptM ``Code.call #[env.Op, env.SOp, env.F, env.V, none, asList, retTp, cf, hl, contLam]

/-- `denote code` as an `Expr`. -/
private def denoteE (c : Expr) : MetaM Expr := mkAppM ``denote #[c]

/-- A `ret` continuation with the result `Tp` given **explicitly** — needed at `V := Tp.denote`,
    where `α` cannot be recovered from a raw-typed atom by unifying `Tp.denote ?α`. -/
def Env.mkRetT (env : Env) (resTp : Expr) : Expr → MetaM Expr := fun atom =>
  mkAppOptM ``Code.ret #[env.Op, env.SOp, env.F, env.V, resTp, atom]

/-- `Kf := fun (r : X) => denote (k r)` — the reflected continuation's denotation. -/
private def mkKf (_V : Expr) (X : Expr) (k : Expr → MetaM Expr) : MetaM Expr :=
  withLocalDeclD `r X fun r => do mkLambdaFVars #[r] (← denoteE (← k r))

/-- Lift a code-only continuation to a `CodePf` one; in proof mode its step is `rfl`
    (`denote (k atom) = denote (k atom)`). -/
def Env.liftK (env : Env) (k : Expr → MetaM Expr) : Expr → MetaM CodePf := fun atom => do
  let c ← k atom
  if env.pf then return (c, some (← mkEqRefl (← denoteE c)))
  else return (c, none)

/-- Bind the host-side placeholder for a continuation result: in proof mode the atom variable *is*
    the host value (`V := Tp.denote`), so it is reused; in abstract mode `V` is opaque, so a separate
    host placeholder of type `hostTy` is bound (to be mapped to the atom via `subst`). -/
def Env.withHostVar {α} (env : Env) (hostTy vx : Expr) (f : Expr → MetaM α) : MetaM α :=
  if env.pf then f vx else withLocalDeclD `h hostTy fun hx => f hx

/-- Build `HList V [tps]` from atoms with the `Tp` indices given **explicitly** — at `V := Tp.denote`
    the index can't be recovered from a raw-typed atom. -/
private def mkArgHListT (V : Expr) : List Expr → List Expr → MetaM Expr
  | [],      []      => mkAppOptM ``HList.nil #[none, V]
  | a :: as, t :: ts => do
      let tail ← mkArgHListT V as ts
      mkAppOptM ``HList.cons #[none, V, t, ← mkListLit (.const ``Tp []) ts, a, tail]
  | _, _ => throwError "reflect%: argument/type length mismatch"

/-- The result Lean type `X` of a source `e : Free Op SOp X`. -/
private def freeResult (e : Expr) : MetaM Expr := do
  let_expr Free _ _ X := (← whnf (← inferType e)) | throwError "reflect%: not a `Free`{indentExpr e}"
  pure X

/-- `Eq.trans` tolerant of a *definitional* mismatch at the shared point: the `denote`-of-a-node steps
    are only defeq (a `Code.bin`/`vget` node reduces to its continuation), so coerce `h2`'s LHS to
    `h1`'s RHS before chaining. -/
private def eqTransD (h1 h2 : Expr) : MetaM Expr := do
  let_expr Eq _ _ b := (← inferType h1) | throwError "reflect%: eqTransD h1 not an Eq"
  let_expr Eq _ _ c := (← inferType h2) | throwError "reflect%: eqTransD h2 not an Eq"
  mkAppM ``Eq.trans #[h1, ← mkExpectedTypeHint h2 (← mkEq b c)]

/-- Classify `e` as a call to a spillable top-level helper: a constant with a value, whose result
    is a `Free` computation (but not an effect/scoped smart-constructor — those inline) **or** a
    plain reifiable `Tp` (a pure helper), with at least one value argument, all value arguments
    reifying to `Tp`s.  `none` means "not a call — keep unfolding". -/
def analyzeCall (e : Expr) : MetaM (Option CallSig) := do
  let fn := e.getAppFn
  let some cName := fn.constName? | return none
  let some ci := (← getEnv).find? cName | return none
  let some cVal := ci.value? | return none
  let fArgs := e.getAppArgs
  let cValInst := cVal.instantiateLevelParams ci.levelParams fn.constLevels!
  let resTy ← inferType e
  let (retTp?, isPure) ← do
    match_expr ← whnf resTy with
    | Free _ _ R => pure (← reifyTp R, false)
    | _ => pure (← reifyTp resTy, true)     -- reify *before* whnf, so `ZMod n` stays `ZMod n`
  let some retTp := retTp? | return none
  unless isPure do
    match_expr ← whnf (cValInst.beta fArgs) with
    | Free.op _ _ _ _ _ _ _ _ => return none      -- effect smart-constructors (→ `op`) inline
    | Free.hop _ _ _ _ _ _ _   => return none      -- scoped constructs (→ `scope`) inline
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
  let valueArgs := valuePos.toList.map (fArgs[·]!)
  let mut argTys : Array Expr := #[]
  let mut argTps : Array Expr := #[]
  for va in valueArgs do
    let ty ← inferType va
    let some t ← reifyTp ty | return none
    argTys := argTys.push ty
    argTps := argTps.push t
  let asList ← mkListLit (.const ``Tp []) argTps.toList
  return some { cName, cValInst, fArgs, valuePos, valueArgs, argTys, argTps, asList, retTp, isPure }

/-- Two spill signatures match: same helper, defeq (monomorphised) argument/result `Tp`s. -/
def sigsMatch (d sig : CallSig) : MetaM Bool :=
  return d.cName == sig.cName && (← isDefEq d.asList sig.asList) && (← isDefEq d.retTp sig.retTp)

mutual
  /-- Reflect a *pure* host value into a `Code` atom, A-normalising into `un`/`bin`/`lit`/collection
      node chains, then feed the atom to `k`.  In proof mode the continuation also returns the step's
      equation, so proofs thread through in one pass; every non-`get`/`set` step is definitional, and
      a get/set/cast inserts exactly `sc_*` (= `dif_pos h`, the source's own proof).  `resTp` is the
      overall result `Tp` (the sc-lemmas' `α`, unrecoverable through `Tp.denote`). -/
  partial def Env.atom (env : Env) (resTp a : Expr) (k : Expr → MetaM CodePf) : MetaM CodePf := do
    let a ← instantiateMVars a
    if let .letE _ ty v b _ := a then
      -- a reifiable pure `let` keeps its **sharing**: the bound value walks once, the body sees
      -- its atom (a non-reifiable let — a proof, a function — zeta-inlines instead)
      if (← reifyTp ty).isSome then
        return ← env.atom resTp v fun av => do
          if env.pf then
            let env' := if let .fvar fid := av
              then { env with subst := (fid, av) :: env.subst } else env
            env'.atom resTp (b.instantiate1 av) k
          else
            withLocalDeclD `h ty fun hx =>
              { env with subst := (hx.fvarId!, av) :: env.subst }.atom resTp (b.instantiate1 hx) k
      else
        return ← env.atom resTp (b.instantiate1 v) k
    if let .fvar fid := a then
      if let some atom := env.subst.lookup fid then return ← k atom
    if !(a.hasAnyFVar fun fid => (env.subst.lookup fid).isSome) then
      if env.pf then
        -- a closed value, proof mode: feed it *directly* (no `Code.lit` node — denotationally
        -- identical, and a literal index/collection keeps a get/set's source proof `h` fitting)
        return ← k a
      else
        return ← env.mkLitBind a (← reifyTpOrThrow (← inferType a)) k
    match_expr a with
    | HMul.hMul _ _ _ _ x y => let (o,c) ← arithOp ``Bin.mul ``Bin.mulZ (← inferType a); env.emitBin resTp o c x y k
    | HAdd.hAdd _ _ _ _ x y => let (o,c) ← arithOp ``Bin.add ``Bin.addZ (← inferType a); env.emitBin resTp o c x y k
    | HSub.hSub _ _ _ _ x y => let (o,c) ← arithOp ``Bin.sub ``Bin.subZ (← inferType a); env.emitBin resTp o c x y k
    | HPow.hPow _ _ _ _ x y =>
        match_expr ← reifyTpOrThrow (← inferType a) with
        | Tp.nat    => env.emitBin resTp (.const ``Bin.pow []) (.const ``Tp.nat []) x y k
        | Tp.zmod n => env.emitBin resTp (mkApp (.const ``Bin.powZ []) n)
                         (mkApp (.const ``Tp.zmod []) n) x y k
        | _ => throwError "reflect%: `^` is only supported at `Nat` and `ZMod`:{indentExpr a}"
    | BEq.beq _ _ x y       => env.emitBin resTp (.const ``Bin.eq []) (.const ``Tp.bool []) x y k
    | Bool.and x y          => env.emitBin resTp (.const ``Bin.and []) (.const ``Tp.bool []) x y k
    | Bool.or  x y          => env.emitBin resTp (.const ``Bin.or []) (.const ``Tp.bool []) x y k
    | Bool.not x            => env.emitUn resTp (.const ``Un.not []) (.const ``Tp.bool []) x k
    | Prod.mk _ _ x y =>
        let aTp ← reifyTpOrThrow (← inferType x); let bTp ← reifyTpOrThrow (← inferType y)
        env.emitBin resTp (mkApp2 (.const ``Bin.pair []) aTp bTp) (mkApp2 (.const ``Tp.prod []) aTp bTp) x y k
    | Prod.fst _ _ p => env.emitUn resTp (← prodUn ``Un.fst p) (← reifyTpOrThrow (← inferType a)) p k
    | Prod.snd _ _ p => env.emitUn resTp (← prodUn ``Un.snd p) (← reifyTpOrThrow (← inferType a)) p k
    | Sum.inl A B x =>
        let aTp ← reifyTpOrThrow A; let bTp ← reifyTpOrThrow B
        env.emitUn resTp (mkApp2 (.const ``Un.inl []) aTp bTp) (mkApp2 (.const ``Tp.sum []) aTp bTp) x k
    | Sum.inr A B x =>
        let aTp ← reifyTpOrThrow A; let bTp ← reifyTpOrThrow B
        env.emitUn resTp (mkApp2 (.const ``Un.inr []) aTp bTp) (mkApp2 (.const ``Tp.sum []) aTp bTp) x k
    | GetElem.getElem _ _ _ _ _ coll i h =>
        -- `coll[i]`: the erased node drops the in-bounds proof; in proof mode the *source's* proof
        -- closes the node's `fail` branch (`sc_vget`/`sc_aget`)
        let (natIdx, finPf) ← finIndexToNat i        -- a `Fin` index becomes `i.val` with `i.isLt`
        let hSrc := finPf.getD h
        let natT : Expr := .const ``Tp.nat []
        match_expr ← reifyTpOrThrow (← inferType coll) with
        | Tp.vec aTp nExpr =>
            env.emitPop resTp a (mkApp2 (.const ``POp.vget []) aTp nExpr) aTp
              [mkApp2 (.const ``Tp.vec []) aTp nExpr, natT] [coll, natIdx]
              (fun klam => mkAppOptM ``sc_vget #[env.Op, env.SOp, resTp, aTp, none, coll, natIdx, klam, hSrc]) k
        | Tp.array aTp =>
            env.emitPop resTp a (mkApp (.const ``POp.aget []) aTp) aTp
              [mkApp (.const ``Tp.array []) aTp, natT] [coll, natIdx]
              (fun klam => mkAppOptM ``sc_aget #[env.Op, env.SOp, resTp, aTp, coll, natIdx, klam, hSrc]) k
        | _ => throwError "reflect%: get on a non-collection value{indentExpr coll}"
    | Vector.ofFn nExpr elemTy f =>
        -- `Vector.ofFn f` : expand over the `n` `Fin` indices into a `#v[f 0, …, f (n-1)]`
        let some n := natLitOf nExpr <|> natLitOf (← whnf nExpr)
          | throwError "reflect%: `Vector.ofFn` non-literal length{indentExpr nExpr}"
        let aTp ← reifyTpOrThrow elemTy
        let elems ← (List.range n).mapM (fun kk => do pure (f.beta #[← mkFinLit nExpr kk]))
        env.emitVec resTp aTp nExpr elems k
    | Vector.set _ _ coll i x h =>
        match_expr ← reifyTpOrThrow (← inferType coll) with
        | Tp.vec aTp nExpr =>
            let vecT := mkApp2 (.const ``Tp.vec []) aTp nExpr
            env.emitPop resTp a (mkApp2 (.const ``POp.vset []) aTp nExpr) vecT
              [vecT, .const ``Tp.nat [], aTp] [coll, i, x]
              (fun klam => mkAppOptM ``sc_vset #[env.Op, env.SOp, resTp, aTp, none, coll, i, x, klam, h]) k
        | _ => throwError "reflect%: `Vector.set` on a non-vector{indentExpr coll}"
    | Array.set _ coll i x h =>
        match_expr ← reifyTpOrThrow (← inferType coll) with
        | Tp.array aTp =>
            let arrT := mkApp (.const ``Tp.array []) aTp
            env.emitPop resTp a (mkApp (.const ``POp.aset []) aTp) arrT
              [arrT, .const ``Tp.nat [], aTp] [coll, i, x]
              (fun klam => mkAppOptM ``sc_aset #[env.Op, env.SOp, resTp, aTp, coll, i, x, klam, h]) k
        | _ => throwError "reflect%: `Array.set` on a non-array{indentExpr coll}"
    | Vector.mk _ nExpr arr h =>
        match_expr ← reifyTpOrThrow (← inferType a) with
        -- a list literal is a construction; a runtime `arr` is an `array → vec` *cast* (`⟨arr, h⟩`)
        | Tp.vec aTp _ =>
            match seqLitElems arr with
            | some elems => env.emitVec resTp aTp nExpr elems k
            | none       =>
                env.emitPop resTp a (mkApp2 (.const ``POp.arrToVec []) aTp nExpr)
                  (mkApp2 (.const ``Tp.vec []) aTp nExpr) [mkApp (.const ``Tp.array []) aTp] [arr]
                  (fun klam => mkAppOptM ``sc_arrToVec #[env.Op, env.SOp, resTp, aTp, nExpr, arr, klam, h]) k
        | _ => throwError "reflect%: `Vector.mk` at a non-vector type{indentExpr a}"
    | List.toArray _ lst =>
        let some elems := seqLitElems lst
          | throwError "reflect%: array not built from a list literal{indentExpr a}"
        match_expr ← reifyTpOrThrow (← inferType a) with
        | Tp.array aTp => env.emitArr resTp aTp elems k
        | _ => throwError "reflect%: array literal at a non-array type{indentExpr a}"
    | Fin.mk nExpr m h =>
        env.emitPop resTp a (mkApp (.const ``POp.natToFin []) nExpr)
          (mkApp (.const ``Tp.fin []) nExpr) [.const ``Tp.nat []] [m]
          (fun klam => mkAppOptM ``sc_natToFin #[env.Op, env.SOp, resTp, nExpr, m, klam, h]) k
    | Vector.toArray A nExpr v =>                                            -- total downcast `v.toArray`
        let aTp ← reifyTpOrThrow A
        env.emitUn resTp (mkApp2 (.const ``Un.toArray []) aTp nExpr) (mkApp (.const ``Tp.array []) aTp) v k
    | Fin.val nExpr i =>                                                     -- total downcast `i.val`
        env.emitUn resTp (mkApp (.const ``Un.finVal []) nExpr) (.const ``Tp.nat []) i k
    | Fin.foldl elemTy nExpr f init =>
        -- a bounded loop — reflected as a first-class `fold` node, NOT unrolled
        let aTp ← reifyTpOrThrow elemTy
        env.emitFold resTp a aTp nExpr f init k
    | ite _ c inst t e =>
        -- a pure decidable `if` — both branches evaluate, a strict `select` picks
        env.emitIte resTp a c inst t e k
    | Decidable.decide p _ =>
        -- a coerced comparison used as a `Bool` value (e.g. inside `… || …`); `Bin.denote` of the
        -- ordering ops is `decide`-shaped, so the step stays definitional
        let natCmp (op : Expr) (x y : Expr) : MetaM CodePf := do
          match_expr ← reifyTpOrThrow (← inferType x) with
          | Tp.nat => env.emitBin resTp op (.const ``Tp.bool []) x y k
          | _ => throwError "reflect%: `decide` only supported on `Nat` comparisons{indentExpr a}"
        match_expr p with
        | LT.lt _ _ x y => natCmp (.const ``Bin.lt []) x y
        | LE.le _ _ x y => natCmp (.const ``Bin.ble []) x y
        | GE.ge _ _ x y => natCmp (.const ``Bin.ble []) y x
        | GT.gt _ _ x y => natCmp (.const ``Bin.lt []) y x
        | _ => throwError "reflect%: `decide` only supported on `Nat` comparisons{indentExpr a}"
    | _ => do
        -- a *pure helper application*: spill it as a `def_` — definitions are **kept folded**;
        -- anything unspillable (unsupported shape, no value args) unfolds and retries
        if !env.noSpill then
          if let some sig ← analyzeCall a then
            if sig.isPure then
              return ← env.emitCallPure resTp sig k
        match ← unfoldDefinition? a with
        | some a' => env.atom resTp a' k
        | none => throwError "reflect%: cannot reflect operand (not an atom or supported \
                              primitive):{indentExpr a}"

  /-- Binary primitive: reflect both operands, bind the result as a fresh var `vc`, emit the `bin`
      node; in proof mode instantiate `vc ↦ Bin.denote o x y` in the continuation's proof (the `bin`
      step is definitional). -/
  partial def Env.emitBin (env : Env) (resTp binOp cTp x y : Expr) (k : Expr → MetaM CodePf) : MetaM CodePf :=
    env.atom resTp x fun ax =>
    env.atom resTp y fun ay =>
    withLocalDeclD `v (mkApp env.V cTp) fun vc => do
      let (kcode, kpf?) ← k vc
      let node ← mkAppOptM ``Code.bin
        #[env.Op, env.SOp, env.F, env.V, none, none, none, none, binOp, ax, ay, ← mkLambdaFVars #[vc] kcode]
      let pf? ← kpf?.mapM fun kp => return kp.replaceFVar vc (← mkAppM ``Bin.denote #[binOp, ax, ay])
      return (node, pf?)

  /-- Unary primitive: as `emitBin`, with `vc ↦ Un.denote o x`. -/
  partial def Env.emitUn (env : Env) (resTp unOp cTp x : Expr) (k : Expr → MetaM CodePf) : MetaM CodePf :=
    env.atom resTp x fun ax =>
    withLocalDeclD `v (mkApp env.V cTp) fun vc => do
      let (kcode, kpf?) ← k vc
      let node ← mkAppOptM ``Code.un
        #[env.Op, env.SOp, env.F, env.V, none, none, none, unOp, ax, ← mkLambdaFVars #[vc] kcode]
      let pf? ← kpf?.mapM fun kp => return kp.replaceFVar vc (← mkAppM ``Un.denote #[unOp, ax])
      return (node, pf?)

  /-- A **partial primitive** (`Code.pop`): reflect the arguments, bind the result as a fresh var,
      emit the node.  In proof mode, close the erased `fail` branch via the per-op `sc_*` bridging
      lemma — built by `mkScStep` from the *source* arguments and the source's own proof (not the
      reflected atoms, which for compound arguments are fresh binders; the enclosing nodes tie each
      binder to its source value) — instantiating the result var with the source value `src`. -/
  partial def Env.emitPop (env : Env) (resTp src popOp retTp : Expr) (argTps argVals : List Expr)
      (mkScStep : Expr → MetaM Expr) (k : Expr → MetaM CodePf) : MetaM CodePf :=
    env.atoms resTp argVals fun atoms => do
      let argsHL ← mkArgHListT env.V atoms argTps
      let asList ← mkListLit (.const ``Tp []) argTps
      withLocalDeclD `v (mkApp env.V retTp) fun vc => do
        let (kcode, kpf?) ← k vc
        let klam ← mkLambdaFVars #[vc] kcode
        let node ← mkAppOptM ``Code.pop
          #[env.Op, env.SOp, env.F, env.V, none, asList, retTp, popOp, argsHL, klam]
        let pf? ← kpf?.mapM fun kp => do
          eqTransD (← mkScStep klam) (kp.replaceFVar vc src)
        return (node, pf?)

  /-- A **bounded fold** (`Fin.foldl n f init`): reflect the initial accumulator, reflect the loop
      body **once** at fresh index/accumulator binders (ending in its own `ret`), and emit the
      `fold` node — the loop is *kept as control flow*, never unrolled.  In proof mode `sc_fold`
      consumes the body's pointwise equations (∀-abstracted over the binders); the `Fin`-typed index
      binder also supplies in-bounds facts (`i.isLt`) to gets inside the body. -/
  partial def Env.emitFold (env : Env) (resTp src aTp nExpr f init : Expr)
      (k : Expr → MetaM CodePf) : MetaM CodePf := do
    let finTp := mkApp (.const ``Tp.fin []) nExpr
    let finHostTy := mkApp (.const ``Fin []) nExpr
    let elemHostTy ← whnf (← inferType init)
    -- the body, walked once; in proof mode also its pointwise equation, ∀-abstracted
    let (bodyLam, hb?) ←
      withLocalDeclD `i (mkApp env.V finTp) fun vi =>
      env.withHostVar finHostTy vi fun hi =>
      withLocalDeclD `acc (mkApp env.V aTp) fun vacc =>
      env.withHostVar elemHostTy vacc fun hacc => do
        let env' := { env with
          subst := (hi.fvarId!, vi) :: (hacc.fvarId!, vacc) :: env.subst }
        let (bcode, bpf?) ← env'.atom aTp (f.beta #[hacc, hi]) (env'.liftK (env'.mkRetT aTp))
        pure (← mkLambdaFVars #[vi, vacc] bcode, ← bpf?.mapM (mkLambdaFVars #[vi, vacc] ·))
    env.atom resTp init fun ainit =>
    withLocalDeclD `v (mkApp env.V aTp) fun vc => do
      let (kcode, kpf?) ← k vc
      let klam ← mkLambdaFVars #[vc] kcode
      let node ← mkAppOptM ``Code.fold
        #[env.Op, env.SOp, env.F, env.V, none, aTp, nExpr, ainit, bodyLam, klam]
      let pf? ← kpf?.mapM fun kp => do
        let some hb := hb? | throwError "reflect%: internal: missing fold body proof"
        let scStep ← mkAppOptM ``sc_fold
          #[env.Op, env.SOp, resTp, aTp, nExpr, init, f, bodyLam, klam, hb]
        eqTransD scStep (kp.replaceFVar vc src)
      return (node, pf?)

  /-- A **pure decidable `if`**: both branches reflect (strict — a circuit-style `select`), the
      condition becomes a `Bool` atom, and one bridging lemma (`ite_decide`/`ite_nat_eq`/`ite_bool`)
      aligns the source `ite` with the selected `bif`. -/
  partial def Env.emitIte (env : Env) (resTp src c inst t e : Expr) (k : Expr → MetaM CodePf) :
      MetaM CodePf := do
    let aTp ← reifyTpOrThrow (← inferType t)
    let natBin (op : Expr) (x y : Expr) : (Expr → MetaM CodePf) → MetaM CodePf := fun kc => do
      match_expr ← reifyTpOrThrow (← inferType x) with
      | Tp.nat => env.emitBin resTp op (.const ``Tp.bool []) x y kc
      | _ => throwError "reflect%: `if` comparison only supported at `Nat`{indentExpr c}"
    -- (condition-atom emitter, source-side condition `Bool`, `ite → bif` bridging equation)
    let (emitCond, cBoolSrc, bridge) ← show MetaM (((Expr → MetaM CodePf) → MetaM CodePf) × Expr × Expr) from do
      match_expr c with
      | Eq ty x y =>
          match_expr ty with
          | Bool => do
              unless y.isConstOf ``Bool.true do
                throwError "reflect%: unsupported `if` condition{indentExpr c}"
              pure ((fun kc => env.atom resTp x kc), x, ← mkAppM ``ite_bool #[x, t, e])
          | Nat => do
              pure (natBin (.const ``Bin.eq []) x y, ← mkAppM ``BEq.beq #[x, y],
                    ← mkAppM ``ite_nat_eq #[x, y, t, e])
          | _ => throwError "reflect%: unsupported `if` condition{indentExpr c}"
      | LT.lt _ _ x y => do
          pure (natBin (.const ``Bin.lt []) x y, ← mkAppOptM ``Decidable.decide #[c, inst],
                ← mkAppOptM ``ite_decide #[c, inst, none, t, e])
      | LE.le _ _ x y => do
          pure (natBin (.const ``Bin.ble []) x y, ← mkAppOptM ``Decidable.decide #[c, inst],
                ← mkAppOptM ``ite_decide #[c, inst, none, t, e])
      | GE.ge _ _ x y => do
          pure (natBin (.const ``Bin.ble []) y x, ← mkAppOptM ``Decidable.decide #[c, inst],
                ← mkAppOptM ``ite_decide #[c, inst, none, t, e])
      | GT.gt _ _ x y => do
          pure (natBin (.const ``Bin.lt []) y x, ← mkAppOptM ``Decidable.decide #[c, inst],
                ← mkAppOptM ``ite_decide #[c, inst, none, t, e])
      | _ => throwError "reflect%: unsupported `if` condition{indentExpr c}"
    emitCond fun cb =>
    env.atom resTp t fun ta =>
    env.atom resTp e fun ea =>
    withLocalDeclD `v (mkApp env.V aTp) fun vc => do
      let (kcode, kpf?) ← k vc
      let klam ← mkLambdaFVars #[vc] kcode
      let boolT : Expr := .const ``Tp.bool []
      let argsHL ← mkArgHListT env.V [cb, ta, ea] [boolT, aTp, aTp]
      let asList ← mkListLit (.const ``Tp []) [boolT, aTp, aTp]
      let node ← mkAppOptM ``Code.pop
        #[env.Op, env.SOp, env.F, env.V, none, asList, aTp, mkApp (.const ``POp.select []) aTp,
          argsHL, klam]
      let pf? ← kpf?.mapM fun kp => do
        let scStep ← mkAppOptM ``sc_select #[env.Op, env.SOp, resTp, aTp, cBoolSrc, t, e, klam]
        -- `bif ⟦c⟧ then t else e = ite c t e` under `denote ∘ klam`
        let congrFn ← withLocalDeclD `z (mkApp env.V aTp) fun z => do
          mkLambdaFVars #[z] (← denoteE (mkApp klam z))
        let congrStep ← mkAppM ``congrArg #[congrFn, ← mkAppM ``Eq.symm #[bridge]]
        eqTransD scStep (← eqTransD congrStep (kp.replaceFVar vc src))
      return (node, pf?)

  /-- **Vector construction** `#v[e₀,…]`: reflect the elements, bind the result vector as a fresh
      var, emit the `vec` node; the step is definitional (`vc ↦` the atom-vector). -/
  partial def Env.emitVec (env : Env) (resTp aTp nExpr : Expr) (elems : List Expr)
      (k : Expr → MetaM CodePf) : MetaM CodePf :=
    env.atoms resTp elems fun atoms => do
      let vecVal ← mkVecOfAtoms env.V aTp nExpr atoms
      withLocalDeclD `v (mkApp env.V (mkApp2 (.const ``Tp.vec []) aTp nExpr)) fun vc => do
        let (kcode, kpf?) ← k vc
        let node ← mkAppOptM ``Code.vec
          #[env.Op, env.SOp, env.F, env.V, none, aTp, nExpr, vecVal, ← mkLambdaFVars #[vc] kcode]
        return (node, kpf?.map (·.replaceFVar vc vecVal))

  /-- **Array construction** `#[e₀,…]`: as `emitVec`, instantiating with `(#[atoms])`. -/
  partial def Env.emitArr (env : Env) (resTp aTp : Expr) (elems : List Expr)
      (k : Expr → MetaM CodePf) : MetaM CodePf :=
    env.atoms resTp elems fun atoms => do
      let lst ← mkListLit (mkApp env.V aTp) atoms
      withLocalDeclD `v (mkApp env.V (mkApp (.const ``Tp.array []) aTp)) fun vc => do
        let (kcode, kpf?) ← k vc
        let node ← mkAppOptM ``Code.arr
          #[env.Op, env.SOp, env.F, env.V, none, aTp, lst, ← mkLambdaFVars #[vc] kcode]
        let pf? ← kpf?.mapM fun kp => return kp.replaceFVar vc (← mkAppM ``List.toArray #[lst])
        return (node, pf?)

  /-- Reflect a list of pure argument values into their atoms. -/
  partial def Env.atoms (env : Env) (resTp : Expr) : List Expr → (List Expr → MetaM CodePf) → MetaM CodePf
    | [],      k => k []
    | v :: vs, k => env.atom resTp v fun av => env.atoms resTp vs (fun atoms => k (av :: atoms))

  /-- Reflect a `Free Op SOp _` computation into a `Code`; `k` consumes the result atom.  In proof
      mode, also return `proof : denote code = bind (ofFree e) Kf` — the invariant (★). -/
  partial def Env.walk (env : Env) (resTp e : Expr) (k : Expr → MetaM Expr) : MetaM CodePf := do
    let e := e.consumeMData.headBeta
    if let .letE _ _ v b _ := e then return ← env.walk resTp (b.instantiate1 v) k
    match_expr e with
    | Free.pure _ _ _ a       => env.walkPure resTp a k
    | Pure.pure _ _ _ a       => env.walkPure resTp a k
    | Bind.bind _ _ _ _ x f   => env.walkBind resTp x f k
    | Free.bind _ _ _ _ x f   => env.walkBind resTp x f k
    | cond _ c t el           => env.walkIte resTp c t el k
    | Free.op _ _ _ I R o i cont => env.walkOp resTp I R o i cont k
    | Free.hop _ _ _ β s b cont  => env.walkScope resTp β s b cont k
    | Fin.foldlM _ elemTy _ nExpr f init =>
        -- a bounded loop with an *effectful* (`Free`-valued) body — the same body-agnostic node
        env.walkFold resTp elemTy nExpr f init k
    | _ =>
        match ← env.tryCall resTp e k with
        | some r => pure r
        | none => match ← unfoldDefinition? e with
          | some e' => env.walk resTp e' k
          | none    => throwError "reflect%: don't know how to reflect computation{indentExpr e}"

  /-- `pure a`: reflect the atom; in proof mode wrap its step with `sc_pure`. -/
  partial def Env.walkPure (env : Env) (resTp a : Expr) (k : Expr → MetaM Expr) : MetaM CodePf := do
    let (code, pA?) ← env.atom resTp a (env.liftK k)
    if !env.pf then return (code, none)
    let some pA := pA? | throwError "reflect%: internal: missing pure-atom proof"
    let Kf ← mkKf env.V (← inferType a) k
    return (code, some (← mkAppOptM ``sc_pure #[env.Op, env.SOp, none, resTp, a, ← denoteE code, Kf, pA]))

  /-- `bind x f`: a pure `x` is inlined via left-identity; else walk `x` with `f` reflected at each
      return point; in proof mode compose `x`'s and `f`'s equations via `sc_bind`. -/
  partial def Env.walkBind (env : Env) (resTp x f : Expr) (k : Expr → MetaM Expr) : MetaM CodePf := do
    match_expr x.consumeMData.headBeta with
    | Free.pure _ _ _ a => env.walk resTp (f.beta #[a]) k
    | Pure.pure _ _ _ a => env.walk resTp (f.beta #[a]) k
    | _ =>
      -- the code continuation at each return point of `x`: walk `f` at the bound atom (in proof
      -- mode the atom is the host value; in abstract mode a host placeholder maps to it)
      let kInner : Expr → MetaM Expr := fun xa => do
        if env.pf then
          let env' := if let .fvar fid := xa then { env with subst := (fid, xa) :: env.subst } else env
          return (← env'.walk resTp (f.beta #[xa]) k).1
        else
          let .forallE _ X _ _ := (← whnf (← inferType f))
            | throwError "reflect%: expected a continuation function{indentExpr f}"
          withLocalDeclD `h X fun hx =>
            return (← { env with subst := (hx.fvarId!, xa) :: env.subst }.walk resTp (f.beta #[hx]) k).1
      let (xcode, xpf?) ← env.walk resTp x kInner
      if !env.pf then return (xcode, none)
      let some xproof := xpf? | throwError "reflect%: internal: missing bind proof"
      let Y ← freeResult x
      let X ← forallTelescope (← inferType f) fun _ cod => do
        let_expr Free _ _ X := (← whnf cod) | throwError "reflect%: bind cont"
        pure X
      let Kf ← mkKf env.V X k
      let fproofLam ← withLocalDeclD `r Y fun vr => do
        let env' := { env with subst := (vr.fvarId!, vr) :: env.subst }
        let (_, fp?) ← env'.walk resTp (f.beta #[vr]) k
        let some fp := fp? | throwError "reflect%: internal: missing bind-continuation proof"
        mkLambdaFVars #[vr] fp
      -- xproof : denote xcode = bind (ofFree x) (fun r => denote (kInner r))
      let ofx ← mkAppM ``ofFree #[x]
      let hEq ← mkAppM ``funext #[fproofLam]      -- (fun r => denote (kInner r)) = (fun r => bind (ofFree (f r)) Kf)
      let compTy ← inferType (← denoteE xcode)
      let fFun ← withLocalDeclD `kk (← mkArrow Y compTy) fun kk => do
        mkLambdaFVars #[kk] (← mkAppM ``ITree.bind #[ofx, kk])
      let congrStep ← mkAppM ``congrArg #[fFun, hEq]
      let hC ← eqTransD xproof congrStep
      return (xcode, some (← mkAppOptM ``sc_bind #[env.Op, env.SOp, none, none, resTp, x, f, Kf, ← denoteE xcode, hC]))

  /-- `op o i cont`: reflect the continuation (binding the result atom), then the input atom wrapping
      the `op` node; in proof mode `sc_op` with the continuation's IH. -/
  partial def Env.walkOp (env : Env) (resTp I R o i cont : Expr) (k : Expr → MetaM Expr) : MetaM CodePf := do
    let ITp ← reifyTpOrThrow I
    let RTp ← reifyTpOrThrow R
    let .forallE _ Rt _ _ := (← whnf (← inferType cont))
      | throwError "reflect%: expected an op continuation{indentExpr cont}"
    let (kbody, ih?) ← withLocalDeclD `v (mkApp env.V RTp) fun vx =>
      env.withHostVar Rt vx fun hx => do
        let env' := { env with subst := (hx.fvarId!, vx) :: env.subst }
        let (rcode, rpf?) ← env'.walk resTp (cont.beta #[hx]) k
        return (← mkLambdaFVars #[vx] rcode, ← rpf?.mapM (mkLambdaFVars #[vx] ·))
    let (code, pI?) ← env.atom resTp i (env.liftK fun ia =>
      mkAppOptM ``Code.op #[env.Op, env.SOp, env.F, env.V, none, ITp, RTp, o, ia, kbody])
    if !env.pf then return (code, none)
    let some pI := pI? | throwError "reflect%: internal: missing op-input proof"
    let some ih := ih? | throwError "reflect%: internal: missing op IH"
    let Xr ← forallTelescope (← inferType cont) fun _ cod => do
      let_expr Free _ _ X := (← whnf cod) | throwError "reflect%: op cont"
      pure X
    let Kf ← mkKf env.V Xr k
    let scStep ← mkAppOptM ``sc_op #[env.Op, env.SOp, ITp, RTp, resTp, none, o, i, cont, kbody, Kf, ih]
    return (code, some (← eqTransD pI scStep))

  /-- `hop s b cont`: reflect the block (ending in `ret`), then the tail; in proof mode `sc_scope`
      composes the block's equation (`walkTop`'s `denote B = ofFree b`) with the tail's IH. -/
  partial def Env.walkScope (env : Env) (resTp β s b cont : Expr) (k : Expr → MetaM Expr) : MetaM CodePf := do
    let βTp ← reifyTpOrThrow β
    let (blockCode, blockPf?) ← env.walkTop βTp b
    let .forallE _ Xt _ _ := (← whnf (← inferType cont))
      | throwError "reflect%: expected a scope continuation{indentExpr cont}"
    let (kbody, ih?) ← withLocalDeclD `v (mkApp env.V βTp) fun vx =>
      env.withHostVar Xt vx fun hx => do
        let env' := { env with subst := (hx.fvarId!, vx) :: env.subst }
        let (rcode, rpf?) ← env'.walk resTp (cont.beta #[hx]) k
        return (← mkLambdaFVars #[vx] rcode, ← rpf?.mapM (mkLambdaFVars #[vx] ·))
    let code ← mkAppOptM ``Code.scope #[env.Op, env.SOp, env.F, env.V, none, βTp, s, blockCode, kbody]
    if !env.pf then return (code, none)
    let some hB := blockPf? | throwError "reflect%: internal: missing scope-block proof"
    let some ih := ih? | throwError "reflect%: internal: missing scope IH"
    let X ← forallTelescope (← inferType cont) fun _ cod => do
      let_expr Free _ _ X := (← whnf cod) | throwError "reflect%: scope cont"
      pure X
    let Kf ← mkKf env.V X k
    return (code, some (← mkAppOptM ``sc_scope
      #[env.Op, env.SOp, βTp, resTp, none, s, b, cont, blockCode, kbody, Kf, hB, ih]))

  /-- `cond c t e`: reflect both arms with the same continuation, then the scrutinee atom wrapping
      the `ite` node; in proof mode `sc_cond` with both arms' IHs. -/
  partial def Env.walkIte (env : Env) (resTp c t el : Expr) (k : Expr → MetaM Expr) : MetaM CodePf := do
    let (tcode, tpf?) ← env.walk resTp t k
    let (ecode, epf?) ← env.walk resTp el k
    let (code, pC?) ← env.atom resTp c (env.liftK fun ca =>
      mkAppOptM ``Code.ite #[env.Op, env.SOp, env.F, env.V, none, ca, tcode, ecode])
    if !env.pf then return (code, none)
    let (some pC, some tproof, some eproof) := (pC?, tpf?, epf?)
      | throwError "reflect%: internal: missing ite proof"
    let X ← freeResult t
    let Kf ← mkKf env.V X k
    let scStep ← mkAppOptM ``sc_cond
      #[env.Op, env.SOp, none, resTp, c, t, el, tcode, ecode, Kf, tproof, eproof]
    return (code, some (← eqTransD pC scStep))

  /-- A **bounded fold with an effectful body** (`Fin.foldlM n f init` over `Free`): the same
      `fold` node — the loop construct is body-agnostic — with the body reflected as a full block
      (`walkTop`: effects, scopes, anything); `sc_foldM` is its (★) step, consuming the blocks'
      pointwise `ofFree`-equations. -/
  partial def Env.walkFold (env : Env) (resTp elemTy nExpr f init : Expr) (k : Expr → MetaM Expr) :
      MetaM CodePf := do
    let aTp ← reifyTpOrThrow elemTy
    let finTp := mkApp (.const ``Tp.fin []) nExpr
    let finHostTy := mkApp (.const ``Fin []) nExpr
    let (bodyLam, hb?) ←
      withLocalDeclD `i (mkApp env.V finTp) fun vi =>
      env.withHostVar finHostTy vi fun hi =>
      withLocalDeclD `acc (mkApp env.V aTp) fun vacc =>
      env.withHostVar elemTy vacc fun hacc => do
        let env' := { env with
          subst := (hi.fvarId!, vi) :: (hacc.fvarId!, vacc) :: env.subst }
        let (bcode, bpf?) ← env'.walkTop aTp (f.beta #[hacc, hi])
        pure (← mkLambdaFVars #[vi, vacc] bcode, ← bpf?.mapM (mkLambdaFVars #[vi, vacc] ·))
    let kbody ← withLocalDeclD `v (mkApp env.V aTp) fun vc => do
      mkLambdaFVars #[vc] (← k vc)
    let (code, pI?) ← env.atom resTp init (env.liftK fun ainit =>
      mkAppOptM ``Code.fold #[env.Op, env.SOp, env.F, env.V, none, aTp, nExpr, ainit, bodyLam, kbody])
    if !env.pf then return (code, none)
    let some pI := pI? | throwError "reflect%: internal: missing fold-init proof"
    let some hb := hb? | throwError "reflect%: internal: missing fold body proof"
    let scStep ← mkAppOptM ``sc_foldM
      #[env.Op, env.SOp, resTp, aTp, nExpr, init, f, bodyLam, kbody, hb]
    return (code, some (← eqTransD pI scStep))

  /-- Top-level walk (continuation `ret`, so `Kf = ret`); in proof mode close (★) with
      `bind_ret_right`, giving `denote code = ofFree e`.  `resTp` is `e`'s result `Tp`. -/
  partial def Env.walkTop (env : Env) (resTp e : Expr) : MetaM CodePf := do
    let (code, pf?) ← env.walk resTp e (env.mkRetT resTp)
    let pf? ← pf?.mapM fun proof =>
      do eqTransD proof (← mkAppM ``ITree.bind_ret_right #[← mkAppM ``ofFree #[e]])
    return (code, pf?)

  /-- Try to reflect `e` (walk position, a `Free` computation) as a **call** to a top-level helper
      (`analyzeCall`), dispatching on the mode: abstract mode monomorphises and spills/resolves;
      proof mode builds the concrete subroutine with its own (★)-proof. -/
  partial def Env.tryCall (env : Env) (resTp e : Expr) (k : Expr → MetaM Expr) : MetaM (Option CodePf) := do
    if env.noSpill then return none
    let some sig ← analyzeCall e | return none
    if env.pf then return some (← env.callWithProof resTp sig k)
    else env.callAbstract resTp sig k

  /-- Build a helper's `def_` body `fun hargs => code`: fresh value binders substituted by the
      `hargs` projections, the body walked at its result `Tp` ending in `ret` — a `Free` helper via
      `walk`, a **pure** helper via `atom`.  Bodies may themselves call (earlier-spilled) helpers. -/
  partial def Env.rebuildBody (env : Env) (sig : CallSig) : MetaM Expr := do
    let hlistTy ← mkAppM ``HList #[env.V, sig.asList]
    withLocalDeclD `args hlistTy fun hargs => do
      let decls : Array (Name × (Array Expr → MetaM Expr)) :=
        sig.argTys.map (fun ty => (`x, fun _ => pure ty))
      withLocalDeclsD decls fun hxs => do
        let mut subst := env.subst
        for j in [0:hxs.size] do
          subst := (hxs[j]!.fvarId!, ← projHList hargs j) :: subst
        let mut fullArgs := sig.fArgs
        for j in [0:sig.valuePos.size] do
          fullArgs := fullArgs.set! (sig.valuePos[j]!) hxs[j]!
        let env' := { env with subst }
        let body := sig.cValInst.beta fullArgs
        let bcode ←
          if sig.isPure then
            Prod.fst <$> env'.atom sig.retTp body (env'.liftK (env'.mkRetT sig.retTp))
          else
            Prod.fst <$> env'.walk sig.retTp body (env'.mkRetT sig.retTp)
        mkLambdaFVars #[hargs] bcode

  /-- Resolve a call's `F`-name.  Build pass: look it up among the bound `def_` binders (bodies see
      only *earlier* binders — guaranteed by discovery post-order).  Discovery pass: walk the callee
      body once (discarded — its own callees spill first, giving the dependency order), record the
      signature, and emit a fresh mvar (the discovery code is thrown away). -/
  partial def Env.resolveCallee (env : Env) (sig : CallSig) : MetaM Expr := do
    match env.resolved with
    | some resolved =>
        let some (_, cf) ← resolved.findM? (fun d => sigsMatch d.1 sig)
          | throwError "reflect%: internal: unresolved helper `{sig.cName}` (dependency order)"
        return cf
    | none =>
        unless (← (← env.defs.get).findM? (sigsMatch · sig)).isSome do
          if (← env.inFlight.get).contains sig.cName then
            throwError "reflect%: recursive helper `{sig.cName}` cannot be spilled — only \
                        top-level structural recursion is supported"
          env.inFlight.modify (·.push sig.cName)
          try
            let _ ← env.rebuildBody sig       -- discovery: callees push first (post-order)
          finally
            env.inFlight.modify (·.filter (· != sig.cName))
          env.defs.modify (·.push sig)
        mkFreshExprMVar (mkApp2 env.F sig.asList sig.retTp)

  /-- Abstract-mode `Free`-helper call: resolve the `F`-name, reflect the arguments, emit `call`. -/
  partial def Env.callAbstract (env : Env) (resTp : Expr) (sig : CallSig) (k : Expr → MetaM Expr) :
      MetaM (Option CodePf) := do
    let cf ← env.resolveCallee sig
    let r ← env.atoms resTp sig.valueArgs (fun atoms => do
      pure (← env.emitCall cf sig.asList sig.retTp (← env.mkArgHList atoms) k, none))
    return some r

  /-- Proof-mode resolution: the helper's concrete subroutine `cf` and its parametric equation
      (`∀ hargs, cf hargs = ofFree …` for a `Free` helper, `… = ret …` for a pure one) — built
      **once** per monomorphised signature (`pfDefs`), reused at every call site.  Bodies are walked
      with fresh *identity*-mapped value vars `pvs` (so `atom`'s `atom = value`), then substituted
      by `projHList hargs` — matching `g`'s spilled `def_` body. -/
  partial def Env.resolveCalleeProof (env : Env) (sig : CallSig) : MetaM (Expr × Expr) := do
    let entryMatches (d : PfDefEntry) : MetaM Bool :=
      return d.name == sig.cName && (← isDefEq d.asList sig.asList) && (← isDefEq d.retTp sig.retTp)
    if let some d ← (← env.pfDefs.get).findM? entryMatches then
      return (d.cf, d.bodyProof)
    if (← env.inFlight.get).contains sig.cName then
      throwError "reflect%: recursive helper `{sig.cName}` cannot be spilled — only top-level \
                  structural recursion is supported"
    env.inFlight.modify (·.push sig.cName)
    try
      let hlistTy ← mkAppM ``HList #[env.V, sig.asList]
      let (cf, bodyProofLam) ← withLocalDeclD `args hlistTy fun hargs => do
        let decls : Array (Name × (Array Expr → MetaM Expr)) :=
          sig.argTys.map (fun ty => (`x, fun _ => pure ty))
        withLocalDeclsD decls fun pvs => do
          let subst := (pvs.toList.map (fun p => (p.fvarId!, p))) ++ env.subst
          let mut fullArgs := sig.fArgs
          for j in [0:sig.valuePos.size] do fullArgs := fullArgs.set! (sig.valuePos[j]!) pvs[j]!
          let env' := { env with subst }
          let body := sig.cValInst.beta fullArgs
          let (bcode, bpf?) ←
            if sig.isPure then
              env'.atom sig.retTp body (env'.liftK (env'.mkRetT sig.retTp))
            else
              env'.walkTop sig.retTp body
          let some bproof := bpf? | throwError "reflect%: internal: missing call-body proof"
          let mut projs : Array Expr := #[]
          for j in [0:pvs.size] do projs := projs.push (← projHList hargs j)
          let bcode' := bcode.replaceFVars pvs projs
          let bproof' := bproof.replaceFVars pvs projs
          pure (← mkLambdaFVars #[hargs] (← denoteE bcode'), ← mkLambdaFVars #[hargs] bproof')
      env.pfDefs.modify (·.push { name := sig.cName, asList := sig.asList, retTp := sig.retTp,
                                  cf, bodyProof := bodyProofLam })
      return (cf, bodyProofLam)
    finally
      env.inFlight.modify (·.filter (· != sig.cName))

  /-- Proof-mode `Free`-helper call: reflect the arguments, then `sc_call` — the helper's soundness
      `hcf : cf args = ofFree (helper args)` composes with the caller's continuation. -/
  partial def Env.callWithProof (env : Env) (resTp : Expr) (sig : CallSig) (k : Expr → MetaM Expr) :
      MetaM CodePf := do
    let (cf, bodyProofLam) ← env.resolveCalleeProof sig
    let kcont ← withLocalDeclD `r (mkApp env.V sig.retTp) fun vr => do mkLambdaFVars #[vr] (← k vr)
    env.atoms resTp sig.valueArgs fun atoms => do
      let argHList ← mkArgHListT env.V atoms sig.argTps.toList
      let callCode ← env.emitCall cf sig.asList sig.retTp argHList k
      let hcf := bodyProofLam.beta #[argHList]
      -- `m = ofFree (helper applied to *these* atoms)` — matches `hcf`'s RHS; a bin/get argument's
      -- atom is a bound var here, later instantiated to the source value (so `m` becomes `ofFree e`).
      let mut fullArgs := sig.fArgs
      for j in [0:sig.valuePos.size] do fullArgs := fullArgs.set! (sig.valuePos[j]!) atoms.toArray[j]!
      let m ← mkAppM ``ofFree #[sig.cValInst.beta fullArgs]
      let scStep ← mkAppOptM ``sc_call
        #[env.Op, env.SOp, sig.asList, sig.retTp, resTp, cf, argHList, kcont, m, hcf]
      pure (callCode, some scStep)

  /-- A **pure helper call** in atom position — definitions are *kept folded*: the helper spills as
      a `def_` and a `call` node binds its result atom.  In proof mode the helper's own memoized
      equation closes the step via `sc_callPure`. -/
  partial def Env.emitCallPure (env : Env) (resTp : Expr) (sig : CallSig)
      (k : Expr → MetaM CodePf) : MetaM CodePf := do
    let (cf, bodyProofLam?) ←
      if env.pf then
        let (cf, bp) ← env.resolveCalleeProof sig
        pure (cf, some bp)
      else
        pure (← env.resolveCallee sig, none)
    env.atoms resTp sig.valueArgs fun atoms => do
      let argHList ← mkArgHListT env.V atoms sig.argTps.toList
      withLocalDeclD `v (mkApp env.V sig.retTp) fun vc => do
        let (kcode, kpf?) ← k vc
        let klam ← mkLambdaFVars #[vc] kcode
        let node ← mkAppOptM ``Code.call
          #[env.Op, env.SOp, env.F, env.V, none, sig.asList, sig.retTp, cf, argHList, klam]
        let pf? ← kpf?.mapM fun kp => do
          let some bodyProofLam := bodyProofLam?
            | throwError "reflect%: internal: missing pure-call body proof"
          let hcf := bodyProofLam.beta #[argHList]
          let scStep ← mkAppOptM ``sc_callPure
            #[env.Op, env.SOp, sig.asList, sig.retTp, resTp, cf, argHList, none, klam, hcf]
          -- the value at *these* atoms (bound vars tied to sources by the enclosing nodes)
          let mut fullArgs := sig.fArgs
          for j in [0:sig.valuePos.size] do
            fullArgs := fullArgs.set! (sig.valuePos[j]!) atoms.toArray[j]!
          eqTransD scStep (kp.replaceFVar vc (sig.cValInst.beta fullArgs))
        return (node, pf?)
end

/-- Reflect a program `foo : A₁ → … → Aₙ → Free Op SOp X` (`n ≥ 0`) into
    `{ g : Closed // ∀ args, denoteProg (g KC Tp.denote) ⟨value-args⟩ ≈ ofFree (foo args) }` — the
    `Prog` whose `main` is a function of the program's inputs (delivered as an `HList`), with a `def_`
    per monomorphised helper.  Each `Aᵢ` that reifies to a `Tp` is a program input; any that does not
    (e.g. an in-bounds proof `j < n` for a symbolic index) is **erased from the AST** and instead
    left quantifying the soundness statement, where it discharges the erased get/set's `fail` branch.
    The non-recursive arm of `reflect%`. -/
partial def reflectMain (foo : Expr) : TermElabM Expr := do
  forallTelescope (← inferType foo) fun args codom => do
    let_expr Free Op SOp X := (← whnf codom)
      | throwError "reflect%: the body must have type `Free Op SOp _`, got{indentExpr codom}"
    let XTp ← reifyTpOrThrow X
    -- Classify each argument: those whose type reifies to a `Tp` are **program inputs**; the rest
    -- (e.g. an in-bounds proof `j < n` accompanying a symbolic index) are **erased** from the AST but
    -- kept as hypotheses scoping the soundness statement — that is how a proof-erased `vget`/`vset`'s
    -- `fail` branch is ruled out when the index is symbolic: the source still carries the proof.
    let argTpOpt ← args.mapM (fun a => do reifyTp (← inferType a))
    let mut mainArgTps : Array Expr := #[]
    let mut valueArgs : Array Expr := #[]
    for i in [0:args.size] do
      if let some t := argTpOpt[i]! then
        mainArgTps := mainArgTps.push t; valueArgs := valueArgs.push args[i]!
    -- program inputs must be monomorphic and non-dependent (no type-parameter arguments); a *hypothesis*
    -- argument may freely depend on earlier value arguments (it is a proof *about* them).
    for i in [0:args.size] do
      if X.containsFVar args[i]!.fvarId! then
        throwError "reflect%: `main`'s result type may not depend on its arguments"
      for j in [i+1:args.size] do
        if argTpOpt[j]!.isSome && (← inferType args[j]!).containsFVar args[i]!.fvarId! then
          throwError "reflect%: `main` may not take a type-parameter argument\
                      {indentExpr (← inferType args[i]!)}"
    let tpTy := (.const ``Tp [] : Expr)
    let mainArgsList ← mkListLit tpTy mainArgTps.toList
    let fTy ← mkArrow (← mkAppM ``List #[tpTy]) (← mkArrow tpTy (mkSort (.succ (.succ .zero))))
    let vTy ← mkArrow tpTy (mkSort (.succ .zero))
    let defs ← IO.mkRef (#[] : Array CallSig)
    let pfDefs ← IO.mkRef (#[] : Array PfDefEntry)
    let inFlight ← IO.mkRef (#[] : Array Name)
    let denoteV := Lean.mkConst ``Tp.denote []
    let topBody := (← unfoldDefinition? (foo.beta args)).getD (foo.beta args)
    let g ← withLocalDeclD `F fTy fun F => withLocalDeclD `V vTy fun V => do
      let hlistTy ← mkAppM ``HList #[V, mainArgsList]
      let mkEnv (resolved : Option (Array (CallSig × Expr))) (subst : List (FVarId × Expr)) : Env :=
        { Op, SOp, F, V, subst, defs, pfDefs, inFlight, resolved }
      -- walk `main` under an argument tuple `hargs`, substituting each host argument for its atom
      let walkMain (resolved : Option (Array (CallSig × Expr))) (hargs : Expr) : MetaM Expr := do
        let mut subst : List (FVarId × Expr) := []
        for i in [0:valueArgs.size] do subst := (valueArgs[i]!.fvarId!, ← projHList hargs i) :: subst
        let env := mkEnv resolved subst
        Prod.fst <$> env.walk XTp topBody (env.mkRetT XTp)
      let _ ← withLocalDeclD `args hlistTy fun h => walkMain none h    -- pass 1: discovery
      let entries ← defs.get
      -- pass 2: rebuild each helper body under only the *earlier* `def_` binders (discovery is
      -- post-order, so callees precede callers), then `main` under all of them
      let rec buildTele (i : Nat) (resolved : Array (CallSig × Expr)) : MetaM Expr := do
        if _h : i < entries.size then
          let sig := entries[i]!
          let bodyLam ← (mkEnv (some resolved) []).rebuildBody sig
          withLocalDeclD `f (mkApp2 F sig.asList sig.retTp) fun cf => do
            let rest ← buildTele (i + 1) (resolved.push (sig, cf))
            mkAppOptM ``Prog.def_ #[Op, SOp, F, V, mainArgsList, none, sig.asList, sig.retTp,
                                    bodyLam, ← mkLambdaFVars #[cf] rest]
        else
          let mainLam ← withLocalDeclD `args hlistTy fun h => do
            mkLambdaFVars #[h] (← walkMain (some resolved) h)
          mkAppOptM ``Prog.main #[Op, SOp, F, V, mainArgsList, none, mainLam]
      let prog ← buildTele 0 #[]
      mkLambdaFVars #[F, V] prog
    let gTy ← inferType g
    let kc ← mkAppM ``KC #[Op]
    -- the actual (value) arguments as an `HList Tp.denote mainArgs`, for the soundness statement
    let mut argHList ← mkAppOptM ``HList.nil #[none, denoteV]
    for (a, t) in (valueArgs.zip mainArgTps).reverse do
      argHList ← mkAppOptM ``HList.cons #[none, denoteV, t, none, a, argHList]
    let ofFreeFn ← mkAppOptM ``ofFree #[Op, SOp, X]
    -- soundness  fun g => ∀ args, denoteProg (g KC Tp.denote) ⟨args⟩ ≈ ofFree (foo args)
    -- — `denoteProg` lands in `Comp` *directly*; `ofFree` only embeds the source `Free`.
    let pred ← withLocalDeclD `g gTy fun gv => do
      let lhs ← mkAppOptM ``denoteProg #[Op, SOp, none, none, mkAppN gv #[kc, denoteV], argHList]
      let eutt ← mkAppM ``ITree.Eutt #[lhs, mkApp ofFreeFn (foo.beta args)]
      mkLambdaFVars #[gv] (← mkForallFVars args eutt)
    -- proof: `denoteProg (g KC ⟨args⟩) = ofFree (foo args)` directly — `denote`/`denoteProg` and
    -- `ofFree` unfold to the same tree, the `call`-binds fusing via `bind_ret`/`bind_vis`.
    let dpC ← mkAppOptM ``denoteProg #[Op, SOp, none, none, mkAppN g #[kc, denoteV], argHList]
    let eqTy ← mkEq dpC (mkApp ofFreeFn (foo.beta args))
    -- **The compositional soundness proof**: re-walk the source in proof mode and assemble the
    -- `sc_*` congruence lemmas — the source's own in-bounds proofs discharge each erased get/set
    -- `fail` branch (`dif_pos`), and helper calls compose via each helper's own (★)-proof.
    -- No `simp`: the proof term mirrors the source structure.
    let mut psubst : List (FVarId × Expr) := []
    for va in valueArgs do psubst := (va.fvarId!, va) :: psubst
    let penv : Env := { Op, SOp, F := kc, V := denoteV, subst := psubst, defs, pfDefs, inFlight,
                        pf := true }
    let (_, pf?) ← penv.walkTop XTp topBody
    let some proof := pf? | throwError "reflect%: internal: proof mode produced no proof"
    let eqPrf ← mkExpectedTypeHint proof eqTy
    let prf ← mkLambdaFVars args (← mkAppM ``ITree.Eutt.of_eq #[eqPrf])
    mkAppOptM ``Subtype.mk #[gTy, pred, g, prf]

end Freigen
