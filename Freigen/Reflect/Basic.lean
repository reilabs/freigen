import Freigen.Ast
import Freigen.Free
import Freigen.ITree
import Freigen.Reflect.Sound
/-! ## The `reflect%` reflector — value arm

Reflects a `Free Op SOp α` program (which may call top-level helper functions) into a `Prog`: pure
computation is A-normalised into `un`/`bin`/`lit`; effects/scoped blocks pass through; **calls to
helper functions become `call` nodes, monomorphised and spilled as `def_`s** (a two-pass
discovery/build).

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

/-- A discovered (monomorphised) function spill: name, argument object-types, result object-type,
    and the reflected body `HList V as → Code …`. -/
structure DefEntry where
  name    : Name
  asList  : Expr
  retTp   : Expr
  bodyLam : Expr
  deriving Inhabited

/-- The proof-mode twin of `DefEntry`: a helper's concrete subroutine `cf` and its parametric
    (★)-proof `bodyProof : ∀ hargs, cf hargs = ofFree …`, built **once** per monomorphised
    signature and reused at every call site (a helper called `N` times would otherwise embed `N`
    copies of its body proof in the final term). -/
structure PfDefEntry where
  name      : Name
  asList    : Expr
  retTp     : Expr
  cf        : Expr
  bodyProof : Expr
  deriving Inhabited

/-- The reflection environment: the `Op`/`SOp`/`F`/`V` we build against, a substitution from
    continuation-bound host placeholders to object atoms, the running spill cache, whether we are
    inside a function body (bodies may not call), on the build pass the resolved names, and the
    walk **mode** (`pf`). -/
structure Env where
  Op : Expr
  SOp : Expr
  F : Expr
  V : Expr
  subst : List (FVarId × Expr)
  defs : IO.Ref (Array DefEntry)
  /-- Proof-mode helper cache (`cf` + body proof per monomorphised signature). -/
  pfDefs : IO.Ref (Array PfDefEntry)
  inBody : Bool := false
  resolved : Option (Array (DefEntry × Expr)) := none
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

/-- Extract a `Nat` literal, seeing through `OfNat.ofNat`. -/
def natLitOf (e : Expr) : Option Nat :=
  e.nat? <|> (match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_, n, _]) => n.nat?
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

/-- A call-site analysis: the callee, its instantiated value, the split of its arguments into type
    parameters vs value arguments, and the reified signature.  Shared by both walk modes. -/
structure CallSig where
  cName     : Name
  cValInst  : Expr
  fArgs     : Array Expr
  valuePos  : Array Nat
  valueArgs : List Expr
  argTps    : Array Expr
  asList    : Expr
  retTp     : Expr

/-- Classify `e` as a call to a reflectable top-level helper: a constant with a value, not an
    effect/scoped smart-constructor (those inline), with at least one value argument, all value
    arguments and the result reifying to `Tp`s.  `none` means "not a call — keep unfolding". -/
def analyzeCall (e : Expr) : MetaM (Option CallSig) := do
  let fn := e.getAppFn
  let some cName := fn.constName? | return none
  let some ci := (← getEnv).find? cName | return none
  let some cVal := ci.value? | return none
  let fArgs := e.getAppArgs
  let cValInst := cVal.instantiateLevelParams ci.levelParams fn.constLevels!
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
  let mut argTps : Array Expr := #[]
  for va in valueArgs do
    let some t ← reifyTp (← inferType va) | return none
    argTps := argTps.push t
  let asList ← mkListLit (.const ``Tp []) argTps.toList
  let some retTp ← (match_expr (← whnf (← inferType e)) with
                      | Free _ _ R => reifyTp R | _ => pure none) | return none
  return some { cName, cValInst, fArgs, valuePos, valueArgs, argTps, asList, retTp }

mutual
  /-- Reflect a *pure* host value into a `Code` atom, A-normalising into `un`/`bin`/`lit`/collection
      node chains, then feed the atom to `k`.  In proof mode the continuation also returns the step's
      equation, so proofs thread through in one pass; every non-`get`/`set` step is definitional, and
      a get/set/cast inserts exactly `sc_*` (= `dif_pos h`, the source's own proof).  `resTp` is the
      overall result `Tp` (the sc-lemmas' `α`, unrecoverable through `Tp.denote`). -/
  partial def Env.atom (env : Env) (resTp a : Expr) (k : Expr → MetaM CodePf) : MetaM CodePf := do
    let a ← instantiateMVars a
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
        -- `Bin.pow` is `Nat`-only; give a readable error for field `x ^ n` instead of a deep
        -- unification failure (reflected field pow needs a `powZ` primitive first)
        match_expr ← reifyTpOrThrow (← inferType a) with
        | Tp.nat => env.emitBin resTp (.const ``Bin.pow []) (.const ``Tp.nat []) x y k
        | _ => throwError "reflect%: `^` is only supported at `Nat` — field exponentiation is not \
                           reflected yet:{indentExpr a}"
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
    | _ => throwError "reflect%: cannot reflect operand (not an atom or supported primitive):{indentExpr a}"

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

  /-- Top-level walk (continuation `ret`, so `Kf = ret`); in proof mode close (★) with
      `bind_ret_right`, giving `denote code = ofFree e`.  `resTp` is `e`'s result `Tp`. -/
  partial def Env.walkTop (env : Env) (resTp e : Expr) : MetaM CodePf := do
    let (code, pf?) ← env.walk resTp e (env.mkRetT resTp)
    let pf? ← pf?.mapM fun proof =>
      do eqTransD proof (← mkAppM ``ITree.bind_ret_right #[← mkAppM ``ofFree #[e]])
    return (code, pf?)

  /-- Try to reflect `e` as a **call** to a top-level helper function (`analyzeCall`), dispatching on
      the mode: abstract mode monomorphises and spills/resolves; proof mode builds the concrete
      subroutine with its own (★)-proof. -/
  partial def Env.tryCall (env : Env) (resTp e : Expr) (k : Expr → MetaM Expr) : MetaM (Option CodePf) := do
    if env.inBody then return none
    let some sig ← analyzeCall e | return none
    if env.pf then return some (← env.callWithProof resTp sig k)
    else env.callAbstract resTp sig k

  /-- Abstract-mode call: monomorphise on `(name, arg-tps, ret-tp)`, spill the specialised body as a
      `def_` (discovery pass) or emit a `call` to its resolved name (build pass). -/
  partial def Env.callAbstract (env : Env) (resTp : Expr) (sig : CallSig) (k : Expr → MetaM Expr) :
      MetaM (Option CodePf) := do
    let sigMatches (d : DefEntry) : MetaM Bool :=
      return d.name == sig.cName && (← isDefEq d.asList sig.asList) && (← isDefEq d.retTp sig.retTp)
    let emit (cf : Expr) : MetaM CodePf :=
      env.atoms resTp sig.valueArgs (fun atoms => do
        pure (← env.emitCall cf sig.asList sig.retTp (← env.mkArgHList atoms) k, none))
    match env.resolved with
    | some resolved =>
        let some (_, cf) ← resolved.findM? (fun de => sigMatches de.1) | return none
        some <$> emit cf
    | none =>
        unless (← (← env.defs.get).findM? sigMatches).isSome do
          let hlistTy ← mkAppM ``HList #[env.V, sig.asList]
          let bodyLam ← withLocalDeclD `args hlistTy fun hargs => do
            let decls : Array (Name × (Array Expr → MetaM Expr)) :=
              sig.valueArgs.toArray.map (fun va => (`x, fun _ => inferType va))
            withLocalDeclsD decls fun hxs => do
              let mut subst := env.subst
              for j in [0:hxs.size] do
                subst := (hxs[j]!.fvarId!, ← projHList hargs j) :: subst
              let mut fullArgs := sig.fArgs
              for j in [0:sig.valuePos.size] do
                fullArgs := fullArgs.set! (sig.valuePos[j]!) hxs[j]!
              let env' := { env with subst, inBody := true }
              let (bcode, _) ← env'.walk sig.retTp (sig.cValInst.beta fullArgs) (env.mkRetT sig.retTp)
              mkLambdaFVars #[hargs] bcode
          env.defs.modify (·.push { name := sig.cName, asList := sig.asList, retTp := sig.retTp, bodyLam })
        some <$> emit (← mkFreshExprMVar (mkApp2 env.F sig.asList sig.retTp))

  /-- Proof-mode call: build the (concrete) subroutine `cf` and its own (★)-proof, reflect the
      arguments, then `sc_call` — the helper's soundness `hcf : cf args = ofFree (helper args)`
      composes with the caller's continuation. -/
  partial def Env.callWithProof (env : Env) (resTp : Expr) (sig : CallSig) (k : Expr → MetaM Expr) :
      MetaM CodePf := do
    -- the concrete subroutine `cf` and its parametric (★)-proof `bodyProof : ∀ hargs, cf hargs = ofFree …`
    -- — built once per monomorphised signature (`pfDefs` cache), reused at every further call site.
    let sigMatches (d : PfDefEntry) : MetaM Bool :=
      return d.name == sig.cName && (← isDefEq d.asList sig.asList) && (← isDefEq d.retTp sig.retTp)
    let (cf, bodyProofLam) ← do
      if let some d ← (← env.pfDefs.get).findM? sigMatches then
        pure (d.cf, d.bodyProof)
      else
        let hlistTy ← mkAppM ``HList #[env.V, sig.asList]
        -- Walk the body with fresh *identity*-mapped value vars `pvs` (so `atom`'s `atom = value`),
        -- then substitute `pvs ↦ projHList hargs` — matching `g`'s spilled `def_` body (which
        -- projects `hargs`).
        let (cf, bodyProofLam) ← withLocalDeclD `args hlistTy fun hargs => do
          let decls : Array (Name × (Array Expr → MetaM Expr)) :=
            sig.valueArgs.toArray.map (fun va => (`x, fun _ => inferType va))
          withLocalDeclsD decls fun pvs => do
            let subst := (pvs.toList.map (fun p => (p.fvarId!, p))) ++ env.subst
            let mut fullArgs := sig.fArgs
            for j in [0:sig.valuePos.size] do fullArgs := fullArgs.set! (sig.valuePos[j]!) pvs[j]!
            let env' := { env with subst, inBody := true }
            let (bcode, bpf?) ← env'.walkTop sig.retTp (sig.cValInst.beta fullArgs)
            let some bproof := bpf? | throwError "reflect%: internal: missing call-body proof"
            let mut projs : Array Expr := #[]
            for j in [0:pvs.size] do projs := projs.push (← projHList hargs j)
            let bcode' := bcode.replaceFVars pvs projs
            let bproof' := bproof.replaceFVars pvs projs
            pure (← mkLambdaFVars #[hargs] (← denoteE bcode'), ← mkLambdaFVars #[hargs] bproof')
        env.pfDefs.modify (·.push { name := sig.cName, asList := sig.asList, retTp := sig.retTp,
                                    cf, bodyProof := bodyProofLam })
        pure (cf, bodyProofLam)
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
end

/-- Reflect a program `foo : A₁ → … → Aₙ → Free Op SOp X` (`n ≥ 0`) into
    `{ g : Closed // ∀ args, denoteProg (g KC Tp.denote) ⟨value-args⟩ ≈ ofFree (foo args) }` — the
    `Prog` whose `main` is a function of the program's inputs (delivered as an `HList`), with a `def_`
    per monomorphised helper.  Each `Aᵢ` that reifies to a `Tp` is a program input; any that does not
    (e.g. an in-bounds proof `j < n` for a symbolic index) is **erased from the AST** and instead
    left quantifying the soundness statement, where it discharges the erased get/set's `fail` branch.
    The non-recursive arm of `reflect%`. -/
def reflectMain (foo : Expr) : TermElabM Expr := do
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
    let defs ← IO.mkRef (#[] : Array DefEntry)
    let pfDefs ← IO.mkRef (#[] : Array PfDefEntry)
    let denoteV := Lean.mkConst ``Tp.denote []
    let topBody := (← unfoldDefinition? (foo.beta args)).getD (foo.beta args)
    let g ← withLocalDeclD `F fTy fun F => withLocalDeclD `V vTy fun V => do
      let hlistTy ← mkAppM ``HList #[V, mainArgsList]
      -- walk `main` under an argument tuple `hargs`, substituting each host argument for its atom
      let walkMain (resolved : Option (Array (DefEntry × Expr))) (hargs : Expr) : MetaM Expr := do
        let mut subst : List (FVarId × Expr) := []
        for i in [0:valueArgs.size] do subst := (valueArgs[i]!.fvarId!, ← projHList hargs i) :: subst
        let env : Env := { Op, SOp, F, V, subst, defs, pfDefs, resolved }
        Prod.fst <$> env.walk XTp topBody (env.mkRetT XTp)
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
    let penv : Env := { Op, SOp, F := kc, V := denoteV, subst := psubst, defs, pfDefs, pf := true }
    let (_, pf?) ← penv.walkTop XTp topBody
    let some proof := pf? | throwError "reflect%: internal: proof mode produced no proof"
    let eqPrf ← mkExpectedTypeHint proof eqTy
    let prf ← mkLambdaFVars args (← mkAppM ``ITree.Eutt.of_eq #[eqPrf])
    mkAppOptM ``Subtype.mk #[gTy, pred, g, prf]

end Freigen
