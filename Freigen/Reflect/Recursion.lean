import Freigen.Reflect.Basic
/-!
# Recursion: reflecting a recursive `Free` function into a `Prog`

A structural-recursive `def f : Nat → A₁ → … → Aₖ → Free Op SOp ρ` (recursion on the **first**
argument; the `Aᵢ` are extra `Tp`-typed state threading through) reflects into a `Prog` with a
**`rec_` node** — its body re-expressed over the call-extended signature (self-calls are the
`CallOp.call` op) at the tupled state `σ := Nat × A₁ × …`, tied by `mrec`, with `main` taking the
`k+1` arguments separately, tupling them (`bin .pair` nodes) and calling it.  Soundness is `mrec`
adequacy: `denoteProg` of the reflected program is `≈ ofFree (f N a₁ …)` for every input.
`mrec_adequacy` is the core lemma (`interp` of a call-body is `≈` to running it with the source
plugged in at each call), parameterised by a **measure** `μ : σ → Nat` (the `Nat` component) that
each self-call strictly decreases; `recSound` packages it, and `reflect%`'s recursive arm emits it,
composing the `main`-call (`bind_ret_right`) with the `rec_` body's adequacy.
-/

namespace Freigen

open Freigen.ITree

variable {Op : Type → Type → Type 1} {SOp : Type → Type} {σ ρ : Type}


/-- Run a call-body with the source `e` plugged in at each `call` (external `base` effects relabelled
    back to `Op`; a scoped block's own calls are plugged too). -/
def runSrc (e : σ → Free Op SOp ρ) :
    {γ : Type} → Free (CallOp Op σ ρ) SOp γ → Free Op SOp γ
  | _, .pure a => .pure a
  | _, .op (.base o) i c => .op o i (fun x => runSrc e (c x))
  | _, .op .call i c => Free.bind (e i) (fun v => runSrc e (c v))
  | _, .hop s b c => .hop s (runSrc e b) (fun x => runSrc e (c x))

/-- Every `call` argument in the body has measure `μ` strictly below `bound`. -/
def callsLt (μ : σ → Nat) (bound : Nat) : {γ : Type} → Free (CallOp Op σ ρ) SOp γ → Prop
  | _, .pure _ => True
  | _, .op (.base _) _ c => ∀ x, callsLt μ bound (c x)
  | _, .op .call i c => μ i < bound ∧ ∀ x, callsLt μ bound (c x)
  | _, .hop _ b c => callsLt μ bound b ∧ ∀ x, callsLt μ bound (c x)

/-- **The adequacy step.** Interpreting a call-body is `≈` to running it with the source plugged in,
    given the source is adequate below `bound` and the body only calls below `bound`. -/
theorem adeqBody (body : σ → Comp (CallOp Op σ ρ) ρ) (e : σ → Free Op SOp ρ) (μ : σ → Nat)
    (bound : Nat) (Ho : ∀ k, μ k < bound → mrec body k ≈ ofFree (e k)) :
    ∀ {γ : Type} (t : Free (CallOp Op σ ρ) SOp γ), callsLt μ bound t →
      interp body (ofFree t) ≈ ofFree (runSrc e t) := by
  intro γ t
  induction t with
  | pure a => intro _; simp only [ofFree, runSrc, interp_ret]; exact eutt_refl _
  | op o i c ih =>
      cases o with
      | base o' =>
          intro h
          simp only [ofFree, runSrc, interp_vis_base]
          exact eutt_vis_cong _ (fun x => ih x (h x))
      | call =>
          intro h
          simp only [ofFree, runSrc, interp_vis_call, interp_bind, ofFree_bind]
          refine eutt_tau_left ?_
          exact eutt_bind_cong (Ho i h.1) (fun x => ih x (h.2 x))
  | hop s b c ihb ihc =>
      intro h
      simp only [ofFree, runSrc, interp_bind]
      exact eutt_bind_cong (ihb h.1) (fun x => ihc x (h.2 x))

/-- **`mrec` adequacy (strong-induction shell on the measure)** over `ofFree`: the whole reflected
    recursion is `≈` its source, given each step is adequate using the adequacy of all
    measure-smaller arguments. -/
theorem mrec_adequacy (body : σ → Comp (CallOp Op σ ρ) ρ) (e : σ → Free Op SOp ρ) (μ : σ → Nat)
    (Hstep : ∀ N, (∀ k, μ k < μ N → mrec body k ≈ ofFree (e k)) → mrec body N ≈ ofFree (e N)) :
    ∀ N, mrec body N ≈ ofFree (e N) := by
  suffices H : ∀ n N, μ N ≤ n → mrec body N ≈ ofFree (e N) from fun N => H (μ N) N (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
      intro N hN
      exact Hstep N (fun k hk => absurd (Nat.lt_of_lt_of_le hk hN) (Nat.not_lt_zero _))
  | succ n ih =>
      intro N hN
      exact Hstep N (fun k hk => ih k (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hk hN)))

/-- `adeqBody` with the `runSrc = e` bridge folded in — one step discharged against the source. -/
theorem adeqBody' (body : σ → Comp (CallOp Op σ ρ) ρ) (e : σ → Free Op SOp ρ) (μ : σ → Nat)
    (N : σ) (t : Free (CallOp Op σ ρ) SOp ρ)
    (IH : ∀ k, μ k < μ N → mrec body k ≈ ofFree (e k)) (hcl : callsLt μ (μ N) t)
    (hrun : runSrc e t = e N) :
    interp body (ofFree t) ≈ ofFree (e N) := by
  rw [← hrun]; exact adeqBody body e μ (μ N) IH t hcl

/-- **Generic recursion soundness** — what `reflect%` emits.  Given the reflected call-body
    `body` (a `Code` over the call-extended signature) and the source `f`, provided each call's
    measure is below its argument's (`hcl`) and running the body with `f` plugged in recovers `f`
    (`hrun`), the `mrec` denotation is `≈ ofFree ∘ f`.  Packages `mrec_adequacy` + `adeqBody'`. -/
theorem recSound {σT ρT : Tp} (μ : σT.denote → Nat)
    (body : σT.denote →
      Code (CallOp Op σT.denote ρT.denote) SOp (KC (CallOp Op σT.denote ρT.denote)) Tp.denote ρT)
    (cb : σT.denote → Free (CallOp Op σT.denote ρT.denote) SOp ρT.denote)
    (f : σT.denote → Free Op SOp ρT.denote)
    (hspec : ∀ N, denote (body N) = ofFree (cb N))
    (hrun : ∀ N, runSrc f (cb N) = f N)
    (hcl : ∀ N, callsLt μ (μ N) (cb N)) :
    ∀ N, mrec (fun s => denote (body s)) N ≈ ofFree (f N) := by
  have hbody : (fun s => denote (body s)) = fun s => ofFree (cb s) := funext hspec
  intro N
  rw [hbody]
  refine mrec_adequacy _ f μ ?_ N
  intro M IH
  exact adeqBody' _ _ μ _ _ IH (hcl M) (hrun M)

/-! ## The `reflect%` elaborator

`reflect% f` reflects a structural-recursive `def f : Nat → A₁ → … → Aₖ → Free Op SOp ρ` into the
recursion denotation `mrec` at the tupled state `σ := Nat × A₁ × …` and bundles its soundness
`{ g // ∀ N a₁ …, denoteProg (g …) ⟨N, a₁, …⟩ ≈ ofFree (f N a₁ …) }`.  It recognises the recursion
(its equational lemmas, matching `0`/`n+1` on the first argument), re-expresses the body over
`CallOp` (self-calls, re-tupled, → `CallOp.call`), reflects that into a dumb `Code`, and discharges
soundness via `recSound` at the measure `μ := fun s => s.1`. -/

open Lean Lean.Meta Lean.Elab.Term

/-- Right-nested host product type `A₀ × (A₁ × …)` (singleton = the type itself). -/
private def mkProdTy : List Expr → Expr
  | [t]     => t
  | t :: ts => mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) t (mkProdTy ts)
  | []      => Lean.mkConst ``Unit []

/-- Right-nested reified product `Tp` (`t₀ ×ₚ (t₁ ×ₚ …)`; singleton = the `Tp` itself). -/
private def prodTpOf : List Expr → Expr
  | [t]     => t
  | t :: ts => mkApp2 (Lean.mkConst ``Tp.prod []) t (prodTpOf ts)
  | []      => Lean.mkConst ``Tp.unit []

/-- Host projections of `s : A₀ × (A₁ × …)` — one per component, with explicit type arguments
    (pure, so usable on open terms). -/
private def mkTupleProjs (tps : List Expr) (s : Expr) : List Expr :=
  match tps with
  | []  => []
  | [_] => [s]
  | t :: ts =>
      let tailTy := mkProdTy ts
      mkApp3 (Lean.mkConst ``Prod.fst [.zero, .zero]) t tailTy s ::
        mkTupleProjs ts (mkApp3 (Lean.mkConst ``Prod.snd [.zero, .zero]) t tailTy s)

/-- Right-nested host tuple `⟨a₀, ⟨a₁, …⟩⟩` with explicit type arguments (pure, so usable on open
    terms — the self-call rewrite runs under binders). -/
private def mkTupleE (tps args : List Expr) : Expr :=
  match tps, args with
  | [_], [a] => a
  | t :: ts, a :: as =>
      mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) t (mkProdTy ts) a (mkTupleE ts as)
  | _, _ => Lean.mkConst ``Unit []   -- unreachable: arity ≥ 1 throughout

/-- Rewrite every full application `f e₀ … eₖ` of the recursive function into `rec ⟨e₀, …⟩`. -/
private def rewriteSelfCalls (cName : Name) (recV : Expr) (tps : List Expr) (arity : Nat)
    (e : Expr) : MetaM Expr :=
  Core.transform e (post := fun node => do
    if node.getAppFn.isConstOf cName && node.getAppArgs.size == arity then
      return .done (mkApp recV (mkTupleE tps node.getAppArgs.toList))
    return .continue)

/-- Recognise a **structural recursion on the first argument**
    `f : Nat → A₁ → … → Aₖ → Free Op SOp ρ` (two equations matching `0`/`n+1`; `k ≥ 0`; the
    telescope non-dependent) and rebuild its recursion functional over the tupled state
    `σ := Nat × A₁ × …`:

    `fun rec s => bif s.1 == 0 then base[s.2…] else step[rec, s.1 - 1, s.2…]`

    with self-calls re-tupled.  Returns `(F, σ → Free Op SOp ρ, host argument types)`. -/
private def reflectStructuralRec (fn : Expr) : MetaM (Option (Expr × Expr × Array Expr)) := do
  let some cName := fn.constName? | return none
  let some eqns ← getEqnsFor? cName | return none
  if eqns.size != 2 then return none
  forallTelescope (← inferType fn) fun xs cod => do
    if xs.size == 0 then return none
    let mut tps : Array Expr := #[]
    for x in xs do tps := tps.push (← inferType x)
    unless ← isDefEq tps[0]! (.const ``Nat []) do return none
    let_expr Free _ _ _ := (← whnf cod) | return none
    -- the telescope must be non-dependent (the state is a plain tuple type)
    for i in [0:xs.size] do
      if cod.containsFVar xs[i]!.fvarId! then return none
      for j in [i+1:xs.size] do
        if tps[j]!.containsFVar xs[i]!.fvarId! then return none
    let σT := mkProdTy tps.toList
    let recTy' ← mkArrow σT cod
    -- extract base/step from the two equations, classified by the first-argument pattern.
    -- The equation's *binder order* is not the argument order, so abstract the rhs over the
    -- pattern variables **by their position in the LHS** (each must be a plain variable).
    let extract (nm : Name) : MetaM (Option Expr × Option Expr) := do
      let some ci := (← getEnv).find? nm | return (none, none)
      forallTelescope ci.type fun _bs body => do
        match_expr body with
        | Eq _ lhs rhs =>
          let args := lhs.getAppArgs
          if args.size != xs.size then return (none, none)
          unless (args[1:] : Array Expr).all (·.isFVar) do return (none, none)
          match_expr args[0]! with
          | Nat.succ m =>
              unless m.isFVar do return (none, none)
              return (none, some (← mkLambdaFVars (#[m] ++ args[1:]) rhs))
          | _ =>
              return (some (← mkLambdaFVars args[1:] rhs), none)
        | _ => return (none, none)
    let (r01, s1) ← extract eqns[0]!
    let (r02, s2) ← extract eqns[1]!
    let some base := r01 <|> r02 | return none
    let some stepF := s1 <|> s2 | return none
    unless (stepF.find? (·.isConstOf cName)).isSome do return none
    withLocalDeclD `rec recTy' fun rec =>
    withLocalDeclD `s σT fun s => do
      let projs := (mkTupleProjs tps.toList s).toArray
      let condE ← mkAppM ``BEq.beq #[projs[0]!, mkNatLit 0]
      let km1 ← mkAppM ``HSub.hSub #[projs[0]!, mkNatLit 1]
      let baseE := base.beta projs[1:]
      let stepE ← rewriteSelfCalls cName rec tps.toList xs.size (stepF.beta (#[km1] ++ projs[1:]))
      let bifE ← mkAppM ``cond #[condE, baseE, stepE]
      return some (← mkLambdaFVars #[rec, s] bifE, recTy', tps)

/-- Re-express a recursion body over the `CallOp Op σ ρ` signature: self-calls (`recId _`) become the
    `call` effect, external effects `base`, `pure`/`bind`/`bif` rebuilt structurally. -/
private partial def toCallBody (recId : FVarId) (Op SOp σT ρT : Expr) (t : Expr) : MetaM Expr := do
  let t := t.consumeMData.headBeta
  if let .letE _ _ v b _ := t then return ← toCallBody recId Op SOp σT ρT (b.instantiate1 v)
  let callOp := mkAppN (.const ``ITree.CallOp []) #[Op, σT, ρT]
  if t.getAppFn.isFVar && t.getAppFn.fvarId! == recId then
    let some arg := t.getAppArgs.back? | throwError "reflect%: self-call has no argument"
    let callC := mkAppN (.const ``ITree.CallOp.call []) #[Op, σT, ρT]
    let pureC ← mkAppOptM ``Free.pure #[callOp, SOp, ρT]
    return ← mkAppM ``Free.op #[callC, arg, pureC]
  let doBind (x f : Expr) : MetaM Expr := do
    let .forallE _ X _ _ := (← whnf (← inferType f)) | throwError "reflect%: bind cont not a function"
    let xC ← toCallBody recId Op SOp σT ρT x
    let fC ← withLocalDeclD `a X fun ha => do
      mkLambdaFVars #[ha] (← toCallBody recId Op SOp σT ρT (f.beta #[ha]))
    mkAppM ``Free.bind #[xC, fC]
  match_expr t with
  | Free.pure _ _ _ r => mkAppOptM ``Free.pure #[callOp, SOp, none, r]
  | Pure.pure _ _ _ r => mkAppOptM ``Free.pure #[callOp, SOp, none, r]
  | Bind.bind _ _ _ _ x f => doBind x f
  | Free.bind _ _ _ _ x f => doBind x f
  | cond _ c m1 m2 => do
      let a ← toCallBody recId Op SOp σT ρT m1
      let b ← toCallBody recId Op SOp σT ρT m2
      mkAppM ``cond #[c, a, b]
  | Free.op _ _ _ I R o i k => do
      let baseO := mkAppN (.const ``ITree.CallOp.base []) #[Op, σT, ρT, I, R, o]
      let kC ← withLocalDeclD `x R fun hx => do
        mkLambdaFVars #[hx] (← toCallBody recId Op SOp σT ρT (k.beta #[hx]))
      mkAppM ``Free.op #[baseO, i, kC]
  | Free.hop _ _ _ β s b k => do
      let bC ← toCallBody recId Op SOp σT ρT b
      let kC ← withLocalDeclD `x β fun hx => do
        mkLambdaFVars #[hx] (← toCallBody recId Op SOp σT ρT (k.beta #[hx]))
      mkAppM ``Free.hop #[s, bC, kC]
  | _ =>
      match ← unfoldDefinition? t with
      | some t' => toCallBody recId Op SOp σT ρT t'
      | none    => throwError "reflect%: cannot reflect recursion body{indentExpr t}"

/-- `Code` assembling the right-nested tuple of `atoms` (typed by the reified `tps`) via
    `bin .pair` nodes, feeding the tuple atom to `kont` (singleton: the atom itself). -/
private partial def buildTupleCode (Op SOp Fp Vp ρTp : Expr) (tps atoms : List Expr)
    (kont : Expr → MetaM Expr) : MetaM Expr := do
  match tps, atoms with
  | [_], [a] => kont a
  | t :: ts, a :: as =>
      buildTupleCode Op SOp Fp Vp ρTp ts as fun tailAtom => do
        let bTp := prodTpOf ts
        let pairOp := mkApp2 (.const ``Bin.pair []) t bTp
        let resTp := mkApp2 (.const ``Tp.prod []) t bTp
        withLocalDeclD `p (mkApp Vp resTp) fun vp => do
          let inner ← kont vp
          mkAppOptM ``Code.bin #[Op, SOp, Fp, Vp, ρTp, t, bTp, resTp, pairOp, a, tailAtom,
                                 ← mkLambdaFVars #[vp] inner]
  | _, _ => throwError "reflect%: internal: tuple arity mismatch"

/-- Reflect a structural-recursive `def f : Nat → A₁ → … → Aₖ → Free Op SOp ρ` into
    `{ g // ∀ N a₁ …, denoteProg (g …) ⟨N, a₁, …⟩ ≈ ofFree (f N a₁ …) }` — the `mrec` denotation at
    the tupled state and its soundness.  The recursive arm of `reflect%`. -/
def reflectRec (F recTy : Expr) (tps : Array Expr) (cName : Name) : TermElabM Expr := do
  let .forallE _ σT codom _ := (← whnf recTy) | throwError "reflect%: recursion must be a function"
  let_expr Free Op SOp ρT := (← whnf codom)
    | throwError "reflect%: recursion result must be `Free Op SOp _`"
  let callOp := mkAppN (.const ``ITree.CallOp []) #[Op, σT, ρT]
  let σTp ← reifyTpOrThrow σT
  let ρTp ← reifyTpOrThrow ρT
  let mainTps ← tps.mapM (fun t => do reifyTpOrThrow t)   -- one `main` argument per source argument
  let kcCallOp ← mkAppM ``KC #[callOp]
  let denoteV := Lean.mkConst ``Tp.denote []
  let tpTy := (.const ``Tp [] : Expr)
  let recArgsList ← mkListLit tpTy [σTp]
  let mainArgsList ← mkListLit tpTy mainTps.toList
  let fTy ← mkArrow (← mkAppM ``List #[tpTy]) (← mkArrow tpTy (mkSort (.succ (.succ .zero))))
  let vTy ← mkArrow tpTy (mkSort (.succ .zero))
  let defs ← IO.mkRef (#[] : Array CallSig)
  let pfDefs ← IO.mkRef (#[] : Array PfDefEntry)
  let inFlight ← IO.mkRef (#[] : Array Name)
  let fFn := .const cName []
  -- `fW` : the source over the tupled state; `μE` : the structural measure (the `Nat` component)
  let (fW, μE) ← withLocalDeclD `s σT fun s => do
    let projs := (mkTupleProjs tps.toList s).toArray
    pure (← mkLambdaFVars #[s] (mkAppN fFn projs), ← mkLambdaFVars #[s] projs[0]!)
  -- `cb` : the Free call-body `fun s => …`
  let cb ← withLocalDeclD `s σT fun s => do
    let cbT ← withLocalDeclD `rec recTy fun rec =>
      toCallBody rec.fvarId! Op SOp σT ρT ((F.beta #[rec]).beta #[s])
    mkLambdaFVars #[s] cbT
  -- `recBody` : the `rec_` body `fun V0 F' argAtom => …`, parametric in the value/function reps
  let recBody ← withLocalDeclD `V0 vTy fun Vp0 => withLocalDeclD `F' fTy fun F' =>
    withLocalDeclD `arg (mkApp Vp0 σTp) fun argAtom => do
      let codeT ← withLocalDeclD `s σT fun s => withLocalDeclD `rec recTy fun rec => do
        let cbT ← toCallBody rec.fvarId! Op SOp σT ρT ((F.beta #[rec]).beta #[s])
        let env : Env := { Op := callOp, SOp, F := F', V := Vp0, subst := [(s.fvarId!, argAtom)],
                           defs, pfDefs, inFlight, noSpill := true }
        Prod.fst <$> env.walk ρTp cbT (env.mkRetT ρTp)
      mkLambdaFVars #[Vp0, F', argAtom] codeT
  -- `bodyCode` : `recBody` at `V := Tp.denote`, `F := KC callOp` — what `recSound`/`denoteProg` see
  let bodyCode := recBody.beta #[denoteV, kcCallOp]
  -- the soundness hypotheses (the body homom + `mrec` adequacy side-conditions).
  -- `hspec` (`∀ N, denote (bodyCode N) = ofFree (cb N)`) is a denotation congruence — prove it
  -- **compositionally** (`walkTop` in proof mode), no `simp`.
  let hspecPrf ← withLocalDeclD `N σT fun N => do
    let penv : Env := { Op := callOp, SOp, F := kcCallOp, V := denoteV,
                        subst := [(N.fvarId!, N)], defs, pfDefs, inFlight, noSpill := true,
                        pf := true }
    let (_, pf?) ← penv.walkTop ρTp (cb.beta #[N])
    let some proof := pf? | throwError "reflect%: internal: recursion proof mode produced no proof"
    let want ← mkEq (← mkAppM ``denote #[bodyCode.beta #[N]]) (← mkAppM ``ofFree #[cb.beta #[N]])
    mkLambdaFVars #[N] (← mkExpectedTypeHint proof want)
  -- both side-condition tactics destructure the tuple (when there is one), then case on the `Nat`
  let hrun ← withLocalDeclD `N σT fun N => do
    mkForallFVars #[N] (← mkEq (← mkAppM ``runSrc #[fW, cb.beta #[N]]) (fW.beta #[N]))
  let hrunPrf ← elabTermEnsuringType (← `(by
      intro N
      (first
        | (obtain ⟨n, rest⟩ := N; rcases n with _ | m)
        | rcases N with _ | m) <;>
      (first | rfl | exact Freigen.Free.bind_pure _))) (some hrun)
  let hcl ← withLocalDeclD `N σT fun N => do
    mkForallFVars #[N] (← mkAppM ``callsLt #[μE, mkApp μE N, cb.beta #[N]])
  let hclPrf ← elabTermEnsuringType (← `(by
      intro N
      (first
        | (obtain ⟨n, rest⟩ := N; rcases n with _ | m)
        | rcases N with _ | m) <;>
      (repeat' first | apply And.intro | intro _) <;>
      (try simp only []) <;>   -- beta/proj-normalise the measure applications for `omega`
      (first | omega | trivial))) (some hcl)
  -- `recSoundApp` : ∀ s, mrec (fun s => denote (bodyCode s)) s ≈ ofFree (fW s)   [mrec adequacy]
  let recSoundApp ← mkAppOptM ``recSound
    #[Op, SOp, σTp, ρTp, μE, bodyCode, cb, fW, hspecPrf, hrunPrf, hclPrf]
  -- `g` : the closed `Prog` — `rec_` (the reflected body) then
  -- `main(n, a₁, …) := call frec ⟨(n, a₁, …)⟩` (the tuple built by `bin .pair` nodes)
  let g ← withLocalDeclD `Fp fTy fun Fp => withLocalDeclD `Vp vTy fun Vp => do
    let recBodyG := recBody.beta #[Vp]
    let frecTy := mkApp2 Fp recArgsList ρTp
    let mainK ← withLocalDeclD `frec frecTy fun frec => do
      let mainLam ← withLocalDeclD `hargs (← mkAppM ``HList #[Vp, mainArgsList]) fun hargs => do
        let mut atoms : List Expr := []
        for j in [0:mainTps.size] do atoms := atoms ++ [← projHList hargs j]
        let body ← buildTupleCode Op SOp Fp Vp ρTp mainTps.toList atoms fun tupAtom => do
          let cont ← withLocalDeclD `r (mkApp Vp ρTp) fun r => do
            mkLambdaFVars #[r] (← mkAppOptM ``Code.ret #[Op, SOp, Fp, Vp, ρTp, r])
          let hl ← mkAppOptM ``HList.cons
            #[none, Vp, σTp, none, tupAtom, ← mkAppOptM ``HList.nil #[none, Vp]]
          mkAppOptM ``Code.call #[Op, SOp, Fp, Vp, ρTp, recArgsList, ρTp, frec, hl, cont]
        mkLambdaFVars #[hargs] body
      mkLambdaFVars #[frec] (← mkAppOptM ``Prog.main #[Op, SOp, Fp, Vp, mainArgsList, ρTp, mainLam])
    mkLambdaFVars #[Fp, Vp]
      (← mkAppOptM ``Prog.rec_ #[Op, SOp, Fp, Vp, mainArgsList, ρTp, σTp, ρTp, recBodyG, mainK])
  let closedTy ← mkAppOptM ``Closed #[Op, SOp, mainArgsList, ρTp]
  let kc ← mkAppM ``KC #[Op]
  let ofFreeFn ← mkAppOptM ``ofFree #[Op, SOp, ρT]
  -- the soundness statement binds the `k+1` arguments separately
  let binderDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
    tps.mapIdx (fun i t => (Name.mkSimple s!"a{i}", fun _ => pure t))
  let mkArgsHL (Ns : Array Expr) : MetaM Expr := do
    let mut hl ← mkAppOptM ``HList.nil #[none, denoteV]
    for idx in [0:Ns.size] do
      let j := Ns.size - 1 - idx
      hl ← mkAppOptM ``HList.cons #[none, denoteV, mainTps[j]!, none, Ns[j]!, hl]
    pure hl
  let pred ← withLocalDeclD `g closedTy fun gv => do
    let body ← withLocalDeclsD binderDecls fun Ns => do
      let hl ← mkArgsHL Ns
      let lhs ← mkAppOptM ``denoteProg #[Op, SOp, mainArgsList, ρTp, mkAppN gv #[kc, denoteV], hl]
      mkForallFVars Ns (← mkAppM ``ITree.Eutt #[lhs, mkApp ofFreeFn (mkAppN fFn Ns)])
    mkLambdaFVars #[gv] body
  -- proof: `denoteProg (g KC ⟨args⟩) = mrec (…) ⟨tuple⟩` (the pair nodes are definitional and the
  -- `main`-call closes by bind right-identity), then `recSoundApp ⟨tuple⟩`.
  let bodyFnC ← withLocalDeclD `s σT fun s => do
    mkLambdaFVars #[s] (← mkAppM ``denote #[bodyCode.beta #[s]])
  let proof ← withLocalDeclsD binderDecls fun Ns => do
    let hl ← mkArgsHL Ns
    let lhs ← mkAppOptM ``denoteProg #[Op, SOp, mainArgsList, ρTp, mkAppN g #[kc, denoteV], hl]
    let tupleE := mkTupleE tps.toList Ns.toList
    let rhs ← mkAppM ``mrec #[bodyFnC, tupleE]
    let bridge ← mkExpectedTypeHint (← mkAppM ``ITree.bind_ret_right #[rhs]) (← mkEq lhs rhs)
    let eut ← mkAppM ``ITree.Eutt.trans
      #[← mkAppM ``ITree.Eutt.of_eq #[bridge], mkApp recSoundApp tupleE]
    -- `fW ⟨tuple⟩` projection-reduces to `f a₀ a₁ …` — hint the statement's form
    let target ← mkAppM ``ITree.Eutt #[lhs, mkApp ofFreeFn (mkAppN fFn Ns)]
    mkLambdaFVars Ns (← mkExpectedTypeHint eut target)
  mkAppOptM ``Subtype.mk #[closedTy, pred, g, proof]

/-- Reflect an elaborated source `e`, dispatching between the value/function arm and the recursion
    arm.  Returns the bundled `{ g : Closed … // ‹≈-soundness› }` (a `Subtype.mk`). -/
def reflectExpr (e : Expr) : TermElabM Expr := do
  match_expr (← whnf (← inferType e)) with
  | Free _ _ _ => reflectMain e
  | _ =>
      match ← reflectStructuralRec e.getAppFn with
      | some (F, recTy, tps) =>
          let some cName := e.getAppFn.constName?
            | throwError "reflect%: recursive source is not a definition"
          reflectRec F recTy tps cName
      | none => reflectMain e

/-- **`reflect%`** — the unified entry point.  It does the right thing automatically:

* a `Free Op SOp α` **program value** → a `Prog` with a nullary `main`;
* a program `A₁ → … → Aₙ → Free Op SOp α` (of `Tp`-typed inputs) → a `Prog` whose `main` is a
  function of those inputs;
* a structural-recursive `def f : Nat → A₁ → … → Aₖ → Free Op SOp ρ` (recursion on the first
  argument, extra `Tp`-typed state threading through) → the `mrec` denotation at the tupled state.

Each returns a `{ · // · }` bundling the AST with its `≈`-soundness against the source. -/
elab "reflect% " t:term : term => do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  reflectExpr (← instantiateMVars e)

/-- **`reflect_def C := src`** — reflect `src` (as `reflect%`) and introduce **two named
    definitions**:

* `C` — the closed `Prog`;
* `C_sound` — its `≈`-soundness against `ofFree src`,

so use sites read `C` / `C_sound` instead of projecting `.1`/`.2` out of the bundled `Subtype`
(and goals display the named constants). -/
elab doc:(Lean.Parser.Command.docComment)? "reflect_def " nm:ident " := " t:term : command =>
  Lean.Elab.Command.liftTermElabM do
    let e ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    let packed ← reflectExpr (← instantiateMVars e)
    -- run any tactic blocks the reflection scheduled (the recursion arm's side conditions)
    synthesizeSyntheticMVarsNoPostponing
    let packed ← instantiateMVars packed
    let_expr Subtype.mk _ pred g prf := packed
      | throwError "reflect_def: internal: reflection did not produce a `Subtype.mk`"
    let progName := (← getCurrNamespace) ++ nm.getId
    let soundName := progName.appendAfter "_sound"
    addAndCompile (.defnDecl {
      name := progName, levelParams := [], type := ← inferType g, value := g,
      hints := .abbrev, safety := .safe })
    -- `C := g` definitionally, so the bundled proof also proves the statement *about `C`*
    addDecl (.thmDecl {
      name := soundName, levelParams := [],
      type := pred.beta #[Lean.mkConst progName], value := prf })
    if let some d := doc then
      addDocStringCore progName (← Lean.getDocStringText d)
    Lean.Elab.Term.addTermInfo' nm (Lean.mkConst progName) (isBinder := true)

end Freigen
