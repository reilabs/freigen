import Freigen.Ast.JoinPoints.Rel

/-!
Related states are equivalent up to silent steps: `SR` is a simulation, once
states are read as the computations they run.
-/

namespace Freigen.Ast.JoinPoints

open CompM EvalState

variable {L : Language} {M : L.Model}

/-- The computations of related states. -/
def Rc {γ : L.Ctx} {α : Type} (x y : EvalM L M γ α) : Prop :=
  ∃ st₁ st₂ : EvalState L M (γ, α), SR st₁ st₂ ∧ x = st₁.run ∧ y = st₂.run

theorem Rc.of {γ : L.Ctx} {α : Type} {st₁ st₂ : EvalState L M (γ, α)} (h : SR st₁ st₂) :
    Rc st₁.run st₂.run :=
  ⟨st₁, st₂, h, rfl, rfl⟩

private theorem sync_tick {γ : L.Ctx} {α : Type} {x y : EvalM L M γ α} (h : Rc x y) :
    EuttF Rc (tick >>= fun _ => x) (tick >>= fun _ => y) := by
  rw [tick_bind _ tauBlocks, tick_bind _ tauBlocks]
  exact .op _ (fun t => nomatch Eff.Step.Has.lowerBlockTag (F := Eff.Tau) (E := EvalEff L M) t)
    fun _ => h

private theorem sync_fail {γ : L.Ctx} {α : Type} :
    EuttF Rc (fail : EvalM L M γ α) fail := by
  rw [fail_eq failBlocks failCont]
  exact .op _ (fun t => nomatch Eff.Step.Has.lowerBlockTag (F := Eff.Fail) (E := EvalEff L M) t)
    fun o => nomatch Eff.Step.Has.lowerOutput (F := Eff.Fail) (E := EvalEff L M) o

/-- Continuations that finish a block or a program: their results are
equal, at ABI types. -/
private theorem kr_done {γ : L.Ctx} {t : L.AbiTp} {ρ : Refs} {h₁ h₂ : Heap L M} :
    KR (R := M.V t.val) (γ := γ) .normal ρ h₁ h₂ (fun _ r => .done r) (fun _ r => .done r) :=
  .normal fun _ _ _ _ _ _ _ hv => VRel.eq_abi hv ▸ .done _

/-- One step of the simulation, for states evaluating related nodes. -/
theorem step_expr (hprim : L.PrimFnFree) {γ : L.Ctx} {R : Type} {o o' : L.Tp}
    {m : RMode M.V γ o o'} {Δ : WfCtx L M.V M.V} {ρ : Refs} {h₁ h₂ : Heap L M}
    {e₁ : Expr L M.V γ o} {e₂ : Expr L M.V γ o'}
    {K₁ K₁' : Heap L M → M.V o → EvalState L M (γ, R)}
    {K₂ : Heap L M → M.V o' → EvalState L M (γ, R)}
    (s : JPs Δ m e₁ e₂) (hH : HRel ρ h₁ h₂) (hΔ : VRelCtx ρ Δ) (hK : KR m ρ h₁ h₂ K₁ K₂)
    (hP : Pad K₁ K₁') :
    EuttF Rc (cont h₁ e₁ K₁').run (cont h₂ e₂ K₂).run := by
  cases s with
  | ret hx =>
    cases hK with
    | normal hk =>
      rw [run_ret, run_ret]
      exact sync_tick (.of (SR.padL hP (hk ρ h₁ h₂ (.refl ..) hH _ _ (hΔ _ hx))))
  | lit hk =>
    rw [run_lit, run_lit]
    exact sync_tick (.of (build (hk _ _) hH (hΔ.cons (VRel.refl_abi _)) hK hP))
  | @builtin _ _ _ _ _ _ _ b a₁ a₂ _ _ ha hk =>
    have hr := Builtin.denote_rel hprim b (hΔ.args ha)
    rcases hb₁ : b.denote M a₁ with _ | r₁ <;> rcases hb₂ : b.denote M a₂ with _ | r₂ <;>
      rw [hb₁, hb₂] at hr
    · rw [run_builtin_none _ hb₁, run_builtin_none _ hb₂]
      exact sync_fail
    · cases hr
    · cases hr
    · cases hr with
      | some hr =>
        rw [run_builtin _ hb₁, run_builtin _ hb₂]
        exact sync_tick (.of (build (hk r₁ r₂) hH (hΔ.cons hr) hK hP))
  | @lam _ _ _ _ _ _ _ b₁ b₂ _ _ hb hk =>
    rw [run_lam, run_lam]
    have hmono : ∀ a b, ρ a b → ρ a b ∨ a = (h₁.alloc fun _ x => b₁ x).2 ∧
        b = (h₂.alloc fun _ x => b₂ x).2 := fun _ _ h => .inl h
    have hΔ' := hΔ.mono hmono
    refine sync_tick (.of (build (hk _ _)
      (hH.alloc (fun _ x => b₁ x) (fun _ x => b₂ x) hΔ' fun x₁ x₂ => hb x₁ x₂)
      (hΔ'.cons (.inr ⟨rfl, rfl⟩))
      (hK.mono ⟨hmono, Heap.le_alloc _ _, Heap.le_alloc _ _⟩) hP))
  | @app _ _ _ _ _ _ _ f₁ f₂ x₁ x₂ _ _ hf hx hk =>
    obtain ⟨γ₀, i₀, o₀, g₁, g₂, hg₁, hg₂, Δg, hΔg, hbody⟩ := hH f₁ f₂ (hΔ _ hf)
    rcases hl₁ : h₁.lookup (γ := γ) f₁ with _ | g₁'
    · have hl₂ : h₂.lookup (γ := γ) f₂ = none := by
        rcases hl₂ : h₂.lookup (γ := γ) f₂ with _ | g₂'
        · rfl
        · obtain ⟨rfl, rfl, rfl⟩ := Heap.lookup_types hg₂ hl₂
          rw [hg₁] at hl₁
          cases hl₁
      rw [run_app_none _ hl₁, run_app_none _ hl₂]
      exact sync_fail
    · obtain ⟨rfl, rfl, rfl⟩ := Heap.lookup_types hg₁ hl₁
      rw [hg₁] at hl₁
      cases hl₁
      rw [run_app _ hg₁, run_app _ hg₂]
      exact sync_tick (.of (build (hbody x₁ x₂) hH (hΔg.cons (hΔ _ hx))
        (.normal fun ρ' h₁' h₂' he hH' v₁ v₂ hv =>
          build (hk v₁ v₂) hH' ((hΔ.mono he.1).cons hv) (hK.mono he) hP)
        (.refl _)))
  | @ite _ _ _ _ _ _ c₁ c₂ _ _ _ _ _ _ hc ht he hk =>
    have hc' : c₁ = c₂ := hΔ _ hc
    subst hc'
    rw [run_ite, run_ite]
    have kr : KR .normal ρ h₁ h₂ _ _ := .normal fun ρ' h₁' h₂' he hH' v₁ v₂ hv =>
      build (hk v₁ v₂) hH' ((hΔ.mono he.1).cons hv) (hK.mono he) hP
    cases c₁
    · exact sync_tick (.of (build he hH hΔ kr (.refl _)))
    · exact sync_tick (.of (build ht hH hΔ kr (.refl _)))
  | @iteJump _ _ _ _ _ j κ c₁ c₂ _ _ _ _ hc ht he =>
    have hc' : c₁ = c₂ := hΔ _ hc
    subst hc'
    rw [run_ite, run_ite]
    have kr : KR (.jump j fun v => .ret v) ρ h₁ h₂ (fun s r => cont s (.ret r) K₁')
        (fun s r => cont s (κ r) K₂) := by
      cases hK with
      | scope hl hb => exact .branch hl hb (.step hP) (.refl _)
      | branch hl hb hp₁ hp₂ => exact .branch hl hb (.step (hp₁.trans hP)) (.step hp₂)
    cases c₁
    · exact sync_tick (.of (build he hH hΔ kr (.refl _)))
    · exact sync_tick (.of (build ht hH hΔ kr (.refl _)))
  | @loop _ _ _ _ _ c b₁ b₂ i₁ i₂ k₁ k₂ hi hb hk =>
    rw [run_loop, run_loop]
    refine sync_tick (.of (build (hb i₁ i₂) hH (hΔ.cons (hΔ _ hi))
      (.normal fun ρ' h₁' h₂' he hH' v₁ v₂ hv => ?_) (.refl _)))
    rcases v₁ with ⟨a₁, d₁⟩
    rcases v₂ with ⟨a₂, d₂⟩
    obtain ⟨ha, hd⟩ := hv
    cases (hd : d₁ = d₂)
    have hΔ' := (hΔ.mono he.1).cons ha
    cases d₁
    · exact build (hk a₁ a₂) hH' hΔ' (hK.mono he) hP
    · have hsub : ∀ x ∈ Δ, x ∈ (⟨c, a₁, a₂⟩ :: Δ) := fun _ h => List.mem_cons_of_mem _ h
      exact .expr (.loop List.mem_cons_self
        (fun x₁ x₂ => (hb x₁ x₂).weaken (cons_sub hsub _))
        fun r₁ r₂ => (hk r₁ r₂).weaken (cons_sub hsub _)) hH' hΔ' (hK.mono he) hP
  | @op _ _ _ _ _ e i₁ i₂ bl₁ bl₂ _ _ hi hb hk =>
    have hi' : i₁ = i₂ := VRel.eq_abi (hΔ _ hi)
    subst hi'
    rw [run_op, run_op]
    exact .op _
      (fun t x => .of (build (hb t x x) hH (hΔ.cons (VRel.refl_abi x)) kr_done (.refl _)))
      fun r => .of (build (hk r r) hH (hΔ.cons (VRel.refl_abi r)) hK hP)

/-- `SR` is a simulation. -/
theorem step (hprim : L.PrimFnFree) {i : L.Ctx × Type} {st₁ st₂ : EvalState L M i}
    (h : SR st₁ st₂) : EuttF Rc st₁.run st₂.run := by
  induction h using SR.rec (motive_2 := fun _ _ _ _ _ _ _ => True) with
  | done r =>
    simp only [run_done]
    exact .pure r
  | tauL _ ih =>
    rw [run_ret]
    exact .tauL ih
  | tauR _ ih =>
    rw [run_ret]
    exact .tauR ih
  | alloc _ ih =>
    rw [run_lam]
    exact .tauL ih
  | call hl _ ih =>
    rw [run_app _ hl]
    exact .tauL ih
  | expr s hH hΔ hK hP _ => exact step_expr hprim s hH hΔ hK hP
  | normal => trivial
  | scope => trivial
  | branch => trivial

theorem SR.eutt (hprim : L.PrimFnFree) {γ : L.Ctx} {α : Type} {st₁ st₂ : EvalState L M (γ, α)}
    (h : SR st₁ st₂) : Eutt st₁.run st₂.run :=
  Eutt.coind Rc (fun ⟨_, _, h, hx, hy⟩ => hx ▸ hy ▸ step hprim h) (.of h)

/-! ## Programs -/

theorem Program.JP.eutt_go (hprim : L.PrimFnFree) {mainCtx : L.Ctx} {iT oT : L.AbiTp}
    {Δ : WfCtx L M.V M.V} {p₁ p₂ : Program L mainCtx iT oT M.V} (hp : Program.JP Δ p₁ p₂)
    {ρ : Refs} {h₁ h₂ : Heap L M} (hH : HRel ρ h₁ h₂) (hΔ : VRelCtx ρ Δ) (x : M.V iT.val) :
    Eutt (Prod.snd <$> Program.denote'.go x h₁ p₁) (Prod.snd <$> Program.denote'.go x h₂ p₂) := by
  induction hp generalizing ρ h₁ h₂ with
  | @define Δ γ inp out body₁ body₂ k₁ k₂ hb _ ih =>
    rw [Program.denote'_go_define, Program.denote'_go_define]
    have hmono : ∀ a b, ρ a b → ρ a b ∨ a = (h₁.alloc fun f x => body₁ f x).2 ∧
        b = (h₂.alloc fun f x => body₂ f x).2 := fun _ _ h => .inl h
    have hΔ' := (hΔ.mono hmono).cons (t := .fn inp out) (.inr ⟨rfl, rfl⟩)
    exact ih _ _ (hH.alloc (fun f x => body₁ f x) (fun f x => body₂ f x) hΔ'
      fun x₁ x₂ => hb _ _ x₁ x₂) hΔ'
  | main hb =>
    rw [Program.denote'_go_main, Program.denote'_go_main]
    have hrun : ∀ (s : Heap L M) (e : Expr L M.V mainCtx oT.val),
        Prod.snd <$> e.denote s = (cont s e fun _ r => done r).run := by
      intro s e
      rw [Expr.run_cont]
      simp only [run_done, bind_pure_comp]
    rw [hrun, hrun]
    exact SR.eutt hprim (build (hb x x) hH (hΔ.cons (VRel.refl_abi x)) kr_done (.refl _))

/-- Related programs are equivalent on every input. -/
theorem Program.JP.eutt (hprim : L.PrimFnFree) {mainCtx : L.Ctx} {iT oT : L.AbiTp}
    {p₁ p₂ : Program L mainCtx iT oT M.V} (hp : Program.JP [] p₁ p₂) (x : M.V iT.val) :
    Eutt (p₁.denote x) (p₂.denote x) := by
  rw [Program.denote_eq, Program.denote_eq]
  exact hp.eutt_go hprim (ρ := fun _ _ => False) (fun _ _ h => h.elim) (fun _ h => nomatch h) x

end Freigen.Ast.JoinPoints
