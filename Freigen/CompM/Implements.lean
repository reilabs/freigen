import Freigen.CompM.WF

/-!
The erasure pipeline that compares a computation over `Fail ⊕ Tau ⊕ E`
against a source computation over `F`, and a compositional
characterization of it.

The pipeline reifies a well-founded computation, elides the unused `Fail`
effect, erases silent steps and interprets the remaining effects through a
handler. Reification and elision have no bind laws of their own: they take
well-foundedness and failure-freedom as proof arguments, and a continuation
may only have those on the results the first computation can actually reach.
Instead, `Implements` is defined by one rule per node shape, composes through
bind on reachable results, and is shown equivalent to the pipeline.
-/

namespace Freigen

open Eff (Fail Tau)

variable {Γ : Type u} {E F : Γ → Type u}
  [sE : Eff.Spec.{u, 0} E] [sF : Eff.Spec.{u, 0} F]
  {γ : Γ} {α β : Type}

/-- Erase silent steps. -/
def Free.eraseTau (y : Free (Tau ⊕ₑ E) γ α) : Free E γ α :=
  y.interpL fun _ _ => pure ()

namespace Free

@[simp]
theorem eraseTau_pure (a : α) :
    eraseTau (pure a : Free (Tau ⊕ₑ E) γ α) = pure a :=
  rfl

@[simp]
theorem eraseTau_bind (y : Free (Tau ⊕ₑ E) γ α)
    (f : α → Free (Tau ⊕ₑ E) γ β) :
    eraseTau (y >>= f) = eraseTau y >>= fun a => eraseTau (f a) :=
  interpL_bind _ y f

@[simp 1100]
theorem eraseTau_tau_bind (t : Tau γ) {blocks}
    (k : PUnit → Free (Tau ⊕ₑ E) γ α) :
    eraseTau (bind (α := no_index _) (op (E := Tau ⊕ₑ E) (.inl t) blocks) k) =
      eraseTau (k ()) := by
  simp only [eraseTau, interpL_bind, interpL_op_inl, pure_bind]

@[simp 1100]
theorem eraseTau_op_bind (e : E γ) {blocks}
    (k : sE.output γ e → Free (Tau ⊕ₑ E) γ α) :
    eraseTau (bind (α := no_index _) (op (E := Tau ⊕ₑ E) (.inr e) blocks) k) =
      op e (fun t i => eraseTau (blocks t i)) >>= fun o => eraseTau (k o) := by
  simp only [eraseTau, interpL_bind, interpL_op_inr]
  rfl

end Free

namespace CompM

variable (handler : Eff.Handler E (Free F))

/-- The erasure pipeline: reify, elide `Fail`, erase `Tau`, and interpret
the remaining effects. -/
def erase (x : CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α) (wf : WF x)
    (nofail : Free.UnusedL (x.toFree wf)) : Free F γ α :=
  ((x.toFree wf).elideL nofail).eraseTau.interp handler

/-- `x` implements the source computation `s`: it is well-founded, never
fails, and erases to `s`. See `implements_iff`. -/
inductive Implements :
    {γ : Γ} → {α : Type} →
    CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α → Free F γ α → Prop
| pure {γ : Γ} {α : Type} (a : α) :
    Implements (pure a : CompM _ γ α) (pure a)
| tick {γ : Γ} {α : Type}
    {k : Unit → CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α} {s : Free F γ α} :
    Implements (k ()) s → Implements (tick >>= k) s
| op {γ : Γ} {α : Type} (e : E γ)
    {blocks :
      (t : sE.blockTag γ e) →
      sE.blockInputs γ e t →
      CompM (Fail ⊕ₑ Tau ⊕ₑ E) (sE.blockCtx γ e t) (sE.blockOutputs γ e t)}
    {k : sE.output γ e → CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α}
    {sb :
      (t : sE.blockTag γ e) →
      sE.blockInputs γ e t →
      Free F (sE.blockCtx γ e t) (sE.blockOutputs γ e t)}
    {sk : sE.output γ e → Free F γ α} :
    (∀ t i, Implements (blocks t i) (sb t i)) →
    (∀ o, Implements (k o) (sk o)) →
    Implements (op (E := Fail ⊕ₑ Tau ⊕ₑ E) (.inr (.inr e)) blocks >>= k)
      (handler e sb >>= sk)

variable {handler}

/-! ## Composition -/

/-- Bind: the continuation only needs to be implemented on reachable
results. -/
theorem Implements.bind {x : CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α} {s : Free F γ α}
    {f : α → CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ β} {g : α → Free F γ β}
    (hx : Implements handler x s)
    (hf : ∀ a, x.MayReturn a → Implements handler (f a) (g a)) :
    Implements handler (x >>= f) (s >>= g) := by
  induction hx with
  | pure a => simpa using hf a (.pure a)
  | tick _ ih =>
    rw [bind_assoc]
    exact .tick (ih fun a ha => hf a (mayReturn_tick_bind_iff.mpr ha))
  | op e _ _ _ ih =>
    rw [bind_assoc, bind_assoc]
    exact .op e (by assumption) fun o => ih o fun a ha => hf a (.op o ha)

theorem Implements.map {x : CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α} {s : Free F γ α}
    (f : α → β) (hx : Implements handler x s) :
    Implements handler (f <$> x) (f <$> s) := by
  simp only [← bind_pure_comp]
  exact hx.bind fun a _ => .pure (f a)

/-- The source may only return what the implementation may. -/
theorem Implements.mayReturn {x : CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α}
    {s : Free F γ α} {a : α}
    (hx : Implements handler x s) (hs : s.MayReturn a) : x.MayReturn a := by
  induction hx with
  | pure b => simpa using hs
  | tick _ ih => exact mayReturn_tick_bind_iff.mpr (ih hs)
  | op e _ _ _ ih =>
    rcases Free.mayReturn_bind_iff.mp hs with ⟨o, -, hs⟩
    exact .op o (ih o hs)

/-! ## Equivalence with the pipeline -/

/-- The pipeline up to elision, stated without proof arguments. -/
private def Erases (handler : Eff.Handler E (Free F))
    (x : CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α) (s : Free F γ α) : Prop :=
  ∃ (wf : WF x) (y : Free (Tau ⊕ₑ E) γ α),
    x.toFree wf = Free.extendL γ α y ∧ y.eraseTau.interp handler = s

private theorem Implements.erases {x : CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α}
    {s : Free F γ α} (hx : Implements handler x s) : Erases handler x s := by
  induction hx with
  | pure a => exact ⟨wf_pure a, Pure.pure a, toFree_pure a _, rfl⟩
  | @tick γ α k s _ ih =>
    rcases ih with ⟨wf, y, hy, rfl⟩
    have wf' : WF (CompM.tick >>= k) := wf_tick_bind_iff.mpr wf
    refine ⟨wf', Free.op (E := Tau ⊕ₑ E) (.inl Eff.TauCarrier.mk)
      (fun t => nomatch t) >>= fun _ => y, ?_,
      by rw [Free.eraseTau_tau_bind]⟩
    rw [toFree_congr (tick_bind k tauBlocks) wf'
        (wf_op_bind_iff.mpr ⟨wf_tauBlocks, fun _ => wf⟩),
      toFree_op_bind _ _ _ _ wf_tauBlocks (fun _ => wf), hy]
    simp only [Free.extendL_bind, Free.extendL_op]
    congr 1
    congr 1
    funext t
    exact nomatch t
  | @op γ α e blocks k sb sk _ _ ihb ihk =>
    choose wfb yb hyb hsb using ihb
    choose wfk yk hyk hsk using ihk
    have wf : WF (CompM.op (E := Fail ⊕ₑ Tau ⊕ₑ E) (.inr (.inr e)) blocks >>= k) :=
      wf_op_bind_iff.mpr ⟨wfb, wfk⟩
    refine ⟨wf, Free.op (E := Tau ⊕ₑ E) (.inr e) yb >>= yk, ?_, ?_⟩
    · rw [toFree_op_bind _ _ _ _ wfb wfk]
      simp only [Free.extendL_bind, Free.extendL_op, hyb, hyk]
      rfl
    · simp only [Free.eraseTau_op_bind, Free.interp_bind, Free.interp_op,
        hsb, hsk]

private theorem Erases.implements {x : CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α}
    {s : Free F γ α} (hx : Erases handler x s) : Implements handler x s := by
  rcases hx with ⟨wf, y, hy, rfl⟩
  revert y
  refine WF.induction
    (motive := fun {γ α} (x : CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α) =>
      ∀ (wf : WF x) (y : Free (Tau ⊕ₑ E) γ α),
        x.toFree wf = Free.extendL γ α y →
        Implements handler x (y.eraseTau.interp handler))
    ?_ ?_ wf wf
  · intro _ _ a _ y hy
    rw [toFree_pure] at hy
    cases y using Free.casesOn with
    | ret b =>
      cases Free.pure_inj.mp hy
      exact .pure a
    | op e blocks k =>
      simp only [Free.extendL_bind, Free.extendL_op] at hy
      exact absurd hy Free.pure_ne_op_bind
  · intro _ _ e blocks k hb hk ihb ihk _ y hy
    rw [toFree_op_bind _ _ _ _ hb hk] at hy
    cases y using Free.casesOn with
    | ret b =>
      simp only [Free.extendL_pure] at hy
      exact absurd hy.symm Free.pure_ne_op_bind
    | op e' blocks' k' =>
      simp only [Free.extendL_bind, Free.extendL_op, Free.op_bind_inj] at hy
      rcases hy with ⟨rfl, hb', hk'⟩
      simp only [heq_eq_eq, Free.op_inj] at hb' hk'
      rcases e' with t | e'
      · have hx : CompM.op (E := Fail ⊕ₑ Tau ⊕ₑ E) (.inr (.inl t)) blocks >>= k =
            CompM.tick >>= fun _ => k PUnit.unit :=
          (tick_bind (fun _ => k PUnit.unit) blocks).symm
        rw [hx, Free.eraseTau_tau_bind]
        exact .tick (ihk _ _ _ (congrFun hk' _))
      · simp only [Free.eraseTau_op_bind, Free.interp_bind, Free.interp_op]
        exact .op e'
          (fun t i => ihb t i _ _ (congrFun (congrFun hb' t) i))
          (fun o => ihk o _ _ (congrFun hk' o))

private theorem erases_iff {x : CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α}
    {s : Free F γ α} :
    Erases handler x s ↔
      ∃ wf nofail, erase handler x wf nofail = s := by
  constructor
  · rintro ⟨wf, y, hy, rfl⟩
    refine ⟨wf, ⟨y, hy.symm⟩, ?_⟩
    rw [erase, Free.elideL_eq_iff.mpr hy]
  · rintro ⟨wf, nofail, rfl⟩
    exact ⟨wf, _, (Free.extendL_elideL _ nofail).symm, rfl⟩

/-- `Implements` is exactly the erasure pipeline. -/
theorem implements_iff {x : CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α}
    {s : Free F γ α} :
    Implements handler x s ↔
      ∃ wf nofail, erase handler x wf nofail = s :=
  ⟨fun h => erases_iff.mp h.erases, fun h => (erases_iff.mpr h).implements⟩

theorem Implements.wf {x : CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α} {s : Free F γ α}
    (hx : Implements handler x s) : WF x :=
  (implements_iff.mp hx).1

theorem Implements.nofail {x : CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α}
    {s : Free F γ α} (hx : Implements handler x s) :
    Free.UnusedL (x.toFree hx.wf) :=
  (implements_iff.mp hx).2.1

theorem Implements.erase_eq {x : CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α}
    {s : Free F γ α} (hx : Implements handler x s)
    (wf : WF x) (nofail : Free.UnusedL (x.toFree wf)) :
    erase handler x wf nofail = s := by
  rcases implements_iff.mp hx with ⟨_, _, h⟩
  exact h

theorem not_implements_fail {s : Free F γ α} :
    ¬ Implements handler (fail : CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α) s := by
  intro hx
  have h := hx.nofail
  rw [toFree_congr (fail_eq failBlocks failCont) hx.wf
      (wf_op_bind_iff.mpr ⟨wf_failBlocks, wf_failCont⟩),
    toFree_op_bind _ _ _ _ wf_failBlocks wf_failCont,
    Free.unusedL_op_bind] at h
  exact Bool.false_ne_true h.1

end CompM

end Freigen
