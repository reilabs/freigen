import Freigen.Free.Defs

/-!
`x.MayReturn a`: some effect interpreter could make `x` return `a`. The
interpreter decides every operation's output, so any output is allowed, and
blocks play no part. Continuations only matter at values the first
computation may return, which is how invariants get threaded through
binds.
-/

namespace Freigen

variable {Γ : Type u} {E : Γ → Type u} [eS : Eff.Spec.{u, v} E]
  {γ : Γ} {α β : Type v}

theorem Free.pure_inj {a b : α} :
    (pure a : Free E γ α) = pure b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have h := congrArg Free.toRaw h
  simp only [Free.toRaw_pure] at h
  change IxPoly.W.roll (Eff.Step.ret a) = IxPoly.W.roll (Eff.Step.ret b) at h
  simp only [IxPoly.W.roll, Eff.Step.ret] at h
  injection h
  rename_i _ hp _
  injection hp

inductive Free.MayReturn : Free E γ α → α → Prop
| pure (a : α) : Free.MayReturn (pure a) a
| op {e : E γ}
    {blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      Free E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)}
    {k : eS.output γ e → Free E γ α} {a : α}
    (o : eS.output γ e) :
    Free.MayReturn (k o) a → Free.MayReturn (Free.op e blocks >>= k) a

namespace Free

@[simp]
theorem mayReturn_pure_iff {a b : α} :
    (pure a : Free E γ α).MayReturn b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => h ▸ .pure a⟩
  generalize hx : (pure a : Free E γ α) = x at h
  cases h with
  | pure => exact pure_inj.mp hx
  | op => exact absurd hx pure_ne_op_bind

@[simp]
theorem mayReturn_op_bind_iff {e : E γ}
    {blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      Free E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)}
    {k : eS.output γ e → Free E γ α} {a : α} :
    (bind (α := no_index _) (op e blocks) k).MayReturn a ↔ ∃ o, (k o).MayReturn a := by
  refine ⟨fun h => ?_, fun ⟨o, h⟩ => .op o h⟩
  generalize hx : op e blocks >>= k = x at h
  cases h with
  | pure => exact absurd hx.symm pure_ne_op_bind
  | op o h =>
    rcases op_bind_inj.mp hx with ⟨rfl, -, hk⟩
    cases hk
    exact ⟨o, h⟩

@[simp]
theorem mayReturn_op {e : E γ}
    {blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      Free E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)}
    (o : eS.output γ e) :
    MayReturn (α := no_index _) (op e blocks) o := by
  rw [← bind_pure (op e blocks)]
  exact .op o (.pure o)

@[simp]
theorem mayReturn_bind_iff {x : Free E γ α} {f : α → Free E γ β} {b : β} :
    (x >>= f).MayReturn b ↔ ∃ a, x.MayReturn a ∧ (f a).MayReturn b := by
  induction x using Free.recOn with
  | ret a => simp
  | op e blocks k _ ih =>
    simp only [bind_assoc, mayReturn_op_bind_iff, ih]
    constructor
    · rintro ⟨o, a, h₁, h₂⟩
      exact ⟨a, ⟨o, h₁⟩, h₂⟩
    · rintro ⟨a, ⟨o, h₁⟩, h₂⟩
      exact ⟨o, a, h₁, h₂⟩

@[simp]
theorem mayReturn_map_iff {x : Free E γ α} {f : α → β} {b : β} :
    (f <$> x).MayReturn b ↔ ∃ a, x.MayReturn a ∧ f a = b := by
  simp [← bind_pure_comp]

/-- A bind only depends on its continuation at reachable results. -/
theorem bind_congr_mayReturn {x : Free E γ α} {f g : α → Free E γ β}
    (h : ∀ a, x.MayReturn a → f a = g a) :
    x >>= f = x >>= g := by
  induction x using Free.recOn with
  | ret a => simpa using h a (.pure a)
  | op e blocks k _ ih =>
    simp only [bind_assoc]
    congr 1
    funext o
    exact ih o fun a ha => h a (.op o ha)

/-- Interpreting into another free monad does not create results. -/
theorem MayReturn.of_interp {F : Γ → Type u} [Eff.Spec.{u, v} F]
    {handler : Eff.Handler E (Free F)} {x : Free E γ α} {a : α}
    (h : (x.interp handler).MayReturn a) : x.MayReturn a := by
  induction x using Free.recOn with
  | ret b => simpa using h
  | op e blocks k _ ih =>
    simp only [interp_bind, interp_op, mayReturn_bind_iff] at h
    rcases h with ⟨o, -, h⟩
    exact .op o (ih o h)

end Free

end Freigen
