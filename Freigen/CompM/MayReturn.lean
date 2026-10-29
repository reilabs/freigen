import Freigen.CompM.Basic

/-!
`x.MayReturn a`: some effect interpreter could make `x` return `a` after
finitely many operations. The interpreter decides every operation's output,
so any output is allowed, and blocks play no part.
-/

namespace Freigen.CompM

variable
  {Γ : Type u} {E : Γ → Type u} [eS : Eff.Spec E]
  {γ : Γ}

inductive MayReturn {α : Type v} : CompM E γ α → α → Prop
| pure (a : α) : MayReturn (pure a) a
| op {e : E γ}
    {blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      CompM E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)}
    {k : eS.output γ e → CompM E γ α} {a : α}
    (o : eS.output γ e) :
    MayReturn (k o) a → MayReturn (op e blocks >>= k) a

@[simp]
theorem mayReturn_pure_iff {α : Type v} {a b : α} :
    (pure a : CompM E γ α).MayReturn b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => h ▸ .pure a⟩
  generalize hx : (pure a : CompM E γ α) = x at h
  cases h with
  | pure => exact pure_inj.mp hx
  | op => exact absurd hx pure_ne_op_bind

@[simp]
theorem mayReturn_op_bind_iff {α : Type v} {e : E γ}
    {blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      CompM E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)}
    {k : eS.output γ e → CompM E γ α} {a : α} :
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
      CompM E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)}
    (o : eS.output γ e) :
    MayReturn (α := no_index _) (op e blocks) o := by
  rw [← bind_pure (op e blocks)]
  exact .op o (.pure o)

@[simp]
theorem mayReturn_bind_iff {α β : Type v}
    {x : CompM E γ α} {f : α → CompM E γ β} {b : β} :
    (x >>= f).MayReturn b ↔ ∃ a, x.MayReturn a ∧ (f a).MayReturn b := by
  constructor
  · intro h
    generalize hm : x >>= f = m at h
    induction h generalizing x with
    | pure c =>
      rcases eq_pure_or_op_bind x with ⟨a, rfl⟩ | ⟨e, blocks, k, rfl⟩
      · rw [pure_bind] at hm
        exact ⟨a, .pure a, hm ▸ .pure c⟩
      · rw [bind_assoc] at hm
        exact absurd hm.symm pure_ne_op_bind
    | op o hk ih =>
      rcases eq_pure_or_op_bind x with ⟨a, rfl⟩ | ⟨e', blocks', k', rfl⟩
      · rw [pure_bind] at hm
        exact ⟨a, .pure a, hm ▸ .op o hk⟩
      · rw [bind_assoc] at hm
        rcases op_bind_inj.mp hm with ⟨rfl, -, hk'⟩
        cases hk'
        rcases ih (x := k' o) rfl with ⟨a, h₁, h₂⟩
        exact ⟨a, .op o h₁, h₂⟩
  · rintro ⟨a, h₁, h₂⟩
    induction h₁ with
    | pure => simpa using h₂
    | op o _ ih =>
      rw [bind_assoc]
      exact .op o (ih h₂)

@[simp]
theorem mayReturn_map_iff {α β : Type v}
    {x : CompM E γ α} {f : α → β} {b : β} :
    (f <$> x).MayReturn b ↔ ∃ a, x.MayReturn a ∧ f a = b := by
  simp [← bind_pure_comp]

@[simp]
theorem mayReturn_tick_bind_iff [Eff.Has.{u, 0} Eff.Tau E] {α : Type}
    {k : Unit → CompM E γ α} {a : α} :
    (tick >>= k).MayReturn a ↔ (k ()).MayReturn a := by
  rw [tick_bind k tauBlocks,
    mayReturn_op_bind_iff]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨Eff.Step.Has.liftOutput PUnit.unit, h⟩⟩

@[simp]
theorem not_returns_fail [Eff.Has.{u, 0} Eff.Fail E] {α : Type} {a : α} :
    ¬ (fail : CompM E γ α).MayReturn a := by
  rw [fail_eq failBlocks failCont, mayReturn_op_bind_iff]
  rintro ⟨o, -⟩
  exact nomatch Eff.Step.Has.lowerOutput (F := Eff.Fail) (E := E) o

end Freigen.CompM
