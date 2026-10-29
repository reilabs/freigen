import Freigen.ITree.Defs

namespace Freigen.ITree.WF

structure Packed {Γ : Type u} (E : Γ → Type u) [Eff.Spec E] where
  γ : Γ
  α : Type w
  t : ITree E γ α

inductive Child {Γ} {E : Γ → Type u} [s: Eff.Spec E] : Packed E → Packed E → Prop
| op_block {γ α e k t i} {blocks} :
    Child ⟨_, _, blocks t i⟩ ⟨γ, α, ITree.op e blocks k⟩
| op_cont {γ α e k} {blocks} {o} :
    Child ⟨_, _, k o⟩ ⟨γ, α, ITree.op e blocks k⟩

end WF

def WF {Γ : Type u} {E : Γ → Type u} {γ : Γ} {α} [s: Eff.Spec E] (t : ITree E γ α) : Prop :=
  Acc WF.Child ⟨γ, α, t⟩

variable {Γ : Type u} {E : Γ → Type u} [eS : Eff.Spec E] {γ : Γ}

theorem ret_ne_op {α : Type v} {a : α} {e : E γ}
    {blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      ITree E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)}
    {k : eS.output γ e → ITree E γ α} :
    ret a ≠ op e blocks k := by
  intro h
  have h := congrArg observe h
  simp only [observe_ret, observe_op, Eff.Step.ret, Eff.Step.op] at h
  injection h with h
  injection h

theorem op_inj {α : Type v} {e₁ e₂ : E γ}
    {blocks₁ :
      (t : eS.blockTag γ e₁) →
      eS.blockInputs γ e₁ t →
      ITree E (eS.blockCtx γ e₁ t) (eS.blockOutputs γ e₁ t)}
    {blocks₂ :
      (t : eS.blockTag γ e₂) →
      eS.blockInputs γ e₂ t →
      ITree E (eS.blockCtx γ e₂ t) (eS.blockOutputs γ e₂ t)}
    {k₁ : eS.output γ e₁ → ITree E γ α}
    {k₂ : eS.output γ e₂ → ITree E γ α} :
    op e₁ blocks₁ k₁ = op e₂ blocks₂ k₂ ↔
      ∃ _h : e₁ = e₂, HEq blocks₁ blocks₂ ∧ HEq k₁ k₂ := by
  constructor
  · intro h
    have h := congrArg observe h
    simp only [observe_op, Eff.Step.op] at h
    injection h with htag hfields
    injection htag with he
    subst he
    have hfields := eq_of_heq hfields
    refine ⟨rfl, heq_of_eq ?_, heq_of_eq ?_⟩
    · funext t i
      exact congrFun hfields (.inr ⟨t, i⟩)
    · funext o
      exact congrFun hfields (.inl o)
  · rintro ⟨rfl, hb, hk⟩
    cases hb
    cases hk
    rfl

namespace WF

theorem Child.not_ret {y : Packed E} {α : Type v} {a : α} :
    ¬ Child y ⟨γ, α, ret a⟩ := by
  intro h
  generalize hp : (⟨γ, α, ret a⟩ : Packed E) = p at h
  cases h with
  | op_block | op_cont =>
    injection hp with hγ hα ht
    subst hγ hα
    exact ret_ne_op (eq_of_heq ht)

theorem Child.inv_op {y : Packed E} {α : Type v} {e : E γ}
    {blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      ITree E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)}
    {k : eS.output γ e → ITree E γ α}
    (h : Child y ⟨γ, α, op e blocks k⟩) :
    (∃ t i, y = ⟨_, _, blocks t i⟩) ∨ ∃ o, y = ⟨_, _, k o⟩ := by
  generalize hp : (⟨γ, α, op e blocks k⟩ : Packed E) = p at h
  cases h with
  | op_block =>
    injection hp with hγ hα ht
    subst hγ hα
    rcases op_inj.mp (eq_of_heq ht) with ⟨rfl, hb, hk⟩
    cases hb
    cases hk
    exact .inl ⟨_, _, rfl⟩
  | op_cont =>
    injection hp with hγ hα ht
    subst hγ hα
    rcases op_inj.mp (eq_of_heq ht) with ⟨rfl, hb, hk⟩
    cases hb
    cases hk
    exact .inr ⟨_, rfl⟩

end Freigen.ITree.WF
