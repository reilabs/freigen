import Freigen.CompM.Basic
import Freigen.CompM.Examples.Nondet.Defs
import Freigen.ITree.Basic
import Freigen.Eff

namespace Freigen.CompM.Examples.Nondet.SamePrints

inductive Silent {α} : Nondet α → (β : Type) → (β → Nondet α) → Prop where
| tick : (k : Unit → Nondet α) → Silent (tick >>= k) Unit k
| rand : (k : ℤ → Nondet α) → Silent (Nondet.rand >>= k) ℤ k

inductive Step {α β} (RR : α → β → Prop) (R : Nondet α → Nondet β → Prop) : Nondet α → Nondet β → Prop where
-- aligning silent steps – recursing through R because both sides progress
| silent {t1 t2 β1 β2 k1 k2} :
    Silent t1 β1 k1 → Silent t2 β2 k2 →
    (∀ x1 x2, R (k1 x1) (k2 x2)) →
    Step RR R t1 t2
-- the important cases:
-- * prints relate if they print the same thing and continuations agree
-- * rets relate if they are the same
-- * fails relate if they align
| print {z k1 k2} : R k1 k2 → Step RR R (Nondet.print z *> k1) (Nondet.print z *> k2)
| ret {k₁ k₂} : RR k₁ k₂ → Step RR R (pure k₁) (pure k₂)
-- skipping silent steps on one side – recursing through SamePrintsF, to avoid consuming an
-- infinite number of them (preserve termination)
| silentL : ∀ {t1 t2 β k}, Silent t1 β k → (∀ i, Step RR R (k i) t2) → Step RR R t1 t2
| silentR : ∀ {t1 t2 β k}, Silent t2 β k → (∀ i, Step RR R t1 (k i)) → Step RR R t1 t2

def SamePrintsA {α β} (RR : α → β → Prop): (Nondet α → Nondet β → Prop) →o (Nondet α → Nondet β → Prop) where
  toFun R := Step RR R
  monotone' := by
    intro _ _ _ _ _ h12
    induction h12
    · apply Step.silent <;> solve_by_elim
    · apply Step.print ; solve_by_elim
    · apply Step.ret ; solve_by_elim
    · apply Step.silentL <;> solve_by_elim
    · apply Step.silentR <;> solve_by_elim

end SamePrints

def SamePrints {α β} (RR : α → β → Prop) : Nondet α → Nondet β → Prop := (SamePrints.SamePrintsA RR).gfp

namespace SamePrints

protected theorem out {x : Nondet α} {y : Nondet β} {RR : α → β → Prop}
    (h : SamePrints RR x y) :
    Step RR (SamePrints RR) x y := by
  change SamePrintsA RR (SamePrints RR) x y
  have := OrderHom.isFixedPt_gfp (SamePrintsA RR (α := α))
  unfold Function.IsFixedPt at this
  unfold SamePrints
  rw [this]
  exact h

protected theorem roll {α β} {x : Nondet α} {y : Nondet β} {RR : α → β → Prop}
    (h : Step RR (SamePrints RR) x y) :
    SamePrints RR x y := by
  change SamePrintsA RR (SamePrints RR) x y at h
  have hfix := OrderHom.isFixedPt_gfp (SamePrintsA RR (α := α))
  unfold Function.IsFixedPt at hfix
  unfold SamePrints at h ⊢
  simpa only [hfix] using h

private theorem coind_raw {α β} (a b) {RR : α → β → Prop} (R : Nondet α → Nondet β → Prop)
    (h_stable : ∀x y, R x y → Step RR R x y)
    (h : R a b) : SamePrints RR a b := OrderHom.le_gfp (SamePrintsA RR) h_stable a b h

protected theorem coind_up_to_fix {α β} (a b) {RR : α → β → Prop} (R : Nondet α → Nondet β → Prop)
    (h_stable : ∀x y, R x y → Step RR (fun x y => SamePrints RR x y ∨ R x y) x y)
    (h : R a b) : SamePrints RR a b := by
  apply coind_raw (RR := RR) (R := fun x y => SamePrints RR x y ∨ R x y)
  · intro x y hxy
    cases hxy
    · rename_i h
      apply (SamePrintsA RR).monotone (fun _ _ h => Or.inl h)
      exact h.out
    · tauto
  · tauto

theorem Silent.bind {α β : Type} {t : Nondet α} {k : β → Nondet α} {k2 : α → Nondet γ}
    (h : Silent t _ k): Silent (t >>= k2) _ (fun x => k x >>= k2) := by
  cases h <;> rw [bind_assoc] <;> constructor

protected theorem bind {α₁ α₂ β₁ β₂ : Type} {a₁ : Nondet α₁} {a₂ : Nondet α₂} {b₁ : α₁ → Nondet β₁}
    {b₂ : α₂ → Nondet β₂}
    {RRo : β₁ → β₂ → Prop} {RR : α₁ → α₂ → Prop}
    (h1 : SamePrints RR a₁ a₂) (h2 : ∀x y, RR x y → SamePrints RRo (b₁ x) (b₂ y)) :
    SamePrints RRo (a₁ >>= b₁) (a₂ >>= b₂) := by
  let R : Nondet β₁ → Nondet β₂ → Prop := fun x y =>
    ∃ x1 x2, SamePrints RR x1 x2 ∧ x = (x1 >>= b₁) ∧ y = (x2 >>= b₂)
  apply SamePrints.coind_up_to_fix (R := R)
  · rintro _ _ ⟨x, y, hxy, rfl, rfl⟩
    have := hxy.out
    clear hxy
    induction this with
    | silent =>
      apply Step.silent
      · apply Silent.bind; assumption
      · apply Silent.bind; assumption
      grind
    | print =>
      simp only [seqRight_eq_bind, bind_assoc]
      apply Step.print
      grind
    | ret =>
      simp only [pure_bind]
      apply (SamePrintsA _).monotone (fun _ _ h => Or.inl h)
      apply SamePrints.out
      solve_by_elim
    | silentL =>
      apply Step.silentL
      · apply Silent.bind; assumption
      assumption
    | silentR =>
      apply Step.silentR
      · apply Silent.bind; assumption
      assumption
  · exact ⟨a₁, a₂, h1, rfl, rfl⟩

protected theorem rand {β₁ β₂ : Type} {b₁ : ℤ → Nondet β₁} {b₂ : ℤ → Nondet β₂} {RR : β₁ → β₂ → Prop}
    (h2 : ∀x y, SamePrints RR (b₁ x) (b₂ y)):
  SamePrints RR (Nondet.rand >>= b₁) (Nondet.rand >>= b₂) := by
  apply SamePrints.roll
  apply Step.silent
  · apply Silent.rand
  · apply Silent.rand
  assumption

protected theorem print {z : ℤ}:
  SamePrints Eq (Nondet.print z) (Nondet.print z) := by
  apply SamePrints.roll
  have : pure (f := Nondet) = fun _ => pure () := by simp
  conv =>
    congr
    · skip
    · skip
    · rw [←bind_pure (x := Nondet.print z), this]
    · rw [←bind_pure (x := Nondet.print z), this]
  apply Step.print
  apply SamePrints.roll
  apply Step.ret
  rfl

protected theorem ret {α β : Type} {x : α} {y : β} {R : α → β → Prop} (h : R x y):
  SamePrints R (pure x) (pure y) := by
  apply SamePrints.roll
  apply Step.ret h

/-! ### Inverting nondeterministic choice -/

private def isRand {α} :
    Eff.NodeTag Unit Nondet.Stack () α → Bool
  | .op (.inr .rand) => true
  | _ => false

private def isRandHead {α} (t : Nondet α) : Bool :=
  isRand (ITree.observe (t.run pure)).1

private def printValue {α} :
    Eff.NodeTag Unit Nondet.Stack () α → Option ℤ
  | .op (.inr (.print z)) => some z
  | _ => none

private def printHead {α} (t : Nondet α) : Option ℤ :=
  printValue (ITree.observe (t.run pure)).1

@[simp] private theorem isRandHead_rand {α} (b : ℤ → Nondet α) :
    isRandHead (Nondet.rand >>= b) = true := by
  change isRand (ITree.observe ((Nondet.rand >>= b).run pure)).1 = true
  rw [show (Nondet.rand >>= b).run pure = Nondet.rand.run (fun z => (b z).run pure) by rfl]
  rfl

@[simp] private theorem isRandHead_tick {α} (k : Unit → Nondet α) :
    isRandHead (CompM.tick >>= k) = false := by
  change isRand (ITree.observe ((CompM.tick >>= k).run pure)).1 = false
  rw [show (CompM.tick >>= k).run pure = CompM.tick.run (fun z => (k z).run pure) by rfl]
  rfl

@[simp] private theorem isRandHead_print {α} (z : ℤ) (k : Nondet α) :
    isRandHead (Nondet.print z *> k) = false := by
  change isRand (ITree.observe ((Nondet.print z *> k).run pure)).1 = false
  rw [show (Nondet.print z *> k).run pure = (Nondet.print z).run (fun _ => k.run pure) by rfl]
  rfl

@[simp] private theorem isRandHead_ret {α} (x : α) :
    isRandHead (pure x : Nondet α) = false := by
  change isRand (ITree.observe (ITree.ret x)).1 = false
  simp [Eff.Step.ret, isRand]

@[simp] private theorem printHead_rand {α} (b : ℤ → Nondet α) :
    printHead (Nondet.rand >>= b) = none := by
  change printValue (ITree.observe ((Nondet.rand >>= b).run pure)).1 = none
  rw [show (Nondet.rand >>= b).run pure = Nondet.rand.run (fun z => (b z).run pure) by rfl]
  rfl

@[simp] private theorem printHead_tick {α} (k : Unit → Nondet α) :
    printHead (CompM.tick >>= k) = none := by
  change printValue (ITree.observe ((CompM.tick >>= k).run pure)).1 = none
  rw [show (CompM.tick >>= k).run pure = CompM.tick.run (fun z => (k z).run pure) by rfl]
  rfl

@[simp] private theorem printHead_print {α} (z : ℤ) (k : Nondet α) :
    printHead (Nondet.print z *> k) = some z := by
  change printValue (ITree.observe ((Nondet.print z *> k).run pure)).1 = some z
  rw [show (Nondet.print z *> k).run pure = (Nondet.print z).run (fun _ => k.run pure) by rfl]
  rfl

@[simp] private theorem printHead_ret {α} (x : α) :
    printHead (pure x : Nondet α) = none := by
  change printValue (ITree.observe (ITree.ret x)).1 = none
  rfl

private theorem Silent.printHead_eq_none {α γ} {t : Nondet α} {k : γ → Nondet α}
    (h : Silent t γ k) : printHead t = none := by
  cases h <;> simp

private theorem Step.print_head_eq {α β} {RR : α → β → Prop}
    {R : Nondet α → Nondet β → Prop} {x : Nondet α} {y : Nondet β}
    {z₁ z₂ : ℤ} (h : Step RR R x y)
    (hx : printHead x = some z₁) (hy : printHead y = some z₂) : z₁ = z₂ := by
  cases h with
  | silent hs₁ hs₂ h =>
    rw [hs₁.printHead_eq_none] at hx
    contradiction
  | print =>
    simp only [printHead_print, Option.some.injEq] at hx hy
    exact hx.symm.trans hy
  | ret =>
    simp only [printHead_ret] at hx
    contradiction
  | silentL hs h =>
    rw [hs.printHead_eq_none] at hx
    contradiction
  | silentR hs h =>
    rw [hs.printHead_eq_none] at hy
    contradiction

private theorem rand_bind_injective {α} {b k : ℤ → Nondet α}
    (h : (Nondet.rand >>= b) = (Nondet.rand >>= k)) : b = k := by
  have hrun := congrArg (fun t : Nondet α => t.run pure) h
  rw [show (Nondet.rand >>= b).run pure = Nondet.rand.run (fun z => (b z).run pure) by rfl,
      show (Nondet.rand >>= k).run pure = Nondet.rand.run (fun z => (k z).run pure) by rfl] at hrun
  simp only [Nondet.rand, CompM.op] at hrun
  have ho := congrArg ITree.observe hrun
  simp at ho
  injection ho with _ hk
  funext z
  apply ExactCodensity.equiv.injective
  change (b z).result = (k z).result
  rw [(b z).result_eq, (k z).result_eq]
  exact congrFun hk (Sum.inl z)

private theorem rand_ne {α} {b : ℤ → Nondet α} {t : Nondet α}
    (ht : isRandHead t = false) (h : Nondet.rand >>= b = t) : False := by
  have hh := congrArg isRandHead h
  simp only [isRandHead_rand, ht] at hh
  exact Bool.noConfusion hh

private theorem Step.rand_right_inv {α β} {RR : α → β → Prop}
    {t : Nondet α} {b : ℤ → Nondet β}
    (h : Step RR (SamePrints RR) t (Nondet.rand >>= b)) :
    ∀ y, SamePrints RR t (b y) := by
  generalize heq : (Nondet.rand >>= b) = t₂ at h
  induction h generalizing b with
  | silent hs₁ hs₂ hcont =>
    cases hs₂ with
    | tick k => exact False.elim (rand_ne (isRandHead_tick k) heq)
    | rand k =>
      have hk := rand_bind_injective heq
      subst k
      intro y
      apply SamePrints.roll
      apply Step.silentL hs₁
      intro x
      exact (hcont x y).out
  | @print z k₁ k₂ h => exact False.elim (rand_ne (isRandHead_print z k₂) heq)
  | @ret x y h => exact False.elim (rand_ne (isRandHead_ret y) heq)
  | silentL hs hnext ih =>
    intro y
    apply SamePrints.roll
    apply Step.silentL hs
    intro x
    exact (ih x heq y).out
  | silentR hs hnext ih =>
    cases hs with
    | tick k => exact False.elim (rand_ne (isRandHead_tick k) heq)
    | rand k =>
      have hk := rand_bind_injective heq
      subst k
      intro y
      exact SamePrints.roll (hnext y)

private theorem Step.rand_left_inv {α β} {RR : α → β → Prop}
    {b : ℤ → Nondet α} {t : Nondet β}
    (h : Step RR (SamePrints RR) (Nondet.rand >>= b) t) :
    ∀ x, SamePrints RR (b x) t := by
  generalize heq : (Nondet.rand >>= b) = t₁ at h
  induction h generalizing b with
  | silent hs₁ hs₂ hcont =>
    cases hs₁ with
    | tick k => exact False.elim (rand_ne (isRandHead_tick k) heq)
    | rand k =>
      have hk := rand_bind_injective heq
      subst k
      intro x
      apply SamePrints.roll
      apply Step.silentR hs₂
      intro y
      exact (hcont x y).out
  | @print z k₁ k₂ h => exact False.elim (rand_ne (isRandHead_print z k₁) heq)
  | @ret x y h => exact False.elim (rand_ne (isRandHead_ret x) heq)
  | silentL hs hnext ih =>
    cases hs with
    | tick k => exact False.elim (rand_ne (isRandHead_tick k) heq)
    | rand k =>
      have hk := rand_bind_injective heq
      subst k
      intro x
      exact SamePrints.roll (hnext x)
  | silentR hs hnext ih =>
    intro x
    apply SamePrints.roll
    apply Step.silentR hs
    intro y
    exact (ih y heq x).out

protected theorem rand_inv {α β} {RR : α → β → Prop}
    {b₁ : ℤ → Nondet α} {b₂ : ℤ → Nondet β}
    (h : SamePrints RR (Nondet.rand >>= b₁) (Nondet.rand >>= b₂)) :
    ∀ x y, SamePrints RR (b₁ x) (b₂ y) := by
  intro x y
  have hr := Step.rand_right_inv h.out y
  exact Step.rand_left_inv hr.out x

protected theorem not_rand {α β} {RR : α → β → Prop}
    {b₁ : ℤ → Nondet α} {b₂ : ℤ → Nondet β}
    (x y : ℤ) (h : ¬ SamePrints RR (b₁ x) (b₂ y)) :
    ¬ SamePrints RR (Nondet.rand >>= b₁) (Nondet.rand >>= b₂) := by
  intro hr
  exact h (hr.rand_inv x y)

protected theorem print_head_eq {α β} {RR : α → β → Prop}
    {z₁ z₂ : ℤ} {k₁ : Nondet α} {k₂ : Nondet β}
    (h : SamePrints RR (Nondet.print z₁ *> k₁) (Nondet.print z₂ *> k₂)) :
    z₁ = z₂ :=
  Step.print_head_eq h.out rfl rfl

protected theorem not_print {α β} {RR : α → β → Prop}
    {z₁ z₂ : ℤ} {k₁ : Nondet α} {k₂ : Nondet β}
    (h : z₁ ≠ z₂) :
    ¬ SamePrints RR (Nondet.print z₁ *> k₁) (Nondet.print z₂ *> k₂) := by
  intro hs
  exact h hs.print_head_eq

def ForInStep.Rel {α β} (RR : α → β → Prop) (I : α → β → Prop):
    ForInStep α → ForInStep β → Prop
  | .done x, .done y => RR x y
  | .yield x, .yield y => I x y
  | _, _ => False

def LoopPair {α₁ β₁ α₂ β₂}
  (b₁ : α₁ → Nondet (α₁ ⊕ β₁))
  (b₂ : α₂ → Nondet (α₂ ⊕ β₂))
  (I : α₁ → α₂ → Prop) : Nondet β₁ → Nondet β₂ → Prop :=
  fun x y =>
    ∃ s₁ s₂,
      I s₁ s₂ ∧
      x = CompM.loop b₁ s₁ ∧
      y = CompM.loop b₂ s₂

inductive Steps {α β} (RR : α → β → Prop) (R : Nondet α → Nondet β → Prop) : Nondet α → Nondet β → Prop where
| done {x y} : SamePrints RR x y → Steps RR R x y
| step {x y} : Step RR (Steps RR R) x y → Steps RR R x y
| recur {x y} : R x y → Steps RR R x y

/-! ### Named silent transitions -/

theorem Step.tick_tick {α β} {RR : α → β → Prop} {R : Nondet α → Nondet β → Prop}
    {k₁ : Unit → Nondet α} {k₂ : Unit → Nondet β}
    (h : R (k₁ ()) (k₂ ())) :
    Step RR R (CompM.tick >>= k₁) (CompM.tick >>= k₂) :=
  Step.silent (Silent.tick k₁) (Silent.tick k₂) fun _ _ => h

theorem Step.tick_rand {α β} {RR : α → β → Prop} {R : Nondet α → Nondet β → Prop}
    {k₁ : Unit → Nondet α} {k₂ : ℤ → Nondet β}
    (h : ∀ x₂, R (k₁ ()) (k₂ x₂)) :
    Step RR R (CompM.tick >>= k₁) (Nondet.rand >>= k₂) :=
  Step.silent (Silent.tick k₁) (Silent.rand k₂) fun _ x₂ => h x₂

theorem Step.rand_tick {α β} {RR : α → β → Prop} {R : Nondet α → Nondet β → Prop}
    {k₁ : ℤ → Nondet α} {k₂ : Unit → Nondet β}
    (h : ∀ x₁, R (k₁ x₁) (k₂ ())) :
    Step RR R (Nondet.rand >>= k₁) (CompM.tick >>= k₂) :=
  Step.silent (Silent.rand k₁) (Silent.tick k₂) fun x₁ _ => h x₁

theorem Step.rand_rand {α β} {RR : α → β → Prop} {R : Nondet α → Nondet β → Prop}
    {k₁ : ℤ → Nondet α} {k₂ : ℤ → Nondet β}
    (h : ∀ x₁ x₂, R (k₁ x₁) (k₂ x₂)) :
    Step RR R (Nondet.rand >>= k₁) (Nondet.rand >>= k₂) :=
  Step.silent (Silent.rand k₁) (Silent.rand k₂) h

theorem Step.tick_left {α β} {RR : α → β → Prop} {R : Nondet α → Nondet β → Prop}
    {k : Unit → Nondet α} {t : Nondet β}
    (h : Step RR R (k ()) t) :
    Step RR R (CompM.tick >>= k) t :=
  Step.silentL (Silent.tick k) fun _ => h

theorem Step.rand_left {α β} {RR : α → β → Prop} {R : Nondet α → Nondet β → Prop}
    {k : ℤ → Nondet α} {t : Nondet β}
    (h : ∀ x, Step RR R (k x) t) :
    Step RR R (Nondet.rand >>= k) t :=
  Step.silentL (Silent.rand k) h

theorem Step.tick_right {α β} {RR : α → β → Prop} {R : Nondet α → Nondet β → Prop}
    {t : Nondet α} {k : Unit → Nondet β}
    (h : Step RR R t (k ())) :
    Step RR R t (CompM.tick >>= k) :=
  Step.silentR (Silent.tick k) fun _ => h

theorem Step.rand_right {α β} {RR : α → β → Prop} {R : Nondet α → Nondet β → Prop}
    {t : Nondet α} {k : ℤ → Nondet β}
    (h : ∀ x, Step RR R t (k x)) :
    Step RR R t (Nondet.rand >>= k) :=
  Step.silentR (Silent.rand k) h

/-! ### Finite-step constructors -/

theorem Steps.silent {α β} {RR : α → β → Prop} {R : Nondet α → Nondet β → Prop}
    {t₁ : Nondet α} {t₂ : Nondet β} {γ₁ γ₂} {k₁ : γ₁ → Nondet α} {k₂ : γ₂ → Nondet β}
    (h₁ : Silent t₁ γ₁ k₁) (h₂ : Silent t₂ γ₂ k₂)
    (h : ∀ x₁ x₂, Steps RR R (k₁ x₁) (k₂ x₂)) :
    Steps RR R t₁ t₂ :=
  Steps.step (Step.silent h₁ h₂ h)

theorem Steps.print {α β} {RR : α → β → Prop} {R : Nondet α → Nondet β → Prop}
    {z : ℤ} {k₁ : Nondet α} {k₂ : Nondet β}
    (h : Steps RR R k₁ k₂) :
    Steps RR R (Nondet.print z *> k₁) (Nondet.print z *> k₂) :=
  Steps.step (Step.print h)

theorem Steps.ret {α β} {RR : α → β → Prop} {R : Nondet α → Nondet β → Prop}
    {x : α} {y : β} (h : RR x y) :
    Steps RR R (pure x) (pure y) :=
  Steps.step (Step.ret h)

theorem Steps.silentL {α β} {RR : α → β → Prop} {R : Nondet α → Nondet β → Prop}
    {t₁ : Nondet α} {t₂ : Nondet β} {γ} {k : γ → Nondet α}
    (hs : Silent t₁ γ k) (h : ∀ x, Step RR (Steps RR R) (k x) t₂) :
    Steps RR R t₁ t₂ :=
  Steps.step (Step.silentL hs h)

theorem Steps.silentR {α β} {RR : α → β → Prop} {R : Nondet α → Nondet β → Prop}
    {t₁ : Nondet α} {t₂ : Nondet β} {γ} {k : γ → Nondet β}
    (hs : Silent t₂ γ k) (h : ∀ x, Step RR (Steps RR R) t₁ (k x)) :
    Steps RR R t₁ t₂ :=
  Steps.step (Step.silentR hs h)

theorem Steps.tick_tick {α β} {RR : α → β → Prop} {R : Nondet α → Nondet β → Prop}
    {k₁ : Unit → Nondet α} {k₂ : Unit → Nondet β}
    (h : Steps RR R (k₁ ()) (k₂ ())) :
    Steps RR R (CompM.tick >>= k₁) (CompM.tick >>= k₂) :=
  Steps.step (Step.tick_tick h)

theorem Steps.tick_rand {α β} {RR : α → β → Prop} {R : Nondet α → Nondet β → Prop}
    {k₁ : Unit → Nondet α} {k₂ : ℤ → Nondet β}
    (h : ∀ x₂, Steps RR R (k₁ ()) (k₂ x₂)) :
    Steps RR R (CompM.tick >>= k₁) (Nondet.rand >>= k₂) :=
  Steps.step (Step.tick_rand h)

theorem Steps.rand_tick {α β} {RR : α → β → Prop} {R : Nondet α → Nondet β → Prop}
    {k₁ : ℤ → Nondet α} {k₂ : Unit → Nondet β}
    (h : ∀ x₁, Steps RR R (k₁ x₁) (k₂ ())) :
    Steps RR R (Nondet.rand >>= k₁) (CompM.tick >>= k₂) :=
  Steps.step (Step.rand_tick h)

theorem Steps.rand_rand {α β} {RR : α → β → Prop} {R : Nondet α → Nondet β → Prop}
    {k₁ : ℤ → Nondet α} {k₂ : ℤ → Nondet β}
    (h : ∀ x₁ x₂, Steps RR R (k₁ x₁) (k₂ x₂)) :
    Steps RR R (Nondet.rand >>= k₁) (Nondet.rand >>= k₂) :=
  Steps.step (Step.rand_rand h)

theorem Steps.tick_left {α β} {RR : α → β → Prop} {R : Nondet α → Nondet β → Prop}
    {k : Unit → Nondet α} {t : Nondet β}
    (h : Step RR (Steps RR R) (k ()) t) :
    Steps RR R (CompM.tick >>= k) t :=
  Steps.step (Step.tick_left h)

theorem Steps.rand_left {α β} {RR : α → β → Prop} {R : Nondet α → Nondet β → Prop}
    {k : ℤ → Nondet α} {t : Nondet β}
    (h : ∀ x, Step RR (Steps RR R) (k x) t) :
    Steps RR R (Nondet.rand >>= k) t :=
  Steps.step (Step.rand_left h)

theorem Steps.tick_right {α β} {RR : α → β → Prop} {R : Nondet α → Nondet β → Prop}
    {t : Nondet α} {k : Unit → Nondet β}
    (h : Step RR (Steps RR R) t (k ())) :
    Steps RR R t (CompM.tick >>= k) :=
  Steps.step (Step.tick_right h)

theorem Steps.rand_right {α β} {RR : α → β → Prop} {R : Nondet α → Nondet β → Prop}
    {t : Nondet α} {k : ℤ → Nondet β}
    (h : ∀ x, Step RR (Steps RR R) t (k x)) :
    Steps RR R t (Nondet.rand >>= k) :=
  Steps.step (Step.rand_right h)

/-! ### Unfolding loops under relations -/

theorem Step.loop_left {α₁ β₁ β₂} {RR : β₁ → β₂ → Prop} {R : Nondet β₁ → Nondet β₂ → Prop}
    {body : α₁ → Nondet (α₁ ⊕ β₁)} {s : α₁} {t : Nondet β₂}
    (h : Step RR R
      (body s >>= fun
        | .inr v => pure v
        | .inl v => CompM.tick *> CompM.loop body v)
      t) :
    Step RR R (CompM.loop body s) t := by
  exact Eq.mpr (congrArg (fun x => Step RR R x t) (CompM.loop_def body s)) h

theorem Step.loop_right {α₂ β₁ β₂} {RR : β₁ → β₂ → Prop} {R : Nondet β₁ → Nondet β₂ → Prop}
    {t : Nondet β₁} {body : α₂ → Nondet (α₂ ⊕ β₂)} {s : α₂}
    (h : Step RR R t
      (body s >>= fun
        | .inr v => pure v
        | .inl v => CompM.tick *> CompM.loop body v)) :
    Step RR R t (CompM.loop body s) := by
  exact Eq.mpr (congrArg (Step RR R t) (CompM.loop_def body s)) h

theorem Step.loop {α₁ α₂ β₁ β₂} {RR : β₁ → β₂ → Prop} {R : Nondet β₁ → Nondet β₂ → Prop}
    {body₁ : α₁ → Nondet (α₁ ⊕ β₁)} {body₂ : α₂ → Nondet (α₂ ⊕ β₂)} {s₁ : α₁} {s₂ : α₂}
    (h : Step RR R
      (body₁ s₁ >>= fun
        | .inr v => pure v
        | .inl v => CompM.tick *> CompM.loop body₁ v)
      (body₂ s₂ >>= fun
        | .inr v => pure v
        | .inl v => CompM.tick *> CompM.loop body₂ v)) :
    Step RR R (CompM.loop body₁ s₁) (CompM.loop body₂ s₂) := by
  exact Eq.mpr
    (congrArg₂ (Step RR R) (CompM.loop_def body₁ s₁) (CompM.loop_def body₂ s₂)) h

theorem Steps.loop_left {α₁ β₁ β₂} {RR : β₁ → β₂ → Prop} {R : Nondet β₁ → Nondet β₂ → Prop}
    {body : α₁ → Nondet (α₁ ⊕ β₁)} {s : α₁} {t : Nondet β₂}
    (h : Steps RR R
      (body s >>= fun
        | .inr v => pure v
        | .inl v => CompM.tick *> CompM.loop body v)
      t) :
    Steps RR R (CompM.loop body s) t := by
  exact Eq.mpr (congrArg (fun x => Steps RR R x t) (CompM.loop_def body s)) h

theorem Steps.loop_right {α₂ β₁ β₂} {RR : β₁ → β₂ → Prop} {R : Nondet β₁ → Nondet β₂ → Prop}
    {t : Nondet β₁} {body : α₂ → Nondet (α₂ ⊕ β₂)} {s : α₂}
    (h : Steps RR R t
      (body s >>= fun
        | .inr v => pure v
        | .inl v => CompM.tick *> CompM.loop body v)) :
    Steps RR R t (CompM.loop body s) := by
  exact Eq.mpr (congrArg (Steps RR R t) (CompM.loop_def body s)) h

theorem Steps.loop {α₁ α₂ β₁ β₂} {RR : β₁ → β₂ → Prop} {R : Nondet β₁ → Nondet β₂ → Prop}
    {body₁ : α₁ → Nondet (α₁ ⊕ β₁)} {body₂ : α₂ → Nondet (α₂ ⊕ β₂)} {s₁ : α₁} {s₂ : α₂}
    (h : Steps RR R
      (body₁ s₁ >>= fun
        | .inr v => pure v
        | .inl v => CompM.tick *> CompM.loop body₁ v)
      (body₂ s₂ >>= fun
        | .inr v => pure v
        | .inl v => CompM.tick *> CompM.loop body₂ v)) :
    Steps RR R (CompM.loop body₁ s₁) (CompM.loop body₂ s₂) := by
  exact Eq.mpr
    (congrArg₂ (Steps RR R) (CompM.loop_def body₁ s₁) (CompM.loop_def body₂ s₂)) h

theorem Step.strengthen {α β} {RR : α → β → Prop} {R R' : Nondet α → Nondet β → Prop}
    (h : R ≤ R') {x y} (hstep : Step RR R x y):
    Step RR R' x y := by
  apply (SamePrintsA RR).monotone h
  exact hstep

protected theorem coind {α β} (a b) {RR : α → β → Prop}
    (R : Nondet α → Nondet β → Prop)
    (h_stable : ∀ x y, R x y → Step RR (Steps RR R) x y)
    (h : R a b) : SamePrints RR a b := by
  apply coind_raw (R := Steps RR R)
  · intro x y hxy
    cases hxy with
    | done h =>
      apply Step.strengthen (hstep := h.out)
      intro x y hxy
      exact Steps.done hxy
    | step h =>
      exact h
    | recur h =>
      exact h_stable x y h
  · exact Steps.recur h

protected theorem loop_coind {α₁ α₂ β₁ β₂}
    {b₁ : α₁ → Nondet (α₁ ⊕ β₁)} {b₂ : α₂ → Nondet (α₂ ⊕ β₂)}
    {i₁ : α₁} {i₂ : α₂} {RR : β₁ → β₂ → Prop}
    (I : α₁ → α₂ → Prop)
    (hinit : I i₁ i₂)
    (hstep : ∀ s₁ s₂, I s₁ s₂ →
      Step RR (Steps RR (LoopPair b₁ b₂ I))
      (loop b₁ s₁) (loop b₂ s₂)):
    SamePrints RR (loop b₁ i₁) (loop b₂ i₂) := by
  apply SamePrints.coind (R := LoopPair b₁ b₂ I)
  · rintro _ _ ⟨s₁, s₂, hI, rfl, rfl⟩
    exact hstep s₁ s₂ hI
  · exact ⟨i₁, i₂, hinit, rfl, rfl⟩

end Freigen.CompM.Examples.Nondet.SamePrints
