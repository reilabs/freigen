import Std.Tactic.Do

namespace Freigen.F2Z

open Std.Do
open scoped Std.Do

/-- Universal nondeterminism as a weakest-precondition transformer. -/
def Nondet := PredTrans .pure

namespace Nondet

instance : Monad Nondet := inferInstanceAs (Monad (PredTrans .pure))
instance : LawfulMonad Nondet := inferInstanceAs (LawfulMonad (PredTrans .pure))

instance : WP Nondet .pure where
  wp x := x

instance : WPMonad Nondet .pure where
  wp_pure _ := rfl
  wp_bind _ _ := rfl

/-- Universally choose a value satisfying `P`. -/
def chooseWhere (P : α → Prop) : Nondet α where
  trans Q := spred(∀ a, ⌜P a⌝ → Q.1 a)
  conjunctiveRaw := by
    intro Q₁ Q₂
    simp only [SPred.bientails_nil, SPred.and_nil, SPred.forall_nil,
      SPred.imp_nil, SPred.down_pure_nil]
    constructor
    · intro h
      exact ⟨fun a ha => (h a ha).1, fun a ha => (h a ha).2⟩
    · rintro ⟨h₁, h₂⟩ a ha
      exact ⟨h₁ a ha, h₂ a ha⟩

def choose (α : Type u) : Nondet α :=
  chooseWhere fun _ => True

/-- Require `P` on the current verification path. -/
def assert (P : Prop) : Nondet Unit where
  trans Q := spred(⌜P⌝ ∧ Q.1 ())
  conjunctiveRaw := by
    intro Q₁ Q₂
    simp only [SPred.bientails_nil, SPred.and_nil, SPred.down_pure_nil]
    constructor
    · rintro ⟨hp, h₁, h₂⟩
      exact ⟨⟨hp, h₁⟩, hp, h₂⟩
    · rintro ⟨⟨hp, h₁⟩, _, h₂⟩
      exact ⟨hp, h₁, h₂⟩

def abort : Nondet α :=
  PredTrans.const ⌜True⌝

@[spec]
theorem chooseWhere_spec (P : α → Prop) (Q : PostCond α .pure) :
    Triple (chooseWhere P) spred(∀ a, ⌜P a⌝ → Q.1 a) Q := by
  apply Triple.iff.mpr
  exact SPred.entails.rfl

@[spec]
theorem assert_spec (P : Prop) (Q : PostCond Unit .pure) :
    Triple (assert P) spred(⌜P⌝ ∧ Q.1 ()) Q := by
  apply Triple.iff.mpr
  exact SPred.entails.rfl

end Nondet

end Freigen.F2Z
