import Freigen.Iso

namespace Freigen

structure ExactCodensity (M : Type u → Type v) [Monad M] (α : Type _) where
  run : ∀ {β : Type u}, (α → M β) → M β
  exact : ∀ {β : Type u} (f : α → M β), run pure >>= f = run f

instance {M} [Monad M] [LawfulMonad M] : Monad (ExactCodensity M) where
  pure a := ⟨fun f => f a, by simp⟩
  bind x f := {
    run := fun g => x.run fun a => (f a).run g,
    exact := by
      intros
      conv => lhs; rw [←x.exact]
      rw [bind_assoc]
      simp only [ExactCodensity.exact]
  }

instance {M} [Monad M] [LawfulMonad M] : LawfulMonad (ExactCodensity M) := LawfulMonad.mk' _
  (by intros; rfl)
  (by intros; rfl)
  (by intros; rfl)

protected def ExactCodensity.equiv {M} [Monad M] [LawfulMonad M] {α : Type u} : ExactCodensity M α ≃ M α where
  toFun x := x.run pure
  invFun x := ⟨fun f => x >>= f, by simp⟩
  left_inv x := by simp only [ExactCodensity.exact]
  right_inv x := by simp

@[simp]
theorem ExactCodensity.equiv_pure
    {M : Type u → Type v} [Monad M] [LawfulMonad M]
    (x : α) :
    ExactCodensity.equiv (pure x : ExactCodensity M α) =
      pure x :=
  rfl

@[simp]
theorem ExactCodensity.equiv_bind
    {M : Type u → Type v} [Monad M] [LawfulMonad M]
    (x : ExactCodensity M α)
    (f : α → ExactCodensity M β) :
    ExactCodensity.equiv (x >>= f) =
      ExactCodensity.equiv x >>= fun a =>
        ExactCodensity.equiv (f a) :=
  (x.exact _).symm

def ExactCodensity.bind_def {M} [Monad M] [LawfulMonad M] {α β : Type _} (x : ExactCodensity M α) (f : α → ExactCodensity M β) :
    x >>= f = ⟨fun g => x.run fun a => (f a).run g, by
      intros
      conv => lhs; rw [←x.exact]
      rw [bind_assoc]
      simp only [ExactCodensity.exact]⟩ := by
  rfl

end Freigen
