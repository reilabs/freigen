import Mathlib.Logic.Equiv.Defs

namespace Freigen

structure ExactCodensity (M : Type u → Type v) [Monad M] (α : Type _) where
  run : ∀ {β : Type u}, (α → M β) → M β
  exact : ∀ {β : Type u} (f : α → M β), run pure >>= f = run f
  result : M α
  result_eq : result = run pure

@[ext]
theorem ExactCodensity.ext
    {M : Type u → Type v} [Monad M] {α : Type u}
    {x y : ExactCodensity M α}
    (h : ∀ {β : Type u} (f : α → M β), x.run f = y.run f) : x = y := by
  cases x with
  | mk xrun xexact xresult xresult_eq =>
    cases y with
    | mk yrun yexact yresult yresult_eq =>
      have hrun : @xrun = @yrun := by
        funext β f
        exact h f
      cases hrun
      have : xresult = yresult := xresult_eq.trans yresult_eq.symm
      cases this
      rfl

instance {M} [Monad M] [LawfulMonad M] : Monad (ExactCodensity M) where
  pure a := {
    run := fun f => f a
    exact := by simp
    result := pure a
    result_eq := rfl
  }
  bind x f := {
    run := fun g => x.run fun a => (f a).run g,
    exact := by
      intros
      conv => lhs; rw [←x.exact]
      rw [bind_assoc]
      simp only [ExactCodensity.exact]
    result := x.run fun a => (f a).result
    result_eq := by
      congr 1
      funext a
      exact (f a).result_eq
  }

instance {M} [Monad M] [LawfulMonad M] : LawfulMonad (ExactCodensity M) := LawfulMonad.mk' _
  (by intros; apply ExactCodensity.ext; intros; rfl)
  (by intros; apply ExactCodensity.ext; intros; rfl)
  (by intros; apply ExactCodensity.ext; intros; rfl)

protected def ExactCodensity.equiv {M} [Monad M] [LawfulMonad M] {α : Type u} : ExactCodensity M α ≃ M α where
  toFun x := x.result
  invFun x := {
    run := fun f => x >>= f
    exact := by simp
    result := x
    result_eq := by simp
  }
  left_inv x := by
    apply ExactCodensity.ext
    intro β f
    change x.result >>= f = x.run f
    rw [x.result_eq, x.exact]
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
  by
    change x.run (fun a => (f a).result) =
      x.result >>= fun a => (f a).result
    rw [x.result_eq, x.exact]

def ExactCodensity.bind_def {M} [Monad M] [LawfulMonad M] {α β : Type _} (x : ExactCodensity M α) (f : α → ExactCodensity M β) :
    x >>= f = {
      run := fun g => x.run fun a => (f a).run g
      exact := by
        intros
        conv => lhs; rw [←x.exact]
        rw [bind_assoc]
        simp only [ExactCodensity.exact]
      result := x.run fun a => (f a).result
      result_eq := by
        congr 1
        funext a
        exact (f a).result_eq
    } := by
  rfl

end Freigen
