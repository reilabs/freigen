import Freigen.Reflect
import Freigen.DenoteITree
import Freigen.Examples.Circuit.Basic

/-!
# Recursion through the elaborator: a reflected loop

With sum types (`Tp.sum`, `Sum.inl`/`Sum.inr`) and the boolean branch (`Exp.ite`/`bif`) now
reflectable, a **loop step** `σ → Free (Effect Op) (σ ⊕ ρ)` reflects, and `ITree.iter` ties the
unbounded recursive knot in the coinductive domain.  This is the recursion the `Free`/`Prog`
fragment could never express — and its soundness is `ITree.iter_converges`.

Here: a countdown.  The step is *reflected* from a host `bif … then … else …`; the loop is `iter`;
and we prove it **converges to `0`** from every input by unfolding the reflected step and applying
the general adequacy theorem's reasoning.
-/

namespace Freigen

open ITree

/-- The loop step (a host program): stop at `0`, else loop on the predecessor.  Reflectable now
    that `bif` (→ `Exp.ite`) and `Sum.inl`/`Sum.inr` (→ `Un.inl`/`Un.inr`) are handled. -/
def cdStep (n : Nat) : Free (Effect CircOp) (Nat ⊕ Nat) :=
  bif n == 0 then pure (Sum.inr 0) else pure (Sum.inl (n - 1))

/-- Reflect the step to a closed AST. -/
def rStep := reflect% cdStep

/-- The step, denoted into the interaction-tree domain. -/
noncomputable def cdStepD (n : Nat) : Comp CircOp (Nat ⊕ Nat) :=
  denoteProgI (rStep.1 (KleisliFI CircOp) Tp.denote) (.cons n .nil)

/-- The denoted step computes the pure decision (concrete `n`). -/
theorem cdStepD_zero : cdStepD 0 = ret (Sum.inr 0) := by
  unfold cdStepD rStep
  simp only [denoteProgI, denoteI, cdStep, bind_ret, denoteValI, Bin.denote, Un.denote,
             HList.head, cond]
  rfl

theorem cdStepD_succ (m : Nat) : cdStepD (m + 1) = ret (Sum.inl m) := by
  unfold cdStepD rStep
  simp only [denoteProgI, denoteI, cdStep, bind_ret, denoteValI, Bin.denote, Un.denote,
             HList.head, cond]
  rfl

/-- The countdown loop: `iter` over the reflected step. -/
noncomputable def countdown (N : Nat) : Comp CircOp Nat := iter cdStepD N

theorem countdown_zero : countdown 0 = ret 0 := by
  rw [countdown, iter_unfold, cdStepD_zero]
  simp only [bind_ret, iterK]

theorem countdown_succ (m : Nat) : countdown (m + 1) = tau (countdown m) := by
  rw [countdown, iter_unfold, cdStepD_succ]
  simp only [bind_ret, iterK]
  rfl

/-- **The reflected recursive loop converges to `0` from every input.** -/
theorem countdown_converges (N : Nat) : Converges (countdown N) 0 := by
  induction N with
  | zero => exact ⟨1, by rw [countdown_zero, stepN_ret]⟩
  | succ m ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, by rw [countdown_succ, stepN_tau]; exact hk⟩

end Freigen
