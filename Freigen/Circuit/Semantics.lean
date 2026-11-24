import Freigen.Circuit.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

namespace Freigen.Circuit.Semantics

def NoOp : Type u → Type w := fun _ => PUnit

instance : Monad NoOp where
  pure _ := PUnit.unit
  bind _ _ := PUnit.unit

instance : LawfulMonad NoOp := LawfulMonad.mk' _
  (by intros; rfl)
  (by intros; rfl)
  (by intros; rfl)

def NondetM (α : Type u) : Type u := (α → Prop) → Prop

instance : Monad NondetM where
  pure a := fun p => p a
  bind m f := fun p => m fun a => f a p

instance : LawfulMonad NondetM := LawfulMonad.mk' _
  (by intros; rfl)
  (by intros; rfl)
  (by intros; rfl)

def InterpM : Circuit.Scope → Type u → Type u := fun _ => NondetM

instance (s : Circuit.Scope) : Monad (InterpM s) := inferInstanceAs (Monad NondetM)

instance (s : Circuit.Scope) : LawfulMonad (InterpM s) := inferInstanceAs (LawfulMonad NondetM)

def idValuation {P : Nat} : Valuation (ZMod P) (ZMod P) where
  toFun := {
    toFun := id
    map_add' := by simp
    map_smul' := by simp
  }
  one_map := by simp

instance {P : Nat} : CertLogic (fun A => PLift $ A (idValuation (P := P))) where
  derive := by
    intro _ _ _ hI hA
    apply PLift.up
    apply_assumption
    intro
    apply PLift.down
    apply_assumption

local instance ctx {P : Nat} : Circuit.Context P where
  W := ZMod P
  Cert := fun A => PLift $ A idValuation
  certSubsingleton := fun _ => ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

-- def interp {P: Nat} [Fact (Nat.Prime P)] {α} : Circuit (ZMod P) α → NondetM α := Free.interp (M:=InterpM) @fun
-- | Scope.constraint, ConstraintEff.assertR1C (a : ZMod P) b c, blocks => fun k =>
--     ∃(p : a * b = c), k (PLift.up p)
-- | Scope.constraint, ConstraintEff.rangeCheck n a, blocks => fun k =>
--     ∃(p : a.val < 2 ^ n), k (PLift.up $ by exists a.val; simp [p, idValuation])
-- -- | Scope.constraint, ConstraintEff.assertSpread n a b, blocks => fun k =>


end Freigen.Circuit.Semantics
