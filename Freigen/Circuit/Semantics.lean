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

def idValuation {F : Type} [Field F] : Valuation F F where
  toFun := {
    toFun := id
    map_add' := by simp
    map_smul' := by simp
  }
  one_map := by simp

instance {F} [Field F] : CertLogic (fun P => PLift $ P (idValuation (F := F))) where
  derive := by
    intro _ _ _ hI hA
    apply PLift.up
    apply_assumption
    intro
    apply PLift.down
    apply_assumption

local instance ctx {F} [Field F] : Circuit.Context F where
  W := F
  Cert := fun P => PLift $ P idValuation

end Freigen.Circuit.Semantics
