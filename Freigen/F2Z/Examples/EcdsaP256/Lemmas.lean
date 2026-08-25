import Freigen.F2Z.Examples.EcdsaP256.Impl

/-!
# Auxiliary ECDSA-P256 reference lemmas

Small scalar-field facts used by the public soundness and completeness
statements live here, away from both implementation and theorem boundary.
-/

namespace Freigen.F2Z.Examples.EcdsaP256.Reference.Aux

open Freigen.F2Z.Examples.P256
open Freigen.F2Z.Examples.EcdsaP256.Reference

theorem cast_ne_zero_of_pos_of_lt {x : Nat}
    (hx : 0 < x) (hlt : x < scalarModulus) : (x : Scalar) ≠ 0 := by
  intro hzero
  have hval := congrArg ZMod.val hzero
  rw [ZMod.val_cast_of_lt hlt] at hval
  simp at hval
  omega

theorem inverse_eq_of_mul_eq_one {x inverse : Scalar}
    (hx : x ≠ 0) (h : x * inverse = 1) : inverse = x⁻¹ := by
  calc
    inverse = 1 * inverse := by simp
    _ = (x⁻¹ * x) * inverse := by rw [inv_mul_cancel₀ hx]
    _ = x⁻¹ * (x * inverse) := by rw [mul_assoc]
    _ = x⁻¹ := by rw [h]; simp

end Freigen.F2Z.Examples.EcdsaP256.Reference.Aux
