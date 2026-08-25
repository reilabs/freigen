import Freigen.F2Z.Examples.EcdsaP256.Lemmas

/-!
# ECDSA-P256 verification and Mathlib equivalence

The verification circuits are defined in `EcdsaP256.Impl`. This module
contains their main boundary correctness statements.
-/

namespace Freigen.F2Z.Examples.EcdsaP256

namespace Reference

/-! ## Mathlib equivalence -/

/-- Soundness of the checked inverse-witness ECDSA logic with respect to the
Mathlib P-256 verifier. -/
theorem checked_sound {digest r s rInv sInv : Nat} {publicKey : Point}
    (h : CheckedVerifies digest r s rInv sInv publicKey) :
    Verifies digest r s publicKey := by
  rcases h with ⟨hq0, hqOrder, hr, hs, hrInv, hsInv, hrMul, hsMul, hfinal⟩
  have hr0 : 0 < r := by
    by_contra hzero
    have : r = 0 := Nat.eq_zero_of_not_pos hzero
    subst r
    simp at hrMul
  have hs0 : 0 < s := by
    by_contra hzero
    have : s = 0 := Nat.eq_zero_of_not_pos hzero
    subst s
    simp at hsMul
  have hsCast : (s : Scalar) ≠ 0 := Aux.cast_ne_zero_of_pos_of_lt hs0 hs
  have hsInvEq : (sInv : Scalar) = (s : Scalar)⁻¹ :=
    Aux.inverse_eq_of_mul_eq_one hsCast hsMul
  refine ⟨hq0, hqOrder, hr0, hr, hs0, hs, ?_⟩
  simpa [verificationPoint, verificationPointWithInverse, hsInvEq] using hfinal

/-- Completeness: every Mathlib-valid signature has canonical inverse
witnesses satisfying the circuit-facing checked relation. -/
theorem checked_complete {digest r s : Nat} {publicKey : Point}
    (h : Verifies digest r s publicKey) :
    ∃ rInv sInv, CheckedVerifies digest r s rInv sInv publicKey := by
  rcases h with ⟨hq0, hqOrder, hr0, hr, hs0, hs, hfinal⟩
  let rInv : Nat := ((r : Scalar)⁻¹).val
  let sInv : Nat := ((s : Scalar)⁻¹).val
  refine ⟨rInv, sInv, hq0, hqOrder, hr, hs, ?_, ?_, ?_, ?_, ?_⟩
  · exact ZMod.val_lt _
  · exact ZMod.val_lt _
  · rw [show (rInv : Scalar) = (r : Scalar)⁻¹ by
      exact ZMod.natCast_zmod_val _]
    exact mul_inv_cancel₀ (Aux.cast_ne_zero_of_pos_of_lt hr0 hr)
  · rw [show (sInv : Scalar) = (s : Scalar)⁻¹ by
      exact ZMod.natCast_zmod_val _]
    exact mul_inv_cancel₀ (Aux.cast_ne_zero_of_pos_of_lt hs0 hs)
  · simpa [verificationPoint, verificationPointWithInverse, sInv,
      ZMod.natCast_zmod_val] using hfinal

/-- The checked-witness ECDSA relation and the direct Mathlib definition are
equivalent.  The forward direction is soundness; the reverse direction
constructs the canonical inverse witnesses. -/
theorem checked_iff {digest r s : Nat} {publicKey : Point} :
    (∃ rInv sInv, CheckedVerifies digest r s rInv sInv publicKey) ↔
      Verifies digest r s publicKey :=
  ⟨fun ⟨_, _, h⟩ => checked_sound h, checked_complete⟩

end Reference

/-! ## Digest verification circuit size -/

/--
info: { mRows := 1158991, mCols := 1158479, r1csRows := 5730 }
-/
#guard_msgs in
#eval verifyDigestCS.2.stats

end Freigen.F2Z.Examples.EcdsaP256
