import Freigen.F2Z.Examples.Modular
import Freigen.F2Z.Examples.P256.Reference

/-!
# Auxiliary lemmas for P-256 correctness

Supporting validity, evaluation, and relational facts used by the public
soundness, completeness, and well-formedness proofs.
-/

namespace Freigen.F2Z.Examples.P256

set_option maxRecDepth 10000

open Std.Do
open scoped Std.Do
open Modular

@[simp] theorem base_modulus_eq : base.modulus = baseModulus := rfl

namespace Projective.Aux

theorem curveB_evalNat : curveB.evalNat ρ =
    0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b := by
  exact Modular.ofNat_evalNat base _ (by native_decide) (by native_decide)

@[simp] theorem curveB_intVal_eval {ρ : WF.Valuation} :
    curveB.val.intVal.eval ρ.int =
    (0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b :
      Int) := by
  have hvalid : curveB.Valid ρ :=
    Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  have hcast := Modular.Elem.evalNat_cast base hvalid
  rw [curveB_evalNat] at hcast
  exact hcast.symm

end Projective.Aux

namespace Reference.Aux

theorem represents_zero {P : AffineSlope.Point}
    (h : Reference.Represents ρ P 0) :
    P.infinity.eval ρ.int = 1 := by
  rcases h with ⟨hbit, hcoords⟩
  unfold Reference.circuitCoordinates Reference.coordinates at hcoords
  rcases hbit with hzero | hone
  · simp [hzero] at hcoords
  · exact hone

theorem represents_some {P : AffineSlope.Point}
    {x y : Reference.Field}
    {hxy : Reference.curve.toAffine.Nonsingular x y}
    (h : Reference.Represents ρ P (.some x y hxy)) :
    P.infinity.eval ρ.int = 0 ∧
      Modular.Lazy.evalZMod base P.X ρ = x ∧
      Modular.Lazy.evalZMod base P.Y ρ = y := by
  rcases h with ⟨hbit, hcoords⟩
  unfold Reference.circuitCoordinates Reference.coordinates at hcoords
  rcases hbit with hzero | hone
  · rw [if_neg (by omega)] at hcoords
    exact ⟨hzero, Reference.Coordinates.finite.inj hcoords⟩
  · simp [hone] at hcoords

theorem chordSlope_eq_mathlib {x₁ y₁ x₂ y₂ : Reference.Field}
    (hx : x₁ ≠ x₂) :
    Reference.chordSlope x₁ y₁ x₂ y₂ =
      Reference.curve.toAffine.slope x₁ x₂ y₁ y₂ := by
  simp [Reference.chordSlope, WeierstrassCurve.Affine.slope, hx]
  rw [show y₂ - y₁ = -(y₁ - y₂) by ring,
    show x₂ - x₁ = -(x₁ - x₂) by ring, neg_div_neg_eq]

theorem tangentSlope_eq_mathlib {x₁ y₁ x₂ y₂ : Reference.Field}
    (hx : x₁ = x₂)
    (hy : y₁ ≠ Reference.curve.toAffine.negY x₂ y₂) :
    Reference.tangentSlope x₁ y₁ =
      Reference.curve.toAffine.slope x₁ x₂ y₁ y₂ := by
  have hy' : y₁ ≠ -y₂ := by
    simpa [WeierstrassCurve.Affine.negY, Reference.curve] using hy
  simp [Reference.tangentSlope, WeierstrassCurve.Affine.slope, hx, hy',
    Reference.curve, two_mul, sub_eq_add_neg]

theorem resultX_eq_mathlib (x₁ x₂ slope : Reference.Field) :
    Reference.resultX x₁ x₂ slope =
      Reference.curve.toAffine.addX x₁ x₂ slope := by
  simp [Reference.resultX, WeierstrassCurve.Affine.addX, Reference.curve]

theorem resultY_eq_mathlib (x₁ x₂ y₁ slope : Reference.Field) :
    Reference.resultY x₁ x₂ y₁ slope =
      Reference.curve.toAffine.addY x₁ x₂ y₁ slope := by
  simp [Reference.resultY, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, Reference.resultX,
    WeierstrassCurve.Affine.addX, Reference.curve]
  ring

end Reference.Aux

namespace AffineSlope.Aux

theorem two_mul_ne_zero_of_eq_of_ne_neg
    {a b : Reference.Field} (hab : a = b) (hne : a ≠ -b) :
    2 * a ≠ 0 := by
  intro hzero
  apply hne
  rw [← hab]
  linear_combination hzero

theorem add_self_ne_zero_of_eq_of_ne_neg
    {a b : Reference.Field} (hab : a = b) (hne : a ≠ -b) :
    a + a ≠ 0 := by
  intro hzero
  apply hne
  rw [← hab]
  linear_combination hzero

theorem sub_ne_zero_of_ne_rev {a b : Reference.Field}
    (hne : a ≠ b) : b - a ≠ 0 :=
  sub_ne_zero.mpr (Ne.symm hne)

end AffineSlope.Aux

end Freigen.F2Z.Examples.P256
