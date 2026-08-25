import Freigen.F2Z.Examples.P256.Lemmas

/-!
# Correctness boundary for the P-256 circuit gadgets

Representations and circuits are defined in `P256.Impl`; supporting facts are
isolated in `P256.Lemmas`; Mathlib's affine point group is the only curve
semantics, defined in `P256.Reference`.
-/

namespace Freigen.F2Z.Examples.P256

set_option maxRecDepth 10000

open Std.Do
open scoped Std.Do
open Modular

namespace Projective.Lazy

@[spec] theorem mul_sound_zmod {x y : Rep} :
    ⦃⌜True⌝⦄ Sound.interp ρ (mul x y)
    ⦃⇓ out => ⌜Modular.Lazy.MulZModSpec base ρ x y out⌝⦄ :=
  Modular.Lazy.mul_sound_zmod base

@[spec] theorem assertOnCurve_sound {x y : Fp} :
    ⦃⌜True⌝⦄ Sound.interp ρ (assertOnCurve x y)
    ⦃⇓ _ => ⌜OnCurveZModSpec ρ x y⌝⦄ := by
  mvcgen -trivial [assertOnCurve, OnCurveZModSpec,
    Modular.Lazy.MulZModSpec, Modular.Lazy.AssertMulEqZModSpec,
    Modular.Lazy.evalZMod, Modular.Lazy.evalElemZMod,
    Modular.Lazy.ofElem, Modular.Lazy.add, Modular.Lazy.sub,
    Modular.Lazy.scale, base]
  rename_i x2 hx2 x3 hx3 _
  simp_all [Modular.Lazy.MulZModSpec,
    Modular.Lazy.AssertMulEqZModSpec, Modular.Lazy.evalZMod,
    Aux.curveB_intVal_eval]
  intro hcurve
  unfold OnCurveZModSpec
  dsimp
  let X : ZMod baseModulus :=
    Int.castRingHom (ZMod baseModulus) (x.val.intVal.eval ρ.int)
  let Y : ZMod baseModulus :=
    Int.castRingHom (ZMod baseModulus) (y.val.intVal.eval ρ.int)
  let X3 : ZMod baseModulus :=
    Int.castRingHom (ZMod baseModulus) (x3.intVal.eval ρ.int)
  change Y * Y = X3 +
      (0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b :
        ZMod baseModulus) - 3 * X at hcurve
  change X3 = X * X * X at hx3
  change Y ^ 2 = X ^ 3 - 3 * X +
    (0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b :
      ZMod baseModulus)
  calc
    Y ^ 2 = Y * Y := by ring
    _ = X3 +
        (0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b :
          ZMod baseModulus) - 3 * X := hcurve
    _ = X ^ 3 - 3 * X +
        (0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b :
          ZMod baseModulus) := by rw [hx3]; ring

end Projective.Lazy

namespace AffineSlope

@[spec] theorem andBit_sound {x y : LC ℤ} :
    ⦃⌜True⌝⦄ Sound.interp ρ (andBit x y)
    ⦃⇓ out => ⌜AndBitSpec ρ x y out⌝⦄ := by
  mvcgen [andBit, AndBitSpec]
  intro bits
  mvcgen
  rename_i out hout hmul
  refine ⟨hmul.symm, ?_⟩
  have hz := hout.1 (0 : Fin 1)
  cases hb : out.bits.bitsLE[0].eval ρ.bool <;> simp [hb] at hz
  · left
    simp [U.intVal, hz]
  · right
    simp [U.intVal, hz]

@[spec] theorem selectCanonical_sound {choose : LC ℤ}
    {whenOne whenZero : Rep} :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (selectCanonical choose whenOne whenZero)
    ⦃⇓ out => ⌜SelectZModSpec ρ choose whenOne whenZero out⌝⦄ := by
  mvcgen [selectCanonical, SelectZModSpec]
  intro bits
  mvcgen
  rename_i out hout heq
  constructor
  · intro hc
    have hval : out.intVal.eval ρ.int = whenOne.intVal.eval ρ.int := by
      simp only [LC.eval_sub, hc, one_mul] at heq
      omega
    unfold Modular.Lazy.evalZMod
    rw [hval]
  · intro hc
    have hval : out.intVal.eval ρ.int = whenZero.intVal.eval ρ.int := by
      simp only [LC.eval_sub, hc, zero_mul] at heq
      omega
    unfold Modular.Lazy.evalZMod
    rw [hval]

@[spec] theorem selectFormula_sound {choose : LC ℤ}
    {whenOne whenZero : Rep} :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (selectFormula choose whenOne whenZero)
    ⦃⇓ out => ⌜SelectZModSpec ρ choose whenOne whenZero out⌝⦄ := by
  mvcgen [selectFormula, SelectZModSpec]
  intro bits
  mvcgen
  rename_i out hout heq
  constructor
  · intro hc
    have hval : out.intVal.eval ρ.int = whenOne.intVal.eval ρ.int := by
      simp only [LC.eval_sub, hc, one_mul] at heq
      omega
    unfold Modular.Lazy.evalZMod
    rw [hval]
  · intro hc
    have hval : out.intVal.eval ρ.int = whenZero.intVal.eval ρ.int := by
      simp only [LC.eval_sub, hc, zero_mul] at heq
      omega
    unfold Modular.Lazy.evalZMod
    rw [hval]

end AffineSlope

namespace Reference

/-- A successful fused circuit check is exactly Mathlib's affine P-256
equation, not a separate hand-written curve predicate. -/
@[spec] theorem assertOnCurve_sound {x y : Fp} :
    ⦃⌜True⌝⦄ Sound.interp ρ (Projective.Lazy.assertOnCurve x y)
    ⦃⇓ _ => ⌜curve.toAffine.Equation
      (Int.castRingHom (ZMod baseModulus) (x.val.intVal.eval ρ.int))
      (Int.castRingHom (ZMod baseModulus) (y.val.intVal.eval ρ.int))⌝⦄ := by
  apply Triple.iff_conseq.mp Projective.Lazy.assertOnCurve_sound (by simp)
  simp only [PostCond.entails, SPred.entails_nil]
  exact ⟨fun _ h => (equation_iff_short _ _).2 h,
    ExceptConds.entails.refl _⟩

/-- The complete affine slope algorithm used by the optimized P-256 circuit
has exactly Mathlib's affine elliptic-curve group law as its pure semantics.

This covers both identity cases, opposite points, ordinary chord addition,
and tangent addition.  The only trusted premise in the reference layer is
`baseModulus_prime`; nonsingularity and all group-law facts come from Mathlib.
-/
theorem slopeAddCoordinates_eq_mathlib (P Q : Point) :
    slopeAddCoordinates P Q = coordinates (P + Q) := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rfl
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  by_cases hx : x₁ = x₂
  · by_cases hy : y₁ = curve.toAffine.negY x₂ y₂
    · simp only [slopeAddCoordinates, if_pos hx, if_pos hy]
      rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx hy]
      rfl
    · simp only [slopeAddCoordinates, if_pos hx, if_neg hy]
      rw [WeierstrassCurve.Affine.Point.add_of_Y_ne hy]
      simp only [coordinates]
      rw [Aux.resultX_eq_mathlib, Aux.resultY_eq_mathlib,
        Aux.tangentSlope_eq_mathlib hx hy]
  · simp only [slopeAddCoordinates, if_neg hx]
    rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
    simp only [coordinates]
    rw [Aux.resultX_eq_mathlib, Aux.resultY_eq_mathlib,
      Aux.chordSlope_eq_mathlib hx]

end Reference

end Freigen.F2Z.Examples.P256
