import Freigen.F2Z.Examples.P256.Lemmas
import Freigen.F2Z.Examples.P256.WF
import Freigen.F2Z.Examples.P256.CollapsedLemmas
import Freigen.F2Z.Examples.P256.CollapsedWF

/-!
# Correctness boundary for the P-256 circuit gadgets

Representations and circuits are defined in `P256.Impl`; supporting facts are
isolated in `P256.Lemmas`; Mathlib's affine point group is the only curve
semantics, defined in `P256.Reference`.
-/

namespace Freigen.F2Z.Examples.P256

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

open Std.Do
open scoped Std.Do
open Modular

namespace Projective.Lazy

@[spec] theorem mul_sound_zmod {x y : Rep} :
    ⦃⌜True⌝⦄ Sound.interp ρ (mul x y)
    ⦃⇓ out => ⌜Modular.Lazy.MulZModSpec base ρ x y out⌝⦄ :=
  Modular.Lazy.mul_sound_zmod base

@[spec] theorem mul_complete_zmod {x y : Rep}
    (hx : x.Valid ρ) (hy : y.Valid ρ)
    (hbound : x.bound * y.bound < 2 ^ Modular.Lazy.quotientExtraBits) :
    ⦃⌜True⌝⦄ Complete.interp ρ (mul x y)
    ⦃⇓ out => ⌜Modular.Lazy.MulZModSpec base ρ x y out ∧
      out.Valid ρ ∧ out.bound = 2⌝⦄ :=
  Modular.Lazy.mul_complete_zmod base hx hy hbound

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
  let X : ZMod base.modulus :=
    Int.castRingHom (ZMod base.modulus) (x.val.intVal.eval ρ.int)
  let Y : ZMod base.modulus :=
    Int.castRingHom (ZMod base.modulus) (y.val.intVal.eval ρ.int)
  let X3 : ZMod base.modulus :=
    Int.castRingHom (ZMod base.modulus) (x3.intVal.eval ρ.int)
  change Y * Y = X3 +
      (0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b :
        ZMod base.modulus) - 3 * X at hcurve
  change X3 = X * X * X at hx3
  change Y ^ 2 = X ^ 3 - 3 * X +
    (0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b :
      ZMod base.modulus)
  calc
    Y ^ 2 = Y * Y := by ring
    _ = X3 +
        (0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b :
          ZMod base.modulus) - 3 * X := hcurve
    _ = X ^ 3 - 3 * X +
        (0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b :
          ZMod base.modulus) := by rw [hx3]; ring

@[spec] theorem assertOnCurve_complete {x y : Fp}
    (hx : x.Valid ρ) (hy : y.Valid ρ)
    (hcurve : OnCurveZModSpec ρ x y) :
    ⦃⌜True⌝⦄ Complete.interp ρ (assertOnCurve x y)
    ⦃⇓ _ => ⌜OnCurveZModSpec ρ x y⌝⦄ := by
  mvcgen -trivial [assertOnCurve]
  case vc1.hx => exact Modular.Lazy.ofElem_valid base hx
  case vc2.hy => exact Modular.Lazy.ofElem_valid base hx
  case vc3.hbound =>
    norm_num [Modular.Lazy.ofElem, Modular.Lazy.quotientExtraBits]
  case vc4.hx => exact (by aesop)
  case vc5.hy => exact Modular.Lazy.ofElem_valid base hx
  case vc6.hbound =>
    simp_all [Modular.Lazy.ofElem, Modular.Lazy.quotientExtraBits]
  case vc7.success.success => exact fun _ => hcurve
  case vc8 =>
    intros
    exact Modular.Lazy.ofElem_valid base hy
  case vc9 =>
    intros
    exact Modular.Lazy.ofElem_valid base hy
  case vc10 =>
    intro _ hx3 _
    apply Modular.Lazy.sub_valid base
    · exact Modular.Lazy.add_valid base hx3
        (Modular.Lazy.ofElem_valid base
          (Modular.ofNat_valid base _ (by native_decide) (by native_decide)))
    · exact Modular.Lazy.scale_valid base
        (Modular.Lazy.ofElem_valid base hx) (by omega)
  case vc11 =>
    rename_i x2 hx2 x3
    intro hx3 _ _
    unfold Modular.Lazy.AssertMulEqZModSpec
    simp only [Modular.Lazy.evalZMod_sub, Modular.Lazy.evalZMod_add,
      Modular.Lazy.evalZMod_scale, Modular.Lazy.evalZMod_ofElem]
    unfold OnCurveZModSpec at hcurve
    dsimp at hcurve
    rw [hx3, hx2.1]
    have hb := Aux.curveB_intVal_eval (ρ := ρ)
    unfold Modular.Lazy.evalElemZMod at hb ⊢
    rw [hb]
    simp only [Modular.Lazy.evalZMod_ofElem]
    rw [pow_two, pow_succ] at hcurve
    unfold Modular.Lazy.evalElemZMod
    norm_num
    linear_combination hcurve
  case vc12 =>
    intros
    simp_all [Modular.Lazy.ofElem, Modular.Lazy.add,
      Modular.Lazy.sub, Modular.Lazy.scale,
      Modular.Lazy.quotientExtraBits]


end Projective.Lazy

namespace Reference

@[simp] theorem negY_eq (x y : Field) :
    curve.toAffine.negY x y = -y := by
  simp [curve]

@[simp] theorem curve_a1 : curve.toAffine.a₁ = 0 := rfl

@[simp] theorem curve_a3 : curve.toAffine.a₃ = 0 := rfl

/-- A successful fused circuit check is exactly Mathlib's affine P-256
equation, not a separate hand-written curve predicate. -/
@[spec] theorem assertOnCurve_sound {x y : Fp} :
    ⦃⌜True⌝⦄ Sound.interp ρ (Projective.Lazy.assertOnCurve x y)
    ⦃⇓ _ => ⌜curve.toAffine.Equation
      (Int.castRingHom Field (x.val.intVal.eval ρ.int))
      (Int.castRingHom Field (y.val.intVal.eval ρ.int))⌝⦄ := by
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

namespace AffineSlope

/-- Soundness of the selector-free doubling circuit.  `NormalizedRep` records
the `(0,0)` carrier used for infinity by the scalar-multiplication loop. -/
@[spec] theorem doubleComplete_sound_mathlib {P : Point}
    {p : Reference.Point}
    (hP : Reference.NormalizedRep ρ P p) :
    ⦃⌜True⌝⦄ Sound.interp ρ (doubleComplete P)
    ⦃⇓ out => ⌜Reference.NormalizedRep ρ out (p + p)⌝⦄ := by
  mvcgen [doubleComplete]
  rename_i slope hslope out
  intro hout
  exact Aux.double_specs_mathlib hP hslope hout

/-- Witness generation for the real doubling circuit is total on a valid,
normalized Mathlib point representation.  This is circuit completeness: the
postcondition is reached through `Complete.interp`, not through a second
reference predicate. -/
@[spec] theorem doubleComplete_complete_mathlib {P : Point}
    {p : Reference.Point}
    (hvalid : P.Valid ρ)
    (hP : Reference.NormalizedRep ρ P p)
    (hdouble : p = 0 ∨ p + p ≠ 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (doubleComplete P)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      Reference.NormalizedRep ρ out (p + p)⌝⦄ := by
  mvcgen [doubleComplete]
  case vc6 =>
    intros
    exact hvalid
  case vc7 =>
    intro hslope _ _ _
    exact hslope
  case vc8 =>
    intro _ hslopeBound _ _
    exact hslopeBound
  case vc9 =>
    intro _ _ hslopeCanonical _
    exact hslopeCanonical
  case vc5.success.success slope out =>
    intro houtValid houtSpec
    exact ⟨houtValid, Aux.double_specs_mathlib hP slope.2.2.2 houtSpec⟩

/-- Quotient well-formedness of the real doubling circuit under every pair
of total valuations. -/
theorem doubleComplete_wf :
    WF.GadgetSpec Point.WFRel doubleComplete Point.WFRel :=
  doubleComplete_wf_aux


/-- Soundness of the real complete-addition circuit against Mathlib's P-256
affine point group. -/
theorem addComplete_sound_mathlib {P Q : Point}
    {p q : Reference.Point}
    (hP : Reference.Represents ρ P p)
    (hQ : Reference.Represents ρ Q q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (addComplete P Q)
    ⦃⇓ out => ⌜Reference.Represents ρ out (p + q)⌝⦄ := by
  mvcgen [addComplete]
  rename_i control hcontrol candidate hcandidate out
  intro hout
  have hraw := Aux.add_specs_raw hP hQ hcontrol hcandidate hout
  unfold Reference.Represents
  exact ⟨hraw.1, hraw.2.trans (Reference.slopeAddCoordinates_eq_mathlib p q)⟩

/-- Complete addition also preserves the canonical `(0,0)` carrier for the
identity, which is the invariant consumed by selector-free doubling. -/
@[spec] theorem addComplete_sound_normalized {P Q : Point}
    {p q : Reference.Point}
    (hP : Reference.NormalizedRep ρ P p)
    (hQ : Reference.NormalizedRep ρ Q q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (addComplete P Q)
    ⦃⇓ out => ⌜Reference.NormalizedRep ρ out (p + q)⌝⦄ := by
  mvcgen [addComplete]
  rename_i control hcontrol candidate hcandidate out
  intro hout
  exact Aux.add_specs_normalized hP hQ hcontrol hcandidate hout
    (Reference.slopeAddCoordinates_eq_mathlib p q)

/-- Witness generation for the real complete-addition circuit is total on
valid normalized representatives.  The no-two-torsion premise is exactly the
condition needed by the tangent-slope branch. -/
@[spec] theorem addComplete_complete_mathlib {P Q : Point}
    {q p : Reference.Point}
    (hPvalid : P.Valid ρ) (hQvalid : Q.Valid ρ)
    (hP : Reference.NormalizedRep ρ P p)
    (hQ : Reference.NormalizedRep ρ Q q)
    (hnoTwoTorsion : p = 0 ∨ p + p ≠ 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (addComplete P Q)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      Reference.NormalizedRep ρ out (p + q)⌝⦄ := by
  mvcgen [addComplete]
  all_goals first
    | exact hPvalid
    | exact hQvalid
    | exact hP.1
    | exact hnoTwoTorsion
    | assumption
    | skip
  case vc10 => aesop
  case vc11 => aesop
  case vc12 => aesop
  case vc13 => aesop
  case vc14 => aesop
  case vc15 => aesop
  case vc16 => aesop
  case vc9.success.success.success =>
    rename_i control hcontrol candidate hcandidate out
    intros houtValid houtSpec
    exact ⟨houtValid,
      Aux.add_specs_normalized hP hQ hcontrol hcandidate.2.2.2.2.2.2
        houtSpec (Reference.slopeAddCoordinates_eq_mathlib p q)⟩

/-- Quotient well-formedness of the real complete-addition circuit under
every pair of total valuations. -/
theorem addComplete_wf :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point) =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2)
      (fun input => addComplete input.1 input.2) Point.WFRel :=
  addComplete_wf_aux

/-! Open-once complete addition.  These theorems share the existing
Mathlib semantic join point while replacing wide bit-decomposed selector
trees by gated integer constraints. -/

theorem addCompleteCollapsed_sound_mathlib {P Q : Point}
    {p q : Reference.Point}
    (hP : Reference.Represents ρ P p)
    (hQ : Reference.Represents ρ Q q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (addCompleteCollapsed P Q)
    ⦃⇓ out => ⌜Reference.Represents ρ out (p + q)⌝⦄ := by
  mvcgen [addCompleteCollapsed]
  rename_i control hcontrol candidate hcandidate out
  intro hout
  have hout' := hout.toSelectAddOutputSpec hP.1 hQ.1 hcontrol
  have hraw := Aux.add_specs_raw hP hQ hcontrol hcandidate hout'
  unfold Reference.Represents
  exact ⟨hraw.1,
    hraw.2.trans (Reference.slopeAddCoordinates_eq_mathlib p q)⟩

@[spec] theorem addCompleteCollapsed_sound_normalized {P Q : Point}
    {p q : Reference.Point}
    (hP : Reference.NormalizedRep ρ P p)
    (hQ : Reference.NormalizedRep ρ Q q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (addCompleteCollapsed P Q)
    ⦃⇓ out => ⌜Reference.NormalizedRep ρ out (p + q)⌝⦄ := by
  mvcgen [addCompleteCollapsed]
  rename_i control hcontrol candidate hcandidate out
  intro hout
  have hout' := hout.toSelectAddOutputSpec hP.1.1 hQ.1.1 hcontrol
  exact Aux.add_specs_normalized hP hQ hcontrol hcandidate hout'
    (Reference.slopeAddCoordinates_eq_mathlib p q)

@[spec] theorem addCompleteCollapsed_complete_mathlib {P Q : Point}
    {q p : Reference.Point}
    (hPvalid : P.Valid ρ) (hQvalid : Q.Valid ρ)
    (hP : Reference.NormalizedRep ρ P p)
    (hQ : Reference.NormalizedRep ρ Q q)
    (hnoTwoTorsion : p = 0 ∨ p + p ≠ 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (addCompleteCollapsed P Q)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      Reference.NormalizedRep ρ out (p + q)⌝⦄ := by
  mvcgen [addCompleteCollapsed]
  all_goals first
    | exact hPvalid
    | exact hQvalid
    | exact hP.1
    | exact hnoTwoTorsion
    | assumption
    | skip
  case vc10 => aesop
  case vc11 => aesop
  case vc12 => aesop
  case vc13 => aesop
  case vc14 => aesop
  case vc15 => aesop
  case vc16 => aesop
  case vc9.success.success.success =>
    rename_i control hcontrol candidate hcandidate out
    intros houtValid houtSpec
    exact ⟨houtValid,
      Aux.add_specs_normalized hP hQ hcontrol hcandidate.2.2.2.2.2.2
        houtSpec (Reference.slopeAddCoordinates_eq_mathlib p q)⟩

theorem addCompleteCollapsed_wf :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point) =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2)
      (fun input => addCompleteCollapsed input.1 input.2) Point.WFRel :=
  addCompleteCollapsed_wf_aux


end AffineSlope

end Freigen.F2Z.Examples.P256
