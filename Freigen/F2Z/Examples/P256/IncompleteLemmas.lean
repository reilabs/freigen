import Freigen.F2Z.Examples.P256
import Freigen.F2Z.Examples.P256.IncompleteImpl

/-!
# Correctness of checked incomplete affine addition

The gadget is generic: it proves the ordinary chord formula whenever its
finite-input and inverse-certificate constraints are satisfiable.  Scalar
schedule arguments belong to callers.
-/

namespace Freigen.F2Z.Examples.P256

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open Std.Do
open scoped Std.Do
open Modular

namespace Reference.Aux

/-- Two finite curve points whose group elements are neither equal nor
opposites have distinct X coordinates. -/
theorem finite_x_ne_of_ne_and_ne_neg
    {p q : Reference.Point}
    (hpq : p ≠ q) (hpnegq : p ≠ -q)
    {x₁ y₁ x₂ y₂ : Reference.Field}
    {h₁ : Reference.curve.toAffine.Nonsingular x₁ y₁}
    {h₂ : Reference.curve.toAffine.Nonsingular x₂ y₂}
    (hp : p = .some x₁ y₁ h₁) (hq : q = .some x₂ y₂ h₂) :
    x₁ ≠ x₂ := by
  intro hx
  rcases WeierstrassCurve.Affine.Point.X_eq_iff.mp hx with heq | hneg
  · exact hpq (hp.trans (heq.trans hq.symm))
  · exact hpnegq (hp.trans (hneg.trans (congrArg Neg.neg hq).symm))

/-- Group-level exceptional-case exclusions imply that the direct chord
denominator represented by the circuit is nonzero. -/
theorem chord_denominator_ne_zero
    {P Q : AffineSlope.Point} {p q : Reference.Point}
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hpq : p ≠ q) (hpnegq : p ≠ -q)
    (hP : Reference.Represents ρ P p)
    (hQ : Reference.Represents ρ Q q) :
    P.infinity.eval ρ.int = 0 ∧ Q.infinity.eval ρ.int = 0 ∧
      Modular.Lazy.evalZMod base (AffineSlope.sub Q.X P.X) ρ ≠ 0 := by
  rcases hp : p with _ | ⟨px, py, hpcurve⟩
  · exact (hp0 hp).elim
  rcases hq : q with _ | ⟨qx, qy, hqcurve⟩
  · exact (hq0 hq).elim
  have hPsome : Reference.Represents ρ P (.some px py hpcurve) := hp ▸ hP
  have hQsome : Reference.Represents ρ Q (.some qx qy hqcurve) := hq ▸ hQ
  obtain ⟨hPinf, hPx, _⟩ := represents_some hPsome
  obtain ⟨hQinf, hQx, _⟩ := represents_some hQsome
  have hx : px ≠ qx := finite_x_ne_of_ne_and_ne_neg hpq hpnegq hp hq
  refine ⟨hPinf, hQinf, ?_⟩
  simp only [AffineSlope.sub, Modular.Lazy.evalZMod_sub, hQx, hPx]
  exact sub_ne_zero.mpr hx.symm

end Reference.Aux

namespace AffineSlope

@[spec] theorem addIncompleteChecked_sound_mathlib
    {P Q : Point} {p q : Reference.Point}
    (hP : Reference.Represents ρ P p)
    (hQ : Reference.Represents ρ Q q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (addIncompleteChecked P Q)
    ⦃⇓ out => ⌜Reference.NormalizedRep ρ out (p + q)⌝⦄ := by
  mvcgen [addIncompleteChecked, finishAddCandidate]
  rename_i hPfinite hQfinite inverse hinverse slope hslope x hx y hy
  have hPinf : P.infinity.eval ρ.int = 0 := by
    simpa using hPfinite.symm
  have hQinf : Q.infinity.eval ρ.int = 0 := by
    simpa using hQfinite.symm
  have hden : Modular.Lazy.evalZMod base (sub Q.X P.X) ρ ≠ 0 := by
    intro hzero
    unfold Modular.Lazy.DivideZModSpec at hinverse
    rw [hzero] at hinverse
    simp [ofElem] at hinverse
  rcases hp : p with _ | ⟨px, py, hpcurve⟩
  · have hPzero := hP
    rw [hp] at hPzero
    have hpinf := Reference.Aux.represents_zero hPzero
    omega
  rcases hq : q with _ | ⟨qx, qy, hqcurve⟩
  · have hQzero := hQ
    rw [hq] at hQzero
    have hqinf := Reference.Aux.represents_zero hQzero
    omega
  have hPsome : Reference.Represents ρ P (.some px py hpcurve) := hp ▸ hP
  have hQsome : Reference.Represents ρ Q (.some qx qy hqcurve) := hq ▸ hQ
  obtain ⟨_, hPx, hPy⟩ := Reference.Aux.represents_some hPsome
  obtain ⟨_, hQx, hQy⟩ := Reference.Aux.represents_some hQsome
  have hcoordX : px ≠ qx := by
    intro heq
    apply hden
    simp only [sub, Modular.Lazy.evalZMod_sub, hQx, hPx, heq, sub_self]
  have hden' : qx - px ≠ 0 := sub_ne_zero.mpr hcoordX.symm
  have hslopeEq : Modular.Lazy.evalZMod base slope ρ =
      Reference.chordSlope px py qx qy := by
    unfold Modular.Lazy.DivideZModSpec at hslope
    simp only [sub, Modular.Lazy.evalZMod_sub, hQx, hPx, hQy, hPy]
      at hslope
    exact (eq_div_iff hden').2 hslope
  have hsum :
      (WeierstrassCurve.Affine.Point.some px py hpcurve : Reference.Point) +
          .some qx qy hqcurve =
        .some _ _ (WeierstrassCurve.Affine.nonsingular_add hpcurve hqcurve
          (fun hxy => hcoordX hxy.1)) :=
    WeierstrassCurve.Affine.Point.add_of_X_ne hcoordX
  constructor
  · constructor
    · simp
    · unfold Reference.circuitCoordinates
      have hzeroFlag : (0 : LC ℤ).eval ρ.int = 0 := by simp
      rw [if_neg (by rw [hzeroFlag]; norm_num)]
      rw [hsum]
      unfold Reference.coordinates
      congr 1
      · change Modular.Lazy.evalZMod base (ofElem x) ρ = _
        unfold Modular.Lazy.MulSubToElemZModSpec at hx
        rw [ofElem, Modular.Lazy.evalZMod_ofElem, hx, hslopeEq]
        simp only [add, Modular.Lazy.evalZMod_add, hPx, hQx]
        rw [Reference.Aux.chordSlope_eq_mathlib hcoordX]
        simpa only [Reference.resultX, pow_two, sub_sub] using
          (Reference.Aux.resultX_eq_mathlib px qx
            (Reference.curve.toAffine.slope px qx py qy))
      · change Modular.Lazy.evalZMod base (ofElem y) ρ = _
        unfold Modular.Lazy.MulSubToElemZModSpec at hx hy
        rw [ofElem, Modular.Lazy.evalZMod_ofElem, hy, hslopeEq, hPy]
        simp only [sub, Modular.Lazy.evalZMod_sub, ofElem,
          Modular.Lazy.evalZMod_ofElem]
        rw [hx, hslopeEq]
        simp only [add, Modular.Lazy.evalZMod_add, hPx, hQx]
        rw [Reference.Aux.chordSlope_eq_mathlib hcoordX]
        simpa only [Reference.resultY, Reference.resultX, pow_two,
          sub_sub] using
          (Reference.Aux.resultY_eq_mathlib px qx py
            (Reference.curve.toAffine.slope px qx py qy))
  · intro hzero
    rw [hsum] at hzero
    exact (WeierstrassCurve.Affine.Point.some_ne_zero _ hzero).elim

@[spec] theorem addIncompleteChecked_complete_mathlib
    {P Q : Point} {p q : Reference.Point}
    (hPvalid : P.Valid ρ) (hQvalid : Q.Valid ρ)
    (hP : Reference.NormalizedRep ρ P p)
    (hQ : Reference.NormalizedRep ρ Q q)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hpq : p ≠ q) (hpnegq : p ≠ -q) :
    ⦃⌜True⌝⦄ Complete.interp ρ (addIncompleteChecked P Q)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      Reference.NormalizedRep ρ out (p + q)⌝⦄ := by
  have hsafe := Reference.Aux.chord_denominator_ne_zero
    hp0 hq0 hpq hpnegq hP.1 hQ.1
  rcases hPvalid with
    ⟨hPXbound, hPX, hPXCanonical, hPYbound, hPY, hPYCanonical, hPinf⟩
  rcases hQvalid with
    ⟨hQXbound, hQX, hQXCanonical, hQYbound, hQY, hQYCanonical, hQinf⟩
  mvcgen [addIncompleteChecked, finishAddCandidate]
  constructor
  · simpa using hsafe.1.symm
  · mvcgen [finishAddCandidate]
    constructor
    · simpa using hsafe.2.1.symm
    · mvcgen [finishAddCandidate]
      case vc1 => exact Modular.Lazy.sub_valid base hQX hPX
      case vc2 =>
        exact Modular.Lazy.ofElem_valid base
          (Modular.ofNat_valid base 1
            (by norm_num [base, baseModulus])
            (by norm_num [base, baseModulus]))
      case vc3 => exact hsafe.2.2
      case vc4 =>
        norm_num [sub, Modular.Lazy.sub, ofElem, Modular.Lazy.ofElem,
          hPXbound, hQXbound, Modular.Lazy.quotientExtraBits]
      case vc5 => exact Modular.Lazy.sub_valid base hQX hPX
      case vc6 => exact Modular.Lazy.sub_valid base hQY hPY
      case vc7 => exact hsafe.2.2
      case vc8 =>
        norm_num [sub, Modular.Lazy.sub, hPXbound, hPYbound,
          hQXbound, hQYbound, Modular.Lazy.quotientExtraBits]
      case vc9 slope hslope => exact hslope.1
      case vc10 slope hslope => exact hslope.1
      case vc11 => exact Modular.Lazy.add_valid base hPX hQX
      case vc12 slope hslope =>
        rw [hslope.2.2]
        norm_num [add, Modular.Lazy.add, hPXbound, hQXbound,
          Modular.Lazy.quotientExtraBits]
      case vc13 =>
        rename_i inverse hinverse slope hslope x hx
        exact hslope.1
      case vc14 =>
        rename_i inverse hinverse slope hslope x hx
        exact Modular.Lazy.sub_valid base hPX
          (Modular.Lazy.ofElem_valid base hx.1)
      case vc16 =>
        rename_i inverse hinverse slope hslope x hx
        rw [hslope.2.2]
        norm_num [sub, Modular.Lazy.sub, ofElem, Modular.Lazy.ofElem,
          hPXbound, hPYbound, Modular.Lazy.quotientExtraBits]
      case vc17 =>
        rename_i inverse hinverse slope hslope x hx y hy
        refine ⟨⟨rfl, Modular.Lazy.ofElem_valid base hx.1, hx.1.2,
          rfl, Modular.Lazy.ofElem_valid base hy.1, hy.1.2, by simp⟩, ?_⟩
        rcases hp : p with _ | ⟨px, py, hpcurve⟩
        · exact (hp0 hp).elim
        rcases hq : q with _ | ⟨qx, qy, hqcurve⟩
        · exact (hq0 hq).elim
        have hPsome : Reference.Represents ρ P (.some px py hpcurve) :=
          hp ▸ hP.1
        have hQsome : Reference.Represents ρ Q (.some qx qy hqcurve) :=
          hq ▸ hQ.1
        obtain ⟨_, hPx, hPy⟩ := Reference.Aux.represents_some hPsome
        obtain ⟨_, hQx, hQy⟩ := Reference.Aux.represents_some hQsome
        have hcoordX : px ≠ qx :=
          Reference.Aux.finite_x_ne_of_ne_and_ne_neg hpq hpnegq hp hq
        have hden : qx - px ≠ 0 := sub_ne_zero.mpr hcoordX.symm
        have hslopeEq : Modular.Lazy.evalZMod base slope ρ =
            Reference.chordSlope px py qx qy := by
          unfold Modular.Lazy.DivideZModSpec at hslope
          simp only [sub, Modular.Lazy.evalZMod_sub, hQx, hPx, hQy, hPy]
            at hslope
          exact (eq_div_iff hden).2 hslope.2.1
        have hsum :
            (WeierstrassCurve.Affine.Point.some px py hpcurve :
              Reference.Point) + .some qx qy hqcurve =
              .some _ _
                (WeierstrassCurve.Affine.nonsingular_add hpcurve hqcurve
                  (fun hxy => hcoordX hxy.1)) :=
          WeierstrassCurve.Affine.Point.add_of_X_ne hcoordX
        constructor
        · constructor
          · simp
          · unfold Reference.circuitCoordinates
            have hzeroFlag : (0 : LC ℤ).eval ρ.int = 0 := by simp
            rw [if_neg (by rw [hzeroFlag]; norm_num)]
            rw [hsum]
            unfold Reference.coordinates
            congr 1
            · change Modular.Lazy.evalZMod base (ofElem x) ρ = _
              unfold Modular.Lazy.MulSubToElemZModSpec at hx
              rw [ofElem, Modular.Lazy.evalZMod_ofElem, hx.2, hslopeEq]
              simp only [add, Modular.Lazy.evalZMod_add, hPx, hQx]
              rw [Reference.Aux.chordSlope_eq_mathlib hcoordX]
              simpa only [Reference.resultX, pow_two, sub_sub] using
                (Reference.Aux.resultX_eq_mathlib px qx
                  (Reference.curve.toAffine.slope px qx py qy))
            · change Modular.Lazy.evalZMod base (ofElem y) ρ = _
              unfold Modular.Lazy.MulSubToElemZModSpec at hx hy
              rw [ofElem, Modular.Lazy.evalZMod_ofElem, hy.2, hslopeEq, hPy]
              simp only [sub, Modular.Lazy.evalZMod_sub, ofElem,
                Modular.Lazy.evalZMod_ofElem]
              rw [hx.2, hslopeEq]
              simp only [add, Modular.Lazy.evalZMod_add, hPx, hQx]
              rw [Reference.Aux.chordSlope_eq_mathlib hcoordX]
              simpa only [Reference.resultY, Reference.resultX, pow_two,
                sub_sub] using
                (Reference.Aux.resultY_eq_mathlib px qx py
                  (Reference.curve.toAffine.slope px qx py qy))
        · intro hzero
          rw [hsum] at hzero
          exact (WeierstrassCurve.Affine.Point.some_ne_zero _ hzero).elim


end AffineSlope
end Freigen.F2Z.Examples.P256
