import Freigen.F2Z.Examples.P256.XOnlyLemmas
import Freigen.F2Z.Examples.P256.CanonicalXImpl

/-!
# Semantics of canonical terminal X-only complete affine addition

The selected X coordinate is opened canonically in the P-256 base field.  The
identity flag remains explicit because ECDSA rejects the identity at the final
acceptance boundary.
-/

namespace Freigen.F2Z.Examples.P256

open Std.Do
open scoped Std.Do
open Modular

namespace AffineSlope

def CanonicalXPoint.Valid (P : CanonicalXPoint)
    (ρ : WF.Valuation) : Prop :=
  P.X.Valid ρ ∧
    (P.infinity.eval ρ.int = 0 ∨ P.infinity.eval ρ.int = 1)

def CanonicalXPoint.toXPoint (P : CanonicalXPoint) : XPoint :=
  ⟨ofElem P.X, P.infinity⟩

theorem CanonicalXPoint.Valid.toXPoint {P : CanonicalXPoint}
    (hP : P.Valid ρ) : P.toXPoint.Valid ρ := by
  exact ⟨rfl, Modular.Lazy.ofElem_valid base hP.1,
    hP.1.2, hP.2⟩

end AffineSlope

namespace Reference

def CanonicalXRepresents (ρ : WF.Valuation)
    (P : AffineSlope.CanonicalXPoint) (p : Point) : Prop :=
  XRepresents ρ P.toXPoint p

end Reference

namespace AffineSlope.Aux

def SelectAddCanonicalXOutputSpec (ρ : WF.Valuation)
    (P Q : AffineSlope.Point) (control : AffineSlope.AddControl)
    (candidateX : AffineSlope.Rep)
    (out : AffineSlope.CanonicalXPoint) : Prop :=
  ∃ bothInfinity oppositePair finiteOpposite : LC ℤ,
    Gated3Spec ρ control.active P.infinity
      (Q.infinity - bothInfinity)
      candidateX Q.X P.X (AffineSlope.ofElem out.X) ∧
    AndBitSpec ρ P.infinity Q.infinity bothInfinity ∧
    AndBitSpec ρ control.sameX control.oppositeY oppositePair ∧
    AndBitSpec ρ control.finite oppositePair finiteOpposite ∧
    out.infinity.eval ρ.int =
      bothInfinity.eval ρ.int + finiteOpposite.eval ρ.int

@[spec] theorem selectAddOutputCanonicalX_sound
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {candidateX : AffineSlope.Rep} :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (AffineSlope.selectAddOutputCanonicalX P Q control candidateX)
    ⦃⇓ out => ⌜out.X.Valid ρ ∧
      SelectAddCanonicalXOutputSpec ρ P Q control candidateX out⌝⦄ := by
  mvcgen [AffineSlope.selectAddOutputCanonicalX]
  rename_i bothInfinity hbothInfinity
  intro bits
  mvcgen
  case vc1.hx => exact (by assumption : U.Rel ρ _ _).1
  case vc2.success =>
    rename_i xWord hxWord quotient hquotient
      hactive hPInfinity hQInfinity X hX finiteOpposite hfiniteOpposite
    rcases hfiniteOpposite with
      ⟨oppositePair, hoppositePair, hfiniteOpposite⟩
    refine ⟨hX.1, bothInfinity, oppositePair, finiteOpposite, ?_,
      hbothInfinity, hoppositePair, hfiniteOpposite, by simp⟩
    unfold Gated3Spec
    constructor
    · intro hgate
      have heq : candidateX.intVal.eval ρ.int =
          xWord.intVal.eval ρ.int +
            base.modulus * quotient.intVal.eval ρ.int := by
        simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul,
          LC.eval_zero, nsmul_eq_mul, hgate, one_mul] at hactive
        omega
      change Modular.Lazy.evalZMod base
        (Modular.Lazy.ofElem base X) ρ = _
      rw [Modular.Lazy.evalZMod_ofElem]
      unfold Modular.Lazy.evalElemZMod Modular.Lazy.evalZMod
      rw [hX.2]
      simpa using
        (congrArg (Int.castRingHom (ZMod base.modulus)) heq).symm
    · constructor
      · intro hgate
        have heq : Q.X.intVal.eval ρ.int =
            xWord.intVal.eval ρ.int +
              base.modulus * quotient.intVal.eval ρ.int := by
          simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul,
            LC.eval_zero, nsmul_eq_mul, hgate, one_mul] at hPInfinity
          omega
        change Modular.Lazy.evalZMod base
          (Modular.Lazy.ofElem base X) ρ = _
        rw [Modular.Lazy.evalZMod_ofElem]
        unfold Modular.Lazy.evalElemZMod Modular.Lazy.evalZMod
        rw [hX.2]
        simpa using
          (congrArg (Int.castRingHom (ZMod base.modulus)) heq).symm
      · intro hgate
        have heq : P.X.intVal.eval ρ.int =
            xWord.intVal.eval ρ.int +
              base.modulus * quotient.intVal.eval ρ.int := by
          simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul,
            LC.eval_zero, nsmul_eq_mul, hgate, one_mul] at hQInfinity
          omega
        change Modular.Lazy.evalZMod base
          (Modular.Lazy.ofElem base X) ρ = _
        rw [Modular.Lazy.evalZMod_ofElem]
        unfold Modular.Lazy.evalElemZMod Modular.Lazy.evalZMod
        rw [hX.2]
        simpa using
          (congrArg (Int.castRingHom (ZMod base.modulus)) heq).symm

theorem SelectAddCanonicalXOutputSpec.infinity_bit
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {candidateX : AffineSlope.Rep} {out : AffineSlope.CanonicalXPoint}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ)
    (hcontrol : AddControlSpec ρ P Q control)
    (hout : SelectAddCanonicalXOutputSpec ρ P Q control candidateX out) :
    out.infinity.eval ρ.int = 0 ∨ out.infinity.eval ρ.int = 1 := by
  rcases hP with ⟨_, _, _, _, _, _, hPinf⟩
  rcases hQ with ⟨_, _, _, _, _, _, hQinf⟩
  rcases hcontrol with ⟨_, _, hfinite, _, _, _, _, _, _⟩
  rcases hout with ⟨bothInfinity, _, finiteOpposite, _,
    hbothInfinity, _, hfiniteOpposite, houtInfinity⟩
  rcases hPinf with hp | hp <;>
    rcases hQinf with hq | hq <;>
    rcases hfiniteOpposite.2 with hfo | hfo <;>
    simp_all [AndBitSpec]

theorem add_specs_canonical_x_raw {P Q : AffineSlope.Point}
    {out : AffineSlope.CanonicalXPoint} {p q : Reference.Point}
    (hP : Reference.Represents ρ P p)
    (hQ : Reference.Represents ρ Q q)
    {control : AffineSlope.AddControl} {candidateX : AffineSlope.Rep}
    (hcontrol : AddControlSpec ρ P Q control)
    (hcandidate : AddCandidateXSpec ρ P Q control candidateX)
    (hout : SelectAddCanonicalXOutputSpec ρ P Q control candidateX out) :
    (out.infinity.eval ρ.int = 0 ∨ out.infinity.eval ρ.int = 1) ∧
      Reference.circuitXCoordinate ρ out.toXPoint =
        match Reference.slopeAddCoordinates p q with
        | .infinity => none
        | .finite x _ => some x := by
  rcases hout with ⟨bothInfinity, oppositePair, finiteOpposite,
    hX, hbothInfinity, hoppositePair, hfiniteOpposite, houtInfinity⟩
  have hcases := hcontrol.x_output_gated_cases hP.1 hQ.1 hbothInfinity
  have liftNondefault
      (hfourth :
        (control.finite - control.active).eval ρ.int = 0) :
      SelectAddXOutputSpec ρ P Q control candidateX out.toXPoint := by
    refine ⟨bothInfinity, oppositePair, finiteOpposite,
      ⟨hX.1, hX.2.1, hX.2.2, ?_⟩,
      hbothInfinity, hoppositePair, hfiniteOpposite, houtInfinity⟩
    intro h
    omega
  rcases hcases with hc | hc | hc | hc
  · exact add_specs_x_raw hP hQ hcontrol hcandidate
      (liftNondefault hc.2.2.2)
  · exact add_specs_x_raw hP hQ hcontrol hcandidate
      (liftNondefault hc.2.2.2)
  · exact add_specs_x_raw hP hQ hcontrol hcandidate
      (liftNondefault hc.2.2.2)
  · have hinfinity : out.infinity.eval ρ.int = 1 := by
      rcases hcontrol with
        ⟨hsame, hopposite, hfinite, doubleKind, genericCase,
          hdoubleKind, hdoubleCase, hgenericCase, hactive⟩
      have hfinite1 : control.finite.eval ρ.int = 1 := by
        simp only [LC.eval_sub] at hc
        omega
      have hgeneric0 : genericCase.eval ρ.int = 0 := by
        rw [hactive] at hc
        rcases hdoubleCase.2 with hd0 | hd1 <;>
          rcases hgenericCase.2 with hg0 | hg1 <;> omega
      have hsame1 : control.sameX.eval ρ.int = 1 := by
        rw [hgenericCase.1, hfinite1] at hgeneric0
        rcases hsame.1 with hs0 | hs1
        · simp [hs0] at hgeneric0
        · exact hs1
      have hdouble0 : control.doubleCase.eval ρ.int = 0 := by
        rw [hactive] at hc
        rcases hdoubleCase.2 with hd0 | hd1 <;>
          rcases hgenericCase.2 with hg0 | hg1 <;> omega
      have hdoubleKind0 : doubleKind.eval ρ.int = 0 := by
        rw [hdoubleCase.1, hfinite1] at hdouble0
        simpa using hdouble0
      have hopposite1 : control.oppositeY.eval ρ.int = 1 := by
        rw [hdoubleKind.1, hsame1] at hdoubleKind0
        rcases hopposite.1 with ho0 | ho1
        · simp [ho0] at hdoubleKind0
        · exact ho1
      have hboth0 : bothInfinity.eval ρ.int = 0 := by
        rw [hbothInfinity.1]
        simp [hc.2.1]
      have hoppositePair1 : oppositePair.eval ρ.int = 1 := by
        rw [hoppositePair.1, hsame1, hopposite1]
        norm_num
      have hfiniteOpposite1 : finiteOpposite.eval ρ.int = 1 := by
        rw [hfiniteOpposite.1, hfinite1, hoppositePair1]
        norm_num
      rw [houtInfinity, hboth0, hfiniteOpposite1]
      norm_num
    let zeroOut : AffineSlope.XPoint :=
      ⟨AffineSlope.ofElem zero, out.infinity⟩
    have hzeroSpec : SelectAddXOutputSpec ρ P Q control candidateX zeroOut := by
      refine ⟨bothInfinity, oppositePair, finiteOpposite, ?_,
        hbothInfinity, hoppositePair, hfiniteOpposite, houtInfinity⟩
      unfold Gated4Spec
      constructor
      · intro h
        omega
      · constructor
        · intro h
          omega
        · constructor
          · intro h
            omega
          · intro _
            rfl
    have hraw := add_specs_x_raw hP hQ hcontrol hcandidate hzeroSpec
    refine ⟨hraw.1, ?_⟩
    unfold Reference.circuitXCoordinate
    simp only [AffineSlope.CanonicalXPoint.toXPoint]
    rw [if_pos hinfinity]
    have hraw' := hraw.2
    unfold Reference.circuitXCoordinate at hraw'
    simp only [zeroOut] at hraw'
    rw [if_pos hinfinity] at hraw'
    exact hraw'

@[spec] theorem selectAddOutputCanonicalX_complete
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {candidateX : AffineSlope.Rep}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ)
    (hcontrol : AddControlSpec ρ P Q control)
    (hcandidateX : candidateX.Valid ρ)
    (hcandidateXCanonical :
      candidateX.intVal.eval ρ.int < base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectAddOutputCanonicalX P Q control candidateX)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      SelectAddCanonicalXOutputSpec ρ P Q control candidateX out⌝⦄ := by
  mvcgen [AffineSlope.selectAddOutputCanonicalX]
  case vc1.hx => exact hP.2.2.2.2.2.2
  case vc2.hy => exact hQ.2.2.2.2.2.2
  case vc3.success =>
    rename_i bothInfinity hbothInfinity
    let source : Int :=
      if control.active.eval ρ.int = 1 then candidateX.intVal.eval ρ.int
      else if P.infinity.eval ρ.int = 1 then Q.X.intVal.eval ρ.int
      else if Q.infinity.eval ρ.int = 1 then P.X.intVal.eval ρ.int
      else 0
    have hsource0 : 0 ≤ source := by
      simp only [source]
      split_ifs <;> first
        | exact hcandidateX.1
        | exact hQ.2.1.1
        | exact hP.2.1.1
        | omega
    have hsourceLt : source < base.modulus := by
      simp only [source]
      split_ifs <;> first
        | exact hcandidateXCanonical
        | exact hQ.2.2.1
        | exact hP.2.2.1
        | norm_num [base, baseModulus]
    have hsourceNatLt : source.toNat < base.modulus :=
      (Int.toNat_lt hsource0).2 hsourceLt
    have hsourceBits : source.toNat < 2 ^ 256 :=
      hsourceNatLt.trans_le base.fits
    let bits : Vector Bool 257 := Vector.ofFn fun i =>
      if _ : i.val < 256 then source.toNat.testBit i.val else false
    refine ⟨bits, ?_, ?_⟩
    · simp [WF.interpHint, WF.evalArgs,
        AffineSlope.canonicalAddXHint, source, bits, hsource0,
        Nat.mod_eq_of_lt hsourceNatLt,
        Nat.div_eq_of_lt hsourceNatLt]
    · mvcgen
      rename_i xWord hxWord quotient hquotient
      have hxWordValue : xWord.intVal.eval ρ.int = source := by
        rw [U.Rel.intVal hxWord]
        have hwordInt := congrArg Int.ofNat
          (Modular.Aux.constWord_eval_toNat
            source.toNat hsourceBits ρ)
        simpa [bits, Int.toNat_of_nonneg hsource0] using hwordInt
      have hquotientValue : quotient.intVal.eval ρ.int = 0 := by
        rw [U.Rel.intVal hquotient]
        have hqInt := congrArg Int.ofNat
          (Modular.Aux.constWord_eval_toNat (n := 1) 0 (by norm_num) ρ)
        simpa [bits] using hqInt
      have hcases := hcontrol.x_output_gated_cases
        hP.2.2.2.2.2.2 hQ.2.2.2.2.2.2 hbothInfinity
      constructor
      · rcases hcases with hc | hc | hc | hc <;>
          simp_all [source, AndBitSpec]
      · mvcgen
        case vc1.h =>
          constructor
          · rcases hcases with hc | hc | hc | hc <;>
              simp_all [source, AndBitSpec]
          · mvcgen
            case vc1.h =>
              constructor
              · rcases hcases with hc | hc | hc | hc <;>
                  simp_all [source, AndBitSpec]
              · mvcgen
                case vc1.hx => exact hxWord.1
                case vc2.hlt => simpa [hxWordValue] using hsourceLt
                case vc3.hx => exact hcontrol.1.1
                case vc4.hy => exact hcontrol.2.1.1
                case vc5.hz => exact hcontrol.2.2.1.2
                case vc6.success =>
                  rename_i X hX finiteOpposite hfiniteOpposite
                  rcases hfiniteOpposite with
                    ⟨oppositePair, hoppositePair, hfiniteOpposite⟩
                  have houtInt : X.val.intVal.eval ρ.int = source := by
                    rw [hX.2, hxWordValue]
                  have hGated : Gated3Spec ρ control.active P.infinity
                      (Q.infinity - bothInfinity) candidateX Q.X P.X
                      (AffineSlope.ofElem X) := by
                    rcases hcases with hc | hc | hc | hc
                    · simp_all [Gated3Spec, source, AffineSlope.ofElem,
                        Modular.Lazy.ofElem, Modular.Lazy.evalZMod]
                    · simp_all [Gated3Spec, source, AffineSlope.ofElem,
                        Modular.Lazy.ofElem, Modular.Lazy.evalZMod]
                    · have hboth0 : bothInfinity.eval ρ.int = 0 := by
                        rw [hbothInfinity.1]
                        simp [hc.2.1]
                      have hQInfinity1 : Q.infinity.eval ρ.int = 1 := by
                        simp only [LC.eval_sub] at hc
                        omega
                      simp_all [Gated3Spec, source, AffineSlope.ofElem,
                        Modular.Lazy.ofElem, Modular.Lazy.evalZMod]
                    · simp_all [Gated3Spec, source, AffineSlope.ofElem,
                        Modular.Lazy.ofElem, Modular.Lazy.evalZMod]
                  have houtSpec : SelectAddCanonicalXOutputSpec ρ P Q
                      control candidateX
                      ⟨X, bothInfinity + finiteOpposite⟩ :=
                    ⟨bothInfinity, oppositePair, finiteOpposite, hGated,
                      hbothInfinity, hoppositePair, hfiniteOpposite, by simp⟩
                  exact ⟨⟨hX.1,
                    SelectAddCanonicalXOutputSpec.infinity_bit
                      hP hQ hcontrol houtSpec⟩, houtSpec⟩

theorem add_specs_canonical_x_mathlib {P Q : AffineSlope.Point}
    {out : AffineSlope.CanonicalXPoint} {p q : Reference.Point}
    (hP : Reference.Represents ρ P p)
    (hQ : Reference.Represents ρ Q q)
    {control : AffineSlope.AddControl} {candidateX : AffineSlope.Rep}
    (hcontrol : AddControlSpec ρ P Q control)
    (hcandidate : AddCandidateXSpec ρ P Q control candidateX)
    (hout : SelectAddCanonicalXOutputSpec ρ P Q control candidateX out) :
    Reference.CanonicalXRepresents ρ out (p + q) := by
  have hraw := add_specs_canonical_x_raw hP hQ hcontrol hcandidate hout
  exact ⟨hraw.1,
    hraw.2.trans (Reference.xCoordinate_slopeAdd p q)⟩

end AffineSlope.Aux

open AffineSlope

@[spec] theorem addCompleteCollapsedCanonicalX_sound_mathlib
    {P Q : Point} {p q : Reference.Point}
    (hP : Reference.Represents ρ P p)
    (hQ : Reference.Represents ρ Q q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (addCompleteCollapsedCanonicalX P Q)
    ⦃⇓ out => ⌜out.X.Valid ρ ∧
      Reference.CanonicalXRepresents ρ out (p + q)⌝⦄ := by
  mvcgen [addCompleteCollapsedCanonicalX]
  rename_i control hcontrol candidateX hcandidate out
  intros houtValid hout
  exact ⟨houtValid, Aux.add_specs_canonical_x_mathlib hP hQ hcontrol
    hcandidate hout⟩

@[spec] theorem addCompleteCollapsedCanonicalX_complete_mathlib
    {P Q : Point} {q p : Reference.Point}
    (hPvalid : P.Valid ρ) (hQvalid : Q.Valid ρ)
    (hP : Reference.NormalizedRep ρ P p)
    (hQ : Reference.NormalizedRep ρ Q q)
    (hnoTwoTorsion : p = 0 ∨ p + p ≠ 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (addCompleteCollapsedCanonicalX P Q)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      Reference.CanonicalXRepresents ρ out (p + q)⌝⦄ := by
  mvcgen [addCompleteCollapsedCanonicalX]
  all_goals first
    | exact hPvalid
    | exact hQvalid
    | exact hP.1
    | exact hnoTwoTorsion
    | assumption
    | skip
  case vc9.success.success.success =>
    rename_i control hcontrol candidateX hcandidate out
    intros houtValid houtSpec
    exact ⟨houtValid,
      Aux.add_specs_canonical_x_mathlib hP.1 hQ.1 hcontrol
        hcandidate.2.2.2 houtSpec⟩
  all_goals aesop

end Freigen.F2Z.Examples.P256
