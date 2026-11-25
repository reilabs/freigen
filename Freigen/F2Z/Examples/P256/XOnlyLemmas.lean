import Freigen.F2Z.Examples.P256
import Freigen.F2Z.Examples.P256.XOnlyImpl

/-!
# Semantics of terminal X-only complete affine addition

The terminal ECDSA check consumes only the identity flag and X coordinate.
This module proves that the specialized circuit preserves exactly that
projection of Mathlib point addition while retaining every complete-add case.
-/

namespace Freigen.F2Z.Examples.P256

open Std.Do
open scoped Std.Do
open Modular

namespace AffineSlope

def XPoint.Valid (P : XPoint) (ρ : WF.Valuation) : Prop :=
  P.X.bound = 2 ∧ P.X.Valid ρ ∧
    P.X.intVal.eval ρ.int < base.modulus ∧
    (P.infinity.eval ρ.int = 0 ∨ P.infinity.eval ρ.int = 1)

def Point.toXPoint (P : Point) : XPoint := ⟨P.X, P.infinity⟩

theorem Point.Valid.toXPoint {P : Point} {rho : WF.Valuation}
    (hP : P.Valid rho) : P.toXPoint.Valid rho := by
  exact ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2.2.2.2⟩

end AffineSlope

namespace Reference

def xCoordinate : Point → Option Field
  | 0 => none
  | .some x _ _ => some x

def circuitXCoordinate (ρ : WF.Valuation)
    (P : AffineSlope.XPoint) : Option Field :=
  if P.infinity.eval ρ.int = 1 then none
  else some (Modular.Lazy.evalZMod base P.X ρ)

def XRepresents (ρ : WF.Valuation) (P : AffineSlope.XPoint)
    (p : Point) : Prop :=
  (P.infinity.eval ρ.int = 0 ∨ P.infinity.eval ρ.int = 1) ∧
    circuitXCoordinate ρ P = xCoordinate p

def NormalizedXRep (ρ : WF.Valuation) (P : AffineSlope.XPoint)
    (p : Point) : Prop :=
  XRepresents ρ P p ∧
    (p = 0 → Modular.Lazy.evalZMod base P.X ρ = 0)

theorem Represents.toXRepresents {rho : WF.Valuation}
    {P : AffineSlope.Point} {p : Point}
    (h : Represents rho P p) : XRepresents rho P.toXPoint p := by
  rcases h with ⟨hbit, hcoordinates⟩
  constructor
  · exact hbit
  · rcases p with _ | ⟨x, y, hxy⟩
    · have hinfinity := Aux.represents_zero ⟨hbit, hcoordinates⟩
      simp [circuitXCoordinate, xCoordinate, AffineSlope.Point.toXPoint,
        hinfinity]
    · obtain ⟨hinfinity, hx, _⟩ :=
        Aux.represents_some ⟨hbit, hcoordinates⟩
      simp [circuitXCoordinate, xCoordinate, AffineSlope.Point.toXPoint,
        hinfinity, hx]

theorem NormalizedRep.toNormalizedXRep {rho : WF.Valuation}
    {P : AffineSlope.Point} {p : Point}
    (h : NormalizedRep rho P p) : NormalizedXRep rho P.toXPoint p := by
  exact ⟨h.1.toXRepresents, fun hp => (h.2 hp).1⟩

theorem XRepresents.zero {rho : WF.Valuation}
    {P : AffineSlope.XPoint} (h : XRepresents rho P 0) :
    P.infinity.eval rho.int = 1 := by
  rcases h with ⟨hbit, hx⟩
  rcases hbit with hzero | hone
  · simp [circuitXCoordinate, xCoordinate, hzero] at hx
  · exact hone

theorem XRepresents.some {rho : WF.Valuation}
    {P : AffineSlope.XPoint} {x y : Field}
    {hxy : curve.toAffine.Nonsingular x y}
    (h : XRepresents rho P (.some x y hxy)) :
    P.infinity.eval rho.int = 0 ∧
      Modular.Lazy.evalZMod base P.X rho = x := by
  rcases h with ⟨hbit, hx⟩
  rcases hbit with hzero | hone
  · simp [circuitXCoordinate, xCoordinate, hzero] at hx
    exact ⟨hzero, hx⟩
  · simp [circuitXCoordinate, xCoordinate, hone] at hx

theorem xCoordinate_slopeAdd (p q : Point) :
    (match slopeAddCoordinates p q with
      | .infinity => none
      | .finite x _ => some x) = xCoordinate (p + q) := by
  rw [slopeAddCoordinates_eq_mathlib]
  cases p + q <;> rfl

end Reference

namespace AffineSlope.Aux

def AddCandidateXSpec (ρ : WF.Valuation) (P Q : AffineSlope.Point)
    (control : AffineSlope.AddControl) (candidateX : AffineSlope.Rep) : Prop :=
  control.active.eval ρ.int = 1 →
    ∃ slope : AffineSlope.Rep,
      (if control.doubleCase.eval ρ.int = 1 then
          Modular.Lazy.evalZMod base slope ρ *
              (2 * Modular.Lazy.evalZMod base P.Y ρ) =
            3 * (Modular.Lazy.evalZMod base P.X ρ *
              Modular.Lazy.evalZMod base P.X ρ) - 3
        else
          Modular.Lazy.evalZMod base slope ρ *
              (Modular.Lazy.evalZMod base Q.X ρ -
            Modular.Lazy.evalZMod base P.X ρ) =
            Modular.Lazy.evalZMod base Q.Y ρ -
              Modular.Lazy.evalZMod base P.Y ρ) ∧
      Modular.Lazy.evalZMod base candidateX ρ =
        Modular.Lazy.evalZMod base slope ρ *
            Modular.Lazy.evalZMod base slope ρ -
          (Modular.Lazy.evalZMod base P.X ρ +
            Modular.Lazy.evalZMod base Q.X ρ)

def SelectAddXOutputSpec (ρ : WF.Valuation) (P Q : AffineSlope.Point)
    (control : AffineSlope.AddControl) (candidateX : AffineSlope.Rep)
    (out : AffineSlope.XPoint) : Prop :=
  ∃ bothInfinity oppositePair finiteOpposite : LC ℤ,
    Gated4Spec ρ control.active P.infinity
      (Q.infinity - bothInfinity) (control.finite - control.active)
      candidateX Q.X P.X (AffineSlope.ofElem zero) out.X ∧
    AndBitSpec ρ P.infinity Q.infinity bothInfinity ∧
    AndBitSpec ρ control.sameX control.oppositeY oppositePair ∧
    AndBitSpec ρ control.finite oppositePair finiteOpposite ∧
    out.infinity.eval ρ.int =
      bothInfinity.eval ρ.int + finiteOpposite.eval ρ.int

theorem AddControlSpec.x_output_gated_cases
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {bothInfinity : LC ℤ}
    (hcontrol : AddControlSpec ρ P Q control)
    (hPinf : P.infinity.eval ρ.int = 0 ∨
      P.infinity.eval ρ.int = 1)
    (hQinf : Q.infinity.eval ρ.int = 0 ∨
      Q.infinity.eval ρ.int = 1)
    (hboth : AndBitSpec ρ P.infinity Q.infinity bothInfinity) :
    Gated4Cases ρ control.active P.infinity
      (Q.infinity - bothInfinity) (control.finite - control.active) := by
  have hactiveBit := hcontrol.active_bit
  rcases hcontrol with
    ⟨_, _, hfinite, doubleKind, genericCase,
      hdoubleKind, hdoubleCase, hgenericCase, hactive⟩
  have active_zero (hf : control.finite.eval ρ.int = 0) :
      control.active.eval ρ.int = 0 := by
    have hd : control.doubleCase.eval ρ.int = 0 := by
      rw [hdoubleCase.1, hf]
      norm_num
    have hg : genericCase.eval ρ.int = 0 := by
      rw [hgenericCase.1, hf]
      norm_num
    rw [hactive, hd, hg]
    norm_num
  rcases hPinf with hp | hp <;> rcases hQinf with hq | hq
  · have hf : control.finite.eval ρ.int = 1 := by
      rw [hfinite.1]
      simp [hp, hq]
    have hb : bothInfinity.eval ρ.int = 0 := by
      rw [hboth.1]
      simp [hp, hq]
    rcases hactiveBit with ha | ha
    · exact Or.inr (Or.inr (Or.inr ⟨ha, hp, by simp [hq, hb], by simp [hf, ha]⟩))
    · exact Or.inl ⟨ha, hp, by simp [hq, hb], by simp [hf, ha]⟩
  · have hf : control.finite.eval ρ.int = 0 := by
      rw [hfinite.1]
      simp [hp, hq]
    have hb : bothInfinity.eval ρ.int = 0 := by
      rw [hboth.1]
      simp [hp, hq]
    have ha := active_zero hf
    exact Or.inr (Or.inr (Or.inl ⟨ha, hp, by simp [hq, hb], by simp [hf, ha]⟩))
  · have hf : control.finite.eval ρ.int = 0 := by
      rw [hfinite.1]
      simp [hp, hq]
    have hb : bothInfinity.eval ρ.int = 0 := by
      rw [hboth.1]
      simp [hp, hq]
    have ha := active_zero hf
    exact Or.inr (Or.inl ⟨ha, hp, by simp [hq, hb], by simp [hf, ha]⟩)
  · have hf : control.finite.eval ρ.int = 0 := by
      rw [hfinite.1]
      simp [hp, hq]
    have hb : bothInfinity.eval ρ.int = 1 := by
      rw [hboth.1]
      simp [hp, hq]
    have ha := active_zero hf
    exact Or.inr (Or.inl ⟨ha, hp, by simp [hq, hb], by simp [hf, ha]⟩)

theorem SelectAddXOutputSpec.infinity_bit
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {candidateX : AffineSlope.Rep} {out : AffineSlope.XPoint}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ)
    (hcontrol : AddControlSpec ρ P Q control)
    (hout : SelectAddXOutputSpec ρ P Q control candidateX out) :
    out.infinity.eval ρ.int = 0 ∨ out.infinity.eval ρ.int = 1 := by
  rcases hP with ⟨_, _, _, _, _, _, hPinf⟩
  rcases hQ with ⟨_, _, _, _, _, _, hQinf⟩
  rcases hcontrol with ⟨_, _, hfinite, _, _, _, _, _, _⟩
  rcases hout with ⟨bothInfinity, _, finiteOpposite, _,
    hbothInfinity, _, hfiniteOpposite, houtInfinity⟩
  rcases hPinf with hp | hp <;>
    rcases hQinf with hq | hq <;>
    rcases hfiniteOpposite.2 with hfo | hfo <;>
    simp_all [AndBitSpec] <;> omega

@[spec] theorem finishAddCandidateX_sound {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl}
    {operands : AffineSlope.SlopeOperands}
    (hoperands : SlopeOperandsSpec ρ P Q control operands)
    (hdoubleBit : control.doubleCase.eval ρ.int = 0 ∨
      control.doubleCase.eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (AffineSlope.finishAddCandidateX P Q operands)
    ⦃⇓ candidateX => ⌜AddCandidateXSpec ρ P Q control candidateX⌝⦄ := by
  mvcgen [AffineSlope.finishAddCandidateX]
  rename_i slope hslope candidateX hcandidateX
  unfold AddCandidateXSpec
  intro hactive
  rcases hoperands.1 hactive with ⟨hdouble, hgeneric⟩
  by_cases hd : control.doubleCase.eval ρ.int = 1
  · rcases hdouble hd with ⟨hnum, hden⟩
    refine ⟨slope, ?_⟩
    simp_all [Modular.Lazy.DivideZModSpec,
      Modular.Lazy.MulSubToElemZModSpec, AffineSlope.add,
      AffineSlope.ofElem]
  · have hd0 : control.doubleCase.eval ρ.int = 0 := by
      rcases hdoubleBit with h | h
      · exact h
      · contradiction
    rcases hgeneric hd0 with ⟨hnum, hden⟩
    refine ⟨slope, ?_⟩
    simp_all [Modular.Lazy.DivideZModSpec,
      Modular.Lazy.MulSubToElemZModSpec, AffineSlope.add,
      AffineSlope.ofElem]

@[spec] theorem finishAddCandidateX_complete {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl}
    {operands : AffineSlope.SlopeOperands}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ)
    (hoperands : operands.Valid ρ)
    (hoperandsSpec : SlopeOperandsSpec ρ P Q control operands)
    (hden : Modular.Lazy.evalZMod base operands.denominator ρ ≠ 0)
    (hdoubleBit : control.doubleCase.eval ρ.int = 0 ∨
      control.doubleCase.eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.finishAddCandidateX P Q operands)
    ⦃⇓ candidateX => ⌜candidateX.Valid ρ ∧
      candidateX.bound = 2 ∧
      candidateX.intVal.eval ρ.int < base.modulus ∧
      AddCandidateXSpec ρ P Q control candidateX⌝⦄ := by
  rcases hP with ⟨hPXbound, hPX, _, _, _, _, _⟩
  rcases hQ with ⟨hQXbound, hQX, _, _, _, _, _⟩
  rcases hoperands with ⟨hnum, hnumBound, hdenValid, hdenBound⟩
  mvcgen [AffineSlope.finishAddCandidateX]
  all_goals first
    | exact hdenValid
    | exact hnum
    | exact hden
    | exact hPX
    | exact Modular.Lazy.add_valid base hPX hQX
    | simp [AffineSlope.add, Modular.Lazy.add,
        Modular.Lazy.quotientExtraBits, hPXbound, hQXbound,
        hnumBound, hdenBound]
    | skip
  case vc5.hx slope hslope => exact hslope.1
  case vc6.hy slope hslope => exact hslope.1
  case vc8.hbound slope hslope =>
    rw [hslope.2.2]
    norm_num [AffineSlope.add, Modular.Lazy.add, hPXbound, hQXbound,
      Modular.Lazy.quotientExtraBits]
  case vc9.success slope hslope candidateX hcandidateX =>
    refine ⟨Modular.Lazy.ofElem_valid base hcandidateX.1,
      rfl, hcandidateX.1.2, ?_⟩
    unfold AddCandidateXSpec
    unfold Modular.Lazy.DivideZModSpec at hslope
    unfold Modular.Lazy.MulSubToElemZModSpec at hcandidateX
    intro hactive
    rcases hoperandsSpec.1 hactive with ⟨hdouble, hgeneric⟩
    have hcandidateXEq := hcandidateX.2
    simp only [AffineSlope.add, Modular.Lazy.evalZMod_add] at hcandidateXEq
    rcases hdoubleBit with hd0 | hd1
    · rcases hgeneric hd0 with ⟨hnumEq, hdenEq⟩
      have hslopeEq := hslope.2.1
      rw [hdenEq, hnumEq] at hslopeEq
      exact ⟨slope, by simpa [hd0] using hslopeEq, hcandidateXEq⟩
    · rcases hdouble hd1 with ⟨hnumEq, hdenEq⟩
      have hslopeEq := hslope.2.1
      rw [hdenEq, hnumEq] at hslopeEq
      exact ⟨slope, by simpa [hd1] using hslopeEq, hcandidateXEq⟩

@[spec] theorem finishAddCandidateCollapsedX_sound {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl}
    {operands : AffineSlope.SlopeOperands}
    (hoperands : SlopeOperandsSpec ρ P Q control operands)
    (hdoubleBit : control.doubleCase.eval ρ.int = 0 ∨
      control.doubleCase.eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (AffineSlope.finishAddCandidateCollapsedX P Q operands)
    ⦃⇓ candidateX => ⌜AddCandidateXSpec ρ P Q control candidateX⌝⦄ := by
  mvcgen [AffineSlope.finishAddCandidateCollapsedX]
  rename_i slope hslope candidateX hcandidateX
  unfold AddCandidateXSpec
  intro hactive
  rcases hoperands.1 hactive with ⟨hdouble, hgeneric⟩
  by_cases hd : control.doubleCase.eval ρ.int = 1
  · rcases hdouble hd with ⟨hnum, hden⟩
    refine ⟨slope, ?_⟩
    simp_all [Modular.Lazy.DivideZModSpec,
      Modular.Lazy.MulSubToElemZModSpec,
      AffineSlope.collapsedCandidateXTarget, AffineSlope.add,
      AffineSlope.ofElem]
  · have hd0 : control.doubleCase.eval ρ.int = 0 := by
      rcases hdoubleBit with h | h
      · exact h
      · contradiction
    rcases hgeneric hd0 with ⟨hnum, hden⟩
    refine ⟨slope, ?_⟩
    simp_all [Modular.Lazy.DivideZModSpec,
      Modular.Lazy.MulSubToElemZModSpec,
      AffineSlope.collapsedCandidateXTarget, AffineSlope.add,
      AffineSlope.ofElem]

@[spec] theorem finishAddCandidateCollapsedX_complete {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl}
    {operands : AffineSlope.SlopeOperands}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ)
    (hoperands : CollapsedSlopeOperandsValid ρ operands)
    (hoperandsSpec : SlopeOperandsSpec ρ P Q control operands)
    (hden : Modular.Lazy.evalZMod base operands.denominator ρ ≠ 0)
    (hdoubleBit : control.doubleCase.eval ρ.int = 0 ∨
      control.doubleCase.eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.finishAddCandidateCollapsedX P Q operands)
    ⦃⇓ candidateX => ⌜candidateX.Valid ρ ∧
      candidateX.bound = 2 ∧
      candidateX.intVal.eval ρ.int < base.modulus ∧
      AddCandidateXSpec ρ P Q control candidateX⌝⦄ := by
  rcases hP with ⟨hPXbound, hPX, _, _, _, _, _⟩
  rcases hQ with ⟨hQXbound, hQX, _, _, _, _, _⟩
  rcases hoperands with ⟨hnum, hnumBound, hdenValid, hdenBound⟩
  mvcgen [AffineSlope.finishAddCandidateCollapsedX]
  all_goals first
    | exact hdenValid
    | exact hnum
    | exact hden
    | exact hPX
    | exact Modular.Lazy.add_valid base hPX hQX
    | simp [AffineSlope.add, Modular.Lazy.add,
        Modular.Lazy.quotientExtraBits, hPXbound, hQXbound,
        hnumBound, hdenBound]
    | skip
  case vc8.hslope =>
    rename_i slope hslope
    exact hslope.1
  case vc9.hslopeBound =>
    rename_i slope hslope
    exact hslope.2.1
  case vc10.hslopeCanonical =>
    rename_i slope hslope
    exact hslope.2.2.1
  case vc11.success.success =>
    rename_i slope hslope candidateX hcandidateX
    refine ⟨Modular.Lazy.ofElem_valid base hcandidateX.1,
      rfl, hcandidateX.1.2, ?_⟩
    unfold AddCandidateXSpec
    unfold Modular.Lazy.DivideZModSpec at hslope
    unfold Modular.Lazy.MulSubToElemZModSpec at hcandidateX
    intro hactive
    rcases hoperandsSpec.1 hactive with ⟨hdouble, hgeneric⟩
    have hcandidateXEq := hcandidateX.2
    simp only [AffineSlope.collapsedCandidateXTarget, AffineSlope.add,
      Modular.Lazy.evalZMod_add] at hcandidateXEq
    rcases hdoubleBit with hd0 | hd1
    · rcases hgeneric hd0 with ⟨hnumEq, hdenEq⟩
      have hslopeEq := hslope.2.2.2
      rw [hdenEq, hnumEq] at hslopeEq
      exact ⟨slope, by simpa [hd0] using hslopeEq, hcandidateXEq⟩
    · rcases hdouble hd1 with ⟨hnumEq, hdenEq⟩
      have hslopeEq := hslope.2.2.2
      rw [hdenEq, hnumEq] at hslopeEq
      exact ⟨slope, by simpa [hd1] using hslopeEq, hcandidateXEq⟩
@[spec] theorem addCandidateCollapsedX_sound {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl}
    (hcontrol : AddControlSpec ρ P Q control) :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (AffineSlope.addCandidateCollapsedX P Q control)
    ⦃⇓ candidateX => ⌜AddCandidateXSpec ρ P Q control candidateX⌝⦄ := by
  have hdoubleBit : control.doubleCase.eval ρ.int = 0 ∨
      control.doubleCase.eval ρ.int = 1 := by
    rcases hcontrol with ⟨_, _, _, _, _, _, hdoubleCase, _, _⟩
    exact hdoubleCase.2
  mvcgen [AffineSlope.addCandidateCollapsedX]
  all_goals intros <;> assumption

@[spec] theorem addCandidateCollapsedX_complete {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl} {p : Reference.Point}
    (hPvalid : P.Valid ρ) (hQvalid : Q.Valid ρ)
    (hcontrol : AddControlSpec ρ P Q control)
    (hP : Reference.Represents ρ P p)
    (hnoTwoTorsion : p = 0 ∨ p + p ≠ 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.addCandidateCollapsedX P Q control)
    ⦃⇓ candidateX => ⌜candidateX.Valid ρ ∧
      candidateX.bound = 2 ∧
      candidateX.intVal.eval ρ.int < base.modulus ∧
      AddCandidateXSpec ρ P Q control candidateX⌝⦄ := by
  have hdoubleBit : control.doubleCase.eval ρ.int = 0 ∨
      control.doubleCase.eval ρ.int = 1 := by
    rcases hcontrol with ⟨_, _, _, _, _, _, hdoubleCase, _, _⟩
    exact hdoubleCase.2
  mvcgen [AffineSlope.addCandidateCollapsedX]
  all_goals first
    | exact hPvalid
    | exact hQvalid
    | exact hcontrol
    | exact hP
    | exact hnoTwoTorsion
    | exact hdoubleBit
    | assumption
    | skip
  all_goals intros <;> assumption

@[spec] theorem selectAddOutputCollapsedX_sound
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {candidateX : AffineSlope.Rep} :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (AffineSlope.selectAddOutputCollapsedX P Q control candidateX)
    ⦃⇓ out => ⌜SelectAddXOutputSpec ρ P Q control candidateX out⌝⦄ := by
  mvcgen -trivial [AffineSlope.selectAddOutputCollapsedX,
    AffineSlope.selectAddCoordinateCollapsed, SelectAddXOutputSpec]
  rename_i bothInfinity hbothInfinity X hX
    finiteOpposite hfiniteOpposite
  rcases hfiniteOpposite with
    ⟨oppositePair, hoppositePair, hfiniteOpposite⟩
  exact ⟨bothInfinity, oppositePair, finiteOpposite,
    hX, hbothInfinity, hoppositePair, hfiniteOpposite, by simp⟩

@[spec] theorem selectAddOutputCollapsedX_complete
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {candidateX : AffineSlope.Rep}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ)
    (hcontrol : AddControlSpec ρ P Q control)
    (hcandidateX : candidateX.Valid ρ)
    (hcandidateXCanonical :
      candidateX.intVal.eval ρ.int < base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectAddOutputCollapsedX P Q control candidateX)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      SelectAddXOutputSpec ρ P Q control candidateX out⌝⦄ := by
  rcases hP with ⟨hPXbound, hPX, hPXCanonical,
    hPYbound, hPY, hPYCanonical, hPinf⟩
  rcases hQ with ⟨hQXbound, hQX, hQXCanonical,
    hQYbound, hQY, hQYCanonical, hQinf⟩
  have hzeroElem : zero.Valid ρ :=
    Modular.ofNat_valid base 0 (by native_decide) (by native_decide)
  have hzero : (AffineSlope.ofElem zero).Valid ρ :=
    Modular.Lazy.ofElem_valid base hzeroElem
  have hzeroCanonical :
      (AffineSlope.ofElem zero).intVal.eval ρ.int < base.modulus :=
    hzeroElem.2
  mvcgen -trivial [AffineSlope.selectAddOutputCollapsedX,
    AffineSlope.selectAddCoordinateCollapsed]
  case vc1.hx => exact hPinf
  case vc2.hy => exact hQinf
  case vc3.hcases => exact hcontrol.x_output_gated_cases hPinf hQinf (by assumption)
  case vc4.hvalue1 => exact hcandidateX
  case vc5.hvalue1Canonical => exact hcandidateXCanonical
  case vc6.hvalue2 => exact hQX
  case vc7.hvalue2Canonical => exact hQXCanonical
  case vc8.hvalue3 => exact hPX
  case vc9.hvalue3Canonical => exact hPXCanonical
  case vc10.hvalue4 => exact hzero
  case vc11.hvalue4Canonical => exact hzeroCanonical
  case vc12.hx => exact hcontrol.1.1
  case vc13.hy => exact hcontrol.2.1.1
  case vc14.hz => exact hcontrol.2.2.1.2
  case vc15.success.success.success =>
    rename_i bothInfinity hbothInfinity X hX finiteOpposite hfiniteOpposite
    rcases hfiniteOpposite with
      ⟨oppositePair, hoppositePair, hfiniteOpposite⟩
    have houtSpec : SelectAddXOutputSpec ρ P Q control candidateX
        ⟨X, bothInfinity + finiteOpposite⟩ :=
      ⟨bothInfinity, oppositePair, finiteOpposite,
        hX.1, hbothInfinity, hoppositePair, hfiniteOpposite, by simp⟩
    constructor
    · exact ⟨hX.2.2.2, hX.2.1, hX.2.2.1,
        SelectAddXOutputSpec.infinity_bit
          ⟨hPXbound, hPX, hPXCanonical, hPYbound, hPY,
            hPYCanonical, hPinf⟩
          ⟨hQXbound, hQX, hQXCanonical, hQYbound, hQY,
            hQYCanonical, hQinf⟩
          hcontrol houtSpec⟩
    · exact houtSpec

theorem add_specs_x_raw {P Q : AffineSlope.Point}
    {out : AffineSlope.XPoint} {p q : Reference.Point}
    (hP : Reference.Represents ρ P p)
    (hQ : Reference.Represents ρ Q q)
    {control : AffineSlope.AddControl} {candidateX : AffineSlope.Rep}
    (hcontrol : AddControlSpec ρ P Q control)
    (hcandidate : AddCandidateXSpec ρ P Q control candidateX)
    (hout : SelectAddXOutputSpec ρ P Q control candidateX out) :
    (out.infinity.eval ρ.int = 0 ∨ out.infinity.eval ρ.int = 1) ∧
      Reference.circuitXCoordinate ρ out =
        match Reference.slopeAddCoordinates p q with
        | .infinity => none
        | .finite x _ => some x := by
  rcases hcontrol with
    ⟨hsame, hopposite, hfinite, doubleKind, genericCase,
      hdoubleKind, hdoubleCase, hgenericCase, hactive⟩
  rcases hout with
    ⟨bothInfinity, oppositePair, finiteOpposite, hX,
      hbothInfinity, hoppositePair, hfiniteOpposite, houtInfinity⟩
  rcases p with _ | ⟨px, py, hpcurve⟩
  · have hpinf := Reference.Aux.represents_zero hP
    rcases q with _ | ⟨qx, qy, hqcurve⟩
    · have hqinf := Reference.Aux.represents_zero hQ
      simp_all [AndBitSpec, Gated4Spec,
        Reference.circuitXCoordinate, Reference.slopeAddCoordinates,
        Reference.coordinates,
        AffineSlope.ofElem, Modular.Lazy.evalZMod,
        Modular.Lazy.evalElemZMod]
    · obtain ⟨hqinf, hqx, hqy⟩ := Reference.Aux.represents_some hQ
      simp_all [AndBitSpec, Gated4Spec,
        Reference.circuitXCoordinate, Reference.slopeAddCoordinates,
        Reference.coordinates,
        AffineSlope.ofElem, Modular.Lazy.evalZMod,
        Modular.Lazy.evalElemZMod]
  · obtain ⟨hpinf, hpx, hpy⟩ := Reference.Aux.represents_some hP
    rcases q with _ | ⟨qx, qy, hqcurve⟩
    · have hqinf := Reference.Aux.represents_zero hQ
      simp_all [AndBitSpec, Gated4Spec,
        Reference.circuitXCoordinate, Reference.slopeAddCoordinates,
        Reference.coordinates,
        AffineSlope.ofElem, Modular.Lazy.evalZMod,
        Modular.Lazy.evalElemZMod]
    · obtain ⟨hqinf, hqx, hqy⟩ := Reference.Aux.represents_some hQ
      have hdx : Modular.Lazy.evalZMod base (AffineSlope.sub Q.X P.X) ρ =
          qx - px := by simp [hqx, hpx, AffineSlope.sub]
      have hysum : Modular.Lazy.evalZMod base (AffineSlope.add P.Y Q.Y) ρ =
          py + qy := by simp [hpy, hqy, AffineSlope.add]
      unfold Modular.Lazy.ZeroTestZModSpec at hsame hopposite
      rw [hdx] at hsame
      rw [hysum] at hopposite
      by_cases hx : px = qx
      · by_cases hy : py = Reference.curve.toAffine.negY qx qy
        · simp_all [AndBitSpec, Gated4Spec,
            Modular.Lazy.ZeroTestZModSpec, Reference.circuitXCoordinate,
            Reference.slopeAddCoordinates, WeierstrassCurve.Affine.negY,
            Reference.curve, AffineSlope.ofElem, Modular.Lazy.evalZMod]
        · have hpyqy : py = qy :=
            WeierstrassCurve.Affine.Y_eq_of_Y_ne
              hpcurve.1 hqcurve.1 hx hy
          have hsumne : py + qy ≠ 0 := by
            intro hzero
            apply hy
            simp only [WeierstrassCurve.Affine.negY, Reference.curve,
              zero_mul]
            linear_combination hzero
          have hden : 2 * py ≠ 0 := by
            intro hzero
            apply hy
            simp only [WeierstrassCurve.Affine.negY, Reference.curve,
              zero_mul]
            rw [← hpyqy]
            linear_combination hzero
          have hsame1 : control.sameX.eval ρ.int = 1 := by
            rw [hsame.2.2]
            simp [hx]
          have hopposite0 : control.oppositeY.eval ρ.int = 0 := by
            rw [hopposite.2.2]
            simp [hsumne]
          have hfinite1 : control.finite.eval ρ.int = 1 := by
            rw [hfinite.1]
            simp [hpinf, hqinf]
          have hdoubleKind1 : doubleKind.eval ρ.int = 1 := by
            rw [hdoubleKind.1]
            simp [hsame1, hopposite0]
          have hdouble : control.doubleCase.eval ρ.int = 1 := by
            rw [hdoubleCase.1, hfinite1, hdoubleKind1]
            norm_num
          have hgeneric0 : genericCase.eval ρ.int = 0 := by
            rw [hgenericCase.1]
            simp [hfinite1, hsame1]
          have hac : control.active.eval ρ.int = 1 := by
            rw [hactive, hdouble, hgeneric0]
            norm_num
          rcases hcandidate hac with ⟨slope, hslope, hcandidateX⟩
          rw [if_pos hdouble] at hslope
          have hslopeEq : Modular.Lazy.evalZMod base slope ρ =
              (3 * qx ^ 2 - 3) / (2 * py) := by
            rw [hpx, hpy, hx] at hslope
            exact (eq_div_iff hden).2 (by simpa [pow_two] using hslope)
          have houtX := hX.1 hac
          have houtInf : out.infinity.eval ρ.int = 0 := by
            have hboth0 : bothInfinity.eval ρ.int = 0 := by
              rw [hbothInfinity.1]
              simp [hpinf, hqinf]
            have hoppositePair0 : oppositePair.eval ρ.int = 0 := by
              rw [hoppositePair.1, hsame1, hopposite0]
              norm_num
            have hfiniteOpposite0 : finiteOpposite.eval ρ.int = 0 := by
              rw [hfiniteOpposite.1, hfinite1, hoppositePair0]
              norm_num
            omega
          constructor
          · exact Or.inl houtInf
          · unfold Reference.circuitXCoordinate
            rw [if_neg (by omega)]
            simp only [Reference.slopeAddCoordinates, if_pos hx, if_neg hy]
            congr 1
            rw [houtX, hcandidateX, hslopeEq, hpx, hqx, hx]
            simp only [Reference.tangentSlope, Reference.resultX]
            ring
      · have hden : qx - px ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
        have hsame0 : control.sameX.eval ρ.int = 0 := by
          rw [hsame.2.2]
          simp [sub_ne_zero.mpr (Ne.symm hx)]
        have hfinite1 : control.finite.eval ρ.int = 1 := by
          rw [hfinite.1]
          simp [hpinf, hqinf]
        have hdoubleKind0 : doubleKind.eval ρ.int = 0 := by
          rw [hdoubleKind.1, hsame0]
          norm_num
        have hdouble : control.doubleCase.eval ρ.int = 0 := by
          rw [hdoubleCase.1, hfinite1, hdoubleKind0]
          norm_num
        have hgeneric1 : genericCase.eval ρ.int = 1 := by
          rw [hgenericCase.1]
          simp [hfinite1, hsame0]
        have hac : control.active.eval ρ.int = 1 := by
          rw [hactive, hdouble, hgeneric1]
          norm_num
        rcases hcandidate hac with ⟨slope, hslope, hcandidateX⟩
        rw [if_neg (by omega)] at hslope
        have hslopeEq : Modular.Lazy.evalZMod base slope ρ =
            (qy - py) / (qx - px) := (eq_div_iff hden).2 (by
          rw [hpx, hpy, hqx, hqy] at hslope
          exact hslope)
        have houtX := hX.1 hac
        have houtInf : out.infinity.eval ρ.int = 0 := by
          have hboth0 : bothInfinity.eval ρ.int = 0 := by
            rw [hbothInfinity.1]
            simp [hpinf, hqinf]
          have hoppositePair0 : oppositePair.eval ρ.int = 0 := by
            rw [hoppositePair.1, hsame0]
            norm_num
          have hfiniteOpposite0 : finiteOpposite.eval ρ.int = 0 := by
            rw [hfiniteOpposite.1, hfinite1, hoppositePair0]
            norm_num
          omega
        constructor
        · exact Or.inl houtInf
        · unfold Reference.circuitXCoordinate
          rw [if_neg (by omega)]
          simp only [Reference.slopeAddCoordinates, if_neg hx]
          congr 1
          rw [houtX, hcandidateX, hslopeEq, hpx, hqx]
          simp only [Reference.chordSlope, Reference.resultX]
          ring

theorem add_specs_x_normalized {P Q : AffineSlope.Point}
    {out : AffineSlope.XPoint} {p q : Reference.Point}
    (hP : Reference.NormalizedRep ρ P p)
    (hQ : Reference.NormalizedRep ρ Q q)
    {control : AffineSlope.AddControl} {candidateX : AffineSlope.Rep}
    (hcontrol : AddControlSpec ρ P Q control)
    (hcandidate : AddCandidateXSpec ρ P Q control candidateX)
    (hout : SelectAddXOutputSpec ρ P Q control candidateX out) :
    Reference.NormalizedXRep ρ out (p + q) := by
  have hraw := add_specs_x_raw hP.1 hQ.1 hcontrol hcandidate hout
  constructor
  · exact ⟨hraw.1, hraw.2.trans (Reference.xCoordinate_slopeAdd p q)⟩
  · intro hsum
    rcases hcontrol with
      ⟨hsame, hopposite, hfinite, doubleKind, genericCase,
        hdoubleKind, hdoubleCase, hgenericCase, hactive⟩
    rcases hout with
      ⟨bothInfinity, oppositePair, finiteOpposite, hX,
        hbothInfinity, hoppositePair, hfiniteOpposite, houtInfinity⟩
    rcases p with _ | ⟨px, py, hpcurve⟩
    · have hpinf := Reference.Aux.represents_zero hP.1
      have hpcoords := hP.2 rfl
      rcases q with _ | ⟨qx, qy, hqcurve⟩
      · have hqinf := Reference.Aux.represents_zero hQ.1
        have hqcoords := hQ.2 rfl
        simp_all [AddControlSpec, SelectAddXOutputSpec,
          AndBitSpec, Gated4Spec,
          Modular.Lazy.ZeroTestZModSpec, AffineSlope.add,
          AffineSlope.sub, AffineSlope.ofElem]
      · change (WeierstrassCurve.Affine.Point.some qx qy hqcurve :
          Reference.Point) = 0 at hsum
        contradiction
    · rcases q with _ | ⟨qx, qy, hqcurve⟩
      · change (WeierstrassCurve.Affine.Point.some px py hpcurve :
          Reference.Point) = 0 at hsum
        contradiction
      · obtain ⟨hpinf, hpx, hpy⟩ := Reference.Aux.represents_some hP.1
        obtain ⟨hqinf, hqx, hqy⟩ := Reference.Aux.represents_some hQ.1
        have hneg :
            (WeierstrassCurve.Affine.Point.some px py hpcurve :
              Reference.Point) =
              -(.some qx qy hqcurve) :=
          eq_neg_iff_add_eq_zero.mpr hsum
        have hxy : px = qx ∧
            py = Reference.curve.toAffine.negY qx qy := by
          simpa only [WeierstrassCurve.Affine.Point.neg_some,
            WeierstrassCurve.Affine.Point.some.injEq] using hneg
        simp_all [AddControlSpec, SelectAddXOutputSpec,
          AndBitSpec, Gated4Spec,
          Modular.Lazy.ZeroTestZModSpec, AffineSlope.add,
          AffineSlope.sub, AffineSlope.ofElem,
          WeierstrassCurve.Affine.negY, Reference.curve]

end AffineSlope.Aux

open AffineSlope

theorem addCompleteCollapsedX_sound_mathlib {P Q : Point}
    {p q : Reference.Point}
    (hP : Reference.Represents ρ P p)
    (hQ : Reference.Represents ρ Q q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (addCompleteCollapsedX P Q)
    ⦃⇓ out => ⌜Reference.XRepresents ρ out (p + q)⌝⦄ := by
  mvcgen [addCompleteCollapsedX]
  rename_i control hcontrol candidateX hcandidate out
  intro hout
  have hraw := Aux.add_specs_x_raw hP hQ hcontrol hcandidate hout
  exact ⟨hraw.1, hraw.2.trans (Reference.xCoordinate_slopeAdd p q)⟩

@[spec] theorem addCompleteCollapsedX_sound_normalized {P Q : Point}
    {p q : Reference.Point}
    (hP : Reference.NormalizedRep ρ P p)
    (hQ : Reference.NormalizedRep ρ Q q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (addCompleteCollapsedX P Q)
    ⦃⇓ out => ⌜Reference.NormalizedXRep ρ out (p + q)⌝⦄ := by
  mvcgen [addCompleteCollapsedX]
  rename_i control hcontrol candidateX hcandidate out
  intro hout
  exact Aux.add_specs_x_normalized hP hQ hcontrol hcandidate hout

@[spec] theorem addCompleteCollapsedX_complete_mathlib {P Q : Point}
    {q p : Reference.Point}
    (hPvalid : P.Valid ρ) (hQvalid : Q.Valid ρ)
    (hP : Reference.NormalizedRep ρ P p)
    (hQ : Reference.NormalizedRep ρ Q q)
    (hnoTwoTorsion : p = 0 ∨ p + p ≠ 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (addCompleteCollapsedX P Q)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      Reference.NormalizedXRep ρ out (p + q)⌝⦄ := by
  mvcgen [addCompleteCollapsedX]
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
      Aux.add_specs_x_normalized hP hQ hcontrol hcandidate.2.2.2 houtSpec⟩
  all_goals aesop

end Freigen.F2Z.Examples.P256
