import Freigen.F2Z.Examples.Modular
import Freigen.F2Z.Examples.P256.Reference

/-!
# Auxiliary lemmas for P-256 correctness

Supporting validity, evaluation, and relational facts used by the public
soundness, completeness, and well-formedness proofs.
-/

namespace Freigen.F2Z.Examples.P256

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open Std.Do
open scoped Std.Do

namespace Reference.Aux

theorem ofElems_represents_pointOfCircuit {x y : Fp}
    (hcurve : Projective.Lazy.OnCurveZModSpec ρ x y) :
    Reference.Represents ρ (AffineSlope.ofElems x y)
      (Reference.pointOfCircuit ρ x y hcurve) := by
  simp [Reference.Represents, Reference.circuitCoordinates,
    Reference.coordinates, Reference.pointOfCircuit, AffineSlope.ofElems,
    WeierstrassCurve.Affine.Point.mk, Modular.Lazy.evalZMod,
    Modular.Lazy.ofElem]

end Reference.Aux
open Modular

theorem scalar_modulus_eq : scalar.modulus = scalarModulus := rfl

@[simp] theorem evalZMod_mk (x : LC ℤ) (bound : Nat) {ρ : WF.Valuation} :
    Modular.Lazy.evalZMod base { intVal := x, bound := bound } ρ =
      Int.castRingHom (ZMod base.modulus) (x.eval ρ.int) := rfl

@[simp] theorem three_evalElemZMod {ρ : WF.Valuation} :
    Modular.Lazy.evalElemZMod base three ρ = 3 := by
  have hvalid : three.Valid ρ := by
    exact Modular.ofNat_valid base 3 (by native_decide) (by native_decide)
  unfold Modular.Lazy.evalElemZMod
  rw [← Modular.Elem.evalNat_cast (p := base) hvalid]
  rw [show three.evalNat ρ = 3 by
    exact Modular.ofNat_evalNat base 3 (by native_decide) (by native_decide)]
  norm_num

@[simp] theorem one_evalElemZMod {ρ : WF.Valuation} :
    Modular.Lazy.evalElemZMod base one ρ = 1 := by
  have hvalid : one.Valid ρ := by
    exact Modular.ofNat_valid base 1 (by native_decide) (by native_decide)
  unfold Modular.Lazy.evalElemZMod
  rw [← Modular.Elem.evalNat_cast (p := base) hvalid]
  rw [show one.evalNat ρ = 1 by
    exact Modular.ofNat_evalNat base 1 (by native_decide) (by native_decide)]
  norm_num

@[simp] theorem zero_evalElemZMod {ρ : WF.Valuation} :
    Modular.Lazy.evalElemZMod base zero ρ = 0 := by
  have hvalid : zero.Valid ρ := by
    exact Modular.ofNat_valid base 0 (by native_decide) (by native_decide)
  unfold Modular.Lazy.evalElemZMod
  rw [← Modular.Elem.evalNat_cast (p := base) hvalid]
  rw [show zero.evalNat ρ = 0 by
    exact Modular.ofNat_evalNat base 0 (by native_decide) (by native_decide)]
  norm_num

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

def DoubleSlopeSpec (ρ : WF.Valuation) (P : AffineSlope.Point)
    (slope : AffineSlope.Rep) : Prop :=
  Modular.Lazy.evalZMod base slope ρ *
      (2 * Modular.Lazy.evalZMod base P.Y ρ +
        Int.castRingHom (ZMod base.modulus) (P.infinity.eval ρ.int)) =
    3 * (Modular.Lazy.evalZMod base P.X ρ *
      Modular.Lazy.evalZMod base P.X ρ) - 3 +
        3 * Int.castRingHom (ZMod base.modulus) (P.infinity.eval ρ.int)

def FinishDoubleSpec (ρ : WF.Valuation) (P : AffineSlope.Point)
    (slope : AffineSlope.Rep) (out : AffineSlope.Point) : Prop :=
  Modular.Lazy.evalZMod base out.X ρ =
      Modular.Lazy.evalZMod base slope ρ *
        Modular.Lazy.evalZMod base slope ρ -
          2 * Modular.Lazy.evalZMod base P.X ρ ∧
    Modular.Lazy.evalZMod base out.Y ρ =
      Modular.Lazy.evalZMod base slope ρ *
        (Modular.Lazy.evalZMod base P.X ρ -
          Modular.Lazy.evalZMod base out.X ρ) -
        Modular.Lazy.evalZMod base P.Y ρ ∧
    out.infinity = P.infinity

@[spec] theorem doubleSquare_sound {P : AffineSlope.Point} :
    ⦃⌜True⌝⦄ Sound.interp ρ (AffineSlope.doubleSquare P)
    ⦃⇓ x2 => ⌜Modular.Lazy.MulZModSpec base ρ P.X P.X x2⌝⦄ := by
  mvcgen [AffineSlope.doubleSquare, AffineSlope.doubleSquareHint,
    AffineSlope.doubleSquareDecodeR, AffineSlope.doubleSquareDecodeQ,
    AffineSlope.doubleSquareCheck, Modular.Lazy.MulZModSpec,
    Modular.Lazy.evalZMod]
  intro bits
  mvcgen
  rename_i r q hr hq heq
  have hcast := congrArg (fun z : Int => (z : ZMod base.modulus)) heq
  simp only [LC.eval_add, LC.eval_nsmul, nsmul_eq_mul, Int.cast_mul,
    Int.cast_add, Int.cast_natCast, ZMod.natCast_self, zero_mul,
    add_zero] at hcast
  exact hcast.symm

@[spec] theorem doubleSlopeFromSquare_sound {P : AffineSlope.Point}
    {x2 : AffineSlope.Rep} :
    ⦃⌜True⌝⦄ Sound.interp ρ (AffineSlope.doubleSlopeFromSquare P x2)
    ⦃⇓ slope => ⌜Modular.Lazy.DivideZModSpec base ρ
      (AffineSlope.add (AffineSlope.scale 2 P.Y) ⟨P.infinity, 1⟩)
      (AffineSlope.add
        (AffineSlope.sub (AffineSlope.scale 3 x2)
          (AffineSlope.ofElem three)) ⟨3 • P.infinity, 1⟩)
      slope⌝⦄ := by
  mvcgen [AffineSlope.doubleSlopeFromSquare,
    AffineSlope.doubleSlopeNumerator, AffineSlope.doubleSlopeDenominator,
    AffineSlope.doubleSlopeHint, AffineSlope.doubleSlopeDecodeValue,
    AffineSlope.doubleSlopeDecodeQ, AffineSlope.doubleSlopeCheck,
    Modular.Lazy.DivideZModSpec, Modular.Lazy.evalZMod]
  intro bits
  mvcgen
  rename_i value q hvalue hq heq
  have hcast := congrArg (fun z : Int => (z : ZMod base.modulus)) heq.2
  simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul, LC.eval_ofConst,
    nsmul_eq_mul, Int.cast_mul, Int.cast_add, Int.cast_sub,
    Int.cast_natCast, Nat.cast_mul, ZMod.natCast_self, mul_zero,
    zero_mul, add_zero, sub_zero] at hcast
  exact hcast

@[spec] theorem finishDoubleX_sound {P : AffineSlope.Point}
    {slope : AffineSlope.Rep} :
    ⦃⌜True⌝⦄ Sound.interp ρ (AffineSlope.finishDoubleX P slope)
    ⦃⇓ x3 => ⌜Modular.Lazy.MulSubToElemZModSpec base ρ slope slope
      (AffineSlope.scale 2 P.X) x3⌝⦄ := by
  mvcgen [AffineSlope.finishDoubleX, AffineSlope.finishDoubleXTarget,
    AffineSlope.finishDoubleXHint, AffineSlope.finishDoubleXDecodeR,
    AffineSlope.finishDoubleXDecodeQ, AffineSlope.finishDoubleXCheck,
    Modular.Lazy.MulSubToElemZModSpec, Modular.Lazy.evalZMod,
    Modular.Lazy.evalElemZMod]
  intro bits
  mvcgen
  rename_i r q hr hq heq
  have hcast := congrArg (fun z : Int => (z : ZMod base.modulus)) heq.2
  simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul, LC.eval_ofConst,
    nsmul_eq_mul, Int.cast_mul, Int.cast_add, Int.cast_sub,
    Int.cast_natCast, Nat.cast_mul, ZMod.natCast_self, mul_zero,
    zero_mul, add_zero, sub_zero] at hcast
  exact (eq_sub_iff_add_eq).2 hcast.symm

@[spec] theorem finishDoubleY_sound {P : AffineSlope.Point}
    {slope : AffineSlope.Rep} {x3 : Fp} :
    ⦃⌜True⌝⦄ Sound.interp ρ (AffineSlope.finishDoubleY P slope x3)
    ⦃⇓ y3 => ⌜Modular.Lazy.MulSubToElemZModSpec base ρ slope
      (AffineSlope.sub P.X (AffineSlope.ofElem x3)) P.Y y3⌝⦄ := by
  mvcgen [AffineSlope.finishDoubleY, AffineSlope.finishDoubleYFactor,
    AffineSlope.finishDoubleYHint, AffineSlope.finishDoubleYDecodeR,
    AffineSlope.finishDoubleYDecodeQ, AffineSlope.finishDoubleYCheck,
    Modular.Lazy.MulSubToElemZModSpec, Modular.Lazy.evalZMod,
    Modular.Lazy.evalElemZMod]
  intro bits
  mvcgen
  rename_i r q hr hq heq
  have hcast := congrArg (fun z : Int => (z : ZMod base.modulus)) heq.2
  simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul, LC.eval_ofConst,
    nsmul_eq_mul, Int.cast_mul, Int.cast_add, Int.cast_sub,
    Int.cast_natCast, Nat.cast_mul, ZMod.natCast_self, mul_zero,
    zero_mul, add_zero, sub_zero] at hcast
  exact (eq_sub_iff_add_eq).2 hcast.symm

@[spec] theorem collapsedSlope_sound
    {operands : AffineSlope.SlopeOperands} :
    ⦃⌜True⌝⦄ Sound.interp ρ (AffineSlope.collapsedSlope operands)
    ⦃⇓ slope => ⌜Modular.Lazy.DivideZModSpec base ρ
      operands.denominator operands.numerator slope⌝⦄ := by
  mvcgen [AffineSlope.collapsedSlope, AffineSlope.collapsedSlopeHint,
    AffineSlope.collapsedSlopeDecodeValue,
    AffineSlope.collapsedSlopeDecodeQ,
    AffineSlope.collapsedSlopeCheck,
    Modular.Lazy.DivideZModSpec, Modular.Lazy.evalZMod]
  intro bits
  mvcgen
  rename_i value q hvalue hq heq
  have hcast := congrArg (fun z : Int => (z : ZMod base.modulus)) heq
  simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul, LC.eval_ofConst,
    nsmul_eq_mul, Int.cast_mul, Int.cast_add, Int.cast_sub,
    Int.cast_natCast, Nat.cast_mul, ZMod.natCast_self, mul_zero,
    zero_mul, add_zero, sub_zero] at hcast
  exact hcast

@[spec] theorem collapsedCandidateX_sound {P Q : AffineSlope.Point}
    {slope : AffineSlope.Rep} :
    ⦃⌜True⌝⦄ Sound.interp ρ (AffineSlope.collapsedCandidateX P Q slope)
    ⦃⇓ x3 => ⌜Modular.Lazy.MulSubToElemZModSpec base ρ slope slope
      (AffineSlope.collapsedCandidateXTarget P Q) x3⌝⦄ := by
  mvcgen [AffineSlope.collapsedCandidateX,
    AffineSlope.collapsedCandidateXTarget,
    AffineSlope.collapsedCandidateXHint,
    AffineSlope.collapsedCandidateXDecodeR,
    AffineSlope.collapsedCandidateXDecodeQ,
    AffineSlope.collapsedCandidateXCheck,
    Modular.Lazy.MulSubToElemZModSpec, Modular.Lazy.evalZMod,
    Modular.Lazy.evalElemZMod]
  intro bits
  mvcgen
  rename_i r q hr hq heq
  have hcast := congrArg (fun z : Int => (z : ZMod base.modulus)) heq.2
  simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul, LC.eval_ofConst,
    nsmul_eq_mul, Int.cast_mul, Int.cast_add, Int.cast_sub,
    Int.cast_natCast, Nat.cast_mul, ZMod.natCast_self, mul_zero,
    zero_mul, add_zero, sub_zero] at hcast
  exact (eq_sub_iff_add_eq).2 hcast.symm

@[spec] theorem collapsedCandidateY_sound {P : AffineSlope.Point}
    {slope : AffineSlope.Rep} {x3 : Fp} :
    ⦃⌜True⌝⦄ Sound.interp ρ (AffineSlope.collapsedCandidateY P slope x3)
    ⦃⇓ y3 => ⌜Modular.Lazy.MulSubToElemZModSpec base ρ slope
      (AffineSlope.collapsedCandidateYFactor P x3) P.Y y3⌝⦄ := by
  mvcgen [AffineSlope.collapsedCandidateY,
    AffineSlope.collapsedCandidateYFactor,
    AffineSlope.collapsedCandidateYHint,
    AffineSlope.collapsedCandidateYDecodeR,
    AffineSlope.collapsedCandidateYDecodeQ,
    AffineSlope.collapsedCandidateYCheck,
    Modular.Lazy.MulSubToElemZModSpec, Modular.Lazy.evalZMod,
    Modular.Lazy.evalElemZMod]
  intro bits
  mvcgen
  rename_i r q hr hq heq
  have hcast := congrArg (fun z : Int => (z : ZMod base.modulus)) heq.2
  simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul, LC.eval_ofConst,
    nsmul_eq_mul, Int.cast_mul, Int.cast_add, Int.cast_sub,
    Int.cast_natCast, Nat.cast_mul, ZMod.natCast_self, mul_zero,
    zero_mul, add_zero, sub_zero] at hcast
  exact (eq_sub_iff_add_eq).2 hcast.symm

@[spec] theorem doubleSquare_complete {P : AffineSlope.Point}
    (hP : P.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (AffineSlope.doubleSquare P)
    ⦃⇓ x2 => ⌜x2.Valid ρ ∧ x2.bound = 2 ∧
      x2.intVal.eval ρ.int < base.modulus ∧
      Modular.Lazy.MulZModSpec base ρ P.X P.X x2⌝⦄ := by
  rcases hP with ⟨hPXbound, hPX, hPXcanonical, _, _, _, _⟩
  mvcgen [AffineSlope.doubleSquare, AffineSlope.doubleSquareHint,
    AffineSlope.doubleSquareDecodeR, AffineSlope.doubleSquareDecodeQ,
    AffineSlope.doubleSquareCheck]
  let a := P.X.intVal.eval ρ.int
  let value := a.toNat * a.toNat
  let bits := Modular.Aux.quotientBits 512 256
    (value % base.modulus) (value / base.modulus)
  refine ⟨bits, ?_, ?_⟩
  · simp [WF.interpHint, WF.evalArgs, hPX.1, bits,
      Modular.Aux.quotientBits, value, a]
  · mvcgen
    rename_i r hr q hq
    have hrFit : value % base.modulus < 2 ^ 256 :=
      (Nat.mod_lt _ base.positive).trans_le base.fits
    have haVal : (a.toNat : Int) = a := Int.toNat_of_nonneg hPX.1
    have haLt : a.toNat < base.modulus :=
      (Int.toNat_lt hPX.1).2 hPXcanonical
    have hvalueLt : value < base.modulus * base.modulus := by
      dsimp [value]
      nlinarith
    have hqSmall : value / base.modulus < base.modulus :=
      (Nat.div_lt_iff_lt_mul base.positive).2 (by
        simpa [Nat.mul_comm] using hvalueLt)
    have hqFit : value / base.modulus < 2 ^ 256 :=
      hqSmall.trans_le base.fits
    have hrWord := Modular.Aux.quotientBits_low
      (totalWidth := 512) (n := 256)
      (low := value % base.modulus) (high := value / base.modulus)
      (by omega) hrFit ρ
    have hqWord := Modular.Aux.quotientBits_high
      (totalWidth := 512) (n := 256) (quotientWidth := 256)
      (low := value % base.modulus) (high := value / base.modulus)
      (by omega) hqFit ρ
    have hrVal : r.intVal.eval ρ.int = (value % base.modulus : Nat) := by
      rw [U.Rel.intVal hr, hrWord]
    have hqVal : q.intVal.eval ρ.int = (value / base.modulus : Nat) := by
      rw [U.Rel.intVal hq, hqWord]
    constructor
    · simp only [LC.eval_add, LC.eval_nsmul, nsmul_eq_mul,
        hrVal, hqVal, value, a]
      change a * a = _
      rw [← haVal]
      exact_mod_cast (Nat.mod_add_div value base.modulus).symm
    · mvcgen
      refine ⟨?_, True.intro, ?_, ?_⟩
      · exact ⟨U.intVal_nonneg r hr.1, by
          rw [hrVal]
          have hmod := Nat.mod_lt value base.positive
          push_cast
          nlinarith [base.positive]⟩
      · rw [hrVal]
        exact_mod_cast Nat.mod_lt value base.positive
      · unfold Modular.Lazy.MulZModSpec Modular.Lazy.evalZMod
        have heq : a * a =
            (value % base.modulus : Nat) +
              base.modulus * (value / base.modulus) := by
          rw [← haVal]
          exact_mod_cast (Nat.mod_add_div value base.modulus).symm
        have hcast := congrArg (fun z : Int => (z : ZMod base.modulus)) heq
        simpa [hrVal, value, a] using hcast.symm

@[spec] theorem doubleSlopeFromSquare_complete {P : AffineSlope.Point}
    {x2 : AffineSlope.Rep}
    (hP : P.Valid ρ) (hx2 : x2.Valid ρ) (hx2Bound : x2.bound = 2)
    (hx2Canonical : x2.intVal.eval ρ.int < base.modulus)
    (hden : Modular.Lazy.evalZMod base
      (AffineSlope.doubleSlopeDenominator P) ρ ≠ 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.doubleSlopeFromSquare P x2)
    ⦃⇓ slope => ⌜slope.Valid ρ ∧ slope.bound = 2 ∧
      slope.intVal.eval ρ.int < base.modulus ∧
      Modular.Lazy.DivideZModSpec base ρ
        (AffineSlope.doubleSlopeDenominator P)
        (AffineSlope.doubleSlopeNumerator P x2) slope⌝⦄ := by
  rcases hP with
    ⟨_, _, _, hPYbound, hPY, hPYcanonical, hPinf⟩
  let numerator := AffineSlope.doubleSlopeNumerator P x2
  let denominator := AffineSlope.doubleSlopeDenominator P
  have hthree : (AffineSlope.ofElem three).Valid ρ :=
    Modular.Lazy.ofElem_valid base
      (Modular.ofNat_valid base 3 (by decide) (by decide))
  have hinfinityNum :
      ({ intVal := 3 • P.infinity, bound := 1 } : AffineSlope.Rep).Valid ρ := by
    rcases hPinf with h | h <;>
      simp [Modular.Lazy.Rep.Valid, h, base, baseModulus] <;> norm_num
  have hinfinityDen :
      ({ intVal := P.infinity, bound := 1 } : AffineSlope.Rep).Valid ρ := by
    rcases hPinf with h | h <;>
      simp [Modular.Lazy.Rep.Valid, h, base, baseModulus] <;> norm_num
  have hnumerator : numerator.Valid ρ := by
    dsimp [numerator, AffineSlope.doubleSlopeNumerator]
    exact Modular.Lazy.add_valid base
      (Modular.Lazy.sub_valid base
        (Modular.Lazy.scale_valid base hx2 (by omega)) hthree)
      hinfinityNum
  have hdenominator : denominator.Valid ρ := by
    dsimp [denominator, AffineSlope.doubleSlopeDenominator]
    exact Modular.Lazy.add_valid base
      (Modular.Lazy.scale_valid base hPY (by omega)) hinfinityDen
  have hnumeratorBound : numerator.bound = 9 := by
    simp [numerator, AffineSlope.doubleSlopeNumerator, AffineSlope.add,
      AffineSlope.sub, AffineSlope.scale, AffineSlope.ofElem,
      Modular.Lazy.add, Modular.Lazy.sub, Modular.Lazy.scale,
      Modular.Lazy.ofElem, hx2Bound]
  mvcgen [AffineSlope.doubleSlopeFromSquare,
    AffineSlope.doubleSlopeNumerator, AffineSlope.doubleSlopeDenominator,
    AffineSlope.doubleSlopeHint, AffineSlope.doubleSlopeDecodeValue,
    AffineSlope.doubleSlopeDecodeQ, AffineSlope.doubleSlopeCheck]
  let a := denominator.intVal.eval ρ.int
  let b := numerator.intVal.eval ρ.int
  have haNat : (a.toNat : Int) = a := Int.toNat_of_nonneg hdenominator.1
  have hbNat : (b.toNat : Int) = b := Int.toNat_of_nonneg hnumerator.1
  let d := a.toNat % base.modulus
  have hdlt : d < base.modulus := Nat.mod_lt _ base.positive
  have haZ : (a : ZMod base.modulus) = (a.toNat : ZMod base.modulus) := by
    rw [← Int.cast_natCast]
    exact congrArg (Int.castRingHom (ZMod base.modulus)) haNat.symm
  have hd : d ≠ 0 := by
    intro hd0
    apply hden
    unfold Modular.Lazy.evalZMod
    change (a : ZMod base.modulus) = 0
    rw [haZ]
    rw [show (a.toNat : ZMod base.modulus) =
      (d : ZMod base.modulus) by simp [d], hd0]
    simp
  have hgcd : Nat.gcd d base.modulus = 1 := by
    rw [Nat.gcd_comm]
    exact (Nat.coprime_of_lt_prime hd hdlt Fact.out).gcd_eq_one
  let inverse := ((Nat.gcdA d base.modulus) %
    (base.modulus : Int)).toNat
  let value := (inverse * (b.toNat % base.modulus)) % base.modulus
  have hinverse : (inverse : ZMod base.modulus) *
      (d : ZMod base.modulus) = 1 := by
    have hp0 : (base.modulus : Int) ≠ 0 := by
      exact_mod_cast base.positive.ne'
    have hinverseInt : (inverse : Int) =
        Nat.gcdA d base.modulus % (base.modulus : Int) := by
      exact Int.toNat_of_nonneg (Int.emod_nonneg _ hp0)
    have hinverseCast : (inverse : ZMod base.modulus) =
        (Nat.gcdA d base.modulus : ZMod base.modulus) := by
      rw [← Int.cast_natCast, hinverseInt]
      simp
    rw [hinverseCast]
    have hbezout := Nat.gcd_eq_gcd_ab d base.modulus
    have hcast := congrArg (Int.castRingHom (ZMod base.modulus)) hbezout
    simpa [hgcd, mul_comm] using hcast.symm
  have hbZ : (b.toNat : ZMod base.modulus) = (b : ZMod base.modulus) := by
    rw [← Int.cast_natCast]
    exact congrArg (Int.castRingHom (ZMod base.modulus)) hbNat
  have hvalueZ : (value : ZMod base.modulus) *
      (a : ZMod base.modulus) = (b : ZMod base.modulus) := by
    rw [haZ]
    have hvalueCast : (value : ZMod base.modulus) =
        (inverse : ZMod base.modulus) * (b.toNat : ZMod base.modulus) := by
      simp [value]
    have haMod : (a.toNat : ZMod base.modulus) =
        (d : ZMod base.modulus) := by simp [d]
    rw [hvalueCast, haMod]
    calc
      (inverse : ZMod base.modulus) * (b.toNat : ZMod base.modulus) * d =
          (inverse * d) * (b.toNat : ZMod base.modulus) := by ring
      _ = (b.toNat : ZMod base.modulus) := by rw [hinverse]; simp
      _ = (b : ZMod base.modulus) := hbZ
  let shifted : Int := (value : Int) * a +
    (numerator.bound * base.modulus : Nat) - b
  have hshifted : 0 ≤ shifted := by
    have hva : 0 ≤ (value : Int) * a :=
      mul_nonneg (by positivity) hdenominator.1
    have hbUpper : b < (numerator.bound * base.modulus : Nat) :=
      hnumerator.2
    dsimp [shifted]
    omega
  have hshiftCond : b ≤ (value : Int) * a +
      (numerator.bound * base.modulus : Nat) := by
    change 0 ≤ (value : Int) * a +
      (numerator.bound * base.modulus : Nat) - b at hshifted
    omega
  have hshiftDvd : (base.modulus : Int) ∣ shifted := by
    have hmod : (((value : Int) * a : Int) : ZMod base.modulus) =
        (b : ZMod base.modulus) := by simpa using hvalueZ
    have hdvdDiff : (base.modulus : Int) ∣ b - (value : Int) * a :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hmod
    have hdvdNeg : (base.modulus : Int) ∣ (value : Int) * a - b := by
      simpa [neg_sub] using dvd_neg.mpr hdvdDiff
    dsimp [shifted]
    rcases hdvdNeg with ⟨k, hk⟩
    refine ⟨k + numerator.bound, ?_⟩
    push_cast
    calc
      (value : Int) * a + numerator.bound * base.modulus - b =
          ((value : Int) * a - b) + numerator.bound * base.modulus := by ring
      _ = base.modulus * k + numerator.bound * base.modulus := by rw [hk]
      _ = base.modulus * (k + numerator.bound) := by ring
  let bits := Modular.Aux.quotientBits 513 256 value
    (shifted.toNat / base.modulus)
  have hdenominatorNonnegRaw : 0 ≤
      (AffineSlope.doubleSlopeDenominator P).intVal.eval ρ.int := by
    simpa [denominator] using hdenominator.1
  have hnumeratorNonnegRaw : 0 ≤
      (AffineSlope.doubleSlopeNumerator P x2).intVal.eval ρ.int := by
    simpa [numerator] using hnumerator.1
  have hdenominatorEvalRaw :
      (AffineSlope.doubleSlopeDenominator P).intVal.eval ρ.int = a := by
    rfl
  have hnumeratorEvalRaw :
      (AffineSlope.doubleSlopeNumerator P x2).intVal.eval ρ.int = b := by
    rfl
  have hdenominatorEvalExpanded :
      (AffineSlope.add (AffineSlope.scale 2 P.Y)
        { intVal := P.infinity, bound := 1 }).intVal.eval ρ.int = a := by
    simpa only [AffineSlope.doubleSlopeDenominator] using hdenominatorEvalRaw
  have hnumeratorEvalExpanded :
      (AffineSlope.add
        (AffineSlope.sub (AffineSlope.scale 3 x2) (AffineSlope.ofElem three))
        { intVal := 3 • P.infinity, bound := 1 }).intVal.eval ρ.int = b := by
    simpa only [AffineSlope.doubleSlopeNumerator] using hnumeratorEvalRaw
  have hnumeratorBoundExpanded :
      (AffineSlope.add
        (AffineSlope.sub (AffineSlope.scale 3 x2) (AffineSlope.ofElem three))
        { intVal := 3 • P.infinity, bound := 1 }).bound = numerator.bound := by
    rfl
  have ha0 : 0 ≤ a := hdenominator.1
  have hb0 : 0 ≤ b := hnumerator.1
  have hinverseIntNonneg : 0 ≤
      Nat.gcdA d base.modulus % (base.modulus : Int) :=
    Int.emod_nonneg _ (by exact_mod_cast base.positive.ne')
  have hinverseIntEq :
      (Nat.gcdA d base.modulus % (base.modulus : Int)) = inverse := by
    exact (Int.toNat_of_nonneg hinverseIntNonneg).symm
  have hvalueInt :
      (Nat.gcdA d base.modulus % (base.modulus : Int)) * b %
          (base.modulus : Int) = value := by
    rw [hinverseIntEq, ← hbNat]
    push_cast
    rw [Int.mul_emod]
    simp [value, Nat.mul_mod]
  have hshiftCondInt : b ≤ (value : Int) * a +
      (numerator.bound : Int) * base.modulus := by
    simpa only [Nat.cast_mul] using hshiftCond
  refine ⟨bits, ?_, ?_⟩
  · simp only [WF.interpHint, WF.evalArgs]
    rw [hdenominatorEvalExpanded, hnumeratorEvalExpanded,
      hnumeratorBoundExpanded]
    simp [ha0, hb0, hd, hgcd, hinverseIntNonneg, hshifted, bits,
      Modular.Aux.quotientBits, value, inverse, shifted, d]
    rw [hvalueInt, if_pos hshiftCondInt]
    rfl
  · mvcgen
    rename_i r hr q hq
    have hvalueFit : value < 2 ^ 256 :=
      (Nat.mod_lt _ base.positive).trans_le base.fits
    have hshiftEq : (shifted.toNat : Int) = shifted :=
      Int.toNat_of_nonneg hshifted
    have haUpper : a < (2 * base.modulus : Nat) + 1 := by
      dsimp [a, denominator, AffineSlope.doubleSlopeDenominator]
      simp only [AffineSlope.add, AffineSlope.scale, Modular.Lazy.add,
        Modular.Lazy.scale, LC.eval_add, LC.eval_nsmul, nsmul_eq_mul]
      rcases hPinf with h | h <;> rw [h]
      all_goals push_cast
      all_goals nlinarith
    have hvaUpper : (value : Int) * a <
        (base.modulus : Int) * (2 * base.modulus + 1) := by
      have hv : (value : Int) < base.modulus := by
        exact_mod_cast Nat.mod_lt (inverse * (b.toNat % base.modulus))
          base.positive
      have haPos : 0 < (2 * base.modulus + 1 : Int) := by positivity
      exact (mul_le_mul_of_nonneg_left haUpper.le (by positivity)).trans_lt
        (mul_lt_mul_of_pos_right hv haPos)
    have hshiftUpper : shifted.toNat <
        (2 * base.modulus + 10) * base.modulus := by
      apply (Int.toNat_lt hshifted).2
      have hb0 : 0 ≤ b := hnumerator.1
      dsimp [shifted]
      rw [hnumeratorBound]
      push_cast at hvaUpper ⊢
      ring_nf at hvaUpper ⊢
      linarith
    have hqSmall : shifted.toNat / base.modulus <
        2 * base.modulus + 10 :=
      (Nat.div_lt_iff_lt_mul base.positive).2 (by
        simpa [Nat.mul_assoc] using hshiftUpper)
    have hqFit : shifted.toNat / base.modulus < 2 ^ 257 :=
      hqSmall.trans (by
        set_option exponentiation.threshold 300 in
          norm_num [base, baseModulus])
    have hrWord : (Word.eval ρ.bool {
        bitsLE := Vector.ofFn (n := 256) fun i =>
          (Vector.map LC.ofConst bits)[i.val]'(by omega) }).toNat = value := by
      simpa [Nat.mod_eq_of_lt hvalueFit] using
        (Modular.Aux.quotientBits_low (totalWidth := 513)
          (n := 256) (low := value) (high := shifted.toNat / base.modulus)
          (by omega) hvalueFit ρ)
    have hqWord := Modular.Aux.quotientBits_high
      (totalWidth := 513) (n := 256) (quotientWidth := 257)
      (low := value) (high := shifted.toNat / base.modulus)
      (by omega) hqFit ρ
    have hrVal : r.intVal.eval ρ.int = (value : Nat) := by
      rw [U.Rel.intVal hr, hrWord]
    have hqVal : q.intVal.eval ρ.int =
        (shifted.toNat / base.modulus : Nat) := by
      rw [U.Rel.intVal hq, hqWord]
    have hshiftDvdNat : base.modulus ∣ shifted.toNat := by
      rcases hshiftDvd with ⟨k, hk⟩
      refine ⟨k.toNat, ?_⟩
      have hk0 : 0 ≤ k := by
        have hp : (0 : Int) < base.modulus := by
          exact_mod_cast base.positive
        rw [hk] at hshifted
        nlinarith
      have hkNat : (k.toNat : Int) = k := Int.toNat_of_nonneg hk0
      apply Int.ofNat_inj.mp
      calc
        (shifted.toNat : Int) = shifted := hshiftEq
        _ = (base.modulus : Int) * k := hk
        _ = (base.modulus : Int) * (k.toNat : Int) := by rw [hkNat]
        _ = ((base.modulus * k.toNat : Nat) : Int) := by norm_num
    have hshiftDecomp : (shifted.toNat : Int) =
        (base.modulus : Int) *
          (shifted.toNat / base.modulus : Nat) := by
      have hnat := Nat.mod_add_div shifted.toNat base.modulus
      rw [Nat.mod_eq_zero_of_dvd hshiftDvdNat] at hnat
      simp only [zero_add] at hnat
      exact_mod_cast hnat.symm
    constructor
    · simp only [LC.eval_add, LC.eval_sub, LC.eval_nsmul,
        LC.eval_ofConst, nsmul_eq_mul, hrVal, hqVal]
      change (value : Int) * a = b +
        (base.modulus : Int) * (shifted.toNat / base.modulus : Nat) -
          (numerator.bound * base.modulus : Nat)
      calc
        (value : Int) * a =
            shifted - (numerator.bound * base.modulus : Nat) + b := by
          dsimp [shifted]
          ring
        _ = (shifted.toNat : Int) -
            (numerator.bound * base.modulus : Nat) + b := by rw [hshiftEq]
        _ = (base.modulus : Int) *
            (shifted.toNat / base.modulus : Nat) -
              (numerator.bound * base.modulus : Nat) + b := by
          rw [hshiftDecomp]
        _ = b + (base.modulus : Int) *
            (shifted.toNat / base.modulus : Nat) -
              (numerator.bound * base.modulus : Nat) := by ring
    · mvcgen
      refine ⟨?_, True.intro, ?_, ?_⟩
      · change 0 ≤ r.intVal.eval ρ.int ∧
          r.intVal.eval ρ.int < (2 * base.modulus : Nat)
        constructor
        · rw [hrVal]
          positivity
        · rw [hrVal]
          have hv : value < base.modulus := Nat.mod_lt _ base.positive
          push_cast
          omega
      · rw [hrVal]
        exact_mod_cast Nat.mod_lt (inverse * (b.toNat % base.modulus))
          base.positive
      · unfold Modular.Lazy.DivideZModSpec Modular.Lazy.evalZMod
        rw [hrVal]
        simpa [a, b, denominator, numerator] using hvalueZ

@[spec] theorem finishDoubleX_complete {P : AffineSlope.Point}
    {slope : AffineSlope.Rep}
    (hP : P.Valid ρ) (hslope : slope.Valid ρ)
    (hslopeBound : slope.bound = 2)
    (hslopeCanonical : slope.intVal.eval ρ.int < base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ (AffineSlope.finishDoubleX P slope)
    ⦃⇓ x3 => ⌜x3.Valid ρ ∧
      Modular.Lazy.MulSubToElemZModSpec base ρ slope slope
        (AffineSlope.finishDoubleXTarget P) x3⌝⦄ := by
  rcases hP with ⟨hPXbound, hPX, hPXcanonical, _, _, _, _⟩
  let target := AffineSlope.finishDoubleXTarget P
  have htarget : target.Valid ρ := by
    dsimp [target, AffineSlope.finishDoubleXTarget]
    exact Modular.Lazy.scale_valid base hPX (by omega)
  have htargetBound : target.bound = 4 := by
    simp [target, AffineSlope.finishDoubleXTarget, AffineSlope.scale,
      Modular.Lazy.scale, hPXbound]
  mvcgen [AffineSlope.finishDoubleX, AffineSlope.finishDoubleXTarget,
    AffineSlope.finishDoubleXHint, AffineSlope.finishDoubleXDecodeR,
    AffineSlope.finishDoubleXDecodeQ, AffineSlope.finishDoubleXCheck]
  let a := slope.intVal.eval ρ.int
  let c := target.intVal.eval ρ.int
  let shifted := a * a + (target.bound * base.modulus : Nat) - c
  have hshifted : 0 ≤ shifted := by
    have haa : 0 ≤ a * a := mul_nonneg hslope.1 hslope.1
    have hc : c < (target.bound * base.modulus : Nat) := htarget.2
    dsimp [shifted]
    omega
  have hshiftedRaw : 0 ≤
      slope.intVal.eval ρ.int * slope.intVal.eval ρ.int +
        ((AffineSlope.finishDoubleXTarget P).bound * base.modulus : Nat) -
          (AffineSlope.finishDoubleXTarget P).intVal.eval ρ.int := by
    simpa [a, c, target, shifted] using hshifted
  have htargetEvalRaw :
      (AffineSlope.finishDoubleXTarget P).intVal.eval ρ.int = c := by
    rfl
  have htargetBoundRaw :
      (AffineSlope.finishDoubleXTarget P).bound = target.bound := by
    rfl
  have htargetEvalExpanded :
      (AffineSlope.scale 2 P.X).intVal.eval ρ.int = c := by
    simpa only [AffineSlope.finishDoubleXTarget] using htargetEvalRaw
  have htargetBoundExpanded :
      (AffineSlope.scale 2 P.X).bound = target.bound := by
    simpa only [AffineSlope.finishDoubleXTarget] using htargetBoundRaw
  have hshiftCond : c ≤ a * a +
      (target.bound * base.modulus : Nat) := by
    change 0 ≤ a * a + (target.bound * base.modulus : Nat) - c at hshifted
    omega
  have hshiftCondLocal : c ≤
      slope.intVal.eval ρ.int * slope.intVal.eval ρ.int +
        (target.bound * base.modulus : Nat) := by
    simpa [a] using hshiftCond
  have hshiftCondTarget : target.intVal.eval ρ.int ≤
      slope.intVal.eval ρ.int * slope.intVal.eval ρ.int +
        (target.bound * base.modulus : Nat) := by
    simpa [a, c] using hshiftCond
  have hshiftCondTargetInt : target.intVal.eval ρ.int ≤
      slope.intVal.eval ρ.int * slope.intVal.eval ρ.int +
        (target.bound : Int) * base.modulus := by
    simpa only [Nat.cast_mul] using hshiftCondTarget
  let value := shifted.toNat
  let bits := Modular.Aux.quotientBits 512 256
    (value % base.modulus) (value / base.modulus)
  refine ⟨bits, ?_, ?_⟩
  · simp only [WF.interpHint, WF.evalArgs]
    rw [htargetEvalExpanded, htargetBoundExpanded]
    simp [hshiftCondLocal, bits, Modular.Aux.quotientBits, value,
      shifted, a, c]
    rw [if_pos hshiftCondTargetInt]
    rfl
  · mvcgen
    rename_i r hr q hq
    have hrFit : value % base.modulus < 2 ^ 256 :=
      (Nat.mod_lt _ base.positive).trans_le base.fits
    have hvalue : (value : Int) = shifted :=
      Int.toNat_of_nonneg hshifted
    have haUpper : a < base.modulus := hslopeCanonical
    have haaUpper : a * a < (base.modulus : Int) * base.modulus := by
      nlinarith [hslope.1]
    have hshiftUpper : value <
        (base.modulus + 4) * base.modulus := by
      apply (Int.toNat_lt hshifted).2
      have hc0 : 0 ≤ c := htarget.1
      dsimp [shifted]
      rw [htargetBound]
      push_cast at haaUpper ⊢
      ring_nf at haaUpper ⊢
      linarith
    have hqSmall : value / base.modulus < base.modulus + 4 :=
      (Nat.div_lt_iff_lt_mul base.positive).2 (by
        simpa [Nat.mul_assoc] using hshiftUpper)
    have hqFit : value / base.modulus < 2 ^ 256 :=
      hqSmall.trans (by
        set_option exponentiation.threshold 300 in
          norm_num [base, baseModulus])
    have hrWord := Modular.Aux.quotientBits_low
      (totalWidth := 512) (n := 256)
      (low := value % base.modulus) (high := value / base.modulus)
      (by omega) hrFit ρ
    have hqWord := Modular.Aux.quotientBits_high
      (totalWidth := 512) (n := 256) (quotientWidth := 256)
      (low := value % base.modulus) (high := value / base.modulus)
      (by omega) hqFit ρ
    have hrVal : r.intVal.eval ρ.int = (value % base.modulus : Nat) := by
      rw [U.Rel.intVal hr, hrWord]
    have hqVal : q.intVal.eval ρ.int = (value / base.modulus : Nat) := by
      rw [U.Rel.intVal hq, hqWord]
    constructor
    · simp only [LC.eval_add, LC.eval_sub, LC.eval_nsmul,
        LC.eval_ofConst, nsmul_eq_mul, hrVal, hqVal]
      have hdecomp : (value : Int) =
          ((value % base.modulus : Nat) : Int) +
            (base.modulus : Int) * ((value / base.modulus : Nat) : Int) := by
        exact_mod_cast (Nat.mod_add_div value base.modulus).symm
      dsimp [shifted, a, c] at hvalue
      rw [htargetBound] at hvalue
      rw [htargetEvalExpanded, htargetBoundExpanded]
      rw [htargetBound]
      change slope.intVal.eval ρ.int * slope.intVal.eval ρ.int =
        (value % base.modulus : Nat) + c +
          (base.modulus : Int) * (value / base.modulus : Nat) -
            (4 * base.modulus : Nat)
      calc
        slope.intVal.eval ρ.int * slope.intVal.eval ρ.int =
            (value : Int) + c - (4 * base.modulus : Nat) := by omega
        _ = (value % base.modulus : Nat) + c +
              (base.modulus : Int) * (value / base.modulus : Nat) -
                (4 * base.modulus : Nat) := by rw [hdecomp]; ring
    · mvcgen
      constructor
      · exact ⟨hr.1, by
          rw [hrVal]
          exact_mod_cast Nat.mod_lt value base.positive⟩
      · unfold Modular.Lazy.MulSubToElemZModSpec
          Modular.Lazy.evalElemZMod Modular.Lazy.evalZMod
        rw [hrVal]
        have hcast := congrArg
          (Int.castRingHom (ZMod base.modulus)) hvalue
        simpa [shifted, a, c, target] using hcast

@[spec] theorem finishDoubleY_complete {P : AffineSlope.Point}
    {slope : AffineSlope.Rep} {x3 : Fp}
    (hP : P.Valid ρ) (hslope : slope.Valid ρ)
    (hslopeBound : slope.bound = 2)
    (hslopeCanonical : slope.intVal.eval ρ.int < base.modulus)
    (hx3 : x3.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (AffineSlope.finishDoubleY P slope x3)
    ⦃⇓ y3 => ⌜y3.Valid ρ ∧
      Modular.Lazy.MulSubToElemZModSpec base ρ slope
        (AffineSlope.finishDoubleYFactor P x3) P.Y y3⌝⦄ := by
  rcases hP with
    ⟨_, hPX, hPXcanonical, hPYbound, hPY, _, _⟩
  let factor := AffineSlope.finishDoubleYFactor P x3
  have hfactor : factor.Valid ρ := by
    dsimp [factor, AffineSlope.finishDoubleYFactor]
    exact Modular.Lazy.sub_valid base hPX
      (Modular.Lazy.ofElem_valid base hx3)
  have hfactorUpper : factor.intVal.eval ρ.int <
      (3 * base.modulus : Nat) := by
    dsimp [factor, AffineSlope.finishDoubleYFactor,
      AffineSlope.sub, AffineSlope.ofElem]
    simp only [Modular.Lazy.sub, Modular.Lazy.ofElem,
      LC.eval_sub, LC.eval_add, LC.eval_ofConst]
    have hx30 := Modular.Elem.nonneg (p := base) hx3
    push_cast
    linarith
  mvcgen [AffineSlope.finishDoubleY, AffineSlope.finishDoubleYFactor,
    AffineSlope.finishDoubleYHint, AffineSlope.finishDoubleYDecodeR,
    AffineSlope.finishDoubleYDecodeQ, AffineSlope.finishDoubleYCheck]
  let a := slope.intVal.eval ρ.int
  let b := factor.intVal.eval ρ.int
  let c := P.Y.intVal.eval ρ.int
  let shifted := a * b + (P.Y.bound * base.modulus : Nat) - c
  have hshifted : 0 ≤ shifted := by
    have hab : 0 ≤ a * b := mul_nonneg hslope.1 hfactor.1
    have hc : c < (P.Y.bound * base.modulus : Nat) := hPY.2
    dsimp [shifted]
    omega
  have hshiftedRaw : 0 ≤
      slope.intVal.eval ρ.int *
          (AffineSlope.finishDoubleYFactor P x3).intVal.eval ρ.int +
        (P.Y.bound * base.modulus : Nat) - P.Y.intVal.eval ρ.int := by
    simpa [a, b, c, factor, shifted] using hshifted
  have hfactorEvalRaw :
      (AffineSlope.finishDoubleYFactor P x3).intVal.eval ρ.int = b := by
    rfl
  have hfactorEvalExpanded :
      (AffineSlope.sub P.X (AffineSlope.ofElem x3)).intVal.eval ρ.int = b := by
    simpa only [AffineSlope.finishDoubleYFactor] using hfactorEvalRaw
  have hshiftCond : c ≤ a * b +
      (P.Y.bound * base.modulus : Nat) := by
    change 0 ≤ a * b + (P.Y.bound * base.modulus : Nat) - c at hshifted
    omega
  have hshiftCondLocal : P.Y.intVal.eval ρ.int ≤
      slope.intVal.eval ρ.int * factor.intVal.eval ρ.int +
        (P.Y.bound * base.modulus : Nat) := by
    simpa [a, b, c] using hshiftCond
  have hshiftCondLocalInt : P.Y.intVal.eval ρ.int ≤
      slope.intVal.eval ρ.int * factor.intVal.eval ρ.int +
        (P.Y.bound : Int) * base.modulus := by
    simpa only [Nat.cast_mul] using hshiftCondLocal
  let value := shifted.toNat
  let bits := Modular.Aux.quotientBits 514 256
    (value % base.modulus) (value / base.modulus)
  refine ⟨bits, ?_, ?_⟩
  · simp only [WF.interpHint, WF.evalArgs]
    rw [hfactorEvalExpanded]
    simp [hshiftCondLocal, bits, Modular.Aux.quotientBits, value,
      shifted, a, b, c]
    rw [if_pos hshiftCondLocalInt]
    rfl
  · mvcgen
    rename_i r hr q hq
    have hrFit : value % base.modulus < 2 ^ 256 :=
      (Nat.mod_lt _ base.positive).trans_le base.fits
    have hvalue : (value : Int) = shifted :=
      Int.toNat_of_nonneg hshifted
    have habUpper : a * b <
        (base.modulus : Int) * (3 * base.modulus) := by
      have hpPos : (0 : Int) < base.modulus := by
        exact_mod_cast base.positive
      have hbPos : 0 < (3 * base.modulus : Int) := by nlinarith
      exact (mul_le_mul_of_nonneg_left hfactorUpper.le hslope.1).trans_lt
        (mul_lt_mul_of_pos_right hslopeCanonical hbPos)
    have hshiftUpper : value <
        (3 * base.modulus + 2) * base.modulus := by
      apply (Int.toNat_lt hshifted).2
      have hc0 : 0 ≤ c := hPY.1
      dsimp [shifted]
      rw [hPYbound]
      push_cast at habUpper ⊢
      ring_nf at habUpper ⊢
      linarith
    have hqSmall : value / base.modulus < 3 * base.modulus + 2 :=
      (Nat.div_lt_iff_lt_mul base.positive).2 (by
        simpa [Nat.mul_assoc] using hshiftUpper)
    have hqFit : value / base.modulus < 2 ^ 258 :=
      hqSmall.trans (by
        set_option exponentiation.threshold 300 in
          norm_num [base, baseModulus])
    have hrWord := Modular.Aux.quotientBits_low
      (totalWidth := 514) (n := 256)
      (low := value % base.modulus) (high := value / base.modulus)
      (by omega) hrFit ρ
    have hqWord := Modular.Aux.quotientBits_high
      (totalWidth := 514) (n := 256) (quotientWidth := 258)
      (low := value % base.modulus) (high := value / base.modulus)
      (by omega) hqFit ρ
    have hrVal : r.intVal.eval ρ.int = (value % base.modulus : Nat) := by
      rw [U.Rel.intVal hr, hrWord]
    have hqVal : q.intVal.eval ρ.int = (value / base.modulus : Nat) := by
      rw [U.Rel.intVal hq, hqWord]
    constructor
    · simp only [LC.eval_add, LC.eval_sub, LC.eval_nsmul,
        LC.eval_ofConst, nsmul_eq_mul, hrVal, hqVal]
      have hdecomp : (value : Int) =
          ((value % base.modulus : Nat) : Int) +
            (base.modulus : Int) * ((value / base.modulus : Nat) : Int) := by
        exact_mod_cast (Nat.mod_add_div value base.modulus).symm
      dsimp [shifted, a, b, c] at hvalue
      rw [hPYbound] at hvalue
      rw [hfactorEvalExpanded]
      rw [hPYbound]
      change slope.intVal.eval ρ.int * factor.intVal.eval ρ.int =
        (value % base.modulus : Nat) + P.Y.intVal.eval ρ.int +
          (base.modulus : Int) * (value / base.modulus : Nat) -
            (2 * base.modulus : Nat)
      calc
        slope.intVal.eval ρ.int * factor.intVal.eval ρ.int =
            (value : Int) + P.Y.intVal.eval ρ.int -
              (2 * base.modulus : Nat) := by omega
        _ = (value % base.modulus : Nat) + P.Y.intVal.eval ρ.int +
              (base.modulus : Int) * (value / base.modulus : Nat) -
                (2 * base.modulus : Nat) := by rw [hdecomp]; ring
    · mvcgen
      constructor
      · exact ⟨hr.1, by
          rw [hrVal]
          exact_mod_cast Nat.mod_lt value base.positive⟩
      · unfold Modular.Lazy.MulSubToElemZModSpec
          Modular.Lazy.evalElemZMod Modular.Lazy.evalZMod
        rw [hrVal]
        have hcast := congrArg
          (Int.castRingHom (ZMod base.modulus)) hvalue
        simpa [shifted, a, b, c, factor] using hcast

@[spec] theorem collapsedSlope_complete {operands : AffineSlope.SlopeOperands}
    (hnumerator : operands.numerator.Valid ρ)
    (hnumeratorBound : operands.numerator.bound = 5)
    (hdenominator : operands.denominator.Valid ρ)
    (hdenominatorBound : operands.denominator.bound = 3)
    (hden : Modular.Lazy.evalZMod base operands.denominator ρ ≠ 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (AffineSlope.collapsedSlope operands)
    ⦃⇓ slope => ⌜slope.Valid ρ ∧ slope.bound = 2 ∧
      slope.intVal.eval ρ.int < base.modulus ∧
      Modular.Lazy.DivideZModSpec base ρ
        operands.denominator operands.numerator slope⌝⦄ := by
  let numerator := operands.numerator
  let denominator := operands.denominator
  mvcgen [AffineSlope.collapsedSlope, AffineSlope.collapsedSlopeHint,
    AffineSlope.collapsedSlopeDecodeValue, AffineSlope.collapsedSlopeDecodeQ,
    AffineSlope.collapsedSlopeCheck]
  let numerator := operands.numerator
  let denominator := operands.denominator
  let a := denominator.intVal.eval ρ.int
  let b := numerator.intVal.eval ρ.int
  have haNat : (a.toNat : Int) = a := Int.toNat_of_nonneg hdenominator.1
  have hbNat : (b.toNat : Int) = b := Int.toNat_of_nonneg hnumerator.1
  let d := a.toNat % base.modulus
  have hdlt : d < base.modulus := Nat.mod_lt _ base.positive
  have haZ : (a : ZMod base.modulus) = (a.toNat : ZMod base.modulus) := by
    rw [← Int.cast_natCast]
    exact congrArg (Int.castRingHom (ZMod base.modulus)) haNat.symm
  have hd : d ≠ 0 := by
    intro hd0
    apply hden
    unfold Modular.Lazy.evalZMod
    change (a : ZMod base.modulus) = 0
    rw [haZ]
    rw [show (a.toNat : ZMod base.modulus) =
      (d : ZMod base.modulus) by simp [d], hd0]
    simp
  have hgcd : Nat.gcd d base.modulus = 1 := by
    rw [Nat.gcd_comm]
    exact (Nat.coprime_of_lt_prime hd hdlt Fact.out).gcd_eq_one
  let inverse := ((Nat.gcdA d base.modulus) %
    (base.modulus : Int)).toNat
  let value := (inverse * (b.toNat % base.modulus)) % base.modulus
  have hinverse : (inverse : ZMod base.modulus) *
      (d : ZMod base.modulus) = 1 := by
    have hp0 : (base.modulus : Int) ≠ 0 := by
      exact_mod_cast base.positive.ne'
    have hinverseInt : (inverse : Int) =
        Nat.gcdA d base.modulus % (base.modulus : Int) := by
      exact Int.toNat_of_nonneg (Int.emod_nonneg _ hp0)
    have hinverseCast : (inverse : ZMod base.modulus) =
        (Nat.gcdA d base.modulus : ZMod base.modulus) := by
      rw [← Int.cast_natCast, hinverseInt]
      simp
    rw [hinverseCast]
    have hbezout := Nat.gcd_eq_gcd_ab d base.modulus
    have hcast := congrArg (Int.castRingHom (ZMod base.modulus)) hbezout
    simpa [hgcd, mul_comm] using hcast.symm
  have hbZ : (b.toNat : ZMod base.modulus) = (b : ZMod base.modulus) := by
    rw [← Int.cast_natCast]
    exact congrArg (Int.castRingHom (ZMod base.modulus)) hbNat
  have hvalueZ : (value : ZMod base.modulus) *
      (a : ZMod base.modulus) = (b : ZMod base.modulus) := by
    rw [haZ]
    have hvalueCast : (value : ZMod base.modulus) =
        (inverse : ZMod base.modulus) * (b.toNat : ZMod base.modulus) := by
      simp [value]
    have haMod : (a.toNat : ZMod base.modulus) =
        (d : ZMod base.modulus) := by simp [d]
    rw [hvalueCast, haMod]
    calc
      (inverse : ZMod base.modulus) * (b.toNat : ZMod base.modulus) * d =
          (inverse * d) * (b.toNat : ZMod base.modulus) := by ring
      _ = (b.toNat : ZMod base.modulus) := by rw [hinverse]; simp
      _ = (b : ZMod base.modulus) := hbZ
  let shifted : Int := (value : Int) * a +
    (numerator.bound * base.modulus : Nat) - b
  have hshifted : 0 ≤ shifted := by
    have hva : 0 ≤ (value : Int) * a :=
      mul_nonneg (by positivity) hdenominator.1
    have hbUpper : b < (numerator.bound * base.modulus : Nat) :=
      hnumerator.2
    dsimp [shifted]
    omega
  have hshiftCond : b ≤ (value : Int) * a +
      (numerator.bound * base.modulus : Nat) := by
    change 0 ≤ (value : Int) * a +
      (numerator.bound * base.modulus : Nat) - b at hshifted
    omega
  have hshiftDvd : (base.modulus : Int) ∣ shifted := by
    have hmod : (((value : Int) * a : Int) : ZMod base.modulus) =
        (b : ZMod base.modulus) := by simpa using hvalueZ
    have hdvdDiff : (base.modulus : Int) ∣ b - (value : Int) * a :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hmod
    have hdvdNeg : (base.modulus : Int) ∣ (value : Int) * a - b := by
      simpa [neg_sub] using dvd_neg.mpr hdvdDiff
    dsimp [shifted]
    rcases hdvdNeg with ⟨k, hk⟩
    refine ⟨k + numerator.bound, ?_⟩
    push_cast
    calc
      (value : Int) * a + numerator.bound * base.modulus - b =
          ((value : Int) * a - b) + numerator.bound * base.modulus := by ring
      _ = base.modulus * k + numerator.bound * base.modulus := by rw [hk]
      _ = base.modulus * (k + numerator.bound) := by ring
  let bits := Modular.Aux.quotientBits 514 256 value
    (shifted.toNat / base.modulus)
  have hdenominatorEvalRaw :
      operands.denominator.intVal.eval ρ.int = a := by rfl
  have hnumeratorEvalRaw :
      operands.numerator.intVal.eval ρ.int = b := by rfl
  have ha0 : 0 ≤ a := hdenominator.1
  have hb0 : 0 ≤ b := hnumerator.1
  have hinverseIntNonneg : 0 ≤
      Nat.gcdA d base.modulus % (base.modulus : Int) :=
    Int.emod_nonneg _ (by exact_mod_cast base.positive.ne')
  have hinverseIntEq :
      (Nat.gcdA d base.modulus % (base.modulus : Int)) = inverse := by
    exact (Int.toNat_of_nonneg hinverseIntNonneg).symm
  have hvalueInt :
      (Nat.gcdA d base.modulus % (base.modulus : Int)) * b %
          (base.modulus : Int) = value := by
    rw [hinverseIntEq, ← hbNat]
    push_cast
    rw [Int.mul_emod]
    simp [value, Nat.mul_mod]
  have hshiftCondInt : b ≤ (value : Int) * a +
      (numerator.bound : Int) * base.modulus := by
    simpa only [Nat.cast_mul] using hshiftCond
  refine ⟨bits, ?_, ?_⟩
  · simp only [WF.interpHint, WF.evalArgs]
    rw [hdenominatorEvalRaw, hnumeratorEvalRaw]
    simp [ha0, hb0, hd, hgcd, hinverseIntNonneg, hshifted, bits,
      Modular.Aux.quotientBits, value, inverse, shifted, d]
    rw [hvalueInt, if_pos hshiftCondInt]
    rfl
  · mvcgen
    rename_i r hr q hq
    have hvalueFit : value < 2 ^ 256 :=
      (Nat.mod_lt _ base.positive).trans_le base.fits
    have hshiftEq : (shifted.toNat : Int) = shifted :=
      Int.toNat_of_nonneg hshifted
    have haUpper : a < (3 * base.modulus : Nat) := by
      simpa [hdenominatorBound] using hdenominator.2
    have hvaUpper : (value : Int) * a <
        (base.modulus : Int) * (3 * base.modulus) := by
      have hv : (value : Int) < base.modulus := by
        exact_mod_cast Nat.mod_lt (inverse * (b.toNat % base.modulus))
          base.positive
      have hp : (0 : Int) < base.modulus := by
        exact_mod_cast base.positive
      have haPos : 0 < (3 * base.modulus : Int) := by nlinarith
      exact (mul_le_mul_of_nonneg_left haUpper.le (by positivity)).trans_lt
        (mul_lt_mul_of_pos_right hv haPos)
    have hshiftUpper : shifted.toNat <
        (3 * base.modulus + 5) * base.modulus := by
      apply (Int.toNat_lt hshifted).2
      have hb0 : 0 ≤ b := hnumerator.1
      dsimp [shifted]
      rw [hnumeratorBound]
      push_cast at hvaUpper ⊢
      ring_nf at hvaUpper ⊢
      linarith
    have hqSmall : shifted.toNat / base.modulus <
        3 * base.modulus + 5 :=
      (Nat.div_lt_iff_lt_mul base.positive).2 (by
        simpa [Nat.mul_assoc] using hshiftUpper)
    have hqFit : shifted.toNat / base.modulus < 2 ^ 258 :=
      hqSmall.trans (by
        set_option exponentiation.threshold 300 in
          norm_num [base, baseModulus])
    have hrWord : (Word.eval ρ.bool {
        bitsLE := Vector.ofFn (n := 256) fun i =>
          (Vector.map LC.ofConst bits)[i.val]'(by omega) }).toNat = value := by
      simpa [Nat.mod_eq_of_lt hvalueFit] using
        (Modular.Aux.quotientBits_low (totalWidth := 514)
          (n := 256) (low := value) (high := shifted.toNat / base.modulus)
          (by omega) hvalueFit ρ)
    have hqWord := Modular.Aux.quotientBits_high
      (totalWidth := 514) (n := 256) (quotientWidth := 258)
      (low := value) (high := shifted.toNat / base.modulus)
      (by omega) hqFit ρ
    have hrVal : r.intVal.eval ρ.int = (value : Nat) := by
      rw [U.Rel.intVal hr, hrWord]
    have hqVal : q.intVal.eval ρ.int =
        (shifted.toNat / base.modulus : Nat) := by
      rw [U.Rel.intVal hq, hqWord]
    have hshiftDvdNat : base.modulus ∣ shifted.toNat := by
      rcases hshiftDvd with ⟨k, hk⟩
      refine ⟨k.toNat, ?_⟩
      have hk0 : 0 ≤ k := by
        have hp : (0 : Int) < base.modulus := by
          exact_mod_cast base.positive
        rw [hk] at hshifted
        nlinarith
      have hkNat : (k.toNat : Int) = k := Int.toNat_of_nonneg hk0
      apply Int.ofNat_inj.mp
      calc
        (shifted.toNat : Int) = shifted := hshiftEq
        _ = (base.modulus : Int) * k := hk
        _ = (base.modulus : Int) * (k.toNat : Int) := by rw [hkNat]
        _ = ((base.modulus * k.toNat : Nat) : Int) := by norm_num
    have hshiftDecomp : (shifted.toNat : Int) =
        (base.modulus : Int) *
          (shifted.toNat / base.modulus : Nat) := by
      have hnat := Nat.mod_add_div shifted.toNat base.modulus
      rw [Nat.mod_eq_zero_of_dvd hshiftDvdNat] at hnat
      simp only [zero_add] at hnat
      exact_mod_cast hnat.symm
    constructor
    · simp only [LC.eval_add, LC.eval_sub, LC.eval_nsmul,
        LC.eval_ofConst, nsmul_eq_mul, hrVal, hqVal]
      change (value : Int) * a = b +
        (base.modulus : Int) * (shifted.toNat / base.modulus : Nat) -
          (numerator.bound * base.modulus : Nat)
      calc
        (value : Int) * a =
            shifted - (numerator.bound * base.modulus : Nat) + b := by
          dsimp [shifted]
          ring
        _ = (shifted.toNat : Int) -
            (numerator.bound * base.modulus : Nat) + b := by rw [hshiftEq]
        _ = (base.modulus : Int) *
            (shifted.toNat / base.modulus : Nat) -
              (numerator.bound * base.modulus : Nat) + b := by
          rw [hshiftDecomp]
        _ = b + (base.modulus : Int) *
            (shifted.toNat / base.modulus : Nat) -
              (numerator.bound * base.modulus : Nat) := by ring
    · mvcgen
      refine ⟨?_, True.intro, ?_, ?_⟩
      · change 0 ≤ r.intVal.eval ρ.int ∧
          r.intVal.eval ρ.int < (2 * base.modulus : Nat)
        constructor
        · rw [hrVal]
          positivity
        · rw [hrVal]
          have hv : value < base.modulus := Nat.mod_lt _ base.positive
          push_cast
          omega
      · rw [hrVal]
        exact_mod_cast Nat.mod_lt (inverse * (b.toNat % base.modulus))
          base.positive
      · unfold Modular.Lazy.DivideZModSpec Modular.Lazy.evalZMod
        rw [hrVal]
        simpa [a, b, denominator, numerator] using hvalueZ

@[spec] theorem collapsedCandidateX_complete {P Q : AffineSlope.Point}
    {slope : AffineSlope.Rep}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ) (hslope : slope.Valid ρ)
    (hslopeBound : slope.bound = 2)
    (hslopeCanonical : slope.intVal.eval ρ.int < base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.collapsedCandidateX P Q slope)
    ⦃⇓ x3 => ⌜x3.Valid ρ ∧
      Modular.Lazy.MulSubToElemZModSpec base ρ slope slope
        (AffineSlope.collapsedCandidateXTarget P Q) x3⌝⦄ := by
  rcases hP with ⟨hPXbound, hPX, _, _, _, _, _⟩
  rcases hQ with ⟨hQXbound, hQX, _, _, _, _, _⟩
  let target := AffineSlope.collapsedCandidateXTarget P Q
  have htarget : target.Valid ρ := by
    dsimp [target, AffineSlope.collapsedCandidateXTarget]
    exact Modular.Lazy.add_valid base hPX hQX
  have htargetBound : target.bound = 4 := by
    simp [target, AffineSlope.collapsedCandidateXTarget, AffineSlope.add,
      Modular.Lazy.add, hPXbound, hQXbound]
  mvcgen [AffineSlope.collapsedCandidateX,
    AffineSlope.collapsedCandidateXTarget,
    AffineSlope.collapsedCandidateXHint,
    AffineSlope.collapsedCandidateXDecodeR,
    AffineSlope.collapsedCandidateXDecodeQ,
    AffineSlope.collapsedCandidateXCheck]
  let a := slope.intVal.eval ρ.int
  let c := target.intVal.eval ρ.int
  let shifted := a * a + (target.bound * base.modulus : Nat) - c
  have hshifted : 0 ≤ shifted := by
    have haa : 0 ≤ a * a := mul_nonneg hslope.1 hslope.1
    have hc : c < (target.bound * base.modulus : Nat) := htarget.2
    dsimp [shifted]
    omega
  have htargetEvalRaw :
      (AffineSlope.collapsedCandidateXTarget P Q).intVal.eval ρ.int = c := rfl
  have htargetBoundRaw :
      (AffineSlope.collapsedCandidateXTarget P Q).bound = target.bound := rfl
  have htargetEvalExpanded :
      (AffineSlope.add P.X Q.X).intVal.eval ρ.int = c := by
    simpa only [AffineSlope.collapsedCandidateXTarget] using htargetEvalRaw
  have htargetBoundExpanded :
      (AffineSlope.add P.X Q.X).bound = target.bound := by
    simpa only [AffineSlope.collapsedCandidateXTarget] using htargetBoundRaw
  have hshiftCond : c ≤ a * a +
      (target.bound * base.modulus : Nat) := by
    change 0 ≤ a * a + (target.bound * base.modulus : Nat) - c at hshifted
    omega
  have hshiftCondLocal : c ≤
      slope.intVal.eval ρ.int * slope.intVal.eval ρ.int +
        (target.bound * base.modulus : Nat) := by
    simpa [a] using hshiftCond
  have hshiftCondTarget : target.intVal.eval ρ.int ≤
      slope.intVal.eval ρ.int * slope.intVal.eval ρ.int +
        (target.bound * base.modulus : Nat) := by
    simpa [a, c] using hshiftCond
  have hshiftCondTargetInt : target.intVal.eval ρ.int ≤
      slope.intVal.eval ρ.int * slope.intVal.eval ρ.int +
        (target.bound : Int) * base.modulus := by
    simpa only [Nat.cast_mul] using hshiftCondTarget
  let value := shifted.toNat
  let bits := Modular.Aux.quotientBits 512 256
    (value % base.modulus) (value / base.modulus)
  refine ⟨bits, ?_, ?_⟩
  · simp only [WF.interpHint, WF.evalArgs]
    rw [htargetEvalExpanded, htargetBoundExpanded]
    simp [hshiftCondLocal, bits, Modular.Aux.quotientBits, value,
      shifted, a, c]
    rw [if_pos hshiftCondTargetInt]
    rfl
  · mvcgen
    rename_i r hr q hq
    have hrFit : value % base.modulus < 2 ^ 256 :=
      (Nat.mod_lt _ base.positive).trans_le base.fits
    have hvalue : (value : Int) = shifted :=
      Int.toNat_of_nonneg hshifted
    have haaUpper : a * a < (base.modulus : Int) * base.modulus := by
      nlinarith [hslope.1, hslopeCanonical]
    have hshiftUpper : value <
        (base.modulus + 4) * base.modulus := by
      apply (Int.toNat_lt hshifted).2
      have hc0 : 0 ≤ c := htarget.1
      dsimp [shifted]
      rw [htargetBound]
      push_cast at haaUpper ⊢
      ring_nf at haaUpper ⊢
      linarith
    have hqSmall : value / base.modulus < base.modulus + 4 :=
      (Nat.div_lt_iff_lt_mul base.positive).2 (by
        simpa [Nat.mul_assoc] using hshiftUpper)
    have hqFit : value / base.modulus < 2 ^ 256 :=
      hqSmall.trans (by
        set_option exponentiation.threshold 300 in
          norm_num [base, baseModulus])
    have hrWord := Modular.Aux.quotientBits_low
      (totalWidth := 512) (n := 256)
      (low := value % base.modulus) (high := value / base.modulus)
      (by omega) hrFit ρ
    have hqWord := Modular.Aux.quotientBits_high
      (totalWidth := 512) (n := 256) (quotientWidth := 256)
      (low := value % base.modulus) (high := value / base.modulus)
      (by omega) hqFit ρ
    have hrVal : r.intVal.eval ρ.int = (value % base.modulus : Nat) := by
      rw [U.Rel.intVal hr, hrWord]
    have hqVal : q.intVal.eval ρ.int = (value / base.modulus : Nat) := by
      rw [U.Rel.intVal hq, hqWord]
    constructor
    · simp only [LC.eval_add, LC.eval_sub, LC.eval_nsmul,
        LC.eval_ofConst, nsmul_eq_mul, hrVal, hqVal]
      have hdecomp : (value : Int) =
          ((value % base.modulus : Nat) : Int) +
            (base.modulus : Int) * ((value / base.modulus : Nat) : Int) := by
        exact_mod_cast (Nat.mod_add_div value base.modulus).symm
      dsimp [shifted, a, c] at hvalue
      rw [htargetBound] at hvalue
      rw [htargetEvalExpanded, htargetBoundExpanded, htargetBound]
      change slope.intVal.eval ρ.int * slope.intVal.eval ρ.int =
        (value % base.modulus : Nat) + c +
          (base.modulus : Int) * (value / base.modulus : Nat) -
            (4 * base.modulus : Nat)
      calc
        slope.intVal.eval ρ.int * slope.intVal.eval ρ.int =
            (value : Int) + c - (4 * base.modulus : Nat) := by omega
        _ = (value % base.modulus : Nat) + c +
              (base.modulus : Int) * (value / base.modulus : Nat) -
                (4 * base.modulus : Nat) := by rw [hdecomp]; ring
    · mvcgen
      constructor
      · exact ⟨hr.1, by
          rw [hrVal]
          exact_mod_cast Nat.mod_lt value base.positive⟩
      · unfold Modular.Lazy.MulSubToElemZModSpec
          Modular.Lazy.evalElemZMod Modular.Lazy.evalZMod
        rw [hrVal]
        have hcast := congrArg
          (Int.castRingHom (ZMod base.modulus)) hvalue
        simpa [shifted, a, c, target] using hcast

@[spec] theorem collapsedCandidateY_complete {P : AffineSlope.Point}
    {slope : AffineSlope.Rep} {x3 : Fp}
    (hP : P.Valid ρ) (hslope : slope.Valid ρ)
    (hslopeBound : slope.bound = 2)
    (hslopeCanonical : slope.intVal.eval ρ.int < base.modulus)
    (hx3 : x3.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (AffineSlope.collapsedCandidateY P slope x3)
    ⦃⇓ y3 => ⌜y3.Valid ρ ∧
      Modular.Lazy.MulSubToElemZModSpec base ρ slope
        (AffineSlope.collapsedCandidateYFactor P x3) P.Y y3⌝⦄ := by
  rcases hP with
    ⟨_, hPX, hPXcanonical, hPYbound, hPY, _, _⟩
  let factor := AffineSlope.collapsedCandidateYFactor P x3
  have hfactor : factor.Valid ρ := by
    dsimp [factor, AffineSlope.collapsedCandidateYFactor]
    exact Modular.Lazy.sub_valid base hPX
      (Modular.Lazy.ofElem_valid base hx3)
  have hfactorUpper : factor.intVal.eval ρ.int <
      (3 * base.modulus : Nat) := by
    dsimp [factor, AffineSlope.collapsedCandidateYFactor,
      AffineSlope.sub, AffineSlope.ofElem]
    simp only [Modular.Lazy.sub, Modular.Lazy.ofElem,
      LC.eval_sub, LC.eval_add, LC.eval_ofConst]
    have hx30 := Modular.Elem.nonneg (p := base) hx3
    push_cast
    linarith
  mvcgen [AffineSlope.collapsedCandidateY, AffineSlope.collapsedCandidateYFactor,
    AffineSlope.collapsedCandidateYHint, AffineSlope.collapsedCandidateYDecodeR,
    AffineSlope.collapsedCandidateYDecodeQ, AffineSlope.collapsedCandidateYCheck]
  let a := slope.intVal.eval ρ.int
  let b := factor.intVal.eval ρ.int
  let c := P.Y.intVal.eval ρ.int
  let shifted := a * b + (P.Y.bound * base.modulus : Nat) - c
  have hshifted : 0 ≤ shifted := by
    have hab : 0 ≤ a * b := mul_nonneg hslope.1 hfactor.1
    have hc : c < (P.Y.bound * base.modulus : Nat) := hPY.2
    dsimp [shifted]
    omega
  have hshiftedRaw : 0 ≤
      slope.intVal.eval ρ.int *
          (AffineSlope.collapsedCandidateYFactor P x3).intVal.eval ρ.int +
        (P.Y.bound * base.modulus : Nat) - P.Y.intVal.eval ρ.int := by
    simpa [a, b, c, factor, shifted] using hshifted
  have hfactorEvalRaw :
      (AffineSlope.collapsedCandidateYFactor P x3).intVal.eval ρ.int = b := by
    rfl
  have hfactorEvalExpanded :
      (AffineSlope.sub P.X (AffineSlope.ofElem x3)).intVal.eval ρ.int = b := by
    simpa only [AffineSlope.collapsedCandidateYFactor] using hfactorEvalRaw
  have hshiftCond : c ≤ a * b +
      (P.Y.bound * base.modulus : Nat) := by
    change 0 ≤ a * b + (P.Y.bound * base.modulus : Nat) - c at hshifted
    omega
  have hshiftCondLocal : P.Y.intVal.eval ρ.int ≤
      slope.intVal.eval ρ.int * factor.intVal.eval ρ.int +
        (P.Y.bound * base.modulus : Nat) := by
    simpa [a, b, c] using hshiftCond
  have hshiftCondLocalInt : P.Y.intVal.eval ρ.int ≤
      slope.intVal.eval ρ.int * factor.intVal.eval ρ.int +
        (P.Y.bound : Int) * base.modulus := by
    simpa only [Nat.cast_mul] using hshiftCondLocal
  let value := shifted.toNat
  let bits := Modular.Aux.quotientBits 514 256
    (value % base.modulus) (value / base.modulus)
  refine ⟨bits, ?_, ?_⟩
  · simp only [WF.interpHint, WF.evalArgs]
    rw [hfactorEvalExpanded]
    simp [hshiftCondLocal, bits, Modular.Aux.quotientBits, value,
      shifted, a, b, c]
    rw [if_pos hshiftCondLocalInt]
    rfl
  · mvcgen
    rename_i r hr q hq
    have hrFit : value % base.modulus < 2 ^ 256 :=
      (Nat.mod_lt _ base.positive).trans_le base.fits
    have hvalue : (value : Int) = shifted :=
      Int.toNat_of_nonneg hshifted
    have habUpper : a * b <
        (base.modulus : Int) * (3 * base.modulus) := by
      have hpPos : (0 : Int) < base.modulus := by
        exact_mod_cast base.positive
      have hbPos : 0 < (3 * base.modulus : Int) := by nlinarith
      exact (mul_le_mul_of_nonneg_left hfactorUpper.le hslope.1).trans_lt
        (mul_lt_mul_of_pos_right hslopeCanonical hbPos)
    have hshiftUpper : value <
        (3 * base.modulus + 2) * base.modulus := by
      apply (Int.toNat_lt hshifted).2
      have hc0 : 0 ≤ c := hPY.1
      dsimp [shifted]
      rw [hPYbound]
      push_cast at habUpper ⊢
      ring_nf at habUpper ⊢
      linarith
    have hqSmall : value / base.modulus < 3 * base.modulus + 2 :=
      (Nat.div_lt_iff_lt_mul base.positive).2 (by
        simpa [Nat.mul_assoc] using hshiftUpper)
    have hqFit : value / base.modulus < 2 ^ 258 :=
      hqSmall.trans (by
        set_option exponentiation.threshold 300 in
          norm_num [base, baseModulus])
    have hrWord := Modular.Aux.quotientBits_low
      (totalWidth := 514) (n := 256)
      (low := value % base.modulus) (high := value / base.modulus)
      (by omega) hrFit ρ
    have hqWord := Modular.Aux.quotientBits_high
      (totalWidth := 514) (n := 256) (quotientWidth := 258)
      (low := value % base.modulus) (high := value / base.modulus)
      (by omega) hqFit ρ
    have hrVal : r.intVal.eval ρ.int = (value % base.modulus : Nat) := by
      rw [U.Rel.intVal hr, hrWord]
    have hqVal : q.intVal.eval ρ.int = (value / base.modulus : Nat) := by
      rw [U.Rel.intVal hq, hqWord]
    constructor
    · simp only [LC.eval_add, LC.eval_sub, LC.eval_nsmul,
        LC.eval_ofConst, nsmul_eq_mul, hrVal, hqVal]
      have hdecomp : (value : Int) =
          ((value % base.modulus : Nat) : Int) +
            (base.modulus : Int) * ((value / base.modulus : Nat) : Int) := by
        exact_mod_cast (Nat.mod_add_div value base.modulus).symm
      dsimp [shifted, a, b, c] at hvalue
      rw [hPYbound] at hvalue
      rw [hfactorEvalExpanded]
      rw [hPYbound]
      change slope.intVal.eval ρ.int * factor.intVal.eval ρ.int =
        (value % base.modulus : Nat) + P.Y.intVal.eval ρ.int +
          (base.modulus : Int) * (value / base.modulus : Nat) -
            (2 * base.modulus : Nat)
      calc
        slope.intVal.eval ρ.int * factor.intVal.eval ρ.int =
            (value : Int) + P.Y.intVal.eval ρ.int -
              (2 * base.modulus : Nat) := by omega
        _ = (value % base.modulus : Nat) + P.Y.intVal.eval ρ.int +
              (base.modulus : Int) * (value / base.modulus : Nat) -
                (2 * base.modulus : Nat) := by rw [hdecomp]; ring
    · mvcgen
      constructor
      · exact ⟨hr.1, by
          rw [hrVal]
          exact_mod_cast Nat.mod_lt value base.positive⟩
      · unfold Modular.Lazy.MulSubToElemZModSpec
          Modular.Lazy.evalElemZMod Modular.Lazy.evalZMod
        rw [hrVal]
        have hcast := congrArg
          (Int.castRingHom (ZMod base.modulus)) hvalue
        simpa [shifted, a, b, c, factor] using hcast

@[spec] theorem doubleSlope_sound {P : AffineSlope.Point} :
    ⦃⌜True⌝⦄ Sound.interp ρ (AffineSlope.doubleSlope P)
    ⦃⇓ slope => ⌜DoubleSlopeSpec ρ P slope⌝⦄ := by
  mvcgen [AffineSlope.doubleSlope]
  rename_i x2 hx2 slope
  intro hslope
  unfold DoubleSlopeSpec
  unfold Modular.Lazy.MulZModSpec at hx2
  unfold Modular.Lazy.DivideZModSpec at hslope
  simp [AffineSlope.add, AffineSlope.sub, AffineSlope.scale,
    AffineSlope.ofElem] at hslope
  rw [hx2] at hslope
  exact hslope

@[spec] theorem finishDouble_sound {P : AffineSlope.Point}
    {slope : AffineSlope.Rep} :
    ⦃⌜True⌝⦄ Sound.interp ρ (AffineSlope.finishDouble P slope)
    ⦃⇓ out => ⌜FinishDoubleSpec ρ P slope out⌝⦄ := by
  mvcgen [AffineSlope.finishDouble]
  rename_i x3 hx3 y3 hy3
  unfold FinishDoubleSpec
  refine ⟨?_, ?_, rfl⟩
  · simpa [Modular.Lazy.MulSubToElemZModSpec, AffineSlope.scale,
      AffineSlope.ofElem] using hx3
  · simpa [Modular.Lazy.MulSubToElemZModSpec, AffineSlope.sub,
      AffineSlope.ofElem, hx3] using hy3

@[spec] theorem doubleSlope_complete {P : AffineSlope.Point}
    {p : Reference.Point}
    (hvalid : P.Valid ρ)
    (hP : Reference.NormalizedRep ρ P p)
    (hdouble : p = 0 ∨ p + p ≠ 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (AffineSlope.doubleSlope P)
    ⦃⇓ slope => ⌜slope.Valid ρ ∧ slope.bound = 2 ∧
      slope.intVal.eval ρ.int < base.modulus ∧
      DoubleSlopeSpec ρ P slope⌝⦄ := by
  rcases hvalid with
    ⟨hPXbound, hPX, hPXcanonical, hPYbound, hPY, hPYcanonical, hPinf⟩
  have hvalid' : P.Valid ρ :=
    ⟨hPXbound, hPX, hPXcanonical, hPYbound, hPY, hPYcanonical, hPinf⟩
  have hden : Modular.Lazy.evalZMod base
      (AffineSlope.add (AffineSlope.scale 2 P.Y)
        ⟨P.infinity, 1⟩) ρ ≠ 0 := by
    rcases p with _ | ⟨px, py, hpcurve⟩
    · have hpinf := Reference.Aux.represents_zero hP.1
      have hpy0 := (hP.2 rfl).2
      simp [AffineSlope.add, AffineSlope.scale, hpinf, hpy0]
    · obtain ⟨hpinf, hpx, hpy⟩ := Reference.Aux.represents_some hP.1
      have hyneg : py ≠ Reference.curve.toAffine.negY px py := by
        intro hy
        rcases hdouble with hzero | hne
        · contradiction
        · apply hne
          exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy
      simp only [AffineSlope.add, AffineSlope.scale,
        Modular.Lazy.evalZMod_add, Modular.Lazy.evalZMod_scale,
        evalZMod_mk, hpinf, hpy]
      intro hzero
      apply hyneg
      simp only [WeierstrassCurve.Affine.negY, Reference.curve, zero_mul]
      have hzero' : 2 * py = 0 := by simpa using hzero
      linear_combination hzero'
  mvcgen [AffineSlope.doubleSlope]
  all_goals first
    | exact hvalid'
    | exact hden
    | assumption
    | skip
  all_goals
    simp_all [DoubleSlopeSpec, Modular.Lazy.MulZModSpec,
      Modular.Lazy.DivideZModSpec, AffineSlope.doubleSlopeNumerator,
      AffineSlope.doubleSlopeDenominator, AffineSlope.add,
      AffineSlope.sub, AffineSlope.scale, AffineSlope.ofElem,
      three_evalElemZMod]

@[spec] theorem finishDouble_complete {P : AffineSlope.Point}
    {slope : AffineSlope.Rep}
    (hP : P.Valid ρ) (hslope : slope.Valid ρ)
    (hslopeBound : slope.bound = 2)
    (hslopeCanonical : slope.intVal.eval ρ.int < base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ (AffineSlope.finishDouble P slope)
    ⦃⇓ out => ⌜out.Valid ρ ∧ FinishDoubleSpec ρ P slope out⌝⦄ := by
  rcases hP with
    ⟨hPXbound, hPX, hPXcanonical, hPYbound, hPY, hPYcanonical, hPinf⟩
  have hP' : P.Valid ρ :=
    ⟨hPXbound, hPX, hPXcanonical, hPYbound, hPY, hPYcanonical, hPinf⟩
  mvcgen [AffineSlope.finishDouble]
  all_goals first
    | exact hP'
    | exact hslope
    | exact hslopeBound
    | exact hslopeCanonical
    | assumption
    | skip
  case vc9.hx3 =>
    rename_i x3 hx3
    exact hx3.1
  case vc10.success =>
    rename_i x3 hx3 y3 hy3
    constructor
    · exact ⟨rfl, Modular.Lazy.ofElem_valid base hx3.1,
        hx3.1.2, rfl, Modular.Lazy.ofElem_valid base hy3.1,
        hy3.1.2, hPinf⟩
    · unfold FinishDoubleSpec
      unfold Modular.Lazy.MulSubToElemZModSpec at hx3 hy3
      constructor
      · simpa [AffineSlope.finishDoubleXTarget, AffineSlope.ofElem,
          AffineSlope.scale] using hx3.2
      · constructor
        · simpa [AffineSlope.finishDoubleYFactor, AffineSlope.ofElem,
            AffineSlope.sub] using hy3.2
        · rfl

theorem double_specs_mathlib {P out : AffineSlope.Point}
    {p : Reference.Point} {slope : AffineSlope.Rep}
    (hP : Reference.NormalizedRep ρ P p)
    (hslope : DoubleSlopeSpec ρ P slope)
    (hout : FinishDoubleSpec ρ P slope out) :
    Reference.NormalizedRep ρ out (p + p) := by
  rcases hP with ⟨hrep, hnormalized⟩
  rcases hout with ⟨houtX, houtY, houtInf⟩
  rcases p with _ | ⟨px, py, hpcurve⟩
  · have hpinf := Reference.Aux.represents_zero hrep
    have hcoords := hnormalized rfl
    have hPXY : Modular.Lazy.evalZMod base P.X ρ = 0 ∧
        Modular.Lazy.evalZMod base P.Y ρ = 0 := hcoords
    have hslope0 : Modular.Lazy.evalZMod base slope ρ = 0 := by
      simp [DoubleSlopeSpec, hpinf, hPXY.1, hPXY.2] at hslope
      exact hslope
    have houtXY : Modular.Lazy.evalZMod base out.X ρ = 0 ∧
        Modular.Lazy.evalZMod base out.Y ρ = 0 := by
      simp [hslope0, hPXY.1, hPXY.2] at houtX houtY
      exact ⟨houtX, houtY⟩
    constructor
    · constructor
      · rw [houtInf, hpinf]
        exact Or.inr rfl
      · unfold Reference.circuitCoordinates
        rw [houtInf, hpinf]
        change Reference.coordinates 0 = Reference.coordinates (0 + 0)
        rw [zero_add]
    · intro _
      exact houtXY
  · obtain ⟨hpinf, hpx, hpy⟩ := Reference.Aux.represents_some hrep
    have hslopeRaw : Modular.Lazy.evalZMod base slope ρ * (2 * py) =
        3 * (px * px) - 3 := by
      simpa [DoubleSlopeSpec, hpinf, hpx, hpy] using hslope
    have hden : 2 * py ≠ 0 := by
      intro hzero
      have hnonsingular :=
        (WeierstrassCurve.Affine.nonsingular_iff' px py).1 hpcurve
      have hnumzero : 3 * (px * px) - 3 = 0 := by
        calc
          3 * (px * px) - 3 =
              Modular.Lazy.evalZMod base slope ρ * (2 * py) :=
            hslopeRaw.symm
          _ = 0 := by rw [hzero]; simp
      rcases hnonsingular.2 with hx | hy
      · apply hx
        have hneg := congrArg Neg.neg hnumzero
        simpa [Reference.curve, pow_two, sub_eq_add_neg, add_comm]
          using hneg
      · apply hy
        simpa [Reference.curve] using hzero
    have hslopeEq : Modular.Lazy.evalZMod base slope ρ =
        Reference.tangentSlope px py := by
      apply (eq_div_iff hden).2
      simpa [Reference.tangentSlope, pow_two] using hslopeRaw
    have hyneg : py ≠ Reference.curve.toAffine.negY px py := by
      intro hy
      apply hden
      simp [WeierstrassCurve.Affine.negY, Reference.curve] at hy
      linear_combination hy
    unfold Reference.NormalizedRep Reference.Represents
    constructor
    · constructor
      · rw [houtInf, hpinf]
        exact Or.inl rfl
      · unfold Reference.circuitCoordinates
        rw [if_neg (by simp [houtInf, hpinf])]
        rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyneg]
        simp only [Reference.coordinates]
        apply congrArg₂ Reference.Coordinates.finite
        · rw [houtX, hslopeEq, hpx]
          rw [← Reference.Aux.tangentSlope_eq_mathlib rfl hyneg]
          rw [← Reference.Aux.resultX_eq_mathlib]
          simp only [Reference.resultX]
          ring
        · rw [houtY, houtX, hslopeEq, hpx, hpy]
          rw [← Reference.Aux.tangentSlope_eq_mathlib rfl hyneg]
          rw [← Reference.Aux.resultY_eq_mathlib]
          simp only [Reference.resultY, Reference.resultX]
          ring
    · intro hzero
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyneg] at hzero
      contradiction

@[spec] theorem andBit_sound {x y : LC ℤ} :
    ⦃⌜True⌝⦄ Sound.interp ρ (AffineSlope.andBit x y)
    ⦃⇓ out => ⌜AffineSlope.AndBitSpec ρ x y out⌝⦄ := by
  mvcgen [AffineSlope.andBit, AffineSlope.AndBitSpec]
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

@[spec] theorem andBit_complete {x y : LC ℤ}
    (hx : x.eval ρ.int = 0 ∨ x.eval ρ.int = 1)
    (hy : y.eval ρ.int = 0 ∨ y.eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Complete.interp ρ (AffineSlope.andBit x y)
    ⦃⇓ out => ⌜AffineSlope.AndBitSpec ρ x y out⌝⦄ := by
  mvcgen [AffineSlope.andBit]
  let value : Bool := x.eval ρ.int = 1 && y.eval ρ.int = 1
  let bits : Vector Bool 1 := Vector.ofFn fun _ => value
  refine ⟨bits, ?_, ?_⟩
  · simp [WF.interpHint, WF.evalArgs, bits, value]
  · mvcgen
    rename_i out hout
    have hword :
        (Word.eval ρ.bool { bitsLE := Vector.map LC.ofConst bits }).toNat =
          if value then 1 else 0 := by
      cases hv : value <;>
        simp [Word.eval, BitVec.toNat_ofFnLE, bits, hv, Nat.ofBits] <;>
        native_decide
    have houtVal : out.intVal.eval ρ.int = if value then 1 else 0 := by
      rw [U.Rel.intVal hout]
      exact_mod_cast hword
    constructor
    · rcases hx with hx | hx <;> rcases hy with hy | hy <;>
        simp [value, hx, hy] at houtVal ⊢ <;> omega
    · mvcgen
      unfold AffineSlope.AndBitSpec
      refine ⟨?_, ?_⟩
      · rcases hx with hx | hx <;> rcases hy with hy | hy <;>
          simp [value, hx, hy] at houtVal ⊢ <;> omega
      · rcases hx with hx | hx <;> rcases hy with hy | hy <;>
          simp [value, hx, hy] at houtVal ⊢ <;> omega

def And3BitSpec (ρ : WF.Valuation) (x y z out : LC ℤ) : Prop :=
  ∃ xy : LC ℤ, AffineSlope.AndBitSpec ρ x y xy ∧
    AffineSlope.AndBitSpec ρ z xy out

@[spec] theorem and3Bit_sound {x y z : LC ℤ} :
    ⦃⌜True⌝⦄ Sound.interp ρ (AffineSlope.and3Bit x y z)
    ⦃⇓ out => ⌜And3BitSpec ρ x y z out⌝⦄ := by
  mvcgen [AffineSlope.and3Bit, And3BitSpec]
  rename_i xy hxy out
  intro hout
  exact ⟨xy, hxy, hout⟩

@[spec] theorem and3Bit_complete {x y z : LC ℤ}
    (hx : x.eval ρ.int = 0 ∨ x.eval ρ.int = 1)
    (hy : y.eval ρ.int = 0 ∨ y.eval ρ.int = 1)
    (hz : z.eval ρ.int = 0 ∨ z.eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Complete.interp ρ (AffineSlope.and3Bit x y z)
    ⦃⇓ out => ⌜And3BitSpec ρ x y z out⌝⦄ := by
  mvcgen [AffineSlope.and3Bit, And3BitSpec]
  all_goals intros
  all_goals first
    | assumption
    | exact (by assumption : AffineSlope.AndBitSpec ρ x y _).2
    | exact ⟨_, by assumption, by assumption⟩

@[spec] theorem selectRep_sound {width outBound : Nat} {description : String}
    {choose : LC ℤ} {whenOne whenZero : AffineSlope.Rep} :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (AffineSlope.selectRep width outBound description choose whenOne whenZero)
    ⦃⇓ out => ⌜AffineSlope.SelectZModSpec ρ choose whenOne whenZero out⌝⦄ := by
  mvcgen [AffineSlope.selectRep, AffineSlope.SelectZModSpec]
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

@[spec] theorem selectRep_complete {width outBound limit : Nat}
    {description : String} {choose : LC ℤ}
    {whenOne whenZero : AffineSlope.Rep}
    (hchoose : choose.eval ρ.int = 0 ∨ choose.eval ρ.int = 1)
    (hone : whenOne.Valid ρ)
    (honeFit : whenOne.intVal.eval ρ.int < limit)
    (hzero : whenZero.Valid ρ)
    (hzeroFit : whenZero.intVal.eval ρ.int < limit)
    (hwidth : limit ≤ 2 ^ width)
    (hbound : limit ≤ outBound * base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectRep width outBound description choose whenOne whenZero)
    ⦃⇓ out => ⌜AffineSlope.SelectZModSpec ρ choose whenOne whenZero out ∧
      out.Valid ρ ∧ out.intVal.eval ρ.int < limit ∧
      out.bound = outBound⌝⦄ := by
  mvcgen [AffineSlope.selectRep]
  let value := if choose.eval ρ.int = 1 then
    whenOne.intVal.eval ρ.int else whenZero.intVal.eval ρ.int
  let bits : Vector Bool width := Vector.ofFn fun i => value.toNat.testBit i.val
  refine ⟨bits, ?_, ?_⟩
  · rcases hchoose with hc | hc
    · simp [WF.interpHint, WF.evalArgs, bits, value, hc, hzero.1]
    · simp [WF.interpHint, WF.evalArgs, bits, value, hc, hone.1]
  · mvcgen
    rename_i out hout
    have hvalue0 : 0 ≤ value := by
      unfold value
      split
      · exact hone.1
      · exact hzero.1
    have hvalueFit : value < limit := by
      unfold value
      split
      · exact honeFit
      · exact hzeroFit
    have hfit : value.toNat < 2 ^ width := by
      apply (Int.toNat_lt hvalue0).2
      exact hvalueFit.trans_le (by exact_mod_cast hwidth)
    have hword :
        (Word.eval ρ.bool { bitsLE := Vector.map LC.ofConst bits }).toNat =
          value.toNat := by
      rw [show Vector.map LC.ofConst bits =
          Vector.ofFn (n := width) fun i =>
            LC.ofConst (value.toNat.testBit i.val) by
        ext i
        simp [bits]]
      exact Modular.Aux.constWord_eval_toNat value.toNat hfit ρ
    have houtVal : out.intVal.eval ρ.int = value := by
      rw [U.Rel.intVal hout, hword, Int.toNat_of_nonneg hvalue0]
    constructor
    · rcases hchoose with hc | hc
      · simp [LC.eval_sub, hc, value, houtVal]
      · simp [LC.eval_sub, hc, value, houtVal]
    · mvcgen
      constructor
      · unfold AffineSlope.SelectZModSpec Modular.Lazy.evalZMod
        constructor <;> intro hc <;> simp [value, hc] at houtVal ⊢ <;>
          rw [houtVal]
      · refine ⟨⟨U.intVal_nonneg out hout.1, ?_⟩, ?_⟩
        · rw [houtVal]
          exact hvalueFit.trans_le (by exact_mod_cast hbound)
        · simpa [houtVal] using hvalueFit

@[spec] theorem selectCanonical_sound {choose : LC ℤ}
    {whenOne whenZero : AffineSlope.Rep} :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (AffineSlope.selectCanonical choose whenOne whenZero)
    ⦃⇓ out => ⌜AffineSlope.SelectZModSpec ρ choose whenOne whenZero out⌝⦄ := by
  exact selectRep_sound

@[spec] theorem selectCanonical_complete {choose : LC ℤ}
    {whenOne whenZero : AffineSlope.Rep}
    (hchoose : choose.eval ρ.int = 0 ∨ choose.eval ρ.int = 1)
    (hone : whenOne.Valid ρ)
    (honeCanonical : whenOne.intVal.eval ρ.int < base.modulus)
    (hzero : whenZero.Valid ρ)
    (hzeroCanonical : whenZero.intVal.eval ρ.int < base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectCanonical choose whenOne whenZero)
    ⦃⇓ out => ⌜AffineSlope.SelectZModSpec ρ choose whenOne whenZero out ∧
      out.Valid ρ ∧ out.intVal.eval ρ.int < base.modulus ∧
      out.bound = 2⌝⦄ := by
  unfold AffineSlope.selectCanonical
  exact selectRep_complete hchoose hone honeCanonical hzero hzeroCanonical
    base.fits (by norm_num [base, baseModulus])

@[spec] theorem selectFormula_sound {choose : LC ℤ}
    {whenOne whenZero : AffineSlope.Rep} :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (AffineSlope.selectFormula choose whenOne whenZero)
    ⦃⇓ out => ⌜AffineSlope.SelectZModSpec ρ choose whenOne whenZero out⌝⦄ := by
  exact selectRep_sound

@[spec] theorem selectFormula_complete {choose : LC ℤ}
    {whenOne whenZero : AffineSlope.Rep}
    (hchoose : choose.eval ρ.int = 0 ∨ choose.eval ρ.int = 1)
    (hone : whenOne.Valid ρ)
    (honeFit : whenOne.intVal.eval ρ.int < (2 ^ 262 : Nat))
    (hzero : whenZero.Valid ρ)
    (hzeroFit : whenZero.intVal.eval ρ.int < (2 ^ 262 : Nat)) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectFormula choose whenOne whenZero)
    ⦃⇓ out => ⌜AffineSlope.SelectZModSpec ρ choose whenOne whenZero out ∧
      out.Valid ρ ∧ out.intVal.eval ρ.int < (2 ^ 262 : Nat) ∧
      out.bound = 66⌝⦄ := by
  unfold AffineSlope.selectFormula
  exact selectRep_complete hchoose hone honeFit hzero hzeroFit le_rfl
    (by norm_num [base, baseModulus]; native_decide)

def Gated3Spec (ρ : WF.Valuation) (gate1 gate2 gate3 : LC ℤ)
    (value1 value2 value3 out : AffineSlope.Rep) : Prop :=
  (gate1.eval ρ.int = 1 →
    Modular.Lazy.evalZMod base out ρ =
      Modular.Lazy.evalZMod base value1 ρ) ∧
  (gate2.eval ρ.int = 1 →
    Modular.Lazy.evalZMod base out ρ =
      Modular.Lazy.evalZMod base value2 ρ) ∧
  (gate3.eval ρ.int = 1 →
    Modular.Lazy.evalZMod base out ρ =
      Modular.Lazy.evalZMod base value3 ρ)

def Gated4Spec (ρ : WF.Valuation) (gate1 gate2 gate3 gate4 : LC ℤ)
    (value1 value2 value3 value4 out : AffineSlope.Rep) : Prop :=
  (gate1.eval ρ.int = 1 →
    Modular.Lazy.evalZMod base out ρ =
      Modular.Lazy.evalZMod base value1 ρ) ∧
  (gate2.eval ρ.int = 1 →
    Modular.Lazy.evalZMod base out ρ =
      Modular.Lazy.evalZMod base value2 ρ) ∧
  (gate3.eval ρ.int = 1 →
    Modular.Lazy.evalZMod base out ρ =
      Modular.Lazy.evalZMod base value3 ρ) ∧
  (gate4.eval ρ.int = 1 →
    Modular.Lazy.evalZMod base out ρ =
      Modular.Lazy.evalZMod base value4 ρ)

def Gated3Cases (ρ : WF.Valuation) (gate1 gate2 gate3 : LC ℤ) : Prop :=
  (gate1.eval ρ.int = 1 ∧ gate2.eval ρ.int = 0 ∧
      gate3.eval ρ.int = 0) ∨
  (gate1.eval ρ.int = 0 ∧ gate2.eval ρ.int = 1 ∧
      gate3.eval ρ.int = 0) ∨
  (gate1.eval ρ.int = 0 ∧ gate2.eval ρ.int = 0 ∧
      gate3.eval ρ.int = 1)

def Gated4Cases (ρ : WF.Valuation)
    (gate1 gate2 gate3 gate4 : LC ℤ) : Prop :=
  (gate1.eval ρ.int = 1 ∧ gate2.eval ρ.int = 0 ∧
      gate3.eval ρ.int = 0 ∧ gate4.eval ρ.int = 0) ∨
  (gate1.eval ρ.int = 0 ∧ gate2.eval ρ.int = 1 ∧
      gate3.eval ρ.int = 0 ∧ gate4.eval ρ.int = 0) ∨
  (gate1.eval ρ.int = 0 ∧ gate2.eval ρ.int = 0 ∧
      gate3.eval ρ.int = 1 ∧ gate4.eval ρ.int = 0) ∨
  (gate1.eval ρ.int = 0 ∧ gate2.eval ρ.int = 0 ∧
      gate3.eval ρ.int = 0 ∧ gate4.eval ρ.int = 1)

@[spec] theorem selectGated3Rep_sound {width outBound : Nat}
    {description : String} {gate1 gate2 gate3 : LC ℤ}
    {value1 value2 value3 : AffineSlope.Rep} :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (AffineSlope.selectGated3Rep width outBound description
        gate1 gate2 gate3 value1 value2 value3)
    ⦃⇓ out => ⌜Gated3Spec ρ gate1 gate2 gate3 value1 value2 value3 out⌝⦄ := by
  mvcgen [AffineSlope.selectGated3Rep, Gated3Spec]
  intro bits
  mvcgen
  rename_i out hout hgate1 hgate2 hgate3
  constructor
  · intro hg
    unfold Modular.Lazy.evalZMod
    have heq := hgate1.2
    simp [hg] at heq
    rw [show out.intVal.eval ρ.int = value1.intVal.eval ρ.int by
      omega]
  · constructor
    · intro hg
      unfold Modular.Lazy.evalZMod
      have heq := hgate2.2
      simp [hg] at heq
      rw [show out.intVal.eval ρ.int = value2.intVal.eval ρ.int by omega]
    · intro hg
      unfold Modular.Lazy.evalZMod
      have heq := hgate3.2
      simp [hg] at heq
      rw [show out.intVal.eval ρ.int = value3.intVal.eval ρ.int by omega]

@[spec] theorem selectGated4Rep_sound {width outBound : Nat}
    {description : String} {gate1 gate2 gate3 gate4 : LC ℤ}
    {value1 value2 value3 value4 : AffineSlope.Rep} :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (AffineSlope.selectGated4Rep width outBound description
        gate1 gate2 gate3 gate4 value1 value2 value3 value4)
    ⦃⇓ out => ⌜Gated4Spec ρ gate1 gate2 gate3 gate4
      value1 value2 value3 value4 out⌝⦄ := by
  mvcgen [AffineSlope.selectGated4Rep, Gated4Spec]
  intro bits
  mvcgen
  rename_i out hout hgate1 hgate2 hgate3 hgate4
  constructor
  · intro hg
    unfold Modular.Lazy.evalZMod
    have heq := hgate1.2
    simp [hg] at heq
    rw [show out.intVal.eval ρ.int = value1.intVal.eval ρ.int by omega]
  · constructor
    · intro hg
      unfold Modular.Lazy.evalZMod
      have heq := hgate2.2
      simp [hg] at heq
      rw [show out.intVal.eval ρ.int = value2.intVal.eval ρ.int by omega]
    · constructor
      · intro hg
        unfold Modular.Lazy.evalZMod
        have heq := hgate3.2
        simp [hg] at heq
        rw [show out.intVal.eval ρ.int = value3.intVal.eval ρ.int by omega]
      · intro hg
        unfold Modular.Lazy.evalZMod
        have heq := hgate4.2
        simp [hg] at heq
        rw [show out.intVal.eval ρ.int = value4.intVal.eval ρ.int by omega]

theorem selectGated3Rep_complete {width outBound limit : Nat}
    {description : String} {gate1 gate2 gate3 : LC ℤ}
    {value1 value2 value3 : AffineSlope.Rep}
    (hcases : Gated3Cases ρ gate1 gate2 gate3)
    (hvalue1 : value1.Valid ρ)
    (hvalue1Fit : value1.intVal.eval ρ.int < limit)
    (hvalue2 : value2.Valid ρ)
    (hvalue2Fit : value2.intVal.eval ρ.int < limit)
    (hvalue3 : value3.Valid ρ)
    (hvalue3Fit : value3.intVal.eval ρ.int < limit)
    (hwidth : limit ≤ 2 ^ width)
    (hbound : limit ≤ outBound * base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectGated3Rep width outBound description
        gate1 gate2 gate3 value1 value2 value3)
    ⦃⇓ out => ⌜Gated3Spec ρ gate1 gate2 gate3 value1 value2 value3 out ∧
      out.Valid ρ ∧ out.intVal.eval ρ.int < limit ∧
      out.bound = outBound⌝⦄ := by
  mvcgen [AffineSlope.selectGated3Rep]
  let value := if gate1.eval ρ.int = 1 then value1.intVal.eval ρ.int
    else if gate2.eval ρ.int = 1 then value2.intVal.eval ρ.int
    else value3.intVal.eval ρ.int
  let bits : Vector Bool width := Vector.ofFn fun i => value.toNat.testBit i.val
  refine ⟨bits, ?_, ?_⟩
  · rcases hcases with h | h | h <;>
      simp [WF.interpHint, WF.evalArgs, bits, value, h, hvalue1.1,
        hvalue2.1, hvalue3.1]
  · mvcgen
    rename_i out hout
    have hvalue0 : 0 ≤ value := by
      rcases hcases with h | h | h <;>
        simp [value, h, hvalue1.1, hvalue2.1, hvalue3.1]
    have hvalueFit : value < limit := by
      rcases hcases with h | h | h <;>
        simp [value, h, hvalue1Fit, hvalue2Fit, hvalue3Fit]
    have hfit : value.toNat < 2 ^ width := by
      apply (Int.toNat_lt hvalue0).2
      exact hvalueFit.trans_le (by exact_mod_cast hwidth)
    have hword :
        (Word.eval ρ.bool { bitsLE := Vector.map LC.ofConst bits }).toNat =
          value.toNat := by
      rw [show Vector.map LC.ofConst bits =
          Vector.ofFn (n := width) fun i =>
            LC.ofConst (value.toNat.testBit i.val) by
        ext i
        simp [bits]]
      exact Modular.Aux.constWord_eval_toNat value.toNat hfit ρ
    have houtVal : out.intVal.eval ρ.int = value := by
      rw [U.Rel.intVal hout, hword, Int.toNat_of_nonneg hvalue0]
    constructor
    · rcases hcases with h | h | h <;> simp [h, value, houtVal]
    · mvcgen
      constructor
      · rcases hcases with h | h | h <;> simp [h, value, houtVal]
      · mvcgen
        constructor
        · rcases hcases with h | h | h <;> simp [h, value, houtVal]
        · mvcgen
          constructor
          · rcases hcases with h | h | h <;>
              simp [Gated3Spec, Modular.Lazy.evalZMod, h, value, houtVal]
          · refine ⟨⟨U.intVal_nonneg out hout.1, ?_⟩, ?_⟩
            · rw [houtVal]
              exact hvalueFit.trans_le (by exact_mod_cast hbound)
            · simpa [houtVal] using hvalueFit

theorem selectGated4Rep_complete {width outBound limit : Nat}
    {description : String} {gate1 gate2 gate3 gate4 : LC ℤ}
    {value1 value2 value3 value4 : AffineSlope.Rep}
    (hcases : Gated4Cases ρ gate1 gate2 gate3 gate4)
    (hvalue1 : value1.Valid ρ)
    (hvalue1Fit : value1.intVal.eval ρ.int < limit)
    (hvalue2 : value2.Valid ρ)
    (hvalue2Fit : value2.intVal.eval ρ.int < limit)
    (hvalue3 : value3.Valid ρ)
    (hvalue3Fit : value3.intVal.eval ρ.int < limit)
    (hvalue4 : value4.Valid ρ)
    (hvalue4Fit : value4.intVal.eval ρ.int < limit)
    (hwidth : limit ≤ 2 ^ width)
    (hbound : limit ≤ outBound * base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectGated4Rep width outBound description
        gate1 gate2 gate3 gate4 value1 value2 value3 value4)
    ⦃⇓ out => ⌜Gated4Spec ρ gate1 gate2 gate3 gate4
      value1 value2 value3 value4 out ∧ out.Valid ρ ∧
      out.intVal.eval ρ.int < limit ∧ out.bound = outBound⌝⦄ := by
  mvcgen [AffineSlope.selectGated4Rep]
  let value := if gate1.eval ρ.int = 1 then value1.intVal.eval ρ.int
    else if gate2.eval ρ.int = 1 then value2.intVal.eval ρ.int
    else if gate3.eval ρ.int = 1 then value3.intVal.eval ρ.int
    else value4.intVal.eval ρ.int
  let bits : Vector Bool width := Vector.ofFn fun i => value.toNat.testBit i.val
  refine ⟨bits, ?_, ?_⟩
  · rcases hcases with h | h | h | h <;>
      simp [WF.interpHint, WF.evalArgs, bits, value, h, hvalue1.1,
        hvalue2.1, hvalue3.1, hvalue4.1]
  · mvcgen
    rename_i out hout
    have hvalue0 : 0 ≤ value := by
      rcases hcases with h | h | h | h <;>
        simp [value, h, hvalue1.1, hvalue2.1, hvalue3.1, hvalue4.1]
    have hvalueFit : value < limit := by
      rcases hcases with h | h | h | h <;>
        simp [value, h, hvalue1Fit, hvalue2Fit, hvalue3Fit, hvalue4Fit]
    have hfit : value.toNat < 2 ^ width := by
      apply (Int.toNat_lt hvalue0).2
      exact hvalueFit.trans_le (by exact_mod_cast hwidth)
    have hword :
        (Word.eval ρ.bool { bitsLE := Vector.map LC.ofConst bits }).toNat =
          value.toNat := by
      rw [show Vector.map LC.ofConst bits =
          Vector.ofFn (n := width) fun i =>
            LC.ofConst (value.toNat.testBit i.val) by
        ext i
        simp [bits]]
      exact Modular.Aux.constWord_eval_toNat value.toNat hfit ρ
    have houtVal : out.intVal.eval ρ.int = value := by
      rw [U.Rel.intVal hout, hword, Int.toNat_of_nonneg hvalue0]
    constructor
    · rcases hcases with h | h | h | h <;> simp [h, value, houtVal]
    · mvcgen
      constructor
      · rcases hcases with h | h | h | h <;> simp [h, value, houtVal]
      · mvcgen
        constructor
        · rcases hcases with h | h | h | h <;> simp [h, value, houtVal]
        · mvcgen
          constructor
          · rcases hcases with h | h | h | h <;> simp [h, value, houtVal]
          · mvcgen
            constructor
            · rcases hcases with h | h | h | h <;>
                simp [Gated4Spec, Modular.Lazy.evalZMod, h, value, houtVal]
            · refine ⟨⟨U.intVal_nonneg out hout.1, ?_⟩, ?_⟩
              · rw [houtVal]
                exact hvalueFit.trans_le (by exact_mod_cast hbound)
              · simpa [houtVal] using hvalueFit
def AddControlSpec (ρ : WF.Valuation) (P Q : AffineSlope.Point)
    (control : AffineSlope.AddControl) : Prop :=
  Modular.Lazy.ZeroTestZModSpec base ρ
      (AffineSlope.sub Q.X P.X) control.sameX ∧
    Modular.Lazy.ZeroTestZModSpec base ρ
      (AffineSlope.add P.Y Q.Y) control.oppositeY ∧
    AffineSlope.AndBitSpec ρ (LC.ofConst 1 - P.infinity)
      (LC.ofConst 1 - Q.infinity) control.finite ∧
    ∃ doubleKind genericCase : LC ℤ,
      AffineSlope.AndBitSpec ρ control.sameX
        (LC.ofConst 1 - control.oppositeY) doubleKind ∧
      AffineSlope.AndBitSpec ρ control.finite doubleKind
        control.doubleCase ∧
      AffineSlope.AndBitSpec ρ control.finite
        (LC.ofConst 1 - control.sameX) genericCase ∧
      control.active.eval ρ.int =
        control.doubleCase.eval ρ.int + genericCase.eval ρ.int

theorem AddControlSpec.active_bit {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl}
    (h : AddControlSpec ρ P Q control) :
    control.active.eval ρ.int = 0 ∨ control.active.eval ρ.int = 1 := by
  rcases h with ⟨hsame, _, _, doubleKind, genericCase,
    hdoubleKind, hdoubleCase, hgenericCase, hactive⟩
  rcases hsame.1 with hsame | hsame
  · have hdoubleKind0 : doubleKind.eval ρ.int = 0 := by
      rw [hdoubleKind.1]
      simp [hsame]
    have hdoubleCase0 : control.doubleCase.eval ρ.int = 0 := by
      rw [hdoubleCase.1, hdoubleKind0]
      simp
    rw [hactive, hdoubleCase0]
    simpa using hgenericCase.2
  · have hgenericCase0 : genericCase.eval ρ.int = 0 := by
      rw [hgenericCase.1]
      simp [hsame]
    rw [hactive, hgenericCase0]
    simpa using hdoubleCase.2

theorem AddControlSpec.slope_gated_cases {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl}
    (h : AddControlSpec ρ P Q control) :
    Gated3Cases ρ control.doubleCase
      (control.active - control.doubleCase) (LC.ofConst 1 - control.active) := by
  have hactiveBit := h.active_bit
  rcases h with ⟨_, _, _, _, genericCase, _, hdoubleCase,
    hgenericCase, hactive⟩
  rcases hactiveBit with ha | ha <;>
    rcases hdoubleCase.2 with hd | hd <;>
    rcases hgenericCase.2 with hg | hg <;>
    simp_all [Gated3Cases]

@[spec] theorem zeroTestBound4_sound {x : AffineSlope.Rep} :
    ⦃⌜True⌝⦄ Sound.interp ρ (AffineSlope.zeroTestBound4 x)
    ⦃⇓ z => ⌜Modular.Lazy.ZeroTestZModSpec base ρ x z⌝⦄ := by
  mvcgen [AffineSlope.zeroTestBound4, AffineSlope.zeroTestBound4Prepare,
    AffineSlope.zeroTestBound4Hint, AffineSlope.zeroTestBound4DecodeZero,
    AffineSlope.zeroTestBound4DecodeInverse,
    AffineSlope.zeroTestBound4InverseCheck,
    AffineSlope.zeroTestBound4ZeroCheck,
    Modular.Lazy.ZeroTestZModSpec]
  intro bits
  mvcgen
  intro inverseQBits
  mvcgen
  intro zeroQBits
  mvcgen
  rename_i zWord hzWord inverse hInverse inverseQ hInverseQ
    hInverseEq zeroQ hZeroQ hZeroEq
  have hzBit : zWord.intBits[0].eval ρ.int = 0 ∨
      zWord.intBits[0].eval ρ.int = 1 := by
    have hz := hzWord.1 (0 : Fin 1)
    cases hb : zWord.bits.bitsLE[0].eval ρ.bool <;>
      simp [hb] at hz
    · exact Or.inl hz
    · exact Or.inr hz
  have hmul' : Modular.Lazy.evalZMod base x ρ *
      ((inverse.intVal.eval ρ.int : Int) : ZMod base.modulus) =
      1 - ((zWord.intBits[0].eval ρ.int : Int) : ZMod base.modulus) := by
    have hcast := congrArg (fun z : Int => (z : ZMod base.modulus)) hInverseEq
    simpa [Modular.Lazy.evalZMod, LC.eval_sub, LC.eval_add,
      LC.eval_nsmul, LC.eval_ofConst, Int.cast_sub, Int.cast_add,
      Int.cast_one] using hcast
  have hfinalCast :=
    congrArg (fun z : Int => (z : ZMod base.modulus)) hZeroEq
  simp only [LC.eval_nsmul, nsmul_eq_mul, Int.cast_mul,
    Int.cast_natCast, ZMod.natCast_self, zero_mul] at hfinalCast
  refine ⟨hzBit, ?_, ?_⟩
  · constructor
    · intro hz
      simpa [Modular.Lazy.evalZMod, hz] using hfinalCast
    · intro hx
      rcases hzBit with hz | hz
      · have hzeroOne : (0 : ZMod base.modulus) = 1 := by
          simpa [hx, hz] using hmul'
        exact (zero_ne_one hzeroOne).elim
      · exact hz
  · rcases hzBit with hz | hz
    · have hx0 : Modular.Lazy.evalZMod base x ρ ≠ 0 := by
        intro hx
        have hzeroOne : (0 : ZMod base.modulus) = 1 := by
          simpa [hx, hz] using hmul'
        exact zero_ne_one hzeroOne
      simp [hz, hx0]
    · have hx0 : Modular.Lazy.evalZMod base x ρ = 0 := by
        simpa [Modular.Lazy.evalZMod, hz] using hfinalCast
      simp [hz, hx0]

@[spec] theorem zeroTestCanonicalSum_sound {x : AffineSlope.Rep} :
    ⦃⌜True⌝⦄ Sound.interp ρ (AffineSlope.zeroTestCanonicalSum x)
    ⦃⇓ z => ⌜Modular.Lazy.ZeroTestZModSpec base ρ x z⌝⦄ := by
  mvcgen [AffineSlope.zeroTestCanonicalSum,
    AffineSlope.zeroTestBound4Prepare,
    AffineSlope.zeroTestBound4Hint,
    AffineSlope.zeroTestBound4DecodeZero,
    AffineSlope.zeroTestBound4DecodeInverse,
    AffineSlope.zeroTestCanonicalSumInverse,
    AffineSlope.zeroTestCanonicalSumInverseQHint,
    AffineSlope.zeroTestCanonicalSumInverseQDecode,
    AffineSlope.zeroTestCanonicalSumInverseCheck,
    AffineSlope.zeroTestCanonicalSumZero,
    AffineSlope.zeroTestCanonicalSumZeroQHint,
    AffineSlope.zeroTestCanonicalSumZeroQDecode,
    AffineSlope.zeroTestCanonicalSumZeroCheck,
    Modular.Lazy.ZeroTestZModSpec]
  intro bits
  mvcgen
  intro inverseQBits
  mvcgen
  intro zeroQBits
  mvcgen
  rename_i zWord hzWord inverse hInverse inverseQ hInverseQ
    hInverseEq zeroQ hZeroQ hZeroEq
  have hzBit : zWord.intBits[0].eval ρ.int = 0 ∨
      zWord.intBits[0].eval ρ.int = 1 := by
    have hz := hzWord.1 (0 : Fin 1)
    cases hb : zWord.bits.bitsLE[0].eval ρ.bool <;>
      simp [hb] at hz
    · exact Or.inl hz
    · exact Or.inr hz
  have hmul' : Modular.Lazy.evalZMod base x ρ *
      ((inverse.intVal.eval ρ.int : Int) : ZMod base.modulus) =
      1 - ((zWord.intBits[0].eval ρ.int : Int) : ZMod base.modulus) := by
    have hcast := congrArg (fun z : Int => (z : ZMod base.modulus)) hInverseEq
    simpa [Modular.Lazy.evalZMod, LC.eval_sub, LC.eval_add,
      LC.eval_nsmul, LC.eval_ofConst, Int.cast_sub, Int.cast_add,
      Int.cast_one] using hcast
  have hfinalCast :=
    congrArg (fun z : Int => (z : ZMod base.modulus)) hZeroEq
  simp only [LC.eval_nsmul, nsmul_eq_mul, Int.cast_mul,
    Int.cast_natCast, ZMod.natCast_self, zero_mul] at hfinalCast
  refine ⟨hzBit, ?_, ?_⟩
  · constructor
    · intro hz
      simpa [Modular.Lazy.evalZMod, hz] using hfinalCast
    · intro hx
      rcases hzBit with hz | hz
      · have hzeroOne : (0 : ZMod base.modulus) = 1 := by
          simpa [hx, hz] using hmul'
        exact (zero_ne_one hzeroOne).elim
      · exact hz
  · rcases hzBit with hz | hz
    · have hx0 : Modular.Lazy.evalZMod base x ρ ≠ 0 := by
        intro hx
        have hzeroOne : (0 : ZMod base.modulus) = 1 := by
          simpa [hx, hz] using hmul'
        exact zero_ne_one hzeroOne
      simp [hz, hx0]
    · have hx0 : Modular.Lazy.evalZMod base x ρ = 0 := by
        simpa [Modular.Lazy.evalZMod, hz] using hfinalCast
      simp [hz, hx0]

@[spec] theorem zeroTestBound4_complete {x : AffineSlope.Rep}
    (hx : x.Valid ρ) (hbound : x.bound = 4) :
    ⦃⌜True⌝⦄ Complete.interp ρ (AffineSlope.zeroTestBound4 x)
    ⦃⇓ z => ⌜Modular.Lazy.ZeroTestZModSpec base ρ x z⌝⦄ := by
  mvcgen [AffineSlope.zeroTestBound4, AffineSlope.zeroTestBound4Prepare,
    AffineSlope.zeroTestBound4Hint, AffineSlope.zeroTestBound4DecodeZero,
    AffineSlope.zeroTestBound4DecodeInverse,
    AffineSlope.zeroTestBound4InverseCheck,
    AffineSlope.zeroTestBound4ZeroCheck]
  let a := x.intVal.eval ρ.int
  have haNat : (a.toNat : Int) = a := Int.toNat_of_nonneg hx.1
  let d := a.toNat % base.modulus
  let isZero := d = 0
  let inverse := Nat.gcdA d base.modulus % (base.modulus : Int)
  have hpInt0 : (base.modulus : Int) ≠ 0 := by
    exact_mod_cast base.positive.ne'
  have hinverse0 : 0 ≤ inverse := by
    exact Int.emod_nonneg _ hpInt0
  have hinverseLtInt : inverse < base.modulus := by
    exact Int.emod_lt_of_pos _ (by exact_mod_cast base.positive)
  have hinverseLt : inverse.toNat < base.modulus :=
    (Int.toNat_lt hinverse0).2 hinverseLtInt
  have hinverseFit : inverse.toNat < 2 ^ 256 :=
    hinverseLt.trans_le base.fits
  let bits : Vector Bool 257 := Vector.ofFn fun i =>
    if hi : i.val = 0 then isZero
    else inverse.toNat.testBit (i.val - 1)
  have inverseWordEval :
      (Word.eval ρ.bool {
        bitsLE := Vector.ofFn (n := 256) fun i =>
          (Vector.map LC.ofConst bits)[i.val + 1]'(by omega)
      }).toNat = inverse.toNat := by
    simpa [bits] using
      Modular.Aux.constWord_eval_toNat inverse.toNat hinverseFit ρ
  have invValid (inv : U 256) (hinv : U.Rel ρ inv
      (Word.eval ρ.bool {
        bitsLE := Vector.ofFn fun i =>
          (Vector.map LC.ofConst bits)[i.val + 1]'(by omega) })) :
      (Modular.Lazy.ofElem base { val := inv }).Valid ρ := by
    apply Modular.Lazy.ofElem_valid
    refine ⟨hinv.1, ?_⟩
    rw [U.Rel.intVal hinv, inverseWordEval]
    exact_mod_cast hinverseLt
  have zBitEval (z : U 1) (hz : U.Rel ρ z
      (Word.eval ρ.bool {
        bitsLE := Vector.ofFn (n := 1) fun _ =>
          (Vector.map LC.ofConst bits)[0] })) :
      z.intBits[0].eval ρ.int = if isZero then 1 else 0 := by
    have hzInt := U.Rel.intVal hz
    have hword :
        (Word.eval ρ.bool {
          bitsLE := Vector.ofFn (n := 1) fun _ =>
            (Vector.map LC.ofConst bits)[0] }).toNat =
          if isZero then 1 else 0 := by
      by_cases hzero : isZero
      · simp [Word.eval, BitVec.toNat_ofFnLE, bits, isZero, hzero,
          Nat.ofBits]
        decide
      · simp [Word.eval, BitVec.toNat_ofFnLE, bits, isZero, hzero,
          Nat.ofBits]
        decide
    have hzIntVal : z.intVal.eval ρ.int =
        if isZero then 1 else 0 := hzInt.trans (by exact_mod_cast hword)
    simpa [U.intVal] using hzIntVal
  have zeroMulSpec (z : U 1) (hz : U.Rel ρ z
      (Word.eval ρ.bool {
        bitsLE := Vector.ofFn (n := 1) fun _ =>
          (Vector.map LC.ofConst bits)[0] }))
      (inv : U 256) (hinv : U.Rel ρ inv
      (Word.eval ρ.bool {
        bitsLE := Vector.ofFn fun i =>
          (Vector.map LC.ofConst bits)[i.val + 1]'(by omega) })) :
      Modular.Lazy.AssertMulEqZModSpec base ρ x
        (Modular.Lazy.ofElem base { val := inv })
        { intVal := (LC.ofConst 1 : LC Int) - z.intBits[0],
          bound := 1 } := by
    have hzBit := zBitEval z hz
    have hinvVal : inv.intVal.eval ρ.int = inverse.toNat := by
      rw [U.Rel.intVal hinv, inverseWordEval]
    have haZ : (a : ZMod base.modulus) = (d : ZMod base.modulus) := by
      have haCast : (a : ZMod base.modulus) =
          (a.toNat : ZMod base.modulus) := by
        rw [← Int.cast_natCast]
        exact (congrArg (Int.castRingHom (ZMod base.modulus)) haNat).symm
      rw [haCast]
      simp [d]
    unfold Modular.Lazy.AssertMulEqZModSpec Modular.Lazy.evalZMod
      Modular.Lazy.ofElem
    rw [hinvVal]
    simp only [LC.eval_sub, LC.eval_ofConst]
    have hmain : (a : ZMod base.modulus) *
        (inverse.toNat : ZMod base.modulus) =
        ((1 - z.intBits[0].eval ρ.int : Int) : ZMod base.modulus) := by
      rw [haZ, hzBit]
      by_cases hzero : d = 0
      · simp [isZero, hzero]
      · have hgcd : Nat.gcd d base.modulus = 1 := by
          rw [Nat.gcd_comm]
          exact (Nat.coprime_of_lt_prime hzero
            (Nat.mod_lt _ base.positive) Fact.out).gcd_eq_one
        have hinverseCast : (inverse.toNat : ZMod base.modulus) =
            (Nat.gcdA d base.modulus : ZMod base.modulus) := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg hinverse0]
          dsimp [inverse]
          simp
        rw [hinverseCast]
        have hbezout := Nat.gcd_eq_gcd_ab d base.modulus
        have hcast := congrArg
          (Int.castRingHom (ZMod base.modulus)) hbezout
        simpa [isZero, hzero, hgcd, mul_comm] using hcast.symm
    have hinverseCastZ : (inverse.toNat : ZMod base.modulus) =
        (inverse : ZMod base.modulus) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hinverse0]
    rw [hinverseCastZ] at hmain
    simpa [a, Int.cast_sub, Int.cast_one, max_eq_left hinverse0] using hmain
  refine ⟨bits, ?_, ?_⟩
  · simp [WF.interpHint, WF.evalArgs, hx.1, a, d, isZero, inverse, bits]
  · mvcgen <;> first
      | exact invValid _ (by assumption)
      | skip
    rename_i z hz inv hinv
    have hzVal := zBitEval z hz
    have hspec := zeroMulSpec z hz inv hinv
    let shifted : Int := a * inverse.toNat + base.modulus -
      (1 - z.intBits[0].eval ρ.int)
    have hshifted : 0 ≤ shifted := by
      have hprod : 0 ≤ a * (inverse.toNat : Int) :=
        mul_nonneg hx.1 (by positivity)
      have hp : (0 : Int) < base.modulus := by
        exact_mod_cast base.positive
      have hz01 : z.intBits[0].eval ρ.int = 0 ∨
          z.intBits[0].eval ρ.int = 1 := by
        rw [hzVal]
        split <;> simp
      rcases hz01 with hz0 | hz1
      · dsimp [shifted]
        rw [hz0]
        omega
      · dsimp [shifted]
        rw [hz1]
        omega
    have hshiftDvd : (base.modulus : Int) ∣ shifted := by
      unfold Modular.Lazy.AssertMulEqZModSpec Modular.Lazy.evalZMod
        Modular.Lazy.ofElem at hspec
      have hinvVal : inv.intVal.eval ρ.int = inverse.toNat := by
        rw [U.Rel.intVal hinv, inverseWordEval]
      rw [hinvVal] at hspec
      simp only [LC.eval_sub, LC.eval_ofConst] at hspec
      have hmod : ((a * inverse.toNat : Int) : ZMod base.modulus) =
          ((1 - z.intBits[0].eval ρ.int : Int) : ZMod base.modulus) := by
        simpa [a, Int.cast_sub, Int.cast_one] using hspec
      have hdvdDiff : (base.modulus : Int) ∣
          (1 - z.intBits[0].eval ρ.int) - a * inverse.toNat :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hmod
      have hdvdNeg : (base.modulus : Int) ∣
          a * inverse.toNat - (1 - z.intBits[0].eval ρ.int) := by
        simpa [neg_sub] using dvd_neg.mpr hdvdDiff
      rcases hdvdNeg with ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      calc
        shifted = a * inverse.toNat -
            (1 - z.intBits[0].eval ρ.int) + base.modulus := by
          dsimp [shifted]
          ring
        _ = (base.modulus : Int) * k + base.modulus := by rw [hk]
        _ = (base.modulus : Int) * (k + 1) := by ring
    let inverseQuotient := shifted.toNat / base.modulus
    let inverseQBits : Vector Bool 258 := Vector.ofFn fun i =>
      inverseQuotient.testBit i.val
    have inverseWordEval' :
        (Word.eval ρ.bool {
          bitsLE := Vector.ofFn (n := 256) fun i =>
            LC.ofConst bits[i.val + 1]
        }).toNat = inverse.toNat := by
      simpa using inverseWordEval
    refine ⟨inverseQBits, ?_, ?_⟩
    · have hshifted' : 0 ≤ a * inverse + base.modulus -
          (1 - if isZero then 1 else 0) := by
        simpa [shifted, Int.toNat_of_nonneg hinverse0, hzVal] using hshifted
      have hcond : 1 ≤ a * inverse + base.modulus +
          (if isZero then 1 else 0) := by omega
      simp [WF.interpHint, WF.evalArgs, a, inverseWordEval,
        inverseWordEval', U.Rel.intVal hinv, hzVal,
        Int.toNat_of_nonneg hinverse0, inverseQBits, inverseQuotient, hcond]
      apply Vector.ext
      intro i
      simp [shifted, Int.toNat_of_nonneg hinverse0, hzVal]
      intro _
      rfl
    · mvcgen
      rename_i inverseQ hInverseQ
      have hshiftEq : (shifted.toNat : Int) = shifted :=
        Int.toNat_of_nonneg hshifted
      have hqSmall : inverseQuotient < 4 * base.modulus + 1 := by
        dsimp [inverseQuotient]
        apply (Nat.div_lt_iff_lt_mul base.positive).2
        apply (Int.toNat_lt hshifted).2
        have haUpper : a < 4 * base.modulus := by
          simpa [hbound] using hx.2
        have hinvUpper : (inverse.toNat : Int) < base.modulus := by
          exact_mod_cast hinverseLt
        have hp : (0 : Int) < base.modulus := by
          exact_mod_cast base.positive
        have hprodUpper : a * (inverse.toNat : Int) <
            (4 * base.modulus : Int) * base.modulus :=
          (mul_le_mul_of_nonneg_left hinvUpper.le hx.1).trans_lt
            (mul_lt_mul_of_pos_right haUpper hp)
        have hz01 : z.intBits[0].eval ρ.int = 0 ∨
            z.intBits[0].eval ρ.int = 1 := by
          rw [hzVal]
          split <;> simp
        rcases hz01 with hz0 | hz1
        · dsimp [shifted]
          rw [hz0]
          push_cast
          nlinarith
        · dsimp [shifted]
          rw [hz1]
          push_cast
          nlinarith
      have hqFit : inverseQuotient < 2 ^ 258 := by
        calc
          inverseQuotient < 4 * base.modulus + 1 := hqSmall
          _ < 2 ^ 258 := by
            set_option exponentiation.threshold 300 in
              norm_num [base, baseModulus]
      have hqWord :
          (Word.eval ρ.bool {
            bitsLE := Vector.map LC.ofConst inverseQBits
          }).toNat = inverseQuotient := by
        rw [show Vector.map LC.ofConst inverseQBits =
            Vector.ofFn fun i =>
              LC.ofConst (inverseQuotient.testBit i.val) by
          ext i
          simp [inverseQBits]]
        exact Modular.Aux.constWord_eval_toNat inverseQuotient hqFit ρ
      have hqVal : inverseQ.intVal.eval ρ.int = inverseQuotient := by
        rw [U.Rel.intVal hInverseQ, hqWord]
      have hshiftDvdNat : base.modulus ∣ shifted.toNat := by
        rcases hshiftDvd with ⟨k, hk⟩
        have hk0 : 0 ≤ k := by
          have hp : (0 : Int) < base.modulus := by
            exact_mod_cast base.positive
          rw [hk] at hshifted
          nlinarith
        refine ⟨k.toNat, ?_⟩
        apply Int.ofNat_inj.mp
        calc
          (shifted.toNat : Int) = shifted := hshiftEq
          _ = (base.modulus : Int) * k := hk
          _ = (base.modulus : Int) * (k.toNat : Int) := by
            rw [Int.toNat_of_nonneg hk0]
          _ = ((base.modulus * k.toNat : Nat) : Int) := by norm_num
      have hdecomp : (shifted.toNat : Int) =
          (base.modulus : Int) * inverseQuotient := by
        have hnat := Nat.mod_add_div shifted.toNat base.modulus
        rw [Nat.mod_eq_zero_of_dvd hshiftDvdNat] at hnat
        simp only [zero_add] at hnat
        dsimp [inverseQuotient]
        exact_mod_cast hnat.symm
      constructor
      · simp only [LC.eval_add, LC.eval_sub, LC.eval_nsmul,
          LC.eval_ofConst, nsmul_eq_mul, hqVal]
        have hinvVal : inv.intVal.eval ρ.int = inverse.toNat := by
          rw [U.Rel.intVal hinv, inverseWordEval]
        rw [hinvVal]
        calc
          a * (inverse.toNat : Int) =
              shifted - base.modulus +
                (1 - z.intBits[0].eval ρ.int) := by
            dsimp [shifted]
            ring
          _ = (shifted.toNat : Int) - base.modulus +
                (1 - z.intBits[0].eval ρ.int) := by rw [hshiftEq]
          _ = (base.modulus : Int) * inverseQuotient - base.modulus +
                (1 - z.intBits[0].eval ρ.int) := by rw [hdecomp]
          _ = 1 - z.intBits[0].eval ρ.int +
                (base.modulus : Int) * inverseQuotient - base.modulus := by ring
      · mvcgen
        let product := (z.intBits[0].eval ρ.int * a).toNat
        let quotient := product / base.modulus
        let zeroQBits : Vector Bool 2 := Vector.ofFn fun i =>
          quotient.testBit i.val
        refine ⟨zeroQBits, ?_, ?_⟩
        · rfl
        · mvcgen
          rename_i zeroQ hZeroQ
          have hproduct0 : 0 ≤ z.intBits[0].eval ρ.int * a := by
            rw [hzVal]
            split
            · simpa using hx.1
            · simp
          have hproductEq : (product : Int) =
              z.intBits[0].eval ρ.int * a :=
            Int.toNat_of_nonneg hproduct0
          have hqSmall : quotient < 4 := by
            dsimp [quotient, product]
            apply (Nat.div_lt_iff_lt_mul base.positive).2
            apply (Int.toNat_lt hproduct0).2
            have hp : (0 : Int) < base.modulus := by
              exact_mod_cast base.positive
            rw [hzVal]
            split
            · simpa [hbound] using hx.2
            · simp
              nlinarith
          have hqFit : quotient < 2 ^ 2 := by simpa using hqSmall
          have hqWord :
              (Word.eval ρ.bool {
                bitsLE := Vector.map LC.ofConst zeroQBits
              }).toNat = quotient := by
            rw [show Vector.map LC.ofConst zeroQBits =
                Vector.ofFn fun i => LC.ofConst (quotient.testBit i.val) by
              ext i
              simp [zeroQBits]]
            exact Modular.Aux.constWord_eval_toNat quotient hqFit ρ
          have hqVal : zeroQ.intVal.eval ρ.int = quotient := by
            rw [U.Rel.intVal hZeroQ, hqWord]
          constructor
          · simp only [LC.eval_nsmul, nsmul_eq_mul, hqVal]
            change z.intBits[0].eval ρ.int * a =
              (base.modulus : Int) * quotient
            by_cases hzero : isZero
            · have hd0 : d = 0 := hzero
              have hmod : a.toNat % base.modulus = 0 := by
                simpa [d] using hd0
              have hdecomp := Nat.mod_add_div a.toNat base.modulus
              rw [hmod] at hdecomp
              simp only [zero_add] at hdecomp
              have hproduct : product = a.toNat := by
                simp [product, hzVal, hzero]
              have hquotient : quotient = a.toNat / base.modulus := by
                simp [quotient, hproduct]
              rw [hzVal, if_pos hzero, hquotient]
              simp only [one_mul]
              calc
                a = (a.toNat : Int) := haNat.symm
                _ = (base.modulus : Int) *
                    (a.toNat / base.modulus : Nat) := by
                  exact_mod_cast hdecomp.symm
            · have hproduct : product = 0 := by
                simp [product, hzVal, hzero]
              have hquotient : quotient = 0 := by
                simp [quotient, hproduct]
              rw [hzVal, if_neg hzero, hquotient]
              simp
          · have hxZero : Modular.Lazy.evalZMod base x ρ = 0 ↔
                isZero := by
              unfold Modular.Lazy.evalZMod
              have haCast : (a : ZMod base.modulus) =
                  (a.toNat : ZMod base.modulus) := by
                rw [← Int.cast_natCast]
                exact (congrArg
                  (Int.castRingHom (ZMod base.modulus)) haNat).symm
              change (a : ZMod base.modulus) = 0 ↔ isZero
              rw [haCast, ZMod.natCast_eq_zero_iff]
              simp [isZero, d, Nat.dvd_iff_mod_eq_zero]
            mvcgen
            unfold Modular.Lazy.ZeroTestZModSpec
            rw [hzVal]
            constructor
            · split <;> simp
            · constructor
              · rw [hxZero]
                by_cases hzero : isZero <;> simp [hzero]
              · by_cases hzero : isZero
                · have hxz : Modular.Lazy.evalZMod base x ρ = 0 :=
                    hxZero.mpr hzero
                  simp [hzero, hxz]
                · have hxz : Modular.Lazy.evalZMod base x ρ ≠ 0 :=
                    fun h => hzero (hxZero.mp h)
                  simp [hzero, hxz]

@[spec] theorem zeroTestCanonicalSum_complete {x : AffineSlope.Rep}
    (hx : x.Valid ρ)
    (hcanonicalSum : x.intVal.eval ρ.int < 2 * base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ (AffineSlope.zeroTestCanonicalSum x)
    ⦃⇓ z => ⌜Modular.Lazy.ZeroTestZModSpec base ρ x z⌝⦄ := by
  mvcgen [AffineSlope.zeroTestCanonicalSum,
    AffineSlope.zeroTestBound4Prepare,
    AffineSlope.zeroTestBound4Hint,
    AffineSlope.zeroTestBound4DecodeZero,
    AffineSlope.zeroTestBound4DecodeInverse,
    AffineSlope.zeroTestCanonicalSumInverse,
    AffineSlope.zeroTestCanonicalSumInverseQHint,
    AffineSlope.zeroTestCanonicalSumInverseQDecode,
    AffineSlope.zeroTestCanonicalSumInverseCheck,
    AffineSlope.zeroTestCanonicalSumZero,
    AffineSlope.zeroTestCanonicalSumZeroQHint,
    AffineSlope.zeroTestCanonicalSumZeroQDecode,
    AffineSlope.zeroTestCanonicalSumZeroCheck]
  let a := x.intVal.eval ρ.int
  have haNat : (a.toNat : Int) = a := Int.toNat_of_nonneg hx.1
  let d := a.toNat % base.modulus
  let isZero := d = 0
  let inverse := Nat.gcdA d base.modulus % (base.modulus : Int)
  have hpInt0 : (base.modulus : Int) ≠ 0 := by
    exact_mod_cast base.positive.ne'
  have hinverse0 : 0 ≤ inverse := by
    exact Int.emod_nonneg _ hpInt0
  have hinverseLtInt : inverse < base.modulus := by
    exact Int.emod_lt_of_pos _ (by exact_mod_cast base.positive)
  have hinverseLt : inverse.toNat < base.modulus :=
    (Int.toNat_lt hinverse0).2 hinverseLtInt
  have hinverseFit : inverse.toNat < 2 ^ 256 :=
    hinverseLt.trans_le base.fits
  let bits : Vector Bool 257 := Vector.ofFn fun i =>
    if hi : i.val = 0 then isZero
    else inverse.toNat.testBit (i.val - 1)
  have inverseWordEval :
      (Word.eval ρ.bool {
        bitsLE := Vector.ofFn (n := 256) fun i =>
          (Vector.map LC.ofConst bits)[i.val + 1]'(by omega)
      }).toNat = inverse.toNat := by
    simpa [bits] using
      Modular.Aux.constWord_eval_toNat inverse.toNat hinverseFit ρ
  have invValid (inv : U 256) (hinv : U.Rel ρ inv
      (Word.eval ρ.bool {
        bitsLE := Vector.ofFn fun i =>
          (Vector.map LC.ofConst bits)[i.val + 1]'(by omega) })) :
      (Modular.Lazy.ofElem base { val := inv }).Valid ρ := by
    apply Modular.Lazy.ofElem_valid
    refine ⟨hinv.1, ?_⟩
    rw [U.Rel.intVal hinv, inverseWordEval]
    exact_mod_cast hinverseLt
  have zBitEval (z : U 1) (hz : U.Rel ρ z
      (Word.eval ρ.bool {
        bitsLE := Vector.ofFn (n := 1) fun _ =>
          (Vector.map LC.ofConst bits)[0] })) :
      z.intBits[0].eval ρ.int = if isZero then 1 else 0 := by
    have hzInt := U.Rel.intVal hz
    have hword :
        (Word.eval ρ.bool {
          bitsLE := Vector.ofFn (n := 1) fun _ =>
            (Vector.map LC.ofConst bits)[0] }).toNat =
          if isZero then 1 else 0 := by
      by_cases hzero : isZero
      · simp [Word.eval, BitVec.toNat_ofFnLE, bits, isZero, hzero,
          Nat.ofBits]
        decide
      · simp [Word.eval, BitVec.toNat_ofFnLE, bits, isZero, hzero,
          Nat.ofBits]
        decide
    have hzIntVal : z.intVal.eval ρ.int =
        if isZero then 1 else 0 := hzInt.trans (by exact_mod_cast hword)
    simpa [U.intVal] using hzIntVal
  have zeroMulSpec (z : U 1) (hz : U.Rel ρ z
      (Word.eval ρ.bool {
        bitsLE := Vector.ofFn (n := 1) fun _ =>
          (Vector.map LC.ofConst bits)[0] }))
      (inv : U 256) (hinv : U.Rel ρ inv
      (Word.eval ρ.bool {
        bitsLE := Vector.ofFn fun i =>
          (Vector.map LC.ofConst bits)[i.val + 1]'(by omega) })) :
      Modular.Lazy.AssertMulEqZModSpec base ρ x
        (Modular.Lazy.ofElem base { val := inv })
        { intVal := (LC.ofConst 1 : LC Int) - z.intBits[0],
          bound := 1 } := by
    have hzBit := zBitEval z hz
    have hinvVal : inv.intVal.eval ρ.int = inverse.toNat := by
      rw [U.Rel.intVal hinv, inverseWordEval]
    have haZ : (a : ZMod base.modulus) = (d : ZMod base.modulus) := by
      have haCast : (a : ZMod base.modulus) =
          (a.toNat : ZMod base.modulus) := by
        rw [← Int.cast_natCast]
        exact (congrArg (Int.castRingHom (ZMod base.modulus)) haNat).symm
      rw [haCast]
      simp [d]
    unfold Modular.Lazy.AssertMulEqZModSpec Modular.Lazy.evalZMod
      Modular.Lazy.ofElem
    rw [hinvVal]
    simp only [LC.eval_sub, LC.eval_ofConst]
    have hmain : (a : ZMod base.modulus) *
        (inverse.toNat : ZMod base.modulus) =
        ((1 - z.intBits[0].eval ρ.int : Int) : ZMod base.modulus) := by
      rw [haZ, hzBit]
      by_cases hzero : d = 0
      · simp [isZero, hzero]
      · have hgcd : Nat.gcd d base.modulus = 1 := by
          rw [Nat.gcd_comm]
          exact (Nat.coprime_of_lt_prime hzero
            (Nat.mod_lt _ base.positive) Fact.out).gcd_eq_one
        have hinverseCast : (inverse.toNat : ZMod base.modulus) =
            (Nat.gcdA d base.modulus : ZMod base.modulus) := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg hinverse0]
          dsimp [inverse]
          simp
        rw [hinverseCast]
        have hbezout := Nat.gcd_eq_gcd_ab d base.modulus
        have hcast := congrArg
          (Int.castRingHom (ZMod base.modulus)) hbezout
        simpa [isZero, hzero, hgcd, mul_comm] using hcast.symm
    have hinverseCastZ : (inverse.toNat : ZMod base.modulus) =
        (inverse : ZMod base.modulus) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hinverse0]
    rw [hinverseCastZ] at hmain
    simpa [a, Int.cast_sub, Int.cast_one, max_eq_left hinverse0] using hmain
  refine ⟨bits, ?_, ?_⟩
  · simp [WF.interpHint, WF.evalArgs, hx.1, a, d, isZero, inverse, bits]
  · mvcgen <;> first
      | exact invValid _ (by assumption)
      | skip
    rename_i z hz inv hinv
    have hzVal := zBitEval z hz
    have hspec := zeroMulSpec z hz inv hinv
    let shifted : Int := a * inverse.toNat + base.modulus -
      (1 - z.intBits[0].eval ρ.int)
    have hshifted : 0 ≤ shifted := by
      have hprod : 0 ≤ a * (inverse.toNat : Int) :=
        mul_nonneg hx.1 (by positivity)
      have hp : (0 : Int) < base.modulus := by
        exact_mod_cast base.positive
      have hz01 : z.intBits[0].eval ρ.int = 0 ∨
          z.intBits[0].eval ρ.int = 1 := by
        rw [hzVal]
        split <;> simp
      rcases hz01 with hz0 | hz1
      · dsimp [shifted]
        rw [hz0]
        omega
      · dsimp [shifted]
        rw [hz1]
        omega
    have hshiftDvd : (base.modulus : Int) ∣ shifted := by
      unfold Modular.Lazy.AssertMulEqZModSpec Modular.Lazy.evalZMod
        Modular.Lazy.ofElem at hspec
      have hinvVal : inv.intVal.eval ρ.int = inverse.toNat := by
        rw [U.Rel.intVal hinv, inverseWordEval]
      rw [hinvVal] at hspec
      simp only [LC.eval_sub, LC.eval_ofConst] at hspec
      have hmod : ((a * inverse.toNat : Int) : ZMod base.modulus) =
          ((1 - z.intBits[0].eval ρ.int : Int) : ZMod base.modulus) := by
        simpa [a, Int.cast_sub, Int.cast_one] using hspec
      have hdvdDiff : (base.modulus : Int) ∣
          (1 - z.intBits[0].eval ρ.int) - a * inverse.toNat :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hmod
      have hdvdNeg : (base.modulus : Int) ∣
          a * inverse.toNat - (1 - z.intBits[0].eval ρ.int) := by
        simpa [neg_sub] using dvd_neg.mpr hdvdDiff
      rcases hdvdNeg with ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      calc
        shifted = a * inverse.toNat -
            (1 - z.intBits[0].eval ρ.int) + base.modulus := by
          dsimp [shifted]
          ring
        _ = (base.modulus : Int) * k + base.modulus := by rw [hk]
        _ = (base.modulus : Int) * (k + 1) := by ring
    let inverseQuotient := shifted.toNat / base.modulus
    let inverseQBits : Vector Bool 257 := Vector.ofFn fun i =>
      inverseQuotient.testBit i.val
    have inverseWordEval' :
        (Word.eval ρ.bool {
          bitsLE := Vector.ofFn (n := 256) fun i =>
            LC.ofConst bits[i.val + 1]
        }).toNat = inverse.toNat := by
      simpa using inverseWordEval
    refine ⟨inverseQBits, ?_, ?_⟩
    · have hshifted' : 0 ≤ a * inverse + base.modulus -
          (1 - if isZero then 1 else 0) := by
        simpa [shifted, Int.toNat_of_nonneg hinverse0, hzVal] using hshifted
      have hcond : 1 ≤ a * inverse + base.modulus +
          (if isZero then 1 else 0) := by omega
      simp [WF.interpHint, WF.evalArgs, a, inverseWordEval,
        inverseWordEval', U.Rel.intVal hinv, hzVal,
        Int.toNat_of_nonneg hinverse0, inverseQBits, inverseQuotient, hcond]
      apply Vector.ext
      intro i
      simp [shifted, Int.toNat_of_nonneg hinverse0, hzVal]
      intro _
      rfl
    · mvcgen
      rename_i inverseQ hInverseQ
      have hshiftEq : (shifted.toNat : Int) = shifted :=
        Int.toNat_of_nonneg hshifted
      have hqSmall : inverseQuotient < 2 * base.modulus + 1 := by
        dsimp [inverseQuotient]
        apply (Nat.div_lt_iff_lt_mul base.positive).2
        apply (Int.toNat_lt hshifted).2
        have haUpper : a < 2 * base.modulus := hcanonicalSum
        have hinvUpper : (inverse.toNat : Int) < base.modulus := by
          exact_mod_cast hinverseLt
        have hp : (0 : Int) < base.modulus := by
          exact_mod_cast base.positive
        have hprodUpper : a * (inverse.toNat : Int) <
            (2 * base.modulus : Int) * base.modulus :=
          (mul_le_mul_of_nonneg_left hinvUpper.le hx.1).trans_lt
            (mul_lt_mul_of_pos_right haUpper hp)
        have hz01 : z.intBits[0].eval ρ.int = 0 ∨
            z.intBits[0].eval ρ.int = 1 := by
          rw [hzVal]
          split <;> simp
        rcases hz01 with hz0 | hz1
        · dsimp [shifted]
          rw [hz0]
          push_cast
          nlinarith
        · dsimp [shifted]
          rw [hz1]
          push_cast
          nlinarith
      have hqFit : inverseQuotient < 2 ^ 257 := by
        calc
          inverseQuotient < 2 * base.modulus + 1 := hqSmall
          _ < 2 ^ 257 := by
            set_option exponentiation.threshold 300 in
              norm_num [base, baseModulus]
      have hqWord :
          (Word.eval ρ.bool {
            bitsLE := Vector.map LC.ofConst inverseQBits
          }).toNat = inverseQuotient := by
        rw [show Vector.map LC.ofConst inverseQBits =
            Vector.ofFn fun i =>
              LC.ofConst (inverseQuotient.testBit i.val) by
          ext i
          simp [inverseQBits]]
        exact Modular.Aux.constWord_eval_toNat inverseQuotient hqFit ρ
      have hqVal : inverseQ.intVal.eval ρ.int = inverseQuotient := by
        rw [U.Rel.intVal hInverseQ, hqWord]
      have hshiftDvdNat : base.modulus ∣ shifted.toNat := by
        rcases hshiftDvd with ⟨k, hk⟩
        have hk0 : 0 ≤ k := by
          have hp : (0 : Int) < base.modulus := by
            exact_mod_cast base.positive
          rw [hk] at hshifted
          nlinarith
        refine ⟨k.toNat, ?_⟩
        apply Int.ofNat_inj.mp
        calc
          (shifted.toNat : Int) = shifted := hshiftEq
          _ = (base.modulus : Int) * k := hk
          _ = (base.modulus : Int) * (k.toNat : Int) := by
            rw [Int.toNat_of_nonneg hk0]
          _ = ((base.modulus * k.toNat : Nat) : Int) := by norm_num
      have hdecomp : (shifted.toNat : Int) =
          (base.modulus : Int) * inverseQuotient := by
        have hnat := Nat.mod_add_div shifted.toNat base.modulus
        rw [Nat.mod_eq_zero_of_dvd hshiftDvdNat] at hnat
        simp only [zero_add] at hnat
        dsimp [inverseQuotient]
        exact_mod_cast hnat.symm
      constructor
      · simp only [LC.eval_add, LC.eval_sub, LC.eval_nsmul,
          LC.eval_ofConst, nsmul_eq_mul, hqVal]
        have hinvVal : inv.intVal.eval ρ.int = inverse.toNat := by
          rw [U.Rel.intVal hinv, inverseWordEval]
        rw [hinvVal]
        calc
          a * (inverse.toNat : Int) =
              shifted - base.modulus +
                (1 - z.intBits[0].eval ρ.int) := by
            dsimp [shifted]
            ring
          _ = (shifted.toNat : Int) - base.modulus +
                (1 - z.intBits[0].eval ρ.int) := by rw [hshiftEq]
          _ = (base.modulus : Int) * inverseQuotient - base.modulus +
                (1 - z.intBits[0].eval ρ.int) := by rw [hdecomp]
          _ = 1 - z.intBits[0].eval ρ.int +
                (base.modulus : Int) * inverseQuotient - base.modulus := by ring
      · mvcgen
        let product := (z.intBits[0].eval ρ.int * a).toNat
        let quotient := product / base.modulus
        let zeroQBits : Vector Bool 1 := Vector.ofFn fun i =>
          quotient.testBit i.val
        refine ⟨zeroQBits, ?_, ?_⟩
        · rfl
        · mvcgen
          rename_i zeroQ hZeroQ
          have hproduct0 : 0 ≤ z.intBits[0].eval ρ.int * a := by
            rw [hzVal]
            split
            · simpa using hx.1
            · simp
          have hproductEq : (product : Int) =
              z.intBits[0].eval ρ.int * a :=
            Int.toNat_of_nonneg hproduct0
          have hqSmall : quotient < 2 := by
            dsimp [quotient, product]
            apply (Nat.div_lt_iff_lt_mul base.positive).2
            apply (Int.toNat_lt hproduct0).2
            have hp : (0 : Int) < base.modulus := by
              exact_mod_cast base.positive
            rw [hzVal]
            split
            · simpa using hcanonicalSum
            · simp
              nlinarith
          have hqFit : quotient < 2 ^ 1 := by simpa using hqSmall
          have hqWord :
              (Word.eval ρ.bool {
                bitsLE := Vector.map LC.ofConst zeroQBits
              }).toNat = quotient := by
            rw [show Vector.map LC.ofConst zeroQBits =
                Vector.ofFn fun i => LC.ofConst (quotient.testBit i.val) by
              ext i
              simp [zeroQBits]]
            exact Modular.Aux.constWord_eval_toNat quotient hqFit ρ
          have hqVal : zeroQ.intVal.eval ρ.int = quotient := by
            rw [U.Rel.intVal hZeroQ, hqWord]
          constructor
          · simp only [LC.eval_nsmul, nsmul_eq_mul, hqVal]
            change z.intBits[0].eval ρ.int * a =
              (base.modulus : Int) * quotient
            by_cases hzero : isZero
            · have hd0 : d = 0 := hzero
              have hmod : a.toNat % base.modulus = 0 := by
                simpa [d] using hd0
              have hdecomp := Nat.mod_add_div a.toNat base.modulus
              rw [hmod] at hdecomp
              simp only [zero_add] at hdecomp
              have hproduct : product = a.toNat := by
                simp [product, hzVal, hzero]
              have hquotient : quotient = a.toNat / base.modulus := by
                simp [quotient, hproduct]
              rw [hzVal, if_pos hzero, hquotient]
              simp only [one_mul]
              calc
                a = (a.toNat : Int) := haNat.symm
                _ = (base.modulus : Int) *
                    (a.toNat / base.modulus : Nat) := by
                  exact_mod_cast hdecomp.symm
            · have hproduct : product = 0 := by
                simp [product, hzVal, hzero]
              have hquotient : quotient = 0 := by
                simp [quotient, hproduct]
              rw [hzVal, if_neg hzero, hquotient]
              simp
          · have hxZero : Modular.Lazy.evalZMod base x ρ = 0 ↔
                isZero := by
              unfold Modular.Lazy.evalZMod
              have haCast : (a : ZMod base.modulus) =
                  (a.toNat : ZMod base.modulus) := by
                rw [← Int.cast_natCast]
                exact (congrArg
                  (Int.castRingHom (ZMod base.modulus)) haNat).symm
              change (a : ZMod base.modulus) = 0 ↔ isZero
              rw [haCast, ZMod.natCast_eq_zero_iff]
              simp [isZero, d, Nat.dvd_iff_mod_eq_zero]
            mvcgen
            unfold Modular.Lazy.ZeroTestZModSpec
            rw [hzVal]
            constructor
            · split <;> simp
            · constructor
              · rw [hxZero]
                by_cases hzero : isZero <;> simp [hzero]
              · by_cases hzero : isZero
                · have hxz : Modular.Lazy.evalZMod base x ρ = 0 :=
                    hxZero.mpr hzero
                  simp [hzero, hxz]
                · have hxz : Modular.Lazy.evalZMod base x ρ ≠ 0 :=
                    fun h => hzero (hxZero.mp h)
                  simp [hzero, hxz]

@[spec] theorem classifyAdd_sound {P Q : AffineSlope.Point} :
  ⦃⌜True⌝⦄ Sound.interp ρ (AffineSlope.classifyAdd P Q)
    ⦃⇓ control => ⌜AddControlSpec ρ P Q control⌝⦄ := by
  mvcgen [AffineSlope.classifyAdd, AddControlSpec]
  rename_i sameX hsame oppositeY hopposite finite hfinite
    doubleKind hdoubleKind doubleCase hdoubleCase genericCase hgenericCase
  exact ⟨hsame, hopposite, hfinite, doubleKind, genericCase,
    hdoubleKind, hdoubleCase, hgenericCase, by simp⟩

@[spec] theorem classifyAdd_complete {P Q : AffineSlope.Point}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (AffineSlope.classifyAdd P Q)
    ⦃⇓ control => ⌜AddControlSpec ρ P Q control⌝⦄ := by
  rcases hP with
    ⟨hPXb, hPX, _, hPYb, hPY, hPYcanonical, hPinf⟩
  rcases hQ with
    ⟨hQXb, hQX, _, hQYb, hQY, hQYcanonical, hQinf⟩
  have hdx : (AffineSlope.sub Q.X P.X).Valid ρ :=
    Modular.Lazy.sub_valid base hQX hPX
  have hysum : (AffineSlope.add P.Y Q.Y).Valid ρ :=
    Modular.Lazy.add_valid base hPY hQY
  have hdxBound : (AffineSlope.sub Q.X P.X).bound = 4 := by
    simp [AffineSlope.sub, Modular.Lazy.sub, hPXb, hQXb]
  have hysumBound : (AffineSlope.add P.Y Q.Y).bound = 4 := by
    simp [AffineSlope.add, Modular.Lazy.add, hPYb, hQYb]
  have hysumCanonical :
      (AffineSlope.add P.Y Q.Y).intVal.eval ρ.int < 2 * base.modulus := by
    simp only [AffineSlope.add, Modular.Lazy.add, LC.eval_add]
    omega
  have hnotP : (LC.ofConst 1 - P.infinity).eval ρ.int = 0 ∨
      (LC.ofConst 1 - P.infinity).eval ρ.int = 1 := by
    rcases hPinf with h | h <;> simp [h]
  have hnotQ : (LC.ofConst 1 - Q.infinity).eval ρ.int = 0 ∨
      (LC.ofConst 1 - Q.infinity).eval ρ.int = 1 := by
    rcases hQinf with h | h <;> simp [h]
  have zeroTestBit {x : Modular.Lazy.Rep base} {z : LC ℤ}
      (h : Modular.Lazy.ZeroTestZModSpec base ρ x z) :
      z.eval ρ.int = 0 ∨ z.eval ρ.int = 1 := h.1
  have andSpecBit {x y z : LC ℤ}
      (h : AffineSlope.AndBitSpec ρ x y z) :
      z.eval ρ.int = 0 ∨ z.eval ρ.int = 1 := h.2
  have oneSubBit {z : LC ℤ}
      (h : z.eval ρ.int = 0 ∨ z.eval ρ.int = 1) :
      (LC.ofConst 1 - z).eval ρ.int = 0 ∨
        (LC.ofConst 1 - z).eval ρ.int = 1 := by
    rcases h with h | h <;> simp [h]
  mvcgen [AffineSlope.classifyAdd, AddControlSpec] <;> first
    | exact hdx
    | exact hysum
    | exact hdxBound
    | exact hysumBound
    | exact hysumCanonical
    | exact hnotP
    | exact hnotQ
    | exact zeroTestBit (by assumption)
    | exact andSpecBit (by assumption)
    | exact oneSubBit (zeroTestBit (by assumption))
    | exact oneSubBit (andSpecBit (by assumption))
    | skip
  rename_i sameX hsame oppositeY hopposite finite hfinite
    doubleKind hdoubleKind doubleCase hdoubleCase genericCase hgenericCase
  exact ⟨hsame, hopposite, hfinite, doubleKind, genericCase,
    hdoubleKind, hdoubleCase, hgenericCase, by simp⟩

def RawSlopeOperandsSpec (ρ : WF.Valuation) (P Q : AffineSlope.Point)
    (control : AffineSlope.AddControl)
    (selected : AffineSlope.SlopeOperands) : Prop :=
  (control.doubleCase.eval ρ.int = 1 →
    Modular.Lazy.evalZMod base selected.numerator ρ =
      3 * (Modular.Lazy.evalZMod base P.X ρ *
        Modular.Lazy.evalZMod base P.X ρ) - 3 ∧
    Modular.Lazy.evalZMod base selected.denominator ρ =
      2 * Modular.Lazy.evalZMod base P.Y ρ) ∧
  (control.doubleCase.eval ρ.int = 0 →
    Modular.Lazy.evalZMod base selected.numerator ρ =
      Modular.Lazy.evalZMod base Q.Y ρ -
        Modular.Lazy.evalZMod base P.Y ρ ∧
    Modular.Lazy.evalZMod base selected.denominator ρ =
      Modular.Lazy.evalZMod base Q.X ρ -
        Modular.Lazy.evalZMod base P.X ρ)

def SlopeOperandsSpec (ρ : WF.Valuation) (P Q : AffineSlope.Point)
    (control : AffineSlope.AddControl)
    (operands : AffineSlope.SlopeOperands) : Prop :=
  (control.active.eval ρ.int = 1 →
    (control.doubleCase.eval ρ.int = 1 →
      Modular.Lazy.evalZMod base operands.numerator ρ =
        3 * (Modular.Lazy.evalZMod base P.X ρ *
          Modular.Lazy.evalZMod base P.X ρ) - 3 ∧
      Modular.Lazy.evalZMod base operands.denominator ρ =
        2 * Modular.Lazy.evalZMod base P.Y ρ) ∧
    (control.doubleCase.eval ρ.int = 0 →
      Modular.Lazy.evalZMod base operands.numerator ρ =
        Modular.Lazy.evalZMod base Q.Y ρ -
          Modular.Lazy.evalZMod base P.Y ρ ∧
      Modular.Lazy.evalZMod base operands.denominator ρ =
        Modular.Lazy.evalZMod base Q.X ρ -
          Modular.Lazy.evalZMod base P.X ρ)) ∧
  (control.active.eval ρ.int = 0 →
    Modular.Lazy.evalZMod base operands.numerator ρ = 0 ∧
    Modular.Lazy.evalZMod base operands.denominator ρ = 1)

@[spec] theorem selectRawSlopeOperands_sound {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl} :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (AffineSlope.selectRawSlopeOperands P Q control)
    ⦃⇓ selected => ⌜RawSlopeOperandsSpec ρ P Q control selected⌝⦄ := by
  mvcgen [AffineSlope.selectRawSlopeOperands]
  rename_i x2 hx2 selectedNumerator hselectedNumerator
    selectedDenominator hselectedDenominator
  unfold RawSlopeOperandsSpec
  constructor
  · intro hdouble
    constructor
    · calc
        Modular.Lazy.evalZMod base selectedNumerator ρ =
            Modular.Lazy.evalZMod base
              (AffineSlope.sub (AffineSlope.scale 3 x2)
                (AffineSlope.ofElem three)) ρ :=
          hselectedNumerator.1 hdouble
        _ = _ := by
          simp [Modular.Lazy.MulZModSpec] at hx2
          simp [hx2, AffineSlope.sub, AffineSlope.scale,
            AffineSlope.ofElem]
    · calc
        Modular.Lazy.evalZMod base selectedDenominator ρ =
            Modular.Lazy.evalZMod base (AffineSlope.scale 2 P.Y) ρ :=
          hselectedDenominator.1 hdouble
        _ = _ := by simp [AffineSlope.scale]
  · intro hdouble
    constructor
    · calc
        Modular.Lazy.evalZMod base selectedNumerator ρ =
            Modular.Lazy.evalZMod base (AffineSlope.sub Q.Y P.Y) ρ :=
          hselectedNumerator.2 hdouble
        _ = _ := by simp [AffineSlope.sub]
    · calc
        Modular.Lazy.evalZMod base selectedDenominator ρ =
            Modular.Lazy.evalZMod base (AffineSlope.sub Q.X P.X) ρ :=
          hselectedDenominator.2 hdouble
        _ = _ := by simp [AffineSlope.sub]

@[spec] theorem activateSlopeOperands_sound
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {selected : AffineSlope.SlopeOperands}
    (hselected : RawSlopeOperandsSpec ρ P Q control selected) :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (AffineSlope.activateSlopeOperands P Q control selected)
    ⦃⇓ operands => ⌜SlopeOperandsSpec ρ P Q control operands⌝⦄ := by
  mvcgen [AffineSlope.activateSlopeOperands]
  rename_i numerator hnumerator denominator hdenominator
  unfold SlopeOperandsSpec
  constructor
  · intro hactive
    constructor
    · intro hdouble
      exact ⟨hnumerator.1 hactive |>.trans (hselected.1 hdouble).1,
        hdenominator.1 hactive |>.trans (hselected.1 hdouble).2⟩
    · intro hdouble
      exact ⟨hnumerator.1 hactive |>.trans (hselected.2 hdouble).1,
        hdenominator.1 hactive |>.trans (hselected.2 hdouble).2⟩
  · intro hactive
    exact ⟨by simpa [AffineSlope.ofElem] using hnumerator.2 hactive,
      by simpa [AffineSlope.ofElem] using hdenominator.2 hactive⟩

@[spec] theorem selectSlopeOperands_sound {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl}
    (hcontrol : AddControlSpec ρ P Q control) :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (AffineSlope.selectSlopeOperands P Q control)
    ⦃⇓ operands => ⌜SlopeOperandsSpec ρ P Q control operands⌝⦄ := by
  mvcgen [AffineSlope.selectSlopeOperands]
  all_goals intros
  all_goals try assumption
  all_goals intros <;> assumption

@[spec] theorem selectSlopeOperandsCollapsed_sound {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl}
    (hcontrol : AddControlSpec ρ P Q control) :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (AffineSlope.selectSlopeOperandsCollapsed P Q control)
    ⦃⇓ operands => ⌜SlopeOperandsSpec ρ P Q control operands⌝⦄ := by
  mvcgen [AffineSlope.selectSlopeOperandsCollapsed,
    AffineSlope.finishSelectSlopeOperandsCollapsed,
    AffineSlope.selectCollapsedNumerator,
    AffineSlope.selectCollapsedDenominator]
  rename_i x2 hx2 numerator hnumerator denominator hdenominator
  unfold SlopeOperandsSpec
  constructor
  · intro hactive
    constructor
    · intro hdouble
      constructor
      · calc
          Modular.Lazy.evalZMod base numerator ρ =
              Modular.Lazy.evalZMod base
                (AffineSlope.sub (AffineSlope.scale 3 x2)
                  (AffineSlope.ofElem three)) ρ := hnumerator.1 hdouble
          _ = _ := by
            simp [Modular.Lazy.MulZModSpec] at hx2
            simp [hx2, AffineSlope.sub, AffineSlope.scale,
              AffineSlope.ofElem]
      · calc
          Modular.Lazy.evalZMod base denominator ρ =
              Modular.Lazy.evalZMod base (AffineSlope.scale 2 P.Y) ρ :=
            hdenominator.1 hdouble
          _ = _ := by simp [AffineSlope.scale]
    · intro hdouble
      have hgeneric :
          (control.active - control.doubleCase).eval ρ.int = 1 := by
        simp [hactive, hdouble]
      constructor
      · calc
          Modular.Lazy.evalZMod base numerator ρ =
              Modular.Lazy.evalZMod base (AffineSlope.sub Q.Y P.Y) ρ :=
            hnumerator.2.1 hgeneric
          _ = _ := by simp [AffineSlope.sub]
      · calc
          Modular.Lazy.evalZMod base denominator ρ =
              Modular.Lazy.evalZMod base (AffineSlope.sub Q.X P.X) ρ :=
            hdenominator.2.1 hgeneric
          _ = _ := by simp [AffineSlope.sub]
  · intro hactive
    have hinactive : (LC.ofConst 1 - control.active).eval ρ.int = 1 := by
      simp [hactive]
    exact ⟨by simpa [AffineSlope.ofElem] using hnumerator.2.2 hinactive,
      by simpa [AffineSlope.ofElem] using hdenominator.2.2 hinactive⟩

theorem SlopeOperandsSpec.denominator_ne_zero
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {operands : AffineSlope.SlopeOperands} {p : Reference.Point}
    (hcontrol : AddControlSpec ρ P Q control)
    (hoperands : SlopeOperandsSpec ρ P Q control operands)
    (hP : Reference.Represents ρ P p)
    (hnoTwoTorsion : p = 0 ∨ p + p ≠ 0) :
    Modular.Lazy.evalZMod base operands.denominator ρ ≠ 0 := by
  have hactiveBit := hcontrol.active_bit
  rcases hcontrol with
    ⟨hsame, _, hfinite, doubleKind, genericCase,
      _, hdoubleCase, hgenericCase, hactive⟩
  rcases hactiveBit with hactive0 | hactive1
  · rw [(hoperands.2 hactive0).2]
    exact one_ne_zero
  · rcases hdoubleCase.2 with hdouble0 | hdouble1
    · have hgeneric1 : genericCase.eval ρ.int = 1 := by
        rw [hactive1, hdouble0] at hactive
        omega
      have hsame0 : control.sameX.eval ρ.int = 0 := by
        rw [hgenericCase.1] at hgeneric1
        rcases hfinite.2 with hfinite0 | hfinite1
        · simp [hfinite0] at hgeneric1
        · simp [hfinite1] at hgeneric1
          omega
      have hdx : Modular.Lazy.evalZMod base
          (AffineSlope.sub Q.X P.X) ρ ≠ 0 := by
        intro hzero
        have := hsame.2.2
        simp [hzero] at this
        omega
      rw [((hoperands.1 hactive1).2 hdouble0).2]
      simpa [AffineSlope.sub] using hdx
    · rw [((hoperands.1 hactive1).1 hdouble1).2]
      rcases p with _ | ⟨px, py, hpcurve⟩
      · have hpinf := Reference.Aux.represents_zero hP
        have hfinite1 : control.finite.eval ρ.int = 1 := by
          rw [hdoubleCase.1] at hdouble1
          rcases hfinite.2 with h | h
          · simp [h] at hdouble1
          · exact h
        rw [hfinite.1] at hfinite1
        simp [hpinf] at hfinite1
      · obtain ⟨hpinf, hpx, hpy⟩ := Reference.Aux.represents_some hP
        rw [hpy]
        have hyneg : py ≠ Reference.curve.toAffine.negY px py := by
          intro hy
          rcases hnoTwoTorsion with hzero | hne
          · contradiction
          · apply hne
            exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy
        intro hzero
        apply hyneg
        simp only [WeierstrassCurve.Affine.negY, Reference.curve, zero_mul]
        linear_combination hzero

@[spec] theorem selectRawSlopeOperands_complete
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    (hPvalid : P.Valid ρ) (hQvalid : Q.Valid ρ)
    (hdoubleBit : control.doubleCase.eval ρ.int = 0 ∨
      control.doubleCase.eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectRawSlopeOperands P Q control)
    ⦃⇓ selected => ⌜selected.Valid ρ ∧
      RawSlopeOperandsSpec ρ P Q control selected ∧
      selected.numerator.intVal.eval ρ.int < (2 ^ 262 : Nat) ∧
      selected.denominator.intVal.eval ρ.int < (2 ^ 262 : Nat)⌝⦄ := by
  rcases hPvalid with ⟨hPXbound, hPX, _, hPYbound, hPY, _, _⟩
  rcases hQvalid with ⟨hQXbound, hQX, _, hQYbound, hQY, _, _⟩
  have hthree : (AffineSlope.ofElem three).Valid ρ :=
    Modular.Lazy.ofElem_valid base
      (Modular.ofNat_valid base 3 (by native_decide) (by native_decide))
  have fit8 {x : AffineSlope.Rep} (hx : x.Valid ρ)
      (hbound : x.bound ≤ 8) :
      x.intVal.eval ρ.int < (2 ^ 262 : Nat) := by
    calc
      x.intVal.eval ρ.int < x.bound * base.modulus := hx.2
      _ ≤ 8 * base.modulus := by
        exact_mod_cast Nat.mul_le_mul_right base.modulus hbound
      _ < (2 ^ 262 : Nat) := by
        norm_num [base, baseModulus]
        native_decide
  have hx2Bound : P.X.bound * P.X.bound <
      2 ^ Modular.Lazy.quotientExtraBits := by
    simp [hPXbound, Modular.Lazy.quotientExtraBits]
  mvcgen [AffineSlope.selectRawSlopeOperands]
  all_goals first
    | exact hPX
    | exact hx2Bound
    | exact hdoubleBit
    | exact Modular.Lazy.sub_valid base hQY hPY
    | exact Modular.Lazy.sub_valid base hQX hPX
    | exact Modular.Lazy.scale_valid base hPY (by omega)
    | exact Modular.Lazy.sub_valid base
        (Modular.Lazy.scale_valid base (by assumption) (by omega)) hthree
    | apply fit8
      · exact Modular.Lazy.sub_valid base
          (Modular.Lazy.scale_valid base (by assumption) (by omega)) hthree
      · simp_all [AffineSlope.sub, AffineSlope.scale, AffineSlope.ofElem]
    | apply fit8
      · exact Modular.Lazy.sub_valid base hQY hPY
      · simp [AffineSlope.sub, hQYbound, hPYbound]
    | apply fit8
      · exact Modular.Lazy.scale_valid base hPY (by omega)
      · simp [AffineSlope.scale, hPYbound]
    | apply fit8
      · exact Modular.Lazy.sub_valid base hQX hPX
      · simp [AffineSlope.sub, hQXbound, hPXbound]
    | skip
  case vc5.hone x2 hx2 =>
    exact Modular.Lazy.sub_valid base
      (Modular.Lazy.scale_valid base hx2.2.1 (by omega)) hthree
  case vc6.honeFit x2 hx2 =>
    apply fit8
    · exact Modular.Lazy.sub_valid base
        (Modular.Lazy.scale_valid base hx2.2.1 (by omega)) hthree
    · change 3 * x2.bound + 2 ≤ 8
      omega
  case vc8.hzeroFit =>
    apply fit8 (Modular.Lazy.sub_valid base hQY hPY)
    change Q.Y.bound + P.Y.bound ≤ 8
    omega
  case vc11.honeFit =>
    apply fit8 (Modular.Lazy.scale_valid base hPY (by omega))
    change 2 * P.Y.bound ≤ 8
    omega
  case vc13.hzeroFit =>
    apply fit8 (Modular.Lazy.sub_valid base hQX hPX)
    change Q.X.bound + P.X.bound ≤ 8
    omega
  case vc14.success x2 hx2 num hnum den hden =>
    refine ⟨⟨hnum.2.1, hnum.2.2.2, hden.2.1, hden.2.2.2⟩, ?_,
      hnum.2.2.1, hden.2.2.1⟩
    unfold RawSlopeOperandsSpec
    constructor
    · intro hd
      constructor
      · calc
          Modular.Lazy.evalZMod base num ρ =
              Modular.Lazy.evalZMod base
                (AffineSlope.sub (AffineSlope.scale 3 x2)
                  (AffineSlope.ofElem three)) ρ := hnum.1.1 hd
          _ = _ := by
            simp [Modular.Lazy.MulZModSpec] at hx2
            simp [hx2.1, AffineSlope.sub, AffineSlope.scale,
              AffineSlope.ofElem]
      · calc
          Modular.Lazy.evalZMod base den ρ =
              Modular.Lazy.evalZMod base (AffineSlope.scale 2 P.Y) ρ :=
            hden.1.1 hd
          _ = _ := by simp [AffineSlope.scale]
    · intro hd
      constructor
      · calc
          Modular.Lazy.evalZMod base num ρ =
              Modular.Lazy.evalZMod base (AffineSlope.sub Q.Y P.Y) ρ :=
            hnum.1.2 hd
          _ = _ := by simp [AffineSlope.sub]
      · calc
          Modular.Lazy.evalZMod base den ρ =
              Modular.Lazy.evalZMod base (AffineSlope.sub Q.X P.X) ρ :=
            hden.1.2 hd
          _ = _ := by simp [AffineSlope.sub]

@[spec] theorem activateSlopeOperands_complete
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {selected : AffineSlope.SlopeOperands}
    (hselected : selected.Valid ρ)
    (hselectedSpec : RawSlopeOperandsSpec ρ P Q control selected)
    (hnumFit : selected.numerator.intVal.eval ρ.int < (2 ^ 262 : Nat))
    (hdenFit : selected.denominator.intVal.eval ρ.int < (2 ^ 262 : Nat))
    (hactiveBit : control.active.eval ρ.int = 0 ∨
      control.active.eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.activateSlopeOperands P Q control selected)
    ⦃⇓ operands => ⌜operands.Valid ρ ∧
      SlopeOperandsSpec ρ P Q control operands⌝⦄ := by
  have hzero : (AffineSlope.ofElem zero).Valid ρ :=
    Modular.Lazy.ofElem_valid base
      (Modular.ofNat_valid base 0 (by native_decide) (by native_decide))
  have hone : (AffineSlope.ofElem one).Valid ρ :=
    Modular.Lazy.ofElem_valid base
      (Modular.ofNat_valid base 1 (by native_decide) (by native_decide))
  have hzeroFit : (AffineSlope.ofElem zero).intVal.eval ρ.int <
      (2 ^ 262 : Nat) := hzero.2.trans (by
    norm_num [AffineSlope.ofElem, base, baseModulus]
    native_decide)
  have honeFit : (AffineSlope.ofElem one).intVal.eval ρ.int <
      (2 ^ 262 : Nat) := hone.2.trans (by
    norm_num [AffineSlope.ofElem, base, baseModulus]
    native_decide)
  rcases hselected with ⟨hnum, hnumBound, hden, hdenBound⟩
  mvcgen [AffineSlope.activateSlopeOperands]
  all_goals first
    | exact hactiveBit
    | exact hnum
    | exact hden
    | exact hnumFit
    | exact hdenFit
    | exact hzero
    | exact hone
    | exact hzeroFit
    | exact honeFit
    | skip
  case vc11.success.success num hnumOut den hdenOut =>
    refine ⟨⟨hnumOut.2.1, hnumOut.2.2.2,
      hdenOut.2.1, hdenOut.2.2.2⟩, ?_⟩
    unfold SlopeOperandsSpec
    constructor
    · intro hactive
      constructor
      · intro hdouble
        exact ⟨hnumOut.1.1 hactive |>.trans (hselectedSpec.1 hdouble).1,
          hdenOut.1.1 hactive |>.trans (hselectedSpec.1 hdouble).2⟩
      · intro hdouble
        exact ⟨hnumOut.1.1 hactive |>.trans (hselectedSpec.2 hdouble).1,
          hdenOut.1.1 hactive |>.trans (hselectedSpec.2 hdouble).2⟩
    · intro hactive
      exact ⟨by simpa [AffineSlope.ofElem] using hnumOut.1.2 hactive,
        by simpa [AffineSlope.ofElem] using hdenOut.1.2 hactive⟩

@[spec] theorem selectSlopeOperands_complete
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {p : Reference.Point}
    (hPvalid : P.Valid ρ) (hQvalid : Q.Valid ρ)
    (hcontrol : AddControlSpec ρ P Q control)
    (hP : Reference.Represents ρ P p)
    (hnoTwoTorsion : p = 0 ∨ p + p ≠ 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectSlopeOperands P Q control)
    ⦃⇓ operands => ⌜operands.Valid ρ ∧
      SlopeOperandsSpec ρ P Q control operands ∧
      Modular.Lazy.evalZMod base operands.denominator ρ ≠ 0⌝⦄ := by
  have hactiveBit := hcontrol.active_bit
  have hdoubleBit : control.doubleCase.eval ρ.int = 0 ∨
      control.doubleCase.eval ρ.int = 1 := by
    rcases hcontrol with ⟨_, _, _, _, _, _, hdoubleCase, _, _⟩
    exact hdoubleCase.2
  mvcgen [AffineSlope.selectSlopeOperands]
  all_goals intros
  all_goals try assumption
  case vc4.success.success selected hselected out houtValid houtSpec =>
    exact ⟨houtValid, houtSpec,
      SlopeOperandsSpec.denominator_ne_zero hcontrol houtSpec hP
        hnoTwoTorsion⟩

def AddCandidateSpec (ρ : WF.Valuation) (P Q : AffineSlope.Point)
    (control : AffineSlope.AddControl)
    (candidate : AffineSlope.Rep × AffineSlope.Rep) : Prop :=
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
      Modular.Lazy.evalZMod base candidate.1 ρ =
        Modular.Lazy.evalZMod base slope ρ *
            Modular.Lazy.evalZMod base slope ρ -
          (Modular.Lazy.evalZMod base P.X ρ +
            Modular.Lazy.evalZMod base Q.X ρ) ∧
      Modular.Lazy.evalZMod base candidate.2 ρ =
        Modular.Lazy.evalZMod base slope ρ *
          (Modular.Lazy.evalZMod base P.X ρ -
          Modular.Lazy.evalZMod base candidate.1 ρ) -
            Modular.Lazy.evalZMod base P.Y ρ

@[spec] theorem finishAddCandidate_sound {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl}
    {operands : AffineSlope.SlopeOperands}
    (hoperands : SlopeOperandsSpec ρ P Q control operands)
    (hdoubleBit : control.doubleCase.eval ρ.int = 0 ∨
      control.doubleCase.eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (AffineSlope.finishAddCandidate P Q operands)
    ⦃⇓ candidate => ⌜AddCandidateSpec ρ P Q control candidate⌝⦄ := by
  mvcgen [AffineSlope.finishAddCandidate]
  rename_i slope hslope candidateX hcandidateX candidateY hcandidateY
  unfold AddCandidateSpec
  intro hactive
  rcases hoperands.1 hactive with ⟨hdouble, hgeneric⟩
  by_cases hd : control.doubleCase.eval ρ.int = 1
  · rcases hdouble hd with ⟨hnum, hden⟩
    refine ⟨slope, ?_⟩
    simp_all [Modular.Lazy.DivideZModSpec,
      Modular.Lazy.MulSubToElemZModSpec, AffineSlope.add,
      AffineSlope.sub, AffineSlope.ofElem]
  · have hd0 : control.doubleCase.eval ρ.int = 0 := by
      rcases hdoubleBit with h | h
      · exact h
      · contradiction
    rcases hgeneric hd0 with ⟨hnum, hden⟩
    refine ⟨slope, ?_⟩
    simp_all [Modular.Lazy.DivideZModSpec,
      Modular.Lazy.MulSubToElemZModSpec, AffineSlope.add,
      AffineSlope.sub, AffineSlope.ofElem]

@[spec] theorem finishAddCandidate_complete {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl}
    {operands : AffineSlope.SlopeOperands}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ)
    (hoperands : operands.Valid ρ)
    (hoperandsSpec : SlopeOperandsSpec ρ P Q control operands)
    (hden : Modular.Lazy.evalZMod base operands.denominator ρ ≠ 0)
    (hdoubleBit : control.doubleCase.eval ρ.int = 0 ∨
      control.doubleCase.eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.finishAddCandidate P Q operands)
    ⦃⇓ candidate => ⌜candidate.1.Valid ρ ∧
      candidate.1.bound = 2 ∧
      candidate.1.intVal.eval ρ.int < base.modulus ∧
      candidate.2.Valid ρ ∧ candidate.2.bound = 2 ∧
      candidate.2.intVal.eval ρ.int < base.modulus ∧
      AddCandidateSpec ρ P Q control candidate⌝⦄ := by
  rcases hP with ⟨hPXbound, hPX, _, hPYbound, hPY, _, _⟩
  rcases hQ with ⟨hQXbound, hQX, _, hQYbound, hQY, _, _⟩
  rcases hoperands with ⟨hnum, hnumBound, hdenValid, hdenBound⟩
  mvcgen [AffineSlope.finishAddCandidate]
  all_goals first
    | exact hdenValid
    | exact hnum
    | exact hden
    | exact hPX
    | exact hPY
    | exact Modular.Lazy.add_valid base hPX hQX
    | exact Modular.Lazy.sub_valid base hPX
        (Modular.Lazy.ofElem_valid base (by assumption))
    | simp [AffineSlope.add, AffineSlope.sub, AffineSlope.ofElem,
        Modular.Lazy.add, Modular.Lazy.sub, Modular.Lazy.ofElem,
        Modular.Lazy.quotientExtraBits, hPXbound, hPYbound,
        hQXbound, hQYbound, hnumBound, hdenBound]
    | skip
  case vc5.hx slope hslope =>
    exact hslope.1
  case vc6.hy slope hslope =>
    exact hslope.1
  case vc8.hbound slope hslope =>
    rw [hslope.2.2]
    norm_num [AffineSlope.add, Modular.Lazy.add, hPXbound, hQXbound,
      Modular.Lazy.quotientExtraBits]
  case vc9.hx slope hslope candidateX hcandidateX =>
    exact hslope.1
  case vc10.hy slope hslope candidateX hcandidateX =>
    rcases hPX with ⟨hx0, hxlt⟩
    have hy0 : 0 ≤ candidateX.val.intVal.eval ρ.int :=
      Modular.Elem.nonneg (p := base) hcandidateX.1
    have hylt : candidateX.val.intVal.eval ρ.int < base.modulus :=
      hcandidateX.1.2
    constructor
    · simp only [AffineSlope.sub, AffineSlope.ofElem, Modular.Lazy.sub,
        Modular.Lazy.ofElem, Modular.Lazy.Rep.Valid,
        LC.eval_sub, LC.eval_add, LC.eval_ofConst]
      push_cast
      omega
    · simp only [AffineSlope.sub, AffineSlope.ofElem, Modular.Lazy.sub,
        Modular.Lazy.ofElem, Modular.Lazy.Rep.Valid,
        LC.eval_sub, LC.eval_add, LC.eval_ofConst]
      push_cast
      ring_nf
      nlinarith
  case vc12.hbound slope hslope candidateX hcandidateX =>
    rw [hslope.2.2]
    norm_num [AffineSlope.sub, AffineSlope.ofElem, Modular.Lazy.sub,
      Modular.Lazy.ofElem, hPXbound, hPYbound,
      Modular.Lazy.quotientExtraBits]
  case vc13.success slope hslope candidateX hcandidateX candidateY hcandidateY =>
    refine ⟨Modular.Lazy.ofElem_valid base hcandidateX.1,
      hcandidateX.1.2, Modular.Lazy.ofElem_valid base hcandidateY.1,
      hcandidateY.1.2, ?_⟩
    unfold AddCandidateSpec
    unfold Modular.Lazy.DivideZModSpec at hslope
    unfold Modular.Lazy.MulSubToElemZModSpec at hcandidateX hcandidateY
    intro hactive
    rcases hoperandsSpec.1 hactive with ⟨hdouble, hgeneric⟩
    have hcandidateXEq := hcandidateX.2
    have hcandidateYEq := hcandidateY.2
    simp only [AffineSlope.add, Modular.Lazy.evalZMod_add] at hcandidateXEq
    simp only [AffineSlope.sub, AffineSlope.ofElem,
      Modular.Lazy.evalZMod_sub, Modular.Lazy.evalZMod_ofElem]
      at hcandidateYEq
    rcases hdoubleBit with hd0 | hd1
    · rcases hgeneric hd0 with ⟨hnumEq, hdenEq⟩
      have hslopeEq := hslope.2.1
      rw [hdenEq, hnumEq] at hslopeEq
      refine ⟨slope, ?_, ?_, ?_⟩
      · simpa [hd0] using hslopeEq
      · exact hcandidateXEq
      · exact hcandidateYEq
    · rcases hdouble hd1 with ⟨hnumEq, hdenEq⟩
      have hslopeEq := hslope.2.1
      rw [hdenEq, hnumEq] at hslopeEq
      refine ⟨slope, ?_, ?_, ?_⟩
      · simpa [hd1] using hslopeEq
      · exact hcandidateXEq
      · exact hcandidateYEq

@[spec] theorem addCandidate_complete {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl} {p : Reference.Point}
    (hPvalid : P.Valid ρ) (hQvalid : Q.Valid ρ)
    (hcontrol : AddControlSpec ρ P Q control)
    (hP : Reference.Represents ρ P p)
    (hnoTwoTorsion : p = 0 ∨ p + p ≠ 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.addCandidate P Q control)
    ⦃⇓ candidate => ⌜candidate.1.Valid ρ ∧
      candidate.1.bound = 2 ∧
      candidate.1.intVal.eval ρ.int < base.modulus ∧
      candidate.2.Valid ρ ∧ candidate.2.bound = 2 ∧
      candidate.2.intVal.eval ρ.int < base.modulus ∧
      AddCandidateSpec ρ P Q control candidate⌝⦄ := by
  have hdoubleBit : control.doubleCase.eval ρ.int = 0 ∨
      control.doubleCase.eval ρ.int = 1 := by
    rcases hcontrol with ⟨_, _, _, _, _, _, hdoubleCase, _, _⟩
    exact hdoubleCase.2
  mvcgen [AffineSlope.addCandidate]
  all_goals intros
  all_goals first | assumption | skip

@[spec] theorem addCandidate_sound {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl}
    (hcontrol : AddControlSpec ρ P Q control) :
    ⦃⌜True⌝⦄ Sound.interp ρ (AffineSlope.addCandidate P Q control)
    ⦃⇓ candidate => ⌜AddCandidateSpec ρ P Q control candidate⌝⦄ := by
  have hdoubleBit : control.doubleCase.eval ρ.int = 0 ∨
      control.doubleCase.eval ρ.int = 1 := by
    rcases hcontrol with ⟨_, _, _, _, _, _, hdoubleCase, _, _⟩
    exact hdoubleCase.2
  mvcgen [AffineSlope.addCandidate]
  all_goals intros <;> assumption


def SelectAddOutputSpec (ρ : WF.Valuation) (P Q : AffineSlope.Point)
    (control : AffineSlope.AddControl)
    (candidate : AffineSlope.Rep × AffineSlope.Rep)
    (out : AffineSlope.Point) : Prop :=
  ∃ inactiveX0 inactiveY0 inactiveX inactiveY : AffineSlope.Rep,
      AffineSlope.SelectZModSpec ρ Q.infinity P.X
        (AffineSlope.ofElem zero) inactiveX0 ∧
      AffineSlope.SelectZModSpec ρ Q.infinity P.Y
        (AffineSlope.ofElem zero) inactiveY0 ∧
      AffineSlope.SelectZModSpec ρ P.infinity Q.X inactiveX0 inactiveX ∧
      AffineSlope.SelectZModSpec ρ P.infinity Q.Y inactiveY0 inactiveY ∧
      AffineSlope.SelectZModSpec ρ control.active candidate.1 inactiveX
        out.X ∧
      AffineSlope.SelectZModSpec ρ control.active candidate.2 inactiveY
        out.Y ∧
    ∃ bothInfinity oppositePair finiteOpposite : LC ℤ,
      AffineSlope.AndBitSpec ρ P.infinity Q.infinity bothInfinity ∧
      AffineSlope.AndBitSpec ρ control.sameX control.oppositeY oppositePair ∧
      AffineSlope.AndBitSpec ρ control.finite oppositePair finiteOpposite ∧
      out.infinity.eval ρ.int =
        bothInfinity.eval ρ.int + finiteOpposite.eval ρ.int

theorem SelectAddOutputSpec.infinity_bit
    {P Q out : AffineSlope.Point}
    {control : AffineSlope.AddControl}
    {candidate : AffineSlope.Rep × AffineSlope.Rep}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ)
    (hcontrol : AddControlSpec ρ P Q control)
    (hout : SelectAddOutputSpec ρ P Q control candidate out) :
    out.infinity.eval ρ.int = 0 ∨ out.infinity.eval ρ.int = 1 := by
  rcases hP with ⟨_, _, _, _, _, _, hPinf⟩
  rcases hQ with ⟨_, _, _, _, _, _, hQinf⟩
  rcases hcontrol with
    ⟨_, _, hfinite, _, _, _, _, _, _⟩
  rcases hout with
    ⟨_, _, _, _, _, _, _, _, _, _,
      bothInfinity, oppositePair, finiteOpposite,
      hbothInfinity, _, hfiniteOpposite, houtInfinity⟩
  rcases hPinf with hp | hp <;>
    rcases hQinf with hq | hq <;>
    rcases hfiniteOpposite.2 with hfo | hfo <;>
    simp_all [AffineSlope.AndBitSpec] <;> omega

@[spec] theorem selectAddOutput_sound {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl}
    {candidate : AffineSlope.Rep × AffineSlope.Rep} :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (AffineSlope.selectAddOutput P Q control candidate)
    ⦃⇓ out => ⌜SelectAddOutputSpec ρ P Q control candidate out⌝⦄ := by
  mvcgen [AffineSlope.selectAddOutput, SelectAddOutputSpec]
  rename_i inactiveX0 hinactiveX0 inactiveY0 hinactiveY0
    inactiveX hinactiveX inactiveY hinactiveY X hX Y hY
    bothInfinity hbothInfinity finiteOpposite hfiniteOpposite
  rcases hfiniteOpposite with
    ⟨oppositePair, hoppositePair, hfiniteOpposite⟩
  exact ⟨inactiveX0, inactiveY0, inactiveX, inactiveY,
    hinactiveX0, hinactiveY0, hinactiveX, hinactiveY, hX, hY,
    bothInfinity, oppositePair, finiteOpposite,
    hbothInfinity, hoppositePair, hfiniteOpposite, by simp⟩

@[spec] theorem selectAddOutput_complete {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl}
    {candidate : AffineSlope.Rep × AffineSlope.Rep}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ)
    (hcontrol : AddControlSpec ρ P Q control)
    (hcandidateX : candidate.1.Valid ρ)
    (hcandidateXCanonical :
      candidate.1.intVal.eval ρ.int < base.modulus)
    (hcandidateY : candidate.2.Valid ρ)
    (hcandidateYCanonical :
      candidate.2.intVal.eval ρ.int < base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectAddOutput P Q control candidate)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      SelectAddOutputSpec ρ P Q control candidate out⌝⦄ := by
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
  have hactive := hcontrol.active_bit
  have hcontrol' := hcontrol
  rcases hcontrol with
    ⟨hsame, hopposite, hfinite, doubleKind, genericCase,
      hdoubleKind, hdoubleCase, hgenericCase, hactiveEq⟩
  mvcgen [AffineSlope.selectAddOutput, SelectAddOutputSpec]
  all_goals first
    | assumption
    | exact hPinf
    | exact hQinf
    | exact hactive
    | exact hsame.1
    | exact hopposite.1
    | exact hfinite.2
    | exact hPX
    | exact hPY
    | exact hQX
    | exact hQY
    | exact hPXCanonical
    | exact hPYCanonical
    | exact hQXCanonical
    | exact hQYCanonical
    | exact hcandidateX
    | exact hcandidateY
    | exact hcandidateXCanonical
    | exact hcandidateYCanonical
    | exact hzero
    | exact hzeroCanonical
    | skip
  case vc14.hzero => aesop
  case vc15.hzeroCanonical => aesop
  case vc19.hzero => aesop
  case vc20.hzeroCanonical => aesop
  case vc24.hzero => aesop
  case vc25.hzeroCanonical => aesop
  case vc29.hzero => aesop
  case vc30.hzeroCanonical => aesop
  case vc36.success.success.success.success.success.success.success.success =>
    rename_i inactiveX0 hinactiveX0 inactiveY0 hinactiveY0
      inactiveX hinactiveX inactiveY hinactiveY X hX Y hY
      bothInfinity hbothInfinity finiteOpposite hfiniteOpposite
    rcases hfiniteOpposite with
      ⟨oppositePair, hoppositePair, hfiniteOpposite⟩
    have houtSpec : SelectAddOutputSpec ρ P Q control candidate
        ⟨X, Y, bothInfinity + finiteOpposite⟩ := by
      exact ⟨inactiveX0, inactiveY0, inactiveX, inactiveY,
        hinactiveX0.1, hinactiveY0.1, hinactiveX.1, hinactiveY.1,
        hX.1, hY.1, bothInfinity, oppositePair, finiteOpposite,
        hbothInfinity, hoppositePair, hfiniteOpposite, by simp⟩
    constructor
    · exact ⟨hX.2.2.2, hX.2.1, hX.2.2.1,
        hY.2.2.2, hY.2.1, hY.2.2.1,
        SelectAddOutputSpec.infinity_bit
          ⟨hPXbound, hPX, hPXCanonical, hPYbound, hPY,
            hPYCanonical, hPinf⟩
          ⟨hQXbound, hQX, hQXCanonical, hQYbound, hQY,
            hQYCanonical, hQinf⟩
          hcontrol' houtSpec⟩
    · exact houtSpec


/-- The pure semantic join point for complete affine addition.  The circuit
proofs above expose only the facts established by each subcircuit; this lemma
does all branch reasoning once, away from the exported circuit theorem. -/
theorem add_specs_raw {P Q out : AffineSlope.Point}
    {p q : Reference.Point}
    (hP : Reference.Represents ρ P p)
    (hQ : Reference.Represents ρ Q q)
    {control : AffineSlope.AddControl}
    {candidate : AffineSlope.Rep × AffineSlope.Rep}
    (hcontrol : AddControlSpec ρ P Q control)
    (hcandidate : AddCandidateSpec ρ P Q control candidate)
    (hout : SelectAddOutputSpec ρ P Q control candidate out) :
    (out.infinity.eval ρ.int = 0 ∨ out.infinity.eval ρ.int = 1) ∧
      Reference.circuitCoordinates ρ out =
        Reference.slopeAddCoordinates p q := by
  rcases hcontrol with
    ⟨hsame, hopposite, hfinite, doubleKind, genericCase,
      hdoubleKind, hdoubleCase, hgenericCase, hactive⟩
  rcases hout with
    ⟨inactiveX0, inactiveY0, inactiveX, inactiveY,
      hinactiveX0, hinactiveY0, hinactiveX, hinactiveY, hX, hY,
      bothInfinity, oppositePair, finiteOpposite,
      hbothInfinity, hoppositePair, hfiniteOpposite, houtInfinity⟩
  rcases p with _ | ⟨px, py, hpcurve⟩
  · have hpinf := Reference.Aux.represents_zero hP
    rcases q with _ | ⟨qx, qy, hqcurve⟩
    · have hqinf := Reference.Aux.represents_zero hQ
      simp_all [AffineSlope.AndBitSpec, AffineSlope.SelectZModSpec,
        Reference.circuitCoordinates, Reference.slopeAddCoordinates,
        Reference.coordinates]
    · obtain ⟨hqinf, hqx, hqy⟩ := Reference.Aux.represents_some hQ
      simp_all [AffineSlope.AndBitSpec, AffineSlope.SelectZModSpec,
        Reference.circuitCoordinates, Reference.slopeAddCoordinates,
        Reference.coordinates,
        AffineSlope.ofElem, Modular.Lazy.evalZMod,
        Modular.Lazy.evalElemZMod]
  · obtain ⟨hpinf, hpx, hpy⟩ := Reference.Aux.represents_some hP
    rcases q with _ | ⟨qx, qy, hqcurve⟩
    · have hqinf := Reference.Aux.represents_zero hQ
      simp_all [AffineSlope.AndBitSpec, AffineSlope.SelectZModSpec,
        Reference.circuitCoordinates, Reference.slopeAddCoordinates,
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
        · simp_all [AffineSlope.AndBitSpec, AffineSlope.SelectZModSpec,
            Modular.Lazy.ZeroTestZModSpec, Reference.circuitCoordinates,
            Reference.slopeAddCoordinates, Reference.coordinates,
            WeierstrassCurve.Affine.negY, Reference.curve,
            AffineSlope.ofElem, Modular.Lazy.evalZMod]
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
          rcases hcandidate hac with ⟨slope, hslope, hcandidateX,
            hcandidateY⟩
          rw [if_pos hdouble] at hslope
          have hslopeEq : Modular.Lazy.evalZMod base slope ρ =
              (3 * qx ^ 2 - 3) / (2 * py) := by
            rw [hpx, hpy, hx] at hslope
            exact (eq_div_iff hden).2 (by simpa [pow_two] using hslope)
          have houtX := hX.1 hac
          have houtY := hY.1 hac
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
          · unfold Reference.circuitCoordinates
            rw [if_neg (by omega)]
            simp only [Reference.slopeAddCoordinates, if_pos hx, if_neg hy]
            congr 1
            · rw [houtX, hcandidateX, hslopeEq, hpx, hqx, hx]
              simp only [Reference.tangentSlope, Reference.resultX]
              ring
            · rw [houtY, hcandidateY, hcandidateX, hslopeEq,
                hpx, hpy, hqx, hx]
              simp only [Reference.tangentSlope, Reference.resultX,
                Reference.resultY]
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
        rcases hcandidate hac with ⟨slope, hslope, hcandidateX,
          hcandidateY⟩
        rw [if_neg (by omega)] at hslope
        have hslopeEq : Modular.Lazy.evalZMod base slope ρ =
            (qy - py) / (qx - px) := (eq_div_iff hden).2 (by
          rw [hpx, hpy, hqx, hqy] at hslope
          exact hslope)
        have houtX := hX.1 hac
        have houtY := hY.1 hac
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
        · unfold Reference.circuitCoordinates
          rw [if_neg (by omega)]
          simp only [Reference.slopeAddCoordinates, if_neg hx]
          congr 1
          · rw [houtX, hcandidateX, hslopeEq, hpx, hqx]
            simp only [Reference.chordSlope, Reference.resultX]
            ring
          · rw [houtY, hcandidateY, hcandidateX, hslopeEq,
              hpx, hpy, hqx]
            simp only [Reference.chordSlope, Reference.resultX,
              Reference.resultY]
            ring

/-- The semantic join point strengthened with the normalized infinity
carrier required by the scalar-multiplication implementation. -/
theorem add_specs_normalized {P Q out : AffineSlope.Point}
    {p q : Reference.Point}
    (hP : Reference.NormalizedRep ρ P p)
    (hQ : Reference.NormalizedRep ρ Q q)
    {control : AffineSlope.AddControl}
    {candidate : AffineSlope.Rep × AffineSlope.Rep}
    (hcontrol : AddControlSpec ρ P Q control)
    (hcandidate : AddCandidateSpec ρ P Q control candidate)
    (hout : SelectAddOutputSpec ρ P Q control candidate out)
    (hmath : Reference.slopeAddCoordinates p q =
      Reference.coordinates (p + q)) :
    Reference.NormalizedRep ρ out (p + q) := by
  have hraw := add_specs_raw hP.1 hQ.1 hcontrol hcandidate hout
  constructor
  · exact ⟨hraw.1,
      hraw.2.trans hmath⟩
  · intro hsum
    rcases hcontrol with
      ⟨hsame, hopposite, hfinite, doubleKind, genericCase,
        hdoubleKind, hdoubleCase, hgenericCase, hactive⟩
    rcases hout with
      ⟨inactiveX0, inactiveY0, inactiveX, inactiveY,
        hinactiveX0, hinactiveY0, hinactiveX, hinactiveY, hX, hY,
        bothInfinity, oppositePair, finiteOpposite,
        hbothInfinity, hoppositePair, hfiniteOpposite, houtInfinity⟩
    rcases p with _ | ⟨px, py, hpcurve⟩
    · have hpinf := Reference.Aux.represents_zero hP.1
      have hpcoords := hP.2 rfl
      rcases q with _ | ⟨qx, qy, hqcurve⟩
      · have hqinf := Reference.Aux.represents_zero hQ.1
        have hqcoords := hQ.2 rfl
        simp_all [AddControlSpec, SelectAddOutputSpec,
          AffineSlope.AndBitSpec, AffineSlope.SelectZModSpec,
          Modular.Lazy.ZeroTestZModSpec,
          AffineSlope.add, AffineSlope.sub, AffineSlope.ofElem]
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
        simp_all [AffineSlope.AndBitSpec, AffineSlope.SelectZModSpec,
          Modular.Lazy.ZeroTestZModSpec, AffineSlope.add, AffineSlope.sub,
          AffineSlope.ofElem, WeierstrassCurve.Affine.negY, Reference.curve]

end AffineSlope.Aux

end Freigen.F2Z.Examples.P256
