import Freigen.F2Z.Examples.Modular.Impl

/-!
# P-256 circuit implementations

This module contains only circuit representations and executable gadgets.
ECDSA uses affine slope addition with an explicit infinity bit and a small
projective carrier for its public-key input.  There is no independent
elliptic-curve value model here: mathematical semantics come from Mathlib in
`P256.Reference`.

Correctness results are provided by
`Freigen.F2Z.Examples.P256`.
-/

namespace Freigen.F2Z.Examples.P256

set_option maxRecDepth 10000

open Std.Do
open scoped Std.Do
open Modular

def baseModulus : Nat :=
  0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

def scalarModulus : Nat :=
  0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

def base : Params 256 where
  modulus := baseModulus
  bitsPositive := by omega
  positive := by native_decide
  fits := by native_decide
  lowerHalf := by native_decide

def scalar : Params 256 where
  modulus := scalarModulus
  bitsPositive := by omega
  positive := by native_decide
  fits := by native_decide
  lowerHalf := by native_decide

abbrev Fp [ctx : Context] := Elem base
abbrev Fn [ctx : Context] := Elem scalar

def fpConst [ctx : Context] (x : Nat) (h : x < baseModulus) : Fp :=
  Modular.ofNat base x (h.trans_le base.fits) h

def fnConst [ctx : Context] (x : Nat) (h : x < scalarModulus) : Fn :=
  Modular.ofNat scalar x (h.trans_le scalar.fits) h

def fnOne [ctx : Context] : Fn := fnConst 1 (by native_decide)

def zero [ctx : Context] : Fp := fpConst 0 (by native_decide)
def one [ctx : Context] : Fp := fpConst 1 (by native_decide)
def two [ctx : Context] : Fp := fpConst 2 (by native_decide)
def three [ctx : Context] : Fp := fpConst 3 (by native_decide)
def four [ctx : Context] : Fp := fpConst 4 (by native_decide)
def eight [ctx : Context] : Fp := fpConst 8 (by native_decide)

def curveB [ctx : Context] : Fp := fpConst
  0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
  (by native_decide)

def generatorX [ctx : Context] : Fp := fpConst
  0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
  (by native_decide)

def generatorY [ctx : Context] : Fp := fpConst
  0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
  (by native_decide)

structure Projective [ctx : Context] where
  X : Fp
  Y : Fp
  Z : Fp

namespace Projective

/-- A projective carrier retained at the circuit boundary.  ECDSA supplies
`Z = 1`; elliptic-curve semantics live exclusively in `P256.Reference`. -/
def Valid [ctx : Context] (P : @Projective ctx)
    (ρ : @WF.Valuation ctx) : Prop :=
  P.X.Valid ρ ∧ P.Y.Valid ρ ∧ P.Z.Valid ρ

def WFRel {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx)
    (P : @Projective leftCtx) (Q : @Projective rightCtx) : Prop :=
  Elem.WFRel (leftCtx := leftCtx) (rightCtx := rightCtx) lv rv
      (@Projective.X leftCtx P) (@Projective.X rightCtx Q) ∧
    Elem.WFRel (leftCtx := leftCtx) (rightCtx := rightCtx) lv rv
      (@Projective.Y leftCtx P) (@Projective.Y rightCtx Q) ∧
    Elem.WFRel (leftCtx := leftCtx) (rightCtx := rightCtx) lv rv
      (@Projective.Z leftCtx P) (@Projective.Z rightCtx Q)

namespace Lazy

abbrev Rep [ctx : Context] := Modular.Lazy.Rep base

def OnCurveZModSpec [ctx : Context] (ρ : @WF.Valuation ctx)
    (x y : Fp) : Prop :=
  let X : ZMod base.modulus :=
    Int.castRingHom (ZMod base.modulus) (ρ.int x.val.intVal)
  let Y : ZMod base.modulus :=
    Int.castRingHom (ZMod base.modulus) (ρ.int y.val.intVal)
  Y ^ 2 = X ^ 3 - 3 * X +
    (0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b :
      ZMod base.modulus)

def mul [ctx : Context] (x y : Rep) : Circuit Rep := Modular.Lazy.mul base x y

/-- Fused affine curve check.  Mathlib's equation is the semantic endpoint;
this implementation merely supplies its integer constraints. -/
def assertOnCurve [ctx : Context] (x y : Fp) : Circuit Unit := do
  let x := Modular.Lazy.ofElem base x
  let y := Modular.Lazy.ofElem base y
  let x2 ← mul x x
  let x3 ← mul x2 x
  let rhs := Modular.Lazy.sub base
    (Modular.Lazy.add base x3 (Modular.Lazy.ofElem base curveB))
    (Modular.Lazy.scale base 3 x)
  Modular.Lazy.assertMulEq base y y rhs

end Lazy

end Projective

/-! ## Affine slope implementation used by ECDSA

The optimized verifier keeps points affine and proves each chord or tangent
with its slope.  Infinity is represented by `(0, 0, true)`; its bit supplies
the inactive doubling denominator and a linear tangent-numerator correction.
Coordinates emitted by an
operation are canonical 256-bit representatives, while short-lived selected
formula operands may use six extra bits of representative slack.
-/

namespace AffineSlope

abbrev Rep [ctx : Context] := Modular.Lazy.Rep base

structure Point [ctx : Context] where
  X : Rep
  Y : Rep
  infinity : ctx.Wℤ

/-- Construction invariant for affine circuit state.  Coordinates are
canonical integer representatives; the separate infinity flag is Boolean.
This is stronger than the quotient semantics and is consumed only by witness
generation/completeness. -/
def Point.Valid [ctx : Context] (P : @Point ctx)
    (ρ : @WF.Valuation ctx) : Prop :=
  P.X.bound = 2 ∧ P.X.Valid ρ ∧
    ρ.int P.X.intVal < base.modulus ∧
    P.Y.bound = 2 ∧ P.Y.Valid ρ ∧
    ρ.int P.Y.intVal < base.modulus ∧
    (ρ.int P.infinity = 0 ∨ ρ.int P.infinity = 1)

def Point.WFRel {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx)
    (left : @Point leftCtx) (right : @Point rightCtx) : Prop :=
  Modular.Lazy.Rep.WFRel (leftCtx := leftCtx) (rightCtx := rightCtx) lv rv
      (@Point.X leftCtx left) (@Point.X rightCtx right) ∧
    Modular.Lazy.Rep.WFRel (leftCtx := leftCtx) (rightCtx := rightCtx) lv rv
      (@Point.Y leftCtx left) (@Point.Y rightCtx right) ∧
    WF.LCEq lv.int rv.int (@Point.infinity leftCtx left)
      (@Point.infinity rightCtx right)

def ofElems [ctx : Context] (x y : Fp) : Point :=
  ⟨Modular.Lazy.ofElem base x, Modular.Lazy.ofElem base y, 0⟩

def infinity [ctx : Context] : Point :=
  ⟨Modular.Lazy.ofElem base zero, Modular.Lazy.ofElem base zero, 1⟩

def add [ctx : Context] (x y : Rep) : Rep := Modular.Lazy.add base x y
def sub [ctx : Context] (x y : Rep) : Rep := Modular.Lazy.sub base x y
def scale [ctx : Context] (k : Nat) (x : Rep) : Rep := Modular.Lazy.scale base k x
def ofElem [ctx : Context] (x : Fp) : Rep := Modular.Lazy.ofElem base x

def AndBitSpec [ctx : Context] (ρ : @WF.Valuation ctx)
    (x y out : ctx.Wℤ) : Prop :=
  ρ.int out = ρ.int x * ρ.int y ∧
    (ρ.int out = 0 ∨ ρ.int out = 1)

def SelectZModSpec [ctx : Context] (ρ : @WF.Valuation ctx) (choose : ctx.Wℤ)
    (whenOne whenZero out : Rep) : Prop :=
  (ρ.int choose = 1 →
      Modular.Lazy.evalZMod base out ρ =
        Modular.Lazy.evalZMod base whenOne ρ) ∧
  (ρ.int choose = 0 →
      Modular.Lazy.evalZMod base out ρ =
        Modular.Lazy.evalZMod base whenZero ρ)

/-- Boolean conjunction as one witnessed bit and one R1C. -/
def andBit [ctx : Context] (x y : ctx.Wℤ) : @Circuit ctx ctx.Wℤ := do
  let bits ← hint (argTps := [.z, .z]) h![x, y]
    fun h![(a : Int), (b : Int)] =>
    pure $ Vector.ofFn (n := 1) fun _ => a = 1 && b = 1
  let out ← U.fromWord { bitsLE := bits }
  assertR1C x y out.intVal
  pure out.intVal

/-- Three-input conjunction.  Keeping the intermediate product inside this
gadget gives completeness a local Boolean invariant instead of exposing it
to callers. -/
def and3Bit [ctx : Context] (x y z : ctx.Wℤ) : @Circuit ctx ctx.Wℤ := do
  let xy ← andBit x y
  andBit z xy

/-- Exact selection at a statically chosen witness width and slack bound. -/
def selectRep [ctx : Context] (width outBound : Nat) (description : String)
    (choose : ctx.Wℤ) (whenOne whenZero : Rep) : @Circuit ctx Rep := do
  let bits ← hint (argTps := [.z, .z, .z])
    h![choose, whenOne.intVal, whenZero.intVal]
    fun h![(b : Int), (x : Int), (y : Int)] =>
      let value := if b = 1 then x else y
      if _ : 0 ≤ value then
        pure $ Vector.ofFn (n := width) fun i => value.toNat.testBit i
      else fail s!"negative {description} selection {value}"
  let out ← U.fromWord { bitsLE := bits }
  assertR1C choose (whenOne.intVal - whenZero.intVal)
    (out.intVal - whenZero.intVal)
  pure ⟨out.intVal, outBound⟩

/-- Exact selection between canonical representatives.  The result is again
a 256-bit representative and can safely remain in the affine state. -/
def selectCanonical [ctx : Context] (choose : ctx.Wℤ)
    (whenOne whenZero : Rep) : @Circuit ctx Rep :=
  selectRep 256 2 "canonical" choose whenOne whenZero

/-- Exact selection for temporary formula operands.  Six slack bits cover
the biased differences and the `3*x^2 - 3` tangent numerator. -/
def selectFormula [ctx : Context] (choose : ctx.Wℤ)
    (whenOne whenZero : Rep) : @Circuit ctx Rep :=
  selectRep 262 66 "affine formula" choose whenOne whenZero

/-- Complete affine doubling.  At infinity `(x,y)=(0,0)`: adding three times
the infinity bit cancels the curve's `a = -3` tangent numerator, while adding
the bit to `2*y` makes the denominator one.  The ordinary output equations
then return `(0,0)` directly, with no coordinate selectors. -/
def doubleSlope [ctx : Context] (P : Point) : Circuit Rep := do
  let x2 ← Modular.Lazy.mul base P.X P.X
  let numerator := add (sub (scale 3 x2) (ofElem three))
    ⟨3 • P.infinity, 1⟩
  let denominator := add (scale 2 P.Y) ⟨P.infinity, 1⟩
  Modular.Lazy.divide base denominator numerator

def finishDouble [ctx : Context] (P : Point) (slope : Rep) : Circuit Point := do
  let x3 ← Modular.Lazy.mulSubToElem base slope slope (scale 2 P.X)
  let x3r := ofElem x3
  let y3 ← Modular.Lazy.mulSubToElem base slope (sub P.X x3r) P.Y
  pure ⟨x3r, ofElem y3, P.infinity⟩

def doubleComplete [ctx : Context] (P : Point) : Circuit Point := do
  let slope ← doubleSlope P
  finishDouble P slope

/-- Complete affine addition.  Two verified zero tests distinguish chord,
tangent, and opposite-point cases.  In inactive infinity/opposite branches
the slope relation is changed to the harmless `slope * 1 = 0`; the final two
canonical coordinates are then selected from the appropriate identity case.
-/
structure AddControl [ctx : Context] where
  sameX : ctx.Wℤ
  oppositeY : ctx.Wℤ
  finite : ctx.Wℤ
  doubleCase : ctx.Wℤ
  active : ctx.Wℤ

def AddControl.WFRel {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx)
    (left : @AddControl leftCtx) (right : @AddControl rightCtx) : Prop :=
  WF.LCEq lv.int rv.int (@AddControl.sameX leftCtx left)
      (@AddControl.sameX rightCtx right) ∧
    WF.LCEq lv.int rv.int (@AddControl.oppositeY leftCtx left)
      (@AddControl.oppositeY rightCtx right) ∧
    WF.LCEq lv.int rv.int (@AddControl.finite leftCtx left)
      (@AddControl.finite rightCtx right) ∧
    WF.LCEq lv.int rv.int (@AddControl.doubleCase leftCtx left)
      (@AddControl.doubleCase rightCtx right) ∧
    WF.LCEq lv.int rv.int (@AddControl.active leftCtx left)
      (@AddControl.active rightCtx right)

def classifyAdd [ctx : Context] (P Q : Point) : Circuit AddControl := do
  let dx := sub Q.X P.X
  let ysum := add P.Y Q.Y
  let sameX ← Modular.Lazy.zeroTest base dx
  let oppositeY ← Modular.Lazy.zeroTest base ysum
  let finite ← andBit (ofScalar 1 - P.infinity)
    (ofScalar 1 - Q.infinity)
  let doubleKind ← andBit sameX (ofScalar 1 - oppositeY)
  let doubleCase ← andBit finite doubleKind
  let genericCase ← andBit finite (ofScalar 1 - sameX)
  let active := doubleCase + genericCase
  pure ⟨sameX, oppositeY, finite, doubleCase, active⟩

structure SlopeOperands [ctx : Context] where
  numerator : Rep
  denominator : Rep

def SlopeOperands.WFRel {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx)
    (left : @SlopeOperands leftCtx) (right : @SlopeOperands rightCtx) : Prop :=
  Modular.Lazy.Rep.WFRel (leftCtx := leftCtx) (rightCtx := rightCtx) lv rv
      (@SlopeOperands.numerator leftCtx left)
      (@SlopeOperands.numerator rightCtx right) ∧
    Modular.Lazy.Rep.WFRel (leftCtx := leftCtx) (rightCtx := rightCtx) lv rv
      (@SlopeOperands.denominator leftCtx left)
      (@SlopeOperands.denominator rightCtx right)

def SlopeOperands.Valid [ctx : Context] (operands : @SlopeOperands ctx)
    (ρ : @WF.Valuation ctx) : Prop :=
  operands.numerator.Valid ρ ∧ operands.numerator.bound = 66 ∧
    operands.denominator.Valid ρ ∧ operands.denominator.bound = 66

def selectRawSlopeOperands [ctx : Context] (P Q : Point)
    (control : AddControl) : Circuit SlopeOperands := do
  let dx := sub Q.X P.X
  let dy := sub Q.Y P.Y
  let x2 ← Modular.Lazy.mul base P.X P.X
  let doubleNumerator := sub (scale 3 x2) (ofElem three)
  let doubleDenominator := scale 2 P.Y
  let selectedNumerator ←
    selectFormula control.doubleCase doubleNumerator dy
  let selectedDenominator ←
    selectFormula control.doubleCase doubleDenominator dx
  pure ⟨selectedNumerator, selectedDenominator⟩

def activateSlopeOperands [ctx : Context] (_P _Q : Point) (control : AddControl)
    (selected : SlopeOperands) : Circuit SlopeOperands := do
  let numerator ←
    selectFormula control.active selected.numerator (ofElem zero)
  let denominator ←
    selectFormula control.active selected.denominator (ofElem one)

  pure ⟨numerator, denominator⟩

def selectSlopeOperands [ctx : Context] (P Q : Point)
    (control : AddControl) : Circuit SlopeOperands := do
  let selected ← selectRawSlopeOperands P Q control
  activateSlopeOperands P Q control selected

def finishAddCandidate [ctx : Context] (P Q : Point)
    (operands : SlopeOperands) : Circuit (Rep × Rep) := do
  let slope ← Modular.Lazy.divide base operands.denominator operands.numerator
  let candidateX ← Modular.Lazy.mulSubToElem base slope slope (add P.X Q.X)
  let candidateXr := ofElem candidateX
  let candidateY ← Modular.Lazy.mulSubToElem base slope
    (sub P.X candidateXr) P.Y
  let candidateYr := ofElem candidateY
  pure (candidateXr, candidateYr)

def addCandidate [ctx : Context] (P Q : Point) (control : AddControl) : Circuit (Rep × Rep) := do
  let operands ← selectSlopeOperands P Q control
  finishAddCandidate P Q operands

def selectAddOutput [ctx : Context] (P Q : Point) (control : AddControl)
    (candidate : Rep × Rep) : Circuit Point := do
  let inactiveX0 ← selectCanonical Q.infinity P.X (ofElem zero)
  let inactiveY0 ← selectCanonical Q.infinity P.Y (ofElem zero)
  let inactiveX ← selectCanonical P.infinity Q.X inactiveX0
  let inactiveY ← selectCanonical P.infinity Q.Y inactiveY0
  let X ← selectCanonical control.active candidate.1 inactiveX
  let Y ← selectCanonical control.active candidate.2 inactiveY

  let bothInfinity ← andBit P.infinity Q.infinity
  let finiteOpposite ←
    and3Bit control.sameX control.oppositeY control.finite
  pure ⟨X, Y, bothInfinity + finiteOpposite⟩

def addComplete [ctx : Context] (P Q : Point) : Circuit Point := do
  let control ← classifyAdd P Q
  let candidate ← addCandidate P Q control
  selectAddOutput P Q control candidate

end AffineSlope

end Freigen.F2Z.Examples.P256
