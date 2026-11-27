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

abbrev Fp := Elem base
abbrev Fn := Elem scalar

def fpConst (x : Nat) (h : x < baseModulus) : Fp :=
  Modular.ofNat base x (h.trans_le base.fits) h

def fnConst (x : Nat) (h : x < scalarModulus) : Fn :=
  Modular.ofNat scalar x (h.trans_le scalar.fits) h

def fnOne : Fn := fnConst 1 (by native_decide)

def zero : Fp := fpConst 0 (by native_decide)
def one : Fp := fpConst 1 (by native_decide)
def two : Fp := fpConst 2 (by native_decide)
def three : Fp := fpConst 3 (by native_decide)
def four : Fp := fpConst 4 (by native_decide)
def eight : Fp := fpConst 8 (by native_decide)

def curveB : Fp := fpConst
  0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
  (by native_decide)

def generatorX : Fp := fpConst
  0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
  (by native_decide)

def generatorY : Fp := fpConst
  0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
  (by native_decide)

structure Projective where
  X : Fp
  Y : Fp
  Z : Fp

namespace Projective

/-- A projective carrier retained at the circuit boundary.  ECDSA supplies
`Z = 1`; elliptic-curve semantics live exclusively in `P256.Reference`. -/
def Valid (P : Projective) (ρ : WF.Valuation) : Prop :=
  P.X.Valid ρ ∧ P.Y.Valid ρ ∧ P.Z.Valid ρ

def WFRel (lv rv : WF.Valuation) (P Q : Projective) : Prop :=
  Elem.WFRel lv rv P.X Q.X ∧ Elem.WFRel lv rv P.Y Q.Y ∧
    Elem.WFRel lv rv P.Z Q.Z

namespace Lazy

abbrev Rep := Modular.Lazy.Rep base

def OnCurveZModSpec (ρ : WF.Valuation) (x y : Fp) : Prop :=
  let X : ZMod base.modulus :=
    Int.castRingHom (ZMod base.modulus) (x.val.intVal.eval ρ.int)
  let Y : ZMod base.modulus :=
    Int.castRingHom (ZMod base.modulus) (y.val.intVal.eval ρ.int)
  Y ^ 2 = X ^ 3 - 3 * X +
    (0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b :
      ZMod base.modulus)

def mul (x y : Rep) : Circuit Rep := Modular.Lazy.mul base x y

/-- Fused affine curve check.  Mathlib's equation is the semantic endpoint;
this implementation merely supplies its integer constraints. -/
def assertOnCurve (x y : Fp) : Circuit Unit := do
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

abbrev Rep := Modular.Lazy.Rep base

structure Point where
  X : Rep
  Y : Rep
  infinity : LC ℤ

/-- Construction invariant for affine circuit state.  Coordinates are
canonical integer representatives; the separate infinity flag is Boolean.
This is stronger than the quotient semantics and is consumed only by witness
generation/completeness. -/
def Point.Valid (P : Point) (ρ : WF.Valuation) : Prop :=
  P.X.bound = 2 ∧ P.X.Valid ρ ∧
    P.X.intVal.eval ρ.int < base.modulus ∧
    P.Y.bound = 2 ∧ P.Y.Valid ρ ∧
    P.Y.intVal.eval ρ.int < base.modulus ∧
    (P.infinity.eval ρ.int = 0 ∨ P.infinity.eval ρ.int = 1)

def Point.WFRel (lv rv : WF.Valuation) (left right : Point) : Prop :=
  left.X.WFRel lv rv right.X ∧ left.Y.WFRel lv rv right.Y ∧
    WF.LCEq lv.int rv.int left.infinity right.infinity

def ofElems (x y : Fp) : Point :=
  ⟨Modular.Lazy.ofElem base x, Modular.Lazy.ofElem base y, 0⟩

def infinity : Point :=
  ⟨Modular.Lazy.ofElem base zero, Modular.Lazy.ofElem base zero, 1⟩

def add (x y : Rep) : Rep := Modular.Lazy.add base x y
def sub (x y : Rep) : Rep := Modular.Lazy.sub base x y
def scale (k : Nat) (x : Rep) : Rep := Modular.Lazy.scale base k x
def ofElem (x : Fp) : Rep := Modular.Lazy.ofElem base x

def AndBitSpec (ρ : WF.Valuation) (x y out : LC ℤ) : Prop :=
  out.eval ρ.int = x.eval ρ.int * y.eval ρ.int ∧
    (out.eval ρ.int = 0 ∨ out.eval ρ.int = 1)

def SelectZModSpec (ρ : WF.Valuation) (choose : LC ℤ)
    (whenOne whenZero out : Rep) : Prop :=
  (choose.eval ρ.int = 1 →
      Modular.Lazy.evalZMod base out ρ =
        Modular.Lazy.evalZMod base whenOne ρ) ∧
  (choose.eval ρ.int = 0 →
      Modular.Lazy.evalZMod base out ρ =
        Modular.Lazy.evalZMod base whenZero ρ)

/-- Boolean conjunction as one witnessed bit and one R1C. -/
def andBit (x y : LC ℤ) : Circuit (LC ℤ) := do
  let bits ← hint h![x, y] fun h![(a : Int), (b : Int)] =>
    pure $ Vector.ofFn (n := 1) fun _ => a = 1 && b = 1
  let out ← U.fromWord { bitsLE := bits }
  assertR1C x y out.intVal
  pure out.intVal

/-- Three-input conjunction.  Keeping the intermediate product inside this
gadget gives completeness a local Boolean invariant instead of exposing it
to callers. -/
def and3Bit (x y z : LC ℤ) : Circuit (LC ℤ) := do
  let xy ← andBit x y
  andBit z xy

/-- Exact selection at a statically chosen witness width and slack bound. -/
def selectRep (width outBound : Nat) (description : String)
    (choose : LC ℤ) (whenOne whenZero : Rep) : Circuit Rep := do
  let bits ← hint h![choose, whenOne.intVal, whenZero.intVal]
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
def selectCanonical (choose : LC ℤ) (whenOne whenZero : Rep) : Circuit Rep :=
  selectRep 256 2 "canonical" choose whenOne whenZero

/-- Exact selection for temporary formula operands.  Six slack bits cover
the biased differences and the `3*x^2 - 3` tangent numerator. -/
def selectFormula (choose : LC ℤ) (whenOne whenZero : Rep) : Circuit Rep :=
  selectRep 262 66 "affine formula" choose whenOne whenZero

/-- Complete affine doubling.  At infinity `(x,y)=(0,0)`: adding three times
the infinity bit cancels the curve's `a = -3` tangent numerator, while adding
the bit to `2*y` makes the denominator one.  The ordinary output equations
then return `(0,0)` directly, with no coordinate selectors. -/
def doubleSlope (P : Point) : Circuit Rep := do
  let x2 ← Modular.Lazy.mul base P.X P.X
  let numerator := add (sub (scale 3 x2) (ofElem three))
    ⟨3 • P.infinity, 1⟩
  let denominator := add (scale 2 P.Y) ⟨P.infinity, 1⟩
  Modular.Lazy.divide base denominator numerator

def finishDouble (P : Point) (slope : Rep) : Circuit Point := do
  let x3 ← Modular.Lazy.mulSubToElem base slope slope (scale 2 P.X)
  let x3r := ofElem x3
  let y3 ← Modular.Lazy.mulSubToElem base slope (sub P.X x3r) P.Y
  pure ⟨x3r, ofElem y3, P.infinity⟩

def doubleComplete (P : Point) : Circuit Point := do
  let slope ← doubleSlope P
  finishDouble P slope

/-- Complete affine addition.  Two verified zero tests distinguish chord,
tangent, and opposite-point cases.  In inactive infinity/opposite branches
the slope relation is changed to the harmless `slope * 1 = 0`; the final two
canonical coordinates are then selected from the appropriate identity case.
-/
structure AddControl where
  sameX : LC ℤ
  oppositeY : LC ℤ
  finite : LC ℤ
  doubleCase : LC ℤ
  active : LC ℤ

def AddControl.WFRel (lv rv : WF.Valuation)
    (left right : AddControl) : Prop :=
  WF.LCEq lv.int rv.int left.sameX right.sameX ∧
    WF.LCEq lv.int rv.int left.oppositeY right.oppositeY ∧
    WF.LCEq lv.int rv.int left.finite right.finite ∧
    WF.LCEq lv.int rv.int left.doubleCase right.doubleCase ∧
    WF.LCEq lv.int rv.int left.active right.active

def classifyAdd (P Q : Point) : Circuit AddControl := do
  let dx := sub Q.X P.X
  let ysum := add P.Y Q.Y
  let sameX ← Modular.Lazy.zeroTest base dx
  let oppositeY ← Modular.Lazy.zeroTest base ysum
  let finite ← andBit (LC.ofConst 1 - P.infinity)
    (LC.ofConst 1 - Q.infinity)
  let doubleKind ← andBit sameX (LC.ofConst 1 - oppositeY)
  let doubleCase ← andBit finite doubleKind
  let genericCase ← andBit finite (LC.ofConst 1 - sameX)
  let active := doubleCase + genericCase
  pure ⟨sameX, oppositeY, finite, doubleCase, active⟩

structure SlopeOperands where
  numerator : Rep
  denominator : Rep

def SlopeOperands.WFRel (lv rv : WF.Valuation)
    (left right : SlopeOperands) : Prop :=
  left.numerator.WFRel lv rv right.numerator ∧
    left.denominator.WFRel lv rv right.denominator

def SlopeOperands.Valid (operands : SlopeOperands)
    (ρ : WF.Valuation) : Prop :=
  operands.numerator.Valid ρ ∧ operands.numerator.bound = 66 ∧
    operands.denominator.Valid ρ ∧ operands.denominator.bound = 66

def selectRawSlopeOperands (P Q : Point)
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

def activateSlopeOperands (_P _Q : Point) (control : AddControl)
    (selected : SlopeOperands) : Circuit SlopeOperands := do
  let numerator ←
    selectFormula control.active selected.numerator (ofElem zero)
  let denominator ←
    selectFormula control.active selected.denominator (ofElem one)

  pure ⟨numerator, denominator⟩

def selectSlopeOperands (P Q : Point)
    (control : AddControl) : Circuit SlopeOperands := do
  let selected ← selectRawSlopeOperands P Q control
  activateSlopeOperands P Q control selected

def finishAddCandidate (P Q : Point)
    (operands : SlopeOperands) : Circuit (Rep × Rep) := do
  let slope ← Modular.Lazy.divide base operands.denominator operands.numerator
  let candidateX ← Modular.Lazy.mulSubToElem base slope slope (add P.X Q.X)
  let candidateXr := ofElem candidateX
  let candidateY ← Modular.Lazy.mulSubToElem base slope
    (sub P.X candidateXr) P.Y
  let candidateYr := ofElem candidateY
  pure (candidateXr, candidateYr)

def addCandidate (P Q : Point) (control : AddControl) : Circuit (Rep × Rep) := do
  let operands ← selectSlopeOperands P Q control
  finishAddCandidate P Q operands

def selectAddOutput (P Q : Point) (control : AddControl)
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

def addComplete (P Q : Point) : Circuit Point := do
  let control ← classifyAdd P Q
  let candidate ← addCandidate P Q control
  selectAddOutput P Q control candidate

end AffineSlope

end Freigen.F2Z.Examples.P256
