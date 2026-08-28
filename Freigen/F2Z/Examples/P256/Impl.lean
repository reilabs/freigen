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
def doubleSquareHint (P : Point) : Circuit (Vector (LC Bool) 512) :=
  hint h![P.X.intVal] fun h![(x : Int)] =>
    if hx : 0 ≤ x then
      let value := x.toNat * x.toNat
      let r := value % base.modulus
      let q := value / base.modulus
      pure $ Vector.ofFn (n := 512) fun i =>
        if hi : i.val < 256 then r.testBit i.val
        else q.testBit (i.val - 256)
    else fail s!"negative P-256 doubling x-coordinate {x}"

def doubleSquareDecodeR (bits : Vector (LC Bool) 512) : Circuit (U 256) :=
  U.fromWord {
    bitsLE := Vector.ofFn (n := 256) fun i => bits[i.val]'(by omega) }

def doubleSquareDecodeQ (bits : Vector (LC Bool) 512) : Circuit (U 256) :=
  U.fromWord {
    bitsLE := Vector.ofFn (n := 256) fun i =>
      bits[256 + i.val]'(by omega) }

def doubleSquareCheck (P : Point) (r q : U 256) : Circuit Unit :=
  assertR1C P.X.intVal P.X.intVal
    (r.intVal + base.modulus • q.intVal)

def doubleSquare (P : Point) : Circuit Rep := do
  let bits ← doubleSquareHint P
  let r ← doubleSquareDecodeR bits
  let q ← doubleSquareDecodeQ bits
  doubleSquareCheck P r q
  pure ⟨r.intVal, 2⟩

def doubleSlopeNumerator (P : Point) (x2 : Rep) : Rep :=
  add (sub (scale 3 x2) (ofElem three)) ⟨3 • P.infinity, 1⟩

def doubleSlopeDenominator (P : Point) : Rep :=
  add (scale 2 P.Y) ⟨P.infinity, 1⟩

def doubleSlopeHint (denominator numerator : Rep) :
    Circuit (Vector (LC Bool) 513) :=
  let bias := numerator.bound * base.modulus
  hint h![denominator.intVal, numerator.intVal]
    fun h![(a : Int), (b : Int)] =>
      if ha : 0 ≤ a then
        if hb : 0 ≤ b then
          let d := a.toNat % base.modulus
          if hd : d = 0 then
            fail "zero denominator in P-256 doubling"
          else if hg : Nat.gcd d base.modulus = 1 then
            let inverse :=
              ((Nat.gcdA d base.modulus) % (base.modulus : Int)).toNat
            let value := (inverse * (b.toNat % base.modulus)) % base.modulus
            let shifted := (value : Int) * a + bias - b
            if hs : 0 ≤ shifted then
              let q := shifted.toNat / base.modulus
              pure $ Vector.ofFn (n := 513) fun i =>
                if hi : i.val < 256 then value.testBit i.val
                else q.testBit (i.val - 256)
            else fail s!"negative P-256 doubling slope dividend {shifted}"
          else fail "noninvertible denominator in P-256 doubling"
        else fail s!"negative P-256 doubling numerator {b}"
      else fail s!"negative P-256 doubling denominator {a}"

def doubleSlopeDecodeValue (bits : Vector (LC Bool) 513) : Circuit (U 256) :=
  U.fromWord {
    bitsLE := Vector.ofFn (n := 256) fun i => bits[i.val]'(by omega) }

def doubleSlopeDecodeQ (bits : Vector (LC Bool) 513) : Circuit (U 257) :=
  U.fromWord {
    bitsLE := Vector.ofFn (n := 257) fun i =>
      bits[256 + i.val]'(by omega) }

def doubleSlopeCheck (denominator numerator : Rep)
    (value : U 256) (q : U 257) : Circuit Unit :=
  let bias := numerator.bound * base.modulus
  assertR1C value.intVal denominator.intVal
    (numerator.intVal + base.modulus • q.intVal - LC.ofConst (bias : Int))

def doubleSlopeFromSquare (P : Point) (x2 : Rep) : Circuit Rep := do
  let numerator := doubleSlopeNumerator P x2
  let denominator := doubleSlopeDenominator P
  let bits ← doubleSlopeHint denominator numerator
  let value ← doubleSlopeDecodeValue bits
  let q ← doubleSlopeDecodeQ bits
  doubleSlopeCheck denominator numerator value q
  pure ⟨value.intVal, 2⟩

def doubleSlope (P : Point) : Circuit Rep := do
  let x2 ← doubleSquare P
  doubleSlopeFromSquare P x2

def finishDoubleXTarget (P : Point) : Rep := scale 2 P.X

def finishDoubleXHint (slope target : Rep) :
    Circuit (Vector (LC Bool) 512) :=
  let bias := target.bound * base.modulus
  hint h![slope.intVal, target.intVal]
    fun h![(a : Int), (c : Int)] =>
      let shifted := a * a + bias - c
      if hs : 0 ≤ shifted then
        let value := shifted.toNat
        let r := value % base.modulus
        let q := value / base.modulus
        pure $ Vector.ofFn (n := 512) fun i =>
          if hi : i.val < 256 then r.testBit i.val
          else q.testBit (i.val - 256)
      else fail s!"negative P-256 doubling X dividend {shifted}"

def finishDoubleXDecodeR (bits : Vector (LC Bool) 512) : Circuit (U 256) :=
  U.fromWord {
    bitsLE := Vector.ofFn (n := 256) fun i => bits[i.val]'(by omega) }

def finishDoubleXDecodeQ (bits : Vector (LC Bool) 512) : Circuit (U 256) :=
  U.fromWord {
    bitsLE := Vector.ofFn (n := 256) fun i =>
      bits[256 + i.val]'(by omega) }

def finishDoubleXCheck (slope target : Rep) (r q : U 256) : Circuit Unit :=
  let bias := target.bound * base.modulus
  assertR1C slope.intVal slope.intVal
    (r.intVal + target.intVal + base.modulus • q.intVal -
      LC.ofConst (bias : Int))

def finishDoubleX (P : Point) (slope : Rep) : Circuit Fp := do
  let target := finishDoubleXTarget P
  let bits ← finishDoubleXHint slope target
  let r ← finishDoubleXDecodeR bits
  let q ← finishDoubleXDecodeQ bits
  finishDoubleXCheck slope target r q
  pure ⟨r⟩

def finishDoubleYFactor (P : Point) (x3 : Fp) : Rep :=
  sub P.X (ofElem x3)

def finishDoubleYHint (slope factor target : Rep) :
    Circuit (Vector (LC Bool) 514) :=
  let bias := target.bound * base.modulus
  hint h![slope.intVal, factor.intVal, target.intVal]
    fun h![(a : Int), (b : Int), (c : Int)] =>
      let shifted := a * b + bias - c
      if hs : 0 ≤ shifted then
        let value := shifted.toNat
        let r := value % base.modulus
        let q := value / base.modulus
        pure $ Vector.ofFn (n := 514) fun i =>
          if hi : i.val < 256 then r.testBit i.val
          else q.testBit (i.val - 256)
      else fail s!"negative P-256 doubling Y dividend {shifted}"

def finishDoubleYDecodeR (bits : Vector (LC Bool) 514) : Circuit (U 256) :=
  U.fromWord {
    bitsLE := Vector.ofFn (n := 256) fun i => bits[i.val]'(by omega) }

def finishDoubleYDecodeQ (bits : Vector (LC Bool) 514) : Circuit (U 258) :=
  U.fromWord {
    bitsLE := Vector.ofFn (n := 258) fun i =>
      bits[256 + i.val]'(by omega) }

def finishDoubleYCheck (slope factor target : Rep)
    (r : U 256) (q : U 258) : Circuit Unit :=
  let bias := target.bound * base.modulus
  assertR1C slope.intVal factor.intVal
    (r.intVal + target.intVal + base.modulus • q.intVal -
      LC.ofConst (bias : Int))

def finishDoubleY (P : Point) (slope : Rep) (x3 : Fp) : Circuit Fp := do
  let factor := finishDoubleYFactor P x3
  let bits ← finishDoubleYHint slope factor P.Y
  let r ← finishDoubleYDecodeR bits
  let q ← finishDoubleYDecodeQ bits
  finishDoubleYCheck slope factor P.Y r q
  pure ⟨r⟩

def finishDouble (P : Point) (slope : Rep) : Circuit Point := do
  let x3 ← finishDoubleX P slope
  let x3r := ofElem x3
  let y3 ← finishDoubleY P slope x3
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

/-- P-256 zero test specialized to representatives below `4 * p`.

The affine classifier's `Q.X - P.X` and `P.Y + Q.Y` operands both have this
bound.  An honest canonical inverse makes the first quotient fit in 258 bits,
while the quotient in the zero branch is below four and fits in two bits.
The two integer equations are identical to `Modular.Lazy.zeroTest`; only the
quotient decompositions are narrower. -/
def zeroTestBound4Hint (x : Rep) : Circuit (Vector (LC Bool) 257) :=
  hint h![x.intVal] fun h![(a : Int)] =>
    if ha : 0 ≤ a then
      let value := a.toNat % base.modulus
      let isZero := value = 0
      let inverse := (Nat.gcdA value base.modulus) % (base.modulus : Int)
      pure $ Vector.ofFn (n := 257) fun i =>
        if hi : i.val = 0 then isZero
        else inverse.toNat.testBit (i.val - 1)
    else fail s!"negative bound-4 zero-test operand {a}"

def zeroTestBound4DecodeZero (bits : Vector (LC Bool) 257) :
    Circuit (U 1) :=
  U.fromWord {
    bitsLE := Vector.ofFn (n := 1) fun _ => bits[0] }

def zeroTestBound4DecodeInverse (bits : Vector (LC Bool) 257) :
    Circuit (U 256) :=
  U.fromWord {
    bitsLE := Vector.ofFn (n := 256) fun i =>
      bits[i.val + 1]'(by omega) }

def zeroTestBound4Prepare (x : Rep) : Circuit (LC ℤ × U 256) := do
  let bits ← zeroTestBound4Hint x
  let zWord ← zeroTestBound4DecodeZero bits
  let inverse ← zeroTestBound4DecodeInverse bits
  let z := zWord.intBits[0]
  pure (z, inverse)

def zeroTestBound4InverseCheck (x : Rep) (z : LC ℤ)
    (inverse : U 256) : Circuit Unit := do
  let inverseQBits ← hint h![x.intVal, inverse.intVal, z]
    fun h![(a : Int), (b : Int), (zv : Int)] =>
      let shifted := a * b + base.modulus - (1 - zv)
      if hs : 0 ≤ shifted then
        let q := shifted.toNat / base.modulus
        pure $ Vector.ofFn (n := 258) fun i => q.testBit i
      else fail s!"negative bound-4 inverse quotient {shifted}"
  let inverseQ ← U.fromWord { bitsLE := inverseQBits }
  assertR1C x.intVal inverse.intVal
    ((LC.ofConst 1 - z) + base.modulus • inverseQ.intVal -
      LC.ofConst (base.modulus : Int))

def zeroTestBound4ZeroCheck (x : Rep) (z : LC ℤ) : Circuit Unit := do
  let zeroQBits ← hint h![z, x.intVal] fun h![(b : Int), (a : Int)] =>
    let q := (b * a).toNat / base.modulus
    pure $ Vector.ofFn (n := 2) fun i => q.testBit i
  let zeroQ ← U.fromWord { bitsLE := zeroQBits }
  assertR1C z x.intVal (base.modulus • zeroQ.intVal)

def zeroTestBound4 (x : Rep) : Circuit (LC ℤ) := do
  let (z, inverse) ← zeroTestBound4Prepare x
  zeroTestBound4InverseCheck x z inverse
  zeroTestBound4ZeroCheck x z
  pure z

/-- P-256 zero-test checks specialized to a sum of two canonical
representatives.  The sum is below `2*p`, so the inverse quotient needs 257
bits and the zero-branch quotient is a single bit. -/
def zeroTestCanonicalSumInverseQHint (x : Rep) (z : LC ℤ)
    (inverse : U 256) : Circuit (Vector (LC Bool) 257) :=
  hint h![x.intVal, inverse.intVal, z]
    fun h![(a : Int), (b : Int), (zv : Int)] =>
      let shifted := a * b + base.modulus - (1 - zv)
      if hs : 0 ≤ shifted then
        let q := shifted.toNat / base.modulus
        pure $ Vector.ofFn (n := 257) fun i => q.testBit i
      else fail s!"negative canonical-sum inverse quotient {shifted}"

def zeroTestCanonicalSumInverseQDecode
    (bits : Vector (LC Bool) 257) : Circuit (U 257) :=
  U.fromWord { bitsLE := bits }

def zeroTestCanonicalSumInverseCheck (x : Rep) (z : LC ℤ)
    (inverse : U 256) (q : U 257) : Circuit Unit :=
  assertR1C x.intVal inverse.intVal
    ((LC.ofConst 1 - z) + base.modulus • q.intVal -
      LC.ofConst (base.modulus : Int))

def zeroTestCanonicalSumInverse (x : Rep) (z : LC ℤ)
    (inverse : U 256) : Circuit Unit := do
  let bits ← zeroTestCanonicalSumInverseQHint x z inverse
  let q ← zeroTestCanonicalSumInverseQDecode bits
  zeroTestCanonicalSumInverseCheck x z inverse q

def zeroTestCanonicalSumZeroQHint (x : Rep) (z : LC ℤ) :
    Circuit (Vector (LC Bool) 1) :=
  hint h![z, x.intVal] fun h![(b : Int), (a : Int)] =>
    let q := (b * a).toNat / base.modulus
    pure $ Vector.ofFn (n := 1) fun i => q.testBit i

def zeroTestCanonicalSumZeroQDecode
    (bits : Vector (LC Bool) 1) : Circuit (U 1) :=
  U.fromWord { bitsLE := bits }

def zeroTestCanonicalSumZeroCheck (x : Rep) (z : LC ℤ)
    (q : U 1) : Circuit Unit :=
  assertR1C z x.intVal (base.modulus • q.intVal)

def zeroTestCanonicalSumZero (x : Rep) (z : LC ℤ) : Circuit Unit := do
  let bits ← zeroTestCanonicalSumZeroQHint x z
  let q ← zeroTestCanonicalSumZeroQDecode bits
  zeroTestCanonicalSumZeroCheck x z q

def zeroTestCanonicalSum (x : Rep) : Circuit (LC ℤ) := do
  let (z, inverse) ← zeroTestBound4Prepare x
  zeroTestCanonicalSumInverse x z inverse
  zeroTestCanonicalSumZero x z
  pure z

def classifyAdd (P Q : Point) : Circuit AddControl := do
  let dx := sub Q.X P.X
  let ysum := add P.Y Q.Y
  let sameX ← zeroTestBound4 dx
  let oppositeY ← zeroTestCanonicalSum ysum
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

/-! ## Open-once complete addition

These variants retain the same complete affine case split while opening each
selected field representative only once.  The alternatives are enforced by
gated integer R1Cs, which avoids bit-decomposing intermediate selection-tree
nodes. -/

def selectGated3Rep (width outBound : Nat) (description : String)
    (gate1 gate2 gate3 : LC ℤ) (value1 value2 value3 : Rep) : Circuit Rep := do
  let bits ← hint h![gate1, gate2, value1.intVal, value2.intVal, value3.intVal]
    fun h![(g1 : Int), (g2 : Int), (v1 : Int), (v2 : Int), (v3 : Int)] =>
      let value := if g1 = 1 then v1 else if g2 = 1 then v2 else v3
      if _ : 0 ≤ value then
        pure $ Vector.ofFn (n := width) fun i => value.toNat.testBit i
      else fail s!"negative {description} selection {value}"
  let word ← U.fromWord { bitsLE := bits }
  let out : Rep := ⟨word.intVal, outBound⟩
  assertR1C gate1 (out.intVal - value1.intVal) 0
  assertR1C gate2 (out.intVal - value2.intVal) 0
  assertR1C gate3 (out.intVal - value3.intVal) 0
  pure out

def selectGated4Rep (width outBound : Nat) (description : String)
    (gate1 gate2 gate3 gate4 : LC ℤ)
    (value1 value2 value3 value4 : Rep) : Circuit Rep := do
  let bits ← hint
    h![gate1, gate2, gate3,
      value1.intVal, value2.intVal, value3.intVal, value4.intVal]
    fun h![(g1 : Int), (g2 : Int), (g3 : Int),
      (v1 : Int), (v2 : Int), (v3 : Int), (v4 : Int)] =>
      let value := if g1 = 1 then v1 else if g2 = 1 then v2
        else if g3 = 1 then v3 else v4
      if _ : 0 ≤ value then
        pure $ Vector.ofFn (n := width) fun i => value.toNat.testBit i
      else fail s!"negative {description} selection {value}"
  let word ← U.fromWord { bitsLE := bits }
  let out : Rep := ⟨word.intVal, outBound⟩
  assertR1C gate1 (out.intVal - value1.intVal) 0
  assertR1C gate2 (out.intVal - value2.intVal) 0
  assertR1C gate3 (out.intVal - value3.intVal) 0
  assertR1C gate4 (out.intVal - value4.intVal) 0
  pure out

def selectCollapsedNumeratorTight (P Q : Point)
    (control : AddControl) (x2 : Rep) : Circuit Rep :=
  selectGated3Rep 259 5 "collapsed numerator"
    control.doubleCase (control.active - control.doubleCase)
      (LC.ofConst 1 - control.active)
    (sub (scale 3 x2) (ofElem three)) (sub Q.Y P.Y) (ofElem zero)

def selectCollapsedDenominatorTight (P Q : Point)
    (control : AddControl) : Circuit Rep :=
  selectGated3Rep 258 3 "collapsed denominator"
    control.doubleCase (control.active - control.doubleCase)
      (LC.ofConst 1 - control.active)
    (scale 2 P.Y) (sub Q.X P.X) (ofElem one)

def finishSelectSlopeOperandsCollapsedTight (P Q : Point)
    (control : AddControl) (x2 : Rep) : Circuit SlopeOperands := do
  let numerator ← selectCollapsedNumeratorTight P Q control x2
  let denominator ← selectCollapsedDenominatorTight P Q control
  pure ⟨numerator, denominator⟩

def selectSlopeOperandsCollapsedTight (P Q : Point)
    (control : AddControl) : Circuit SlopeOperands := do
  let x2 ← doubleSquare P
  finishSelectSlopeOperandsCollapsedTight P Q control x2

/-! Legacy open-once slope selector API.  Keep its original 66-bound
representatives for downstream callers; production uses the tight variant
above. -/

def selectCollapsedNumerator (P Q : Point)
    (control : AddControl) (x2 : Rep) : Circuit Rep :=
  selectGated3Rep 262 66 "collapsed numerator"
    control.doubleCase (control.active - control.doubleCase)
      (LC.ofConst 1 - control.active)
    (sub (scale 3 x2) (ofElem three)) (sub Q.Y P.Y) (ofElem zero)

def selectCollapsedDenominator (P Q : Point)
    (control : AddControl) : Circuit Rep :=
  selectGated3Rep 262 66 "collapsed denominator"
    control.doubleCase (control.active - control.doubleCase)
      (LC.ofConst 1 - control.active)
    (scale 2 P.Y) (sub Q.X P.X) (ofElem one)

def finishSelectSlopeOperandsCollapsed (P Q : Point)
    (control : AddControl) (x2 : Rep) : Circuit SlopeOperands := do
  let numerator ← selectCollapsedNumerator P Q control x2
  let denominator ← selectCollapsedDenominator P Q control
  pure ⟨numerator, denominator⟩

def selectSlopeOperandsCollapsed (P Q : Point)
    (control : AddControl) : Circuit SlopeOperands := do
  let x2 ← Modular.Lazy.mul base P.X P.X
  finishSelectSlopeOperandsCollapsed P Q control x2

def collapsedSlopeHint (operands : SlopeOperands) :
    Circuit (Vector (LC Bool) 514) :=
  let bias := operands.numerator.bound * base.modulus
  hint h![operands.denominator.intVal, operands.numerator.intVal]
    fun h![(a : Int), (b : Int)] =>
      if ha : 0 ≤ a then
        if hb : 0 ≤ b then
          let d := a.toNat % base.modulus
          if hd : d = 0 then
            fail "zero denominator in P-256 collapsed addition"
          else if hg : Nat.gcd d base.modulus = 1 then
            let inverse :=
              ((Nat.gcdA d base.modulus) % (base.modulus : Int)).toNat
            let value := (inverse * (b.toNat % base.modulus)) % base.modulus
            let shifted := (value : Int) * a + bias - b
            if hs : 0 ≤ shifted then
              let q := shifted.toNat / base.modulus
              pure $ Vector.ofFn (n := 514) fun i =>
                if hi : i.val < 256 then value.testBit i.val
                else q.testBit (i.val - 256)
            else fail s!"negative P-256 collapsed slope dividend {shifted}"
          else fail "noninvertible denominator in P-256 collapsed addition"
        else fail s!"negative P-256 collapsed numerator {b}"
      else fail s!"negative P-256 collapsed denominator {a}"

def collapsedSlopeDecodeValue
    (bits : Vector (LC Bool) 514) : Circuit (U 256) :=
  U.fromWord {
    bitsLE := Vector.ofFn (n := 256) fun i => bits[i.val]'(by omega) }

def collapsedSlopeDecodeQ
    (bits : Vector (LC Bool) 514) : Circuit (U 258) :=
  U.fromWord {
    bitsLE := Vector.ofFn (n := 258) fun i =>
      bits[256 + i.val]'(by omega) }

def collapsedSlopeCheck (operands : SlopeOperands)
    (value : U 256) (q : U 258) : Circuit Unit :=
  let bias := operands.numerator.bound * base.modulus
  assertR1C value.intVal operands.denominator.intVal
    (operands.numerator.intVal + base.modulus • q.intVal -
      LC.ofConst (bias : Int))

def collapsedSlope (operands : SlopeOperands) : Circuit Rep := do
  let bits ← collapsedSlopeHint operands
  let value ← collapsedSlopeDecodeValue bits
  let q ← collapsedSlopeDecodeQ bits
  collapsedSlopeCheck operands value q
  pure ⟨value.intVal, 2⟩

def collapsedCandidateXTarget (P Q : Point) : Rep := add P.X Q.X

def collapsedCandidateXHint (slope target : Rep) :
    Circuit (Vector (LC Bool) 512) :=
  let bias := target.bound * base.modulus
  hint h![slope.intVal, target.intVal]
    fun h![(a : Int), (c : Int)] =>
      let shifted := a * a + bias - c
      if hs : 0 ≤ shifted then
        let value := shifted.toNat
        let r := value % base.modulus
        let q := value / base.modulus
        pure $ Vector.ofFn (n := 512) fun i =>
          if hi : i.val < 256 then r.testBit i.val
          else q.testBit (i.val - 256)
      else fail s!"negative P-256 collapsed X dividend {shifted}"

def collapsedCandidateXDecodeR
    (bits : Vector (LC Bool) 512) : Circuit (U 256) :=
  U.fromWord {
    bitsLE := Vector.ofFn (n := 256) fun i => bits[i.val]'(by omega) }

def collapsedCandidateXDecodeQ
    (bits : Vector (LC Bool) 512) : Circuit (U 256) :=
  U.fromWord {
    bitsLE := Vector.ofFn (n := 256) fun i =>
      bits[256 + i.val]'(by omega) }

def collapsedCandidateXCheck (slope target : Rep)
    (r q : U 256) : Circuit Unit :=
  let bias := target.bound * base.modulus
  assertR1C slope.intVal slope.intVal
    (r.intVal + target.intVal + base.modulus • q.intVal -
      LC.ofConst (bias : Int))

def collapsedCandidateX (P Q : Point) (slope : Rep) : Circuit Fp := do
  let target := collapsedCandidateXTarget P Q
  let bits ← collapsedCandidateXHint slope target
  let r ← collapsedCandidateXDecodeR bits
  let q ← collapsedCandidateXDecodeQ bits
  collapsedCandidateXCheck slope target r q
  pure ⟨r⟩

def collapsedCandidateYFactor (P : Point) (x3 : Fp) : Rep :=
  sub P.X (ofElem x3)

def collapsedCandidateYHint (slope factor target : Rep) :
    Circuit (Vector (LC Bool) 514) :=
  let bias := target.bound * base.modulus
  hint h![slope.intVal, factor.intVal, target.intVal]
    fun h![(a : Int), (b : Int), (c : Int)] =>
      let shifted := a * b + bias - c
      if hs : 0 ≤ shifted then
        let value := shifted.toNat
        let r := value % base.modulus
        let q := value / base.modulus
        pure $ Vector.ofFn (n := 514) fun i =>
          if hi : i.val < 256 then r.testBit i.val
          else q.testBit (i.val - 256)
      else fail s!"negative P-256 collapsed Y dividend {shifted}"

def collapsedCandidateYDecodeR
    (bits : Vector (LC Bool) 514) : Circuit (U 256) :=
  U.fromWord {
    bitsLE := Vector.ofFn (n := 256) fun i => bits[i.val]'(by omega) }

def collapsedCandidateYDecodeQ
    (bits : Vector (LC Bool) 514) : Circuit (U 258) :=
  U.fromWord {
    bitsLE := Vector.ofFn (n := 258) fun i =>
      bits[256 + i.val]'(by omega) }

def collapsedCandidateYCheck (slope factor target : Rep)
    (r : U 256) (q : U 258) : Circuit Unit :=
  let bias := target.bound * base.modulus
  assertR1C slope.intVal factor.intVal
    (r.intVal + target.intVal + base.modulus • q.intVal -
      LC.ofConst (bias : Int))

def collapsedCandidateY (P : Point) (slope : Rep) (x3 : Fp) : Circuit Fp := do
  let factor := collapsedCandidateYFactor P x3
  let bits ← collapsedCandidateYHint slope factor P.Y
  let r ← collapsedCandidateYDecodeR bits
  let q ← collapsedCandidateYDecodeQ bits
  collapsedCandidateYCheck slope factor P.Y r q
  pure ⟨r⟩

def finishAddCandidateCollapsedX (P Q : Point)
    (operands : SlopeOperands) : Circuit Rep := do
  let slope ← collapsedSlope operands
  let candidateX ← collapsedCandidateX P Q slope
  pure (ofElem candidateX)

def finishAddCandidateCollapsed (P Q : Point)
    (operands : SlopeOperands) : Circuit (Rep × Rep) := do
  let slope ← collapsedSlope operands
  let candidateX ← collapsedCandidateX P Q slope
  let candidateY ← collapsedCandidateY P slope candidateX
  pure (ofElem candidateX, ofElem candidateY)

def addCandidateCollapsed (P Q : Point)
    (control : AddControl) : Circuit (Rep × Rep) := do
  let operands ← selectSlopeOperandsCollapsedTight P Q control
  finishAddCandidateCollapsed P Q operands

def selectAddCoordinateCollapsed (Pcoord Qcoord candidate : Rep)
    (P Q : Point) (control : AddControl) (bothInfinity : LC ℤ) :
    Circuit Rep := do
  selectGated4Rep 256 2 "collapsed output"
    control.active P.infinity (Q.infinity - bothInfinity)
      (control.finite - control.active)
    candidate Qcoord Pcoord (ofElem zero)

def selectAddOutputCollapsed (P Q : Point) (control : AddControl)
    (candidate : Rep × Rep) : Circuit Point := do
  let bothInfinity ← andBit P.infinity Q.infinity
  let X ← selectAddCoordinateCollapsed P.X Q.X candidate.1
    P Q control bothInfinity
  let Y ← selectAddCoordinateCollapsed P.Y Q.Y candidate.2
    P Q control bothInfinity
  let finiteOpposite ← and3Bit control.sameX control.oppositeY control.finite
  pure ⟨X, Y, bothInfinity + finiteOpposite⟩

def addCompleteCollapsed (P Q : Point) : Circuit Point := do
  let control ← classifyAdd P Q
  let candidate ← addCandidateCollapsed P Q control
  selectAddOutputCollapsed P Q control candidate

end AffineSlope

end Freigen.F2Z.Examples.P256
