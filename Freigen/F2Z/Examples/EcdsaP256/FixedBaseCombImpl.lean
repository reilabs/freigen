import Freigen.F2Z.Examples.EcdsaP256.Radix32Impl
import Freigen.F2Z.Examples.EcdsaP256.DirectTerminalImpl
import Freigen.F2Z.Examples.EcdsaP256.DirectTerminalBlockImpl
import Freigen.F2Z.Examples.P256.CanonicalXImpl

/-!
# Mixed-width fixed-base comb for ECDSA-P256

The generator scalar is recoded into signed odd digits over eight 12-bit
windows, twelve 13-bit windows, and one 4-bit top window.  Large fixed-table
lookups use a 7-bit inner one-hot and an outer-plus-sign one-hot, so only one
pair of 256-bit coordinates is materialized per lookup.
-/

namespace Freigen.F2Z.Examples.EcdsaP256

open Std.Do
open scoped Std.Do
open BigOperators
open Modular
open P256

set_option maxRecDepth 10000

def combBit (k : Fn) (i : Nat) (hi : i < 256) : LC ℤ :=
  if _ : i < 255 then k.val.intBits[i + 1]'(by omega) else 1

def combWindowBits (k : Fn) (offset width : Nat)
    (hfit : offset + width ≤ 256) : Vector (LC ℤ) width :=
  Vector.ofFn fun i => combBit k (offset + i.val) (by omega)

def combWindowValue {width : Nat} (bits : Vector (LC ℤ) width) : LC ℤ :=
  ∑ i : Fin width, (2 ^ i.val : Int) • bits[i]

def fixedMagnitudePoint (offset magnitudeIndex : Nat) : Reference.Point :=
  ((2 * magnitudeIndex + 1) * 2 ^ offset) • Reference.generator

def fixedMagnitudeX (offset magnitudeIndex : Nat) : Nat :=
  Reference.xNat (fixedMagnitudePoint offset magnitudeIndex)

def fixedMagnitudeY (offset magnitudeIndex : Nat) : Nat :=
  Reference.yNat (fixedMagnitudePoint offset magnitudeIndex)

/-- Repeated-addition core for a positional odd-multiple table. -/
def fixedMagnitudePoints (step : Reference.Point) :
    Nat → Reference.Point → List Reference.Point
  | 0, _ => []
  | count + 1, point =>
      point :: fixedMagnitudePoints step count (point + step)

/-- Build one positional odd-multiple table by repeated addition.  This keeps
cost evaluation from recomputing a 256-bit scalar multiplication for every
public coefficient, while the recursive form admits one generic correctness
proof instead of a large `native_decide` certificate per table. -/
def fixedMagnitudeTable (offset count : Nat) : Array Reference.Point :=
  (fixedMagnitudePoints ((2 ^ (offset + 1)) • Reference.generator) count
    ((2 ^ offset) • Reference.generator)).toArray

def signedMagnitudeIndex (width raw : Nat) : Nat :=
  if 2 ^ (width - 1) ≤ raw then raw - 2 ^ (width - 1)
  else 2 ^ (width - 1) - 1 - raw

def selectedFixedY (offset width raw : Nat) : Nat :=
  let y := fixedMagnitudeY offset (signedMagnitudeIndex width raw)
  if 2 ^ (width - 1) ≤ raw then y else base.modulus - y

def fixedSignedPoint (offset width raw : Nat) : Reference.Point :=
  if 2 ^ (width - 1) ≤ raw then
    fixedMagnitudePoint offset (raw - 2 ^ (width - 1))
  else
    -fixedMagnitudePoint offset (2 ^ (width - 1) - 1 - raw)

def xnorBit (sign bit : LC ℤ) : Circuit (LC ℤ) := do
  let both ← AffineSlope.andBit sign bit
  pure (2 • both - sign - bit + 1)

def xnorMagnitudeBits {width : Nat} (bits : Vector (LC ℤ) width)
    (hwidth : 1 ≤ width) :
    Circuit (Vector (LC ℤ) (width - 1)) :=
  Vector.ofFnM fun i : Fin (width - 1) =>
    xnorBit (bits[width - 1]'(by omega)) (bits[i.val]'(by omega))

def coordinateHint (f : Nat → Nat) :
    HList Eff.WitnessSide.denoteF [.z] → Hint (Vector Bool 256)
  | h![(raw : Int)] =>
      pure $ Vector.ofFn fun i => (f raw.toNat).testBit i

def materializeFixedCoordinate (f : Nat → Nat) (raw : LC ℤ) :
    Circuit (U 256) := do
  let bits ← hint h![raw] (coordinateHint f)
  U.fromWord { bitsLE := bits }

def fixedInnerX (table : Array Reference.Point) (width outerIndex : Nat)
    (inner : U 128) : LC ℤ :=
  let magnitudeOuter := outerIndex % 2 ^ (width - 8)
  ∑ i : Fin 128,
    Reference.xNat table[128 * magnitudeOuter + i.val]! • inner.intBits[i]

def fixedInnerY (table : Array Reference.Point) (width outerIndex : Nat)
    (inner : U 128) : LC ℤ :=
  let magnitudeOuter := outerIndex % 2 ^ (width - 8)
  let negative := outerIndex / 2 ^ (width - 8) = 0
  ∑ i : Fin 128,
    (if negative then
      base.modulus - Reference.yNat table[128 * magnitudeOuter + i.val]!
     else Reference.yNat table[128 * magnitudeOuter + i.val]!) • inner.intBits[i]

def assertFactoredCoordinates (width : Nat) (table : Array Reference.Point)
    (inner : U 128) (outer : U (2 ^ (width - 7))) (X Y : U 256) :
    Circuit Unit :=
  WF.foldRange [:2 ^ (width - 7)] () fun o ho _ => do
    assertR1C outer.intBits[o] (X.intVal - fixedInnerX table width o inner) 0
    assertR1C outer.intBits[o] (Y.intVal - fixedInnerY table width o inner) 0

/-- Signed odd fixed-base lookup with a factored magnitude selector.

The lower seven magnitude bits select an affine inner table expression.  The
remaining magnitude bits and the sign select one outer branch; gated R1Cs pin
the two canonical output words to that branch. -/
def lookupFixedFactored (offset width : Nat) (hwidth : 8 ≤ width)
    (bits : Vector (LC ℤ) width) : Circuit AffineSlope.Point := do
  let table := fixedMagnitudeTable offset (2 ^ (width - 1))
  let raw := combWindowValue bits
  let sign := bits[width - 1]'(by omega)
  let magnitudeBits ← xnorMagnitudeBits bits (by omega)
  let innerDigit :=
    ∑ i : Fin 7, (2 ^ i.val : Int) • magnitudeBits[i]
  let outerDigit :=
    (∑ i : Fin (width - 8),
      (2 ^ i.val : Int) • magnitudeBits[i.val + 7]'(by omega)) +
    (2 ^ (width - 8) : Int) • sign
  let inner ← indicators 128 innerDigit
  let outer ← indicators (2 ^ (width - 7)) outerDigit
  let X ← materializeFixedCoordinate (fun d => Reference.xNat
    table[(signedMagnitudeIndex width d)]!) raw
  let Y ← materializeFixedCoordinate (fun d =>
      let y := Reference.yNat table[(signedMagnitudeIndex width d)]!
      if 2 ^ (width - 1) ≤ d then y else base.modulus - y) raw
  assertFactoredCoordinates width table inner outer X Y
  pure ⟨⟨X.intVal, 2⟩, ⟨Y.intVal, 2⟩, 0⟩

def lookupFixed12 (k : Fn) (window : Nat) (hwindow : window < 8) :
    Circuit AffineSlope.Point :=
  lookupFixedFactored (12 * window) 12 (by omega)
    (combWindowBits k (12 * window) 12 (by omega))

def lookupFixed13 (k : Fn) (window : Nat) (hwindow : window < 12) :
    Circuit AffineSlope.Point :=
  lookupFixedFactored (96 + 13 * window) 13 (by omega)
    (combWindowBits k (96 + 13 * window) 13 (by omega))

def topCombPoint (raw parity : Nat) : Reference.Point :=
  if _ : 8 ≤ raw then
    let multiple := (2 * raw + 1 - 16) * 2 ^ 252 - (1 - parity)
    multiple • Reference.generator
  else Reference.generator

def topCombX (index : Nat) : Nat :=
  Reference.xNat (topCombPoint (index % 16) (index / 16))

def topCombY (index : Nat) : Nat :=
  Reference.yNat (topCombPoint (index % 16) (index / 16))

def lookupFixedTop (k : Fn) : Circuit AffineSlope.Point := do
  let bits := combWindowBits k 252 4 (by omega)
  let raw := combWindowValue bits
  let parity := k.val.intBits[0]
  let index := raw + 16 • parity
  let oneHot ← indicators 32 index
  let X : AffineSlope.Rep :=
    ⟨∑ i : Fin 32, topCombX i.val • oneHot.intBits[i], 2⟩
  let Y : AffineSlope.Rep :=
    ⟨∑ i : Fin 32, topCombY i.val • oneHot.intBits[i], 2⟩
  pure ⟨X, Y, 0⟩

def fixedBaseComb12 (k : Fn) : Circuit AffineSlope.Point := do
  let initial ← lookupFixed12 k 0 (by omega)
  WF.foldRange [:7] initial fun i hi acc => do
    let point ← lookupFixed12 k (i + 1) (by
      have hi' : i < 7 := by simpa using hi.2.1
      omega)
    AffineSlope.addIncompleteChecked acc point

def fixedBaseComb13 (k : Fn) (initial : AffineSlope.Point) :
    Circuit AffineSlope.Point :=
  WF.foldRange [:12] initial fun i hi acc => do
    let point ← lookupFixed13 k i (by simpa using hi.2.1)
    AffineSlope.addCompleteCollapsed acc point

/-- Production-specific 13-bit comb continuation.  Unlike `fixedBaseComb13`,
this is only seeded by the lower 96-bit positional comb, whose coefficient
bound makes every chord denominator nonzero. -/
def fixedBaseComb13Incomplete (k : Fn) (initial : AffineSlope.Point) :
    Circuit AffineSlope.Point :=
  WF.foldRange [:12] initial fun i hi acc => do
    let point ← lookupFixed13 k i (by simpa using hi.2.1)
    AffineSlope.addIncompleteChecked acc point

/-- Fixed-base comb with checked incomplete additions across the positional
12- and 13-bit schedules.  The final top-window addition remains complete
because the two operands can be opposites when the fixed scalar is zero. -/
def fixedBaseCombComplete (k : Fn) : Circuit AffineSlope.Point := do
  let acc12 ← fixedBaseComb12 k
  let acc ← fixedBaseComb13Incomplete k acc12
  let top ← lookupFixedTop k
  AffineSlope.addCompleteCollapsed acc top

/-- The existing signed radix-32 variable-base ladder with generator events
removed.  Its doubling schedule and Booth digits are unchanged. -/
def signedRadix32VariableStep (u2 : Fn) (qTable : Radix32Table)
    (i : Nat) (hi : i < 255) (acc : AffineSlope.Point) :
    Circuit AffineSlope.Point := do
  let acc ← AffineSlope.doubleComplete acc
  let exponent := 254 - i
  if _hq : exponent % 5 = 0 then do
    have hdigit : exponent / 5 < 52 := by omega
    let digit ← signedDigitIndicators (boothDigit u2 (exponent / 5) hdigit)
    let q ← selectSignedRadix32Point digit qTable
    AffineSlope.addCompleteCollapsed acc q
  else pure acc

def signedRadix32VariableMul (u2 : Fn) (q : Projective) :
    Circuit AffineSlope.Point := do
  let qTable ← materializeRadix32Multiples q
  let topDigit ← signedDigitIndicators (boothDigit u2 51 (by omega))
  let initial ← selectSignedRadix32Point topDigit qTable
  WF.foldRange [:255] initial fun i hi acc =>
    signedRadix32VariableStep u2 qTable i hi.2.1 acc

def fixedCombVerificationSum (input : PreparedVerification) :
    Circuit AffineSlope.Point := do
  let variablePart ← signedRadix32VariableMul input.u2 input.q
  let fixedPart ← fixedBaseCombComplete input.u1
  AffineSlope.addCompleteCollapsed variablePart fixedPart

def fixedCombVerificationX (input : PreparedVerification) :
    Circuit AffineSlope.XPoint := do
  let variablePart ← signedRadix32VariableMul input.u2 input.q
  let fixedPart ← fixedBaseCombComplete input.u1
  AffineSlope.addCompleteCollapsedX variablePart fixedPart

def fixedCombVerificationCanonicalX (input : PreparedVerification) :
    Circuit AffineSlope.CanonicalXPoint := do
  let variablePart ← signedRadix32VariableMul input.u2 input.q
  let fixedPart ← fixedBaseCombComplete input.u1
  AffineSlope.addCompleteCollapsedCanonicalX variablePart fixedPart

def fixedCombVerificationDirectTerminal (input : PreparedVerification) :
    Circuit Unit := do
  let variablePart ← signedRadix32VariableMul input.u2 input.q
  let fixedPart ← fixedBaseCombComplete input.u1
  addCompleteCollapsedDirectTerminal input.r variablePart fixedPart

def fixedCombVerificationDeltaBlock (input : PreparedVerification) :
    Circuit Unit := do
  let variablePart ← signedRadix32VariableMul input.u2 input.q
  let fixedPart ← fixedBaseCombComplete input.u1
  addCompleteCollapsedDeltaBlock input.r variablePart fixedPart

end Freigen.F2Z.Examples.EcdsaP256
