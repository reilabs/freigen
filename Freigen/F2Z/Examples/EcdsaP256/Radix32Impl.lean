import Freigen.F2Z.Examples.EcdsaP256.Impl
import Freigen.F2Z.Examples.P256.IncompleteImpl

/-! Experimental signed radix-32 joint scalar multiplication. -/

namespace Freigen.F2Z.Examples.EcdsaP256

open Std.Do
open scoped Std.Do
open BigOperators
open Modular
open P256
open P256.Projective

set_option maxRecDepth 10000

structure Radix32Table where
  low : Vector AffineSlope.Point 16
  p16 : AffineSlope.Point

/-- Proof index for a checked chord extension of the radix-32 table.  The
index is erased from the generated circuit. -/
def addRadix32Multiple (_k : Nat) (P Q : AffineSlope.Point) :
    Circuit AffineSlope.Point :=
  AffineSlope.addIncompleteChecked P Q

def materializeRadix32Multiples (P : Projective) :
    Circuit Radix32Table := do
  let p1 := AffineSlope.ofElems P.X P.Y
  let p2 ← doubleMultiple 1 p1
  let p3 ← addRadix32Multiple 2 p2 p1
  let p4 ← doubleMultiple 2 p2
  let p5 ← addRadix32Multiple 4 p4 p1
  let p6 ← doubleMultiple 3 p3
  let p7 ← addRadix32Multiple 6 p6 p1
  let p8 ← doubleMultiple 4 p4
  let p9 ← addRadix32Multiple 8 p8 p1
  let p10 ← doubleMultiple 5 p5
  let p11 ← addRadix32Multiple 10 p10 p1
  let p12 ← doubleMultiple 6 p6
  let p13 ← addRadix32Multiple 12 p12 p1
  let p14 ← doubleMultiple 7 p7
  let p15 ← addRadix32Multiple 14 p14 p1
  let p16 ← doubleMultiple 8 p8
  pure ⟨#v[AffineSlope.infinity, p1, p2, p3, p4, p5, p6, p7, p8,
    p9, p10, p11, p12, p13, p14, p15], p16⟩

def applyPointSign (negative : LC ℤ) (P : AffineSlope.Point) :
    Circuit AffineSlope.Point := do
  let bits ← hint h![negative, P.Y.intVal]
    fun h![(s : Int), (y : Int)] =>
      let value := if s = 1 then (base.modulus : Int) - y else y
      if _h : 0 ≤ value then
        pure $ Vector.ofFn (n := 256) fun i => value.toNat.testBit i
      else fail s!"negative signed point coordinate {value}"
  let Y ← U.fromWord { bitsLE := bits }
  assertR1C negative
    (LC.ofConst (base.modulus : Int) - 2 • P.Y.intVal)
    (Y.intVal - P.Y.intVal)
  pure ⟨P.X, ⟨Y.intVal, 2⟩, P.infinity⟩

structure SignedDigit where
  oneHot : U 33

def SignedDigit.value (digit : SignedDigit) : LC ℤ :=
  ∑ slot : Fin 33, ((slot.val : Int) - 16) • digit.oneHot.intBits[slot]

def SignedDigit.magnitude (digit : SignedDigit) : LC ℤ :=
  ∑ slot : Fin 33,
    Int.natAbs ((slot.val : Int) - 16) • digit.oneHot.intBits[slot]

def SignedDigit.negative (digit : SignedDigit) : LC ℤ :=
  ∑ slot : Fin 33,
    (if slot.val < 16 then (1 : Int) else 0) • digit.oneHot.intBits[slot]

def SignedDigit.isSixteen (digit : SignedDigit) : LC ℤ :=
  ∑ slot : Fin 33,
    (if slot.val = 0 ∨ slot.val = 32 then (1 : Int) else 0) •
      digit.oneHot.intBits[slot]

def signedDigitIndicators (value : LC ℤ) : Circuit SignedDigit := do
  let oneHot ← indicators 33 (value + 16)
  pure ⟨oneHot⟩

def boothDigit (k : Fn) (i : Nat) (hi : i < 52) : LC ℤ :=
  if _h : i < 51 then
    let low := windowValue k (5 * i) 4 (by omega)
    let previous := if i = 0 then 0
      else windowValue k (5 * i - 1) 1 (by omega)
    let top := windowValue k (5 * i + 4) 1 (by omega)
    low + previous - 16 • top
  else
    windowValue k 255 1 (by omega) + windowValue k 254 1 (by omega)

/-- Select between two Boolean linear combinations with one R1CS constraint. -/
def selectBit (choose whenOne whenZero : LC ℤ) : Circuit (LC ℤ) := do
  let bits ← hint h![choose, whenOne, whenZero]
    fun h![(b : Int), (x : Int), (y : Int)] =>
      pure $ Vector.ofFn (n := 1) fun _ => if b = 1 then x = 1 else y = 1
  let out ← U.fromWord { bitsLE := bits }
  assertR1C choose (whenOne - whenZero) (out.intVal - whenZero)
  pure out.intVal

private abbrev SignedMagnitudeLookupArgTypes : List Eff.WitnessSide :=
  [.z, .z, .z, .z, .z, .z, .z, .z, .z,
    .z, .z, .z, .z, .z, .z, .z, .z, .z]

def signedMagnitudeLookupArgs (digit : LC ℤ)
    (values : Vector (LC ℤ) 17) :
    HList Eff.WitnessSide.denoteW SignedMagnitudeLookupArgTypes :=
  h![digit, values[0], values[1], values[2], values[3], values[4],
    values[5], values[6], values[7], values[8], values[9], values[10],
    values[11], values[12], values[13], values[14], values[15], values[16]]

def signedMagnitudeLookupRepHint :
    HList Eff.WitnessSide.denoteF SignedMagnitudeLookupArgTypes →
      Hint (Vector Bool 256)
  | h![(d : Int), (x0 : Int), (x1 : Int), (x2 : Int), (x3 : Int),
      (x4 : Int), (x5 : Int), (x6 : Int), (x7 : Int), (x8 : Int),
      (x9 : Int), (x10 : Int), (x11 : Int), (x12 : Int), (x13 : Int),
      (x14 : Int), (x15 : Int), (x16 : Int)] =>
    let values := #[x0, x1, x2, x3, x4, x5, x6, x7, x8,
      x9, x10, x11, x12, x13, x14, x15, x16]
    let chosen := values[d.toNat]!
    if _h : 0 ≤ chosen then
      pure $ Vector.ofFn (n := 256) fun i => chosen.toNat.testBit i
    else
      fail s!"negative direct signed-magnitude coordinate {chosen}"

def signedMagnitudeLookupFlagHint :
    HList Eff.WitnessSide.denoteF SignedMagnitudeLookupArgTypes →
      Hint (Vector Bool 1)
  | h![(d : Int), (x0 : Int), (x1 : Int), (x2 : Int), (x3 : Int),
      (x4 : Int), (x5 : Int), (x6 : Int), (x7 : Int), (x8 : Int),
      (x9 : Int), (x10 : Int), (x11 : Int), (x12 : Int), (x13 : Int),
      (x14 : Int), (x15 : Int), (x16 : Int)] =>
    let values := #[x0, x1, x2, x3, x4, x5, x6, x7, x8,
      x9, x10, x11, x12, x13, x14, x15, x16]
    pure $ Vector.ofFn fun _ => values[d.toNat]! = 1

def radix32MagnitudeValues {α : Type} (low : Vector α 16)
    (p16 : α) : Vector α 17 :=
  Vector.ofFn fun i =>
    if h : i.val < 16 then low[i.val]'h else p16

/-- The gate for magnitude `i+1` is the sum of its negative and positive
signed one-hot slots.  The one-hot invariant makes this sum Boolean. -/
def signedNonzeroMagnitudeGate (digit : SignedDigit)
    (i : Nat) (hi : i < 16) : LC ℤ :=
  digit.oneHot.intBits[15 - i]'(by omega) +
    digit.oneHot.intBits[17 + i]'(by omega)

/-- Open one coordinate for magnitudes zero through sixteen.  Slot 16 marks
the zero digit and constrains the coordinate to the table's normalized
infinity entry; this is required when the top digit seeds the accumulator and
is consumed by doubling before any complete addition. -/
def lookupSignedMagnitudeRep (digit : SignedDigit)
    (values : Vector AffineSlope.Rep 17) : Circuit AffineSlope.Rep := do
  let bits ← hint
    (signedMagnitudeLookupArgs digit.magnitude (values.map (·.intVal)))
    signedMagnitudeLookupRepHint
  let word ← U.fromWord { bitsLE := bits }
  assertR1C digit.oneHot.intBits[16]
    (word.intVal - values[0].intVal) 0
  WF.foldRange [:16] () fun i hi _ => do
    have hi' : i < 16 := hi.2.1
    assertR1C (signedNonzeroMagnitudeGate digit i hi')
      (word.intVal - (values[i + 1]'(by omega)).intVal) 0
  pure ⟨word.intVal, 2⟩

/-- Select the infinity flag from the same 17-entry magnitude table.  The
flag cannot be derived solely from the zero digit: the generic selector also
supports zero and torsion input points, whose nonzero multiples may be
infinity. -/
def lookupSignedMagnitudeFlag (digit : SignedDigit)
    (values : Vector (LC ℤ) 17) : Circuit (LC ℤ) := do
  let bits ← hint (signedMagnitudeLookupArgs digit.magnitude values)
    signedMagnitudeLookupFlagHint
  let out ← f2z bits[0]
  assertR1C digit.oneHot.intBits[16] (out - values[0]) 0
  WF.foldRange [:16] () fun i hi _ => do
    have hi' : i < 16 := hi.2.1
    assertR1C (signedNonzeroMagnitudeGate digit i hi')
      (out - values[i + 1]'(by omega)) 0
  pure out

def selectRadix32Magnitude (digit : SignedDigit) (table : Radix32Table) :
    Circuit AffineSlope.Point := do
  let xs := radix32MagnitudeValues (table.low.map (·.X)) table.p16.X
  let ys := radix32MagnitudeValues (table.low.map (·.Y)) table.p16.Y
  let infinities := radix32MagnitudeValues
    (table.low.map (·.infinity)) table.p16.infinity
  let X ← lookupSignedMagnitudeRep digit xs
  let Y ← lookupSignedMagnitudeRep digit ys
  let infinity ← lookupSignedMagnitudeFlag digit infinities
  pure ⟨X, Y, infinity⟩

def selectSignedRadix32Point (digit : SignedDigit)
    (table : Radix32Table) : Circuit AffineSlope.Point := do
  let point ← selectRadix32Magnitude digit table
  applyPointSign digit.negative point

def signedRadix32Step (u1 u2 : Fn)
    (qTable : Radix32Table)
    (i : Nat) (hi : i < 255) (acc : AffineSlope.Point) :
    Circuit AffineSlope.Point := do
  let acc ← AffineSlope.doubleComplete acc
  let exponent := 254 - i
  let acc ← if _hq : exponent % 5 = 0 then do
    have hdigit : exponent / 5 < 52 := by omega
    let digit ← signedDigitIndicators (boothDigit u2 (exponent / 5) hdigit)
    let q ← selectSignedRadix32Point digit qTable
    AffineSlope.addCompleteCollapsed acc q
  else pure acc
  if _hg : exponent % 8 = 0 then do
    have hfit : exponent + 8 ≤ 256 := by omega
    let g ← lookupGeneratorByte (windowValue u1 exponent 8 hfit)
    AffineSlope.addCompleteCollapsed acc g
  else pure acc

def signedRadix32JointScalarMul (u1 u2 : Fn) (q : Projective) :
    Circuit AffineSlope.Point := do
  let qTable ← materializeRadix32Multiples q
  let topDigit ← signedDigitIndicators (boothDigit u2 51 (by omega))
  let initial ← selectSignedRadix32Point topDigit qTable
  WF.foldRange [:255] initial fun i hi acc =>
    signedRadix32Step u1 u2 qTable i hi.2.1 acc

end Freigen.F2Z.Examples.EcdsaP256
