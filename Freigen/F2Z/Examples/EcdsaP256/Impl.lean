import Freigen.F2Z.Examples.EcdsaP256.Reference

/-!
# ECDSA-P256 verification implementation

`verifyDigest` implements SEC 1 ECDSA verification for a 256-bit SHA-256
digest supplied as a circuit input.

Inverse values are proof-carrying witnesses checked by modular multiplication
and exact equality.

Boundary correctness statements are provided by
`Freigen.F2Z.Examples.EcdsaP256`.
-/

namespace Freigen.F2Z.Examples.EcdsaP256

set_option maxRecDepth 10000

open Std.Do
open scoped Std.Do
open Modular
open P256
open P256.Projective

structure PublicKey where
  x : U 256
  y : U 256

structure Signature where
  r : U 256
  s : U 256

/-- Auxiliary witnesses.  `rInv` proves `r != 0`; `sInv` both proves `s != 0`
and supplies the ECDSA inverse. -/
structure Aux where
  rInv : U 256
  sInv : U 256

private def materializeMultiples (P : Projective) :
    Circuit (Vector AffineSlope.Point 16) := do
  let p1 := AffineSlope.ofElems P.X P.Y
  let p2 ← AffineSlope.doubleFinite p1
  let p3 ← AffineSlope.addFiniteDistinct p2 p1
  let p4 ← AffineSlope.doubleFinite p2
  let p5 ← AffineSlope.addFiniteDistinct p4 p1
  let p6 ← AffineSlope.doubleFinite p3
  let p7 ← AffineSlope.addFiniteDistinct p6 p1
  let p8 ← AffineSlope.doubleFinite p4
  let p9 ← AffineSlope.addFiniteDistinct p8 p1
  let p10 ← AffineSlope.doubleFinite p5
  let p11 ← AffineSlope.addFiniteDistinct p10 p1
  let p12 ← AffineSlope.doubleFinite p6
  let p13 ← AffineSlope.addFiniteDistinct p12 p1
  let p14 ← AffineSlope.doubleFinite p7
  let p15 ← AffineSlope.addFiniteDistinct p14 p1
  pure #v[AffineSlope.infinity, p1, p2, p3, p4, p5, p6, p7,
    p8, p9, p10, p11, p12, p13, p14, p15]

private def windowIndicators (digit : LC ℤ) : Circuit (U 16) := do
  let bits ← hint h![digit] fun h![(d : Int)] =>
    pure $ Vector.ofFn (n := 16) fun i => d = i.val
  let indicators ← U.fromWord { bitsLE := bits }
  assertR1C 0 0 ((∑ i : Fin 16, indicators.intBits[i]) - 1)
  assertR1C 0 0
    ((∑ i : Fin 16, i.val • indicators.intBits[i]) - digit)
  pure indicators

private def lookupRep (digit : LC ℤ) (indicators : U 16)
    (xs : Vector AffineSlope.Rep 16) : Circuit AffineSlope.Rep := do
  let bits ← hint h![digit,
      xs[0].intVal, xs[1].intVal, xs[2].intVal, xs[3].intVal,
      xs[4].intVal, xs[5].intVal, xs[6].intVal, xs[7].intVal,
      xs[8].intVal, xs[9].intVal, xs[10].intVal, xs[11].intVal,
      xs[12].intVal, xs[13].intVal, xs[14].intVal, xs[15].intVal]
    fun h![(d : Int), (x0 : Int), (x1 : Int), (x2 : Int),
      (x3 : Int), (x4 : Int), (x5 : Int), (x6 : Int), (x7 : Int),
      (x8 : Int), (x9 : Int), (x10 : Int), (x11 : Int),
      (x12 : Int), (x13 : Int), (x14 : Int), (x15 : Int)] =>
      let values := #[x0, x1, x2, x3, x4, x5, x6, x7,
        x8, x9, x10, x11, x12, x13, x14, x15]
      let chosen := values[d.toNat]!
      pure $ Vector.ofFn (n := 256) fun i => chosen.toNat.testBit i
  let out ← U.fromWord { bitsLE := bits }
  for h : i in [:16] do
    assertR1C indicators.intBits[i] (out.intVal - xs[i].intVal) 0
  pure ⟨out.intVal, 2⟩

private def lookupPoint (digit : LC ℤ)
    (table : Vector AffineSlope.Point 16) : Circuit AffineSlope.Point := do
  let indicators ← windowIndicators digit
  let X ← lookupRep digit indicators (table.map (·.X))
  let Y ← lookupRep digit indicators (table.map (·.Y))
  pure ⟨X, Y, indicators.intBits[0]⟩

private def generatorByteX : Vector Nat 256 :=
  Vector.ofFn fun i => Reference.xNat (i.val • P256.Reference.generator)

private def generatorByteY : Vector Nat 256 :=
  Vector.ofFn fun i => Reference.yNat (i.val • P256.Reference.generator)

private def byteIndicators (digit : LC ℤ) : Circuit (U 256) := do
  let bits ← hint h![digit] fun h![(d : Int)] =>
    pure $ Vector.ofFn (n := 256) fun i => d = i.val
  let indicators ← U.fromWord { bitsLE := bits }
  assertR1C 0 0 ((∑ i : Fin 256, indicators.intBits[i]) - 1)
  assertR1C 0 0
    ((∑ i : Fin 256, i.val • indicators.intBits[i]) - digit)
  pure indicators

/-- An eight-bit fixed-base lookup is still linear: only the one-hot bits are
committed, while coordinates are public coefficients. -/
private def lookupGeneratorByte (digit : LC ℤ) :
    Circuit AffineSlope.Point := do
  let indicators ← byteIndicators digit
  let X : Modular.Lazy.Rep base :=
    ⟨∑ i : Fin 256, generatorByteX[i] • indicators.intBits[i], 1⟩
  let Y : Modular.Lazy.Rep base :=
    ⟨∑ i : Fin 256, generatorByteY[i] • indicators.intBits[i], 1⟩
  pure ⟨X, Y, indicators.intBits[0]⟩

private def doubleFour (P : AffineSlope.Point) :
    Circuit AffineSlope.Point := do
  let P ← AffineSlope.doubleComplete P
  let P ← AffineSlope.doubleComplete P
  let P ← AffineSlope.doubleComplete P
  AffineSlope.doubleComplete P

private def windowDigit (k : Fn) (i : Nat) (_hi : i < 64) : Circuit (LC ℤ) := do
  let baseIndex := 252 - 4 * i
  have h0 : baseIndex < 256 := by omega
  have h1 : baseIndex + 1 < 256 := by omega
  have h2 : baseIndex + 2 < 256 := by omega
  have h3 : baseIndex + 3 < 256 := by omega
  let b0 ← f2z k.val.bits.bitsLE[baseIndex]
  let b1 ← f2z k.val.bits.bitsLE[baseIndex + 1]
  let b2 ← f2z k.val.bits.bitsLE[baseIndex + 2]
  let b3 ← f2z k.val.bits.bitsLE[baseIndex + 3]
  pure (b0 + 2 • b1 + 4 • b2 + 8 • b3)

private def windowByte (k : Fn) (i : Nat) (_hi : i < 32) : Circuit (LC ℤ) := do
  let baseIndex := 248 - 8 * i
  have h0 : baseIndex < 256 := by omega
  have h1 : baseIndex + 1 < 256 := by omega
  have h2 : baseIndex + 2 < 256 := by omega
  have h3 : baseIndex + 3 < 256 := by omega
  have h4 : baseIndex + 4 < 256 := by omega
  have h5 : baseIndex + 5 < 256 := by omega
  have h6 : baseIndex + 6 < 256 := by omega
  have h7 : baseIndex + 7 < 256 := by omega
  let b0 ← f2z k.val.bits.bitsLE[baseIndex]
  let b1 ← f2z k.val.bits.bitsLE[baseIndex + 1]
  let b2 ← f2z k.val.bits.bitsLE[baseIndex + 2]
  let b3 ← f2z k.val.bits.bitsLE[baseIndex + 3]
  let b4 ← f2z k.val.bits.bitsLE[baseIndex + 4]
  let b5 ← f2z k.val.bits.bitsLE[baseIndex + 5]
  let b6 ← f2z k.val.bits.bitsLE[baseIndex + 6]
  let b7 ← f2z k.val.bits.bitsLE[baseIndex + 7]
  pure (b0 + 2 • b1 + 4 • b2 + 8 • b3 + 16 • b4 + 32 • b5 +
    64 • b6 + 128 • b7)

private def jointByteStep (u1 u2 : Fn)
    (qTable : Vector AffineSlope.Point 16) (i : Nat) (hi : i < 32)
    (acc : AffineSlope.Point) : Circuit AffineSlope.Point := do
  let d1 ← windowByte u1 i hi
  have hhi : 2 * i < 64 := by omega
  have hlo : 2 * i + 1 < 64 := by omega
  let d2hi ← windowDigit u2 (2 * i) hhi
  let d2lo ← windowDigit u2 (2 * i + 1) hlo
  let qhi ← lookupPoint d2hi qTable
  let qlo ← lookupPoint d2lo qTable
  let acc ← doubleFour acc
  let acc ← AffineSlope.addComplete acc qhi
  let acc ← doubleFour acc
  let acc ← AffineSlope.addComplete acc qlo
  let g ← lookupGeneratorByte d1
  AffineSlope.addComplete acc g

/-- Eight-bit fixed-G/four-bit variable-Q joint multiplication for
`u1*G + u2*Q`. Each step consumes one G byte and two Q nibbles. -/
private def jointScalarMul (u1 u2 : Fn) (q : Projective) :
    Circuit AffineSlope.Point := do
  let qTable ← materializeMultiples q
  WF.foldRange [:32] AffineSlope.infinity fun i hi acc =>
    jointByteStep u1 u2 qTable i hi.2.1 acc

/-- Verify an ECDSA-P256 signature over an already computed SHA-256 digest.

All external integers are first made canonical. Therefore the circuit rejects
non-canonical encodings instead of silently reducing signature or key fields.
-/
def verifyDigest (digest : U 256) (key : PublicKey)
    (sig : Signature) (aux : Aux) : Circuit Unit := do
  let qx ← ofU base key.x
  let qy ← ofU base key.y
  let r ← ofU scalar sig.r
  let s ← ofU scalar sig.s
  let rInv ← ofU scalar aux.rInv
  let sInv ← ofU scalar aux.sInv

  Projective.Lazy.assertOnCurve qx qy

  -- These checks enforce 1 <= r,s < n.  Canonicality gives the upper bound;
  -- existence of an inverse modulo the prime group order excludes zero.
  Modular.Lazy.assertMulEq scalar
    (Modular.Lazy.ofElem scalar r) (Modular.Lazy.ofElem scalar rInv)
    (Modular.Lazy.ofElem scalar fnOne)
  Modular.Lazy.assertMulEq scalar
    (Modular.Lazy.ofElem scalar s) (Modular.Lazy.ofElem scalar sInv)
    (Modular.Lazy.ofElem scalar fnOne)
  let w := sInv

  -- SHA-256 and the group order are both 256 bits.  Reduction implements the
  -- SEC 1 `bits2int`/mod-n behavior for P-256.
  let z ← Modular.Relaxed.reduceSmall scalar digest.intVal
  let u1 ← Modular.Relaxed.mul scalar z w
  let u2 ← Modular.Relaxed.mul scalar r w

  let q : Projective := ⟨qx, qy, one⟩
  let sum ← jointScalarMul u1 u2 q

  -- ECDSA rejects the identity.  Affine slope arithmetic has already
  -- materialized the final x-coordinate, so no normalization inverse remains.
  assertR1C 0 0 sum.infinity
  let xModN ← Modular.Relaxed.reduceSmall scalar sum.X.intVal
  assertEq scalar xModN r

/-- Number of Boolean inputs to the standalone digest verifier: the digest,
public-key coordinates, signature scalars, and two inverse witnesses. -/
def verifyDigestInputBits : Nat := 7 * 256

private def verifyDigestInputWord
    (inputs : Vector (LC Bool) verifyDigestInputBits)
    (slot : Fin 7) : Word 256 :=
  { bitsLE := Vector.ofFn fun i =>
      inputs[slot.val * 256 + i.val]'(by
        simp [verifyDigestInputBits]
        omega) }

private def verifyDigestFromBits
    (inputs : Vector (LC Bool) verifyDigestInputBits) : Circuit Unit := do
  let digest ← U.fromWord (verifyDigestInputWord inputs 0)
  let qx ← U.fromWord (verifyDigestInputWord inputs 1)
  let qy ← U.fromWord (verifyDigestInputWord inputs 2)
  let r ← U.fromWord (verifyDigestInputWord inputs 3)
  let s ← U.fromWord (verifyDigestInputWord inputs 4)
  let rInv ← U.fromWord (verifyDigestInputWord inputs 5)
  let sInv ← U.fromWord (verifyDigestInputWord inputs 6)
  verifyDigest digest ⟨qx, qy⟩ ⟨r, s⟩ ⟨rInv, sInv⟩

/-- Constraint-system representation of the standalone digest verifier. -/
def verifyDigestCS : Unit × Semantics.CS :=
  Semantics.CSBuilder.runWithInputs verifyDigestFromBits

end Freigen.F2Z.Examples.EcdsaP256
