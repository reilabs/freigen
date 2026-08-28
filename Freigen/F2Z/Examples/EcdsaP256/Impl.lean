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
open BigOperators
open Modular
open P256
open P256.Projective

variable [ctx : Context]

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

/-- Packed input to the standalone prehashed verifier. -/
abbrev VerifyInput := U 256 × PublicKey × Signature × Aux

def materializeMultiples (P : Projective) :
    Circuit (Vector AffineSlope.Point 16) := do
  let p1 := AffineSlope.ofElems P.X P.Y
  let p2 ← AffineSlope.addComplete p1 p1
  let p3 ← AffineSlope.addComplete p2 p1
  let p4 ← AffineSlope.addComplete p3 p1
  let p5 ← AffineSlope.addComplete p4 p1
  let p6 ← AffineSlope.addComplete p5 p1
  let p7 ← AffineSlope.addComplete p6 p1
  let p8 ← AffineSlope.addComplete p7 p1
  let p9 ← AffineSlope.addComplete p8 p1
  let p10 ← AffineSlope.addComplete p9 p1
  let p11 ← AffineSlope.addComplete p10 p1
  let p12 ← AffineSlope.addComplete p11 p1
  let p13 ← AffineSlope.addComplete p12 p1
  let p14 ← AffineSlope.addComplete p13 p1
  let p15 ← AffineSlope.addComplete p14 p1
  pure #v[AffineSlope.infinity, p1, p2, p3, p4, p5, p6, p7, p8,
    p9, p10, p11, p12, p13, p14, p15]

def indicators (n : Nat) (digit : ctx.Wℤ) : Circuit (U n) := do
  let bits ← hint (argTps := [.z]) h![digit] fun h![(d : Int)] =>
    pure $ Vector.ofFn (n := n) fun i => d = i.val
  let out ← U.fromWord { bitsLE := bits }
  assertR1C 0 0 ((∑ i : Fin n, out.intBits[i]) - 1)
  assertR1C 0 0
    ((∑ i : Fin n, i.val • out.intBits[i]) - digit)
  pure out

def windowIndicators (digit : ctx.Wℤ) : Circuit (U 16) :=
  indicators 16 digit

private abbrev LookupArgTypes : List Eff.WitnessSide :=
  [.z, .z, .z, .z, .z, .z, .z, .z, .z,
    .z, .z, .z, .z, .z, .z, .z, .z]

def lookupArgs (digit : ctx.Wℤ) (values : Vector ctx.Wℤ 16) :
    HList (Eff.WitnessSide.denoteW ctx) LookupArgTypes :=
  h![digit, values[0], values[1], values[2], values[3], values[4],
    values[5], values[6], values[7], values[8], values[9], values[10],
    values[11], values[12], values[13], values[14], values[15]]

def lookupRepHint :
    HList Eff.WitnessSide.denoteF LookupArgTypes →
      Hint (Vector Bool 256)
  | h![(d : Int), (x0 : Int), (x1 : Int), (x2 : Int), (x3 : Int),
      (x4 : Int), (x5 : Int), (x6 : Int), (x7 : Int), (x8 : Int),
      (x9 : Int), (x10 : Int), (x11 : Int), (x12 : Int), (x13 : Int),
      (x14 : Int), (x15 : Int)] =>
    let values := #[x0, x1, x2, x3, x4, x5, x6, x7,
      x8, x9, x10, x11, x12, x13, x14, x15]
    let chosen := values[d.toNat]!
    pure $ Vector.ofFn (n := 256) fun i => chosen.toNat.testBit i

def lookupFlagHint :
    HList Eff.WitnessSide.denoteF LookupArgTypes →
      Hint (Vector Bool 1)
  | h![(d : Int), (f0 : Int), (f1 : Int), (f2 : Int), (f3 : Int),
      (f4 : Int), (f5 : Int), (f6 : Int), (f7 : Int), (f8 : Int),
      (f9 : Int), (f10 : Int), (f11 : Int), (f12 : Int), (f13 : Int),
      (f14 : Int), (f15 : Int)] =>
    let values := #[f0, f1, f2, f3, f4, f5, f6, f7,
      f8, f9, f10, f11, f12, f13, f14, f15]
    pure #v[values[d.toNat]! = 1]

def assertLookupRep (indicators : U 16) (out : U 256)
    (xs : Vector AffineSlope.Rep 16) : Circuit Unit :=
  WF.foldRange [:16] () fun i h _ =>
    assertR1C indicators.intBits[i] (out.intVal - xs[i].intVal) 0

def lookupRepWord (digit : ctx.Wℤ) (xs : Vector AffineSlope.Rep 16) :
    Circuit (U 256) := do
  let bits ← hint (lookupArgs digit (xs.map (·.intVal)))
    lookupRepHint
  U.fromWord { bitsLE := bits }

def lookupRep (digit : ctx.Wℤ) (indicators : U 16)
    (xs : Vector AffineSlope.Rep 16) : Circuit AffineSlope.Rep := do
  let out ← lookupRepWord digit xs
  assertLookupRep indicators out xs
  pure ⟨out.intVal, 2⟩

def assertLookupFlag (indicators : U 16) (out : ctx.Wℤ)
    (flags : Vector ctx.Wℤ 16) : Circuit Unit :=
  WF.foldRange [:16] () fun i h _ =>
    assertR1C indicators.intBits[i] (out - flags[i]) 0

def lookupFlag (digit : ctx.Wℤ) (indicators : U 16)
    (flags : Vector ctx.Wℤ 16) : Circuit ctx.Wℤ := do
  let bits ← hint (lookupArgs digit flags)
    lookupFlagHint
  let out ← f2z bits[0]
  assertLookupFlag indicators out flags
  pure out

def lookupPoint (digit : ctx.Wℤ)
    (table : Vector AffineSlope.Point 16) : Circuit AffineSlope.Point := do
  let indicators ← windowIndicators digit
  let X ← lookupRep digit indicators (table.map (·.X))
  let Y ← lookupRep digit indicators (table.map (·.Y))
  let infinity ← lookupFlag digit indicators (table.map (·.infinity))
  pure ⟨X, Y, infinity⟩

def generatorByteX : Vector Nat 256 :=
  Vector.ofFn fun i => Reference.xNat (i.val • P256.Reference.generator)

def generatorByteY : Vector Nat 256 :=
  Vector.ofFn fun i => Reference.yNat (i.val • P256.Reference.generator)

def byteIndicators (digit : ctx.Wℤ) : Circuit (U 256) :=
  indicators 256 digit

/-- An eight-bit fixed-base lookup is still linear: only the one-hot bits are
committed, while coordinates are public coefficients. -/
def lookupGeneratorByte (digit : ctx.Wℤ) :
    Circuit AffineSlope.Point := do
  let indicators ← byteIndicators digit
  let X : Modular.Lazy.Rep base :=
    ⟨∑ i : Fin 256, generatorByteX[i] • indicators.intBits[i], 2⟩
  let Y : Modular.Lazy.Rep base :=
    ⟨∑ i : Fin 256, generatorByteY[i] • indicators.intBits[i], 2⟩
  pure ⟨X, Y, indicators.intBits[0]⟩

def doubleStep (_k : Nat) (P : AffineSlope.Point) :
    Circuit AffineSlope.Point :=
  AffineSlope.doubleComplete P

/-- Two doublings behind one compositional boundary. -/
def doublePair (P : AffineSlope.Point) :
    Circuit AffineSlope.Point := do
  let P ← doubleStep 1 P
  doubleStep 2 P

def doubleFour (P : AffineSlope.Point) :
    Circuit AffineSlope.Point := do
  let P ← doublePair P
  doublePair P

def windowValue (k : Fn) (start width : Nat) (hfit : start + width ≤ 256) :
    ctx.Wℤ :=
  ∑ j : Fin width, 2 ^ j.val • k.val.intBits[start + j.val]'(by omega)

def windowDigit (k : Fn) (i : Nat) (hi : i < 64) : Circuit ctx.Wℤ :=
  pure (windowValue k (252 - 4 * i) 4 (by omega))

def windowByte (k : Fn) (i : Nat) (hi : i < 32) : Circuit ctx.Wℤ :=
  pure (windowValue k (248 - 8 * i) 8 (by omega))

structure JointTerms where
  qhi : AffineSlope.Point
  qlo : AffineSlope.Point
  g : AffineSlope.Point

def selectJointTerms (u1 u2 : Fn)
    (qTable : Vector AffineSlope.Point 16) (i : Nat) (hi : i < 32) :
    Circuit JointTerms := do
  let d1 ← windowByte u1 i hi
  have hhi : 2 * i < 64 := by omega
  have hlo : 2 * i + 1 < 64 := by omega
  let d2hi ← windowDigit u2 (2 * i) hhi
  let d2lo ← windowDigit u2 (2 * i + 1) hlo
  let qhi ← lookupPoint d2hi qTable
  let qlo ← lookupPoint d2lo qTable
  let g ← lookupGeneratorByte d1
  pure ⟨qhi, qlo, g⟩

def accumulateJoint (acc : AffineSlope.Point) (terms : JointTerms) :
    Circuit AffineSlope.Point := do
  let acc ← doubleFour acc
  let acc ← AffineSlope.addComplete acc terms.qhi
  let acc ← doubleFour acc
  let acc ← AffineSlope.addComplete acc terms.qlo
  AffineSlope.addComplete acc terms.g

def jointByteStep (u1 u2 : Fn)
    (qTable : Vector AffineSlope.Point 16) (i : Nat) (hi : i < 32)
    (acc : AffineSlope.Point) : Circuit AffineSlope.Point := do
  let terms ← selectJointTerms u1 u2 qTable i hi
  accumulateJoint acc terms

/-- Eight-bit fixed-G/four-bit variable-Q joint multiplication for
`u1*G + u2*Q`. Each step consumes one G byte and two Q nibbles. -/
def jointScalarMul (u1 u2 : Fn) (q : Projective) :
    Circuit AffineSlope.Point := do
  let qTable ← materializeMultiples q
  WF.foldRange [:32] AffineSlope.infinity fun i hi acc =>
    jointByteStep u1 u2 qTable i hi.2.1 acc

structure CanonicalInput where
  qx : Fp
  qy : Fp
  r : Fn
  s : Fn
  rInv : Fn
  sInv : Fn

def canonicalizeKey (key : PublicKey) : Circuit (Fp × Fp) := do
  let qx ← ofU base key.x
  let qy ← ofU base key.y
  pure (qx, qy)

def canonicalizeSignature (sig : Signature) : Circuit (Fn × Fn) := do
  let r ← ofU scalar sig.r
  let s ← ofU scalar sig.s
  pure (r, s)

def canonicalizeAux (aux : Aux) : Circuit (Fn × Fn) := do
  let rInv ← ofU scalar aux.rInv
  let sInv ← ofU scalar aux.sInv
  pure (rInv, sInv)

def canonicalizeInput (key : PublicKey) (sig : Signature) (aux : Aux) :
    Circuit CanonicalInput := do
  let q ← canonicalizeKey key
  let rs ← canonicalizeSignature sig
  let invs ← canonicalizeAux aux
  pure ⟨q.1, q.2, rs.1, rs.2, invs.1, invs.2⟩

structure PreparedVerification where
  u1 : Fn
  u2 : Fn
  q : Projective
  r : Fn

def validateCanonicalInput (input : CanonicalInput) : Circuit Unit := do
  Projective.Lazy.assertOnCurve input.qx input.qy

  -- These checks enforce 1 <= r,s < n.  Canonicality gives the upper bound;
  -- existence of an inverse modulo the prime group order excludes zero.
  Modular.Lazy.assertMulEq scalar
    (Modular.Lazy.ofElem scalar input.r)
    (Modular.Lazy.ofElem scalar input.rInv)
    (Modular.Lazy.ofElem scalar fnOne)
  Modular.Lazy.assertMulEq scalar
    (Modular.Lazy.ofElem scalar input.s)
    (Modular.Lazy.ofElem scalar input.sInv)
    (Modular.Lazy.ofElem scalar fnOne)

def multiplyScalars (z : Fn) (input : CanonicalInput) :
    Circuit (Fn × Fn) := do
  let w := input.sInv
  let u1Relaxed ← Modular.Relaxed.mul scalar z w
  let u2Relaxed ← Modular.Relaxed.mul scalar input.r w

  pure (u1Relaxed, u2Relaxed)

def deriveRelaxedScalars (digest : U 256) (input : CanonicalInput) :
    Circuit (Fn × Fn) := do
  -- SHA-256 and the group order are both 256 bits.  Reduction implements the
  -- SEC 1 `bits2int`/mod-n behavior for P-256.
  let z ← Modular.Relaxed.reduceSmall scalar digest.intVal
  multiplyScalars z input

def canonicalizeScalars (input : Fn × Fn) : Circuit (Fn × Fn) := do

  -- Relaxed quotient witnesses may use a representative plus `n`.  That is
  -- harmless during field arithmetic, but scalar multiplication consumes the
  -- representative as a natural number, so tighten exactly at this boundary.
  let u1 ← Modular.Lazy.reduce scalar
    (Modular.Lazy.ofElem scalar input.1)
  let u2 ← Modular.Lazy.reduce scalar
    (Modular.Lazy.ofElem scalar input.2)

  pure (u1, u2)

def deriveScalars (digest : U 256) (input : CanonicalInput) :
    Circuit (Fn × Fn) := do
  let relaxed ← deriveRelaxedScalars digest input
  canonicalizeScalars relaxed

def prepareVerification (digest : U 256) (input : CanonicalInput) :
    Circuit PreparedVerification := do
  validateCanonicalInput input
  let scalars ← deriveScalars digest input

  pure ⟨scalars.1, scalars.2, ⟨input.qx, input.qy, one⟩, input.r⟩

def computeVerificationSum (input : PreparedVerification) :
    Circuit AffineSlope.Point :=
  jointScalarMul input.u1 input.u2 input.q

def checkVerificationX (r : Fn) (sum : AffineSlope.Point) : Circuit Unit := do
  -- ECDSA rejects the identity.  Affine slope arithmetic has already
  -- materialized the final x-coordinate. Canonicalize it in the base field
  -- before changing moduli: reducing an arbitrary `x + k*p` modulo `n` would
  -- be unsound because the P-256 base prime and group order differ.
  assertR1C 0 0 sum.infinity
  let xCanonical ← Modular.Lazy.reduce base sum.X
  let xModN ← Modular.Relaxed.reduceSmall scalar xCanonical.val.intVal
  assertEq scalar xModN r

def finishVerification (input : PreparedVerification) : Circuit Unit := do
  let sum ← computeVerificationSum input
  checkVerificationX input.r sum

/-- Verify an ECDSA-P256 signature over an already computed SHA-256 digest.

All external integers are first made canonical. Therefore the circuit rejects
non-canonical encodings instead of silently reducing signature or key fields.
-/
def verifyDigest (digest : U 256) (key : PublicKey)
    (sig : Signature) (aux : Aux) : Circuit Unit := do
  let input ← canonicalizeInput key sig aux
  let prepared ← prepareVerification digest input
  finishVerification prepared

/-- Number of Boolean inputs to the standalone digest verifier: the digest,
public-key coordinates, signature scalars, and two inverse witnesses. -/
def verifyDigestInputBits : Nat := 7 * 256

def verifyDigestInputWord
    (inputs : Vector ctx.WBool verifyDigestInputBits)
    (slot : Fin 7) : Word 256 :=
  { bitsLE := Vector.ofFn fun i =>
      inputs[slot.val * 256 + i.val]'(by
        simp [verifyDigestInputBits]
        omega) }

def verifyDigestInputValue
    (inputs : Vector Bool verifyDigestInputBits)
    (slot : Fin 7) : BitVec 256 :=
  BitVec.ofFnLE fun i =>
    inputs[slot.val * 256 + i.val]'(by
      simp [verifyDigestInputBits]
      omega)

def verifyDigestInputWords
    (inputs : Vector ctx.WBool verifyDigestInputBits) :
    Vector (Word 256) 7 :=
  Vector.ofFn fun slot => verifyDigestInputWord inputs slot

def verifyDigestFromBits
    (inputs : Vector ctx.WBool verifyDigestInputBits) : Circuit Unit := do
  let values ← (verifyDigestInputWords inputs).mapM U.fromWord
  verifyDigest values[0] ⟨values[1], values[2]⟩
    ⟨values[3], values[4]⟩ ⟨values[5], values[6]⟩

/-- Constraint-system representation of the standalone digest verifier. -/
def verifyDigestCS : Unit × Semantics.CS :=
  Semantics.CSBuilder.runWithInputs (@verifyDigestFromBits lcContext)

end Freigen.F2Z.Examples.EcdsaP256
