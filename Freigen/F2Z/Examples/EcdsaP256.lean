import Freigen.F2Z.Examples.P256
import Freigen.F2Z.Examples.Sha256.Full

/-!
# ECDSA/SHA-256 verification on P-256

`verifyDigest` implements SEC 1 ECDSA verification for a 256-bit SHA-256
digest.  `verify2KB` composes it with F2Z's existing, proved SHA-256 circuit for
an exactly 2 KiB message.

The inverse values are auxiliary, proof-carrying witnesses.  This avoids
embedding extended Euclid in the constraint system: `checkedInv` verifies each
witness with a modular multiplication and exact equality.  They are no more
trusted than any other witness value.

The digest conversion deserves attention: SHA-256 emits conventional stream
order (most-significant bit first), while `U` deliberately stores bits little
endian.  `sha256DigestU` is the single explicit reversal between those two
representations.
-/

namespace Freigen.F2Z.Examples.EcdsaP256

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

/-- Auxiliary witnesses.  `rInv` proves `r != 0`, `sInv` both proves `s != 0`
and supplies the ECDSA inverse, and `zInv` normalizes the final projective
point. -/
structure Aux where
  rInv : U 256
  sInv : U 256
  zInv : U 256

/-- Interpret the conventional big-endian SHA-256 output as a little-endian
`U 256`. -/
def sha256DigestU (digest : Vector (LC Bool) 256) : Circuit (U 256) :=
  U.fromWord { bitsLE := Vector.ofFn fun i => digest[255 - i.val]'(by omega) }

/-- Verify an ECDSA-P256 signature over an already computed SHA-256 digest.

All external integers are first made canonical.  Therefore the circuit rejects
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
  let zInv ← ofU base aux.zInv

  assertOnCurve qx qy

  -- These checks enforce 1 <= r,s < n.  Canonicality gives the upper bound;
  -- existence of an inverse modulo the prime group order excludes zero.
  let _ ← checkedInv scalar fnOne r rInv
  let w ← checkedInv scalar fnOne s sInv

  -- SHA-256 and the group order are both 256 bits.  Reduction implements the
  -- SEC 1 `bits2int`/mod-n behavior for P-256.
  let z ← reduce scalar digest.intVal
  let u1 ← mul scalar z w
  let u2 ← mul scalar r w

  let q : Projective := ⟨qx, qy, one⟩
  let p1 ← scalarMul u1 generator
  let p2 ← scalarMul u2 q
  let sum ← addComplete p1 p2

  -- A point at infinity has Z=0 and consequently cannot pass this checked
  -- inverse.  Homogeneous coordinates normalize with x = X/Z.
  let iz ← checkedInv base one sum.Z zInv
  let affineX ← mul base sum.X iz
  let xModN ← reduce scalar affineX.val.intVal
  assertEq scalar xModN r

/-- Hash and verify an exactly 2 KiB message.  The length matches the existing
full SHA-256 example and includes its fixed, standard padding block. -/
def verify2KB
    (message : Vector (LC Bool) sha2562KBMessageBits)
    (key : PublicKey) (sig : Signature) (aux : Aux) : Circuit Unit := do
  let digestBE ← sha2562KBCircuit message
  let digest ← sha256DigestU digestBE
  verifyDigest digest key sig aux

/-! ## Boundary well-formedness

The arithmetic and curve callees carry their complete/sound/wf triples in
`Modular.lean` and `P256.lean`.  The conversion below records the endian bridge
as a reusable wf gadget as well.
-/

theorem sha256DigestU_wf :
    WF.GadgetSpec
      (WF.VectorRel (fun lv rv (l r : LC Bool) =>
        WF.LCEq lv.bool rv.bool l r))
      sha256DigestU U.WFRel := by
  wfgen' using [U.fromWord_wf_rel] unfold [sha256DigestU]
  intro i
  apply h

end Freigen.F2Z.Examples.EcdsaP256
