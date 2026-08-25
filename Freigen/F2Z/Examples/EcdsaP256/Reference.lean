import Freigen.F2Z.Examples.P256.Reference

/-!
# Mathlib reference semantics for ECDSA-P256

The verifier in this file is the semantic endpoint for the circuit.  Point
addition and scalar multiplication are Mathlib's operations on the P-256
affine point group; scalar arithmetic is `ZMod` at the standard group order.
The two published P-256 primes are the only trusted arithmetic facts.
-/

namespace Freigen.F2Z.Examples.EcdsaP256.Reference

open Freigen.F2Z.Examples.P256

/-- Primality of the published P-256 group order. -/
axiom scalarModulus_prime : Nat.Prime scalarModulus

instance : Fact (Nat.Prime scalarModulus) := ⟨scalarModulus_prime⟩

abbrev Scalar := ZMod scalarModulus
abbrev Point := P256.Reference.Point

/-- Canonical natural-number coordinates, used only when crossing the circuit
boundary or constructing a fixed lookup table.  Infinity maps to `(0,0)`;
callers retain the point itself, so this convention is never ambiguous. -/
def xNat : Point → Nat
  | 0 => 0
  | .some x _ _ => x.val

def yNat : Point → Nat
  | 0 => 0
  | .some _ y _ => y.val

/-- The point calculated by the ECDSA verification equation. -/
def verificationPoint (digest r s : Nat) (publicKey : Point) : Point :=
  let w : Scalar := (s : Scalar)⁻¹
  (((digest : Scalar) * w).val • P256.Reference.generator) +
    (((r : Scalar) * w).val • publicKey)

/-- SEC 1 ECDSA verification for a 256-bit digest.

The digest is cast to the scalar field, which is exactly reduction modulo the
P-256 group order.  Signature scalars are required to be canonical and
nonzero.  The final point is required to be finite and its canonical base-field
x coordinate is reduced modulo the group order before comparison with `r`.
-/
def Verifies (digest r s : Nat) (publicKey : Point) : Prop :=
  publicKey ≠ 0 ∧
  scalarModulus • publicKey = 0 ∧
  0 < r ∧ r < scalarModulus ∧
  0 < s ∧ s < scalarModulus ∧
  match verificationPoint digest r s publicKey with
  | 0 => False
  | .some x _ _ => x.val % scalarModulus = r

end Freigen.F2Z.Examples.EcdsaP256.Reference
