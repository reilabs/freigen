import Freigen.F2Z.Examples.EcdsaP256.Lemmas
import Freigen.F2Z.Examples.EcdsaP256.WF

/-!
# ECDSA-P256 verification and Mathlib equivalence

The verification circuits are defined in `EcdsaP256.Impl`. This module
contains their main boundary correctness statements.
-/

namespace Freigen.F2Z.Examples.EcdsaP256

open Std.Do
open scoped Std.Do

/-! ## Correctness boundary -/

/-- If the real digest-verification circuit accepts, the supplied key
coordinates denote a Mathlib P-256 point and Mathlib's ECDSA equation accepts
the same digest and signature. -/
theorem verifyDigest_sound {digest : U 256} {key : PublicKey}
    {sig : Signature} {aux : Aux}
    (hdigest : digest.Valid ρ)
    (hkeyX : key.x.Valid ρ) (hkeyY : key.y.Valid ρ)
    (hr : sig.r.Valid ρ) (hs : sig.s.Valid ρ)
    (hrInv : aux.rInv.Valid ρ) (hsInv : aux.sInv.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (verifyDigest digest key sig aux)
    ⦃⇓ _ => ⌜∃ publicKey : Reference.Point,
      Reference.HasCoordinates publicKey
        (Int.castRingHom P256.Reference.Field
          (key.x.intVal.eval ρ.int))
        (Int.castRingHom P256.Reference.Field
          (key.y.intVal.eval ρ.int)) ∧
      Reference.Verifies (digest.eval ρ).toNat
        (sig.r.eval ρ).toNat (sig.s.eval ρ).toNat publicKey⌝⦄ :=
  verifyDigest_sound_aux hdigest hkeyX hkeyY hr hs hrInv hsInv

/-- If Mathlib's ECDSA equation and the explicit inverse witnesses hold,
witness generation for the real digest-verification circuit succeeds. -/
theorem verifyDigest_complete {digest : U 256} {key : PublicKey}
    {sig : Signature} {aux : Aux} {publicKey : Reference.Point}
    (hdigest : digest.Valid ρ)
    (hkeyX : key.x.Valid ρ) (hkeyY : key.y.Valid ρ)
    (hr : sig.r.Valid ρ) (hs : sig.s.Valid ρ)
    (hrInv : aux.rInv.Valid ρ) (hsInv : aux.sInv.Valid ρ)
    (hkeyXlt : key.x.intVal.eval ρ.int < P256.base.modulus)
    (hkeyYlt : key.y.intVal.eval ρ.int < P256.base.modulus)
    (hrlt : sig.r.intVal.eval ρ.int < P256.scalar.modulus)
    (hslt : sig.s.intVal.eval ρ.int < P256.scalar.modulus)
    (hrInvlt : aux.rInv.intVal.eval ρ.int < P256.scalar.modulus)
    (hsInvlt : aux.sInv.intVal.eval ρ.int < P256.scalar.modulus)
    (hcoords : Reference.HasCoordinates publicKey
      (Int.castRingHom P256.Reference.Field (key.x.intVal.eval ρ.int))
      (Int.castRingHom P256.Reference.Field (key.y.intVal.eval ρ.int)))
    (horder : P256.scalarModulus • publicKey = 0)
    (hrInvMul : ((sig.r.eval ρ).toNat : Reference.Scalar) *
      ((aux.rInv.eval ρ).toNat : Reference.Scalar) = 1)
    (hsInvMul : ((sig.s.eval ρ).toNat : Reference.Scalar) *
      ((aux.sInv.eval ρ).toNat : Reference.Scalar) = 1)
    (hverifies : Reference.Verifies (digest.eval ρ).toNat
      (sig.r.eval ρ).toNat (sig.s.eval ρ).toNat publicKey) :
    ⦃⌜True⌝⦄ Complete.interp ρ (verifyDigest digest key sig aux)
    ⦃⇓ _ => ⌜Reference.Verifies (digest.eval ρ).toNat
      (sig.r.eval ρ).toNat (sig.s.eval ρ).toNat publicKey⌝⦄ :=
  verifyDigest_complete_aux hdigest hkeyX hkeyY hr hs hrInv hsInv
    hkeyXlt hkeyYlt hrlt hslt hrInvlt hsInvlt hcoords horder
    hrInvMul hsInvMul hverifies

/-- Quotient well-formedness of the real digest-verification circuit.  Inputs
are related exactly when every circuit-visible linear combination evaluates
equally under the two total valuations. -/
theorem verifyDigest_wf :
    WF.GadgetSpec VerifyInput.WFRel
      (fun input => verifyDigest input.1 input.2.1 input.2.2.1 input.2.2.2)
      (fun _ _ _ _ => True) :=
  verifyDigest_wf_aux

/-! ## Prehashed digest verification circuit size -/

/- Direct construction of the standalone ECDSA-P256 verifier with a 256-bit
message hash supplied as input. SHA-256 is not part of this circuit. -/

/--
info: { mRows := 1215663, mCols := 1215663, r1csRows := 7061 }
-/
#guard_msgs in
#eval verifyDigestCS.2.stats

end Freigen.F2Z.Examples.EcdsaP256
