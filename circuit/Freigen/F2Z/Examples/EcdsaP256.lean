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

def VerifyDigestAccepts
    (inputs : Vector Bool verifyDigestInputBits) : Prop :=
  ∃ publicKey : Reference.Point,
    Reference.HasCoordinates publicKey
      (verifyDigestInputValue inputs 1).toNat
      (verifyDigestInputValue inputs 2).toNat ∧
    Reference.Verifies (verifyDigestInputValue inputs 0).toNat
      (verifyDigestInputValue inputs 3).toNat
      (verifyDigestInputValue inputs 4).toNat publicKey

/-- Every satisfying assignment of the generated constraint system represents
an input accepted by Mathlib's P-256 ECDSA verifier. -/
theorem verifyDigest_sound
    (inputs : Vector Bool verifyDigestInputBits) (wit : Nat → Bool)
    (hinputs : ∀ i : Fin verifyDigestInputBits, wit i.val = inputs[i])
    (hsat : verifyDigestCS.2.satisfies wit) :
    VerifyDigestAccepts inputs := by
  apply Sound.adequate
    (circ := verifyDigestFromBits)
    (P := fun _ _ => VerifyDigestAccepts inputs)
  · simpa [Sound.csValuation, VerifyDigestAccepts, verifyDigestCS] using
      verifyDigestFromBits_sound_aux
        (ρ := Sound.csValuation verifyDigestCS.2 wit) inputs
  · exact hinputs
  · simpa [verifyDigestCS] using hsat

/-- If the decoded input satisfies Mathlib's ECDSA equation and supplies the
checked inverse witnesses, the real witness generator succeeds and its output
satisfies the generated constraint system. -/
theorem verifyDigest_complete
    (inputs : Vector Bool verifyDigestInputBits)
    (publicKey : Reference.Point)
    (hkeyXlt : (verifyDigestInputValue inputs 1).toNat < P256.base.modulus)
    (hkeyYlt : (verifyDigestInputValue inputs 2).toNat < P256.base.modulus)
    (hrInvlt : (verifyDigestInputValue inputs 5).toNat < P256.scalar.modulus)
    (hsInvlt : (verifyDigestInputValue inputs 6).toNat < P256.scalar.modulus)
    (hcoords : Reference.HasCoordinates publicKey
      (verifyDigestInputValue inputs 1).toNat
      (verifyDigestInputValue inputs 2).toNat)
    (horder : P256.scalarModulus • publicKey = 0)
    (hrInvMul :
      ((verifyDigestInputValue inputs 3).toNat : Reference.Scalar) *
        ((verifyDigestInputValue inputs 5).toNat : Reference.Scalar) = 1)
    (hsInvMul :
      ((verifyDigestInputValue inputs 4).toNat : Reference.Scalar) *
        ((verifyDigestInputValue inputs 6).toNat : Reference.Scalar) = 1)
    (hverifies : Reference.Verifies
      (verifyDigestInputValue inputs 0).toNat
      (verifyDigestInputValue inputs 3).toNat
      (verifyDigestInputValue inputs 4).toNat publicKey) :
    ∃ wit,
      Semantics.Witgen.runWithInputs verifyDigestFromBits inputs = some wit ∧
      verifyDigestCS.2.satisfies (wit[·]!) := by
  have hbits : ∀ i : Fin verifyDigestInputBits,
      (Complete.witnessValuation inputs.toArray).bool i.val = inputs[i] := by
    intro i
    simp [Complete.witnessValuation, getElem!_pos]
  have hcomplete := verifyDigestFromBits_complete_aux
    (ρ := Complete.witnessValuation inputs.toArray) inputs publicKey hbits
    hkeyXlt hkeyYlt hrInvlt hsInvlt hcoords horder hrInvMul hsInvMul hverifies
  have had := Complete.adequate
    verifyDigestFromBits_wf_aux
    hcomplete
  simpa [verifyDigestCS] using had

/-- Quotient well-formedness of the actual raw-input verifier circuit. -/
theorem verifyDigest_wf :
    WF.GadgetSpec VerifyDigestBits.WFRel verifyDigestFromBits
      (fun _ _ _ _ => True) :=
  verifyDigestFromBits_wf_aux

/-! ## Prehashed digest verification circuit size -/

/- Direct construction of the standalone ECDSA-P256 verifier with a 256-bit
message hash supplied as input. SHA-256 is not part of this circuit. -/

/--
info: { mRows := 1215663, mCols := 1215663, r1csRows := 7061 }
-/
#guard_msgs in
#eval verifyDigestCS.2.stats

end Freigen.F2Z.Examples.EcdsaP256
