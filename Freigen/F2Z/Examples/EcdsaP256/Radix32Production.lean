import Freigen.F2Z.Examples.EcdsaP256.FixedBaseCombImpl

/-! Production ECDSA verifier using a fixed-base comb and signed radix-32
variable-base multiplication. -/

namespace Freigen.F2Z.Examples.EcdsaP256

open Std.Do
open scoped Std.Do
open Modular
open P256

def computeVerificationSum (input : PreparedVerification) :
    Circuit AffineSlope.Point :=
  fixedCombVerificationSum input

def computeVerificationX (input : PreparedVerification) :
    Circuit AffineSlope.XPoint :=
  fixedCombVerificationX input

def computeVerificationCanonicalX (input : PreparedVerification) :
    Circuit AffineSlope.CanonicalXPoint :=
  fixedCombVerificationCanonicalX input

def computeVerificationDirectTerminal (input : PreparedVerification) :
    Circuit Unit :=
  fixedCombVerificationDirectTerminal input

def computeVerificationDeltaBlock (input : PreparedVerification) :
    Circuit Unit :=
  fixedCombVerificationDeltaBlock input

def finishVerification (input : PreparedVerification) : Circuit Unit :=
  computeVerificationDeltaBlock input

/-- Verify an ECDSA-P256 signature over an already computed SHA-256 digest
using a mixed-width fixed-base comb and signed radix-32 Booth recoding. -/
def verifyDigest (digest : U 256) (key : PublicKey)
    (sig : Signature) (aux : Aux) : Circuit Unit := do
  let input ← canonicalizeInput key sig aux
  let prepared ← prepareVerification digest input
  finishVerification prepared

def verifyDigestFromBits
    (inputs : Vector (LC Bool) verifyDigestInputBits) : Circuit Unit := do
  let values ← (verifyDigestInputWords inputs).mapM U.fromWord
  verifyDigest values[0] ⟨values[1], values[2]⟩
    ⟨values[3], values[4]⟩ ⟨values[5], values[6]⟩

/-- Constraint system for the optimized prehashed ECDSA verifier. -/
def verifyDigestCS : Unit × Semantics.CS :=
  Semantics.CSBuilder.runWithInputs verifyDigestFromBits

end Freigen.F2Z.Examples.EcdsaP256
