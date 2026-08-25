import Freigen.F2Z.Examples.EcdsaP256.Lemmas

/-!
# ECDSA-P256 verification and Mathlib equivalence

The verification circuits are defined in `EcdsaP256.Impl`. This module
contains their main boundary correctness statements.
-/

namespace Freigen.F2Z.Examples.EcdsaP256

/-! ## Digest verification circuit size -/

/--
info: { mRows := 1159768, mCols := 1159256, r1csRows := 5732 }
-/
#guard_msgs in
#eval verifyDigestCS.2.stats

end Freigen.F2Z.Examples.EcdsaP256
