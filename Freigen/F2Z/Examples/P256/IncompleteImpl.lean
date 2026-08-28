import Freigen.F2Z.Examples.P256.Impl

/-!
# Checked incomplete affine addition

This module isolates the low-cost ordinary chord formula from the complete
affine case split.  The circuit explicitly requires two finite inputs and a
nonzero X-coordinate difference, so exceptional inputs are unsatisfiable
rather than silently receiving incorrect coordinates.
-/

namespace Freigen.F2Z.Examples.P256.AffineSlope

open Std.Do
open scoped Std.Do
open Modular

/-- Add two finite affine points with distinct X coordinates.  A discarded
division of one by the denominator certifies that the ordinary chord formula
is active; the remaining three modular certificates materialize the slope and
the two output coordinates. -/
def addIncompleteChecked (P Q : Point) : Circuit Point := do
  assertR1C 0 0 P.infinity
  assertR1C 0 0 Q.infinity
  let denominator := sub Q.X P.X
  let _ ← Modular.Lazy.divide base denominator (ofElem one)
  let candidate ← finishAddCandidate P Q
    ⟨sub Q.Y P.Y, denominator⟩
  pure ⟨candidate.1, candidate.2, 0⟩

end Freigen.F2Z.Examples.P256.AffineSlope
