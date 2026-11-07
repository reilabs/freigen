import Freigen.F2Z.Examples.P256.Impl

/-!
# Terminal X-only complete affine addition

ECDSA acceptance consumes only the final X coordinate and infinity flag.  This
terminal specialization retains the complete affine case split while omitting
the candidate and selected Y-coordinate materializations.
-/

namespace Freigen.F2Z.Examples.P256.AffineSlope

open Std.Do
open scoped Std.Do
open Modular

structure XPoint where
  X : Rep
  infinity : LC ℤ

def finishAddCandidateX (P Q : Point) (operands : SlopeOperands) :
    Circuit Rep := do
  let slope ← Modular.Lazy.divide base
    operands.denominator operands.numerator
  let candidateX ←
    Modular.Lazy.mulSubToElem base slope slope (add P.X Q.X)
  pure (ofElem candidateX)

def addCandidateCollapsedX (P Q : Point) (control : AddControl) :
    Circuit Rep := do
  let operands ← selectSlopeOperandsCollapsedTight P Q control
  finishAddCandidateCollapsedX P Q operands

def selectAddOutputCollapsedX (P Q : Point) (control : AddControl)
    (candidateX : Rep) : Circuit XPoint := do
  let bothInfinity ← andBit P.infinity Q.infinity
  let X ← selectAddCoordinateCollapsed P.X Q.X candidateX
    P Q control bothInfinity
  let finiteOpposite ← and3Bit control.sameX control.oppositeY control.finite
  pure ⟨X, bothInfinity + finiteOpposite⟩

def addCompleteCollapsedX (P Q : Point) : Circuit XPoint := do
  let control ← classifyAdd P Q
  let candidateX ← addCandidateCollapsedX P Q control
  selectAddOutputCollapsedX P Q control candidateX

end Freigen.F2Z.Examples.P256.AffineSlope
