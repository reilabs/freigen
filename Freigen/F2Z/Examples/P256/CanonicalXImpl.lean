import Freigen.F2Z.Examples.P256.XOnlyImpl

/-!
# Canonical terminal X-only complete affine addition

This terminal specialization retains the complete affine case split while
opening a single base-field-canonical X coordinate.  The quotient witnessing
reduction of the selected source modulo the P-256 base prime is one bit because
all affine source representations have static bound two.
-/

namespace Freigen.F2Z.Examples.P256.AffineSlope

open Std.Do
open scoped Std.Do
open Modular

structure CanonicalXPoint where
  X : Elem base
  infinity : LC ℤ

/-- Select the active candidate/identity X source, reduce it modulo the P-256
base field, and return its 256 canonical bits followed by a one-bit quotient. -/
def canonicalAddXHint :
    HList Eff.WitnessSide.denoteF [.z, .z, .z, .z, .z, .z] →
      Hint (Vector Bool 257)
  | h![(active : Int), (pInfinity : Int), (qInfinity : Int),
      (candidateX : Int), (pX : Int), (qX : Int)] =>
      let source := if active = 1 then candidateX
        else if pInfinity = 1 then qX
        else if qInfinity = 1 then pX
        else 0
      if _ : 0 ≤ source then
        let x := source.toNat % base.modulus
        let quotient := source.toNat / base.modulus
        pure $ Vector.ofFn fun i =>
          if _ : i.val < 256 then x.testBit i.val else quotient.testBit 0
      else fail s!"negative terminal X source {source}"

/-- Complete-add output specialization that opens one canonical X word and no
Y word. Three mutually exclusive gates identify the active, P-infinity, and
Q-infinity branches. Opposite and both-infinity cases are represented only by
the returned infinity flag and are rejected by terminal ECDSA acceptance. -/
def selectAddOutputCanonicalX (P Q : Point) (control : AddControl)
    (candidateX : Rep) : Circuit CanonicalXPoint := do
  let bothInfinity ← andBit P.infinity Q.infinity
  let bits ← hint
    h![control.active, P.infinity, Q.infinity,
      candidateX.intVal, P.X.intVal, Q.X.intVal]
    canonicalAddXHint
  let xWord ← U.fromWord {
    bitsLE := Vector.ofFn fun i => bits[i.val]'(by omega) }
  let quotient ← U.fromWord {
    bitsLE := Vector.ofFn (n := 1) fun _ => bits[256] }
  let reduced := xWord.intVal + base.modulus • quotient.intVal
  assertR1C control.active (candidateX.intVal - reduced) 0
  assertR1C P.infinity (Q.X.intVal - reduced) 0
  assertR1C (Q.infinity - bothInfinity) (P.X.intVal - reduced) 0
  let X ← Modular.ofU base xWord
  let finiteOpposite ← and3Bit control.sameX control.oppositeY control.finite
  pure ⟨X, bothInfinity + finiteOpposite⟩

def addCompleteCollapsedCanonicalX (P Q : Point) :
    Circuit CanonicalXPoint := do
  let control ← classifyAdd P Q
  let candidateX ← addCandidateCollapsedX P Q control
  selectAddOutputCanonicalX P Q control candidateX

end Freigen.F2Z.Examples.P256.AffineSlope
