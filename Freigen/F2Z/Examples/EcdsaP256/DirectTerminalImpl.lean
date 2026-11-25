import Freigen.F2Z.Examples.EcdsaP256.Impl

/-!
# Direct terminal ECDSA acceptance

The terminal complete addition is consumed only by the ECDSA comparison with
signature `r`.  This specialization therefore constrains the selected lazy X
source directly to `r + n*qScalar + p*qBase`, without opening a canonical
256-bit X coordinate.  A 127-bit slack proves that the scalar representative
`r + n*qScalar` is below the P-256 base modulus.
-/

namespace Freigen.F2Z.Examples.EcdsaP256

open Std.Do
open scoped Std.Do
open Modular
open P256

/-- Return a one-bit scalar quotient, one-bit base quotient, and 127-bit slack
for direct terminal acceptance. -/
def directTerminalHint :
    HList Eff.WitnessSide.denoteF [.z, .z, .z, .z, .z, .z, .z] →
      Hint (Vector Bool 129)
  | h![(active : Int), (pInfinity : Int), (qInfinity : Int),
      (candidateX : Int), (pX : Int), (qX : Int), (r : Int)] =>
      let source := if active = 1 then candidateX
        else if pInfinity = 1 then qX
        else if qInfinity = 1 then pX
        else 0
      if _ : 0 ≤ source then
        if _ : 0 ≤ r then
          let sourceNat := source.toNat
          let rNat := r.toNat
          let x := sourceNat % base.modulus
          let qScalar := (x - rNat) / scalar.modulus
          let qBase := sourceNat / base.modulus
          let slack := if qScalar = 1 then
            base.modulus - scalar.modulus - 1 - rNat
          else 0
          pure $ Vector.ofFn fun i =>
            if i.val = 0 then qScalar.testBit 0
            else if i.val = 1 then qBase.testBit 0
            else slack.testBit (i.val - 2)
        else fail s!"negative signature r {r}"
      else fail s!"negative terminal X source {source}"

/-- Gate the three finite complete-add branches directly against the accepted
integer representative and reject the complete-add identity cases. -/
def selectAddOutputDirectTerminal (r : Fn)
    (P Q : AffineSlope.Point) (control : AffineSlope.AddControl)
    (candidateX : AffineSlope.Rep) : Circuit Unit := do
  let bothInfinity ← AffineSlope.andBit P.infinity Q.infinity
  let bits ← hint
    h![control.active, P.infinity, Q.infinity,
      candidateX.intVal, P.X.intVal, Q.X.intVal, r.val.intVal]
    directTerminalHint
  let qScalar ← U.fromWord {
    bitsLE := Vector.ofFn (n := 1) fun _ => bits[0] }
  let qBase ← U.fromWord {
    bitsLE := Vector.ofFn (n := 1) fun _ => bits[1] }
  let slack ← U.fromWord {
    bitsLE := Vector.ofFn (n := 127) fun i => bits[i.val + 2]'(by omega) }
  let target := r.val.intVal + scalar.modulus • qScalar.intVal +
    base.modulus • qBase.intVal
  assertR1C control.active (candidateX.intVal - target) 0
  assertR1C P.infinity (Q.X.intVal - target) 0
  assertR1C (Q.infinity - bothInfinity) (P.X.intVal - target) 0
  let finiteOpposite ←
    AffineSlope.and3Bit control.sameX control.oppositeY control.finite
  let infinity := bothInfinity + finiteOpposite
  assertR1C 0 0 infinity
  assertR1C qScalar.intVal
    (r.val.intVal + slack.intVal + 1 -
      LC.ofConst ((base.modulus - scalar.modulus : Nat) : Int)) 0

def addCompleteCollapsedDirectTerminal (r : Fn)
    (P Q : AffineSlope.Point) : Circuit Unit := do
  let control ← AffineSlope.classifyAdd P Q
  let candidateX ← AffineSlope.addCandidateCollapsedX P Q control
  selectAddOutputDirectTerminal r P Q control candidateX

end Freigen.F2Z.Examples.EcdsaP256
