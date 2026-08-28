import Freigen.F2Z.Examples.EcdsaP256.DirectTerminalImpl

/-!
# Block-comparator direct terminal ECDSA acceptance

This specialization replaces the 127-bit terminal canonicality slack with a
16-way byte selector, an 8-way bit-offset selector, and the selected byte of
the already materialized signature scalar.  The comparison is strictly
against `p - n`: higher bits equal the threshold and the selected differing
bit is one below it.
-/

namespace Freigen.F2Z.Examples.EcdsaP256

open Std.Do
open scoped Std.Do
open Modular
open P256

def blockTerminalDelta : Nat := base.modulus - scalar.modulus

/-- Exact integer predicates enforced by the outer and inner comparator gates
for one `(block, offset)` choice. -/
def deltaBlockPairSatisfies (r block offset : Nat) : Bool :=
  let start := 8 * block
  let selected := r / 2 ^ start % 2 ^ 8
  r / 2 ^ start =
      selected + 2 ^ 8 * (blockTerminalDelta / 2 ^ (start + 8)) &&
    selected / 2 ^ offset + 1 =
      blockTerminalDelta / 2 ^ (start + offset) % 2 ^ (8 - offset)

/-- Choose the first pair satisfying the exact comparator predicates.  The
bounded search is proof-friendly even when multiple inner offsets work. -/
def firstDeltaBlockPair (r : Nat) : Nat × Nat :=
  match (List.range (16 * 8)).find? fun index =>
      deltaBlockPairSatisfies r (index / 8) (index % 8) with
  | some index => (index / 8, index % 8)
  | none => (0, 0)

/-- Base/scalar quotient bits, a 16-way block selector, an 8-way bit-offset
selector, and the selected byte of `r`. -/
def deltaBlockTerminalHint :
    HList Eff.WitnessSide.denoteF [.z, .z, .z, .z, .z, .z, .z] →
      Hint (Vector Bool 34)
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
          let qBase := sourceNat / base.modulus
          let qScalar := (x - rNat) / scalar.modulus
          let pair := firstDeltaBlockPair rNat
          let block := pair.1
          let offset := pair.2
          pure $ Vector.ofFn fun i =>
            if _ : i.val = 0 then qBase.testBit 0
            else if _ : i.val = 1 then qScalar.testBit 0
            else if _ : i.val < 18 then
              qScalar.testBit 0 && i.val - 2 = block
            else if _ : i.val < 26 then
              qScalar.testBit 0 && i.val - 18 = offset
            else rNat.testBit (8 * block + (i.val - 26))
        else fail s!"negative signature r {r}"
      else fail s!"negative terminal X source {source}"

def deltaBlockBaseQWord (bits : Vector (LC Bool) 34) : Word 1 :=
  { bitsLE := Vector.ofFn fun _ => bits[0] }

def deltaBlockScalarQWord (bits : Vector (LC Bool) 34) : Word 1 :=
  { bitsLE := Vector.ofFn fun _ => bits[1] }

def deltaBlockOuterWord (bits : Vector (LC Bool) 34) : Word 16 :=
  { bitsLE := Vector.ofFn fun i => bits[i.val + 2]'(by omega) }

def deltaBlockInnerWord (bits : Vector (LC Bool) 34) : Word 8 :=
  { bitsLE := Vector.ofFn fun i => bits[i.val + 18]'(by omega) }

def deltaBlockSelectedWord (bits : Vector (LC Bool) 34) : Word 8 :=
  { bitsLE := Vector.ofFn fun i => bits[i.val + 26]'(by omega) }

def deltaScalarBitsFrom (r : Fn) (start : Nat) : LC ℤ :=
  ∑ i : Fin 256, if start ≤ i.val then
    2 ^ (i.val - start) • r.val.intBits[i] else 0

def deltaSelectedBitsFrom (selected : U 8) (start : Nat) : LC ℤ :=
  ∑ i : Fin 8, if start ≤ i.val then
    2 ^ (i.val - start) • selected.intBits[i] else 0

def outerSelectedDeltaBlockFrom (outer : U 16) (start : Nat) : LC ℤ :=
  ∑ i : Fin 16,
    (blockTerminalDelta / 2 ^ (8 * i.val + start) % 2 ^ (8 - start)) •
      outer.intBits[i]

structure DeltaBlockComparatorInput where
  r : Fn
  qScalar : U 1
  outer : U 16
  inner : U 8
  selectedBlock : U 8

/-- Prove `qScalar = 1 → r < p - n` by choosing the byte and bit of the most
significant difference.  This costs two selector sums and 24 gated checks. -/
def deltaBlockComparator (input : DeltaBlockComparatorInput) : Circuit Unit := do
  assertR1C 1
    ((∑ i : Fin 16, input.outer.intBits[i]) - input.qScalar.intVal) 0
  assertR1C 1
    ((∑ i : Fin 8, input.inner.intBits[i]) - input.qScalar.intVal) 0
  for h:i in [0:16] do
    let start := 8 * i
    let expected := input.selectedBlock.intVal + LC.ofConst
      (2 ^ 8 * (blockTerminalDelta / 2 ^ (start + 8) : Nat) : Int)
    assertR1C input.outer.intBits[i]
      (deltaScalarBitsFrom input.r start - expected) 0
  for h:j in [0:8] do
    assertR1C input.inner.intBits[j]
      (deltaSelectedBitsFrom input.selectedBlock j -
        (outerSelectedDeltaBlockFrom input.outer j - 1)) 0

/-- Complete terminal addition fused directly into the strict-delta block
comparison.  No terminal X coordinate is materialized. -/
def selectAddOutputDeltaBlock (r : Fn) (P Q : AffineSlope.Point)
    (control : AffineSlope.AddControl)
    (candidateX : AffineSlope.Rep) : Circuit Unit := do
  let bothInfinity ← AffineSlope.andBit P.infinity Q.infinity
  let bits ← hint
    h![control.active, P.infinity, Q.infinity,
      candidateX.intVal, P.X.intVal, Q.X.intVal, r.val.intVal]
    deltaBlockTerminalHint
  let qBase ← U.fromWord (deltaBlockBaseQWord bits)
  let qScalar ← U.fromWord (deltaBlockScalarQWord bits)
  let outer ← U.fromWord (deltaBlockOuterWord bits)
  let inner ← U.fromWord (deltaBlockInnerWord bits)
  let selectedBlock ← U.fromWord (deltaBlockSelectedWord bits)
  let target := r.val.intVal + scalar.modulus • qScalar.intVal +
    base.modulus • qBase.intVal
  assertR1C control.active (candidateX.intVal - target) 0
  assertR1C P.infinity (Q.X.intVal - target) 0
  assertR1C (Q.infinity - bothInfinity) (P.X.intVal - target) 0
  deltaBlockComparator ⟨r, qScalar, outer, inner, selectedBlock⟩
  let finiteOpposite ←
    AffineSlope.and3Bit control.sameX control.oppositeY control.finite
  assertR1C 0 0 (bothInfinity + finiteOpposite)

def addCompleteCollapsedDeltaBlock (r : Fn)
    (P Q : AffineSlope.Point) : Circuit Unit := do
  let control ← AffineSlope.classifyAdd P Q
  let candidateX ← AffineSlope.addCandidateCollapsedX P Q control
  selectAddOutputDeltaBlock r P Q control candidateX

end Freigen.F2Z.Examples.EcdsaP256
