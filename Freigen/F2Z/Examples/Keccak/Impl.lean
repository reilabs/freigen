import Freigen.F2Z.Examples.Keccak.Model
import Freigen.F2Z.Semantics

namespace Freigen.F2Z.Examples.Keccak

instance : Inhabited (Word n) :=
  ⟨{ bitsLE := Vector.replicate n 0 }⟩

def wordOfBitVec (x : BitVec n) : Word n :=
  { bitsLE := Vector.ofFn fun i => x[i] }

/-- A single nonlinear Keccak term, `(!y) && z`.  Its result is a fresh
Boolean wire and the R1CS equation is exactly the displayed Boolean formula. -/
def andNotBit (y z : LC Bool) : Circuit (LC Bool) := do
  let out ← hint h![y, z] fun h![y, z] => pure #v[(!y) && z]
  let yi ← f2z y
  let zi ← f2z z
  let oi ← f2z out[0]
  assertR1C (1 - yi) zi oi
  pure out[0]

def andNotWord (y z : Word n) : Circuit (Word n) := do
  let bits ← Vector.ofFnM fun i => andNotBit y.bitsLE[i] z.bitsLE[i]
  pure { bitsLE := bits }

def thetaCWords (input : Vector (Word 64) 25) : Vector (Word 64) 5 :=
  Vector.ofFn fun x =>
    input[laneIndex x 0]! ^^^ input[laneIndex x 1]! ^^^
    input[laneIndex x 2]! ^^^ input[laneIndex x 3]! ^^^
    input[laneIndex x 4]!

def thetaDWords (c : Vector (Word 64) 5) : Vector (Word 64) 5 :=
  Vector.ofFn fun x =>
    c[(x.val + 4) % 5]! ^^^
      c[(x.val + 1) % 5]!.rotateRight 63

def thetaWords (input : Vector (Word 64) 25) : Vector (Word 64) 25 :=
  let d := thetaDWords (thetaCWords input)
  Vector.ofFn fun i => input[i] ^^^ d[i.val % 5]!

def rhoPiWords (input : Vector (Word 64) 25) : Vector (Word 64) 25 :=
  Vector.ofFn fun i =>
    let x := i.val % 5
    let y := i.val / 5
    let sourceX := (x + 3 * y) % 5
    let sourceY := x
    let offset := rotationOffsets[laneIndex sourceX sourceY]!
    input[laneIndex sourceX sourceY]!.rotateRight ((64 - offset) % 64)

def chiLaneCircuit (input : Vector (Word 64) 25) (i : Fin 25) :
    Circuit (Word 64) := do
  let x := i.val % 5
  let y := i.val / 5
  let nonlinear ← andNotWord
    input[laneIndex ((x + 1) % 5) y]!
    input[laneIndex ((x + 2) % 5) y]!
  pure (input[laneIndex x y]! ^^^ nonlinear)

def chiCircuit (input : Vector (Word 64) 25) :
    Circuit (Vector (Word 64) 25) :=
  Vector.ofFnM (chiLaneCircuit input)

def iotaWords (rc : BitVec 64) (input : Vector (Word 64) 25) :
    Vector (Word 64) 25 :=
  input.set! 0 (input[0]! ^^^ wordOfBitVec rc)

/-- One circuit round.  Linear Keccak operations remain linear combinations;
only the AND-NOT term in χ allocates constrained witness bits. -/
def roundCircuit (rc : BitVec 64) (input : Vector (Word 64) 25) :
    Circuit (Vector (Word 64) 25) := do
  let b := rhoPiWords (thetaWords input)
  let afterChi ← chiCircuit b
  pure (iotaWords rc afterChi)

def permCircuit (input : Vector (Word 64) 25) :
    Circuit (Vector (Word 64) 25) := do
  let mut state := input
  for r in [0:24] do
    state ← roundCircuit roundConstants[r]! state
  pure state

def inputWords (input : Vector (LC Bool) 1600) : Vector (Word 64) 25 :=
  Vector.ofFn fun lane =>
    { bitsLE := Vector.ofFn fun bit => input[lane.val * 64 + bit.val] }

def flattenOutput (output : Vector (Word 64) 25) : Vector (LC Bool) 1600 :=
  Vector.ofFn fun i => output[i.val / 64].bitsLE[i.val % 64]

def permCirc (input : Vector (LC Bool) 1600) :
    Circuit (Vector (LC Bool) 1600) := do
  let output ← permCircuit (inputWords input)
  pure (flattenOutput output)

abbrev keccakCS : Vector (LC Bool) 1600 × Semantics.CS :=
  Semantics.CSBuilder.runWithInputs permCirc

end Freigen.F2Z.Examples.Keccak
