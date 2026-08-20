import Freigen.F2Z.Gadgets

namespace Freigen.F2Z.Examples.Keccak

/-- The Keccak-f[1600] round constants, in round order. -/
def roundConstants : Vector (BitVec 64) 24 := #v[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808a,
  0x8000000080008000, 0x000000000000808b, 0x0000000080000001,
  0x8000000080008081, 0x8000000000008009, 0x000000000000008a,
  0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
  0x000000008000808b, 0x800000000000008b, 0x8000000000008089,
  0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
  0x000000000000800a, 0x800000008000000a, 0x8000000080008081,
  0x8000000000008080, 0x0000000080000001, 0x8000000080008008
]

/-- Rotation offsets indexed by `x + 5*y`. -/
def rotationOffsets : Vector Nat 25 := #v[
   0,  1, 62, 28, 27,
  36, 44,  6, 55, 20,
   3, 10, 43, 25, 39,
  41, 45, 15, 21,  8,
  18,  2, 61, 56, 14
]

@[inline] def laneIndex (x y : Nat) : Nat := x + 5 * y

/-- Rotate a Keccak lane left.  Writing it via right rotation keeps its
bit ordering aligned with `Word.rotateRight` in the circuit layer. -/
@[inline] def rotl (lane : BitVec 64) (offset : Nat) : BitVec 64 :=
  lane.rotateRight ((64 - offset) % 64)

def thetaC (input : Vector (BitVec 64) 25) : Vector (BitVec 64) 5 :=
  Vector.ofFn fun x =>
    input[laneIndex x 0]! ^^^ input[laneIndex x 1]! ^^^
    input[laneIndex x 2]! ^^^ input[laneIndex x 3]! ^^^
    input[laneIndex x 4]!

def thetaD (c : Vector (BitVec 64) 5) : Vector (BitVec 64) 5 :=
  Vector.ofFn fun x =>
    c[(x.val + 4) % 5]! ^^^ rotl c[(x.val + 1) % 5]! 1

def theta (input : Vector (BitVec 64) 25) : Vector (BitVec 64) 25 :=
  let d := thetaD (thetaC input)
  Vector.ofFn fun i =>
    input[i] ^^^ d[i.val % 5]!

def rhoPi (input : Vector (BitVec 64) 25) : Vector (BitVec 64) 25 :=
  Vector.ofFn fun i =>
    let x := i.val % 5
    let y := i.val / 5
    -- Inverse of B[y, 2*x+3*y] = rot(A[x,y], r[x,y]).
    let sourceX := (x + 3 * y) % 5
    let sourceY := x
    rotl input[laneIndex sourceX sourceY]!
      rotationOffsets[laneIndex sourceX sourceY]!

def chiLane (input : Vector (BitVec 64) 25) (i : Fin 25) : BitVec 64 :=
  let x := i.val % 5
  let y := i.val / 5
  input[laneIndex x y]! ^^^
    ((~~~input[laneIndex ((x + 1) % 5) y]!) &&&
      input[laneIndex ((x + 2) % 5) y]!)

def chi (input : Vector (BitVec 64) 25) : Vector (BitVec 64) 25 :=
  Vector.ofFn (chiLane input)

def iota (rc : BitVec 64) (input : Vector (BitVec 64) 25) :
    Vector (BitVec 64) 25 :=
  input.set! 0 (input[0]! ^^^ rc)

/-- One deliberately direct Keccak-f[1600] round.  The state is in the usual
`x + 5*y` lane order. -/
def round (rc : BitVec 64) (input : Vector (BitVec 64) 25) :
    Vector (BitVec 64) 25 :=
  iota rc (chi (rhoPi (theta input)))

/-- The obvious executable model of Keccak-f[1600]. -/
def perm (input : Vector (BitVec 64) 25) : Vector (BitVec 64) 25 :=
  ([0:24].toList).foldl
    (fun state r => round roundConstants[r]! state) input

/-- Bit-oriented form used by the constraint-system correctness statement.
Both input and output use little-endian bits within each lane. -/
def permBits (input : Vector Bool 1600) : Vector Bool 1600 :=
  let lanes : Vector (BitVec 64) 25 := Vector.ofFn fun lane =>
    BitVec.ofNat 64 (Nat.ofBits fun (bit : Fin 64) =>
      input[lane.val * 64 + bit.val])
  let output := perm lanes
  Vector.ofFn fun i => output[i.val / 64].toNat.testBit (i.val % 64)

end Freigen.F2Z.Examples.Keccak
