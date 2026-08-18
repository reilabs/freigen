import Freigen.F2Z.Examples.Sha256.Parameters

namespace Freigen.F2Z.Examples

/-- A word-packed representation of the Boolean witness for the fixed 2 KiB
SHA-256 circuit. Bit `i` is stored as bit `i % 64` of word `i / 64`. -/
structure Sha2562KBPackedWitness where
  words : Array UInt64

/-- The 16384 circuit inputs packed in witness order. Word `i` stores input
bits `64 * i` through `64 * i + 63`, least-significant bit first. -/
abbrev Sha2562KBPackedMessage := Vector UInt64 256

namespace Sha256FastWitgen

/-- Each compression contributes 48 34-bit schedule sums, two 35-bit sums
per round, and eight 33-bit final-state sums. -/
def witnessBitsPerBlock : Nat := 48 * 34 + 64 * 70 + 8 * 33

/-- Size of the Boolean witness, including the message input prefix. -/
def witnessBits : Nat := sha2562KBMessageBits + 33 * witnessBitsPerBlock

/-- Number of `UInt64` words needed for the packed witness. -/
def witnessWords : Nat := (witnessBits + 63) / 64

#guard witnessBits = 226792
#guard witnessWords = 3544

private structure WitnessBuilder where
  words : Array UInt64
  pending : UInt64
  pendingBits : Nat

private def WitnessBuilder.withInput
    (message : Sha2562KBPackedMessage) : WitnessBuilder := Id.run do
  let mut words := Array.mkEmpty witnessWords
  for word in message do
    words := words.push word
  return { words, pending := 0, pendingBits := 0 }

private structure HashState where
  s0 : UInt32
  s1 : UInt32
  s2 : UInt32
  s3 : UInt32
  s4 : UInt32
  s5 : UInt32
  s6 : UInt32
  s7 : UInt32

private def initialState : HashState where
  s0 := 0x6a09e667
  s1 := 0xbb67ae85
  s2 := 0x3c6ef372
  s3 := 0xa54ff53a
  s4 := 0x510e527f
  s5 := 0x9b05688c
  s6 := 0x1f83d9ab
  s7 := 0x5be0cd19

private def roundConstants : Vector UInt32 64 := #v[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

@[inline] private def rotateRight (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

@[inline] private def smallSigma0 (x : UInt32) : UInt32 :=
  rotateRight x 7 ^^^ rotateRight x 18 ^^^ (x >>> 3)

@[inline] private def smallSigma1 (x : UInt32) : UInt32 :=
  rotateRight x 17 ^^^ rotateRight x 19 ^^^ (x >>> 10)

@[inline] private def bigSigma0 (x : UInt32) : UInt32 :=
  rotateRight x 2 ^^^ rotateRight x 13 ^^^ rotateRight x 22

@[inline] private def bigSigma1 (x : UInt32) : UInt32 :=
  rotateRight x 6 ^^^ rotateRight x 11 ^^^ rotateRight x 25

@[inline] private def choose (e f g : UInt32) : UInt32 :=
  (e &&& f) ^^^ ((~~~e) &&& g)

@[inline] private def majority (a b c : UInt32) : UInt32 :=
  (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)

/-- Reverse all 32 bits using five mask-and-swap stages. -/
@[inline] private def reverseBits32 (x : UInt32) : UInt32 :=
  let x : UInt32 := ((x >>> 1) &&& (0x55555555 : UInt32)) |||
    ((x &&& (0x55555555 : UInt32)) <<< 1)
  let x : UInt32 := ((x >>> 2) &&& (0x33333333 : UInt32)) |||
    ((x &&& (0x33333333 : UInt32)) <<< 2)
  let x : UInt32 := ((x >>> 4) &&& (0x0f0f0f0f : UInt32)) |||
    ((x &&& (0x0f0f0f0f : UInt32)) <<< 4)
  let x : UInt32 := ((x >>> 8) &&& (0x00ff00ff : UInt32)) |||
    ((x &&& (0x00ff00ff : UInt32)) <<< 8)
  (x >>> (16 : UInt32)) ||| (x <<< (16 : UInt32))

/-- Append the little-endian bit decomposition used by `U.fromInt` and
`U.fromDoubledInt35`. Since every appended value is at most 35 bits wide, at
most one packed word is completed per call. -/
@[inline] private def appendBitsLE
    (builder : WitnessBuilder) (value : UInt64) (width : Nat) :
    WitnessBuilder :=
  let totalBits := builder.pendingBits + width
  let completed := builder.pending |||
    (value <<< UInt64.ofNat builder.pendingBits)
  if totalBits < 64 then
    { builder with pending := completed, pendingBits := totalBits }
  else
    let consumed := 64 - builder.pendingBits
    { words := builder.words.push completed
      pending := value >>> UInt64.ofNat consumed
      pendingBits := totalBits - 64 }

/-- Derive the SHA-256 words from packed circuit inputs and append the fixed
padding block. The resulting array contains exactly 33 blocks. -/
private def preparePackedInput
    (message : Sha2562KBPackedMessage) :
    Array UInt32 × WitnessBuilder := Id.run do
  let mut blocks := Array.mkEmpty (33 * 16)
  let builder := WitnessBuilder.withInput message
  for packed in message do
    blocks := blocks.push (reverseBits32 packed.toUInt32)
    blocks := blocks.push (reverseBits32 (packed >>> 32).toUInt32)
  blocks := blocks.push 0x80000000
  for _ in [0:14] do
    blocks := blocks.push 0
  blocks := blocks.push 0x00004000
  return (blocks, builder)

/-- Emit one compression block's hints in precisely the allocation order of
`permCircuit`, returning the next chaining state. -/
private def compress
    (blocks : Array UInt32) (block : Nat) (state : HashState)
    (builder : WitnessBuilder) : HashState × WitnessBuilder := Id.run do
  let mut builder := builder

  -- Message schedule: the first 16 words allocate no Boolean witnesses.
  let mut schedule := Array.mkEmpty 64
  for i in [0:16] do
    schedule := schedule.push blocks[block * 16 + i]!
  for i in [16:64] do
    let wide := schedule[i - 16]!.toUInt64 +
      (smallSigma0 schedule[i - 15]!).toUInt64 +
      schedule[i - 7]!.toUInt64 +
      (smallSigma1 schedule[i - 2]!).toUInt64
    builder := appendBitsLE builder wide 34
    schedule := schedule.push wide.toUInt32

  let mut a := state.s0
  let mut b := state.s1
  let mut c := state.s2
  let mut d := state.s3
  let mut e := state.s4
  let mut f := state.s5
  let mut g := state.s6
  let mut h := state.s7

  for hi:i in [0:64] do
    let s1 := bigSigma1 e
    let ch := choose e f g
    let s0 := bigSigma0 a
    let maj := majority a b c
    let ki := roundConstants[i]
    let wi := schedule[i]!

    -- These are the quotients witnessed by the two doubled-sum gadgets.
    let newEWide := d.toUInt64 + h.toUInt64 + s1.toUInt64 +
      ki.toUInt64 + wi.toUInt64 + ch.toUInt64
    builder := appendBitsLE builder newEWide 35
    let newE := newEWide.toUInt32

    let newAWide := h.toUInt64 + s1.toUInt64 + ki.toUInt64 +
      wi.toUInt64 + s0.toUInt64 + ch.toUInt64 + maj.toUInt64
    builder := appendBitsLE builder newAWide 35
    let newA := newAWide.toUInt32

    h := g
    g := f
    f := e
    e := newE
    d := c
    c := b
    b := a
    a := newA

  -- The final additions use 33-bit `U.fromInt` witnesses.
  let r0 := state.s0.toUInt64 + a.toUInt64
  builder := appendBitsLE builder r0 33
  let r1 := state.s1.toUInt64 + b.toUInt64
  builder := appendBitsLE builder r1 33
  let r2 := state.s2.toUInt64 + c.toUInt64
  builder := appendBitsLE builder r2 33
  let r3 := state.s3.toUInt64 + d.toUInt64
  builder := appendBitsLE builder r3 33
  let r4 := state.s4.toUInt64 + e.toUInt64
  builder := appendBitsLE builder r4 33
  let r5 := state.s5.toUInt64 + f.toUInt64
  builder := appendBitsLE builder r5 33
  let r6 := state.s6.toUInt64 + g.toUInt64
  builder := appendBitsLE builder r6 33
  let r7 := state.s7.toUInt64 + h.toUInt64
  builder := appendBitsLE builder r7 33

  return (⟨r0.toUInt32, r1.toUInt32, r2.toUInt32, r3.toUInt32,
    r4.toUInt32, r5.toUInt32, r6.toUInt32, r7.toUInt32⟩, builder)

end Sha256FastWitgen

/-- Pack the circuit's Boolean input representation into `UInt64` witness
words. This adapter is not needed when the caller already has packed input. -/
def packSha2562KBMessage
    (message : Vector Bool sha2562KBMessageBits) :
    Sha2562KBPackedMessage := Vector.ofFn fun word => Id.run do
  let mut packed : UInt64 := 0
  for bit in [0:64] do
    if message[word.val * 64 + bit]! then
      packed := packed ||| (1 <<< UInt64.ofNat bit)
  return packed

/-- Packed-input/packed-output fast path. This avoids all Boolean-array
materialization and is the intended high-performance API. -/
def sha2562KBFastWitgen
    (message : Sha2562KBPackedMessage) :
    Sha2562KBPackedWitness := Id.run do
  let prepared := Sha256FastWitgen.preparePackedInput message
  let blocks := prepared.1
  let mut builder := prepared.2
  let mut state := Sha256FastWitgen.initialState
  for block in [0:33] do
    let result := Sha256FastWitgen.compress blocks block state builder
    state := result.1
    builder := result.2
  let words := if builder.pendingBits = 0 then builder.words
    else builder.words.push builder.pending
  return { words }

/-- A specialized, safe, word-packed witness generator for
`sha2562KBCircuit`.

It computes directly with `UInt32` SHA words and `UInt64` gadget sums, and
stores the resulting Boolean sequence in `UInt64` words.
`Sha2562KBPackedWitness.get` gives the corresponding witgen valuation. -/
def sha2562KBFastWitgenFromBits
    (message : Vector Bool sha2562KBMessageBits) :
    Sha2562KBPackedWitness :=
  sha2562KBFastWitgen (packSha2562KBMessage message)

/-- Read a Boolean from the packed witness. Out-of-range reads are false. -/
@[inline] def Sha2562KBPackedWitness.get
    (witness : Sha2562KBPackedWitness) (i : Nat) : Bool :=
  if i < Sha256FastWitgen.witnessBits then
    match witness.words[i / 64]? with
    | some word => ((word >>> UInt64.ofNat (i % 64)) &&& 1) != 0
    | none => false
  else
    false

/-- Materialize the packed witness in the exact `Array Bool` representation
returned by the generic F2Z witgen. -/
def Sha2562KBPackedWitness.toBoolArray
    (witness : Sha2562KBPackedWitness) : Array Bool := Id.run do
  let mut output := Array.mkEmpty Sha256FastWitgen.witnessBits
  for i in [0:Sha256FastWitgen.witnessBits] do
    output := output.push (witness.get i)
  return output

/-- Exact-array compatibility wrapper for the current generic witgen API. -/
def sha2562KBFastWitgenBoolArray
    (message : Vector Bool sha2562KBMessageBits) : Array Bool :=
  (sha2562KBFastWitgenFromBits message).toBoolArray

end Freigen.F2Z.Examples
