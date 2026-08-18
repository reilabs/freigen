import Freigen.F2Z.Examples.Sha256.Impl
import Freigen.F2Z.Examples.Sha256.Parameters

namespace Freigen.F2Z.Examples

def sha256Word (value : BitVec 32) : Word 32 :=
  { bitsLE := Vector.ofFn fun i => LC.ofConst value[i] }

/-- The initial hash value from FIPS 180-4, section 5.3.3. -/
def sha256InitialState : Vector (Word 32) 8 := #v[
  sha256Word 0x6a09e667, sha256Word 0xbb67ae85,
  sha256Word 0x3c6ef372, sha256Word 0xa54ff53a,
  sha256Word 0x510e527f, sha256Word 0x9b05688c,
  sha256Word 0x1f83d9ab, sha256Word 0x5be0cd19
]

/-- Padding for a message of exactly 2048 bytes. The first word contributes
the mandatory `1` bit and the final two words encode the 16384-bit length. -/
def sha2562KBPaddingBlock : Vector (Word 32) 16 := #v[
  sha256Word 0x80000000, sha256Word 0x00000000,
  sha256Word 0x00000000, sha256Word 0x00000000,
  sha256Word 0x00000000, sha256Word 0x00000000,
  sha256Word 0x00000000, sha256Word 0x00000000,
  sha256Word 0x00000000, sha256Word 0x00000000,
  sha256Word 0x00000000, sha256Word 0x00000000,
  sha256Word 0x00000000, sha256Word 0x00000000,
  sha256Word 0x00000000, sha256Word 0x00004000
]

/-- Compute SHA-256 for an exactly 2 KiB message.

Both the input message and output digest use the conventional stream order:
bytes are ordered from first to last and the bits within each byte are ordered
most-significant first. The circuit processes 32 message blocks followed by
the fixed SHA-256 padding block. -/
def sha2562KBCircuit
    (message : Vector (LC Bool) sha2562KBMessageBits) :
    Circuit (Vector (LC Bool) 256) := do
  let mut state := sha256InitialState
  for hBlock:block in [0:32] do
    let words : Vector (Word 32) 16 := Vector.ofFn fun word =>
      { bitsLE := Vector.ofFn fun bit =>
          message[block * 512 + word.val * 32 + (31 - bit.val)]'(by
            have block_lt : block < 32 := hBlock.2.1
            simp [sha2562KBMessageBits, sha2562KBMessageBytes]
            omega) }
    let nextState ← permCircuit words state
    state := nextState.map (·.bits)
  let digest ← permCircuit sha2562KBPaddingBlock state
  pure $ Vector.ofFn fun i =>
    digest[i.val / 32].bits.bitsLE[31 - (i.val % 32)]

/-- Constraint-system representation of `sha2562KBCircuit`. -/
abbrev sha2562KBCS : Vector (LC Bool) 256 × Semantics.CS :=
  Semantics.CSBuilder.runWithInputs sha2562KBCircuit

end Freigen.F2Z.Examples
