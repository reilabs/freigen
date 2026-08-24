import Freigen.F2Z.Defs
import Freigen.F2Z.Gadgets
import Freigen.F2Z.Semantics

namespace Freigen.F2Z.Examples

def k : Vector (BitVec 32) 64 := #v[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

section Circuit

/-- Bit-producing reference gadget retained for its standalone specification.
The SHA-256 round circuit uses `ch2` below and does not call this gadget. -/
def U.ch (u v w : U n) : Circuit (U n) := do
  let chBits ← Vector.ofFnM (n:=n) fun i => do
    let h ← hint h![u.bits[i], v.bits[i], w.bits[i]] fun h![u, v, w] =>
      pure $ #v[(u && v) ^^ ((!u) && w)]
    pure h[0]
  let ch ← U.fromWord { bitsLE := chBits }
  let uv ← U.fromWord $ u.bits ^^^ v.bits
  let uw ← U.fromWord $ u.bits ^^^ w.bits
  assertR1C 0 0 $ v.intVal + w.intVal - uv.intVal + uw.intVal - 2 • ch.intVal
  pure ch

/-- Bit-producing reference gadget retained for its standalone specification.
The SHA-256 round circuit uses `maj2` below and does not call this gadget. -/
def U.maj (u v w : U n) : Circuit (U n) := do
  let majBits ← Vector.ofFnM (n:=n) fun i => do
    let h ← hint h![u.bits[i], v.bits[i], w.bits[i]] fun h![u, v, w] =>
      pure $ #v[(u && v) ^^ (u && w) ^^ (v && w)]
    pure h[0]
  let maj ← U.fromWord { bitsLE := majBits }
  let uvw ← U.fromWord $ u.bits ^^^ v.bits ^^^ w.bits
  assertR1C 0 0 $ u.intVal + v.intVal + w.intVal - uvw.intVal - 2 • maj.intVal
  pure maj

def U.ch2 (u v w : U n) : Circuit (LC ℤ) := do
  let uv ← U.fromWord $ u.bits ^^^ v.bits
  let uw ← U.fromWord $ u.bits ^^^ w.bits
  pure $ v.intVal + w.intVal - uv.intVal + uw.intVal

def U.maj2 (u v w : U n) : Circuit (LC ℤ) := do
  let uvw ← U.fromWord $ u.bits ^^^ v.bits ^^^ w.bits
  pure $ u.intVal + v.intVal + w.intVal - uvw.intVal

/-- Decompose a nonnegative integer while supplying its least-significant bit
as an existing affine F₂ expression.  Only the remaining `n` bits are hinted. -/
def U.fromIntWithLowBit (n : Nat) (x : LC ℤ) (low : LC Bool) :
    Circuit (U (n + 1)) := do
  let upper : Vector (LC Bool) n ← hint h![x] fun h![(x : Int)] => match x with
    | .ofNat value => pure $ Vector.ofFn fun i => value.testBit (i + 1)
    | _ => fail s!"negative integer {x} in U.fromIntWithLowBit"
  let bits : Vector (LC Bool) (n + 1) := Vector.ofFn fun i =>
    if h : i.val = 0 then low else upper[i.val - 1]'(by omega)
  let r ← U.fromWord { bitsLE := bits }
  assertR1C 0 0 (x - r.intVal)
  pure r

def U.fromIntWithLowBitPair (n : Nat) (z : LC ℤ × LC Bool) :
    Circuit (U (n + 1)) :=
  U.fromIntWithLowBit n z.1 z.2

/-- Sum words modulo `2^32`, deriving the low output bit as the XOR of the
input low bits instead of allocating it as a fresh witness. -/
def U.sumFixedAffineLow (us : Vector (U 32) m) : Circuit (U 32) := do
  let total := (us.toArray.map (fun u => u.intVal)).sum
  let low := (us.toArray.map (fun u => u.bits.bitsLE[0])).sum
  let wide ← U.fromIntWithLowBitPair (31 + Nat.clog 2 m) (total, low)
  pure $ wide.takeLE 32 (by omega)

/-- Witness the 35-bit quotient of an even nonnegative integer by two.  The
constraint proves the shift without allocating the known-zero low input bit. -/
def U.fromDoubledInt35 (x : LC ℤ) : Circuit (U 35) := do
  let bits ← hint h![x] fun h![(x : Int)] => match x with
    | .ofNat n => pure $ Vector.ofFn fun i => (n / 2).testBit i
    | _ => fail s!"negative integer {x} in U.fromDoubledInt35"
  let r ← U.fromWord { bitsLE := bits }
  assertR1C 0 0 (x - 2 • r.intVal)
  pure r

/-- Witness the 34-bit quotient of an even nonnegative integer by two. -/
def U.fromDoubledInt34 (x : LC ℤ) : Circuit (U 34) := do
  let bits ← hint h![x] fun h![(x : Int)] => match x with
    | .ofNat n => pure $ Vector.ofFn fun i => (n / 2).testBit i
    | _ => fail s!"negative integer {x} in U.fromDoubledInt34"
  let r ← U.fromWord { bitsLE := bits }
  assertR1C 0 0 (x - 2 • r.intVal)
  pure r

/-- Witness the 36-bit quotient of an even nonnegative integer by two. -/
def U.fromDoubledInt36 (x : LC ℤ) : Circuit (U 36) := do
  let bits ← hint h![x] fun h![(x : Int)] => match x with
    | .ofNat n => pure $ Vector.ofFn fun i => (n / 2).testBit i
    | _ => fail s!"negative integer {x} in U.fromDoubledInt36"
  let r ← U.fromWord { bitsLE := bits }
  assertR1C 0 0 (x - 2 • r.intVal)
  pure r

/-- Add ordinary 32-bit terms and terms already represented as twice their
unsigned value.  Keeping the whole expression doubled lets `CH` and `MAJ`
remain linear combinations; witnessing only the 35-bit quotient removes the
common factor without allocating the known-zero low bit or `CH`/`MAJ` bits. -/
def U.sumDoubled32 (us : Array (U 32)) (doubled : Array (LC ℤ)) : Circuit (U 32) := do
  let ordinary := us.map (·.intVal) |>.sum
  let total := 2 • ordinary + doubled.sum
  let half ← U.fromDoubledInt35 total
  pure $ half.takeLE 32 (by omega)

def U.sum5Doubled1 (a b c d e : U 32) (x2 : LC ℤ) : Circuit (U 32) :=
  U.sumDoubled32 #[a, b, c, d, e] #[x2]

def U.sum5Doubled2 (a b c d e : U 32) (x2 y2 : LC ℤ) : Circuit (U 32) :=
  U.sumDoubled32 #[a, b, c, d, e] #[x2, y2]

/-- Add eight 32-bit terms and one doubled term.  This is the terminal-round
shape after inlining a four-term SHA-256 schedule recurrence. -/
def U.sum8Doubled1 (a b c d e f g h : U 32) (x2 : LC ℤ) : Circuit (U 32) := do
  let ordinary := #[a, b, c, d, e, f, g, h].map (·.intVal) |>.sum
  let total := 2 • ordinary + x2
  let half ← U.fromDoubledInt36 total
  pure $ half.takeLE 32 (by omega)

/-- Sum nine 32-bit words and one doubled word, modulo `2^32`. -/
def U.sum9Doubled1 (a b c d e f g h i : U 32) (x2 : LC ℤ) : Circuit (U 32) := do
  let total := 2 • (#[a, b, c, d, e, f, g, h, i].map (·.intVal) |>.sum) + x2
  let half ← U.fromDoubledInt36 total
  pure $ half.takeLE 32 (by omega)

/-- Recover the new `a` from the already constrained new `e`.

For a SHA-256 round, `newE = d + T1 (mod 2^32)` and
`newA = T1 + S0 + Maj (mod 2^32)`.  Hence
`newA = newE + S0 + Maj - d (mod 2^32)`.  Adding `2^32` makes the
integer representative nonnegative; the doubled form keeps `Maj` as a linear
combination.  The representative is below `2^34`, so only 34 quotient bits
are needed. -/
def U.sumAFromE (d newE S0 : U 32) (maj2 : LC ℤ) : Circuit (U 32) := do
  let total := 2 • (newE.intVal + S0.intVal - d.intVal) + maj2 +
    LC.ofConst (2^33 : ℤ)
  let half ← U.fromDoubledInt34 total
  pure $ half.takeLE 32 (by omega)

/-- Fuse the final `a` feed-forward with the coupled round output.

`outA = outE + S0 + stateA - stateE + Maj - d (mod 2^32)`.
The `2^34` doubled offset makes the half-value nonnegative and below `2^35`. -/
def U.sumAFinal (d outE S0 stateA stateE : U 32)
    (maj2 : LC ℤ) : Circuit (U 32) := do
  let total := 2 • (outE.intVal + S0.intVal + stateA.intVal -
    stateE.intVal - d.intVal) + maj2 + LC.ofConst (2^34 : ℤ)
  let half ← U.fromDoubledInt35 total
  pure $ half.takeLE 32 (by omega)

abbrev RoundState (α : Type) :=
  MProd α (MProd α (MProd α (MProd α (MProd α (MProd α (MProd α α))))))

def scheduleStep (i : Nat) (w : Vector (U 32) 64) : Circuit (U 32) := do
  let wi15 := w[i - 15]!.bits
  let s0 ← U.fromWord $
    wi15.rotateRight 7 ^^^ wi15.rotateRight 18 ^^^ (wi15 >>> 3)
  let wi2 := w[i - 2]!.bits
  let s1 ← U.fromWord $
    wi2.rotateRight 17 ^^^ wi2.rotateRight 19 ^^^ (wi2 >>> 10)
  U.sumFixedAffineLow #v[w[i - 16]!, s0, w[i - 7]!, s1]

def roundStep (i : Nat) (hi : i ∈ [0:64])
    (x : Vector (U 32) 64 × RoundState (U 32)) : Circuit (RoundState (U 32)) := do
  let w := x.1
  let r := x.2
  let S1 ← U.fromWord $ r.2.2.2.2.1.bits.rotateRight 6 ^^^
    r.2.2.2.2.1.bits.rotateRight 11 ^^^ r.2.2.2.2.1.bits.rotateRight 25
  let ch2 ← U.ch2 r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1
  let S0 ← U.fromWord $ r.1.bits.rotateRight 2 ^^^
    r.1.bits.rotateRight 13 ^^^ r.1.bits.rotateRight 22
  let maj2 ← U.maj2 r.1 r.2.1 r.2.2.1
  let newE ← U.sum5Doubled1 r.2.2.2.1 r.2.2.2.2.2.2.2 S1 k[i] w[i] ch2
  let newA ← U.sumAFromE r.2.2.2.1 newE S0 maj2
  pure ⟨newA, r.1, r.2.1, r.2.2.1, newE,
    r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1⟩

/-- Materialize schedule word `i` and immediately consume it in round `i`. -/
def scheduleRoundStep (i : Nat) (hi : i ∈ [16:62])
    (x : RoundState (U 32) × Vector (U 32) 64) :
    Circuit (RoundState (U 32) × Vector (U 32) 64) := do
  let wi ← scheduleStep i x.2
  let w := x.2.set! i wi
  let r ← roundStep i (by
    change 16 ≤ i ∧ i < 62 ∧ (i - 16) % 1 = 0 at hi
    change 0 ≤ i ∧ i < 64 ∧ (i - 0) % 1 = 0
    exact ⟨by omega, by omega, Nat.mod_one _⟩) (w, x.1)
  pure (r, w)

def terminalScheduleParts (i : Nat) (w : Vector (U 32) 64) :
    Circuit (U 32 × U 32) := do
  let wi15 := w[i - 15]!.bits
  let s0 ← U.fromWord $
    wi15.rotateRight 7 ^^^ wi15.rotateRight 18 ^^^ (wi15 >>> 3)
  let wi2 := w[i - 2]!.bits
  let s1 ← U.fromWord $
    wi2.rotateRight 17 ^^^ wi2.rotateRight 19 ^^^ (wi2 >>> 10)
  pure (s0, s1)

def roundWithScheduleParts (i : Nat) (hi : i ∈ [16:64])
    (x : Vector (U 32) 64 × RoundState (U 32) × U 32 × U 32) :
    Circuit (RoundState (U 32)) := do
  let w := x.1
  let r := x.2.1
  let s0 := x.2.2.1
  let s1 := x.2.2.2
  let S1 ← U.fromWord $ r.2.2.2.2.1.bits.rotateRight 6 ^^^
    r.2.2.2.2.1.bits.rotateRight 11 ^^^ r.2.2.2.2.1.bits.rotateRight 25
  let ch2 ← U.ch2 r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1
  let S0 ← U.fromWord $ r.1.bits.rotateRight 2 ^^^
    r.1.bits.rotateRight 13 ^^^ r.1.bits.rotateRight 22
  let maj2 ← U.maj2 r.1 r.2.1 r.2.2.1
  let newE ← U.sum8Doubled1 r.2.2.2.1 r.2.2.2.2.2.2.2 S1 k[i]
    w[i - 16]! s0 w[i - 7]! s1 ch2
  let newA ← U.sumAFromE r.2.2.2.1 newE S0 maj2
  pure ⟨newA, r.1, r.2.1, r.2.2.1, newE,
    r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1⟩

/-- Compute a terminal schedule word only inside the round that consumes it. -/
def inlineScheduleRound (i : Nat) (hi : i ∈ [16:64])
    (x : Vector (U 32) 64 × RoundState (U 32)) : Circuit (RoundState (U 32)) := do
  let parts ← terminalScheduleParts i x.1
  roundWithScheduleParts i hi (x.1, x.2, parts.1, parts.2)

/-- Compute the four rotation and Boolean auxiliaries for the final round. -/
def finalRoundTransforms (r : RoundState (U 32)) :
    Circuit (U 32 × LC ℤ × U 32 × LC ℤ) := do
  let S1 ← U.fromWord $ r.2.2.2.2.1.bits.rotateRight 6 ^^^
    r.2.2.2.2.1.bits.rotateRight 11 ^^^ r.2.2.2.2.1.bits.rotateRight 25
  let ch2 ← U.ch2 r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1
  let S0 ← U.fromWord $ r.1.bits.rotateRight 2 ^^^
    r.1.bits.rotateRight 13 ^^^ r.1.bits.rotateRight 22
  let maj2 ← U.maj2 r.1 r.2.1 r.2.2.1
  pure (S1, ch2, S0, maj2)

/-- Compute the two fused final-round feed-forward sums. -/
def finalRoundSums (i : Nat) (hi : i ∈ [16:64])
    (x : Vector (U 32) 64 × RoundState (U 32) × Vector (U 32) 8 ×
      U 32 × U 32 × U 32 × LC ℤ × U 32 × LC ℤ) : Circuit (U 32 × U 32) := do
  let w := x.1
  let r := x.2.1
  let s := x.2.2.1
  let s0 := x.2.2.2.1
  let s1 := x.2.2.2.2.1
  let S1 := x.2.2.2.2.2.1
  let ch2 := x.2.2.2.2.2.2.1
  let S0 := x.2.2.2.2.2.2.2.1
  let maj2 := x.2.2.2.2.2.2.2.2
  let outE ← U.sum9Doubled1 r.2.2.2.1 r.2.2.2.2.2.2.2 S1 k[i]
    w[i - 16]! s0 w[i - 7]! s1 s[4] ch2
  let outA ← U.sumAFinal r.2.2.2.1 outE S0 s[0] s[4] maj2
  pure (outA, outE)

/-- Compute fused final-round outputs from precomputed terminal schedule parts. -/
def finalRoundBody (i : Nat) (hi : i ∈ [16:64])
    (x : Vector (U 32) 64 × RoundState (U 32) × Vector (U 32) 8 × U 32 × U 32) :
    Circuit (U 32 × U 32) := do
  let t ← finalRoundTransforms x.2.1
  finalRoundSums i hi (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2,
    t.1, t.2.1, t.2.2.1, t.2.2.2)

/-- Compute the two final-round words whose feed-forward can be fused. -/
def finalRoundCore (i : Nat) (hi : i ∈ [16:64])
    (x : Vector (U 32) 64 × RoundState (U 32) × Vector (U 32) 8) :
    Circuit (U 32 × U 32) := do
  let parts ← terminalScheduleParts i x.1
  finalRoundBody i hi (x.1, x.2.1, x.2.2, parts.1, parts.2)

/-- Assemble the fused pair and the six unchanged feed-forward sums. -/
def finalRoundTail
    (x : (U 32 × U 32) × RoundState (U 32) × Vector (U 32) 8) :
    Circuit (Vector (U 32) 8) := do
  let out := x.1
  let r := x.2.1
  let s := x.2.2
  pure #v[out.1, ←U.sumFixedAffineLow #v[s[1], r.1],
    ←U.sumFixedAffineLow #v[s[2], r.2.1],
    ←U.sumFixedAffineLow #v[s[3], r.2.2.1], out.2,
    ←U.sumFixedAffineLow #v[s[5], r.2.2.2.2.1],
    ←U.sumFixedAffineLow #v[s[6], r.2.2.2.2.2.1],
    ←U.sumFixedAffineLow #v[s[7], r.2.2.2.2.2.2.1]]

/-- Fuse the terminal round with the two feed-forward words it produces. -/
def finalRound (i : Nat) (hi : i ∈ [16:64])
    (x : Vector (U 32) 64 × RoundState (U 32) × Vector (U 32) 8) :
    Circuit (Vector (U 32) 8) := do
  let out ← finalRoundCore i hi x
  finalRoundTail (out, x.2.1, x.2.2)

def finish (x : Vector (U 32) 8 × RoundState (U 32)) :
    Circuit (Vector (U 32) 8) := do
  let s := x.1
  let r := x.2
  pure #v[
    ←U.sum #[s[0], r.1], ←U.sum #[s[1], r.2.1],
    ←U.sum #[s[2], r.2.2.1], ←U.sum #[s[3], r.2.2.2.1],
    ←U.sum #[s[4], r.2.2.2.2.1], ←U.sum #[s[5], r.2.2.2.2.2.1],
    ←U.sum #[s[6], r.2.2.2.2.2.2.1], ←U.sum #[s[7], r.2.2.2.2.2.2.2]]

/-- Run the two terminal rounds without materializing either terminal schedule word. -/
def terminalRounds
    (x : Vector (U 32) 64 × RoundState (U 32) × Vector (U 32) 8) :
    Circuit (Vector (U 32) 8) := do
  let r ← inlineScheduleRound 62 (by
    change 16 ≤ 62 ∧ 62 < 64 ∧ (62 - 16) % 1 = 0
    norm_num) (x.1, x.2.1)
  finalRound 63 (by
    change 16 ≤ 63 ∧ 63 < 64 ∧ (63 - 16) % 1 = 0
    norm_num) (x.1, r, x.2.2)

/-- Build the schedule through word 61 while executing rounds 0 through 61.

Rounds 0 through 15 consume the message words directly.  Thereafter each
schedule word is materialized immediately before the round that first consumes
it, keeping the schedule and round witnesses in one optimization scope. -/
def permPrefix (m : Vector (Word 32) 16) (su : Vector (U 32) 8) :
    Circuit (Vector (U 32) 64 × RoundState (U 32) × Vector (U 32) 8) := do
  let mut w : Vector (U 32) 64 := default
  for h:i in [0:16] do
    w := w.set! i $ ←U.fromWord m[i]
  let mut r : RoundState (U 32) :=
    ⟨su[0], su[1], su[2], su[3], su[4], su[5], su[6], su[7]⟩
  for hi:i in [0:16] do
    r ← roundStep i (by
      change 0 ≤ i ∧ i < 64 ∧ (i - 0) % 1 = 0
      have hil : i < 16 := by simpa using hi.upper
      exact ⟨by omega, lt_trans hil (by omega), Nat.mod_one _⟩) (w, r)
  let mut rw := (r, w)
  for hi:i in [16:62] do
    rw ← scheduleRoundStep i hi rw
  pure (rw.2, rw.1, su)

def permCircuit (m : Vector (Word 32) 16)
    (s : Vector (Word 32) 8) :
    Circuit (Vector (U 32) 8) := do
  let su ← s.mapM U.fromWord
  let wr ← permPrefix m su
  terminalRounds wr

def permCirc' (inp : Vector (LC Bool) 768): Circuit (Vector (LC Bool) 256) := do
  let m := Vector.ofFn fun wi => Word.mk $ Vector.ofFn fun bi => inp[wi.val * 32 + bi.val]
  let s := Vector.ofFn fun si => Word.mk $ Vector.ofFn fun bi => inp[512 + si.val * 32 + bi.val]
  let out ← permCircuit m s
  pure $ Vector.ofFn fun si => out[si.val / 32].bits.bitsLE[si.val % 32]

abbrev sha256CS : Vector (LC Bool) 256 × Semantics.CS := Semantics.CSBuilder.runWithInputs permCirc'

end Circuit

end Freigen.F2Z.Examples
