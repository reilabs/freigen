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

variable [ctx : Context]

/-- Bit-producing reference gadget retained for its standalone specification.
The SHA-256 round circuit uses `ch2` below and does not call this gadget. -/
def U.ch (u v w : U n) : Circuit (U n) := do
  let chBits ← Vector.ofFnM (n:=n) fun i => do
    let h ← hint (argTps := [.f₂, .f₂, .f₂])
      h![u.bits[i], v.bits[i], w.bits[i]] fun h![u, v, w] =>
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
    let h ← hint (argTps := [.f₂, .f₂, .f₂])
      h![u.bits[i], v.bits[i], w.bits[i]] fun h![u, v, w] =>
      pure $ #v[(u && v) ^^ (u && w) ^^ (v && w)]
    pure h[0]
  let maj ← U.fromWord { bitsLE := majBits }
  let uvw ← U.fromWord $ u.bits ^^^ v.bits ^^^ w.bits
  assertR1C 0 0 $ u.intVal + v.intVal + w.intVal - uvw.intVal - 2 • maj.intVal
  pure maj

def U.ch2 (u v w : U n) : Circuit ctx.Wℤ := do
  let uv ← U.fromWord $ u.bits ^^^ v.bits
  let uw ← U.fromWord $ u.bits ^^^ w.bits
  pure $ v.intVal + w.intVal - uv.intVal + uw.intVal

def U.maj2 (u v w : U n) : Circuit ctx.Wℤ := do
  let uvw ← U.fromWord $ u.bits ^^^ v.bits ^^^ w.bits
  pure $ u.intVal + v.intVal + w.intVal - uvw.intVal

/-- Witness the 35-bit quotient of an even nonnegative integer by two.  The
constraint proves the shift without allocating the known-zero low input bit. -/
def U.fromDoubledInt35 (x : ctx.Wℤ) : Circuit (U 35) := do
  let bits ← hint (argTps := [.z]) h![x] fun h![(x : Int)] => match x with
    | .ofNat n => pure $ Vector.ofFn fun i => (n / 2).testBit i
    | _ => fail s!"negative integer {x} in U.fromDoubledInt35"
  let r ← U.fromWord { bitsLE := bits }
  assertR1C 0 0 (x - 2 • r.intVal)
  pure r

/-- Add ordinary 32-bit terms and terms already represented as twice their
unsigned value.  Keeping the whole expression doubled lets `CH` and `MAJ`
remain linear combinations; witnessing only the 35-bit quotient removes the
common factor without allocating the known-zero low bit or `CH`/`MAJ` bits. -/
def U.sumDoubled32 (us : Array (U 32)) (doubled : Array ctx.Wℤ) : Circuit (U 32) := do
  let ordinary := us.map (·.intVal) |>.sum
  let total := 2 • ordinary + doubled.sum
  let half ← U.fromDoubledInt35 total
  pure $ half.takeLE 32 (by omega)

def U.sum5Doubled1 (a b c d e : U 32) (x2 : ctx.Wℤ) : Circuit (U 32) :=
  U.sumDoubled32 #[a, b, c, d, e] #[x2]

def U.sum5Doubled2 (a b c d e : U 32) (x2 y2 : ctx.Wℤ) : Circuit (U 32) :=
  U.sumDoubled32 #[a, b, c, d, e] #[x2, y2]

def permCircuit (m : Vector (Word 32) 16)
    (s : Vector (Word 32) 8) :
    Circuit (Vector (U 32) 8) := do
  let s ← s.mapM U.fromWord
  let mut w : Vector (U 32) 64 := default
  for h:i in [0:16] do
    w := w.set! i $ ←U.fromWord m[i]
  for i in [16:64] do
    let wi15 := w[i-15]!.bits
    let s0 ← U.fromWord $ wi15.rotateRight 7 ^^^ wi15.rotateRight 18 ^^^ (wi15 >>> 3)
    let wi2 := w[i-2]!.bits
    let s1 ← U.fromWord $ wi2.rotateRight 17 ^^^ wi2.rotateRight 19 ^^^ (wi2 >>> 10)
    w := w.set! i $ ←U.sum #[w[i-16]!, s0, w[i-7]!, s1]

  let mut a := s[0]
  let mut b := s[1]
  let mut c := s[2]
  let mut d := s[3]
  let mut e := s[4]
  let mut f := s[5]
  let mut g := s[6]
  let mut h := s[7]

  for hi:i in [0:64] do
    let S1 ← U.fromWord $ e.bits.rotateRight 6 ^^^ e.bits.rotateRight 11 ^^^ e.bits.rotateRight 25
    let ch2 ← U.ch2 e f g
    let S0 ← U.fromWord $ a.bits.rotateRight 2 ^^^ a.bits.rotateRight 13 ^^^ a.bits.rotateRight 22
    let maj2 ← U.maj2 a b c

    let oldH := h

    h := g
    g := f
    f := e
    e ← U.sum5Doubled1 d oldH S1 k[i] w[i] ch2
    d := c
    c := b
    b := a
    a ← U.sum5Doubled2 oldH S1 k[i] w[i] S0 ch2 maj2

  pure $ #v[
    ←U.sum #[s[0], a],
    ←U.sum #[s[1], b],
    ←U.sum #[s[2], c],
    ←U.sum #[s[3], d],
    ←U.sum #[s[4], e],
    ←U.sum #[s[5], f],
    ←U.sum #[s[6], g],
    ←U.sum #[s[7], h]
  ]

def permCirc' (inp : Vector ctx.WBool 768): Circuit (Vector ctx.WBool 256) := do
  let m := Vector.ofFn fun wi => Word.mk $ Vector.ofFn fun bi => inp[wi.val * 32 + bi.val]
  let s := Vector.ofFn fun si => Word.mk $ Vector.ofFn fun bi => inp[512 + si.val * 32 + bi.val]
  let out ← permCircuit m s
  pure $ Vector.ofFn fun si => out[si.val / 32].bits.bitsLE[si.val % 32]

abbrev sha256CS : Vector (LC Bool) 256 × Semantics.CS :=
  Semantics.CSBuilder.runWithInputs (@permCirc' lcContext)

end Circuit

end Freigen.F2Z.Examples
