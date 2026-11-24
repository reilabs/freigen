import Freigen.Circuit.Defs

import Mathlib.Data.ZMod.Basic

namespace Freigen.Circuit.Examples.Sha256

def P := 21888242871839275222246405745257275088548364400416034343698204186575808495617
axiom p_prime : Fact P.Prime
instance : Fact P.Prime := p_prime
abbrev F := ZMod P

variable [ctx : Circuit.Context P]
private abbrev W := ctx.W

def K: Vector UInt32 64 := #v[
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
]

private def pow2Nat (n : Nat) : Nat := 2 ^ n

private def pow2 (n : Nat) : F := (pow2Nat n : F)

private def spreadNat (n x : Nat) : Nat :=
  (List.range n).foldl
    (fun acc i => if x.testBit i then acc + pow2Nat (2 * i) else acc) 0

private def unspreadNat (parity n x : Nat) : Nat :=
  (List.range n).foldl
    (fun acc i =>
      if x.testBit (2 * i + parity) then acc + pow2Nat i else acc) 0

private def fieldSpread (n : Nat) (x : F) : F :=
  (spreadNat n x.val : F)

private def fieldUnspread (parity n : Nat) (x : F) : F :=
  (unspreadNat parity n x.val : F)

private def assertEq (x y : W) : Circuit P (Cert $ fun ρ => ρ x = ρ y) := do
  let cert ← Circuit.assertR1C 1 x y
  pure $ cert.map fun ρ h => by
    simp only [R1CSAssertion, ρ.one_map, one_mul] at h
    exact h

private def spread (n : Nat) (x : W) : Circuit P W := do
  let y ← Circuit.hint 1 #v[x] fun inputs =>
    Circuit.writeWitness (fieldSpread n inputs[0])
  let _ ← Circuit.assertSpread n x y
  pure y

private def unspread (n : Nat) (x : W) : Circuit P (W × W) := do
  let ys ← Circuit.hint 1 #v[x] fun inputs => do
    let high ← Circuit.writeWitness (fieldUnspread 1 n inputs[0])
    let low ← Circuit.writeWitness (fieldUnspread 0 n inputs[0])
    pure (high, low)
  let highSpread ← spread n ys.1
  let lowSpread ← spread n ys.2
  _ ← assertEq x (lowSpread + (2 : F) • highSpread)
  pure ys

private structure Chunks4 where
  s0 : W
  s1 : W
  s2 : W
  s3 : W

private def splitAndSpread4
    (a b c d : Nat) (_width : a + b + c + d = 32)
    (x : W) : Circuit P Chunks4 := do
  let chunks ← Circuit.hint 1 #v[x] fun inputs => do
    let value := inputs[0].val
    let a0 : F := (value / pow2Nat (b + c + d) % pow2Nat a : F)
    let a1 : F := (value / pow2Nat (c + d) % pow2Nat b : F)
    let a2 : F := (value / pow2Nat d % pow2Nat c : F)
    let w0 ← Circuit.writeWitness a0
    let w1 ← Circuit.writeWitness a1
    let w2 ← Circuit.writeWitness a2
    pure (w0, w1, w2)
  let a3 :=
    x -
      (pow2 (b + c + d)) • chunks.1 -
      (pow2 (c + d)) • chunks.2.1 -
      (pow2 d) • chunks.2.2
  let s0 ← spread a chunks.1
  let s1 ← spread b chunks.2.1
  let s2 ← spread c chunks.2.2
  let s3 ← spread d a3
  pure ⟨s0, s1, s2, s3⟩

private def unspread64 (x : W) : Circuit P (W × W) := do
  let limbs ← Circuit.hint 1 #v[x] fun inputs => do
    let value := inputs[0].val
    let mask := pow2Nat 22 - 1
    let a0 ← Circuit.writeWitness (((value / pow2Nat 42) &&& mask : Nat) : F)
    let a1 ← Circuit.writeWitness (((value / pow2Nat 20) &&& mask : Nat) : F)
    pure (a0, a1)
  let a2 := x - (pow2 42) • limbs.1 - (pow2 20) • limbs.2
  let a0 ← unspread 11 limbs.1
  let a1 ← unspread 11 limbs.2
  let a2 ← unspread 10 a2
  pure
    (a2.1 + (pow2 10) • a1.1 + (pow2 21) • a0.1,
     a2.2 + (pow2 10) • a1.2 + (pow2 21) • a0.2)

private def unsafeWrappingAdd {n : Nat}
    (xs : Vector W n) : Circuit P W := do
  let sum := xs.toList.foldl (· + ·) 0
  let result ← Circuit.hint n xs fun inputs =>
    Circuit.writeWitness
      (((inputs.toList.foldl (· + ·) 0).val % pow2Nat 32 : Nat) : F)
  let carry := (pow2 32)⁻¹ • (sum - result)
  let _ ← Circuit.rangeCheck 8 carry
  pure result

private def wrappingAdd {n : Nat}
    (xs : Vector W n) : Circuit P W := do
  let result ← unsafeWrappingAdd xs
  let _ ← Circuit.rangeCheck 32 result
  pure result

private structure Sigma0Word (W : Type) where
  packed : W
  s0 : W
  s1 : W
  s2 : W
  s3 : W

namespace Sigma0Word

def new (x : W) : Circuit P (Sigma0Word W) := do
  let chunks ← splitAndSpread4 10 9 11 2 (by decide) x
  pure ⟨x, chunks.s0, chunks.s1, chunks.s2, chunks.s3⟩

def spreadValue (x : Sigma0Word W) : W :=
  x.s3 + (1 <<< 4) • x.s2 + (1 <<< 26) • x.s1 + (pow2 44) • x.s0

def bigSigma (x : Sigma0Word W) : Circuit P W := do
  let arr2 :=
    x.s2 + (pow2 22) • x.s1 + (pow2 40) • x.s0 + (pow2 60) • x.s3
  let arr13 :=
    x.s1 + (pow2 18) • x.s0 + (pow2 38) • x.s3 + (pow2 42) • x.s2
  let arr22 :=
    x.s0 + (pow2 20) • x.s3 + (pow2 24) • x.s2 + (pow2 46) • x.s1
  let result ← unspread64 (arr2 + arr13 + arr22)
  pure result.2

def maj (a b c : Sigma0Word W) : Circuit P W := do
  let result ←
    unspread64 (a.spreadValue + b.spreadValue + c.spreadValue)
  pure result.1

def wrappingAdd {n : Nat}
    (xs : Vector W n) : Circuit P (Sigma0Word W) := do
  let result ← unsafeWrappingAdd xs
  new result

end Sigma0Word

private structure Sigma1Word (W : Type) where
  packed : W
  s0 : W
  s1 : W
  s2 : W
  s3 : W

namespace Sigma1Word

def new (x : W) : Circuit P (Sigma1Word W) := do
  let chunks ← splitAndSpread4 7 14 5 6 (by decide) x
  pure ⟨x, chunks.s0, chunks.s1, chunks.s2, chunks.s3⟩

def spreadValue (x : Sigma1Word W) : W :=
  x.s3 + (pow2 12) • x.s2 + (pow2 22) • x.s1 + (pow2 50) • x.s0

def bigSigma (x : Sigma1Word W) : Circuit P W := do
  let err6 :=
    x.s2 + (pow2 10) • x.s1 + (pow2 38) • x.s0 + (pow2 52) • x.s3
  let err11 :=
    x.s1 + (pow2 28) • x.s0 + (pow2 42) • x.s3 + (pow2 54) • x.s2
  let err25 :=
    x.s0 + (pow2 14) • x.s3 + (pow2 26) • x.s2 + (pow2 36) • x.s1
  let result ← unspread64 (err6 + err11 + err25)
  pure result.2

def ch (e f g : Sigma1Word W) : Circuit P W := do
  let eAndF ← unspread64 (e.spreadValue + f.spreadValue)
  let eAndG ← unspread64 (e.spreadValue + g.spreadValue)
  pure (eAndF.1 + g.packed - eAndG.1)

def wrappingAdd {n : Nat}
    (xs : Vector W n) : Circuit P (Sigma1Word W) := do
  let result ← unsafeWrappingAdd xs
  new result

end Sigma1Word

private def smallSigma0 (x : W) : Circuit P W := do
  let s ← splitAndSpread4 14 11 4 3 (by decide) x
  let rr7 := s.s1 + (pow2 22) • s.s0 + (pow2 50) • s.s3 + (pow2 56) • s.s2
  let rr18 := s.s0 + (pow2 28) • s.s3 + (pow2 34) • s.s2 + (pow2 42) • s.s1
  let rs3 := s.s2 + (pow2 8) • s.s1 + (pow2 30) • s.s0
  let result ← unspread64 (rr7 + rr18 + rs3)
  pure result.2

private def smallSigma1 (x : W) : Circuit P W := do
  let s ← splitAndSpread4 13 2 7 10 (by decide) x
  let rr17 := s.s1 + (pow2 4) • s.s0 + (pow2 30) • s.s3 + (pow2 50) • s.s2
  let rr19 := s.s0 + (pow2 26) • s.s3 + (pow2 46) • s.s2 + (pow2 60) • s.s1
  let rs10 := s.s2 + (pow2 14) • s.s1 + (pow2 18) • s.s0
  let result ← unspread64 (rr17 + rr19 + rs10)
  pure result.2

def sha256Compression
    (msgBlock : Vector W 16) (state : Vector W 8) :
    Circuit P (Vector W 8) := do
  for x in msgBlock do
    let _ ← Circuit.rangeCheck 32 x
    pure ()
  for x in state do
    let _ ← Circuit.rangeCheck 32 x
    pure ()

  let mut w := msgBlock ++ Vector.replicate 48 (0 : W)
  for h:i in [16:64] do
    let s1 ← smallSigma1 (w[i - 2]'(by grind [h.2.1]))
    let s0 ← smallSigma0 (w.getD (i - 15) 0)
    let wi ← wrappingAdd #v[s1, w.getD (i - 7) 0, s0, w.getD (i - 16) 0]
    w := w.set! i wi

  let mut a ← Sigma0Word.new state[0]
  let mut b ← Sigma0Word.new state[1]
  let mut c ← Sigma0Word.new state[2]
  let mut d := state[3]
  let mut e ← Sigma1Word.new state[4]
  let mut f ← Sigma1Word.new state[5]
  let mut g ← Sigma1Word.new state[6]
  let mut h := state[7]

  for i in [0:64] do
    let bs1 ← e.bigSigma
    let choice ← Sigma1Word.ch e f g
    let bs0 ← a.bigSigma
    let majority ← Sigma0Word.maj a b c
    let ki := ((K[i]!.toNat : Nat) : F) • 1
    let wi := w.getD i 0
    let newE ← Sigma1Word.wrappingAdd #v[d, h, bs1, choice, ki, wi]
    let newA ← Sigma0Word.wrappingAdd #v[h, bs1, choice, ki, wi, bs0, majority]
    h := g.packed
    g := f
    f := e
    e := newE
    d := c.packed
    c := b
    b := a
    a := newA

  let r0 ← wrappingAdd #v[state[0], a.packed]
  let r1 ← wrappingAdd #v[state[1], b.packed]
  let r2 ← wrappingAdd #v[state[2], c.packed]
  let r3 ← wrappingAdd #v[state[3], d]
  let r4 ← wrappingAdd #v[state[4], e.packed]
  let r5 ← wrappingAdd #v[state[5], f.packed]
  let r6 ← wrappingAdd #v[state[6], g.packed]
  let r7 ← wrappingAdd #v[state[7], h]
  pure #v[r0, r1, r2, r3, r4, r5, r6, r7]



end Freigen.Circuit.Examples.Sha256
