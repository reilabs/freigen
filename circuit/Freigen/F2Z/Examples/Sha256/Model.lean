import Freigen.F2Z.Examples.Sha256.Impl

namespace Freigen.F2Z.Examples

def perm (m : Vector (BitVec 32) 16)
    (s : Vector (BitVec 32) 8) : Vector (BitVec 32) 8 := Id.run $ do
  let mut w := Vector.replicate 64 (0 : BitVec 32)
  for h:i in [0:16] do
    w := w.set! i m[i]
  for i in [16:64] do
    let s0 := (w[i-15]!.rotateRight 7) ^^^
      (w[i-15]!.rotateRight 18) ^^^ (w[i-15]! >>> 3)
    let s1 := (w[i-2]!.rotateRight 17) ^^^
      (w[i-2]!.rotateRight 19) ^^^ (w[i-2]! >>> 10)
    w := w.set! i (w[i-16]! + s0 + w[i-7]! + s1)
  let mut a := s[0]
  let mut b := s[1]
  let mut c := s[2]
  let mut d := s[3]
  let mut e := s[4]
  let mut f := s[5]
  let mut g := s[6]
  let mut h := s[7]

  for h:i in [0:64] do
    let S1 := (e.rotateRight 6) ^^^ (e.rotateRight 11) ^^^
      (e.rotateRight 25)
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let temp1 := h + S1 + ch + k[i] + w[i]
    let S0 := (a.rotateRight 2) ^^^ (a.rotateRight 13) ^^^
      (a.rotateRight 22)
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let temp2 := S0 + maj

    h := g
    g := f
    f := e
    e := d + temp1
    d := c
    c := b
    b := a
    a := temp1 + temp2

  #v[s[0] + a, s[1] + b, s[2] + c, s[3] + d,
    s[4] + e, s[5] + f, s[6] + g, s[7] + h]

def perm' (input : Vector Bool 768) : Vector Bool 256 :=
  let m := Vector.ofFn fun i => BitVec.ofNat 32 $
    Nat.ofBits fun (j : Fin 32) => input[i.val * 32 + j.val]
  let s := Vector.ofFn fun i => BitVec.ofNat 32 $
    Nat.ofBits fun (j : Fin 32) => input[512 + i.val * 32 + j.val]
  let out := perm m s
  Vector.ofFn fun i => out[i.val / 32].toNat.testBit (i % 32)

end Freigen.F2Z.Examples
