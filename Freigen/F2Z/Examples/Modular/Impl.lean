import Freigen.F2Z.Correctness.U

/-!
# Bounded modular arithmetic gadget implementations

An `Elem p` is a `U p.bits`, hence it has a Boolean little-endian
decomposition and an integer linear combination for the same value. The
additional invariant says that the value is strictly below `p.modulus`.

Over the integer constraint semantics, `mul` uses the single R1C equation

`x * y = r + p.modulus * q`.

Both `r` and `q` are range checked by bit decomposition, and `r < modulus` is
proved with a bounded slack. There are therefore no limb carries to constrain.
This encoding needs an additional no-wrap argument before being reused in an
R1CS interpreted over a small finite field.

The soundness, completeness, and well-formedness results are provided by
`Freigen.F2Z.Examples.Modular`.
-/

namespace Freigen.F2Z.Examples.Modular

open Std.Do
open scoped Std.Do

/-- Parameters needed by the generic `n`-bit reduction gadget.  The
lower-half condition makes the quotient of two canonical inputs fit in `n`
bits. -/
structure Params (n : Nat) where
  modulus : Nat
  bitsPositive : 0 < n
  positive : 0 < modulus
  fits : modulus ≤ 2 ^ n
  lowerHalf : 2 ^ (n - 1) ≤ modulus

variable {n : Nat} (p : Params n)
variable [ctx : Context]

structure Elem (p : Params n) where
  val : U n

namespace Elem

def Valid {p : Params n} (x : Elem p) (ρ : WF.Valuation) : Prop :=
  x.val.Valid ρ ∧ ρ.int x.val.intVal < p.modulus

def evalNat {p : Params n} (x : Elem p) (ρ : WF.Valuation) : Nat :=
  (ρ.int x.val.intVal).toNat

def WFRel {p : Params n} {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx)
    (l : @Elem n leftCtx p) (r : @Elem n rightCtx p) : Prop :=
  U.WFRel (leftCtx := leftCtx) (rightCtx := rightCtx) lv rv
    (@Elem.val n leftCtx p l) (@Elem.val n rightCtx p r)

end Elem

/-- Prove `x < bound` by decomposing the nonnegative slack
`bound - 1 - x`. -/
def assertLt (bound : Nat) (x : U n) : Circuit Unit := do
  let _ ← U.fromInt n (ofScalar ((bound : Int) - 1) - x.intVal)
  pure ()

/-- Turn an already bit-decomposed integer into a canonical modular element. -/
def ofU (x : U n) : Circuit (Elem p) := do
  assertLt p.modulus x
  pure ⟨x⟩

/-- Constant canonical element. -/
def ofNat (x : Nat) (hfit : x < 2 ^ n) (hlt : x < p.modulus) : Elem p :=
  ⟨BitVec.ofNat n x⟩

/-- Assert equality of two canonical representatives. -/
def assertEq (x y : Elem p) : Circuit Unit := do
  assertR1C 0 0 (x.val.intVal - y.val.intVal)

/-! ## Relaxed fixed-modulus arithmetic

These gadgets keep internal representatives as `n`-bit values and constrain
only their residue modulo the fixed `p.modulus`.  The witness generator emits
the canonical remainder, but soundness does not rely on that choice: another
satisfying witness may use the other `n`-bit representative of the same
residue.  Canonicality is checked only at public boundaries.
-/

namespace Relaxed

/-- Fixed-modulus reduction with an `n+2`-bit quotient.  This is sufficient
for products of two `n`-bit representatives when `p` occupies the upper half
of the `n`-bit range.  The modular relation itself is one R1C. -/
def mul (x y : Elem p) : Circuit (Elem p) := do
  let bits ← hint (argTps := [.z, .z]) h![x.val.intVal, y.val.intVal]
    fun h![(a : Int), (b : Int)] =>
      if ha : 0 ≤ a then
        if hb : 0 ≤ b then
          let value := a.toNat * b.toNat
          let r := value % p.modulus
          let q := value / p.modulus
          pure $ Vector.ofFn (n := 2 * n + 2) fun i =>
            if hi : i.val < n then r.testBit i.val
            else q.testBit (i.val - n)
        else fail s!"negative factor {b} in relaxed modular multiplication"
      else fail s!"negative factor {a} in relaxed modular multiplication"
  let r ← U.fromWord {
    bitsLE := Vector.ofFn (n := n) fun i => bits[i.val]'(by omega) }
  let q ← U.fromWord {
    bitsLE := Vector.ofFn (n := n + 2) fun i =>
      bits[n + i.val]'(by omega) }
  assertR1C x.val.intVal y.val.intVal
    (r.intVal + p.modulus • q.intVal)
  pure ⟨r⟩

/-- Reduce a nonnegative value known to be below `4*p`.  Addition and the
biased subtraction below therefore need only a two-bit quotient. -/
def reduceSmall (x : ctx.Wℤ) : Circuit (Elem p) := do
  let bits ← hint (argTps := [.z]) h![x] fun h![(a : Int)] =>
    if ha : 0 ≤ a then
      let value := a.toNat
      let r := value % p.modulus
      let q := value / p.modulus
      pure $ Vector.ofFn (n := n + 2) fun i =>
        if hi : i.val < n then r.testBit i.val
        else q.testBit (i.val - n)
    else fail s!"negative relaxed modular dividend {a}"
  let r ← U.fromWord {
    bitsLE := Vector.ofFn fun i => bits[i.val]'(by omega) }
  let q ← U.fromWord {
    bitsLE := Vector.ofFn (n := 2) fun i => bits[n + i.val]'(by omega) }
  assertR1C 0 0 (x - (r.intVal + p.modulus • q.intVal))
  pure ⟨r⟩

end Relaxed

/-! ## Lazy linear representatives

`Lazy.Rep` is only a circuit-construction abstraction: its value is an
ordinary existing `LC ℤ`.  It does not extend F2Z with another kind of
witness.  The `bound` records a conservative multiple of the modulus used to
keep subtraction nonnegative and to size quotient witnesses.

Linear field operations deliberately do not reduce.  A fresh bit-decomposed
representative is allocated only when a nonlinear product must be reused.
-/

namespace Lazy

structure Rep (p : Params n) where
  intVal : ctx.Wℤ
  /-- Static construction-time bound: `0 ≤ intVal < bound * modulus`. -/
  bound : Nat

/-- Quotient-backend equality: representatives have the same static slack
bound and evaluate to the same integer under every pair of valuations supplied
by `WF.GadgetSpec`. -/
def Rep.WFRel {p : Params n} {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx)
    (left : @Rep n leftCtx p) (right : @Rep n rightCtx p) : Prop :=
  (@Rep.bound n leftCtx p left) = (@Rep.bound n rightCtx p right) ∧
    WF.LCEq lv.int rv.int (@Rep.intVal n leftCtx p left)
      (@Rep.intVal n rightCtx p right)

/-- Semantic invariant justified by the construction-time bound. It is used
only by completeness proofs to show that the concrete hint programs cannot
fail and that their quotient words are wide enough. -/
def Rep.Valid {p : Params n} {ctx : Context} (x : @Rep n ctx p)
    (rho : @WF.Valuation ctx) : Prop :=
  0 ≤ rho.int x.intVal ∧
    rho.int x.intVal < x.bound * p.modulus

/-- Field/ring semantics of a lazy representative.  All construction-time
slack and quotient choices disappear under this map. -/
def evalZMod (x : Rep p) (ρ : WF.Valuation) : ZMod p.modulus :=
  Int.castRingHom (ZMod p.modulus) (ρ.int x.intVal)

def evalElemZMod (x : Elem p) (ρ : WF.Valuation) : ZMod p.modulus :=
  Int.castRingHom (ZMod p.modulus) (ρ.int x.val.intVal)

def MulZModSpec (ρ : WF.Valuation) (x y out : Rep p) : Prop :=
  evalZMod p out ρ = evalZMod p x ρ * evalZMod p y ρ

def MulSubToElemZModSpec (ρ : WF.Valuation)
    (x y target : Rep p) (out : Elem p) : Prop :=
  evalElemZMod p out ρ =
    evalZMod p x ρ * evalZMod p y ρ - evalZMod p target ρ

def DivideZModSpec (ρ : WF.Valuation)
    (denominator numerator out : Rep p) : Prop :=
  evalZMod p out ρ * evalZMod p denominator ρ = evalZMod p numerator ρ

def AssertMulEqZModSpec (ρ : WF.Valuation)
    (x y target : Rep p) : Prop :=
  evalZMod p x ρ * evalZMod p y ρ = evalZMod p target ρ

def ZeroTestZModSpec (ρ : WF.Valuation) (x : Rep p) (z : ctx.Wℤ) : Prop :=
  (ρ.int z = 0 ∨ ρ.int z = 1) ∧
    (ρ.int z = 1 ↔ evalZMod p x ρ = 0) ∧
    ρ.int z = if evalZMod p x ρ = 0 then 1 else 0

def ofElem (x : Elem p) : Rep p :=
  ⟨x.val.intVal, 2⟩

def add (x y : Rep p) : Rep p :=
  ⟨x.intVal + y.intVal, x.bound + y.bound⟩

/-- Biased subtraction.  The added multiple of `p` is linear and makes the
representative nonnegative under the recorded construction-time bounds. -/
def sub (x y : Rep p) : Rep p :=
  ⟨x.intVal + ofScalar (y.bound * p.modulus : Int) - y.intVal,
    x.bound + y.bound⟩

def scale (k : Nat) (x : Rep p) : Rep p :=
  ⟨k • x.intVal, k * x.bound⟩

/-- Extra quotient bits cover the small static bounds generated by the P-256
formulas.  This remains far below a limb implementation while keeping the
gadget shape independent of values. -/
def quotientExtraBits : Nat := 9

/-- Multiply two lazy representatives and materialize only the result and
quotient.  Addition/subtraction surrounding this operation stays in the
linear expressions supplied as its operands. -/
def mul (x y : Rep p) : Circuit (Rep p) := do
  let bits ← hint (argTps := [.z, .z]) h![x.intVal, y.intVal]
    fun h![(a : Int), (b : Int)] =>
      if ha : 0 ≤ a then
        if hb : 0 ≤ b then
          let value := a.toNat * b.toNat
          let r := value % p.modulus
          let q := value / p.modulus
          pure $ Vector.ofFn (n := 2 * n + quotientExtraBits) fun i =>
            if hi : i.val < n then r.testBit i.val
            else q.testBit (i.val - n)
        else fail s!"negative lazy multiplication operand {b}"
      else fail s!"negative lazy multiplication operand {a}"
  let r ← U.fromWord {
    bitsLE := Vector.ofFn (n := n) fun i => bits[i.val]'(by omega) }
  let q ← U.fromWord {
    bitsLE := Vector.ofFn (n := n + quotientExtraBits) fun i =>
      bits[n + i.val]'(by omega) }
  assertR1C x.intVal y.intVal
    (r.intVal + p.modulus • q.intVal)
  pure ⟨r.intVal, 2⟩

/-- Materialize `x*y - target (mod p)` directly.  This is the affine-slope
form of a multiplication: the output word and quotient share the one R1C,
so no intermediate product residue is committed. -/
def mulSubToElem (x y target : Rep p) : Circuit (Elem p) := do
  let bias := target.bound * p.modulus
  let bits ← hint (argTps := [.z, .z, .z])
    h![x.intVal, y.intVal, target.intVal]
    fun h![(a : Int), (b : Int), (c : Int)] =>
      let shifted := a * b + bias - c
      if hs : 0 ≤ shifted then
        let value := shifted.toNat
        let r := value % p.modulus
        let q := value / p.modulus
        pure $ Vector.ofFn (n := 2 * n + quotientExtraBits) fun i =>
          if hi : i.val < n then r.testBit i.val
          else q.testBit (i.val - n)
      else fail s!"negative affine product dividend {shifted}"
  let r ← U.fromWord {
    bitsLE := Vector.ofFn (n := n) fun i => bits[i.val]'(by omega) }
  let q ← U.fromWord {
    bitsLE := Vector.ofFn (n := n + quotientExtraBits) fun i =>
      bits[n + i.val]'(by omega) }
  assertR1C x.intVal y.intVal
    (r.intVal + target.intVal + p.modulus • q.intVal -
      ofScalar (bias : Int))
  pure ⟨r⟩

/-- Witness a modular quotient `numerator / denominator`.  The denominator
must be nonzero modulo `p`; callers arrange a harmless `(1,0)` relation for
inactive exceptional branches. -/
def divide (denominator numerator : Rep p) : Circuit (Rep p) := do
  let bias := numerator.bound * p.modulus
  let bits ← hint (argTps := [.z, .z])
    h![denominator.intVal, numerator.intVal]
    fun h![(a : Int), (b : Int)] =>
      if ha : 0 ≤ a then
        if hb : 0 ≤ b then
          let d := a.toNat % p.modulus
          if hd : d = 0 then
            fail "zero denominator in lazy modular division"
          else if hg : Nat.gcd d p.modulus = 1 then
            let inverse := ((Nat.gcdA d p.modulus) % (p.modulus : Int)).toNat
            let value := (inverse * (b.toNat % p.modulus)) % p.modulus
            let shifted := (value : Int) * a + bias - b
            if hs : 0 ≤ shifted then
              let q := shifted.toNat / p.modulus
              pure $ Vector.ofFn (n := 2 * n + quotientExtraBits) fun i =>
                if hi : i.val < n then value.testBit i.val
                else q.testBit (i.val - n)
            else fail s!"negative lazy division dividend {shifted}"
          else fail "noninvertible denominator in lazy modular division"
        else fail s!"negative lazy division numerator {b}"
      else fail s!"negative lazy division denominator {a}"
  let value ← U.fromWord {
    bitsLE := Vector.ofFn (n := n) fun i => bits[i.val]'(by omega) }
  let q ← U.fromWord {
    bitsLE := Vector.ofFn (n := n + quotientExtraBits) fun i =>
      bits[n + i.val]'(by omega) }
  assertR1C value.intVal denominator.intVal
    (numerator.intVal + p.modulus • q.intVal - ofScalar (bias : Int))
  pure ⟨value.intVal, 2⟩

/-- Materialize a lazy representative at a boundary. -/
def reduce (x : Rep p) : Circuit (Elem p) := do
  let bits ← hint (argTps := [.z]) h![x.intVal] fun h![(a : Int)] =>
    if ha : 0 ≤ a then
      let value := a.toNat
      let r := value % p.modulus
      let q := value / p.modulus
      pure $ Vector.ofFn (n := 2 * n + quotientExtraBits) fun i =>
        if hi : i.val < n then r.testBit i.val
        else q.testBit (i.val - n)
    else fail s!"negative lazy reduction operand {a}"
  let rWord ← U.fromWord {
    bitsLE := Vector.ofFn (n := n) fun i => bits[i.val]'(by omega) }
  let q ← U.fromWord {
    bitsLE := Vector.ofFn (n := n + quotientExtraBits) fun i =>
      bits[n + i.val]'(by omega) }
  assertR1C 0 0 (x.intVal - (rWord.intVal + p.modulus • q.intVal))
  -- This is the deliberate tight boundary. Lazy arithmetic may use any
  -- bounded representative internally, but a value crossing into arithmetic
  -- modulo a different prime must be the unique representative below `p`.
  ofU p rWord

/-- Check `x*y = target (mod p)` without allocating a redundant remainder.
The bias is a known multiple of `p`, chosen from the target's static bound so
the quotient produced by honest witgen is nonnegative. -/
def assertMulEq (x y target : Rep p) : Circuit Unit := do
  let bias := target.bound * p.modulus
  let bits ← hint (argTps := [.z, .z, .z])
    h![x.intVal, y.intVal, target.intVal]
    fun h![(a : Int), (b : Int), (c : Int)] =>
      let shifted := a * b + bias - c
      if hs : 0 ≤ shifted then
        let q := shifted.toNat / p.modulus
        pure $ Vector.ofFn (n := n + quotientExtraBits) fun i =>
          q.testBit i
      else fail s!"negative quotient in lazy modular relation: {shifted}"
  let q ← U.fromWord {
    bitsLE := Vector.ofFn (n := n + quotientExtraBits) fun i =>
      bits[i.val] }
  assertR1C x.intVal y.intVal
    (target.intVal + p.modulus • q.intVal - ofScalar (bias : Int))

/-- Prove whether a bounded representative is zero modulo `p`.  The inverse
witness rules out a false zero bit; the small second quotient proves the zero
branch without canonicalizing `x`. -/
def zeroTest (x : Rep p) : Circuit ctx.Wℤ := do
  let bits ← hint (argTps := [.z]) h![x.intVal] fun h![(a : Int)] =>
    if ha : 0 ≤ a then
      let value := a.toNat % p.modulus
      let isZero := value = 0
      let inverse := (Nat.gcdA value p.modulus) % (p.modulus : Int)
      pure $ Vector.ofFn (n := n + 1) fun i =>
        if hi : i.val = 0 then isZero else inverse.toNat.testBit (i.val - 1)
    else fail s!"negative lazy zero-test operand {a}"
  let zWord ← U.fromWord {
    bitsLE := Vector.ofFn (n := 1) fun _ => bits[0] }
  let inverse ← U.fromWord {
    bitsLE := Vector.ofFn (n := n) fun i => bits[i.val + 1]'(by omega) }
  let z := zWord.intBits[0]
  assertMulEq p x (ofElem p ⟨inverse⟩) ⟨ofScalar 1 - z, 1⟩
  let qBits ← hint (argTps := [.z, .z])
    h![z, x.intVal] fun h![(b : Int), (a : Int)] =>
    let q := (b * a).toNat / p.modulus
    pure $ Vector.ofFn (n := quotientExtraBits) fun i => q.testBit i
  let q ← U.fromWord {
    bitsLE := Vector.ofFn (n := quotientExtraBits) fun i => qBits[i.val] }
  assertR1C z x.intVal (p.modulus • q.intVal)
  pure z

end Lazy

end Freigen.F2Z.Examples.Modular
