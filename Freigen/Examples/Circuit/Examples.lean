import Freigen.Reflect
import Freigen.Examples.Circuit.Basic

/-!
# Examples / smoke tests for `CircOp`

Example programs exercising literals, primitives, loops, monomorphised definitions,
multi-argument functions, hints, the new `runCirc` semantics, and the new `Vector` object type.
-/

namespace Freigen

section Examples

variable {V : Tp → Type} {α : Tp}

/-- A real Lean `do`-block.  `hint` evaluates its function (here the identity) on the seed
    `k`; its `(seed, fn)` input is A-normalised into a `lit`-bound function and a `pair`.  The
    result threads `n` rather than computing on it. -/
def hostExample (k : Nat) : Free (Effect CircOp) Nat := do
  let n ← hintF k (fun s => s)
  pure n


/-- Reflecting it yields a **closed** (`∀ V`) A-normal AST plus a `rfl`-backed proof. -/
def reflectedExample := reflect% hostExample

#check (reflectedExample.1 :
  (F : List Tp → Tp → Type 1) → (V : Tp → Type) → Prog CircOp F V [Tp.nat] Tp.nat)

/-- Soundness: `denoteProg` applied to the argument tuple matches the host (at `F := KleisliF`,
    `V := Tp.denote`). -/
example : ∀ k, denoteProg (reflectedExample.1 (KleisliF CircOp) Tp.denote) (.cons k .nil) =
    hostExample k := reflectedExample.2

/-- Closed case (`main` takes no arguments): `reflect%`'s program is literally a `Closed`. -/
example : denoteProg ((reflect% (hostExample 7)).1 (KleisliF CircOp) Tp.denote) .nil = hostExample 7 :=
  (reflect% (hostExample 7)).2

-- `main` takes its argument as a parameter (`x0`); `hint`'s `(seed, fn)` input pairs the seed
-- with the evaluator, now a real AST `λ` (here the identity):
--   def main(x0 : Nat) =>
--     let v2 := λ x1 =>
--       x1
--     let v3 := (x0, v2)
--     let v4 ← hint(v3)
--     v4
#eval IO.println (pp CircOp.name (reflectedExample.1 PpF PpV))

-- And it denotes back to an ordinary `Free (Effect CircOp)` computation (here at `k := 99`):
#check (denoteProg (reflectedExample.1 (KleisliF CircOp) Tp.denote) (.cons 99 .nil) :
  Free (Effect CircOp) Nat)


/-- A computation whose *result* type is not expressible as a `Tp`: `reflect%` must abort. -/
def badResult : Free (Effect CircOp) (List Nat) := pure []
#check_failure (reflect% badResult)

/-- Compile-time exponent. -/
def powN : Nat := 5

/-- Compute `x ^ powN` by iterated multiplication, accumulating in a `let mut` driven by a
    `for … in` loop, then assert the loop result equals a hinted value.

    The `let mut` + `for` lowers to `ForIn.forIn` over the `Free` monad, the body's `acc * x`
    is a pure operation on the loop-state atom (and on `main`'s argument atom `x`), and the
    `==` is another — so this exercises the loop node and the primitive-operation compiler. -/
def powExample (x : Nat) : Free (Effect CircOp) Bool := do
  let mut acc := 1
  for _ in [0:powN] do
    acc := acc * x
  let h ← hintF x (fun v => v ^ powN)
  assert (acc == h)

/-- It reflects into a `forN` loop whose body is a `bin .mul`, then a `hint`, a `bin .eq`,
    and the `assert` effect. -/
def reflectedPow := reflect% powExample

/-- Soundness still holds by `rfl`: `denote`'s `forN` case is defined via the very same
    `forIn`, so the round-trip is definitional even with the loop. -/
example : ∀ x, denoteProg (reflectedPow.1 (KleisliF CircOp) Tp.denote) (.cons x .nil) =
    powExample x := reflectedPow.2

-- `x` is `main`'s argument atom; the reference value is a `hint` whose evaluator is a real
-- AST `λ` computing `· ^ powN`:
--   def main(x0 : Nat) =>
--     let v1 := 1
--     let v4 := forN 5 from v1 via λ i2 a2 =>
--       let v3 := a2 * x0
--       v3
--     let v8 := λ x5 =>
--       let v6 := 5
--       let v7 := x5 ^ v6
--       v7
--     let v9 := (x0, v8)
--     let v10 ← hint(v9)
--     let v11 := v4 == v10
--     let v12 ← assert(v11)
--     v12
#eval IO.println (pp CircOp.name (reflectedPow.1 PpF PpV))

/-! ## Running circuits with the `runCirc` semantics

The same host programs that `reflect%` lowers can also be **run** with `runCirc`: a `hint`
evaluates its evaluator, and the final `assert` either holds (`some true`) or fails (`none`). -/

-- `powExample x` hints `x ^ 5` and asserts it equals the loop's `x*x*…*x` — always true:
example : runCirc (powExample 3) = some true := by native_decide
example : runCirc (powExample 2) = some true := by native_decide

#eval IO.println s!"runCirc (powExample 3) = {runCirc (powExample 3)}"

/-! ## Monomorphising definitions

`dbl` works for any `ZMod N`; `reflect%` recognises calls to it automatically (it is an
applied `def` that does not unfold to a bare effect primitive), monomorphises each call on
`N`, and shares a single spilled definition between equal `N`s. -/

/-- A `ZMod N`-polymorphic helper — no annotation needed. -/
def dbl {N : Nat} (x : ZMod N) : Free (Effect CircOp) (ZMod N) := pure (x + x)

/-- `dbl` is called at `N = 5`, `N = 7`, then `N = 5` again — so reflection should produce
    exactly two spilled functions (one per distinct `N`), the third call re-using the first. -/
def monoExample (a : ZMod 5) (b : ZMod 7) (c : ZMod 5) : Free (Effect CircOp) (ZMod 5) := do
  let p ← dbl a
  let _ ← dbl b
  let r ← dbl c
  pure (p + r)

def reflectedMono := reflect% monoExample

/-- Soundness by `rfl`: each `call` denotes to applying the (denoted) spilled body, which is
    definitionally the original `dbl` instance. -/
example : ∀ a b c, denoteProg (reflectedMono.1 (KleisliF CircOp) Tp.denote) (.cons a (.cons b (.cons c .nil))) =
    monoExample a b c := reflectedMono.2

-- Two definitions pulled out in front of `main` (`f0 = dbl@5`, `f3 = dbl@7`); `main` takes
-- its three arguments, and the third call (N=5) re-uses `f0`:
--   def f0(x1 : Field<5>) =>
--     let v2 := x1 + x1
--     v2
--   def f3(x4 : Field<7>) =>
--     let v5 := x4 + x4
--     v5
--   def main(x6 : Field<5>, x7 : Field<7>, x8 : Field<5>) =>
--     let v9 := f0(x6)           -- dbl a   (N=5)
--     let v10 := f3(x7)          -- dbl b   (N=7)
--     let v11 := f0(x8)          -- dbl c   (N=5, re-uses f0)
--     let v12 := v9 + v11
--     v12
#eval IO.println (pp CircOp.name (reflectedMono.1 PpF PpV))

/-! ## Multi-argument definitions

A function may take several arguments, passed as an `HList`. -/

/-- A two-argument `ZMod N`-polymorphic helper. -/
def muladd {N : Nat} (x y : ZMod N) : Free (Effect CircOp) (ZMod N) := pure (x * y + x)

/-- Two calls to the same `N = 5` instance: one spill, re-used. -/
def multiExample (a b : ZMod 5) : Free (Effect CircOp) (ZMod 5) := do
  let p ← muladd a b
  let q ← muladd b a
  pure (p + q)

def reflectedMulti := reflect% multiExample

/-- Soundness by `rfl`, with arguments delivered through the `HList`. -/
example : ∀ a b, denoteProg (reflectedMulti.1 (KleisliF CircOp) Tp.denote) (.cons a (.cons b .nil)) =
    multiExample a b := reflectedMulti.2

-- One two-argument function (`f0 = muladd@5`) pulled out in front of `main`, called twice:
--   def f0(x1 : Field<5>, x2 : Field<5>) =>
--     let v3 := x1 * x2
--     let v4 := v3 + x1
--     v4
--   def main(x5 : Field<5>, x6 : Field<5>) =>
--     let v7 := f0(x5, x6)       -- muladd a b
--     let v8 := f0(x6, x5)       -- muladd b a   (re-uses f0)
--     let v9 := v7 + v8
--     v9
#eval IO.println (pp CircOp.name (reflectedMulti.1 PpF PpV))

/-! ## The new `Vector` object type

`Vector α n` is now a first-class object type (`Tp.vec`).  A program returning a (closed)
vector literal reflects: `reflect%` reifies `Vector Nat 3` to `Tp.vec .nat 3` and `lit`-binds
the whole vector, and the round-trip is still proven by `rfl`. -/

/-- A program whose result type is `Vector Nat 3` — previously inexpressible, now supported. -/
def vecConst : Free (Effect CircOp) (Vector Nat 3) := pure ⟨#[1, 2, 3], rfl⟩

def reflectedVec := reflect% vecConst

#check (reflectedVec.1 :
  (F : List Tp → Tp → Type 1) → (V : Tp → Type) → Prog CircOp F V [] (Tp.vec Tp.nat 3))

/-- Soundness by `rfl`, with the vector carried as a single `lit` atom. -/
example : denoteProg (reflectedVec.1 (KleisliF CircOp) Tp.denote) .nil = vecConst := reflectedVec.2

-- The pretty-printer renders the vector literal (`#v[…]`) and its type (`Vector<Nat, 3>`):
--   def main() =>
--     let v0 := #v[1, 2, 3]
--     v0
#eval IO.println (pp CircOp.name (reflectedVec.1 PpF PpV))

/-! ## Vector indexing and a *certified* (non-`rfl`) soundness proof

`v[i]` reflects to the proof-erased `vecGet` primitive, whose denotation is the *total*
`getElem!` — **not** definitionally the host's proof-carrying `v[i]`.  So the soundness proof is
no longer a blanket `rfl`: `reflect%` builds it inductively with `bridgeErase`, inserting the
`getElem!_pos` bridge at each indexed access and plain congruence elsewhere.

The index is always a `Nat` in the AST: a `Fin n` index is reflected as `i.val` and its bound
`i.isLt` is exactly what the bridge consumes — there is no `Fin` in the object-type universe. -/

/-- A dot-product-ish program indexing its vector with `Nat` literals. -/
def vdot (v : Vector Nat 3) : Free (Effect CircOp) Nat := pure (v[0] + v[1] + v[2])

def reflectedVdot := reflect% vdot

/-- Soundness still holds — but the proof is the structurally-built bridge, not a global `rfl`. -/
example : ∀ v, denoteProg (reflectedVdot.1 (KleisliF CircOp) Tp.denote) (.cons v .nil) = vdot v :=
  reflectedVdot.2

-- The indexed accesses print with `v[i]` syntax (the index is its own `lit` atom):
--   def main(x0 : Vector<Nat, 3>) =>
--     let v1 := 0
--     let v2 := x0[v1]
--     …
#eval IO.println (pp CircOp.name (reflectedVdot.1 PpF PpV))
#eval IO.println s!"runCirc (vdot #v[10,20,30]) = {runCirc (vdot ⟨#[10, 20, 30], rfl⟩)}"

/-- The same, but with **`Fin`-indexed** access: reflected as `i.val` (`Nat`), the `Fin` bound
    handled by the bridge.  No `Fin` enters the AST. -/
def vdotFin (v : Vector Nat 3) : Free (Effect CircOp) Nat :=
  pure (v[(0 : Fin 3)] + v[(1 : Fin 3)] + v[(2 : Fin 3)])

def reflectedVdotFin := reflect% vdotFin

example : ∀ v, denoteProg (reflectedVdotFin.1 (KleisliF CircOp) Tp.denote) (.cons v .nil) = vdotFin v :=
  reflectedVdotFin.2

#eval IO.println s!"runCirc (vdotFin #v[10,20,30]) = {runCirc (vdotFin ⟨#[10, 20, 30], rfl⟩)}"

end Examples

end Freigen
