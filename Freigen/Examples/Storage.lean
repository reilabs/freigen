import Freigen.Reflect

/-!
# Examples / a storage effect

A second concrete operation signature `StoreOp`: a tiny mutable store of **naturals addressed by
naturals**, with `set` and `get`.

Besides the usual reflect-and-pretty-print round trip, this file gives the effect an
*operational denotation* `runStore`: a handler that threads a concrete `Store` through the
computation, so a program can actually be **run** and watched to compute a result.  This is a
different denotation from the AST `denote` of `Ast.lean` (which only sends a `Prog` back to a
`Free` computation) — here we go all the way to a value.
-/

namespace Freigen

/-! ## A storage signature -/

inductive StoreOp : Type → Type → Type 1
  /-- `set(addr, val)`: write the natural `val` into cell `addr`; returns unit.  Its input
      packages the address and the value as a pair `addr × val`. -/
  | set : StoreOp (Nat × Nat) Unit
  /-- `get(addr)`: read the natural stored at cell `addr` (unwritten cells read as `0`). -/
  | get : StoreOp Nat Nat

/-- Operation names, for the pretty-printer. -/
def StoreOp.name : {I R : Type} → StoreOp I R → String
  | _, _, .set => "set"
  | _, _, .get => "get"

/-- Runtime smart constructors, living in the ordinary `Free (Effect StoreOp)`. -/
def setS (addr val : Nat) : Free (Effect StoreOp) Unit :=
  Free.Impure (Effect.mk StoreOp.set (addr, val)) Free.Pure
def getS (addr : Nat) : Free (Effect StoreOp) Nat :=
  Free.Impure (Effect.mk StoreOp.get addr) Free.Pure

/-! ## An operational denotation: the stateful handler

`Free (Effect StoreOp)` is given meaning by *running* it against a concrete `Store` (a map from
address to value, absent cells reading `0`).  The whole interpreter is just `foldFree` into the
`StateM Store` monad: it folds every effect layer with a one-line `handleStore` — `set` mutates
the store, `get` reads it — and `foldFree` threads the state and sequences the continuations. -/

/-- A concrete memory: address → value (unwritten cells read as `0`). -/
abbrev Store : Type := Nat → Nat

/-- The all-zero store. -/
def Store.empty : Store := fun _ => 0

/-- Write `val` to cell `addr`, leaving the rest of the store unchanged. -/
def Store.write (s : Store) (addr val : Nat) : Store :=
  fun a => if a = addr then val else s a

/-- Interpret a single storage effect into `StateM Store`: `set` mutates the store, `get`
    reads the addressed cell. -/
def handleStore : {x : Type} → Effect StoreOp x → StateM Store x
  | _, .mk .set inp => modify (fun s => s.write inp.1 inp.2)
  | _, .mk .get adr => (· adr) <$> get

/-- Run a storage computation against an initial store, returning its result paired with the
    final store — `foldFree` folds each effect through `handleStore`, threading the `Store`. -/
def runStore {α : Type} (p : Free (Effect StoreOp) α) (s : Store) : α × Store :=
  (foldFree p handleStore).run s

/-! ## Examples / smoke tests -/

section Examples

/-- Transfer `amount` from cell `0` to cell `1`: read both balances, debit cell `0`, credit
    cell `1`, and return the new balance of cell `1`.

    Exercises `get`, arithmetic on op-results and on `main`'s argument (`bal0 - amount`), and
    `set` whose *pair* input A-normalises into a `lit` address, a `-`, and a `pair`. -/
def transfer (amount : Nat) : Free (Effect StoreOp) Nat := do
  let bal0 ← getS 0
  let bal1 ← getS 1
  setS 0 (bal0 - amount)
  setS 1 (bal1 + amount)
  getS 1

/-- A starting memory: `cell 0 ↦ 100`, `cell 1 ↦ 20`. -/
def demoStore : Store := (Store.empty.write 0 100).write 1 20

-- It **denotes (runs) to something sensical**: transferring `30` from `0` (100) to `1` (20)
-- returns `50`, and leaves `cell 0 ↦ 70`, `cell 1 ↦ 50`.
example : (runStore (transfer 30) demoStore).1   = 50 := by decide
example : (runStore (transfer 30) demoStore).2 0 = 70 := by decide
example : (runStore (transfer 30) demoStore).2 1 = 50 := by decide

#eval IO.println s!"transfer 30 from cell0=100, cell1=20 ⇒ returns \
  {(runStore (transfer 30) demoStore).1}; cell0={(runStore (transfer 30) demoStore).2 0}, \
  cell1={(runStore (transfer 30) demoStore).2 1}"

/-- And it **lowers** to a `Prog`, with a `rfl`-backed soundness proof. -/
def reflectedTransfer := reflect% transfer

/-- Soundness: `denoteProg` of the lowered program matches the host computation. -/
example : ∀ amount,
    Freigen.ITree.Eutt
      (Freigen.ITree.ofFree (denoteProg (reflectedTransfer.1 (KleisliF StoreOp) Tp.denote) (.cons amount .nil)))
      (Freigen.ITree.ofFree (transfer amount)) := reflectedTransfer.2

-- …and it **prints back** — `amount` is `main`'s argument atom `x0`, and each `set`'s pair
-- input is built from a `lit` address and a `-`/`+`:
--   def main(x0 : Nat) =>
--     let v1 := 0
--     let v2 ← get(v1)            -- bal0 := get(0)
--     let v3 := 1
--     let v4 ← get(v3)            -- bal1 := get(1)
--     let v5 := 0
--     let v6 := v2 - x0
--     let v7 := (v5, v6)
--     let v8 ← set(v7)            -- set(0, bal0 - amount)
--     let v9 := 1
--     let v10 := v4 + x0
--     let v11 := (v9, v10)
--     let v12 ← set(v11)          -- set(1, bal1 + amount)
--     let v13 := 1
--     let v14 ← get(v13)          -- get(1)
--     v14
#eval IO.println (pp StoreOp.name (reflectedTransfer.1 PpF PpV))

/-- Number of loop steps — a compile-time constant (the `forN` count is a host `Nat`, not a
    runtime atom, so the loop bound must be static, just as `powExample` loops over `powN`). -/
def steps : Nat := 5

/-- A storage program with a **loop**: starting from `main`'s argument `seed`, accumulate
    `seed + 0 + 1 + … + (steps-1)` in a `let mut` driven by a `for` loop, persist the total to
    memory cell `seed` (the address is itself a natural — `main`'s argument), then read it back.

    The `let mut` + `for` lowers to a `forN` over the accumulator atom (its body the pure
    `acc + i`), surrounded by the `set`/`get` effects — so this exercises the loop node *and*
    natural-addressed storage in one program. -/
def storedTriangle (seed : Nat) : Free (Effect StoreOp) Nat := do
  let mut acc := seed
  for i in [0:steps] do
    acc := acc + i
  setS seed acc
  getS seed

-- It denotes (runs) to `seed + (0+1+2+3+4) = seed + 10`, parked at address `seed`:
-- `storedTriangle 4 ↦ 14` (in cell 4), `storedTriangle 7 ↦ 17` (in cell 7).
#eval IO.println s!"storedTriangle 4 ⇒ {(runStore (storedTriangle 4) Store.empty).1} \
  (cell 4 = {(runStore (storedTriangle 4) Store.empty).2 4}), \
  storedTriangle 7 ⇒ {(runStore (storedTriangle 7) Store.empty).1}"

/-- It lowers, with the usual `rfl` soundness (the `forN`/`forIn` round-trip is definitional,
    since the loop body is pure — exactly as in `powExample`). -/
def reflectedStoredTriangle := reflect% storedTriangle

example : ∀ seed,
    Freigen.ITree.Eutt
      (Freigen.ITree.ofFree (denoteProg (reflectedStoredTriangle.1 (KleisliF StoreOp) Tp.denote) (.cons seed .nil)))
      (Freigen.ITree.ofFree (storedTriangle seed)) := reflectedStoredTriangle.2

-- …and prints back: a `forN` (count `5`) accumulating `a + i`, then a `set` at address `x0`
-- (the seed) and a `get`:
--   def main(x0 : Nat) =>
--     let v3 := forN 5 from x0 via λ i1 a1 =>
--       let v2 := a1 + i1
--       v2
--     let v4 := (x0, v3)
--     let v5 ← set(v4)
--     let v6 ← get(x0)
--     v6
#eval IO.println (pp StoreOp.name (reflectedStoredTriangle.1 PpF PpV))

end Examples

end Freigen
