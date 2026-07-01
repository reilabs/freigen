import Freigen.Free
import Freigen.Recursion

/-!
# The `StoreOp` DSL on `Free` — a **hint-less** (`NoScope`) example

A mutable store of naturals addressed by naturals.  No scoped constructs (`NoScope`), so the program
is a plain first-order free monad and never carries a `hop` node — yet it reuses the *same*
`Free`/`run`/`reflect%`/`denote` pipeline as the circuit, with the scoped handler vacuous.
-/

namespace Freigen

/-- Store operations: read/write a `Nat` cell addressed by a `Nat`. -/
inductive StoreOp : Type → Type → Type 1
  | get : StoreOp Nat Nat
  | set : StoreOp (Nat × Nat) Unit

def get (a : Nat) : Free StoreOp NoScope Nat := Free.perform StoreOp.get a
def set (a v : Nat) : Free StoreOp NoScope Unit := Free.perform StoreOp.set (a, v)

/-- Operational semantics into a state monad (the store is a function `Nat → Nat`). -/
def runStore {α} (p : Free StoreOp NoScope α) : StateM (Nat → Nat) α :=
  p.run (fun o i => match o, i with
    | .get, a      => fun s => (s a, s)
    | .set, (a, v) => fun s => ((), fun x => if x == a then v else s x)) noScopeRun

def storeProg : Free StoreOp NoScope Nat := do
  set 0 42
  get 0

#eval (runStore storeProg).run' (fun _ => 0)               -- 42

/-- The same `reflect%` pipeline; no `hop` nodes, soundness for free. -/
def storeC := reflect% storeProg
example :
    denoteProg (storeC.1 (KC StoreOp) Tp.denote) .nil ≈ ofFree storeProg :=
  storeC.2

end Freigen
