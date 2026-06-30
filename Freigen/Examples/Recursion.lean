import Freigen.ITree
import Freigen.Reflect
import Freigen.Examples.Circuit.Basic

/-!
# `reflect%` reflects plain recursive `def`s — **one path**, with the proof bundled

Both functions below are ordinary structural-recursive `Free` functions (Lean compiles them to
`Nat.brecOn`).  `reflect%` recognises them, re-expresses the body over the `CallOp` signature, and
emits the `ITree.mrec` knot in the same `Comp CircOp` domain as every other reflected program — and,
exactly like the non-recursive path, it returns a **`{ f // soundness }` subtype**: `.1` is the
reflected function, `.2` is the proof that it is sound against the source.

The recursion's soundness is the *uniform* `ITree.Eutt` (`≈`): `∀ N, f N ≈ ofFree (e N)` — the
`tau`-guarded knot is weakly bisimilar to the finite source, the recursion guard's `tau`s absorbed.
It is discharged generically by `ITree.mrec_adequacy` / `adeqBody'` (see `Freigen/Adequacy.lean`), so
the elaborator emits it with no per-function input — there is no longer a separate bare-function path.

* `countdown` is **tail**-recursive.
* `sm` is **non-tail**-recursive (`sm n + 1`): the self-call sits under a `bind`.  This is the case
  the old `iter`-based reflection could not even express; `mrec` keeps the post-call continuation in
  the tree and `interp_bind` pushes it through — and the *same* emitted proof discharges its soundness.
-/

namespace Freigen

open ITree

/-! ## Tail recursion -/

def countdown : Nat → Free (Effect CircOp) Nat
  | 0     => pure 0
  | n + 1 => countdown n

/-- `reflect%` returns the `{ f // ∀ N, f N ≈ ofFree (countdown N) }` subtype — function **and** proof. -/
def countdownC := reflect% countdown

/-- `.1` is the reflected `Comp CircOp` function. -/
example (N : Nat) : Comp CircOp Nat := countdownC.1 N

/-- `.2` is the bundled soundness, for free — no hand-written bisimulation. -/
example : ∀ N, countdownC.1 N ≈ ofFree (countdown N) := countdownC.2

/-- And it composes with the source's own facts, e.g. `countdown N = 0`, to read off a closed form. -/
theorem countdownC_eutt (N : Nat) : countdownC.1 N ≈ ret 0 := by
  have h : countdown N = Free.Pure 0 := by induction N with
    | zero => rfl
    | succ m ih => rw [countdown]; exact ih
  have := countdownC.2 N
  rwa [h] at this

/-! ## Non-tail recursion -/

def sm : Nat → Free (Effect CircOp) Nat
  | 0     => pure 0
  | n + 1 => do let r ← sm n; pure (r + 1)

/-- The *same* `reflect%` handles the non-tail case — same subtype, same bundled soundness. -/
def smC := reflect% sm

example : ∀ N, smC.1 N ≈ ofFree (sm N) := smC.2

/-- `sm n = n`, so the reflected non-tail recursion is `≈ ret N`. -/
theorem smC_eutt (N : Nat) : smC.1 N ≈ ret N := by
  have h : sm N = Free.Pure N := by induction N with
    | zero => rfl
    | succ m ih => rw [sm]; simp [ih, freeBind]
  have := smC.2 N
  rwa [h] at this

end Freigen
