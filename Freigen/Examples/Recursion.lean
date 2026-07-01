import Freigen.Reflect
import Freigen.Free

/-! # Recursion examples: `countdown` (tail) and `sm` (non-tail), reflected into `rec_` programs. -/

namespace Freigen

inductive NoOp : Type → Type → Type 1

/-- A tail-recursive `Free` function. -/
def countdown : Nat → Free NoOp NoScope Nat
  | 0     => .pure 0
  | n + 1 => countdown n

/-- `reflect%` reflects the recursive `def` into a **`Prog` with a `rec_` node** (self-calls are the
    `CallOp.call` op, tied by `mrec`) plus its soundness — the *same* `{ g : Closed // … denoteProg …
    ≈ ofFree … }` shape as the non-recursive arm, so recursion is first-class in `Prog`. -/
def countdownC := reflect% countdown

/-- `.1` is the closed `Prog` (a `rec_` + `main`). -/
example : Closed NoOp NoScope [.nat] .nat := countdownC.1
/-- `.2`: denoting the AST (`mrec` at the `rec_`) is `≈ ofFree` of the source, for every input. -/
example : ∀ N, denoteProg (countdownC.1 (KC NoOp) Tp.denote) (.cons N .nil)
    ≈ ofFree (countdown N) := countdownC.2

-- The recursion pretty-prints as a `rec` definition with a self-call, plus `main` calling it.
/-- info:
rec f0(x1 : Nat) =>
  let v2 := 0
  let v3 := x1 == v2
  if v3 then
    let v4 := 0
    v4
  else
    let v5 := 1
    let v6 := x1 - v5
    let v7 ← f0 (self-call)(v6)
    v7
def main(x8 : Nat) =>
  let v9 := f0(x8)
  v9
-/
#guard_msgs (whitespace := lax) in
  #eval IO.println (pp (fun o => nomatch o) (fun s => nomatch s) countdownC.1)

/-- **Non-tail** recursion (`sm n + 1`): the self-call sits under a `bind`.  `reflect%` handles
    it through the same path — `interp_bind` pushes the post-call `+1` through. -/
def sm : Nat → Free NoOp NoScope Nat
  | 0     => .pure 0
  | n + 1 => do let r ← sm n; pure (r + 1)

def smC := reflect% sm
example : ∀ N, denoteProg (smC.1 (KC NoOp) Tp.denote) (.cons N .nil) ≈ ofFree (sm N) := smC.2


end Freigen
