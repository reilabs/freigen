import Freigen.Reflect
import Freigen.Free
import Freigen.Examples.Circuit

/-! # Recursion examples: `countdown` (tail), `sm` (non-tail), and stateful recursion
(`sumAcc`, `countAsserts`), reflected into `rec_` programs. -/

namespace Freigen

inductive NoOp : Type → Type → Type 1

/-- A tail-recursive `Free` function. -/
def countdown : Nat → Free NoOp NoScope Nat
  | 0     => .pure 0
  | n + 1 => countdown n

/-- `reflect_def` reflects the recursive `def` into a **`Prog` with a `rec_` node** (self-calls are
    the `CallOp.call` op, tied by `mrec`) plus its named soundness `countdownC_sound` — the same
    shape as the non-recursive arm, so recursion is first-class in `Prog`. -/
reflect_def countdownC := countdown

/-- The closed `Prog` (a `rec_` + `main`). -/
example : Closed NoOp NoScope [.nat] .nat := countdownC
/-- info: Freigen.countdownC_sound (a0 : ℕ) :
  ITree.Eutt (denoteProg (countdownC (KC NoOp) Tp.denote) (HList.cons a0 HList.nil)) (ofFree (countdown a0)) -/
#guard_msgs (whitespace := lax) in
#check countdownC_sound

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
  #eval IO.println (pp (fun o => nomatch o) (fun s => nomatch s) countdownC)

/-- **Non-tail** recursion (`sm n + 1`): the self-call sits under a `bind`.  `reflect%` handles
    it through the same path — `interp_bind` pushes the post-call `+1` through. -/
def sm : Nat → Free NoOp NoScope Nat
  | 0     => .pure 0
  | n + 1 => do let r ← sm n; pure (r + 1)

reflect_def smC := sm
/-- info: Freigen.smC_sound (a0 : ℕ) :
  ITree.Eutt (denoteProg (smC (KC NoOp) Tp.denote) (HList.cons a0 HList.nil)) (ofFree (sm a0)) -/
#guard_msgs (whitespace := lax) in
#check smC_sound

-- The post-call `+1` sits *after* the self-call — non-tail recursion in the reflected body.
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
    let v8 := 1
    let v9 := v7 + v8
    v9
def main(x10 : Nat) =>
  let v11 := f0(x10)
  v11
-/
#guard_msgs (whitespace := lax) in
  #eval IO.println (pp (fun o => nomatch o) (fun s => nomatch s) smC)

/-! ## Stateful recursion: extra `Tp`-typed arguments thread through the tupled `rec_` state

`f : Nat → A₁ → … → Free Op SOp ρ` (structural on the **first** argument) reflects at the tupled
state `σ = Nat × A₁ × …`: `main` takes the arguments separately and pairs them (`bin .pair`), the
`rec_` body projects them back out (`un .fst`/`.snd`), and a self-call re-tuples its arguments. -/

/-- Sum with an accumulator — tail-recursive, threading `acc` through the recursion. -/
def sumAcc : Nat → Nat → Free NoOp NoScope Nat
  | 0,     acc => pure acc
  | n + 1, acc => sumAcc n (acc + (n + 1))

reflect_def sumAccC := sumAcc
/-- info: Freigen.sumAccC_sound (a0 a1 : ℕ) :
  ITree.Eutt (denoteProg (sumAccC (KC NoOp) Tp.denote) (HList.cons a0 (HList.cons a1 HList.nil)))
    (ofFree (sumAcc a0 a1)) -/
#guard_msgs (whitespace := lax) in
#check sumAccC_sound

/-- info:
rec f0(x1 : (Nat × Nat)) =>
  let v2 := .1 x1
  let v3 := 0
  let v4 := v2 == v3
  if v4 then
    let v5 := .2 x1
    v5
  else
    let v6 := .1 x1
    let v7 := 1
    let v8 := v6 - v7
    let v9 := .2 x1
    let v10 := .1 x1
    let v11 := 1
    let v12 := v10 - v11
    let v13 := 1
    let v14 := v12 + v13
    let v15 := v9 + v14
    let v16 := (v8, v15)
    let v17 ← f0 (self-call)(v16)
    v17
def main(x18 : Nat, x19 : Nat) =>
  let v20 := (x18, x19)
  let v21 := f0(v20)
  v21
-/
#guard_msgs (whitespace := lax) in
  #eval IO.println (pp (fun o => nomatch o) (fun s => nomatch s) sumAccC)

/-- **Effectful, non-tail, stateful**: an `assert` per unrolling (the `Bool` state rides along),
    and a `+1` *after* the self-call. -/
def countAsserts : Nat → Bool → Free CircOp HintS Nat
  | 0,     _ => pure 0
  | n + 1, b => do
      let _ ← assert b
      let r ← countAsserts n b
      pure (r + 1)

reflect_def countAssertsC := countAsserts
/-- info: Freigen.countAssertsC_sound (a0 : ℕ) (a1 : Bool) :
  ITree.Eutt (denoteProg (countAssertsC (KC CircOp) Tp.denote) (HList.cons a0 (HList.cons a1 HList.nil)))
    (ofFree (countAsserts a0 a1)) -/
#guard_msgs (whitespace := lax) in
#check countAssertsC_sound

/-- info:
rec f0(x1 : (Nat × Bool)) =>
  let v2 := .1 x1
  let v3 := 0
  let v4 := v2 == v3
  if v4 then
    let v5 := 0
    v5
  else
    let v6 := .2 x1
    let v7 ← assert(v6)
    let v8 := .1 x1
    let v9 := 1
    let v10 := v8 - v9
    let v11 := .2 x1
    let v12 := (v10, v11)
    let v13 ← f0 (self-call)(v12)
    let v14 := 1
    let v15 := v13 + v14
    v15
def main(x16 : Nat, x17 : Bool) =>
  let v18 := (x16, x17)
  let v19 := f0(v18)
  v19
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc countAssertsC)

end Freigen
