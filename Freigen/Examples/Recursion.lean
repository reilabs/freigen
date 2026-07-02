import Freigen.Reflect.Recursion
import Freigen.Free
import Freigen.Compile
import Freigen.Examples.Circuit.Basic

/-! # Recursion examples: `countdown` (tail), `sm` (non-tail), and stateful recursion
(`sumAcc`, `countAsserts`), reflected into `rec_` programs. -/

namespace Freigen

inductive NoOp : Type → Type → Type 1

/-- The DSL instance: both `NoOp` and `NoScope` are empty, so both namers are vacuous. -/
instance : DSL NoOp NoScope where
  opName o := nomatch o
  scopeName s := s.elim

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

-- The recursion serializes as a `rec` definition with a self-call, plus `main` calling it.
/-- info:
(program
  (rec countdown ((x0 nat)) nat
    (block
      (let v1 nat (lit 0))
      (let v2 bool (eq x0 v1))
      (if v2
        (block
          (let v3 nat (lit 0))
          (ret v3))
        (block
          (let v4 nat (lit 1))
          (let v5 nat (sub x0 v4))
          (let v6 nat (self v5))
          (ret v6)))))
  (main ((x7 nat)) nat
    (block
      (let v8 nat (call countdown x7))
      (ret v8))))
-/
#guard_msgs (whitespace := lax) in #eval IO.println (serialize countdownC)

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
(program
  (rec sm ((x0 nat)) nat
    (block
      (let v1 nat (lit 0))
      (let v2 bool (eq x0 v1))
      (if v2
        (block
          (let v3 nat (lit 0))
          (ret v3))
        (block
          (let v4 nat (lit 1))
          (let v5 nat (sub x0 v4))
          (let v6 nat (self v5))
          (let v7 nat (lit 1))
          (let v8 nat (add v6 v7))
          (ret v8)))))
  (main ((x9 nat)) nat
    (block
      (let v10 nat (call sm x9))
      (ret v10))))
-/
#guard_msgs (whitespace := lax) in #eval IO.println (serialize smC)

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
(program
  (rec sumAcc ((x0 (prod nat nat))) nat
    (block
      (let v1 nat (fst x0))
      (let v2 nat (lit 0))
      (let v3 bool (eq v1 v2))
      (if v3
        (block
          (let v4 nat (snd x0))
          (ret v4))
        (block
          (let v5 nat (fst x0))
          (let v6 nat (lit 1))
          (let v7 nat (sub v5 v6))
          (let v8 nat (snd x0))
          (let v9 nat (fst x0))
          (let v10 nat (lit 1))
          (let v11 nat (sub v9 v10))
          (let v12 nat (lit 1))
          (let v13 nat (add v11 v12))
          (let v14 nat (add v8 v13))
          (let v15 (prod nat nat) (pair v7 v14))
          (let v16 nat (self v15))
          (ret v16)))))
  (main ((x17 nat) (x18 nat)) nat
    (block
      (let v19 (prod nat nat) (pair x17 x18))
      (let v20 nat (call sumAcc v19))
      (ret v20))))
-/
#guard_msgs (whitespace := lax) in #eval IO.println (serialize sumAccC)

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
(program
  (rec countAsserts ((x0 (prod nat bool))) nat
    (block
      (let v1 nat (fst x0))
      (let v2 nat (lit 0))
      (let v3 bool (eq v1 v2))
      (if v3
        (block
          (let v4 nat (lit 0))
          (ret v4))
        (block
          (let v5 bool (snd x0))
          (let v6 unit (op assert v5))
          (let v7 nat (fst x0))
          (let v8 nat (lit 1))
          (let v9 nat (sub v7 v8))
          (let v10 bool (snd x0))
          (let v11 (prod nat bool) (pair v9 v10))
          (let v12 nat (self v11))
          (let v13 nat (lit 1))
          (let v14 nat (add v12 v13))
          (ret v14)))))
  (main ((x15 nat) (x16 bool)) nat
    (block
      (let v17 (prod nat bool) (pair x15 x16))
      (let v18 nat (call countAsserts v17))
      (ret v18))))
-/
#guard_msgs (whitespace := lax) in #eval IO.println (serialize countAssertsC)

end Freigen
