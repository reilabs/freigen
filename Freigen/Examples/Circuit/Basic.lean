import Freigen.Ast

/-!
# The circuit signature `CircOp`, and its computable semantics

`CircOp` is a tiny *arithmetic-circuit* operation signature with two effects:

- `hint a f` — non-deterministic **advice**: in a circuit this introduces a fresh witness whose
  value is computed off-circuit by the evaluator `f` on the seed `a` (and is then constrained).
- `assert b` — a **constraint**: the boolean `b` must hold.

Besides the smart constructors that live in `Free (Effect CircOp)`, this module gives the
signature a **computable semantics** `runCirc` in the spirit of `Storage`'s `runStore`: a
`foldFree` handler into the `Option` monad, where a `hint` simply *evaluates* its function
(advice = the off-circuit value) and an `assert` is a *potential failure* (`none` when the
asserted boolean is false).  So running a circuit either yields `some result` (all asserts held)
or `none` (some assert failed).
-/

namespace Freigen

/-! ## A concrete signature -/

inductive CircOp : Type → Type → Type 1
  /-- A hint (advice): evaluate `f` on the seed `a`, returning the result `β`.  Its input
      packages both into a pair `α × (α → β)`, so this is a special "eval" operator. -/
  | hint {α β : Type} : CircOp (α × (α → β)) β
  /-- Assert the input `Bool` holds; returns it. -/
  | assert   : CircOp Bool Bool

/-- Operation names, for the pretty-printer. -/
def CircOp.name : {I R : Type} → CircOp I R → String
  | _, _, .hint     => "hint"
  | _, _, .assert   => "assert"

/-- Runtime smart constructors, living in the ordinary `Free (Effect CircOp)`.  `CircOp` is
    fully `Tp`-agnostic, so these are plain Lean-typed. -/
def hintF {α β : Type} (a : α) (f : α → β) : Free (Effect CircOp) β :=
  Free.Impure (Effect.mk CircOp.hint (a, f)) Free.Pure
def assert (b : Bool) : Free (Effect CircOp) Bool :=
  Free.Impure (Effect.mk CircOp.assert b) Free.Pure

/-! ## A computable semantics: `runCirc`

`Free (Effect CircOp)` is given meaning by `foldFree`ing every effect layer into `Option`:

* `hint` *evaluates* its function on its seed — the advice value — and always succeeds.
* `assert` *succeeds with* its boolean when it holds, and **fails** (`none`) when it does not.

`foldFree` then threads the `Option` (short-circuiting on the first failed assert) and sequences
the continuations.  This is the operational counterpart of the AST `denote`: where `denote` only
sends a program back to a `Free` computation, `runCirc` runs it all the way to a value-or-failure. -/

/-- Interpret a single circuit effect into `Option`: a `hint` evaluates its evaluator on its
    seed (advice); an `assert` succeeds with its boolean, or fails (`none`) when it is false. -/
def handleCirc : {x : Type} → Effect CircOp x → Option x
  | _, .mk .hint   inp => some (inp.2 inp.1)
  | _, .mk .assert b   => if b then some b else none

/-- Run a circuit computation, returning `some result` if every `assert` held, or `none` if any
    `assert` failed — `foldFree` folds each effect through `handleCirc`, threading the `Option`. -/
def runCirc {α : Type} (p : Free (Effect CircOp) α) : Option α := foldFree p handleCirc

/-! ## Semantics smoke tests -/

-- `assert` is a potential failure: it passes through `true` and aborts on `false`.
example : runCirc (assert true)  = some true := rfl
example : runCirc (assert false) = none      := rfl

-- `hint` is `eval`: it applies its evaluator to its seed.
example : runCirc (hintF 5 (· + 1)) = some 6 := rfl

-- A short program threading a hint into an assert: passes iff the asserted equality holds.
example : runCirc (do let n ← hintF 20 (· / 2); assert (n == 10)) = some true  := rfl
example : runCirc (do let n ← hintF 20 (· / 2); assert (n == 99)) = none       := rfl

end Freigen
