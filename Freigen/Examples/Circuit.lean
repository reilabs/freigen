import Freigen.Scoped
import Freigen.ScopedRec

/-!
# The `CircOp` circuit DSL on `FreeH`

`CircOp` is **first-order** (`assert`); the out-of-circuit witness computation is the scoped `hint`
(`HintS`), *not* an op.  A program is a `FreeH CircOp HintS α` — the source of truth — with two
Lean-side semantics: `runCirc` (witness generation, blocks run) and `conCirc` (constrained,
predicate transformer, blocks erased to fresh existentials).  `reflect%` compiles it to the dumb
`Code` AST, sound against `ofFreeH` by `≈`.
-/

namespace Freigen.Scoped

/-- The circuit signature: constrain a boolean.  Witnesses come from `hint`, a scoped construct. -/
inductive CircOp : Type → Type → Type 1
  | assert : CircOp Bool Unit

/-- Smart constructor for `assert`. -/
def assert (b : Bool) : FreeH CircOp HintS Unit := FreeH.perform CircOp.assert b

/-- **Witness generation** into `Option`: `assert false` fails; `hint` blocks are run. -/
def runCirc {α} (p : FreeH CircOp HintS α) : Option α :=
  p.run (fun o i => match o, i with | .assert, b => if b then some () else none) hintRun

/-- **Constrained** predicate transformer: `assert b` conjoins `b`, `hint` is a fresh existential. -/
def conCirc {α} (p : FreeH CircOp HintS α) : (α → Prop) → Prop :=
  p.con (fun o i => match o, i with | .assert, b => fun c => b = true ∧ c ()) hintCon

/-- A circuit: `hint` the witness `x` out-of-circuit (a real in-monad computation), then constrain
    the computed predicate `x == 7`. -/
def circ : FreeH CircOp HintS Unit := do
  let x ← hint (pure (3 + 4))
  assert (x == 7)

-- Witness generation succeeds:
#eval runCirc circ                                          -- some ()
/-- Constrained semantics: `∃ x, (x == 7) = true ∧ …` (the block is erased). -/
example : conCirc circ (fun _ => True) := ⟨7, rfl, trivial⟩

/-- `reflect%` compiles the circuit into the dumb `Prog` AST **and** its ITree soundness. -/
def circC := reflect% circ
/-- `.1` is the closed `Prog` AST. -/
example : Closed CircOp HintS [] .unit := circC.1
/-- `.2`: the AST's ITree meaning `denoteProg` is `≈ ofFreeH` of the source — note `denoteProg` lands
    in `Comp` directly; `ofFreeH` only embeds the source `FreeH` for comparison. -/
example : denoteProg (circC.1 (KC CircOp) Tp.denote) .nil ≈ ofFreeH circ := circC.2

-- The reified AST pretty-prints — the arithmetic is **visible** (`x == 7` is a real `Bin.eq` node,
-- not an opaque closure), and the `hint` block is an out-of-circuit scope.
#eval pp (fun o => match o with | .assert => "assert") (fun _ => "hint") circC.1

/-! ## First-order functions: a `main` that calls helper subroutines

`double`/`quad` are plain `FreeH` helpers; reflection spills each into a `def_` that `main` `call`s.
Soundness now goes through a **compositional bisimulation** (no `FreeH` bridge): the reflector
unfolds the source definitions it touched so scope- and call-binds fuse consistently on both sides,
and `denoteProg ≈ ofFreeH` closes. -/

def double (x : Nat) : FreeH CircOp HintS Nat := pure (x + x)
def quad (x : Nat) : FreeH CircOp HintS Nat := do let d ← double x; double d

def circ2 : FreeH CircOp HintS Unit := do
  let y ← hint (pure 3)
  let q ← quad y
  assert (q == 12)

def circ2C := reflect% circ2
example : denoteProg (circ2C.1 (KC CircOp) Tp.denote) .nil ≈ ofFreeH circ2 := circ2C.2

-- Prints `def f0(x) => …` (double), `def f1(x) => …` (quad, calling f0 twice), then `def main`.
#eval pp (fun o => match o with | .assert => "assert") (fun _ => "hint") circ2C.1

/-! ## A `main` with inputs

`reflect%` also reflects a program that is a **function of its inputs**: `main` takes the arguments
as an `HList`.  Here `checkSquare` takes `x : Nat`, and soundness is `∀ x, … ≈ ofFreeH (checkSquare x)`. -/

def checkSquare (x : Nat) : FreeH CircOp HintS Unit := do
  let s ← hint (pure (x * x))
  assert (s == x * x)

def checkSquareC := reflect% checkSquare
example : ∀ x, denoteProg (checkSquareC.1 (KC CircOp) Tp.denote) (.cons x .nil)
    ≈ ofFreeH (checkSquare x) := checkSquareC.2

-- Prints `def main(x1 : Nat) => …` — the input is a real `main` parameter.
#eval pp (fun o => match o with | .assert => "assert") (fun _ => "hint") checkSquareC.1

end Freigen.Scoped
