import Freigen.Free
import Freigen.Reflect

/-!
# The `CircOp` circuit DSL

`CircOp` is **first-order** (`assert`); the out-of-circuit witness computation is the scoped `hint`
(`HintS`), *not* an op.  A program is a `Free CircOp HintS α` — the source of truth — with two
Lean-side semantics: `runCirc` (witness generation, blocks run) and `conCirc` (constrained,
predicate transformer, blocks erased to fresh existentials).  `reflect%` compiles it to the dumb
`Prog` AST, sound against `ofFree` by `≈`.

Every example asserts its `runCirc` result and its pretty-printed AST via `#guard_msgs`, so the
comments can't drift from what the code actually produces.
-/

namespace Freigen

/-- The circuit signature: constrain a boolean.  Witnesses come from `hint`, a scoped construct. -/
inductive CircOp : Type → Type → Type 1
  | assert : CircOp Bool Unit

/-- The `hint` scoped signature: for every block type `β`, exactly one `hint` op. -/
abbrev HintS : Type → Type := fun _ => Unit

/-- `hint b`: compute a witness out-of-circuit by running the block `b` (witness generation), or
    introduce a fresh existential and *erase* `b` (constrained).  `b` is a full computation in the
    same monad — a scoped construct, handled per-semantics below. -/
def hint {β} (b : Free CircOp HintS β) : Free CircOp HintS β := .hop () b .pure

/-- Smart constructor for `assert`. -/
def assert (b : Bool) : Free CircOp HintS Unit := Free.perform CircOp.assert b

/-- **Witness generation** into `Option`: `assert false` fails; a `hint` *runs* its block. -/
def runCirc {α} (p : Free CircOp HintS α) : Option α :=
  p.run (fun o i => match o, i with | .assert, b => if b then some () else none)
        (fun _ mb => mb)                         -- hint: use the block's value

/-- The predicate-transformer monad for the constrained semantics. -/
abbrev PredT (α : Type) : Type := (α → Prop) → Prop
instance : Monad PredT where
  pure a := fun c => c a
  bind m f := fun c => m (fun a => f a c)

/-- **Constrained** semantics: `assert b` conjoins `b`; a `hint` introduces a fresh existential and
    *erases* its block (the handler ignores it).  It's the generic `run` at `PredT`. -/
def conCirc {α} (p : Free CircOp HintS α) : (α → Prop) → Prop :=
  p.run (M := PredT) (fun o i => match o, i with | .assert, b => fun c => b = true ∧ c ())
        (fun _ _ c => ∃ x, c x)                  -- hint: fresh existential, block erased

/-- Op names for the pretty-printer. -/
def circName {I R : Type} : CircOp I R → String | .assert => "assert"

/-- Pretty-print a closed `CircOp`/`HintS` program. -/
def ppCirc {mainArgs α} (c : Closed CircOp HintS mainArgs α) : String :=
  pp circName (fun _ => "hint") c

/-! ## A hint + a constraint -/

/-- `hint` the witness `x` out-of-circuit (a real in-monad computation), then constrain `x == 7`. -/
def circ : Free CircOp HintS Unit := do
  let x ← hint (pure (3 + 4))
  assert (x == 7)

/-- info: some PUnit.unit -/
#guard_msgs in #eval runCirc circ

/-- Constrained semantics: `∃ x, (x == 7) = true ∧ …` (the block is erased). -/
example : conCirc circ (fun _ => True) := ⟨7, rfl, trivial⟩

def circC := reflect% circ
example : Closed CircOp HintS [] .unit := circC.1
/-- Denoting the AST is `≈ ofFree` of the source (`ofFree` embeds only the source for comparison). -/
example : denoteProg (circC.1 (KC CircOp) Tp.denote) .nil ≈ ofFree circ := circC.2

-- The reified AST — arithmetic is a real `Bin.eq` node, the `hint` an out-of-circuit scope.
/-- info:
def main() =>
  let v1 ← hint unconstrained
    let v0 := 7
    v0
  let v2 := 7
  let v3 := v1 == v2
  let v4 ← assert(v3)
  v4
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc circC.1)

/-! ## First-order functions: `main` calling helper subroutines

`double`/`quad` are plain `Free` helpers; reflection spills each into a `def_` that `main` `call`s.
Soundness is a compositional bisimulation (no `Free` bridge). -/

def double (x : Nat) : Free CircOp HintS Nat := pure (x + x)
def quad (x : Nat) : Free CircOp HintS Nat := do let d ← double x; double d

def circ2 : Free CircOp HintS Unit := do
  let y ← hint (pure 3)
  let q ← quad y
  assert (q == 12)

def circ2C := reflect% circ2
example : denoteProg (circ2C.1 (KC CircOp) Tp.denote) .nil ≈ ofFree circ2 := circ2C.2

-- `quad` is spilled as `f0` (with `double` inlined), and `main` calls it.
/-- info:
def f0(x1 : Nat) =>
  let v2 := x1 + x1
  let v3 := v2 + v2
  v3
def main() =>
  let v5 ← hint unconstrained
    let v4 := 3
    v4
  let v6 := f0(v5)
  let v7 := 12
  let v8 := v6 == v7
  let v9 ← assert(v8)
  v9
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc circ2C.1)

/-! ## A `main` with inputs

`checkSquare` takes `x : Nat`; `main` receives it as a real parameter. -/

def checkSquare (x : Nat) : Free CircOp HintS Unit := do
  let s ← hint (pure (x * x))
  assert (s == x * x)

def checkSquareC := reflect% checkSquare
example : ∀ x, denoteProg (checkSquareC.1 (KC CircOp) Tp.denote) (.cons x .nil)
    ≈ ofFree (checkSquare x) := checkSquareC.2

/-- info:
def main(x0 : Nat) =>
  let v2 ← hint unconstrained
    let v1 := x0 * x0
    v1
  let v3 := x0 * x0
  let v4 := v2 == v3
  let v5 ← assert(v4)
  v5
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc checkSquareC.1)

/-! ## Monomorphising a polymorphic helper

`dbl` works for any `ZMod N`; `reflect%` monomorphises each call on `N` and shares one spilled `def_`
between equal `N`s.  Here `dbl` is called at `N = 5`, `7`, then `5` again → two defs, the third reuse. -/

def dbl {N : Nat} (x : ZMod N) : Free CircOp HintS (ZMod N) := pure (x + x)

def monoExample (a : ZMod 5) (b : ZMod 7) (c : ZMod 5) : Free CircOp HintS (ZMod 5) := do
  let p ← dbl a
  let _ ← dbl b
  let r ← dbl c
  pure (p + r)

def monoC := reflect% monoExample
example : ∀ a b c, denoteProg (monoC.1 (KC CircOp) Tp.denote) (.cons a (.cons b (.cons c .nil)))
    ≈ ofFree (monoExample a b c) := monoC.2

-- Two spilled defs (`f0 = dbl@5`, `f3 = dbl@7`); `main` takes three args and reuses `f0` for the third.
/-- info:
def f0(x1 : Field<5>) =>
  let v2 := x1 + x1
  v2
def f3(x4 : Field<7>) =>
  let v5 := x4 + x4
  v5
def main(x6 : Field<5>, x7 : Field<7>, x8 : Field<5>) =>
  let v9 := f0(x6)
  let v10 := f3(x7)
  let v11 := f0(x8)
  let v12 := v9 + v11
  v12
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc monoC.1)

/-! ## A multi-argument helper -/

def muladd {N : Nat} (x y : ZMod N) : Free CircOp HintS (ZMod N) := pure (x * y + x)

def multiExample (a b : ZMod 5) : Free CircOp HintS (ZMod 5) := do
  let p ← muladd a b
  let q ← muladd b a
  pure (p + q)

def multiC := reflect% multiExample
example : ∀ a b, denoteProg (multiC.1 (KC CircOp) Tp.denote) (.cons a (.cons b .nil))
    ≈ ofFree (multiExample a b) := multiC.2

-- One two-argument def (`f0 = muladd@5`), called twice.
/-- info:
def f0(x1 : Field<5>, x2 : Field<5>) =>
  let v3 := x1 * x2
  let v4 := v3 + x1
  v4
def main(x5 : Field<5>, x6 : Field<5>) =>
  let v7 := f0(x5, x6)
  let v8 := f0(x6, x5)
  let v9 := v7 + v8
  v9
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc multiC.1)

/-! ## A vector-valued result

`Vector α n` is a first-class object type (`Tp.vec`); a closed vector literal reflects as one `lit`. -/

def vecConst : Free CircOp HintS (Vector Nat 3) := pure ⟨#[1, 2, 3], rfl⟩

def vecC := reflect% vecConst
example : denoteProg (vecC.1 (KC CircOp) Tp.denote) .nil ≈ ofFree vecConst := vecC.2

-- The vector prints as `#v[…]`.
/-- info:
def main() =>
  let v0 := #v[1, 2, 3]
  v0
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc vecC.1)

end Freigen
