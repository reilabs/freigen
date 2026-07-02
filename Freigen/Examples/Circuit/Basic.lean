import Freigen.Free
import Freigen.Reflect

/-!
# The `CircOp` circuit DSL

`CircOp` is **first-order** (`assert`); the out-of-circuit witness computation is the scoped `hint`
(`HintS`), *not* an op.  A program is a `Free CircOp HintS α` — the source of truth — with two
Lean-side semantics: `runCirc` (witness generation, blocks run) and `conCirc` (constrained,
predicate transformer, blocks erased to fresh existentials).  `reflect%` compiles it to the dumb
`Prog` AST, sound against `ofFree` by `≈`.

Every example is reflected with `reflect_def C := src` (named `C` / `C_sound`), and pins its
`runCirc` result, its **soundness statement** (`#check C_sound`), and its pretty-printed AST via
`#guard_msgs`, so the comments can't drift from what the code actually produces.
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

reflect_def circC := circ
example : Closed CircOp HintS [] .unit := circC
/-- info: Freigen.circC_sound : ITree.Eutt (denoteProg (circC (KC CircOp) Tp.denote) HList.nil) (ofFree circ) -/
#guard_msgs (whitespace := lax) in
#check circC_sound

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
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc circC)

/-! ## First-order functions: `main` calling helper subroutines

`double`/`quad` are plain `Free` helpers; reflection spills each into a `def_` that `main` `call`s.
Soundness is a compositional bisimulation (no `Free` bridge). -/

def double (x : Nat) : Free CircOp HintS Nat := pure (x + x)
def quad (x : Nat) : Free CircOp HintS Nat := do let d ← double x; double d

def circ2 : Free CircOp HintS Unit := do
  let y ← hint (pure 3)
  let q ← quad y
  assert (q == 12)

reflect_def circ2C := circ2
/-- info: Freigen.circ2C_sound : ITree.Eutt (denoteProg (circ2C (KC CircOp) Tp.denote) HList.nil) (ofFree circ2) -/
#guard_msgs (whitespace := lax) in
#check circ2C_sound

-- `double` and `quad` each spill under their own names — helper bodies may call earlier helpers.
/-- info:
def double(x0 : Nat) =>
  let v1 := x0 + x0
  v1
def quad(x2 : Nat) =>
  let v3 := double(x2)
  let v4 := double(v3)
  v4
def main() =>
  let v6 ← hint unconstrained
    let v5 := 3
    v5
  let v7 := quad(v6)
  let v8 := 12
  let v9 := v7 == v8
  let v10 ← assert(v9)
  v10
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc circ2C)

/-! ## A `main` with inputs

`checkSquare` takes `x : Nat`; `main` receives it as a real parameter. -/

def checkSquare (x : Nat) : Free CircOp HintS Unit := do
  let s ← hint (pure (x * x))
  assert (s == x * x)

reflect_def checkSquareC := checkSquare
/-- info: Freigen.checkSquareC_sound (x : ℕ) :
  ITree.Eutt (denoteProg (checkSquareC (KC CircOp) Tp.denote) (HList.cons x HList.nil)) (ofFree (checkSquare x)) -/
#guard_msgs (whitespace := lax) in
#check checkSquareC_sound

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
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc checkSquareC)

/-! ## Monomorphising a polymorphic helper

`dbl` works for any `ZMod N`; `reflect%` monomorphises each call on `N` and shares one spilled `def_`
between equal `N`s.  Here `dbl` is called at `N = 5`, `7`, then `5` again → two defs, the third reuse. -/

def dbl {N : Nat} (x : ZMod N) : Free CircOp HintS (ZMod N) := pure (x + x)

def monoExample (a : ZMod 5) (b : ZMod 7) (c : ZMod 5) : Free CircOp HintS (ZMod 5) := do
  let p ← dbl a
  let _ ← dbl b
  let r ← dbl c
  pure (p + r)

reflect_def monoC := monoExample
/-- info: Freigen.monoC_sound (a : ZMod 5) (b : ZMod 7) (c : ZMod 5) :
  ITree.Eutt (denoteProg (monoC (KC CircOp) Tp.denote) (HList.cons a (HList.cons b (HList.cons c HList.nil))))
    (ofFree (monoExample a b c)) -/
#guard_msgs (whitespace := lax) in
#check monoC_sound

-- Two spilled defs (`dbl` at 5, `dbl_2` at 7 — monomorphisations uniquify); the third call reuses `dbl`.
/-- info:
def dbl(x0 : Field<5>) =>
  let v1 := x0 + x0
  v1
def dbl_2(x2 : Field<7>) =>
  let v3 := x2 + x2
  v3
def main(x4 : Field<5>, x5 : Field<7>, x6 : Field<5>) =>
  let v7 := dbl(x4)
  let v8 := dbl_2(x5)
  let v9 := dbl(x6)
  let v10 := v7 + v9
  v10
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc monoC)

/-! ## A multi-argument helper -/

def muladd {N : Nat} (x y : ZMod N) : Free CircOp HintS (ZMod N) := pure (x * y + x)

def multiExample (a b : ZMod 5) : Free CircOp HintS (ZMod 5) := do
  let p ← muladd a b
  let q ← muladd b a
  pure (p + q)

reflect_def multiC := multiExample
/-- info: Freigen.multiC_sound (a b : ZMod 5) :
  ITree.Eutt (denoteProg (multiC (KC CircOp) Tp.denote) (HList.cons a (HList.cons b HList.nil)))
    (ofFree (multiExample a b)) -/
#guard_msgs (whitespace := lax) in
#check multiC_sound

-- One two-argument def (`muladd` at 5), called twice.
/-- info:
def muladd(x0 : Field<5>, x1 : Field<5>) =>
  let v2 := x0 * x1
  let v3 := v2 + x0
  v3
def main(x4 : Field<5>, x5 : Field<5>) =>
  let v6 := muladd(x4, x5)
  let v7 := muladd(x5, x4)
  let v8 := v6 + v7
  v8
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc multiC)

/-! ## A vector-valued result

`Vector α n` is a first-class object type (`Tp.vec`); a closed vector literal reflects as one `lit`. -/

def vecConst : Free CircOp HintS (Vector Nat 3) := pure ⟨#[1, 2, 3], rfl⟩

reflect_def vecC := vecConst
/-- info: Freigen.vecC_sound : ITree.Eutt (denoteProg (vecC (KC CircOp) Tp.denote) HList.nil) (ofFree vecConst) -/
#guard_msgs (whitespace := lax) in
#check vecC_sound

-- The vector prints as `#v[…]`.
/-- info:
def main() =>
  let v0 := #v[1, 2, 3]
  v0
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc vecC)

/-! ## Proof-erased collection get / set

`v[i]` / `v.set i x` reflect into the **partial-primitive node** `Code.pop` at ops
**`POp.vget`/`POp.vset`** (and `aget`/`aset` for `Array`).  The AST is *type-erased*: an index is a
bare `Nat` with **no in-bounds proof**, so the denotation of a get/set **fails** (`ITree.fail`) out
of range.

Reflection is still `≈`-sound because the *source* side carries the proof (`v[i]` elaborates
`getElem … h`).  Crucially the index need **not** be a literal: an in-bounds proof `h : j < n` that
accompanies a *symbolic* index `j` is not a reifiable input, so `reflect%` **erases it from the AST
and keeps it as a hypothesis of the soundness statement** — and the erased node's `fail` branch is
discharged by that hypothesis (`h` rewrites `j < n ↦ True`, `reduceDIte` collapses the branch).  *One
side has the proof, so the read/write cannot actually fail.* -/

/-- Read a **symbolic** slot `j` (with erased in-bounds proof `h : j < 3`) and slot `0`, then add. -/
def vgetSym (v : Vector Nat 3) (j : Nat) (h : j < 3) : Free CircOp HintS Nat := pure (v[j]'h + v[0])

reflect_def vgetSymC := vgetSym
-- `h` is quantified in the soundness statement but is **absent** from the reflected `main`.
/-- info: Freigen.vgetSymC_sound (v : Vector ℕ 3) (j : ℕ) (h : j < 3) :
  ITree.Eutt (denoteProg (vgetSymC (KC CircOp) Tp.denote) (HList.cons v (HList.cons j HList.nil)))
    (ofFree (vgetSym v j h)) -/
#guard_msgs (whitespace := lax) in
#check vgetSymC_sound

-- `main` takes only the vector and the index — no proof argument.
/-- info:
def main(x0 : Vector<Nat, 3>, x1 : Nat) =>
  let v2 := x0[x1]
  let v3 := 0
  let v4 := x0[v3]
  let v5 := v2 + v4
  v5
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc vgetSymC)

/-- Write a value into symbolic slot `j` (`vset`), then read the same slot back (`vget`). -/
def vsetSym (v : Vector Nat 3) (j : Nat) (h : j < 3) (x : Nat) : Free CircOp HintS Nat := do
  let w := v.set j x
  pure (w[j]'h)

reflect_def vsetSymC := vsetSym
/-- info: Freigen.vsetSymC_sound (v : Vector ℕ 3) (j : ℕ) (h : j < 3) (x : ℕ) :
  ITree.Eutt (denoteProg (vsetSymC (KC CircOp) Tp.denote) (HList.cons v (HList.cons j (HList.cons x HList.nil))))
    (ofFree (vsetSym v j h x)) -/
#guard_msgs (whitespace := lax) in
#check vsetSymC_sound

/-- info:
def main(x0 : Vector<Nat, 3>, x1 : Nat, x2 : Nat) =>
  let v3 := x0 with [x1] := x2
  let v4 := v3[x1]
  v4
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc vsetSymC)

/-- A **dynamically-sized** `Array` read: the bound `j < a.size` is itself symbolic, yet the erased
    `aget` is still sound because the source proof `h` rules the failure out. -/
def agetSym (a : Array Nat) (j : Nat) (h : j < a.size) : Free CircOp HintS Nat := pure (a[j]'h)

reflect_def agetSymC := agetSym
/-- info: Freigen.agetSymC_sound (a : Array ℕ) (j : ℕ) (h : j < a.size) :
  ITree.Eutt (denoteProg (agetSymC (KC CircOp) Tp.denote) (HList.cons a (HList.cons j HList.nil)))
    (ofFree (agetSym a j h)) -/
#guard_msgs (whitespace := lax) in
#check agetSymC_sound

/-- info:
def main(x0 : Array<Nat>, x1 : Nat) =>
  let v2 := x0[x1]
  v2
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc agetSymC)

/-- **Read-after-write on a dynamic array**: `(a.set i x)[i]` — the get's collection is itself the
    `aset` node.  The array bound `i < (a.set i x).size` references that compound collection; soundness
    still discharges it because the `aset` node's continuation binds its result to the *concrete*
    `a.set i x`, against which the get's source proof fits. -/
def arrRW (a : Array Nat) (i : Nat) (h : i < a.size) (x : Nat) : Free CircOp HintS Nat := do
  let b := a.set i x
  pure (b[i]'(by rw [Array.size_set]; exact h))

reflect_def arrRWC := arrRW
/-- info: Freigen.arrRWC_sound (a : Array ℕ) (i : ℕ) (h : i < a.size) (x : ℕ) :
  ITree.Eutt (denoteProg (arrRWC (KC CircOp) Tp.denote) (HList.cons a (HList.cons i (HList.cons x HList.nil))))
    (ofFree (arrRW a i h x)) -/
#guard_msgs (whitespace := lax) in
#check arrRWC_sound

/-- info:
def main(x0 : Array<Nat>, x1 : Nat, x2 : Nat) =>
  let v3 := x0 with [x1] := x2
  let v4 := v3[x1]
  v4
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc arrRWC)

/-! ### Deeper in the tree

A get/set need not sit at the top of `main`.  The compositional proof inserts the source's in-bounds
proof *at the get's node*, wherever it is — buried under effects and branches, spilled inside a helper
`def_`, or flowing as the argument of a helper call.  No node's soundness depends on any other. -/

/-- A **spilled helper** indexing its own vector argument: the `vget` lives inside `f0`'s `def_`, and
    its decidable bounds (`0 < 4`, `3 < 4`) are discharged in the generic helper soundness. -/
def firstPlusLast (v : Vector Nat 4) : Free CircOp HintS Nat := pure (v[0] + v[3])
def twice (v : Vector Nat 4) : Free CircOp HintS Nat := do
  let a ← firstPlusLast v
  let b ← firstPlusLast v
  pure (a + b)

reflect_def twiceC := twice
/-- info: Freigen.twiceC_sound (v : Vector ℕ 4) :
  ITree.Eutt (denoteProg (twiceC (KC CircOp) Tp.denote) (HList.cons v HList.nil)) (ofFree (twice v)) -/
#guard_msgs (whitespace := lax) in
#check twiceC_sound

/-- info:
def firstPlusLast(x0 : Vector<Nat, 4>) =>
  let v1 := 0
  let v2 := x0[v1]
  let v3 := 3
  let v4 := x0[v3]
  let v5 := v2 + v4
  v5
def main(x6 : Vector<Nat, 4>) =>
  let v7 := firstPlusLast(x6)
  let v8 := firstPlusLast(x6)
  let v9 := v7 + v8
  v9
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc twiceC)

/-- A **symbolic-bound array** get buried under an effect *and* inside a `bif` branch: the main-level
    proof `h : j < a.size` still rules the failure out, through the `assert`'s `vis` and the branch. -/
def deepArr (a : Array Nat) (j : Nat) (h : j < a.size) (b : Bool) : Free CircOp HintS Nat := do
  let _ ← assert b
  bif b then pure (a[j]'h) else pure 0

reflect_def deepArrC := deepArr
/-- info: Freigen.deepArrC_sound (a : Array ℕ) (j : ℕ) (h : j < a.size) (b : Bool) :
  ITree.Eutt (denoteProg (deepArrC (KC CircOp) Tp.denote) (HList.cons a (HList.cons j (HList.cons b HList.nil))))
    (ofFree (deepArr a j h b)) -/
#guard_msgs (whitespace := lax) in
#check deepArrC_sound

/-- info:
def main(x0 : Array<Nat>, x1 : Nat, x2 : Bool) =>
  let v3 ← assert(x2)
  if x2 then
    let v4 := x0[x1]
    v4
  else
    let v5 := 0
    v5
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc deepArrC)

/-- A **symbolic get flowing as the argument of a helper call** (`quad (v[j]'h)`): the get is reflected
    at the call site and its bound is discharged there, while `quad` spills as `f0` — the compositional
    proof composes the call with `quad`'s own soundness. -/
def viaHelper (v : Vector Nat 3) (j : Nat) (h : j < 3) : Free CircOp HintS Unit := do
  let q ← quad (v[j]'h)
  assert (q == 0)

reflect_def viaHelperC := viaHelper
/-- info: Freigen.viaHelperC_sound (v : Vector ℕ 3) (j : ℕ) (h : j < 3) :
  ITree.Eutt (denoteProg (viaHelperC (KC CircOp) Tp.denote) (HList.cons v (HList.cons j HList.nil)))
    (ofFree (viaHelper v j h)) -/
#guard_msgs (whitespace := lax) in
#check viaHelperC_sound

/-- info:
def double(x0 : Nat) =>
  let v1 := x0 + x0
  v1
def quad(x2 : Nat) =>
  let v3 := double(x2)
  let v4 := double(v3)
  v4
def main(x5 : Vector<Nat, 3>, x6 : Nat) =>
  let v7 := x5[x6]
  let v8 := quad(v7)
  let v9 := 0
  let v10 := v8 == v9
  let v11 ← assert(v10)
  v11
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc viaHelperC)

/-! ### Constructing collections

`#v[…]` / `⟨#[…], _⟩` literals build a `Vector` from *computed* elements — reflected into the
`vec` construction node (`#[…]` → `arr`).  `Vector.ofFn (fun i : Fin n => …)` is a **kept lane
loop** (a `vgen` node — never unrolled), and `Fin`-indexed access `v[i]` becomes `v[i.val]`. -/

/-- Build a new vector by doubling each lane of the input (`Vector.ofFn` + `Fin`-indexed reads). -/
def vdouble (v : Vector Nat 3) : Free CircOp HintS (Vector Nat 3) :=
  pure (Vector.ofFn (fun i : Fin 3 => v[i] + v[i]))

reflect_def vdoubleC := vdouble
/-- info: Freigen.vdoubleC_sound (v : Vector ℕ 3) :
  ITree.Eutt (denoteProg (vdoubleC (KC CircOp) Tp.denote) (HList.cons v HList.nil)) (ofFree (vdouble v)) -/
#guard_msgs (whitespace := lax) in
#check vdoubleC_sound

/-- info:
def main(x0 : Vector<Nat, 3>) =>
  let v7 := gen 3 with (i1 : Fin<3>) =>
    let v2 := .val i1
    let v3 := x0[v2]
    let v4 := .val i1
    let v5 := x0[v4]
    let v6 := v3 + v5
    v6
  v7
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc vdoubleC)

/-! ### Casts between representations

A refinement conversion the *source* performs is reflected into a **cast** node.  Downcasts
(`v.toArray`, `i.val`) are total `un` ops.  Upcasts (`array → vec n`, `nat → fin n`) are proof-erased
and **partial** — a size/bound mismatch fails in the denotation — but infallible in any reflected
program, because the source's own proof (`arr.size = n` / `k < n`) closes the branch (`dif_pos`),
exactly as for a get.  `Fin` is a first-class object type, so a `Fin` may be an input or a value. -/

/-- `array → vec` upcast: rebuild a length-`3` vector from a runtime array + its size proof. -/
def castAV (arr : Array Nat) (h : arr.size = 3) : Free CircOp HintS (Vector Nat 3) := pure ⟨arr, h⟩

reflect_def castAVC := castAV
/-- info: Freigen.castAVC_sound (arr : Array ℕ) (h : arr.size = 3) :
  ITree.Eutt (denoteProg (castAVC (KC CircOp) Tp.denote) (HList.cons arr HList.nil)) (ofFree (castAV arr h)) -/
#guard_msgs (whitespace := lax) in
#check castAVC_sound

/-- info:
def main(x0 : Array<Nat>) =>
  let v1 := x0 as Vector<_, 3>
  v1
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc castAVC)

/-- `nat → fin` upcast, and a `Fin` **input** downcast back to `Nat` (`i.val`). -/
def castNF (k : Nat) (h : k < 5) (i : Fin 5) : Free CircOp HintS (Fin 5 × Nat) :=
  pure (⟨k, h⟩, i.val)

reflect_def castNFC := castNF
/-- info: Freigen.castNFC_sound (k : ℕ) (h : k < 5) (i : Fin 5) :
  ITree.Eutt (denoteProg (castNFC (KC CircOp) Tp.denote) (HList.cons k (HList.cons i HList.nil)))
    (ofFree (castNF k h i)) -/
#guard_msgs (whitespace := lax) in
#check castNFC_sound

/-- info:
def main(x0 : Nat, x1 : Fin<5>) =>
  let v2 := x0 as Fin<5>
  let v3 := .val x1
  let v4 := (v2, v3)
  v4
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc castNFC)

open Freigen.ITree in
/-- The partial upcasts fail on a mismatch, directly. -/
example : denote (Op := CircOp) (SOp := HintS)
    (Code.pop (.arrToVec (a := .nat) (n := 3)) (.cons (#[10, 20] : Array Nat) .nil)
      (fun v => .ret v)) = fail := rfl
open Freigen.ITree in
example : denote (Op := CircOp) (SOp := HintS)
    (Code.pop (.natToFin (n := 5)) (.cons 7 .nil) (fun i => .ret i)) = fail := rfl

/-! ### The failing denotation, directly

The erased get/set ops fail out of range and return the element in range — the property the
reflector's soundness relies on the source proof to rule out.  (`Array` shares the same
`aget`/`aset` machinery; its size is dynamic, so these are shown on closed literals.) -/

open Freigen.ITree in
/-- An out-of-range `vget` denotes to `fail`. -/
example : denote (Op := CircOp) (SOp := HintS)
    (Code.pop (.vget (a := .nat) (n := 3)) (.cons ⟨#[10, 20, 30], rfl⟩ (.cons 5 .nil))
      (fun x => .ret x)) = fail := by
  simp only [denote, POp.denote, Nat.reduceLT, reduceDIte]

open Freigen.ITree in
/-- An in-range `aget` returns the element; an out-of-range one fails. -/
example : denote (Op := CircOp) (SOp := HintS)
    (Code.pop (.aget (a := .nat)) (.cons (#[10, 20, 30] : Array Nat) (.cons 1 .nil))
      (fun x => .ret x)) = ret 20 := rfl

open Freigen.ITree in
example : denote (Op := CircOp) (SOp := HintS)
    (Code.pop (.aget (a := .nat)) (.cons (#[10, 20, 30] : Array Nat) (.cons 7 .nil))
      (fun x => .ret x)) = fail := rfl

/-! ### Loops with effectful bodies

The `fold` node is **body-agnostic**: `Fin.foldlM` over the `Free` monad reflects to the *same*
loop node with effects inside the body — an `assert` per iteration, or even a scoped `hint`
block.  The loop is kept as control flow either way; nothing is unrolled. -/

/-- Assert every lane equals its index while summing the lanes — an `assert` per iteration. -/
def sumChecked (v : Vector Nat 3) : Free CircOp HintS Nat :=
  Fin.foldlM 3 (fun acc i => do
    let _ ← assert (v[i] == i.val)
    pure (acc + v[i])) 0

reflect_def sumCheckedC := sumChecked
/-- info: Freigen.sumCheckedC_sound (v : Vector ℕ 3) :
  ITree.Eutt (denoteProg (sumCheckedC (KC CircOp) Tp.denote) (HList.cons v HList.nil)) (ofFree (sumChecked v)) -/
#guard_msgs (whitespace := lax) in
#check sumCheckedC_sound

/-- info:
def main(x0 : Vector<Nat, 3>) =>
  let v1 := 0
  let v12 := fold 3 from v1 with (i2 : Fin<3>, a3) =>
    let v4 := .val i2
    let v5 := x0[v4]
    let v6 := .val i2
    let v7 := v5 == v6
    let v8 ← assert(v7)
    let v9 := .val i2
    let v10 := x0[v9]
    let v11 := a3 + v10
    v11
  v12
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc sumCheckedC)

/-- A **scoped `hint` block inside the loop body**, its witness constrained each iteration. -/
def hintLoop : Free CircOp HintS Nat :=
  Fin.foldlM 4 (fun acc _ => do
    let h ← hint (pure (acc + 1))
    let _ ← assert (h == acc + 1)
    pure h) 0

reflect_def hintLoopC := hintLoop
/-- info: Freigen.hintLoopC_sound :
  ITree.Eutt (denoteProg (hintLoopC (KC CircOp) Tp.denote) HList.nil) (ofFree hintLoop) -/
#guard_msgs (whitespace := lax) in
#check hintLoopC_sound

/-- info: some 4 -/
#guard_msgs in #eval runCirc hintLoop

/-- info:
def main() =>
  let v0 := 0
  let v10 := fold 4 from v0 with (i1 : Fin<4>, a2) =>
    let v5 ← hint unconstrained
      let v3 := 1
      let v4 := a2 + v3
      v4
    let v6 := 1
    let v7 := a2 + v6
    let v8 := v5 == v7
    let v9 ← assert(v8)
    v5
  v10
-/
#guard_msgs (whitespace := lax) in #eval IO.println (ppCirc hintLoopC)

end Freigen
