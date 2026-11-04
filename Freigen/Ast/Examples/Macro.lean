import Freigen.Ast.Macro
import Freigen.Ast.Examples.Cert

/-!
Programs lifted by the macro. The four stage 4 programs are regenerated and
compared with their hand-written ASTs. Every generated AST is pinned in its
printed form, as are the axioms of the certificates and the errors for
rejected sources.
-/

namespace Freigen.Ast.Examples

/-! ## The stage 4 programs -/

lift_program liftedPoly := srcPoly
lift_program liftedBranch := srcBranch ops [srcPrint]
lift_program liftedHintSquare := srcHintSquare ops [srcHint]
lift_program liftedDoubleTwice := srcDoubleTwice using [srcDouble]

example : ProgramCert (idHandler sig) liftedPoly.ast srcPoly := liftedPoly.cert

example : @liftedPoly.ast = @poly := rfl
example : @liftedBranch.ast = @branch := rfl
example : @liftedHintSquare.ast = @hintSquare := rfl
example : @liftedDoubleTwice.ast = @doubleTwice := rfl

/--
info: (program
  (main main (v0 u32) u32 (let v1 (uMul v0 v0)) (let v2 (uAdd v0 v1)) (ret v2)))
-/
#guard_msgs in #eval IO.println liftedPoly.ast.pretty

/--
info: (program
  (main main (v0 bool) u32
    (let f1 (fun (v2 unit) (let v3 (lit u32 3)) (ret v3)))
    (let v4
      (if v0
        (do
          (let v5 (lit u32 1))
          (let v6 (op print v5))
          (let v7 (app f1 v6))
          (ret v7))
        (do
          (let v8 (lit u32 2))
          (let v9 (op print v8))
          (let v10 (app f1 v9))
          (ret v10))))
    (ret v4)))
-/
#guard_msgs in #eval IO.println liftedBranch.ast.pretty

/--
info: (program
  (main main (v0 u32) u32
    (let v1 (op hint v0 (block body (v2) (let v3 (uMul v2 v2)) (ret v3))))
    (ret v1)))
-/
#guard_msgs in #eval IO.println liftedHintSquare.ast.pretty

/--
info: (program
  (define f0 main (v1 u32) u32 (let v2 (uAdd v1 v1)) (ret v2))
  (main main (v3 u32) u32 (let v4 (app f0 v3)) (let v5 (app f0 v4)) (ret v5)))
-/
#guard_msgs in #eval IO.println liftedDoubleTwice.ast.pretty

/-! ## More programs -/

def srcInput : Src .main UInt32 :=
  Free.op (E := sig.denote) (γ := Scope.main) ⟨MainOp.input, ()⟩ nofun

/-- Maximum of a pair: projections, a comparison, and a branch. -/
def srcMax (p : UInt32 × UInt32) : Src .main UInt32 :=
  if decide (p.1 < p.2) then pure p.2 else pure p.1

lift_program liftedMax := srcMax

/--
info: (program
  (main main (v0 (prod u32 u32)) u32
    (let v1 (fst v0))
    (let v2 (snd v0))
    (let v3 (uLt v1 v2))
    (let v4
      (if v3 (do (let v5 (snd v0)) (ret v5)) (do (let v6 (fst v0)) (ret v6))))
    (ret v4)))
-/
#guard_msgs in #eval IO.println liftedMax.ast.pretty

def srcInc (x : UInt32) : Src .main UInt32 := pure (x + 1)

def srcIncTwice (x : UInt32) : Src .main UInt32 := do
  let y ← srcInc x
  srcInc y

/-- A chain of helpers, one calling another. -/
def srcChain (x : UInt32) : Src .main UInt32 := do
  let y ← srcIncTwice x
  let z ← srcInc y
  pure (y * z)

lift_program liftedChain := srcChain using [srcInc, srcIncTwice]

/--
info: (program
  (define f0 main (v1 u32) u32
    (let v2 (lit u32 1))
    (let v3 (uAdd v1 v2))
    (ret v3))
  (define f4 main (v5 u32) u32
    (let v6 (app f0 v5))
    (let v7 (app f0 v6))
    (ret v7))
  (main main (v8 u32) u32
    (let v9 (app f4 v8))
    (let v10 (app f0 v9))
    (let v11 (uMul v9 v10))
    (ret v11)))
-/
#guard_msgs in #eval IO.println liftedChain.ast.pretty

/-- Effects inside branches, a block, and sequential branches. -/
def srcLog (x : UInt32) : Src .main UInt32 := do
  if x == 0 then srcPrint 0 else srcPrint x
  let y ← srcHint x fun v => pure (v * v)
  if decide (y < 100) then srcPrint y else pure ()
  pure y

lift_program liftedLog := srcLog ops [srcPrint, srcHint]

/--
info: (program
  (main main (v0 u32) u32
    (let f1
      (fun (v2 unit)
        (let v3 (op hint v0 (block body (v4) (let v5 (uMul v4 v4)) (ret v5))))
        (let f6 (fun (v7 unit) (ret v3)))
        (let v8 (lit u32 100))
        (let v9 (uLt v3 v8))
        (let v10
          (if v9
            (do (let v11 (op print v3)) (let v12 (app f6 v11)) (ret v12))
            (do (let v13 (lit unit ())) (let v14 (app f6 v13)) (ret v14))))
        (ret v10)))
    (let v15 (lit u32 0))
    (let v16 (uEq v0 v15))
    (let v17
      (if v16
        (do
          (let v18 (lit u32 0))
          (let v19 (op print v18))
          (let v20 (app f1 v19))
          (ret v20))
        (do (let v21 (op print v0)) (let v22 (app f1 v21)) (ret v22))))
    (ret v17)))
-/
#guard_msgs in #eval IO.println liftedLog.ast.pretty

/-- Reading input, with a raw operation and a pair result. -/
def srcReadPair (_ : Unit) : Src .main (UInt32 × Bool) := do
  let a ← srcInput
  let b ← srcInput
  pure (a + b, a == b && !(b == 0))

lift_program liftedReadPair := srcReadPair ops [srcInput]

/--
info: (program
  (main main (v0 unit) (prod u32 bool)
    (let v1 (lit unit ()))
    (let v2 (op input v1))
    (let v3 (lit unit ()))
    (let v4 (op input v3))
    (let v5 (uAdd v2 v4))
    (let v6 (uEq v2 v4))
    (let v7 (lit u32 0))
    (let v8 (uEq v4 v7))
    (let v9 (not v8))
    (let v10 (and v6 v9))
    (let v11 (pair v5 v10))
    (ret v11)))
-/
#guard_msgs in #eval IO.println liftedReadPair.ast.pretty

/-- A subterm the source repeats is translated each time. -/
def srcSquares (x : UInt32) : Src .main UInt32 := pure (x * x + x * x)

lift_program liftedSquares := srcSquares

/--
info: (program
  (main main (v0 u32) u32
    (let v1 (uMul v0 v0))
    (let v2 (uMul v0 v0))
    (let v3 (uAdd v1 v2))
    (ret v3)))
-/
#guard_msgs in #eval IO.println liftedSquares.ast.pretty

/-- A branch followed by a bind, written without `do`. -/
def srcIteBind (c : Bool) : Src .main UInt32 :=
  (if c then pure 1 else pure 2) >>= fun x => pure (x + x)

lift_program liftedIteBind := srcIteBind

/--
info: (program
  (main main (v0 bool) u32
    (let v1
      (if v0
        (do (let v2 (lit u32 1)) (ret v2))
        (do (let v3 (lit u32 2)) (ret v3))))
    (let v4 (uAdd v1 v1))
    (ret v4)))
-/
#guard_msgs in #eval IO.println liftedIteBind.ast.pretty

/-- A continuation that is a function, not a lambda. -/
def srcEta (x : UInt32) : Src .main UInt32 := srcInc x >>= srcInc

lift_program liftedEta := srcEta using [srcInc]

/--
info: (program
  (define f0 main (v1 u32) u32
    (let v2 (lit u32 1))
    (let v3 (uAdd v1 v2))
    (ret v3))
  (main main (v4 u32) u32 (let v5 (app f0 v4)) (let v6 (app f0 v5)) (ret v6)))
-/
#guard_msgs in #eval IO.println liftedEta.ast.pretty

/-- Boolean and unit literals, and a pair. -/
def srcFlags (b : Bool) : Src .main (Bool × Unit) := pure (b && true, ())

lift_program liftedFlags := srcFlags

/--
info: (program
  (main main (v0 bool) (prod bool unit)
    (let v1 (lit bool true))
    (let v2 (and v0 v1))
    (let v3 (lit unit ()))
    (let v4 (pair v2 v3))
    (ret v4)))
-/
#guard_msgs in #eval IO.println liftedFlags.ast.pretty

/-- Arrays: the empty array, push, and length. -/
def srcArr (x : UInt32) : Src .main UInt32 :=
  pure ((#[] : Array UInt32).push x).size.toUInt32

lift_program liftedArr := srcArr

/--
info: (program
  (main main (v0 u32) u32
    (let v1 (arrEmpty u32))
    (let v2 (arrPush v1 v0))
    (let v3 (arrLen v2))
    (ret v3)))
-/
#guard_msgs in #eval IO.println liftedArr.ast.pretty

/-! ## Axioms -/

/-- info: 'Freigen.Ast.Examples.liftedPoly.cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms liftedPoly.cert

/-- info: 'Freigen.Ast.Examples.liftedLog.cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms liftedLog.cert

/-- info: 'Freigen.Ast.Examples.liftedChain.cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms liftedChain.cert

/-! ## Rejected sources -/

def srcBadProp (x : UInt32) : Src .main UInt32 :=
  if x < 3 then pure 1 else pure 2

/--
error: lift: no rule matches this form; conditions must be booleans: write `decide (x < y)` rather than `x < y`
  if x < 3 then pure 1 else pure 2
-/
#guard_msgs in lift_program badProp := srcBadProp

def srcBadMatch (p : UInt32 × UInt32) : Src .main UInt32 :=
  let (a, b) := p
  pure (a + b)

/--
error: lift: pattern matching (including destructuring) is not supported
  match p with
  | (a, b) => pure (a + b)
-/
#guard_msgs in lift_program badMatch := srcBadMatch

/--
error: lift: call to `Freigen.Ast.Examples.srcInc`, which is neither a listed helper nor an operation
  srcInc x
-/
#guard_msgs in lift_program badCall := srcIncTwice

def myDouble (a : UInt32) : UInt32 := a + a

def srcBadUserDef (x : UInt32) : Src .main UInt32 := pure (myDouble x)

-- Matching never sees through user definitions, even ones that unfold to a
-- builtin.
/--
error: lift: unsupported value
  myDouble x
-/
#guard_msgs in lift_program badUserDef := srcBadUserDef

def srcBadMut (c : Bool) : Src .main UInt32 := do
  let mut a : UInt32 := 0
  if c then a := 1 else a := 3
  pure (a + a)

/--
error: lift: join points with several arguments are not supported; they come from mutable variables
  fun a y => pure (a + a)
-/
#guard_msgs in lift_program badMut := srcBadMut

end Freigen.Ast.Examples
