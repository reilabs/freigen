import Freigen.Ast.Macro
import Freigen.Ast.Examples.Cert

/-!
Programs lifted by the macro. The four stage 4 programs are regenerated and
compared with their hand-written ASTs; further programs pin the generated
ASTs, the axioms of the certificates, and the errors for rejected sources.
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

/-! ## More programs -/

def srcInput : Src .main UInt32 :=
  Free.op (E := sig.denote) (γ := Scope.main) ⟨MainOp.input, ()⟩ nofun

/-- Maximum of a pair: projections, a comparison, and a branch. -/
def srcMax (p : UInt32 × UInt32) : Src .main UInt32 :=
  if decide (p.1 < p.2) then pure p.2 else pure p.1

lift_program liftedMax := srcMax

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

/-- Effects inside branches, a block, and sequential branches. -/
def srcLog (x : UInt32) : Src .main UInt32 := do
  if x == 0 then srcPrint 0 else srcPrint x
  let y ← srcHint x fun v => pure (v * v)
  if decide (y < 100) then srcPrint y else pure ()
  pure y

lift_program liftedLog := srcLog ops [srcPrint, srcHint]

/-- Reading input, with a raw operation and a pair result. -/
def srcReadPair (_ : Unit) : Src .main (UInt32 × Bool) := do
  let a ← srcInput
  let b ← srcInput
  pure (a + b, a == b && !(b == 0))

lift_program liftedReadPair := srcReadPair ops [srcInput]

/-- A subterm the source repeats is translated each time. -/
def srcSquares (x : UInt32) : Src .main UInt32 := pure (x * x + x * x)

lift_program liftedSquares := srcSquares

example : @liftedSquares.ast = fun {V} =>
    (Program.main fun x =>
      .builtin .uMul h![x, x] fun a =>
      .builtin .uMul h![x, x] fun b =>
      .builtin .uAdd h![a, b] .ret : Program sig Scope.main .uInt32 .uInt32 V) := rfl

/-- A branch followed by a bind, written without `do`. -/
def srcIteBind (c : Bool) : Src .main UInt32 :=
  (if c then pure 1 else pure 2) >>= fun x => pure (x + x)

lift_program liftedIteBind := srcIteBind

example : @liftedIteBind.ast = fun {V} =>
    (Program.main fun c =>
      .ite c (.lit .uInt32 1 .ret) (.lit .uInt32 2 .ret) fun x =>
      .builtin .uAdd h![x, x] .ret : Program sig Scope.main .bool .uInt32 V) := rfl

/-- A continuation that is a function, not a lambda. -/
def srcEta (x : UInt32) : Src .main UInt32 := srcInc x >>= srcInc

lift_program liftedEta := srcEta using [srcInc]

example : @liftedEta.ast = fun {V} =>
    (Program.define (γ := Scope.main) (inp := .uInt32) (out := .uInt32)
        (fun _ x => .lit .uInt32 1 fun one => .builtin .uAdd h![x, one] .ret) fun inc =>
      Program.main fun x =>
        .app inc x fun y =>
        .app inc y .ret : Program sig Scope.main .uInt32 .uInt32 V) := rfl

/-- Boolean and unit literals, and a pair. -/
def srcFlags (b : Bool) : Src .main (Bool × Unit) := pure (b && true, ())

lift_program liftedFlags := srcFlags

example : @liftedFlags.ast = fun {V} =>
    (Program.main fun b =>
      .lit .bool true fun t =>
      .builtin .and h![b, t] fun c =>
      .lit .unit () fun u =>
      .builtin .pair h![c, u] .ret : Program sig Scope.main .bool (.prod .bool .unit) V) := rfl

/-- Arrays: the empty array, push, and length. -/
def srcArr (x : UInt32) : Src .main UInt32 :=
  pure ((#[] : Array UInt32).push x).size.toUInt32

lift_program liftedArr := srcArr

example : @liftedArr.ast = fun {V} =>
    (Program.main fun x =>
      .builtin (.arrEmpty (a := .uInt32)) h![] fun e =>
      .builtin .arrPush h![e, x] fun a =>
      .builtin .arrLen h![a] .ret : Program sig Scope.main .uInt32 .uInt32 V) := rfl

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
