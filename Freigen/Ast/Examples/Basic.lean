import Freigen.Ast.Print

/-!
A small language used by AST tests, and sample programs exercising
every construct. The programs are only type-checked: evaluating through
`CompM` is far too slow to serve as a test harness, so their behaviour is
checked by proofs in later stages.
-/

namespace Freigen.Ast.Examples

/-! ## Test language -/

inductive Scope
| main
| hint
deriving DecidableEq

/-- Operations available in `main`. `hint` runs its block in the `hint`
context and returns the block's result. -/
inductive MainOp
| print
| input
| hint

abbrev Tag : Scope → Type
| .main => MainOp
| .hint => Empty

def language : Language where
  Ctx := Scope
  Base := Empty
  abi := nofun
  Prim := fun _ _ => Empty
  Op := Tag
  input := fun
    | .main, .print => .uInt32
    | .main, .input => .unit
    | .main, .hint => .uInt32
    | .hint, e => nomatch e
  output := fun
    | .main, .print => .unit
    | .main, .input => .uInt32
    | .main, .hint => .uInt32
    | .hint, e => nomatch e
  Block := fun
    | .main, .hint => Unit
    | .main, .print => Empty
    | .main, .input => Empty
    | .hint, e => nomatch e
  blockCtx := fun
    | .main, .hint, _ => .hint
    | .main, .print, b => nomatch b
    | .main, .input, b => nomatch b
    | .hint, e, _ => nomatch e
  blockInputs := fun
    | .main, .hint, _ => .uInt32
    | .main, .print, b => nomatch b
    | .main, .input, b => nomatch b
    | .hint, e, _ => nomatch e
  blockOutputs := fun
    | .main, .hint, _ => .uInt32
    | .main, .print, b => nomatch b
    | .main, .input, b => nomatch b
    | .hint, e, _ => nomatch e

/-- The test language has no base types or primitives, so its model is
trivial. -/
def model : language.Model where
  denote := nofun
  prim := nofun

instance : Language.Print language where
  baseSexp := nofun
  primSexp := nofun
  ctxName
    | .main => "main"
    | .hint => "hint"
  opSexp := fun
    | .main, .print => .atom "print"
    | .main, .input => .atom "input"
    | .main, .hint => .atom "hint"
    | .hint, e => nomatch e
  blocks := fun
    | .main, .hint => [()]
    | .main, .print => []
    | .main, .input => []
    | .hint, e => nomatch e
  blockName := fun
    | .main, .hint, _ => "body"
    | .main, .print, b => nomatch b
    | .main, .input, b => nomatch b
    | .hint, e, _ => nomatch e

/-! ## Programs -/

section
variable {V : language.Tp → Type} {out : language.Tp}

def print (x : V .uInt32) (k : V .unit → Expr language V Scope.main out) :
    Expr language V Scope.main out :=
  Expr.op (L := language) (γ := Scope.main) MainOp.print x (fun b => Empty.elim b) k

def input (u : V .unit) (k : V .uInt32 → Expr language V Scope.main out) :
    Expr language V Scope.main out :=
  Expr.op (L := language) (γ := Scope.main) MainOp.input u (fun b => Empty.elim b) k

def hint (x : V .uInt32) (body : V .uInt32 → Expr language V Scope.hint .uInt32)
    (k : V .uInt32 → Expr language V Scope.main out) :
    Expr language V Scope.main out :=
  Expr.op (L := language) (γ := Scope.main) MainOp.hint x (fun () => body) k

/-- Read two numbers, print and return their sum. -/
def addInputs : Program language Scope.main .unit .uInt32 V :=
  .main fun u =>
    input u fun x =>
    input u fun y =>
    .builtin .uAdd h![x, y] fun s =>
    print s fun _ =>
    .ret s

/-- A helper definition called twice. -/
def doubleTwice : Program language Scope.main .uInt32 .uInt32 V :=
  .define (γ := (Scope.main : Scope)) (inp := .uInt32) (out := .uInt32)
    (fun _self x => .builtin .uAdd h![x, x] .ret) fun double =>
  .main fun x =>
    .app double x fun y =>
    .app double y .ret

/-- Square the input inside a hint block. -/
def hintSquare : Program language Scope.main .uInt32 .uInt32 V :=
  .main fun x =>
    hint x (fun y => .builtin .uMul h![y, y] .ret) .ret

/-- `max` of a pair, via branching and projections. -/
def maxPair : Program language Scope.main (.prod .uInt32 .uInt32) .uInt32 V :=
  .main fun p =>
    .builtin .fst h![p] fun a =>
    .builtin .snd h![p] fun b =>
    .builtin .uLt h![a, b] fun c =>
    .ite c (.ret b) (.ret a) .ret

/-- Sum `1 + … + n` with a loop over `(i, acc)`. -/
def sumTo : Program language Scope.main .uInt32 .uInt32 V :=
  .main fun n =>
    .lit .uInt32 0 fun zero =>
    .builtin .pair h![zero, zero] fun init =>
    .loop (c := .prod .uInt32 .uInt32)
      (fun st =>
        .builtin .fst h![st] fun i =>
        .builtin .snd h![st] fun acc =>
        .lit .uInt32 1 fun one =>
        .builtin .uAdd h![i, one] fun i' =>
        .builtin .uAdd h![acc, i'] fun acc' =>
        .builtin .pair h![i', acc'] fun st' =>
        .builtin .uLt h![i', n] fun more =>
        .builtin .pair h![st', more] .ret)
      init fun st =>
    .builtin .snd h![st] .ret

/-- Build `#[x, x + 1]` and read the element at index `i`. -/
def arrayGet : Program language Scope.main (.prod .uInt32 .uInt32) .uInt32 V :=
  .main fun p =>
    .builtin .fst h![p] fun x =>
    .builtin .snd h![p] fun i =>
    .lit .uInt32 1 fun one =>
    .builtin .uAdd h![x, one] fun y =>
    .builtin (.arrEmpty (a := .uInt32)) h![] fun e =>
    .builtin .arrPush h![e, x] fun a =>
    .builtin .arrPush h![a, y] fun a =>
    .builtin .arrGet h![a, i] .ret

/-- Locally created closures. -/
def lamApply : Program language Scope.main .uInt32 .uInt32 V :=
  .main fun x =>
    .lam (inp := .uInt32) (out := .uInt32)
      (fun y => .builtin .uMul h![y, x] .ret) fun f =>
    .app f x .ret

end

/-! ## Builtin semantics -/

#guard (Builtin.uAdd (L := language)).denote model h![(0xFFFFFFFF : UInt32), 1] == some 0
#guard (Builtin.uDiv (L := language)).denote model h![(7 : UInt32), 0] == some 0
#guard (Builtin.uMod (L := language)).denote model h![(7 : UInt32), 0] == some 7
#guard (Builtin.uLt (L := language)).denote model h![(3 : UInt32), 9] == some true
#guard ((Builtin.pair (L := language) (a := .uInt32) (b := .bool))).denote model h![3, true] == some (3, true)
#guard ((Builtin.arrGet (L := language) (a := .uInt32))).denote model h![#[7, 8], 1] == some 8
#guard ((Builtin.arrGet (L := language) (a := .uInt32))).denote model h![#[7, 8], 2] == none
#guard ((Builtin.arrSet (L := language) (a := .uInt32))).denote model h![#[7, 8], 0, 5] == some #[5, 8]
#guard ((Builtin.arrSet (L := language) (a := .uInt32))).denote model h![#[7, 8], 2, 5] == none
#guard ((Builtin.arrLen (L := language) (a := .bool))).denote model h![#[true, false]] == some 2

end Freigen.Ast.Examples
