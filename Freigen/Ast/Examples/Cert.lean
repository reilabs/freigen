import Freigen.Ast.Macro
import Freigen.Ast.Examples.Basic

/-!
Hand-written program certificates over the test language, built from the
certificate rules only. Sources are taken as elaborated, so these are the
reference output for the macro.
-/

namespace Freigen.Ast.Examples

/-! ## Source programs -/

abbrev Src (γ : Scope) (α : Type) := Free (language.denote model) γ α

def srcPrint (x : UInt32) : Src .main Unit :=
  Free.op (E := language.denote model) (γ := Scope.main) ⟨MainOp.print, x⟩ nofun

def srcHint (x : UInt32) (body : UInt32 → Src .hint UInt32) : Src .main UInt32 :=
  Free.op (E := language.denote model) (γ := Scope.main) ⟨MainOp.hint, x⟩ fun _ => body

def srcPoly (x : UInt32) : Src .main UInt32 :=
  let y := x * x
  pure (x + y)

/-- Elaborates to a join point for the code after the branch. -/
def srcBranch (c : Bool) : Src .main UInt32 := do
  if c then srcPrint 1 else srcPrint 2
  pure 3

def srcHintSquare (x : UInt32) : Src .main UInt32 :=
  srcHint x fun y => pure (y * y)

def srcDouble (x : UInt32) : Src .main UInt32 :=
  pure (x + x)

def srcDoubleTwice (x : UInt32) : Src .main UInt32 := do
  let y ← srcDouble x
  srcDouble y

/-! ## AST programs -/

section
variable {V : language.Tp → Type}

def poly : Program language Scope.main .uInt32 .uInt32 V :=
  .main fun x =>
    .builtin .uMul h![x, x] fun y =>
    .builtin .uAdd h![x, y] .ret

/-- The join point becomes a local closure, called from both branches. -/
def branch : Program language Scope.main .bool .uInt32 V :=
  .main fun c =>
    .lam (inp := .unit) (fun _ => .lit .uInt32 3 .ret) fun jp =>
    .ite c
      (.lit .uInt32 1 fun one => print one fun y => .app jp y .ret)
      (.lit .uInt32 2 fun two => print two fun y => .app jp y .ret)
      .ret

end

/-! ## Certificates -/

example : ProgramCert (Lift.id language model) (fun _ => .self _) poly srcPoly :=
  .of_progCert <| .main (fun x =>
    .builtin rfl <|
    .builtin rfl <|
    .ret rfl)

example : ProgramCert (Lift.id language model) (fun _ => .self _) branch srcBranch := by
  refine .of_progCert <| .main (fun _ =>
    .lam (Ri := Eq) (Ro := fun _ => Eq) (src := fun _ => pure 3)
      (fun _ _ _ => .lit (.ret rfl))
      fun _ _ _ hjp => ?_)
  refine .ite_tail ?_ ?_ <;>
  · refine .lit (tp := .uInt32) ?_
    refine .op_eq ?_ fun _ => ?_
    · exact fun b => nomatch b
    · exact .app_tail hjp rfl

example : ProgramCert (Lift.id language model) (fun _ => .self _) hintSquare srcHintSquare :=
  .of_progCert <| .main (fun _ =>
    .op_eq_tail fun _ _ =>
      .builtin rfl <|
      .ret rfl)

example : ProgramCert (Lift.id language model) (fun _ => .self _) doubleTwice srcDoubleTwice :=
  .of_progCert <|
    .define (Ri := Eq) (Ro := fun _ => Eq) (src := srcDouble)
      (fun _ _ _ h => h ▸ .builtin rfl (.ret rfl))
      fun _ _ _ hd =>
    .main (fun _ =>
      .app hd rfl fun _ _ h => h ▸
      .app_tail hd rfl)

end Freigen.Ast.Examples
