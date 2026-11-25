import Freigen.Ast.JoinPoints.Correct
import Freigen.Ast.JoinPoints.Wf
import Freigen.Ast.Examples.Macro

/-!
Join-point elimination on lifted programs. The translations are pinned in
their printed form; a closure that is not a join point is kept.
-/

namespace Freigen.Ast.Examples

instance : Language.Blocks language where
  blocks := fun
    | .main, .hint => [()]
    | .main, .print => []
    | .main, .input => []
    | .hint, e => nomatch e
  complete := by
    intro γ e b
    cases γ <;> cases e <;> cases b
    simp

theorem language_primFnFree : language.PrimFnFree := nofun

/-! ## Translations -/

/--
info: (program
  (main main (v0 bool) u32
    (let v1
      (if v0
        (do (let v2 (lit u32 1)) (let v3 (op print v2)) (ret v3))
        (do (let v4 (lit u32 2)) (let v5 (op print v4)) (ret v5))))
    (let v6 (lit u32 3))
    (ret v6)))
-/
#guard_msgs in #eval IO.println (Program.joinPoints liftedBranch.ast).pretty

-- Sequential branches, the second inside the first's join point.
/--
info: (program
  (main main (v0 u32) u32
    (let v1 (lit u32 0))
    (let v2 (uEq v0 v1))
    (let v3
      (if v2
        (do (let v4 (lit u32 0)) (let v5 (op print v4)) (ret v5))
        (do (let v6 (op print v0)) (ret v6))))
    (let v7 (op hint v0 (block body (v8) (let v9 (uMul v8 v8)) (ret v9))))
    (let v10 (lit u32 100))
    (let v11 (uLt v7 v10))
    (let v12
      (if v11
        (do (let v13 (op print v7)) (ret v13))
        (do (let v14 (lit unit ())) (ret v14))))
    (ret v7)))
-/
#guard_msgs in #eval IO.println (Program.joinPoints liftedLog.ast).pretty

/-- A branch nested in a branch, followed by code in both. -/
def srcNested (x : UInt32) : Src .main UInt32 := do
  if x == 0 then
    if x == 1 then srcPrint 1 else srcPrint 2
    srcPrint 3
  else srcPrint 4
  pure x

lift_program liftedNested := srcNested ops [srcPrint]

/--
info: (program
  (main main (v0 u32) u32
    (let v1 (lit u32 0))
    (let v2 (uEq v0 v1))
    (let v3
      (if v2
        (do
          (let v4 (lit u32 1))
          (let v5 (uEq v0 v4))
          (let v6
            (if v5
              (do (let v7 (lit u32 1)) (let v8 (op print v7)) (ret v8))
              (do (let v9 (lit u32 2)) (let v10 (op print v9)) (ret v10))))
          (let v11 (lit u32 3))
          (let v12 (op print v11))
          (ret v12))
        (do (let v13 (lit u32 4)) (let v14 (op print v13)) (ret v14))))
    (ret v0)))
-/
#guard_msgs in #eval IO.println (Program.joinPoints liftedNested.ast).pretty

/-! ## Closures that are not join points -/

section
variable {V : language.Tp → Type}

/-- A closure called once in tail position, and once with code after the
call. -/
def twoCalls : Program language Scope.main .bool .uInt32 V :=
  .main fun c =>
    .lam (inp := .unit) (fun _ => .lit .uInt32 3 .ret) fun f =>
    .lit .unit () fun u =>
    .ite c (.app f u .ret) (.app f u fun r => .builtin .uAdd h![r, r] .ret) .ret

/-- An early return: one path of the scope returns without calling the
closure. -/
def earlyReturn : Program language Scope.main .bool .uInt32 V :=
  .main fun c =>
    .lam (inp := .unit) (fun _ => .lit .uInt32 3 .ret) fun f =>
    .lit .unit () fun u =>
    .ite c (.app f u .ret) (.lit .uInt32 4 .ret) .ret

end

/--
info: (program
  (main main (v0 bool) u32
    (let f1 (fun (v2 unit) (let v3 (lit u32 3)) (ret v3)))
    (let v4 (lit unit ()))
    (let v5
      (if v0
        (do (let v6 (app f1 v4)) (ret v6))
        (do (let v7 (app f1 v4)) (let v8 (uAdd v7 v7)) (ret v8))))
    (ret v5)))
-/
#guard_msgs in #eval IO.println (Program.joinPoints twoCalls).pretty

/--
info: (program
  (main main (v0 bool) u32
    (let f1 (fun (v2 unit) (let v3 (lit u32 3)) (ret v3)))
    (let v4 (lit unit ()))
    (let v5
      (if v0
        (do (let v6 (app f1 v4)) (ret v6))
        (do (let v7 (lit u32 4)) (ret v7))))
    (ret v5)))
-/
#guard_msgs in #eval IO.println (Program.joinPoints earlyReturn).pretty

/-! ## Certificates carry over -/

example : Program.Wf liftedBranch.ast := by ast_wf [liftedBranch.ast]

example : ProgramCert (Lift.id language model) (fun _ => .self _)
    (Program.joinPoints liftedBranch.ast) srcBranch :=
  .joinPoints language_primFnFree (by ast_wf [liftedBranch.ast]) liftedBranch.cert

example : ProgramCert (Lift.id language model) (fun _ => .self _)
    (Program.joinPoints liftedLog.ast) srcLog :=
  .joinPoints language_primFnFree (by ast_wf [liftedLog.ast]) liftedLog.cert

/-- The output is well-formed, so the pass can run again. -/
example : Program.Wf (Program.joinPoints liftedLog.ast) :=
  Program.joinPoints_wf (by ast_wf [liftedLog.ast])

/-- info: 'Freigen.Ast.ProgramCert.joinPoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ProgramCert.joinPoints

end Freigen.Ast.Examples
