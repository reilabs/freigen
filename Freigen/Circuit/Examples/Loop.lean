import Freigen.Circuit.Examples.Sqrt

/-!
Counted loops in circuits, lifted by the macro: the state is a wire, and the
body performs an operation.
-/

namespace Freigen.Circuit.Examples.Loop

open Ast Lift

variable {P : Nat} [ctx : Context P]

/-- `x` doubled 8 times, every intermediate value range checked. -/
def srcDoubling (x : ctx.W) : Circuit P ctx.W := do
  let mut w := x
  for _ in (0 : UInt32)...<8 do
    w := w + w
    let _ ← Circuit.rangeCheck 8 w
  pure w

lift_program liftedDoubling := srcDoubling via lift

/--
info: (program
  (main constraint (v0 wire) wire
    (let v1 (lit u32 0))
    (let v2 (lit u32 8))
    (let f3
      (fun (v4 (prod u32 wire))
        (let v5 (fst v4))
        (let v6 (snd v4))
        (let v7 (wAdd v6 v6))
        (let v8 (op (rangeCheck 8) v7))
        (let v9 (lit bool true))
        (let v10 (pair v7 v9))
        (ret v10)))
    (let v11 (uLt v1 v2))
    (let v12
      (if v11
        (do
          (let v13 (pair v1 v0))
          (let v14
            (loop v13
              (fun (v15 (prod u32 wire))
                (let v16 (fst v15))
                (let v17 (app f3 v15))
                (let v18 (fst v17))
                (let v19 (snd v17))
                (let v20 (lit u32 1))
                (let v21 (uAdd v16 v20))
                (let v22 (uLt v21 v2))
                (let v23 (and v19 v22))
                (let v24 (pair v21 v18))
                (let v25 (pair v24 v23))
                (ret v25))))
          (let v26 (snd v14))
          (ret v26))
        (ret v0)))
    (ret v12)))
-/
#guard_msgs in #eval IO.println liftedDoubling.ast.pretty

/-- info: 'Freigen.Circuit.Examples.Loop.liftedDoubling.cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms liftedDoubling.cert

/-- A branch without `else`, which returns `()`. -/
def srcCheckIf (x : ctx.W) : Circuit P ctx.W := do
  if true then
    let _ ← Circuit.rangeCheck 8 x
  pure x

lift_program liftedCheckIf := srcCheckIf via lift

/--
info: (program
  (main constraint (v0 wire) wire
    (let f1 (fun (v2 unit) (ret v0)))
    (let v3 (lit bool true))
    (let v4
      (if v3
        (do
          (let v5 (op (rangeCheck 8) v0))
          (let v6 (lit unit ()))
          (let v7 (app f1 v6))
          (ret v7))
        (do (let v8 (lit unit ())) (let v9 (app f1 v8)) (ret v9))))
    (ret v4)))
-/
#guard_msgs in #eval IO.println liftedCheckIf.ast.pretty

end Freigen.Circuit.Examples.Loop
