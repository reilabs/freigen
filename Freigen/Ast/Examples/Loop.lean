import Freigen.Ast.Macro
import Freigen.Ast.Examples.Cert

/-!
Counted loops, `for i in lo...<hi` with a `UInt32` counter, lifted by the
macro to `Expr.forRange`. Every generated AST is pinned in its printed form.
-/

namespace Freigen.Ast.Examples

/-- A sum over the range, using its membership proof's binder. -/
def srcSum (n : UInt32) : Src .main UInt32 := do
  let mut acc : UInt32 := 0
  for _h : i in (0 : UInt32)...<n do
    acc := acc + i
  pure acc

lift_program liftedSum := srcSum

example : ProgramCert (Lift.id language model) (fun _ => .self _) liftedSum.ast srcSum :=
  liftedSum.cert

/--
info: (program
  (main main (v0 u32) u32
    (let v1 (lit u32 0))
    (let v2 (lit u32 0))
    (let f3
      (fun (v4 (prod u32 u32))
        (let v5 (fst v4))
        (let v6 (snd v4))
        (let v7 (uAdd v6 v5))
        (let v8 (lit bool true))
        (let v9 (pair v7 v8))
        (ret v9)))
    (let v10 (uLt v2 v0))
    (let v11
      (if v10
        (do
          (let v12 (pair v2 v1))
          (let v13
            (loop v12
              (fun (v14 (prod u32 u32))
                (let v15 (fst v14))
                (let v16 (app f3 v14))
                (let v17 (fst v16))
                (let v18 (snd v16))
                (let v19 (lit u32 1))
                (let v20 (uAdd v15 v19))
                (let v21 (uLt v20 v0))
                (let v22 (and v18 v21))
                (let v23 (pair v20 v17))
                (let v24 (pair v23 v22))
                (ret v24))))
          (let v25 (snd v13))
          (ret v25))
        (ret v1)))
    (ret v11)))
-/
#guard_msgs in #eval IO.println liftedSum.ast.pretty

/-- info: 'Freigen.Ast.Examples.liftedSum.cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms liftedSum.cert

/-- `break` in a branch: the body stops with `(state, false)`. -/
def srcBreak (n : UInt32) : Src .main UInt32 := do
  let mut acc : UInt32 := 0
  for i in (0 : UInt32)...<n do
    if decide (acc < 100) then acc := acc + i else break
  pure acc

lift_program liftedBreak := srcBreak

/--
info: (program
  (main main (v0 u32) u32
    (let v1 (lit u32 0))
    (let v2 (lit u32 0))
    (let f3
      (fun (v4 (prod u32 u32))
        (let v5 (fst v4))
        (let v6 (snd v4))
        (let v7 (lit u32 100))
        (let v8 (uLt v6 v7))
        (let v9
          (if v8
            (do
              (let v10 (uAdd v6 v5))
              (let v11 (lit bool true))
              (let v12 (pair v10 v11))
              (ret v12))
            (do (let v13 (lit bool false)) (let v14 (pair v6 v13)) (ret v14))))
        (ret v9)))
    (let v15 (uLt v2 v0))
    (let v16
      (if v15
        (do
          (let v17 (pair v2 v1))
          (let v18
            (loop v17
              (fun (v19 (prod u32 u32))
                (let v20 (fst v19))
                (let v21 (app f3 v19))
                (let v22 (fst v21))
                (let v23 (snd v21))
                (let v24 (lit u32 1))
                (let v25 (uAdd v20 v24))
                (let v26 (uLt v25 v0))
                (let v27 (and v23 v26))
                (let v28 (pair v25 v22))
                (let v29 (pair v28 v27))
                (ret v29))))
          (let v30 (snd v18))
          (ret v30))
        (ret v1)))
    (ret v16)))
-/
#guard_msgs in #eval IO.println liftedBreak.ast.pretty

/-- Effects in the body, and no mutable state: the state is `()`. -/
def srcPrintAll (n : UInt32) : Src .main Unit := do
  for i in (1 : UInt32)...<n do
    srcPrint i

lift_program liftedPrintAll := srcPrintAll ops [srcPrint]

/--
info: (program
  (main main (v0 u32) unit
    (let v1 (lit u32 1))
    (let v2 (lit unit ()))
    (let f3
      (fun (v4 (prod u32 unit))
        (let v5 (fst v4))
        (let v6 (snd v4))
        (let v7 (op print v5))
        (let v8 (lit bool true))
        (let v9 (pair v2 v8))
        (ret v9)))
    (let v10 (uLt v1 v0))
    (let v11
      (if v10
        (do
          (let v12 (pair v1 v2))
          (let v13
            (loop v12
              (fun (v14 (prod u32 unit))
                (let v15 (fst v14))
                (let v16 (app f3 v14))
                (let v17 (fst v16))
                (let v18 (snd v16))
                (let v19 (lit u32 1))
                (let v20 (uAdd v15 v19))
                (let v21 (uLt v20 v0))
                (let v22 (and v18 v21))
                (let v23 (pair v20 v17))
                (let v24 (pair v23 v22))
                (ret v24))))
          (let v25 (snd v13))
          (ret v25))
        (ret v2)))
    (let v26 (lit unit ()))
    (ret v26)))
-/
#guard_msgs in #eval IO.println liftedPrintAll.ast.pretty

/-- A nested loop, whose range starts at the outer counter. -/
def srcNested (n : UInt32) : Src .main UInt32 := do
  let mut acc : UInt32 := 0
  for i in (0 : UInt32)...<n do
    for j in i...<n do
      acc := acc + i * j
  pure acc

lift_program liftedNested := srcNested

/--
info: (program
  (main main (v0 u32) u32
    (let v1 (lit u32 0))
    (let v2 (lit u32 0))
    (let f3
      (fun (v4 (prod u32 u32))
        (let v5 (fst v4))
        (let v6 (snd v4))
        (let f7
          (fun (v8 (prod u32 u32))
            (let v9 (fst v8))
            (let v10 (snd v8))
            (let v11 (uMul v5 v9))
            (let v12 (uAdd v10 v11))
            (let v13 (lit bool true))
            (let v14 (pair v12 v13))
            (ret v14)))
        (let v15 (uLt v5 v0))
        (let v16
          (if v15
            (do
              (let v17 (pair v5 v6))
              (let v18
                (loop v17
                  (fun (v19 (prod u32 u32))
                    (let v20 (fst v19))
                    (let v21 (app f7 v19))
                    (let v22 (fst v21))
                    (let v23 (snd v21))
                    (let v24 (lit u32 1))
                    (let v25 (uAdd v20 v24))
                    (let v26 (uLt v25 v0))
                    (let v27 (and v23 v26))
                    (let v28 (pair v25 v22))
                    (let v29 (pair v28 v27))
                    (ret v29))))
              (let v30 (snd v18))
              (ret v30))
            (ret v6)))
        (let v31 (lit bool true))
        (let v32 (pair v16 v31))
        (ret v32)))
    (let v33 (uLt v2 v0))
    (let v34
      (if v33
        (do
          (let v35 (pair v2 v1))
          (let v36
            (loop v35
              (fun (v37 (prod u32 u32))
                (let v38 (fst v37))
                (let v39 (app f3 v37))
                (let v40 (fst v39))
                (let v41 (snd v39))
                (let v42 (lit u32 1))
                (let v43 (uAdd v38 v42))
                (let v44 (uLt v43 v0))
                (let v45 (and v41 v44))
                (let v46 (pair v43 v40))
                (let v47 (pair v46 v45))
                (ret v47))))
          (let v48 (snd v36))
          (ret v48))
        (ret v1)))
    (ret v34)))
-/
#guard_msgs in #eval IO.println liftedNested.ast.pretty

/-! ## Rejected loops -/

/-- `break` without an `else`: the rest of the body is a join point over the
state and the branch's result. -/
def srcEarly (n : UInt32) : Src .main UInt32 := do
  let mut acc : UInt32 := 0
  for i in (0 : UInt32)...<n do
    if i == 3 then break
    acc := acc + i
  pure acc

/--
error: lift: join points with several arguments are not supported; they come from mutable variables
  fun acc y =>
    have acc := acc + i;
    do
    pure PUnit.unit
    pure (ForInStep.yield acc)
-/
#guard_msgs in lift_program badEarly := srcEarly

end Freigen.Ast.Examples
