import Freigen

/-!
# A downstream project using Freigen

This is an ordinary Lake package that only `require`s Freigen (see `lakefile.lean`).  You write a
`Free` program, `reflect%` it, and mark it with `#compile`; then `lake build MyCircuits:prog` renders
the reflected AST and writes it to disk.  Nothing here is Freigen-internal — it is exactly what a user
of the library writes.
-/

namespace MyCircuits
open Freigen

/-- My own circuit program, written against Freigen's `Free CircOp HintS`:
    hint `x = 15`, hint `y = 2·x`, then constrain `y == 30`. -/
def myProgram : Free CircOp HintS Unit := do
  let x ← hint (pure (10 + 5))
  let y ← hint (pure (x * 2))
  assert (y == 30)

/-- `reflect%` gives the reflected `Prog` **and** its `≈`-soundness proof against `myProgram`. -/
def myProgramC := reflect% myProgram
example : denoteProg (myProgramC.1 (KC CircOp) Tp.denote) .nil ≈ ofFree myProgram := myProgramC.2

-- Emit the certified AST to `out/myProgram.prog` on `lake build MyCircuits:prog`.
#compile myProgramC => "out/myProgram.prog"

end MyCircuits
