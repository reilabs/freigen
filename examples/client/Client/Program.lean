import Freigen

/-!
# A downstream project using Freigen

This is an ordinary Lake package that only `require`s Freigen (see `lakefile.lean`).  You write a
`Free` program and mark it with `#compile`; then `lake build Client:prog` reflects it, renders the
AST, and writes it to disk.  Nothing here is Freigen-internal — it is exactly what a user of the
library writes.
-/

namespace Client
open Freigen

/-- My own circuit program, written against Freigen's `Free CircOp HintS`:
    hint `x = 15`, hint `y = 2·x`, then constrain `y == 30`. -/
def myProgram : Free CircOp HintS Unit := do
  let x ← hint (pure (10 + 5))
  let y ← hint (pure (x * 2))
  assert (y == 30)

-- Reflect + emit the certified AST to `out/myProgram.prog` on `lake build Client:prog`.
-- The build prints the `≈`-soundness statement the reflection proves.
#compile myProgram => "out/myProgram.prog"

end Client
