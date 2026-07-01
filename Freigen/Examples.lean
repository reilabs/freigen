import Freigen.Examples.Circuit
import Freigen.Examples.Storage

/-!
# Examples (on the `Free` pipeline)

- `Freigen.Examples.Circuit` — the `CircOp` circuit DSL: first-order `assert` + the scoped `hint`,
  two Lean semantics (`runCirc`/`conCirc`), and `reflect%` + `denote ≈ ofFree`.
- `Freigen.Examples.Storage` — the hint-less `StoreOp` DSL (`NoScope`): the same pipeline with the
  scoped slot empty.
-/
