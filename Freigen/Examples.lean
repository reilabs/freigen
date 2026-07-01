import Freigen.Examples.Circuit
import Freigen.Examples.Storage

/-!
# Examples (on the `FreeH` pipeline)

- `Freigen.Examples.Circuit` — the `CircOp` circuit DSL: first-order `assert` + the scoped `hint`,
  two Lean semantics (`runCirc`/`conCirc`), and `reflectH%` + `denote ≈ ofFreeH`.
- `Freigen.Examples.Storage` — the hint-less `StoreOp` DSL (`NoScope`): the same pipeline with the
  scoped slot empty.
-/
