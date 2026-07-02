import Freigen.Examples.Circuit
import Freigen.Examples.Storage
import Freigen.Examples.Recursion

/-!
# Examples

Each example is reflected with `reflect_def` and pins its runtime result, its soundness statement,
and its pretty-printed AST with `#guard_msgs`, so the shown output can't drift from the code.

- `Freigen.Examples.Circuit` — a **folder** of circuit examples over the `CircOp` DSL (first-order
  `assert` + scoped `hint`, `runCirc`/`conCirc` semantics): `Circuit.Basic` exercises the features
  one by one (hints, helpers, inputs, monomorphisation, collections, casts, loops).  A real
  circuit — the Poseidon hash — lives in the downstream client (`examples/client/`), doubling as
  the `#compile` golden test.
- `Freigen.Examples.Storage` — the hint-less `StoreOp` DSL (`NoScope`): the same pipeline with the
  scoped slot empty, and an operational `runStore`.
- `Freigen.Examples.Recursion` — recursive sources (`countdown`, `sm`, stateful `sumAcc` /
  `countAsserts`), reflected into `rec_` programs.
-/
