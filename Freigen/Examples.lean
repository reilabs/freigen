import Freigen.Examples.Circuit
import Freigen.Examples.Storage

/-!
# Examples

Each example bundles its `reflect%` soundness proof (`… ≈ ofFree …`) and pins its runtime result
and pretty-printed AST with `#guard_msgs`, so the shown output can't drift from the code.

- `Freigen.Examples.Circuit` — the `CircOp` circuit DSL (first-order `assert` + scoped `hint`), with
  `runCirc`/`conCirc` semantics.  Exercises: a hint + constraint, `main` calling helper `def_`s,
  `main` taking inputs, a monomorphised polymorphic helper (`dbl {N} : ZMod N → …`, shared between
  equal `N`s), a multi-argument helper, and a `Vector`-valued result.
- `Freigen.Examples.Storage` — the hint-less `StoreOp` DSL (`NoScope`): the same pipeline with the
  scoped slot empty, and an operational `runStore`.

Recursion is exercised in `Freigen/Recursion.lean` (`countdown`, `sm`).
-/
