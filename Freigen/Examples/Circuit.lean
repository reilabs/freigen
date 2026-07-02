import Freigen.Examples.Circuit.Basic

/-!
# Circuit examples

- `Freigen.Examples.Circuit.Basic` — the `CircOp` DSL (`assert` + scoped `hint`, `runCirc`/`conCirc`
  semantics) and the feature-by-feature examples: hints, helpers, inputs, monomorphisation,
  collections, casts, pure and effectful loops.

A *real* circuit built on this DSL — the Poseidon hash — lives in the downstream client project
(`examples/client/Client/Poseidon.lean`), where it doubles as the multi-artifact `#compile`
golden test.
-/
