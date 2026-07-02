import Freigen.Examples.Circuit.Basic
import Freigen.Examples.Circuit.Poseidon

/-!
# Circuit examples

- `Freigen.Examples.Circuit.Basic` — the `CircOp` DSL (`assert` + scoped `hint`, `runCirc`/`conCirc`
  semantics) and the feature-by-feature examples: hints, helpers, inputs, monomorphisation,
  collections, casts, pure and effectful loops.
- `Freigen.Examples.Circuit.Poseidon` — a real circuit: the Poseidon hash over BN254 `Fr`
  (reference constants, static round schedule), reflected end-to-end with kept loops and folded
  definitions, `≈`-sound, pinned against the circomlib test vectors.
-/
