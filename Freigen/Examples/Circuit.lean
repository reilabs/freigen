import Freigen.Examples.Circuit.Basic
import Freigen.Examples.Circuit.Examples
import Freigen.Examples.Circuit.Poseidon

/-!
# The `CircOp` example, expanded

The arithmetic-circuit operation signature `CircOp` (`hint`/`assert`) and everything built on it,
split across `Freigen/Examples/Circuit/`:

- `Circuit.Basic` — the `CircOp` signature, its smart constructors, and its **computable
  semantics** `runCirc` (`foldFree` into `Option`: `hint` = eval, `assert` = potential failure).
- `Circuit.Examples` — reflect-and-pretty-print smoke tests: literals, primitives, loops,
  monomorphised and multi-argument definitions, hints, `runCirc` runs, and the `Vector` type.
- `Circuit.Poseidon` — the Poseidon sponge hash over the BN254 scalar field for 4 inputs, phrased
  over `Vector Fr t`, plus preimage/hint circuits run with `runCirc`.
-/
