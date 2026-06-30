import Freigen.Examples.Circuit
import Freigen.Examples.Storage
import Freigen.Examples.Recursion

/-!
# Examples

The example signatures and programs, one module per operation signature:

- `Freigen.Examples.Circuit` — the `CircOp` signature (`hint`/`assert`): literals, primitives,
  loops, monomorphised and multi-argument definitions, and the Poseidon hash.
- `Freigen.Examples.Storage` — the `StoreOp` signature (`set`/`get`): a mutable store of
  naturals addressed by naturals, with an *operational* denotation (`runStore`).
- `Freigen.Examples.Recursion` — plain structural-recursive `def`s (tail and non-tail) reflected
  via `reflect%` into the `ITree.mrec` knot, returning function **and** bundled `≈`-soundness.
-/
