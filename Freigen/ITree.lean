import Freigen.ITree.Basic
import Freigen.ITree.Eutt

/-!
# Interaction trees — the coinductive denotation domain

- `Freigen.ITree.Basic` — the domain `Comp Op` (`ret`/`tau`/`vis`/`fail`), `bind` + monad laws, and
  the general-recursion combinator `mrec` (with `interp` and the call-extended signature `CallOp`).
- `Freigen.ITree.Eutt` — weak bisimulation `≈` and its construction algebra (congruences).
-/
