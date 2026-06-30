import Freigen.ITree.Basic
import Freigen.ITree.Eutt
import Freigen.ITree.Adequacy

/-!
# Interaction trees — the coinductive denotation domain

This module re-exports the interaction-tree theory:

- `Freigen.ITree.Basic` — the domain `Comp Op` (`ret`/`tau`/`vis`/`fail`), `bind` + monad laws,
  `mrec` (general recursion) and `iter` (the tail special case), `ofFree`, convergence.
- `Freigen.ITree.Eutt` — weak bisimulation `≈` and its construction algebra (congruences).
- `Freigen.ITree.Adequacy` — `mrec` adequacy: a reflected recursion is `≈` its source.
-/
