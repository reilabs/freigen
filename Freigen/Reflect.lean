import Freigen.Reflect.Basic
import Freigen.Reflect.Recursion

/-!
# The reflection framework

`reflect%` compiles a `Free` program (a value, a function of its inputs, or a structural recursion)
into a `Prog`, bundled with its `≈`-soundness against `ofFree`.

- `Freigen.Reflect.Sound` — the compositional soundness lemmas (`sc_op`/`sc_bind`/`sc_call`/…), one
  per `Code` node, that the value arm assembles into a `simp`-free congruence-tree proof.
- `Freigen.Reflect.Basic` — type reification, the monomorphising `walkProg` two-pass, the value/function
  arm `reflectMain`, and `pWalk` (the compositional proof builder mirroring the source).
- `Freigen.Reflect.Recursion` — `mrec` adequacy and the recursion arm, plus the unified `reflect%`.
-/
