import Freigen.Reflect.Basic
import Freigen.Reflect.Recursion

/-!
# The reflection framework

`reflect%` compiles a `Free` program (a value, a function of its inputs, or a structural recursion)
into a `Prog`, bundled with its `≈`-soundness against `ofFree`.

- `Freigen.Reflect.Sound` — the compositional soundness lemmas (`sc_op`/`sc_bind`/`sc_call`/…), one
  per `Code` node, that the value arm assembles into a `simp`-free congruence-tree proof.
- `Freigen.Reflect.Basic` — type reification and the single **mode-parametric walk** (`Env.walk`:
  abstract mode builds the parametric `Code`, proof mode also assembles the compositional
  (★)-proof), with the monomorphising two-pass and the value/function arm `reflectMain`.
- `Freigen.Reflect.Recursion` — `mrec` adequacy and the recursion arm, plus the unified `reflect%`
  term elaborator and the `reflect_def C := src` command (named `C` / `C_sound` definitions).
-/
