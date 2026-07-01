import Freigen.Reflect.Basic
import Freigen.Reflect.Recursion

/-!
# The reflection framework

`reflect%` compiles a `Free` program (a value, a function of its inputs, or a structural recursion)
into a `Prog`, bundled with its `≈`-soundness against `ofFree`.

- `Freigen.Reflect.Basic` — type reification, the monomorphising `walkProg` two-pass, and the
  value/function arm `reflectMain`.
- `Freigen.Reflect.Recursion` — `mrec` adequacy and the recursion arm, plus the unified `reflect%`.
-/
