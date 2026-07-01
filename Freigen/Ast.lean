import Freigen.Ast.Tp
import Freigen.Ast.Basic

/-!
# The AST framework

- `Freigen.Ast.Tp` — the object-type universe `Tp` and the reified primitive ops `Un`/`Bin`.
- `Freigen.Ast.Basic` — the dumb, typed imperative AST `Code`/`Prog`, its denotation `denoteProg`
  into `Comp`, the source embedding `ofFree`, and a pretty-printer.
-/
