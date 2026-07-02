import Freigen.Ast.Tp
import Freigen.Ast.Basic
import Freigen.Ast.Sexp

/-!
# The AST framework

- `Freigen.Ast.Tp` — the object-type universe `Tp` and the reified primitive ops `Un`/`Bin`.
- `Freigen.Ast.Basic` — the dumb, typed imperative AST `Code`/`Prog`, its denotation `denoteProg`
  into `Comp`, and the source embedding `ofFree`.
- `Freigen.Ast.Sexp` — the uniform, machine-parseable S-expression serialization (what `#compile`
  emits; parsed by the Rust SDK in `rust/`).
-/
