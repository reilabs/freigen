import Freigen.Free
import Freigen.ITree.Effect
import Freigen.ITree.Basic
import Freigen.ITree.Eutt
import Freigen.Ast.Tp
import Freigen.Ast.Basic
import Freigen.Ast.Sexp
import Freigen.Reflect.Sound
import Freigen.Reflect.Basic
import Freigen.Reflect.Recursion
import Freigen.Compile
import Freigen.Examples.Circuit.Basic
import Freigen.Examples.Storage
import Freigen.Examples.Recursion

/-!
# Freigen — the root module

`import Freigen` brings in the whole library.  Directories are pure namespaces (mathlib-style:
no per-directory umbrella modules); this file lists every module, and the lakefile's
`.andSubmodules` glob makes CI build any module even if it goes missing from this list.

Module map (details in each module's own docstring; the full story is in the README):

- `Freigen.Free` — the free monad `Free Op SOp` (`pure`/`op`/`hop`) and the generic interpreter
  `run`.
- `Freigen.ITree.Basic`/`.Effect`/`.Eutt` — the coinductive denotation domain `Comp Op`
  (`ret`/`tau`/`vis`/`fail`), `bind` + its laws, the general-recursion combinator `mrec` (with
  `interp` and the call-extended signature `CallOp`), and weak bisimulation `≈` with its
  congruence algebra.
- `Freigen.Ast.Tp`/`.Basic`/`.Sexp` — the object-type universe and reified primitives, the dumb
  typed AST `Code`/`Prog` with its uniform denotation `denoteProg` into `Comp`, and the
  S-expression serialization (**the** printer; grammar pinned in `Ast.Sexp`).
- `Freigen.Reflect.Sound`/`.Basic`/`.Recursion` — `reflect%` compiles a `Free` program (a value,
  a function of its inputs, or a structural recursion) into a `Prog` bundled with its
  `≈`-soundness against `ofFree`: per-node congruence lemmas, the mode-parametric walk, and the
  recursion arm with the `reflect%`/`reflect_def` elaborators.
- `Freigen.Compile` — the `DSL` class, `serialize`, and the `#compile prog => "path"` command
  behind the `lake build <lib>:prog` facet.
- `Freigen.Examples.Circuit.Basic`/`.Storage`/`.Recursion` — the Lean-side unit-test suite
  (`CircOp` + scoped `hint`, the hint-less `StoreOp`, and `rec_` programs), each example pinning
  its runtime result, soundness statement, and serialized AST with `#guard_msgs`.  The end-to-end
  path — `#compile` → `.prog` artifact → parsed and executed by the Rust SDK — is exercised by
  the separate goldens project (`examples/client/`) on CI.
-/
