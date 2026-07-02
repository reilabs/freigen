# `freigen` — the Rust SDK

The consumer side of Freigen's compiler output.  Freigen (the Lean library at the repository root)
reflects free-monadic programs into a typed imperative AST and emits it as a **uniform S-expression
artifact** (`.prog`); this crate parses that format and runs it.

- `sexp` — a minimal S-expression reader (lists and bare atoms — names included; quoted strings
  are reserved for guest-language string literals; whitespace-insensitive).
- `ast` — the typed Rust AST, mirroring the Lean-side `Prog`/`Code` one-to-one: a program is a
  list of `def`/`rec` definitions ending in `main`; a body is a block of single-assignment,
  type-annotated `let`s ending in a return or a branch; loops (`fold`/`vgen`) are first-class and
  never unrolled; custom effects are opaque named nodes.  This is the structure a **client
  compiler** walks.
- `parse` — `.prog` → `ast::Program`, with type-directed literal parsing (a field element knows
  its modulus, a `Fin` its bound).
- `value` / `interp` — a **canonical interpreter** mirroring the Lean denotation `denoteProg`,
  for executing compiled programs in tests.  The source DSL's two extension slots stay
  client-injectable through the `Handler` trait:
  - `op(name, arg)` — the denotation of a custom first-order effect (e.g. `assert`);
  - `scope(name, block)` — the denotation of a scoped construct; the block arrives as a runnable
    closure, so a handler may run it inline (the default — witness generation for a `hint`),
    substitute a value, or fail.

  Failure is first-class: a partial primitive whose erased proof obligation does not hold (an
  out-of-range access, a size mismatch) evaluates to `Error::Fail` — the image of `ITree.fail`.
  A *reflected* program carries a Lean-side proof that this cannot happen on the source's inputs.

The grammar of the format is pinned in `Freigen/Ast/Sexp.lean` (the emitter); `parse` is its
inverse.

## Tests

`cargo test` runs the unit suite plus the end-to-end tests in `tests/examples.rs`, which parse and
execute the goldens project's artifacts (`examples/client/expected/*.prog`): `myProgram`'s witness
generation, and the Poseidon circuit against the circomlib known-answer vectors.  CI runs this
next to the Lean jobs, so every emitted program is certified `≈` its source *and* executes to the
pinned results through an independent interpreter.
