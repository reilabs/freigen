# Client — using Freigen as a library

A minimal downstream project that depends on Freigen, writes a `Free` program, and compiles it to a
`.prog` file on disk.

## Layout

- `lakefile.toml` — `require freigen`, one `lean_lib Client` (a plain-TOML consumer: the `prog`
  facet and the emitter come from the dependency).
- `Client/Program.lean` — a hand-written `Free CircOp HintS` program, marked with
  `#compile … => "out/myProgram.prog"`.
- `Client/Poseidon.lean` — a *real* circuit: the Poseidon hash over BN254 `Fr` (reference
  constants, circomlib-pinned test vectors, `≈`-soundness and axiom guards inline), marked with
  `#compile … => "out/poseidon.prog"` — two artifacts per build.
- `expected/` — golden files; CI diffs every emitted artifact against them.

## Build and compile

```sh
lake build Client:prog
```

This builds the library and writes both reflected ASTs under `out/`, in the uniform S-expression
format (grammar pinned in `Freigen/Ast/Sexp.lean`); `myProgram.prog` reads:

```
(program
  (main () unit
    (block
      (let v1 nat (scope hint
        (block
          (let v0 nat (lit 15))
          (ret v0))))
      (let v4 nat (scope hint
        (block
          (let v2 nat (lit 2))
          (let v3 nat (bin mul v1 v2))
          (ret v3))))
      (let v5 nat (lit 30))
      (let v6 bool (bin eq v4 v5))
      (let v7 unit (op assert v6))
      (ret v7))))
```

The `prog` facet is provided by Freigen; it works on any library that depends on it, emitting exactly
the artifacts declared by that library's own `#compile` commands.

Because `#compile` points at a `reflect%` result — a `{ Closed // denoteProg … ≈ ofFree … }` pair —
the file is only produced if the soundness proof type-checks: **the emitted AST is certified `≈` its
source program.**

## Executed E2E by the Rust SDK

The goldens are not just diffed — the Rust SDK (`rust/` at the repo root) parses and **executes**
them on CI (`rust/tests/examples.rs`): `myProgram` runs its witness generation (hints run, the
assert holds), and `poseidon` is evaluated against the same circomlib known-answer vectors that
`Client/Poseidon.lean` pins with `#eval runCirc`.  One artifact, three checks: certified `≈` at
emission, golden-diffed against this directory, and re-executed by an independent interpreter.
