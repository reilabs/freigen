# Client — using Freigen as a library

A minimal downstream project that depends on Freigen, writes a `Free` program, and compiles it to a
`.prog` file on disk.

## Layout

- `lakefile.toml` — `require freigen`, one `lean_lib Client` (a plain-TOML consumer: the `prog`
  facet and the emitter come from the dependency).
- `Client/Program.lean` — a hand-written `Free CircOp HintS` program, marked with
  `#compile … => "out/myProgram.prog"`.
- `Client/Poseidon.lean` — a *library-provided* program (Freigen's Poseidon over BN254 `Fr`),
  marked with `#compile … => "out/poseidon.prog"` — two artifacts per build.
- `expected/` — golden files; CI diffs every emitted artifact against them.

## Build and compile

```sh
lake build Client:prog
```

This builds the library and writes both reflected ASTs under `out/`; `myProgram.prog` reads:

```
def main() =>
  let v1 ← hint unconstrained
    let v0 := 15
    v0
  let v4 ← hint unconstrained
    let v2 := 2
    let v3 := v1 * v2
    v3
  let v5 := 30
  let v6 := v4 == v5
  let v7 ← assert(v6)
  v7
```

The `prog` facet is provided by Freigen; it works on any library that depends on it, emitting exactly
the artifacts declared by that library's own `#compile` commands.

Because `#compile` points at a `reflect%` result — a `{ Closed // denoteProg … ≈ ofFree … }` pair —
the file is only produced if the soundness proof type-checks: **the emitted AST is certified `≈` its
source program.**
