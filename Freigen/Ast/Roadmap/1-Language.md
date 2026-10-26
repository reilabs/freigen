# 1. Language completeness

Part of the [AST design](../DESIGN.md). Goal: make the object language
expressive enough for the minimal milestone, and leave `Ast/Defs.lean` free
of leftovers before proofs start depending on its shape.

## Current state

`Ast/Defs.lean` defines the following:
- the types;
- the ABI subset;
- syntactic effect signatures;
- a PHOAS CPS `Expr` with `ret`, `lit`, `builtin`, `lam`, `app`, `ite`,
  `loop` and `op` nodes;
- `Program`, a telescope of self-referencing definitions ending in `main`;
- the closure heap;
- the evaluator.

It compiles. No proofs depend on it yet, so this is the cheapest moment to
change its shape.

## Gaps

### Data construction and projection

Builtins take their arguments as a single variable of product type. However,
no node builds a product from separate variables or takes one apart. As a
result, the language cannot express:

- a binary builtin applied to two independently computed values;
- the `(state, continue?)` pair a loop body must return;
- an effect input, block input or `main` output of product or array type
  that isn't a literal.

Two options:
- **Explicit nodes.** Add pair construction, projections, and array
  construction/indexing as expression nodes. This keeps builtins uniform and
  puts all data plumbing in one place.
- **Multi-argument builtins.** Change builtins to take a heterogeneous list of
  variables, and keep products for data only. Builtin calls become direct,
  but products still need their own nodes anyway.

The likely answer is explicit nodes for data, plus builtins taking
heterogeneous argument lists so arithmetic doesn't go through tuples.

### Primitive semantics

The meaning of each builtin is currently inlined in the evaluator. It should
be a standalone function, so that certificate rules can state "the
continuation receives the builtin's result" without referring to evaluator
internals.

The builtin set covers only unsigned 32-bit arithmetic and comparison. The
minimal milestone needs boolean operations. Whether signed integers stay in
the language at all should be decided now, before anything depends on them.

Division by zero currently inherits Lean's convention. That is acceptable as
long as it is the documented semantics the external compiler must follow.

### Unit and the ABI

`unit` is not an ABI type, so operations with no meaningful input or output
have to invent one. Either make `unit` ABI, or give signatures an explicit
"no payload" option.

### Leftovers

- **Stale aliases.** Aliases name the evaluator's effect stack in a different
  order than the evaluator uses. Replace them with one alias in the order
  actually used: failure first, then silent steps, then user effects.
- **Dead code.** The unused source-monad alias and the superseded
  continuation type should go.
- **Universe mismatch.** Certificates force the context type into the lowest
  universe while signatures are universe-polymorphic. Pick one.

## Test signature

Add a small effect signature dedicated to tests. It needs at least one plain
operation with input and output, and at least one operation with a block
that changes context. Every later stage uses it for examples.

## Done when

- Every construct the minimal macro will emit is expressible, with no
  encoding tricks.
- Builtin semantics are a standalone function.
- The test signature exists, and a few hand-written programs over it evaluate
  as expected via `#eval`/`#guard`.
