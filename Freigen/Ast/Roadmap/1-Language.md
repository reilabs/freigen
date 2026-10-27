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

**Decision:** builtins take heterogeneous argument lists, and data
construction and projection are themselves (type-polymorphic) builtins:
pairs, projections, and array creation, push, indexing, update and length.
This gives one AST node and one certificate rule for all primitive
operations. Builtin semantics are partial, and a failing builtin (an
out-of-bounds array access) makes the evaluator fail, so partiality is
handled once.

### Primitive semantics

The meaning of each builtin is currently inlined in the evaluator. It should
be a standalone function, so that certificate rules can state "the
continuation receives the builtin's result" without referring to evaluator
internals.

The builtin set covers only unsigned 32-bit arithmetic and comparison. The
minimal milestone needs boolean operations.

**Decision:** signed integers are removed. Nothing used them, and the F2Z
numeric types will be designed with F2Z.

Division and remainder by zero follow Lean's `UInt32` convention, and array
lengths wrap modulo `2^32`. This is documented as the semantics the external
compiler must follow.

### Unit and the ABI

`unit` is not an ABI type, so operations with no meaningful input or output
have to invent one.

**Decision:** `unit` is ABI.

### Leftovers

- **Stale aliases.** Aliases name the evaluator's effect stack in a different
  order than the evaluator uses. Replace them with one alias in the order
  actually used: failure first, then silent steps, then user effects.
- **Dead code.** The unused source-monad alias and the superseded
  continuation type should go.
- **Universe mismatch.** Certificates force the context type into the lowest
  universe while signatures are universe-polymorphic.

  **Decision:** signatures are monomorphic (`Type`).

## Test signature

Add a small effect signature dedicated to tests. It needs at least one plain
operation with input and output, and at least one operation with a block
that changes context. Every later stage uses it for examples.

## Done when

- Every construct the minimal macro will emit is expressible, with no
  encoding tricks.
- Builtin semantics are a standalone function, tested with `#guard`.
- The test signature exists, and hand-written programs over it covering every
  construct type-check (`Ast/Examples/Basic.lean`). Running them through the
  evaluator is not a goal: `CompM` is far too slow to execute, so their
  behaviour is checked by the hand-written certificates of stage 4 instead.
