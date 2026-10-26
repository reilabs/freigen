# 6. Extensions

Part of the [AST design](../DESIGN.md). These directions go beyond the
minimal milestone, roughly in the order they are expected to be needed. Each
should get its own document once work on it starts.

## Recursive definitions

Source definitions that recurse, structurally or by well-founded recursion,
become self-referencing AST definitions.

The function certificate for such a definition is proved by well-founded
induction that mirrors the source's own termination argument. The induction
hypothesis supplies certificates for recursive calls on smaller arguments. As
a consequence, termination of the AST comes from the same argument.

The macro has to recognize the recursion scheme Lean compiled the source to,
without unfolding it. Pinned tests must show recursion staying symbolic in
the emitted AST.

## Loops

The AST has a loop construct; the source monad has no matching primitive.
Either:
- certify AST loops against source functions defined by well-founded
  recursion with an explicit measure; or
- have the macro emit loops only from recognized iteration patterns, such as
  bounded folds.

The choice depends on how F2Z sources express iteration.

## Closures as values

Lambda expressions, and function-typed arguments and results. Certificates
would then relate source functions to heap references as *values*, which
reintroduces value relations indexed by type. This is deferred until a source
program actually needs higher-order code.

## Pretty-printing

A textual serialization of AST programs for the external compiler. Its
semantics must be documented in terms of the evaluator, including corner cases
such as division by zero and failure. A round-trip or golden test suite
guards the format.

## F2Z

The endgame. Two pieces:
- an F2Z effect signature and handler encoding AST operations as circuit
  gadgets;
- macro support for the F2Z source language.

Payloads that are not ABI values today, such as linear combinations, will
need either an ABI encoding or an extension of the ABI. This needs its own
design pass once the minimal pipeline is complete.
