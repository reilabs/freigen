# AST Design

## Goal

Lift effectful Lean programs written in the `Free` monad into a small,
first-order AST. Pretty-print that AST for an external compiler. Every
lifting comes with a kernel-checked proof that the AST behaves exactly like
the source program.

The long-term source language is F2Z circuits. The current milestone is a
minimal version: a toy effect signature, unsigned arithmetic, branching,
effects with blocks, and non-recursive helper functions. It should establish
the semantics, the correctness criterion, and the proof architecture that
F2Z will later reuse.

## Architecture

```text
 source program        Free E γ α                    (Lean, inductive, terminating)
       │
       │  macro: lift + prove
       ▼
 AST program           Program eff …                 (syntax)
       │
       │  evaluator
       ▼
 AST behaviour         CompM (Fail ⊕ Tau ⊕ eff) …    (coinductive)
       │
       │  erasure
       ▼
 observable behaviour  Free E γ α                    compared to source by equality
```

There are four layers, each depending only on the ones above it:

1. **Computation theory.** Effects, the finite (`Free`) and possibly-infinite
   (`CompM`) monads, well-foundedness, and reification. Generic, knows nothing
   about the AST.
2. **Object language.** AST syntax, its types, and its evaluator.
3. **Certificates.** What it means for an AST fragment to be correct, and
   compositional rules for establishing it.
4. **Macro.** Lifts source programs to ASTs and assembles certificates
   from the rules. Trusts nothing; the kernel checks its output.

## Computation theory

Effects are context-indexed. An operation may carry *blocks*:
sub-computations that run in a different context and return a value to the
operation. A hint body inside a circuit is the motivating example.

Source programs are finite trees (`Free`). The evaluator produces potentially
infinite trees (`CompM`), because AST programs can diverge or fail even when
well-typed. Proving a `CompM` tree well-founded lets it be reified back into
a `Free` tree, so all comparisons ultimately happen between inductive
objects.

Composition principles live here, stated once for the generic monads:
well-foundedness, reification, and effect erasure distribute over bind. This
layer also supplies a way to reason about the results a finite tree can
return, which later layers need for threading invariants through binds.

## Object language

- **Types.** Machine integers, booleans, arrays, products, and function
  references. A subset of these is *ABI* types: the ones that may cross
  effect boundaries and program entry points. Function references are never
  ABI.
- **Expressions.** PHOAS in continuation-passing style. Each node binds its
  result for the rest of the program. The language should be just rich enough
  to express straight-line arithmetic, data construction and projection,
  branching, effects with blocks, closure creation, and calls.
- **Programs.** A telescope of top-level definitions, each able to refer to
  itself, followed by `main`. Recursion is expressed only through
  definitions; there are no special recursive-call nodes.
- **Effect signatures.** Signatures are given syntactically, with ABI-typed
  inputs, outputs, and block interfaces, and denote into the generic effect
  theory.

### Semantics

There is one evaluator, used both for execution and for proofs. It is a
corecursive machine over an explicit continuation stack and a heap of
closures. Administrative steps are silent (`Tau`). Ill-formed states, such
as a dangling or mistyped closure reference, step to `Fail`. Effects are
forwarded unchanged.

The heap only grows. That order is what lets facts proved about a closure
early in a program stay valid after later allocations.

## Correctness criterion

An AST fragment is correct with respect to a source computation when its
evaluation satisfies three conditions:

1. **Terminates.** Every path is finite.
2. **Never fails.** `Fail` is unreachable.
3. **Matches the source.** After erasing `Tau` and interpreting the AST's
   effects through a fixed handler, it is *equal* to the source computation.

The handler is the only point where AST effects and source effects meet. In
the minimal version it is the identity. For F2Z it will encode each AST
operation as a circuit gadget.

Correctness is stated against all heaps extending the current one, so it
composes across allocations. Intermediate results carry a postcondition
that their final heap extends the initial one. Without it, a certificate for
"evaluate this, then continue" cannot be assembled from certificates of its
parts.

At the top level, a program certificate says that for every input the whole
program is correct with respect to the source function. Inputs and outputs are
ABI values shared verbatim between source and AST, so no value relations are
needed at the boundary.

## Certificates

Certificates are built only through a small library of opaque rules, one per
syntactic construct, plus rules for installing definitions and assembling
programs. The rules hide the evaluator, the heap representation,
well-foundedness proofs, and reification. Generated proofs never unfold any
of them.

Function references are certified by a Kripke-style statement: in every
extended heap, calling the reference on any argument is correct with respect
to a source function. Call sites consume that statement. Definitions produce
it, and recursive definitions will produce it by well-founded induction
mirroring the source's own termination argument, never by unrolling.

The first iteration stays first-order: closures are call targets, not
values passed to specs. Higher-order values would need value relations and
are out of scope until a source program needs them.

## Macro

The macro walks an elaborated source term and emits two things in a single
traversal: the AST and the certificate. It recognizes monadic structure
(bind, return, operations), control flow, supported primitive operations on
ABI values, and calls to previously lifted definitions. Each recognized
form maps to one AST node and one certificate rule.

Design constraints:

- **Proof size.** It is linear in source size. No normalization of the
  source, no unfolding of recursion, and no unfolding of user definitions
  (definitions stay definitions in the AST).
- **Interface.** The macro depends only on the certificate rules, never on
  evaluator internals.
- **Diagnostics.** Unsupported constructs are rejected with a clear error,
  not approximated.
- **Regression tests.** They pin the emitted ASTs and the axiom footprint of
  the generated theorems.

## Roadmap

Each stage has its own document under [`Roadmap/`](Roadmap/).

1. [**Language completeness.**](Roadmap/1-Language.md) Make the object
   language expressive enough for the minimal milestone, mainly data
   construction and projection, and clean up leftovers in the definitions.
2. [**Generic composition theory.**](Roadmap/2-Composition.md) Make
   well-foundedness, reification, failure-freedom and erasure compositional
   over bind, and add reasoning about a tree's possible results.
3. [**Evaluator structure.**](Roadmap/3-Evaluator.md) Show that evaluation
   decomposes along the continuation stack, and that the heap only grows.
4. [**Certificate rules.**](Roadmap/4-Certificates.md) Prove a rule for each
   construct and for calls, non-recursive definitions, and programs. Validate
   them on hand-written certificates for small programs.
5. [**Minimal macro.**](Roadmap/5-Macro.md) Lift the minimal source fragment
   end to end, with tests.
6. [**Extensions.**](Roadmap/6-Extensions.md) Add loops and recursive
   definitions, a pretty-printer for the external compiler, and finally the
   F2Z handler and source language.
