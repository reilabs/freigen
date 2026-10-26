# 3. Evaluator structure

Part of the [AST design](../DESIGN.md). Goal: establish the structural
facts about the evaluator that every certificate rule relies on, so that
later stages never reason about machine states directly.

## Current state

The evaluator is a single corecursor. It runs over machine states consisting
of a heap, the expression being evaluated, and a stack of pending
continuations.

- Each administrative step emits one silent step.
- Effects are forwarded unchanged. Blocks run on the current heap, and their
  final heap is discarded.
- Calls look up the closure, check its context and signature, and fail if
  either doesn't match.

The public entry points are expression and program evaluation. No facts about
them are proved.

## What is needed

### Decomposition along the continuation stack

This is the central fact. Running an expression with a pending continuation
behaves like:
1. one silent step;
2. evaluating the expression on its own;
3. binding its final heap and result into the continuation.

It turns the evaluator's explicit stack into the monad's bind. Every
construct that evaluates a sub-expression and then continues relies on it:
branches, calls, loops, and blocks. The proof is a single bisimulation using
the existing up-to-equality principle for `ITree`.

Once it holds, each expression form has an unfolding equation: "evaluating
this node equals these effects, then evaluating that". Certificate rules are
proved from those equations alone.

### Heap discipline

- Allocation produces a strictly extended heap and returns a fresh reference.
- Lookup is stable under extension: a reference that resolves in a heap
  resolves to the same closure in every extension.
- Looking up a freshly allocated reference returns what was allocated.

These are lemmas about the heap data structure, proved once. After this stage
nothing mentions the hash map.

### Heap growth

Every heap an evaluation can end in extends the heap it started from. This
is stated with the reachable-results predicate from stage 2, after
reification, so it composes through bind like any other invariant.

### Programs

Program evaluation unfolds to allocating each definition in order, then
evaluating `main` in the resulting heap. Each definition's closure refers
to its own reference.

## Design notes

- These facts are the only interface between the evaluator and the
  certificate layer. If a certificate proof needs to unfold the corecursor,
  a fact is missing here.
- Blocks are the subtle case: they start from the current heap and their
  final heap is discarded. The decomposition for operations must reflect
  that, so that blocks behave like independent evaluations.

## Done when

Every expression form has an unfolding equation, the heap lemmas and
heap-growth invariant hold, and program evaluation has its unfolding. No
proof in this stage's consumers unfolds the corecursor.
