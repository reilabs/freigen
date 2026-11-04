# 3. Evaluator structure

Part of the [AST design](../DESIGN.md). Goal: establish the structural
facts about the evaluator that every certificate rule relies on, so that
later stages never reason about machine states directly.

## Current state

The evaluator is a single corecursor. It runs over machine states consisting
of a heap, the expression being evaluated, and a stack of pending
continuations. A state is either finished with a value, or an expression
under a continuation.

- Each administrative step emits one silent step.
- Builtins that have no result (out-of-bounds array access) fail.
- Effects are forwarded unchanged. Blocks run on the current heap, and their
  final heap is discarded.
- Calls look up the closure, check its context and signature, and fail if
  either doesn't match.

The public entry points are expression and program evaluation. No facts about
them are proved.

## What is needed

### Coinduction for `CompM`

Equalities between evaluator computations are proved by bisimulation. The
principle exists on `ITree`, but stage 2's rule is that proofs never see the
underlying tree, so it first gets a `CompM` version. The relation is indexed
by context and result type, because blocks run in a different context.

### Decomposition along the continuation stack

This is the central fact. Running an expression under a pending continuation
*equals* evaluating the expression on its own and binding its final heap and
result into the continuation. There is no extra silent step: silent steps
belong to the individual nodes.

It is stated once for machine states in general. Machine states carry their
own bind, which appends a continuation. The corecursor turns that bind into
`CompM` bind. Every construct that evaluates a sub-expression and then
continues is an instance: calls, branches, loops, and the return to a pending
continuation. Blocks need nothing extra: they finish independently of the
outer continuation, so they are identical on both sides, and behave as
independent evaluations whose final heap is dropped.

### Unfolding equations

Each expression form gets an equation: "evaluating this node equals these
effects, then evaluating that", stated with the `CompM` operations only:
silent steps, operations, failure, and bind. Failing cases are part of the
equations: a builtin without a result and a call to a missing or mistyped
closure both evaluate to failure. Those are where stage 4's side conditions
come from.

Loops get their equation too (run the body, then loop again or continue),
even though loop certificates are out of scope until stage 6.

Certificate rules are proved from these equations alone.

### Heap discipline

- Allocation produces an extended heap and returns a fresh reference.
- Lookup is stable under extension: a reference that resolves in a heap
  resolves to the same closure in every extension.
- Looking up a freshly allocated reference returns what was allocated.

These are lemmas about the heap data structure, proved once. After this stage
nothing mentions the hash map.

### Heap growth

Every heap an evaluation may end in extends the heap it started from:
whenever evaluation from a heap may return a final heap, that heap extends
the initial one. It is stated with the stage 2 `MayReturn` predicate,
directly on the evaluator's computation, which is the form the stage 2 bind
law consumes.

The proof cannot follow the expression's structure, because calls jump into
closures from the heap. It goes by induction on the finite path to the
result, with an invariant over all machine states.

Because this holds for every evaluation, certificates do not need to carry
heap growth as a postcondition of their own. (Stage 4 ended up stating
certificates over continuations, which made this fact unnecessary there.)

### Programs

Program evaluation unfolds to allocating each definition in order, then
evaluating `main` in the resulting heap. Each definition's closure refers
to its own reference. The unfolding is definitional; the only real content
is the lookup-after-allocation lemma.

## Design notes

- These facts are the only interface between the evaluator and the
  certificate layer. If a certificate proof needs to unfold the corecursor,
  a fact is missing here.
- Equations are equalities of computations, not up to silent steps. The
  pipeline relation from stage 2 absorbs silent steps one rule at a time.

## Done when

The decomposition holds, every expression form has an unfolding equation,
the heap lemmas and heap-growth invariant hold, and program evaluation has
its unfolding. A sample program on the stage 1 test signature is rewritten
into silent steps, operations and binds using the equations only. No proof
in this stage's consumers unfolds the corecursor.

**Status:** done. The `CompM` coinduction principle is in `CompM/Basic.lean`,
and the invariant principle for `MayReturn` of corecursive computations in
`CompM/MayReturn.lean`. Heap lemmas are in `Ast/Heap.lean`; machine-state
bind, the decomposition, the unfolding equations, heap growth and the program
facts are in `Ast/Eval.lean`. `Ast/Examples/Eval.lean` unfolds a program with
a twice-called helper, and one with a block.

Builtins and calls also get single equations that case on the result, for
rewriting when it is computable. On the concrete test signature, terms inside
blocks only typecheck by unfolding the signature's definition, so rewriting
there needs `erw`. This only affects hand-written proofs: the certificate
rules and the macro unfold the signature as needed (see stage 4).
