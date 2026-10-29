# 2. Generic composition theory

Part of the [AST design](../DESIGN.md). Goal: make every ingredient of the
correctness criterion compositional over bind, at the level of the generic
monads. Nothing in this stage mentions the AST.

## Starting point

What existed before this stage:

- **`Free`** has a good API: injectivity and disjointness of constructors,
  recursion and case analysis, and interpretation into another monad with
  laws for return, bind and operations. It also has the effect-stack
  operations erasure needs: extending with an unused effect, detecting
  that an effect is unused, and eliding it.
- **`CompM`** has observation, corecursion, the basic operations, loops, and
  lifting and partial interpretation of effect sums. Its laws live on the
  underlying `ITree` and are not exposed at the `CompM` level.
- **Well-foundedness and reification** are defined, but no lemmas about them
  exist.

## What is needed

The correctness criterion is a pipeline:

1. prove the tree well-founded;
2. reify it;
3. show `Fail` is unused and elide it;
4. erase `Tau`;
5. interpret the remaining effects.

For each step, this stage provides how it interacts with return, operations,
silent steps, and bind. Bind is the important one.

### Observation laws for `CompM`

Proofs about `CompM` should never see the codensity encoding or the
underlying tree. That requires laws describing what observing a return,
an operation, a silent step, and a bind yields. The `ITree` versions already
exist; this is a matter of transporting them.

### Well-foundedness

Return, operations and silent steps preserve well-foundedness. For bind,
the first computation must be well-founded, and the continuation must be
well-founded on every result the first computation can actually produce,
not on all values. The weaker hypothesis matters: later stages only know
facts about the continuation at reachable heaps.

### Reification

Reification commutes with return, operations and bind. Because
well-foundedness is a proposition, these laws hold regardless of which proof
is used, so they can be stated as plain equations.

**Decision:** reification and elision get return and operation equations,
but no bind equations. Each takes a proof argument (well-foundedness,
failure-freedom). A continuation only has that proof at reachable results,
so "the reification of the continuation" is not a function on all values.
Bind is handled once, for the whole pipeline (see below).

### Erasure

Being unused, eliding an unused effect, erasing silent steps and
interpretation all distribute over bind. Interpretation already does;
the rest needs the same treatment.

**Decision:** elision is defined by structural recursion on the raw tree,
guarded by an inductive "never performs the left effect" predicate, and lifted
to `Free`. The old definition went through `Free.recOn`, whose casts do not
reduce on an operation followed by a continuation, so no equations could be
proved about it.

### Reachable results

A predicate on finite trees saying "every value this tree can return
satisfies P". It needs the following laws:
- introduction and elimination for return, operations and bind;
- a congruence principle: two continuations that agree on all reachable
  results give equal binds.

This predicate is how invariants, such as heap growth, get threaded through
binds without a general relational theory.

**Decision:** the predicate exists on both `Free` and `CompM`, as
`MayReturn`: some effect interpreter could make the computation return this
value. The interpreter decides every operation's output, so any output is
allowed and blocks play no part. This is exactly as precise as the pipeline
relation below, which also requires continuations for every output. The
`CompM` one is primary: it is what the
evaluator-side invariants (heap growth) are stated with, and reification
preserves it exactly.

### The pipeline as one relation

**Decision:** the five steps are packaged as one relation, "this computation
implements that source computation". It is defined by one rule per node shape:
return, silent step, and operation, with blocks and the continuation
implemented pointwise. It is proved equivalent to the pipeline, so it is
exactly the correctness criterion, with no proof arguments in the statement.

Its bind law is the composition principle the later stages use. If the first
part implements a source computation, and the continuation implements a source
continuation on every reachable result, then the bind implements the bind.
Failure is never implemented, and the source can only return what the
implementation can.

## Design notes

- Everything here is generic in the effect signature and the contexts. Block
  contexts must not need special treatment at this level.
- Statements use the `Free`/`CompM` APIs only. No proof outside this layer
  should need to unfold `ExactCodensity`, `IxPoly.W`, or `IxPoly.M`.
- The `speedup-binds` branch changes how `CompM` bind is represented. Only
  the observation laws see that representation, so landing it later means
  reproving those laws and nothing else.
- Simp lemmas about operations mark the operation's output type `no_index`.
  On a concrete signature, simp's index reduces that type (to `Nat`, say), and
  an indexed `Eff.Spec.output` would never match. New operation lemmas must do
  the same.

## Done when

All five pipeline steps have return/operation/silent-step/bind laws, the
reachable-results predicate has its congruence principle, and a toy example
proves the full pipeline for a two-step `CompM` program using only these
laws.

**Status:** done. The observation laws are in `CompM/Basic.lean`; reachable
results in `CompM/MayReturn.lean` and `Free/MayReturn.lean`; well-foundedness and
reification in `CompM/WF.lean`; erasure in `Free/Erase.lean`; the pipeline
relation in `CompM/Implements.lean`. The example (`CompM/Examples/Implements.lean`)
composes a step that fails on even inputs after a step that only returns
odd ones.
