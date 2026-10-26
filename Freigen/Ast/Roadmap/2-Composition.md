# 2. Generic composition theory

Part of the [AST design](../DESIGN.md). Goal: make every ingredient of the
correctness criterion compositional over bind, at the level of the generic
monads. Nothing in this stage mentions the AST.

## Current state

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

### Erasure

Being unused, eliding an unused effect, erasing silent steps and
interpretation all distribute over bind. Interpretation already does;
the rest needs the same treatment.

### Reachable results

A predicate on finite trees saying "every value this tree can return
satisfies P". It needs the following laws:
- introduction and elimination for return, operations and bind;
- a congruence principle: two continuations that agree on all reachable
  results give equal binds.

This predicate is how invariants, such as heap growth, get threaded through
binds without a general relational theory.

## Design notes

- Everything here is generic in the effect signature and the contexts. Block
  contexts must not need special treatment at this level.
- Statements use the `Free`/`CompM` APIs only. No proof outside this layer
  should need to unfold `ExactCodensity`, `IxPoly.W`, or `IxPoly.M`.
- The `speedup-binds` branch changes how `CompM` bind is represented. If it
  is going to land, it should land before this stage, since every proof here
  touches bind.

## Done when

All five pipeline steps have return/operation/silent-step/bind laws, the
reachable-results predicate has its congruence principle, and a toy example
proves the full pipeline for a two-step `CompM` program using only these
laws.
