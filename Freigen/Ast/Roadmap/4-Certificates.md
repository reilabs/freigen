# 4. Certificate rules

Part of the [AST design](../DESIGN.md). Goal: a small library of opaque
rules, one per construct, from which correctness of any minimal-fragment
program can be assembled without touching the evaluator.

## Current state

Expression and program certificates are stated in `Ast/Defs.lean`:
termination, failure-freedom, and equality with the source after erasure,
quantified over all extended heaps. Nothing is proved about them.

Everything the rules need underneath now exists:
- **Stage 2:** the pipeline relation, its bind law, and its equivalence with
  the pipeline.
- **Stage 3:** an unfolding equation per node, failure equations, heap
  growth, and the heap lemmas.

## Revisions to the statement

### Heap postcondition

The current statement projects away the final heap before comparing with the
source. That is enough at the top level, but it cannot be composed. To
certify "evaluate this, then continue", the continuation's certificate must be
applied at the heap the first part ended in, and that heap is gone.

Revision: the certificate exhibits the erased behaviour *with* final heaps,
such that projecting out the heaps gives the source computation. It does not
need to say that final heaps extend the initial one: stage 3 proves that for
every evaluation.

Certificates are stated with the stage 2 pipeline relation, which carries
no proof arguments. Bind is then its bind law, with stage 3 heap growth
supplying the reachable-heap hypothesis. The stage 2 congruence principle
projects the heaps out again.

The public program certificate keeps its pipeline form, since that is what
users read. It follows from the relation through the stage 2 equivalence,
so it is never proved directly.

### Result types

Certificates require an ABI result type, so the spec can be stated over
shared values. That stays: in CPS, a node's continuation produces the whole
expression's result. Only constructs that evaluate a sub-expression (branches
and calls) introduce an intermediate result. Those intermediate results are
restricted to ABI types in the first iteration.

## Rules

### Expressions

There is one rule per construct. Each rule says how a certificate for the node
follows from certificates for its parts, against the corresponding source
shape. Each rule is proved from the node's stage 3 equation. The equation's
silent steps are absorbed by the relation and never reach the source.
- **Return:** the source returns the same value.
- **Literals and builtins:** the continuation receives the literal or the
  builtin's result. Failure is never implemented, so a builtin that can fail
  (array access) needs a proof that it succeeds. The source must supply one,
  so the source shape the macro accepts determines how. For example, it could
  accept only indexing with an explicit bounds proof.
- **Branches:** the source branches on the same condition, then continues.
- **Effects:** the source performs the handler's image of the operation.
  Each block is certified independently in its own context, from the current
  heap, with its final heap dropped. The continuation is certified for every
  operation result.
- **Calls:** consume a function certificate for the callee, and certify the
  continuation for every result. The function certificate is what rules out
  the failing call cases: a missing closure, or a mismatched context or
  signature.

### Functions

A function certificate says that a heap reference implements a source
function: in every extended heap, calling it on any argument is certified
against the source function applied to that argument. It is the only way
certificates talk about closures.

### Definitions and programs

- **Non-recursive definition.** Certifying the body yields a function
  certificate for the freshly allocated reference.
- **Program assembly.** Install each definition in turn, then certify `main`
  under the resulting function certificates, for every input. The result is
  the public program certificate.

## Design notes

- **Opaque rules.** Rules are proved from stage 2 and 3 facts only. Their
  statements mention no machine states, heap contents, well-foundedness
  proofs, or reification.
- **Matching the macro.** Rule shapes should match what the macro sees in the
  source, so that rule conclusions unify with source terms up to cheap
  definitional unfolding.
- **Handler.** The handler is a parameter of every rule. In the minimal
  milestone it is the identity, but nothing may depend on that.
- **Out of scope:** closures as values (lambda certificates), loops, and
  recursive definitions; see [stage 6](6-Extensions.md). Stage 3 already
  provides equations for closure creation and loops, so these need only
  their rules.
- **Declaring signatures.** On the stage 1 test signature, terms inside
  blocks only typecheck by unfolding the signature's definition. Plain
  rewriting does not do that, and making the signature reducible breaks
  instance resolution. Settle how signatures are declared, so that rules
  apply to blocks by plain rewriting and unification. Macro-generated proofs
  cannot rely on workarounds.

## Validation

Hand-written certificates over the test signature from stage 1:
- straight-line arithmetic;
- a branch;
- an effect with a block;
- a program with a helper definition called twice.

These are the regression suite for the rules and the reference output for
the macro.

## Done when

Every rule is proved, and the hand-written examples check using only the
rules.
