# 4. Certificate rules

Part of the [AST design](../DESIGN.md). Goal: a small library of opaque
rules, one per construct, from which correctness of any minimal-fragment
program can be assembled without touching the evaluator.

## Current state

Expression and program certificates are stated in `Ast/Defs.lean`:
termination, failure-freedom, and equality with the source after erasure,
quantified over all extended heaps. Nothing is proved about them.

## Revisions to the statement

### Heap postcondition

The current statement projects away the final heap before comparing with the
source. That is enough at the top level, but it cannot be composed. To
certify "evaluate this, then continue", the continuation's certificate must be
applied at the heap the first part ended in, and that heap is gone.

Revision: the certificate exhibits the erased behaviour *with* final heaps.
The behaviour satisfies two conditions:
- projecting out the heaps gives the source computation;
- every final heap extends the initial one.

Bind is then the stage 2 congruence principle plus the stage 3 heap growth.

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
shape:
- **Return:** the source returns the same value.
- **Literals and builtins:** the continuation receives the literal or the
  builtin's result.
- **Branches:** the source branches on the same condition, then continues.
- **Effects:** the source performs the handler's image of the operation.
  Each block is certified independently in its own context, and the
  continuation is certified for every operation result.
- **Calls:** consume a function certificate for the callee, and certify the
  continuation for every result.

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
  recursive definitions; see [stage 6](6-Extensions.md).

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
