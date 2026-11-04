# 4. Certificate rules

Part of the [AST design](../DESIGN.md). Goal: a small library of opaque
rules, one per construct, from which correctness of any minimal-fragment
program can be assembled without touching the evaluator.

## Current state

The public program certificate is stated in `Ast/Defs.lean`: termination,
failure-freedom, and equality with the source after erasure.

Everything the rules need underneath now exists:
- **Stage 2:** the pipeline relation, its bind law, and its equivalence with
  the pipeline.
- **Stage 3:** an unfolding equation per node, failure equations, and the
  heap lemmas. (Stage 3 also proves heap growth; the continuation form of
  certificates turned out not to need it.)

## Revisions to the statement

### Heap postcondition

The current statement projects away the final heap before comparing with the
source. That is enough at the top level, but it cannot be composed. To
certify "evaluate this, then continue", the continuation's certificate must be
applied at the heap the first part ended in, and that heap is gone.

Revision: the certificate quantifies over what runs next instead of exposing
what is left. It says that, from every heap extending the given one,
evaluating the expression and then handing its final heap and value to any
*good* continuation implements the source followed by that continuation's
source. A continuation is good from a heap if it implements its source on
every value from every heap extending that one. The final heap is only ever
passed to the continuation; the certificate never names it, and no source tree
carries heaps.

Composition is then passing a bigger continuation along: to certify "this,
then that", certify "this" with the continuation "that, then the outer
continuation", whose goodness is the second certificate. No bind law,
reachability argument, or heap growth is involved. Quantifying over extended
heaps does that work locally: allocation is the only step that changes the
heap, and it only needs the fact that it extends it.

Certificates are stated with the stage 2 pipeline relation, which carries no
proof arguments. Two places fix the continuation to the trivial one, which
returns the value and drops the heap: effect blocks, which the evaluator runs
independently, and the top level.

A heap effect in the effect stack was considered and rejected. Effect answers
are treated as chosen by the environment, so an open tree branching over every
possible lookup result is neither well-founded nor failure-free. Running the
state first brings final heaps back into results.

The public program certificate keeps its pipeline form, since that is what
users read. It follows from the relation through the stage 2 equivalence,
so it is never proved directly.

### Result types

Expression certificates are stated for any result type. Nothing in their
proofs needs ABI types, and requiring them would only restrict intermediate
results of branches and calls. The ABI requirement stays on program
certificates, where inputs and outputs cross the program boundary.

## Source shape

Rules follow the elaborated source term exactly. Whatever the elaborator
shares stays shared in the AST and the certificate, and whatever it
duplicates is duplicated. Nothing is normalized to fit a rule.

The relevant consequence is `do` notation's join points. When a branch is
followed by more code, the elaborator binds that code once as a local
function, puts the branch in tail position, and has each branch call it. So:
- a join point becomes a local closure and its uses become calls;
- branches are always certified in tail position;
- an early return is a branch that does not call the join point.

The first iteration only accepts join points with a single argument; those
taking several (from mutable variables) are rejected. Monadic padding the
elaborator inserts around them is definitionally invisible and needs no rule.

## Rules

### Rule format

All rules share one format, so that rules registered later (stage 6) are
the same kind of thing as the built-in ones. A rule consists of:
- a source pattern;
- an AST template, generic in the variable type, taking the argument
  variables and a continuation;
- premises certifying its holes: sub-terms such as branches, blocks, or
  bodies, each against its own source;
- a certificate for the continuation on every result.

Its conclusion certifies the template against the source pattern followed by
the source continuation. Rules hold for every heap, result type, continuation
and handler, unless a rule deliberately fixes the handler. Templates may take
any number of silent steps, and may allocate. Nested source terms then need
no special treatment: an inner term's continuation is the outer template.

The built-in rules below are instances of this format; they double as
evidence that it is general enough.

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
- **Branches:** the source branches on the same boolean. Conditions on
  decidable propositions are not accepted in the first iteration: the
  elaborated form is not definitionally a branch on a boolean.
- **Effects:** the source performs the handler's image of the operation.
  Each block is certified independently in its own context, from the current
  heap, with its final heap dropped. The continuation is certified for every
  operation result.
- **Local closures:** allocating a closure yields a function certificate for
  the fresh reference; the continuation is certified against any reference
  carrying one. This is the same content as a non-recursive definition, and
  covers join points. Closures are only called, never passed as values.
- **Calls:** consume a function certificate for the callee, and certify the
  continuation for every result. The function certificate is what rules out
  the failing call cases: a missing closure, or a mismatched context or
  signature.

### Functions

A function certificate says that a heap reference implements a source
function: the reference resolves to a body, and the body is certified against
the source function on every argument. It is stated at a single heap; it holds
in every extension because lookups are stable and expression certificates
already quantify over extensions. It is the only way certificates talk about
closures.

### Definitions and programs

- **Non-recursive definition.** Certifying the body yields a function
  certificate for the freshly allocated reference. The body is certified
  under the function certificates of the references it depends on, taken as
  assumptions, so a hand-lifted definition with its own proof fits the same
  way.
- **Program assembly.** Install each definition in turn, then certify `main`
  under the resulting function certificates, for every input. This needs an
  intermediate certificate for the rest of a program at a given heap. Its
  definition step says: if the rest is certified at every extended heap, for
  every reference that carries the definition's function certificate, then
  the whole is certified. Generated proofs then never mention allocation. The
  last step yields the public program certificate.

## Design notes

- **Opaque rules.** Rules are proved from stage 2 and 3 facts only. Their
  statements mention no machine states, heap contents, well-foundedness
  proofs, or reification.
- **Matching the macro.** Rule conclusions should unify with elaborated source
  terms without unfolding user definitions, so that matching a rule, built-in
  or registered, never sees through the source. Unfolding the signature, the
  handler and library definitions is fine: they are fixed and cheap.
- **Handler.** The handler is a parameter of every rule. In the minimal
  milestone it is the identity, but nothing may depend on that.
- **Out of scope:** closures as values, loops, and recursive definitions;
  see [stage 6](6-Extensions.md). Stage 3 already provides the loop
  equation, so loops need only their rule.
- **Declaring signatures.** Signatures are ordinary definitions. Types an
  operation involves, such as its output, are computed from the signature by
  unfolding it. Rules are applied as terms, and matching may unfold the
  signature, so this needs nothing special. Only hand-written proofs that
  rewrite inside blocks need `erw`, because tactic rewriting does not unfold
  the signature.

## Validation

Hand-written certificates over the test signature from stage 1:
- straight-line arithmetic;
- a branch followed by more code, through its join point;
- an effect with a block;
- a program with a helper definition called twice.

These are the regression suite for the rules and the reference output for
the macro.

## Done when

Every rule is proved, and the hand-written examples check using only the
rules.

**Status:** done. Certificates and rules are in `Ast/Cert.lean`; the old
pipeline-form expression certificate is gone from `Ast/Defs.lean`, which keeps
only the public program certificate. `Ast/Examples/Cert.lean` certifies the
four validation programs with rules alone.

Findings:
- **Tail variants.** Rules whose source ends in a bind (branches, effects,
  calls) also come in a tail-position form, with a return as the
  continuation. Binding into `pure` is the identity only by unfolding the
  monad's definition, which matching does not do, so the macro uses the tail
  forms.
- **Signatures.** The block example checks by plain rule application, so the
  test signature stays an ordinary definition.
- **Elaboration order.** Written as terms, some proofs need implicit arguments
  given explicitly (a literal's type, an effect's tag), because arguments
  elaborate before the conclusion is unified with the goal. The macro should
  emit fully explicit rule applications.
- **Moving function certificates.** A function certificate obtained at one
  definition must be moved by monotonicity to each later definition's heap
  where it is used. That is one small step per use and per later definition;
  stage 5 should emit them lazily, only for certificates a body actually
  uses.
