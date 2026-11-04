# 5. Minimal macro

Part of the [AST design](../DESIGN.md). Goal: lift source programs in the
minimal fragment to AST programs automatically, together with their program
certificates.

## Current state

There is no macro yet. Stage 4 provides every rule it needs, and hand-written
certificates for four programs that serve as reference output.

## Source fragment

The source fragment is `Free` programs, taken as elaborated, built from:
- return, bind, and operations (with blocks);
- `if` on booleans, including the join points `do` notation introduces for
  code following a branch;
- `let`;
- builtin arithmetic and comparisons on ABI values, and literals;
- data construction, and projection by field access;
- calls to other source definitions in the same fragment, which become AST
  definitions.

Conditions must be booleans. A comparison such as `x < y` elaborates to a
proposition, so sources write `decide (x < y)`, or use boolean operators such
as `==`. Errors on propositions should say so.

The first iteration rejects:
- conditions on decidable propositions;
- destructuring, which elaborates to a pattern match;
- join points taking several arguments, which come from mutable variables.

Operations, builtins and source definitions are recognized through an
explicit table in the macro, from source head symbol to stage 4 rule. Source
definitions are assumed to already have the shape of AST definitions: one
input, one fixed context, monomorphic.

An argument that is not a variable, such as `print (x + 1)`, is first bound
as the result of its own node, then passed on. This follows the elaborated
term, so a subterm the source repeats is translated each time.

Anything else is rejected with an error pointing at the offending subterm.

## Structure

### Planning

Each source definition becomes one AST definition, never inlined. Eventually
the macro collects the definitions reachable from the entry point and orders
them so callees come first. The first version takes them as an explicit list
in dependency order instead.

### Emission

A single traversal of each definition body produces both the AST fragment and
its certificate, by applying the matching stage 4 rule at each node. Only the
structural forms are handled directly: bind, return, `let`, and join points.
Everything else is dispatched through the rule table, with built-in rules
registered there like any other entry. Rules carry no macro code of their
own: emission instantiates the template, recursively emits the holes, and
continues with the continuation.

The AST is generic in its variable type, while certificates are about the
evaluator's instance, where an AST variable of a type is a value of that
type's denotation. So the traversal keeps a map from source variables to AST
variables and builds the AST once, generically. The AST the certificate talks
about is the same term specialized to the evaluator's instance, with each AST
variable replaced by its source variable.

Rule applications are built as terms with every argument given explicitly,
not elaborated from syntax: elaboration fixes arguments before the
conclusion is matched against the goal, which breaks hand-written proofs in
places. The kernel checks the result once.

The traversal's environment maps:
- source local variables to AST variables;
- source definitions and join points to their AST references and function
  certificates.

Each closure, whether a definition or a join point, moves certification to a
new, larger heap. Function certificates obtained earlier are moved to the
current heap before use. The first version moves all of them at every new
heap; moving only those a body uses is an optimization for later.

### Assembly

Thread the definitions through program assembly, finishing with the entry
point. The output is a closed AST program plus a theorem stating its program
certificate against the source.

### Interface

A command that, given a source entry point, its helper definitions, and the
operation table, adds two declarations: the AST program and its correctness
theorem. The first version fixes the handler to the identity; other handlers
need the table to describe each operation's image under the handler.

## Design notes

- **No normalization.** The macro never reduces the source beyond what is
  needed to recognize the next construct, and never unfolds user definitions
  or recursion. In particular it never inlines a local binding such as a join
  point: that would duplicate code the elaborator shared. Proof size stays
  linear in source size.
- **Untrusted.** If the macro emits a wrong AST, the certificate fails to
  check. It still aims to fail early with a readable error rather than
  produce a term the kernel rejects.
- **Extensible.** Adding a construct means adding a table entry, never
  changing the traversal. Registering entries from outside the macro is a
  stage 6 extension; the table must not assume it is closed.
- **Rules only.** The macro depends only on stage 4 rules. It never refers to
  evaluator internals or to stage 2/3 lemmas.

## Testing

First version:
- The four stage 4 programs are lifted, and each generated AST is checked
  equal to the hand-written one.
- New programs: a maximum via a branch, a chain of helpers, an effect inside a
  branch, and sequential branches.
- The axiom footprint of the generated theorems is pinned.
- Negative tests: a branch on a proposition, destructuring, an unknown
  function.

Later:
- Elaboration-time and proof-size checks on larger generated inputs: long
  definition lists, many call sites, deep binds, and long chains of
  sequential branches, whose join points must not blow up.

## Done when

The command lifts every example in the fragment end to end, and the tests
above are in CI. The first version is done when its tests pass; automatic
planning, other handlers and the scale tests follow.

**Status:** first version done. The macro is in `Ast/Macro.lean`, with the
identity handler, which lives with the certificates. The traversal handles
bind, return, `let` and join points; everything else goes through the rule
table. Its entries are data: a source pattern, the rule and its tail variant,
and the rule's arguments as functions of the pattern variables. Literals and
builtins are listed as source patterns; raw operations, branches, and calls
to helpers and join points are entries too. Applying any entry is the same
code. Only the certificate is built; the AST is read off its conclusion and
generalized over the variable type, then type-checked before it is added.

`Ast/Examples/Macro.lean` lifts the four stage 4 programs, whose ASTs equal
the hand-written ones, and pins the ASTs of further programs: repeated
subterms, a branch followed by a bind, an eta-reduced continuation, boolean
and unit literals, and arrays. It also lifts a maximum via projections, a
chain of helpers, effects in sequential branches with a block, and raw input
operations. It pins the axioms, and the errors for a branch on a
proposition, destructuring, an unknown call, a user definition, and a join
point with several arguments. Forty sequential branches lift in well under a second.

Findings:
- **Operations.** Listed wrappers are unfolded to raw operations. An operation
  input that is not a variable, such as a literal, is bound first.
- **Empty blocks.** Operations without blocks get a canonical eliminator over
  the empty block type in the AST. The test signature's AST helpers use the
  same form, so lifted ASTs compare equal by unfolding.
- **Builtins.** Success proofs are reflexivity: every builtin's semantics
  matches the corresponding source operator by unfolding.
- **Join points.** The certificate substitutes a join point's definition with a
  single beta-redex, so it is never duplicated.
- **Matching.** Patterns and rule conclusions are matched by unification that
  may unfold the signature, the handler, reducible definitions, instances and
  projections, but never user definitions; a test pins that a user definition
  unfolding to a builtin is rejected rather than seen through.
- **Operands.** A non-variable operand is bound by re-instantiating the
  entry's pattern with a new variable in its place, so each occurrence is
  translated separately, and instances inside the pattern stay consistent.
