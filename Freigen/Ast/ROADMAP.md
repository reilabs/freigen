# AST Roadmap (proposal)

What is still missing between the current AST pipeline and F2Z circuits.
This list covers only what remains. The code says how the parts that exist
work. Items are roughly in priority order. Each one names a decision that
must be made before work starts, where there is one.

## 0. Lifting `Circuit` programs: open points

`lift_program … via lift` lifts simple circuits
(`Circuit/Examples/Sqrt.lean`). Still missing or rough:

- **Field literals.** There is no primitive for `(2 : ZMod P)`. `0` and `1`
  are not definitionally casts of naturals when `P` is a variable, so they
  need their own primitives or a rule with a proof.
- **Vector literals** have one rule per size (up to 4).
- **Repeated subterms** are translated at each occurrence (`ins[0]` three times
  in `srcMore`), as for every language.
- **Erased values in branches.** Branches (`ite`) reflect their result type,
  so they cannot return values represented by a relation (`Cert`,
  `CertW`). Join points over such values are untested.
- **Representatives.** A value without an AST type is represented by its
  erasure, which must be an atom in scope or a subterm of the source. A
  `Cert` built where no unit value is in scope cannot be represented.
- **Semantics behind the lift.** The circuit lift represents each DSL
  operation by an AST operation, erasing results, block inputs and block
  results at fixed representations. What a certificate means for running a circuit needs
  a theorem: interpreters of the AST and the DSL whose operations commute
  with the erasure (a hint returns fresh wires carrying its block's results, an assertion its
  certificate) give results that agree up to erasure. It needs the DSL's
  semantics as an interpreter first.
- **Binder names in errors.** Errors name a certificate by the rule's binder
  (`r`), not the source's (`c`): the source continuation is substituted
  before its binder name is read.
- **Developer experience.**
  - Rules must type the AST's binders as `(model P).V t`. This is checked (the
    AST may not mention the language's parameters), but the error is
    internal-sounding.
  - The language's parameters keep their binder kinds, so certificates read
    `(P : ℕ) [ctx : Context P]`.
  - Hand-written certificates need many explicit arguments, because Lean cannot
    infer the source context, and elaborates rule arguments before the goal.
- **`fsqrt`** is a circuit-specific primitive and classical for now. Once loops
  exist, it is to be implemented by exponentiation in the AST.

## 1. Recursive definitions

**Blocker for most real programs.** `ProgCert.define` certifies a body for
any self-reference, without a function certificate for it, so a body
that calls itself cannot be certified.

- A rule for self-referencing definitions. The function certificate is
  proved by well-founded induction that mirrors the source's termination
  argument. The induction hypothesis certifies recursive calls on smaller
  arguments, so AST termination follows from the same argument.
- Macro support: recognize the recursion scheme Lean compiled the source to
  (structural / `WellFounded.fix`) without unfolding it, and emit a
  self-referencing AST definition.
- Tests pin that recursion stays symbolic in the emitted AST.

## 2. Loops

`for h : i in lo...<hi` with a `UInt32` counter and step 1 lifts to
`Expr.forRange` (`Ast/Loop.lean`), with `break` in a branch that has an
`else`. Still missing:

- **Several mutable variables.** The do-elaborator threads them through the
  loop as one `MProd` state, which has no AST type. Needs a representation
  of `MProd` as nested `prod` (with item 3's several-argument join points,
  which the same sources produce).
- **`break` or `continue` without `else`**, which leave the rest of the body
  in a join point over the state and the branch's result (item 3).
- **`Nat` ranges** (`[a:b]`), which all current F2Z sources use. Their
  counter has no injective `u32` representation, so they need a bound
  `hi < 2^32` as a side condition.
- **Other ranges**: closed and open bounds, steps other than 1, and
  iteration over arrays and vectors.
- **General `Expr.loop`**, certified against source functions defined by
  well-founded recursion with an explicit measure. Decide together with
  item 7 whether F2Z sources need it.

## 3. Source fragment gaps

The macro rejects constructs that ordinary source code produces:

- **Non-dependent conditions on propositions** (`if x < y`, without `h :`).
  The dependent form is supported, so `ite` on a decidable proposition can
  be certified as `dite` with constant branches.
- **Destructuring / `match`**, at least on products (and on `Bool`/`Option`
  if F2Z sources need them).
- **Join points with several arguments**, which come from `let mut`.
  They need either tupling through `pair`/`fst`/`snd` or join points with
  several parameters.
- **Functions with several arguments.** Helpers and the entry point take
  exactly one argument. Either curry through tuples automatically, or
  extend definitions.
- **More array forms.** `xs[i.toNat]'h` and `xs.set i.toNat v h` are
  supported, with `u32` indices and a bounds proof. Missing: `xs[i]!` and
  `getD` (a builtin with a default, or a bounds check in the AST), indices
  of other types, and array literals (`#[a, b]`).

## 4. Macro scaling and ergonomics

- **Automatic planning.** Collect the definitions reachable from the entry
  point and put them in dependency order, instead of the explicit `using`
  list.
- **Lazy certificate moves.** `withHeap` moves every function certificate
  at every new heap, so the cost grows with the number of definitions times
  the number of closures. Move only the certificates a body actually uses.
- **Scale tests.** Pin elaboration time and proof size on large generated
  inputs: long definition lists, many call sites, deep binds, and long chains
  of sequential branches.

## 5. Registered rules

- **Rules for source functions.** Users register entries ("this source function ↦
  this AST, with this proof") in the macro's table from outside the macro.
  A hand-lifted definition with its own function certificate is the base
  case. This covers algorithm changes, such as a source recursion
  implemented by an AST loop. Representation changes go through registered
  relations (see item 6).
- **Infer tail-position rules.** Every `_tail` rule (`ite_tail`,
  `dite_tail`, `op_eq_tail`, `app_tail`, and the Circuit ones) is its bind
  rule with `tk := pure` and `k := .ret`, and `x >>= pure` is `x` by `rfl` for
  `Free`. The macro can treat a source `x` in tail position as `x >>= pure`
  and apply the bind rule, discharging the continuation by `ret`. The
  `_tail` theorems, the entries' `tailRule`/`tailArgs` and the `.tail` rule
  kind then go, and rule authors write only the bind form. Hand-written
  certificates using the tail rules are rewritten with the bind rules.

## 6. Closures as values

Closures are call targets only: lambdas passed as values, and function-typed
arguments and results, need a representation of functions, whose erasure
would relate source functions to AST closures. Closures are heap references,
so this is not a function of the value alone. Deferred until a source program
needs it. Representations could also change data layouts (source lists as AST
arrays), which no rule does yet.

## 6b. Generic representations

Each lift fixes injective representations of the source types it supports
(`Lift.Rep`, indexed by the AST type and the source type, with the erasure at
each). Every value crossing an operation is represented at both its types
(`Lift.OpRep`), and program certificates state the representation of the
result. Still missing:

- User types. The lift's representation type gets closure constructors
  (products, subtypes, and a structure as an equivalence to a product of its
  non-`Prop` fields), erased by the same function; injectivity is proved once
  by recursion on representations. The macro then generates representations
  for the user types it meets, never erasers. The equivalence in a
  structure's representation is the one generated part an auditor has to
  check.
- Program inputs of non-object types. Inputs are AST values today; the
  certificate would hold for erasures of source inputs, so invariants become
  preconditions.
- A source type may have several representations (`Fin n` kept or as
  `u32`). Each has a default, overridable explicitly. The macro inserts
  conversions where two choices meet.
- Ghost variables and the rewriting of projections (`w.val`) are replaced
  by projection rules derived from the representation.

## 7. F2Z

The goal of the whole roadmap. It needs its own design pass, which items
1–3 should not wait for.

- An F2Z language, and a handler that encodes AST operations as
  circuit gadgets.
- **Decision:** how payloads that are not ABI values today, such as linear
  combinations, cross effect boundaries: an ABI encoding, or an extension
  of the ABI.
- **Decision:** the numeric types (field elements, bit-vectors of other
  widths) and their builtins.
- Macro support for the F2Z source language, including whatever iteration
  form item 2 settles on.

## 8. External format

`Ast/Print.lean` prints programs as S-expressions with a documented grammar.
Still needed:

- The format's semantics written down for the external compiler, in terms of
  the evaluator: division and remainder by zero, `u32` wrap-around, array
  lengths modulo 2^32, and when evaluation fails (out-of-bounds access).
- A parser and a round-trip test, since the printer promises the format
  can be parsed back.

## 9. Passes

Join-point elimination (`Program.joinPoints`) is proved to preserve
`CompM.Eutt`, and so certificates, for well-formed programs. Still missing:

- **Running it.** Nothing applies the pass: lifted programs are printed
  as the macro emits them. The macro could prove `Program.Wf` (`ast_wf`)
  and state the certificate of the translation.
- **Closures that stay.** A join point with an early-return path, or one
  called more than once outside tail position, stays a closure. Single-use
  closures could be inlined; join points with several arguments (from
  `let mut`) need the macro to support them first (item 3).
- **Hypotheses.** The pass needs `Language.Blocks`, which repeats
  `Language.Print.blocks`, and the theorem needs `Language.PrimFnFree`
  (primitives neither take nor return references).
- **Shared infrastructure.** Further passes reuse `Eutt`, `Wf` and the
  reference-relating simulation of `Ast/JoinPoints/Rel.lean`, which is
  specific to this pass today.
