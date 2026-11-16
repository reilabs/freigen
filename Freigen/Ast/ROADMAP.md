# AST Roadmap (proposal)

What is still missing between the current AST pipeline and F2Z circuits.
This list covers only what remains. The code says how the parts that exist
work. Items are roughly in priority order. Each one names a decision that
must be made before work starts, where there is one.

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

The AST has `loop` and an unfolding equation (`Expr.denote_loop`), but no
certificate rule and no macro support.

- **Decision:** certify loops against source functions defined by
  well-founded recursion with an explicit measure, or emit them only from
  recognized iteration patterns (bounded folds, `for` over ranges). This
  depends on how F2Z sources iterate, so make it together with item 7.
- Then add the rule and its macro table entry.

## 3. Source fragment gaps

The macro rejects constructs that ordinary source code produces:

- **Conditions on decidable propositions** (`if x < y`). Today the source
  has to write `decide (x < y)`. Needs a rule for the elaborated `ite` with
  a `Decidable` instance, or a rewrite to the boolean form.
- **Destructuring / `match`**, at least on products (and on `Bool`/`Option`
  if F2Z sources need them).
- **Join points with several arguments**, which come from `let mut`.
  They need either tupling through `pair`/`fst`/`snd` or join points with
  several parameters.
- **Functions with several arguments.** Helpers and the entry point take
  exactly one argument. Either curry through tuples automatically, or
  extend definitions.
- **Array indexing and update.** `arrGet`/`arrSet` have no table entries.
  **Decision:** which source forms to accept (`xs[i]` with a bounds proof in
  scope, `xs[i]!`, `getD`) and how the success premise of `ExprCert.builtin`
  is discharged for each.

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

## 5. Handlers and registered rules

- **Non-identity handlers.** The rules already take the handler as a
  parameter. The macro hardcodes `idHandler`. The operation table must
  describe each operation's image under the handler.
- **Registered rules.** Users register entries ("this source function ↦
  this AST, with this proof") in the macro's table from outside the macro.
  A hand-lifted definition with its own function certificate is the base
  case. This covers algorithm changes, such as a source recursion
  implemented by an AST loop. It does not cover representation changes (see
  item 6).

## 6. Closures as values and value relations

Closures today are call targets only. Lambdas passed as values, and
function-typed arguments and results, need certificates that relate source
values to AST values by a relation indexed by type, instead of equality. The
same relations would let registered rules change data representations (for
example, source lists as AST arrays). Deferred until a source program needs
it.

## 7. F2Z

The goal of the whole roadmap. It needs its own design pass, which items
1–3 should not wait for.

- An F2Z effect signature, and a handler that encodes AST operations as
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

## 9. Housekeeping

- The heap-growth result (`le_of_mayReturn`, `Grows` in `Ast/Eval.lean`) is
  proved but not used anywhere. **Decision:** keep it for the recursion
  and loop rules if they turn out to need it, or delete it.
- Land the `speedup-binds` branch (cached `result` in `ExactCodensity`).
  Only the `CompM` observation laws should need to be proved again.
