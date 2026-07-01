# Freigen

*frei* (free) + *eigen* (self) — a Lean DSL whose programs are **effectful free-monadic
computations** (`FreeH`, the source of truth), given meaning by Lean-side interpreters and
**reflected** into a dumb imperative AST that **denotes into interaction trees**, with the round-trip
proven faithful by weak bisimulation (`≈`, `ITree.Eutt`).

## The shape of a program

A program is a `FreeH Op SOp α` with **two orthogonal extension slots**:

- `Op : Type → Type → Type 1` — **first-order effects**, opaque instructions (e.g. `CircOp.assert`).
- `SOp : Type → Type` — **scoped constructs**: each operation carries an *in-monad block* (e.g.
  `HintS`, the out-of-circuit `hint`).  `NoScope` recovers a plain first-order DSL.

`FreeH` is the source of truth: run it in Lean, or `reflect%` it for compilation.  The block a
scoped op carries is a positive recursive occurrence in the monad (`hop`) — an ordinary inductive, so
no self-reference and **no function values in ops**.

## Modules

- `Freigen/Scoped.lean` — the monad `FreeH Op SOp` (`pure`/`op`/`hop`) + `Monad` instance, and the two
  **generic** Lean interpreters: `run` (witness generation — scoped blocks are *run*) and `con`
  (constrained — a `(α → Prop) → Prop` predicate transformer, scoped blocks *erased* to fresh
  existentials).  Scoped signatures `HintS`/`NoScope`, the `hint` combinator, and their handlers.
- `Freigen/Tp.lean` — the object-type universe `Tp` (`Bool`/`Nat`/`ZMod n`/`Unit`/`×`/`Vector`/
  `Array`/`⊕`/`→`) with `Tp.denote`, and the **reified** primitive ops `Un`/`Bin` (arithmetic,
  comparison, field ops, tupling, projection, injection, vector indexing) with their denotations and
  pretty-printer symbols.  Arithmetic is a *typed op node*, not an opaque closure.
- `Freigen/ScopedReflect.lean` — `ofFreeH` (the source's ITree semantics), the **dumb, typed
  imperative AST** `Code`/`Prog` (`ret`/`lit`/`un`/`bin`/`op`/`ite`/`call`/`scope`, plus `Prog.def_`
  for **top-level function definitions**, indexed by `Tp`, PHOAS over `F : List Tp → Tp → Type 1`
  and `V : Tp → Type`, `Op`/`SOp` opaque), `denote`/`denoteProg` **uniformly into the interaction-tree
  domain `Comp`** (a function denotes as a **`Comp`-Kleisli subroutine** `HList Tp.denote as → Comp Op
  b`).  A **`Prog.rec_`** node is a *recursive* function definition, denoted by `mrec`; its very
  presence makes a total `Prog → FreeH` map **impossible to define** (no `mrec` in an inductive
  monad), so the AST cannot — and does not — assume termination.  Plus a pretty-printer and the
  **`reflect%`** elaborator returning `{ g : Closed // ∀ args, denoteProg (g KC Tp.denote) ⟨args⟩ ≈
  ofFreeH (foo args) }` (`ofFreeH` only embeds the source `FreeH` for comparison).  The reflector
  reifies types into `Tp`, A-normalises pure computation into `un`/`bin`/`lit` atoms, keeps
  effects/scoped blocks opaque, and **spills each called helper function into a `def_`** via a
  two-pass discovery/build, monomorphised on its `(name, argument-types, result-type)` signature.
  `main` may itself be a **function of the program's inputs** (`A₁ → … → Aₙ → FreeH …`).  Soundness
  is a **compositional bisimulation** (no `FreeH` bridge): the reflector records every source
  definition it unfolds and feeds them to a `simp` that unfolds `denoteProg`/`denote` and
  `ofFreeH`/`ofFreeH_bind` on *both* sides, so scope- and call-binds fuse consistently and the two
  `Comp` trees converge — then `Eutt.of_eq`.
- `Freigen/ITree/` — the coinductive denotation domain `Comp Op` (`ret`/`tau`/`vis`/`fail`), `bind` +
  monad/computation laws, weak bisimulation `≈` (`Eutt`) with its full construction algebra as a
  lawful `Setoid`, and the general-recursion combinator `mrec`.
- `Freigen/ScopedRec.lean` — **recursion, first-class in `Prog`**: the `mrec` adequacy over `ofFreeH`
  (`mrec_adequacyH`/`recSound`, generic over `SOp`) and the recursive arm of **`reflect%`** — a
  structural-recursive `def f : Nat → FreeH Op SOp ρ` reflects into a **`Prog` with a `rec_` node**
  (its call-body re-expressed over `CallOp`, self-calls the `CallOp.call` op, `mrec` tying the knot)
  and `main` calling it.  It returns the *same* `{ g : Closed // ∀ N, denoteProg (g KC Tp.denote) ⟨N⟩
  ≈ ofFreeH (f N) }` shape as the non-recursive arm — the reflector composes the soundness as
  `bind_ret_right` (main's call into the recursive fn) ∘ `mrec_adequacy` (the `rec_` body).  Handles
  **tail and non-tail** recursion.  So one `reflect%` yields a uniform `{ g : Closed // … denoteProg …
  ≈ ofFreeH … }` for values, parameterized `main`s, helper-calling programs, and recursion alike.
- `Freigen/Free.lean` — the `Effect` functor (used by `Comp`'s `vis`) and the finite free monad
  `Free`/`ofFree` (used internally by `mrec` adequacy).
- `Freigen/Examples/` — one module per signature:
  - `Circuit` — `CircOp` (first-order `assert`) + the scoped `hint`: witness generation `runCirc`,
    constrained semantics `conCirc`, and `reflect%` with `denote (circC.1 Id) ≈ ofFreeH circ`.
  - `Storage` — `StoreOp` + `NoScope`: a hint-less DSL reusing the *same* pipeline with the scoped
    slot empty (`hop` nodes never occur), operational `runStore`, and the same `≈`-soundness.

## One-line summary

Effects are first-order and opaque; **scoped constructs** carry an in-monad block and live in `hop`,
so there is no self-reference and no function in any op.  `reflect%`/`denote` are generic over
`Op`/`SOp`, the block reflects like a `let`, and soundness is the uniform `≈` (`ITree.Eutt`) via a
single structural homomorphism — `denote (reflect% foo) ≈ ofFreeH foo`.  One `reflect%` does the right thing — a `FreeH` value or a structural `Nat` recursion.
