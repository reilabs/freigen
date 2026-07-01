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
  b`) — the denotation is recursion-agnostic; nothing in the AST or `denoteProg` cares whether the
  program is recursive.  Plus a pretty-printer and the **`reflect%`** elaborator (non-recursive arm)
  returning `{ g : Closed // ∀ args, denoteProg (g KC Tp.denote) ⟨args⟩ ≈ ofFreeH (foo args) }`
  (`ofFreeH` only embeds the source `FreeH` for comparison).  The reflector reifies types into `Tp`,
  A-normalises pure computation into `un`/`bin`/`lit` atoms, keeps effects/scoped blocks opaque, and
  **spills each called helper function into a `def_`** via a two-pass discovery/build, monomorphised
  on its `(name, argument-types, result-type)` signature.  `main` may itself be a **function of the
  program's inputs** (`A₁ → … → Aₙ → FreeH …`), delivered as an `HList`.  Soundness goes through the
  faithful `FreeH` denotation `denoteProgF` (`denoteProg = ofFreeH ∘ denoteProgF` by `ofFreeH_bind`,
  `denoteProgF (reflect foo) = foo` by `rfl`), so it discharges to `Eutt.of_eq`.
- `Freigen/ITree/` — the coinductive denotation domain `Comp Op` (`ret`/`tau`/`vis`/`fail`), `bind` +
  monad/computation laws, weak bisimulation `≈` (`Eutt`) with its full construction algebra as a
  lawful `Setoid`, and the general-recursion combinator `mrec`.
- `Freigen/ScopedRec.lean` — **recursion on the `FreeH` pipeline**: the `mrec` adequacy restated over
  `ofFreeH` (`mrec_adequacyH`, generic over `SOp`), a `Code.ite` branch node, and the recursive arm of **`reflect%`** — a structural-recursive `def f : Nat → FreeH Op SOp ρ` reflects into `{ g // ∀ N,
  g N ≈ ofFreeH (f N) }` (its call-body re-expressed over `CallOp`, reflected to dumb `Code`, `mrec`
  tying the knot), for **tail and non-tail** recursion alike.
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
