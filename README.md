# Freigen

*frei* (free) + *eigen* (self) — a Lean library whose programs are **effectful free-monadic
computations** (`Free`, the source of truth), given meaning by Lean-side interpreters and
**reflected** into a dumb, typed imperative AST that **denotes into interaction trees**, with the
round-trip proven sound by weak bisimulation (`≈`, `ITree.Eutt`).

## The shape of a program

A program is a `Free Op SOp α` with **two orthogonal extension slots**:

- `Op : Type → Type → Type 1` — **first-order effects**, opaque instructions (e.g. `CircOp.assert`).
- `SOp : Type → Type` — **scoped constructs**: each operation carries an *in-monad block* (e.g.
  `HintS`, the out-of-circuit `hint`).  `NoScope` recovers a plain first-order DSL.

`Free` is the source of truth: run it in Lean, or `reflect%` it for compilation.  A scoped op's block
is a positive recursive occurrence in the monad (the `hop` constructor) — an ordinary inductive, so
there is no self-reference and **no function values inside ops**.

## Modules

- `Freigen/Effect.lean` — the `Effect Op` functor (an operation with its input): what a `Comp`'s
  `vis` node carries.
- `Freigen/Tp.lean` — the object-type universe `Tp` (`Bool`/`Nat`/`ZMod n`/`Unit`/`×`/`Vector`/
  `Array`/`⊕`/`→`) with `Tp.denote`, and the **reified** primitive ops `Un`/`Bin` (arithmetic,
  comparison, field ops, tupling, projection, injection, vector indexing) with their denotations and
  pretty-printer symbols.  Arithmetic is a *typed op node*, not an opaque closure.
- `Freigen/ITree/` — the coinductive denotation domain `Comp Op` (`ret`/`tau`/`vis`/`fail`), `bind` +
  monad/computation laws, weak bisimulation `≈` (`Eutt`) as a lawful `Setoid` with its congruence
  algebra, and the general-recursion combinator `mrec` (with `interp` and the call-extended signature
  `CallOp`).
- `Freigen/Free.lean` — the monad `Free Op SOp` (`pure`/`op`/`hop`) + `Monad` instance, and two
  **generic** Lean interpreters: `run` (witness generation — scoped blocks are *run*) and `con`
  (constrained — a `(α → Prop) → Prop` predicate transformer, scoped blocks *erased* to fresh
  existentials).  The scoped signatures `HintS`/`NoScope`, the `hint` combinator, and their handlers.
- `Freigen/Reflect.lean` — `ofFree` (the source's ITree semantics), the **dumb, typed imperative
  AST** `Code`/`Prog` (`ret`/`lit`/`un`/`bin`/`op`/`ite`/`call`/`scope`, top-level function
  definitions `def_` and recursive ones `rec_`, indexed by `Tp`, PHOAS over a function family
  `F : List Tp → Tp → Type 1` and values `V : Tp → Type`, with `Op`/`SOp` opaque), `denote`/
  `denoteProg` **uniformly into `Comp`** (a function denotes as a `Comp`-Kleisli subroutine, a `rec_`
  by `mrec`), a pretty-printer, and the **`reflect%`** elaborator.  `reflect%` reifies Lean types into
  `Tp`, A-normalises pure computation into `un`/`bin`/`lit` atoms, keeps effects/scoped blocks opaque,
  and **spills each called helper into a `def_`** (a two-pass discovery/build, monomorphised on the
  helper's `(name, argument-types, result-type)`).  `main` may itself be a function of the program's
  inputs.  It returns `{ g : Closed // ∀ args, denoteProg (g Tp.denote) ⟨args⟩ ≈ ofFree (foo args) }`
  (`ofFree` embeds only the *source* into `Comp` for comparison).  Soundness is a **compositional
  bisimulation**: the reflector records every source definition it unfolds and feeds them to a `simp`
  that unfolds `denoteProg`/`denote` and `ofFree` on both sides, so all binds fuse consistently and
  the two `Comp` trees converge.
- `Freigen/Recursion.lean` — the recursive arm of `reflect%`: a structural-recursive
  `def f : Nat → Free Op SOp ρ` reflects into a `Prog` with a **`rec_` node** (self-calls are the
  `CallOp.call` op, tied by `mrec`) and a `main` calling it — the *same* `{ g : Closed // … denoteProg
  … ≈ ofFree … }` shape.  Its soundness is `mrec` adequacy (`mrec_adequacy`/`recSound`): the reflector
  composes the `main`-call step (`bind_ret_right`) with the `rec_` body's adequacy.  Handles **tail
  and non-tail** recursion.  Because a `Prog` can contain `rec_`, there is no total `Prog → Free` map
  (`mrec` has no inductive counterpart): the AST does not — and cannot — assume termination.
- `Freigen/Examples/` — one module per signature:
  - `Circuit` — `CircOp` (first-order `assert`) + the scoped `hint`: witness generation `runCirc`,
    constrained semantics `conCirc`, and `reflect%` (including helper-calling and input-taking
    circuits) with `denoteProg … ≈ ofFree`.
  - `Storage` — `StoreOp` + `NoScope`: a hint-less DSL reusing the *same* pipeline with the scoped
    slot empty, an operational `runStore`, and the same `≈`-soundness.

## One line

Effects are first-order and opaque; scoped constructs carry an in-monad block and live in `hop`.
`reflect%` compiles a `Free` program into a typed imperative `Prog` — with reified arithmetic,
first-class functions (`def_`), and recursion (`rec_`) — and everything denotes into the same
interaction-tree domain `Comp`, sound by the uniform `≈`: `denoteProg (reflect% foo) ≈ ofFree foo`.
