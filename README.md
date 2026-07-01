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

Five top-level concerns:

- **Free monads** — `Freigen/Free.lean` — the monad `Free Op SOp` (`pure`/`op`/`hop`) + `Monad`
  instance, and one **generic** interpreter `run`: fold a program into any monad `M`, given a handler
  for the first-order ops and one for the scoped ops (which receives the interpreted block, so it may
  run it, erase it, …).  Plus the trivial scoped signature `NoScope`.  *How* a scoped construct is
  interpreted is the handler's business — supplied by each example.
- **Semantics** — `Freigen/ITree/` — the coinductive denotation domain `Comp Op`
  (`Effect` functor + `ret`/`tau`/`vis`/`fail`), `bind` + monad/computation laws, weak bisimulation
  `≈` (`Eutt`) as a lawful `Setoid` with its congruence algebra, and the general-recursion combinator
  `mrec` (with `interp` and the call-extended signature `CallOp`).
- **AST** — `Freigen/Ast/` — `Ast.Tp` (the object-type universe `Tp` and the **reified** primitive
  ops `Un`/`Bin` — arithmetic is a *typed op node*, not an opaque closure) and `Ast.Basic` (the dumb
  typed AST `Code`/`Prog`: `ret`/`lit`/`un`/`bin`/`op`/`ite`/`call`/`scope`, top-level `def_` and
  recursive `rec_`, PHOAS over a function family `F` and values `V`; `denoteProg` **uniformly into
  `Comp`** — a function is a `Comp`-Kleisli subroutine, a `rec_` is tied by `mrec`; `ofFree`; a
  pretty-printer).  A `Prog` admits `rec_`, so it has no total map into a finite monad — the AST does
  not assume termination.
- **Reflection** — `Freigen/Reflect/` — `reflect%` compiles a `Free` program into a `Prog` with its
  `≈`-soundness against `ofFree`.  `Reflect.Basic` reifies Lean types into `Tp`, A-normalises pure
  computation into `un`/`bin`/`lit`, and **spills each called helper into a `def_`** (a two-pass
  discovery/build, monomorphised on the helper's `(name, argument-types, result-type)`); `main` may be
  a function of the program's inputs.  `Reflect.Recursion` adds the recursion arm (a structural
  recursion → a `rec_` node) with its `mrec` adequacy.  Soundness is a **compositional bisimulation**:
  the reflector records every source definition it unfolds and feeds them to a `simp` unfolding
  `denoteProg`/`denote` and `ofFree` on both sides, so all binds fuse and the `Comp` trees converge.
- **Examples** — `Freigen/Examples/` — `Circuit` (`CircOp` + scoped `hint`, `runCirc`/`conCirc`;
  hints, helper-calling and input-taking circuits, monomorphisation, multi-argument helpers, a
  `Vector` result), `Storage` (hint-less `StoreOp`, operational `runStore`), and `Recursion`
  (`countdown`/`sm`).  Every example proves its `≈`-soundness and pins its result/AST with
  `#guard_msgs`.

## One line

Effects are first-order and opaque; scoped constructs carry an in-monad block and live in `hop`.
`reflect%` compiles a `Free` program into a typed imperative `Prog` — with reified arithmetic,
first-class functions (`def_`), and recursion (`rec_`) — and everything denotes into the same
interaction-tree domain `Comp`, sound by the uniform `≈`: `denoteProg (reflect% foo) ≈ ofFree foo`.
