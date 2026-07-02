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
  ops: total `Un`/`Bin` — arithmetic is a *typed op node*, not an opaque closure — and **partial**
  `POp` with `Option`-valued denotation: `vget`/`vset`/`aget`/`aset`/`arrToVec`/`natToFin`) and
  `Ast.Basic` (the dumb typed AST `Code`/`Prog`:
  `ret`/`lit`/`un`/`bin`/`pop`/`vec`/`arr`/`fold`/`op`/`ite`/`call`/`scope`,
  top-level `def_` and recursive `rec_`, PHOAS over a function family `F` and values `V`; `denoteProg`
  **uniformly into `Comp`** — a function is a `Comp`-Kleisli subroutine, a `rec_` is tied by `mrec`;
  `ofFree`; a pretty-printer).  The single `pop` node carries every **proof-erased** partial
  primitive (a bare `Nat` index, no in-bounds proof), so its denotation is *partial* — a failing
  `POp.denote` (an out-of-range access, a size mismatch) is `fail`.  A
  `Prog` admits `rec_`, so it has no total map into a finite monad — the AST does not assume
  termination.  `fold` is a **first-class bounded loop** (`Fin.foldl`: a static trip count, a
  `Fin`-indexed body) — loops are *kept as control flow*, never unrolled, and their denotation is
  total and `tau`-free (so a pure loop is *equal*, not merely `≈`, to its source fold).
- **Reflection** — `Freigen/Reflect/` — `reflect%` compiles a `Free` program into a `Prog` with its
  `≈`-soundness against `ofFree`.  `Reflect.Basic` reifies Lean types into `Tp`, A-normalises pure
  computation into `un`/`bin`/`lit` (and a source `coll[i]` / `coll.set i x` into proof-erased
  `pop` nodes), and **spills each called helper — `Free`-valued or pure — into a `def_`**
  (definitions stay *folded*, never inlined; helper bodies may call other helpers, spilled in
  dependency order; a reifiable pure `let` keeps its sharing) (a two-pass
  discovery/build, monomorphised on the helper's `(name, argument-types, result-type)`); `main` may be
  a function of the program's inputs.  `Reflect.Recursion` adds the recursion arm (a structural
  recursion `Nat → A₁ → … → Free Op SOp ρ` on the first argument, extra `Tp`-typed state threading
  through the tupled `rec_` state → a `rec_` node) with its `mrec` adequacy (parameterised by the
  measure `μ = ·.1`).  **The reflector emits no `simp`** — every
  proof it outputs is a compositional/structural term (`simp` is confined to the fixed library lemmas
  like `adeqBody`).  Value-arm soundness: the **same walk, re-run in proof mode**, walks the source
  at the concrete representation (`V := Tp.denote`) and, at every node, applies that node's congruence lemma (`Reflect.Sound`'s
  `sc_op`/`sc_bind`/`sc_call`/…) to the sub-terms' equations — a proof term mirroring the source.  A
  reflected get/set inserts **exactly the source's own in-bounds proof** (`sc_vget … h` = `dif_pos h`),
  so the erased `fail` branch is closed *at that node* — no decidability, no global rewrite, sound for
  a **symbolic** index at **any depth** (buried under effects, branches, or a helper call), including
  dynamically-sized `Array` reads.  A non-reifiable argument (an in-bounds proof `j < n`) is erased
  from the program inputs and instead quantifies the soundness statement.
- **Examples** — `Freigen/Examples/` — the `Circuit/` folder (`CircOp` + scoped `hint`,
  `runCirc`/`conCirc`): `Circuit.Basic` exercises the features one by one (hints, helpers, inputs,
  monomorphisation, collections, casts, pure and effectful loops) and `Circuit.Poseidon` is a real
  circuit — the Poseidon hash over BN254 `Fr` (reference constants, static round schedule),
  reflected with kept loops and folded definitions and pinned against the circomlib test vectors;
  `Storage` (hint-less `StoreOp`, operational `runStore`); and `Recursion`
  (`countdown`/`sm`, stateful `sumAcc`/`countAsserts`).  Every example proves its `≈`-soundness and
  pins its statement/result/AST with `#guard_msgs`.

## One line

Effects are first-order and opaque; scoped constructs carry an in-monad block and live in `hop`.
`reflect%` compiles a `Free` program into a typed imperative `Prog` — with reified arithmetic,
first-class functions (`def_`), and recursion (`rec_`) — and everything denotes into the same
interaction-tree domain `Comp`, sound by the uniform `≈`: `denoteProg (reflect% foo) ≈ ofFree foo`.
