# Freigen

*frei* (free) + *eigen* (self) — reflecting effectful Lean programs into a free-monadic AST
and denoting them back, with the round-trip proven faithful by `rfl`.

- `Freigen/Free.lean` — the free monad and the freer-monad `Effect` functor
- `Freigen/Ast.lean` — the object-type universe `Tp`, the A-normal `Exp`/`Prog` AST, its denotation, and a pretty-printer
- `Freigen/Reflect.lean` — the `reflect%` elaborator (reify a `Free (Effect Op)` computation into a `Prog`)
- `Freigen/Domain.lean` — a finite denotation domain with **failure** (`pure`/`vis`/`fail`): the `Inhabited`-free, OOB-fails vector read and the bridge that discharges failure from the source's in-bounds proof
- `Freigen/ITree.lean` — **interaction trees** (`Comp Op`), the coinductive denotation domain (`ret`/`tau`/`vis`/`fail`) built on `PFunctor.M`: `bind` + monad + all computation laws, `spin` (divergence), `iter` — the guarded-recursion fixpoint combinator — with its **fixpoint unfolding law proved by coinduction**, and **`iter_converges`**, the general adequacy theorem (the `iter` denotation converges to the operational iteration for *any* step), plus `ofFree`, a convergence relation, and `down`/`spin` (terminating-recursion vs divergence)
- `Freigen/DenoteITree.lean` — the AST denotation **retargeted to the interaction-tree domain** (`denoteI`/`denoteProgI`, the bounded loop `forC`)
- `Freigen/Examples/ITreeSound.lean` — a reflected program's ITree denotation equals the embedded source: the native interpreter (`denoteProgI`) concretely, and `ofFree ∘ denoteProg` for *every* reflected program
- `Freigen/Examples/Recursion.lean` — **recursion through the elaborator**: `reflect%` now reflects sum types (`Sum.inl`/`Sum.inr` → `Un.inl`/`Un.inr`) and boolean branches (`bif` → `Exp.ite`), so a loop *step* `σ → Free (Effect Op) (σ ⊕ ρ)` reflects; `ITree.iter` ties the unbounded knot, and the reflected countdown loop is **proved to converge** (`countdown_converges`)
- `Freigen/Examples/` — concrete operation signatures and example programs (one module per signature):
  - `Circuit/` — the `CircOp` signature (`hint`/`assert`):
    - `Circuit/Basic.lean` — the signature, smart constructors, and its computable semantics `runCirc` (`foldFree` into `Option`: `hint` = eval, `assert` = potential failure)
    - `Circuit/Examples.lean` — reflect/pretty-print smoke tests, `runCirc` runs, and the `Vector` object type
    - `Circuit/Poseidon.lean` — the Poseidon sponge hash over the BN254 scalar field for 4 inputs, over `Vector Fr t`
  - `Storage.lean` — the `StoreOp` signature (`set`/`get`): a store of naturals addressed by naturals, with an operational denotation (`runStore`)
