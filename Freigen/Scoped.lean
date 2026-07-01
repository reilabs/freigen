/-!
# `FreeH`: a free monad with an *opaque* first-order signature and an *extensible* scoped signature

Two orthogonal extension slots:

* `Op : Type → Type → Type` — ordinary **first-order effects**; interpreters treat them *opaquely*
  (reify the input, recurse the continuation).  `assert`, `get`, `set`, …
* `SOp : Type → Type` — **scoped constructs**: `SOp β` is the set of scoped operations whose
  *in-monad block* computes a `β`.  `hint` is one such `SOp`; `NoScope` (`fun _ => PEmpty`) recovers
  the plain first-order free monad (e.g. the Storage DSL).

The `FreeH Op SOp` value is the **source of truth**: two Lean-side interpreters give it meaning —
`run` (witness generation: scoped blocks are *run*) and `con` (constrained semantics: scoped blocks
are *erased* to a fresh existential).  Both are generic over `Op` **and** `SOp`, parameterized only
by per-signature handlers.  Nothing is special-cased about `hint`: it's a scoped construct like any
other, and the block is a genuine computation *in the same monad* (positive recursion via `hop`, so
it is well-founded — unlike stuffing a computation into a first-order op's index).
-/

namespace Freigen.Scoped

/-- Free monad over a first-order signature `Op` and a scoped signature `SOp`.  `hop s b k`: scoped
    op `s : SOp β`, block `b : FreeH … β` (a full computation in the *same* monad, producing the
    witness), and continuation `k`.  The block is a *positive* recursive occurrence — a perfectly
    ordinary inductive. -/
inductive FreeH (Op : Type → Type → Type 1) (SOp : Type → Type) : Type → Type 1
  | pure {α} : α → FreeH Op SOp α
  | op   {α I R} : Op I R → I → (R → FreeH Op SOp α) → FreeH Op SOp α
  | hop  {α β} : SOp β → FreeH Op SOp β → (β → FreeH Op SOp α) → FreeH Op SOp α

namespace FreeH
variable {Op : Type → Type → Type 1} {SOp : Type → Type}

/-- Monadic bind: extends the *continuation* (never the scoped block — binding after a `hint`
    sequences what happens with the witness, not the out-of-circuit computation). -/
def bind {α γ} : FreeH Op SOp α → (α → FreeH Op SOp γ) → FreeH Op SOp γ
  | .pure a,    f => f a
  | .op o i k,  f => .op o i (fun r => bind (k r) f)
  | .hop s b k, f => .hop s b (fun x => bind (k x) f)

instance : Monad (FreeH Op SOp) where
  pure := .pure
  bind := bind

/-- Perform a first-order effect, binding its result. -/
def perform {I R} (o : Op I R) (i : I) : FreeH Op SOp R := .op o i .pure

/-- Right identity: `bind m pure = m`. -/
theorem bind_pure {α} (m : FreeH Op SOp α) : bind m .pure = m := by
  induction m with
  | pure a => rfl
  | op o i c ih => simp only [bind]; exact congrArg (FreeH.op o i) (funext ih)
  | hop s b c _ ihc => simp only [bind]; exact congrArg (FreeH.hop s b) (funext ihc)

/-- **Witness generation**: interpret into a monad `M`, *running* scoped blocks.  `ho` handles the
    first-order ops; `hs` handles each scoped op given its already-run block. -/
def run {M : Type → Type} [Monad M]
    (ho : {I R : Type} → Op I R → I → M R)
    (hs : {β : Type} → SOp β → M β → M β) :
    {α : Type} → FreeH Op SOp α → M α
  | _, .pure a    => Pure.pure a
  | _, .op o i k  => ho o i >>= fun r => run ho hs (k r)
  | _, .hop s b k => hs s (run ho hs b) >>= fun x => run ho hs (k x)

/-- **Constrained semantics**: a predicate transformer `(α → Prop) → Prop`.  Scoped blocks are
    *erased*; `hs` supplies each scoped op's meaning (for `hint`: a fresh existential witness). -/
def con
    (ho : {I R : Type} → Op I R → I → (R → Prop) → Prop)
    (hs : {β : Type} → SOp β → (β → Prop) → Prop) :
    {α : Type} → FreeH Op SOp α → (α → Prop) → Prop
  | _, .pure a     => fun c => c a
  | _, .op o i k   => fun c => ho o i (fun r => con ho hs (k r) c)
  | _, .hop s _b k => fun c => hs s (fun x => con ho hs (k x) c)   -- block erased

end FreeH

/-! ## Scoped signatures -/

/-- No scoped operations — the plain first-order free monad (e.g. Storage). -/
abbrev NoScope : Type → Type := fun _ => PEmpty

/-- The `hint` scoped signature: for every block type `β`, exactly one `hint` op. -/
abbrev HintS : Type → Type := fun _ => Unit

/-- `hint b`: compute a witness out-of-circuit by running `b` (witgen), or introduce a fresh
    existential witness and *erase* `b` (constrained).  `b` is a full computation in the same monad. -/
def hint {Op : Type → Type → Type 1} {β} (b : FreeH Op HintS β) : FreeH Op HintS β :=
  .hop () b .pure

/-! ## Handlers for the two scoped signatures -/

/-- Witgen: run the block and use its value. -/
def hintRun {M : Type → Type} [Monad M] : {β : Type} → HintS β → M β → M β := fun _ mb => mb
/-- Constrained: a fresh existential witness (block erased). -/
def hintCon : {β : Type} → HintS β → (β → Prop) → Prop := fun _ cont => ∃ x, cont x

/-- `NoScope` handlers are vacuous (there are no scoped ops to interpret). -/
def noScopeRun {M : Type → Type} : {β : Type} → NoScope β → M β → M β := fun s _ => s.elim
def noScopeCon : {β : Type} → NoScope β → (β → Prop) → Prop := fun s _ => s.elim

end Freigen.Scoped
