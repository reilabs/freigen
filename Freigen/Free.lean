/-!
# `Free`: a free monad with an opaque first-order signature and an extensible scoped signature

Two orthogonal extension slots:

* `Op : Type → Type → Type 1` — ordinary **first-order effects**: `Op I R` takes an input `I` and
  returns an `R`.  Interpreters treat them opaquely (via a handler).
* `SOp : Type → Type` — **scoped constructs**: `SOp β` is the set of scoped operations whose *in-monad
  block* computes a `β`.  The block is a *positive* recursive occurrence — an ordinary inductive.

A `Free Op SOp` value is the **source of truth**.  Its only generic interpreter is `run`: fold the
program into any monad `M`, given a handler for the first-order ops and a handler for the scoped ops.
*How* a particular scoped construct is interpreted (run its block, erase it, …) is entirely the
handler's business — the examples supply their own.
-/

namespace Freigen

/-- Free monad over a first-order signature `Op` and a scoped signature `SOp`.  `hop s b k`: scoped
    op `s : SOp β`, block `b : Free … β` (a full computation in the *same* monad, producing the
    witness), and continuation `k`.  The block is a *positive* recursive occurrence. -/
inductive Free (Op : Type → Type → Type 1) (SOp : Type → Type) : Type → Type 1
  | pure {α} : α → Free Op SOp α
  | op   {α I R} : Op I R → I → (R → Free Op SOp α) → Free Op SOp α
  | hop  {α β} : SOp β → Free Op SOp β → (β → Free Op SOp α) → Free Op SOp α

namespace Free
variable {Op : Type → Type → Type 1} {SOp : Type → Type}

/-- Monadic bind: extends the *continuation* (never the scoped block — binding after a scoped op
    sequences what happens with its result, not the in-block computation). -/
def bind {α γ} : Free Op SOp α → (α → Free Op SOp γ) → Free Op SOp γ
  | .pure a,    f => f a
  | .op o i k,  f => .op o i (fun r => bind (k r) f)
  | .hop s b k, f => .hop s b (fun x => bind (k x) f)

instance : Monad (Free Op SOp) where
  pure := .pure
  bind := bind

/-- Perform a first-order effect, binding its result. -/
def perform {I R} (o : Op I R) (i : I) : Free Op SOp R := .op o i .pure

/-- Right identity: `bind m pure = m`. -/
theorem bind_pure {α} (m : Free Op SOp α) : bind m .pure = m := by
  induction m with
  | pure a => rfl
  | op o i c ih => simp only [bind]; exact congrArg (Free.op o i) (funext ih)
  | hop s b c _ ihc => simp only [bind]; exact congrArg (Free.hop s b) (funext ihc)

/-- **The generic interpreter.** Fold a program into a monad `M`, given a handler `ho` for the
    first-order ops and a handler `hs` for the scoped ops.  `hs` receives the scoped op *and its
    interpreted block* `M β`, and returns an `M β` — so it may run the block, ignore it, and so on;
    all of that logic lives in the handler, not here. -/
def run {M : Type → Type} [Monad M]
    (ho : {I R : Type} → Op I R → I → M R)
    (hs : {β : Type} → SOp β → M β → M β) :
    {α : Type} → Free Op SOp α → M α
  | _, .pure a    => Pure.pure a
  | _, .op o i k  => ho o i >>= fun r => run ho hs (k r)
  | _, .hop s b k => hs s (run ho hs b) >>= fun x => run ho hs (k x)

end Free

/-- The trivial scoped signature: *no* scoped operations — the plain first-order free monad. -/
abbrev NoScope : Type → Type := fun _ => PEmpty

end Freigen
