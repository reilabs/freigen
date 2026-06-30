import Freigen.Examples.Circuit.Basic

/-!
# A denotation **domain** with success, effects, and failure

This module realises the semantics we converged on for an **erased** AST — dependent-type and
proof erased — where a partial operation (e.g. an out-of-bounds vector read) must *fail* rather
than return an `Inhabited` default.

`Comp Op` is the free monad over `Effect Op` extended with a **failure** outcome `fail`.  So a
computation has three observable shapes:

* `pure a`  — converges to a value,
* `vis e k` — performs effect `e`, continues with `k`,
* `fail`    — aborts (e.g. an OOB read on a non-`Inhabited` element type).

A vector read is denoted by the *partial* `getElem?` (no `Inhabited`!), sending an out-of-range
index to `fail`.  The **bridge** lemma `Comp.vget_pos` shows that when the source's (erased)
in-bounds proof exists, the read converges to exactly the source value and the `fail` branch is
dead — i.e. the dropped `Fin`/`Nat` proof's whole job is to discharge the failure case.

Source programs stay in the ordinary inductive `Free (Effect Op)` (as today); `Comp.ofFree`
embeds them, and soundness is stated as an equation in `Comp`.  Divergence/recursion (the `tau`
step, the ω-CPO structure, and `Comp.fix` with its adequacy theorem) is the coinductive extension
documented at the end — *not* implemented here, and deliberately not faked.

Everything in this file is fully proved (no `sorry`) and does not touch the live reflector.
-/

namespace Freigen

/-! ## The domain -/

/-- The free monad over `Effect Op` with an extra **failure** outcome.  (`pure`/`vis` mirror
    `Free.Pure`/`Free.Impure`; `fail` is the new partial-operation abort.) -/
inductive Comp (Op : Type → Type → Type 1) (α : Type) : Type 1
  | pure : α → Comp Op α
  | fail : Comp Op α
  | vis  : {x : Type} → Effect Op x → (x → Comp Op α) → Comp Op α

/-- Monadic bind: thread `pure`, propagate `fail`, thread the effect continuation. -/
def Comp.bind {Op α β} : Comp Op α → (α → Comp Op β) → Comp Op β
  | .pure a,  k => k a
  | .fail,    _ => .fail
  | .vis e c, k => .vis e (fun x => (c x).bind k)

instance {Op} : Monad (Comp Op) where
  pure := Comp.pure
  bind := Comp.bind

/-! ## Embedding the source free monad -/

/-- Embed an ordinary (total, failure-free) source computation into the domain. -/
def Comp.ofFree {Op α} : Free (Effect Op) α → Comp Op α
  | .Pure a     => .pure a
  | .Impure e c => .vis e (fun x => Comp.ofFree (c x))

/-- `ofFree` is a monad homomorphism: it commutes with bind.  (Lets soundness proofs push
    `ofFree` through the source's `do`-structure.) -/
theorem Comp.ofFree_bind {Op α β} (m : Free (Effect Op) α) (k : α → Free (Effect Op) β) :
    Comp.ofFree (freeBind m k) = (Comp.ofFree m).bind (fun a => Comp.ofFree (k a)) := by
  induction m with
  | Pure a => rfl
  | Impure e c ih => simp [freeBind, Comp.ofFree, Comp.bind, ih]

/-! ## The proof-erased vector read — failing, `Inhabited`-free -/

/-- Index a vector at a `Nat`, **failing** out of bounds.  Note: no `[Inhabited α]` — the partial
    `getElem?` is used, and an out-of-range index denotes to `fail`, not a default. -/
def Comp.vget {Op α n} (v : Vector α n) (i : Nat) : Comp Op α :=
  match v[i]? with
  | some x => .pure x
  | none   => .fail

/-- **The bridge.** Given the source's in-bounds proof `h`, the read converges to the source
    value `v[i]'h`; the `fail` branch is provably unreachable.  This is exactly where the erased
    `Fin`/`Nat` proof reappears — to discharge the failure case. -/
theorem Comp.vget_pos {Op α n} (v : Vector α n) (i : Nat) (h : i < n) :
    (Comp.vget v i : Comp Op α) = Comp.pure v[i] := by
  simp [Comp.vget, (Vector.getElem?_eq_some_getElem_iff h).mpr trivial]

/-- Out of bounds genuinely **fails** — no default, no `Inhabited`. -/
theorem Comp.vget_oob {Op α n} (v : Vector α n) (i : Nat) (h : n ≤ i) :
    (Comp.vget v i : Comp Op α) = Comp.fail := by
  simp [Comp.vget, getElem?_neg v i (by omega)]

/-! ## A worked end-to-end example

This is what the reflector *will* produce once it targets `Comp` and emits the failing `vget`
(reclassified from a pure `Bin` to an effect): a source program with proof-carrying reads, denoted
into the domain with `Inhabited`-free failing reads, proved equal via the bridge — no `rfl`-magic
default, no `Inhabited`. -/

section Example

variable (v : Vector Nat 3)

/-- A source program in the ordinary free monad: read two cells (proof-carrying) and add. -/
def srcDot (h0 : (0:Nat) < 3) (h1 : (1:Nat) < 3) : Free (Effect CircOp) Nat :=
  pure (v[0]'h0 + v[1]'h1)

/-- Its domain denotation, in the shape the reflector would emit: the reads are now *effects*
    (sequenced via `bind`) that may `fail`, with no `Inhabited` anywhere. -/
def denDot : Comp CircOp Nat :=
  (Comp.vget v 0).bind fun a => (Comp.vget v 1).bind fun b => Comp.pure (a + b)

/-- **Soundness**, as an equation in the domain: the denotation equals the embedded source.  The
    failing reads collapse to the source values via the bridge — the `fail` branches are dead
    precisely because the source carried the in-bounds proofs. -/
theorem denDot_sound (h0 : (0:Nat) < 3) (h1 : (1:Nat) < 3) :
    denDot v = Comp.ofFree (srcDot v h0 h1) := by
  simp only [denDot, Comp.vget_pos v 0 h0, Comp.vget_pos v 1 h1, Comp.bind]
  rfl

/-- And an out-of-bounds read in the same shape **fails** — captured, not hidden. -/
theorem denDot_oob_fails :
    ((Comp.vget v 5).bind fun a => Comp.pure (a + 1)) = (Comp.fail : Comp CircOp Nat) := by
  simp [Comp.vget_oob v 5 (by omega), Comp.bind]

#eval IO.println "Freigen.Domain: success/effect/fail domain — vget fails OOB without Inhabited, \
  bridge discharges the failure from the source proof, soundness as a domain equation."

end Example

/-! ## What remains (the coinductive layer) — honestly not done here

To capture **unbounded WF recursion** (beyond the bounded `forN`), `Comp` must gain a `tau` step
and become coinductive (an interaction tree), carry an `OmegaCompletePartialOrder` instance
(`⊥`, `ωSup`), and expose `Comp.fix` (the least fixed point) for recursive `Prog` definitions.
Soundness then weakens from the equation above to **convergence** `denote(AST) ⇓ ofFree (e args)`
(weak bisimulation, equality up to `tau`), discharged for recursive definitions by an adequacy
lemma about `Comp.fix`.  That is a substantial build (Lean coinduction via `PFunctor.M`, the CPO
instances, continuity, adequacy) and is intentionally left as the next stage rather than stubbed.

The failure/`Inhabited`-erasure story above is complete and proved; bounded programs (the entire
current example suite, incl. Poseidon) live in the `tau`-free fragment where this domain equation
*is* the soundness statement. -/

end Freigen
