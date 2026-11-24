import Freigen.CompM.Basic
import Freigen.Free.Basic

/-!
Correctness of a computation over `Fail ⊕ Tau ⊕ E` against a source program
over `F`, up to erasure: `Corr`, the counterpart of `Free.Sim` for
computations, with the computation's silent steps skipped. Operations are
paired by a spec (`Free.SimSpec`), and the computation is examined only where
the source can take it: at the erasures of the source's block inputs and
operation outputs. There it terminates and never fails, since `Corr` is
inductive and has no rule for `fail`; elsewhere (an output that erases no
source output, a certificate for a false assertion) it is unconstrained.

`Corr` is defined by one rule per node shape.
-/

namespace Freigen

open Eff (Fail Tau)

variable {Γ : Type c} {E : Γ → Type u} {Γ' : Type c'} {F : Γ' → Type u'}
  [sE : Eff.Spec.{_, u, 0} E] [sF : Eff.Spec.{_, u', 0} F]
  {γ : Γ} {γ' : Γ'} {α β : Type}

namespace CompM

variable (spec : Free.SimSpec E F)

/-- `x` is correct against the source program `s`: `Free.Sim` by `spec`, with
`x`'s silent steps skipped, and `x`'s result `f` of `s`'s. -/
inductive Corr :
    {γ : Γ} → {γ' : Γ'} → {α β : Type} → (β → α) →
    CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α → Free F γ' β → Prop
| pure {γ : Γ} {γ' : Γ'} {α β : Type} {f : β → α} (b : β) :
    Corr f (pure (f b) : CompM _ γ α) (pure b : Free F γ' β)
| tick {γ : Γ} {γ' : Γ'} {α β : Type} {f : β → α}
    {k : Unit → CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α} {s : Free F γ' β} :
    Corr f (k ()) s → Corr f (tick >>= k) s
| op {γ : Γ} {γ' : Γ'} {α β : Type} {f : β → α} (o : spec.Op γ γ')
    {blocks :
      (t : sE.blockTag γ (spec.src o)) →
      sE.blockInputs γ (spec.src o) t →
      CompM (Fail ⊕ₑ Tau ⊕ₑ E) (sE.blockCtx γ (spec.src o) t) (sE.blockOutputs γ (spec.src o) t)}
    {blocks' :
      (t : sF.blockTag γ' (spec.tgt o)) →
      sF.blockInputs γ' (spec.tgt o) t →
      Free F (sF.blockCtx γ' (spec.tgt o) t) (sF.blockOutputs γ' (spec.tgt o) t)}
    {k : sE.output γ (spec.src o) → CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α}
    {k' : sF.output γ' (spec.tgt o) → Free F γ' β} :
    (∀ t i', Corr (spec.out o t) (blocks (spec.tag o t) (spec.inp o t i')) (blocks' t i')) →
    (∀ o', Corr f (k (spec.res o o')) (k' o')) →
    Corr f (op (E := Fail ⊕ₑ Tau ⊕ₑ E) (.inr (.inr (spec.src o))) blocks >>= k)
      (Free.op (spec.tgt o) blocks' >>= k')

variable {spec}

theorem Corr.pure_of_eq {f : β → α} {a : α} {b : β} (h : a = f b) :
    Corr spec f (Pure.pure a : CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α) (Pure.pure b : Free F γ' β) :=
  h ▸ .pure b

end CompM

end Freigen
