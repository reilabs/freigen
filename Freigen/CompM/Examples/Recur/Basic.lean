import Freigen.CompM.Basic
import Freigen.ITree.Basic
import Freigen.Eff

namespace Freigen.CompM.Examples

structure RecurC (inp : Type) (out : Type) where
  args : inp

def Recur {Γ} (i o : Type) (_γ : Γ) := RecurC i o

instance {Γ} {inp out : Type} : Eff.Spec (@Recur Γ inp out) where
  output := fun _ _ => out
  blockTag := fun _ _ => PEmpty
  blockCtx := nofun
  blockInputs := nofun
  blockOutputs := nofun

namespace Recur

def runCounted {Γ : Type} {γ : Γ} {α : Type} :
    (fuel : Nat) → CompM Eff.Tau γ α → Option (α × Nat) :=
  fun fuel x => go fuel (x.result.approx (fuel + 1))
  where
  go : (fuel : Nat) →
      IxPoly.M.Approx (Eff.Step Γ Eff.Tau) (fuel + 1) (γ, α) →
      Option (α × Nat)
  | 0, ._succ _ _ p _ =>
      match p with
      | .ret value => some (value, 0)
      | .op _ => none
  | fuel + 1, ._succ _ _ p children =>
      match p with
      | .ret value => some (value, 0)
      | .op _ =>
          (go fuel (children (.inl PUnit.unit))).map
            fun (value, steps) => (value, steps + 1)

def fix {Γ : Type} {E : Γ → Type} [Eff.Spec E] [Eff.Has Eff.Tau E]
    {inp out : Type}
    (f : (∀ {γ}, inp → CompM (Recur inp out ⊕ₑ E) γ out) →
      ∀ {γ}, inp → CompM (Recur inp out ⊕ₑ E) γ out) :
    ∀ {γ}, inp → CompM E γ out :=
  let recur : ∀ {γ}, inp → CompM (Recur inp out ⊕ₑ E) γ out :=
    fun i => CompM.liftL <| CompM.op (E := Recur inp out) ⟨i⟩ nofun
  let body : ∀ {γ}, inp → CompM (Recur inp out ⊕ₑ E) γ out := f recur
  fun i => CompM.interpL (body i) fun step =>
    Eff.Step.casesOn step
      (motive := fun i _ =>
        Eff.Step _ E
          (fun i => CompM (Recur inp out ⊕ₑ E) i.1 i.2) i)
      (fun value => Eff.Step.ret value)
      (fun {γ} {_} ⟨args⟩ _ k =>
        Eff.Step.tau (body (γ := γ) args >>= k))

def isEvenTail : Nat → CompM Eff.Tau () Bool := fix fun isEven => fun
| 0 => pure true
| 1 => pure false
| n + 2 => isEven n

#eval runCounted 10 (isEvenTail 4)

def isEvenStack : Nat → CompM Eff.Tau () Bool := fix fun isEven => fun
| 0 => pure true
| n + 1 => do pure !(←isEven n)

#eval runCounted 6 (isEvenStack 6)

def add : Nat → Nat → CompM Eff.Tau () Nat := fun n => fix fun add => fun
| 0 => pure n
| m + 1 => do pure $ (←add m) + 1

def mul : Nat → Nat → CompM Eff.Tau () Nat := fun n => fix fun mul => fun
| 0 => pure 0
| m + 1 => do CompM.liftR $ add n (←mul m)

#eval runCounted 5 (mul 10 2)

end Freigen.CompM.Examples.Recur
