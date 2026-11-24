import Freigen.CompM.Implements

/-!
Correctness of a two-step program against its source, proved from the rules
of `Corr`.

The second step fails on even inputs, but the first step's source only ever
returns odd numbers, so the composition never fails.
-/

namespace Freigen.CompM.Examples.Implements

inductive Op : Unit → Type
| read : Op ()

instance : Eff.Spec Op where
  output := fun _ _ => Nat
  blockTag := fun _ _ => PEmpty
  blockCtx := nofun
  blockInputs := nofun
  blockOutputs := nofun

abbrev Stack := Eff.Fail ⊕ₑ Eff.Tau ⊕ₑ Op

def read : CompM Stack () Nat := CompM.op (E := Stack) (.inr (.inr .read)) nofun

def readFree : Free Op () Nat := Free.op Op.read nofun

/-- Read `n` and return `2n + 1`. -/
def step₁ : CompM Stack () Nat := do
  let n ← read
  pure (2 * n + 1)

/-- Halve odd numbers after a silent step, and fail on even ones. -/
def step₂ (m : Nat) : CompM Stack () Nat :=
  if m % 2 = 1 then CompM.tick >>= fun _ => pure (m / 2) else CompM.fail

theorem step₁_corr :
    Corr .id id step₁ (readFree >>= fun n => pure (2 * n + 1)) :=
  .op (spec := .id) (.mk Op.read) nofun fun _ => .pure _

theorem program_corr :
    Corr .id id (step₁ >>= step₂) readFree := by
  have hs : readFree = Free.op Op.read nofun >>= fun n => pure ((2 * n + 1) / 2) := by
    rw [readFree, ← bind_pure (Free.op Op.read nofun)]
    congr 1
    funext (n : Nat)
    show (pure n : Free Op () Nat) = pure ((2 * n + 1) / 2)
    rw [show (2 * n + 1) / 2 = n by omega]
  rw [hs, step₁, read, bind_assoc]
  refine .op (spec := .id) (.mk Op.read) nofun fun n => ?_
  simp only [pure_bind]
  rw [step₂, if_pos (by omega)]
  exact .tick (.pure _)

end Freigen.CompM.Examples.Implements
