import Freigen.CompM.Implements

/-!
The full erasure pipeline for a two-step program, proved from the
compositional laws only.

The second step fails on even inputs, but the first step only ever returns
odd numbers, so the composition never fails.
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

/-- The identity handler. -/
def handler : Eff.Handler Op (Free Op) := fun e blocks => Free.op e blocks

def read : CompM Stack () Nat := CompM.op (E := Stack) (.inr (.inr .read)) nofun

def readFree : Free Op () Nat := Free.op Op.read nofun

/-- Read `n` and return `2n + 1`. -/
def step₁ : CompM Stack () Nat := do
  let n ← read
  pure (2 * n + 1)

/-- Halve odd numbers after a silent step, and fail on even ones. -/
def step₂ (m : Nat) : CompM Stack () Nat :=
  if m % 2 = 1 then CompM.tick >>= fun _ => pure (m / 2) else CompM.fail

theorem step₁_implements :
    Implements handler step₁ (readFree >>= fun n => pure (2 * n + 1)) :=
  .op Op.read nofun fun n => .pure (2 * n + 1)

theorem step₂_implements (m : Nat) (h : step₁.MayReturn m) :
    Implements handler (step₂ m) (pure (m / 2)) := by
  simp only [step₁, read, mayReturn_op_bind_iff, mayReturn_pure_iff] at h
  rcases h with ⟨n, rfl⟩
  rw [step₂, if_pos (by omega)]
  exact .tick (.pure _)

theorem program_implements :
    Implements handler (step₁ >>= step₂) readFree := by
  have h := step₁_implements.bind step₂_implements
  have hs : (readFree >>= fun n => pure (2 * n + 1)) >>= (fun m => pure (m / 2)) =
      readFree := by
    rw [bind_assoc, ← bind_pure readFree]
    congr 1
    funext n
    simp only [pure_bind]
    congr 1
    omega
  rwa [hs] at h

/-- The pipeline, as stated in the AST certificates. -/
example : ∃ wf nofail, erase handler (step₁ >>= step₂) wf nofail = readFree :=
  implements_iff.mp program_implements

end Freigen.CompM.Examples.Implements
