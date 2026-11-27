import Freigen.CompM.Basic
import Freigen.CompM.Examples.Nondet.Defs
import Freigen.CompM.Examples.Nondet.SamePrints
import Freigen.ITree.Basic

namespace Freigen.CompM.Examples.Nondet

/-!
Basic examples: two diverging computations, one deterministic one not + sample
evaluations and determinisim proofs.
-/

def scaryLoop : Nondet Unit := do
  while true do
    let x ← Nondet.rand
    Nondet.print (x*x)

def scaryLoopDet : Nondet Unit := do
  while true do
    let x ← Nondet.rand
    Nondet.print (x - x)

#eval approxWith Int.ofNat scaryLoop 100
example : approxWith Int.ofNat scaryLoop 20 = [0, 1, 4, 9, 16, 25, 36] := by rfl
example : approxWith Int.ofNat scaryLoopDet 20 = [0, 0, 0, 0, 0, 0, 0] := by rfl


def Deterministic {α} (t : Nondet α) : Prop := SamePrints Eq t t

open SamePrints in
example : Deterministic scaryLoopDet := by
  apply SamePrints.bind
  · apply SamePrints.loop_coind (I := Eq) (RR := Eq) rfl
    rintro ⟨⟩ _ rfl
    apply Step.loop
    simp only [↓reduceIte, Int.sub_self, bind_pure_comp, bind_assoc, bind_map_left]
    apply Step.rand_rand
    intros
    apply Steps.print
    apply Steps.tick_tick
    apply Steps.recur
    simp [LoopPair]
  · simp [SamePrints.ret]

example : ¬Deterministic scaryLoop := by
  unfold scaryLoop
  simp only [forIn]
  rw [loop_def]
  simp only [↓reduceIte, bind_pure_comp, bind_assoc, bind_map_left, map_bind, id_map']
  apply SamePrints.not_rand 0 1
  apply SamePrints.not_print
  omega

/-!
More involved (weak) bisimulation: desynchronized infinite loops shown to
produce the same traces.
-/

def printAllInts : Nondet Unit := do
  let mut curr := 0
  while true do
    Nondet.print curr
    curr := curr + 1

def printAllIntsBy2 : Nondet Unit := do
  let mut curr := 0
  while true do
    Nondet.print curr
    Nondet.print (curr + 1)
    curr := curr + 2

#eval approxWith Int.ofNat printAllInts 20
#eval approxWith Int.ofNat printAllIntsBy2 20

open SamePrints in
example : SamePrints Eq printAllInts printAllIntsBy2 := by
  apply SamePrints.bind
  · apply SamePrints.loop_coind Eq (RR := Eq) (by simp)
    rintro s _ rfl
    apply Step.loop
    simp only [↓reduceIte, bind_pure_comp, map_pure, bind_map_left, bind_assoc]
    apply Step.print
    apply Steps.tick_left
    apply Step.loop_left
    simp only [bind_map_left]
    apply Step.print
    apply Steps.tick_tick
    apply Steps.recur
    grind [LoopPair]
  · simp [SamePrints.ret]

/-!
A bytecode interpreter for a simple register machine – just write the interpreter like we
would in Rust, then talk about what it does.
-/

abbrev Register := Fin 10

inductive Op : Type
| const (n : Int) (r : Register) -- r <- n
| rand (r : Register) -- r <- rand
| sub (r1 r2 r3 : Register) -- r3 <- r1 - r2
| print (r : Register) -- print r
| goto (r : Register) -- goto (pc + r)
| done

abbrev Program := Array Op

structure State where
  regs : Register → Int
  pc : Nat

def State.init : State where
  regs := fun _ => 0
  pc := 0

def State.getReg (s : State) (r : Register) : Int := s.regs r
def State.setReg (s : State) (r : Register) (v : Int) : State :=
  { s with regs := fun r' => if r' = r then v else s.regs r' }
def State.addPC (s : State) (n : Int) : State := { s with pc := (Int.ofNat s.pc + n).toNat }

def Op.denote (op : Op) (s : State) : Nondet $ Option State := do
  match op with
  | .const n r => pure $ (s.setReg r n).addPC 1
  | .rand r => (some ∘ State.setReg (s.addPC 1) r) <$> Nondet.rand
  | .sub r1 r2 r3 => pure $ (s.setReg r3 (s.getReg r1 - s.getReg r2)).addPC 1
  | .print r => (Nondet.print $ s.getReg r) *> pure (some $ s.addPC 1)
  | .goto r => pure $ some (s.addPC (s.getReg r))
  | .done => pure none

def Program.denote (p : Program) : Nondet Unit := do
  let mut state := some State.init
  while let some s := state do
    let op := p.getD s.pc Op.done
    state ← op.denote s

def exampleProgram : Program := #[
  .rand 0,
  .sub 0 0 0,
  .print 0,
  .const (-5) 0,
  .goto 0
]

#eval approxWith Int.ofNat exampleProgram.denote 200

open SamePrints in
example : Deterministic exampleProgram.denote := by
  apply SamePrints.bind (RR := Eq)
  simp [forIn]
  apply SamePrints.loop_coind (I := fun s₁ s₂ =>
    (∃reg₁, s₁ = some ⟨reg₁, 0⟩) ∧
    (∃reg₂, s₂ = some ⟨reg₂, 0⟩)
  ) (RR := Eq)
  · simp [State.init]
  · rintro s₁ s₂ ⟨⟨r₁, rfl⟩, ⟨r₂, rfl⟩⟩
    simp [exampleProgram, Op.denote]
    repeat (first
      | apply Steps.recur; grind only [LoopPair]
      | apply Steps.tick_tick
      | apply Steps.print
      | apply Step.rand_rand; intros
      | apply Steps.loop
      | apply Step.loop
      | simp [State.getReg, State.setReg, State.addPC, seqRight_eq_bind, State.addPC]
    )
  · simp [SamePrints.ret]

end Freigen.CompM.Examples.Nondet
