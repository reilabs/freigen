import Freigen.F2Z.Defs
import Freigen.Wheels

namespace Freigen.F2Z.Semantics

structure R1C F [Semiring F] where
  a : LC F
  b : LC F
  c : LC F
deriving Repr

def R1C.satisfies [Semiring F] [DecidableEq F]
    (r1c : R1C F) (witness : Nat → F): Prop :=
  r1c.a.eval witness * r1c.b.eval witness = r1c.c.eval witness

def R1C.satisfies' [Semiring F] [DecidableEq F]
    (r1c : R1C F) (witness : Nat → F): Bool :=
  r1c.a.eval witness * r1c.b.eval witness = r1c.c.eval witness

structure CS where
  r1cs : Array (R1C ℤ)
  m : Array (LC Bool)
deriving Inhabited, Repr

def CS.satisfies' (cs : CS) (witness : Nat → Bool): Bool :=
  let mw := cs.m.map (Bool.toInt ∘ LC.eval witness)
  let mw := fun i => mw[i]!
  cs.r1cs.all (fun r1c => r1c.satisfies' mw)

def CS.satisfies (cs : CS) (witness : Nat → Bool): Prop :=
  let mw := cs.m.map (Bool.toInt ∘ LC.eval witness)
  let mw := fun i => mw[i]!
  ∀ r1c ∈ cs.r1cs, r1c.satisfies mw

def CS.intWitness (cs : CS) (witness : Nat → Bool) : Nat → ℤ :=
  let mw := cs.m.map (Bool.toInt ∘ LC.eval witness)
  fun i => mw[i]!

structure CSBuilder where
  result : CS
  nextWit : Nat
deriving Inhabited

namespace CSBuilder

local instance : Context := lcContext

def fresh : StateM CSBuilder (LC Bool) := do
  modifyGet (fun s => ({ s.nextWit }, { s with nextWit := s.nextWit + 1 }))

def NoMonad : Type → Type u := fun _ => PUnit

instance : Monad NoMonad where
  pure _ := PUnit.unit
  bind _ _ := PUnit.unit

instance : LawfulMonad NoMonad := LawfulMonad.mk' _
  (by intros; rfl)
  (by intros; rfl)
  (by intros; rfl)

abbrev RunnerM : Eff.Scope → Type → Type
| .constraint => StateM CSBuilder
| .hint => NoMonad

instance : (γ : Eff.Scope) → Monad (RunnerM γ)
| .constraint => inferInstance
| .hint       => inferInstance

instance : (γ : Eff.Scope) → LawfulMonad (RunnerM γ)
| .constraint => inferInstance
| .hint       => inferInstance

def handler : Freigen.Eff.Handler (Eff lcContext) RunnerM :=
  @fun
    | .constraint, .assertR1C a b c, _ => do
        let cs ← get
        let r1c : R1C ℤ := { a := a, b := b, c := c }
        set { cs with result := { cs.result with r1cs := cs.result.r1cs.push r1c } }
    | .constraint, .f2z a, _ => do
        let cs ← get
        let nextIdx := cs.result.m.size
        let lc : LC ℤ := { nextIdx }
        set { cs with result := { cs.result with m := cs.result.m.push a } }
        pure lc
    | .constraint, .hint _ _ n, _ => do
        let s ← get
        let out : Vector (LC Bool) n :=
          Vector.ofFn fun i => {s.nextWit + i.val}
        set { s with nextWit := s.nextWit + n }
        pure out
    | .hint, .fail _ _, _ => ()

def runAt {γ : Eff.Scope} {α} (circ : Free (Eff lcContext) γ α) : RunnerM γ α :=
  Free.interp handler circ

def run' {α} (circ : Circuit α): StateM CSBuilder α :=
  runAt circ

def run {α} (circ : Circuit α) (initial : CSBuilder): (α × CS) :=
  let (a, csb) := StateT.run (run' circ) initial
  (a, csb.result)

def runWithInputs {α n} (circ : Vector (LC Bool) n → Circuit α): (α × CS) :=
  let initial : CSBuilder := { result := { r1cs := #[], m := #[] }, nextWit := n }
  run (circ (Vector.ofFn fun i => {i.val})) initial

def Extends (s₁ s₂ : CSBuilder) : Prop :=
  s₁.result.r1cs.toList <+: s₂.result.r1cs.toList ∧
    s₁.result.m.toList <+: s₂.result.m.toList

theorem Extends.refl (s : CSBuilder) : Extends s s := by
  simp [Extends]

theorem Extends.trans {s₁ s₂ s₃ : CSBuilder}
    (h₁₂ : Extends s₁ s₂) (h₂₃ : Extends s₂ s₃) : Extends s₁ s₃ := by
  exact ⟨h₁₂.1.trans h₂₃.1, h₁₂.2.trans h₂₃.2⟩

theorem run'_extends {a : Circuit α} {s : CSBuilder} :
    Extends s (StateT.run (run' a) s).2 := by
  let motive := fun (γ : Eff.Scope) (α : Type)
      (a : Free (Eff lcContext) γ α) =>
    match γ with
    | .constraint => ∀ s, Extends s (StateT.run (runAt a) s).2
    | .hint => True
  apply Free.recOn (motive := motive) a (s := s)
  · intro γ α value
    cases γ with
    | constraint => exact fun s => Extends.refl s
    | hint => trivial
  · intro γ α e blocks k _ ihk
    cases γ with
    | hint => trivial
    | constraint =>
      intro s
      cases e with
      | assertR1C a b c =>
          simp [runAt, handler]
          apply Extends.trans (s₂ := {
            s with result := {
              s.result with r1cs := s.result.r1cs.push { a := a, b := b, c := c }
            }
          })
          · constructor
            · exact ⟨[{ a := a, b := b, c := c }], by simp⟩
            · simp
          · exact ihk () _
      | f2z a =>
          simp [runAt, handler]
          apply Extends.trans (s₂ := {
            s with result := { s.result with m := s.result.m.push a }
          })
          · constructor
            · simp
            · exact ⟨[a], by simp⟩
          · exact ihk ({s.result.m.size} : LC ℤ) _
      | hint argTps args n =>
          simp [runAt, handler]
          apply Extends.trans (s₂ := { s with nextWit := s.nextWit + n })
          · simp [Extends]
          · exact ihk (Vector.ofFn fun i =>
              ({s.nextWit + i.val} : LC Bool)) _

end CSBuilder

namespace Witgen

local instance : Context := valueContext

structure State where
  bools : Array Bool := #[]
deriving Inhabited

def State.boolWitness (s : State) : Nat → Bool :=
  fun i => s.bools[i]!

def zeroWitness : Nat → ℤ := fun _ => 0

def evalArgs (s : State) : {argTps : List Eff.WitnessSide} →
    HList (Eff.WitnessSide.denoteW valueContext) argTps →
    HList Eff.WitnessSide.denoteF argTps
  | [], .nil => .nil
  | Eff.WitnessSide.z :: _, .cons x xs => by
      simp only [Eff.WitnessSide.denoteW] at x
      exact .cons x (evalArgs s xs)
  | Eff.WitnessSide.f₂ :: _, .cons x xs => by
      simp only [Eff.WitnessSide.denoteW] at x
      exact .cons x (evalArgs s xs)

abbrev RunnerM : Eff.Scope → Type → Type
| .constraint => StateT State Option
| .hint => Option

instance : (γ : Eff.Scope) → Monad (RunnerM γ)
| .constraint => inferInstance
| .hint       => inferInstance

instance : (γ : Eff.Scope) → LawfulMonad (RunnerM γ)
| .constraint => inferInstance
| .hint       => inferInstance

def handler : Freigen.Eff.Handler (Eff valueContext) RunnerM :=
  @fun
    | .constraint, .assertR1C a b c, _ => by
      change ℤ at a b c
      exact do
        if a * b = c then pure () else failure
    | .constraint, .f2z a, _ => by
      change Bool at a
      exact pure a.toInt
    | .constraint, .hint _ args _, blkO => do
      let s ← get
      let r ← StateT.lift (blkO PUnit.unit (evalArgs s args))
      set { s with bools := s.bools ++ r.toArray }
      pure r
    | .hint, .fail _ _, _ => none

def runAt { γ : Eff.Scope } (circ : Free (Eff valueContext) γ α) : RunnerM γ α :=
  Free.interp handler circ

def run' (circ : Circuit α) : StateT State Option α :=
  runAt circ

def run (circ : Circuit α) (initial : State) : Option (Array Bool) := do
  let (_, s) ← StateT.run (run' circ) initial
  pure s.bools

def runWithInputs {α n} (circ : Vector Bool n → Circuit α)
    (inputs : Vector Bool n) : Option (Array Bool) := do
  let initial : State := { bools := inputs.toArray }
  run (circ inputs) initial

end Witgen

structure Stats where
  mRows : Nat
  mCols : Nat
  r1csRows : Nat
deriving Repr

def CS.stats (cs : CS) : Stats :=
  { mRows := cs.m.size + 1,
    mCols := cs.m.foldl
      (fun maxKey row => max maxKey row.normalForm.coeffs.maxKey!) 0 + 2,
    r1csRows := cs.r1cs.size }

end Freigen.F2Z.Semantics
