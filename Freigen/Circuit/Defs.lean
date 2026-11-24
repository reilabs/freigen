import Freigen.CompM.Basic
import Freigen.Circuit.Context
import Freigen.Eff
import Freigen.Free.Basic

namespace Freigen.Circuit

inductive Scope : Type u where
| constraint
| hint

inductive ConstraintEff (P : Nat) (ctx : Context P) where
| assertR1C (a b c : ctx.W)
| rangeCheck (n : Nat) (a : ctx.W)
| assertSpread (n : Nat) (a b : ctx.W)
| hint (n : Nat) (α : Type) (args : Vector ctx.W n)

inductive HintEff (P : Nat) (ctx : Context P) : Type u where
| writeWitness (a : ZMod P)

def Eff (P : Nat) (ctx : Context P) : Scope → Type _
| .constraint => ConstraintEff P ctx
| .hint => HintEff P ctx

instance {P : Nat} [ctx : Context P] :
    Freigen.Eff.Spec (Γ := Scope) (Eff P ctx) where
  output := fun
  | .constraint, .assertR1C a b c => Cert (R1CSAssertion a b c)
  | .constraint, .rangeCheck n a => Cert (RangeAssertion n a)
  | .constraint, .assertSpread n a b => Cert (SpreadAssertion n a b)
  | .constraint, .hint _ α _ => α
  | .hint, .writeWitness _ => ctx.W
  blockTag := fun
  | .constraint, .assertR1C _ _ _ => PEmpty
  | .constraint, .rangeCheck _ _ => PEmpty
  | .constraint, .assertSpread _ _ _ => PEmpty
  | .constraint, .hint _ _ _ => PUnit
  | .hint, .writeWitness _ => PEmpty
  blockCtx := fun
  | .constraint, .assertR1C _ _ _ => nofun
  | .constraint, .rangeCheck _ _ => nofun
  | .constraint, .assertSpread _ _ _ => nofun
  | .constraint, .hint _ _ _ => fun _ => .hint
  | .hint, .writeWitness _ => nofun
  blockInputs := fun
  | .constraint, .assertR1C _ _ _ => nofun
  | .constraint, .rangeCheck _ _ => nofun
  | .constraint, .assertSpread _ _ _ => nofun
  | .constraint, .hint n _ _ => fun _ => Vector (ZMod P) n
  | .hint, .writeWitness _ => nofun
  blockOutputs := fun
  | .constraint, .assertR1C _ _ _ => nofun
  | .constraint, .rangeCheck _ _ => nofun
  | .constraint, .assertSpread _ _ _ => nofun
  | .constraint, .hint _ α _ => fun _ => α
  | .hint, .writeWitness _ => nofun

end Circuit

def Circuit (P : Nat) [ctx : Circuit.Context P] : Type → Type _ :=
  Free (Circuit.Eff P ctx) .constraint

instance {P : Nat} [ctx : Circuit.Context P] : Monad (Circuit P) :=
  inferInstanceAs (Monad (Free (Circuit.Eff P ctx) .constraint))

instance {P : Nat} [ctx : Circuit.Context P] : LawfulMonad (Circuit P) :=
  inferInstanceAs (LawfulMonad (Free (Circuit.Eff P ctx) .constraint))

namespace Circuit

variable {P : Nat} [ctx : Context P]

def Hint (P : Nat) [ctx : Context P] : Type → Type _ :=
  Free (Circuit.Eff P ctx) .hint

instance : Monad (Hint P) :=
  inferInstanceAs (Monad (Free (Circuit.Eff P ctx) .hint))

instance : LawfulMonad (Hint P) :=
  inferInstanceAs (LawfulMonad (Free (Circuit.Eff P ctx) .hint))

def assertR1C (a b c : ctx.W) :
    Circuit P (Cert (R1CSAssertion a b c)) :=
  Free.op (E := Circuit.Eff P ctx) (γ := .constraint)
    (.assertR1C a b c) nofun

def rangeCheck (n : Nat) (a : ctx.W) : Circuit P (WUInt P n) := do
  let cert ←
    Free.op (E := Circuit.Eff P ctx) (γ := .constraint)
      (.rangeCheck n a) nofun
  pure ⟨a, cert⟩

def assertSpread (n : Nat) (a b : ctx.W) :
    Circuit P (Cert (SpreadAssertion n a b)) :=
  Free.op (E := Circuit.Eff P ctx) (γ := .constraint)
    (.assertSpread n a b) nofun

def hint {α} (n : Nat) (args : Vector ctx.W n)
    (h : Vector (ZMod P) n → Hint P α) : Circuit P α :=
  Free.op (E := Circuit.Eff P ctx) (γ := .constraint) (.hint n α args)
    (fun _ inputs => h inputs)

def writeWitness (a : ZMod P) : Hint P ctx.W :=
  Free.op (E := Circuit.Eff P ctx) (γ := .hint) (.writeWitness a) nofun

omit ctx in
/-- A square root in the field: some `r` with `r * r = x` if there is one, and
`0` otherwise. A specification, not an algorithm: once the AST has loops it is
to be computed by exponentiation. -/
noncomputable def fsqrt (x : ZMod P) : ZMod P :=
  open Classical in
  if h : ∃ r : ZMod P, r * r = x then Classical.choose h else 0

-- def runWithHints (c : Circuit P α) : Option α :=

end Freigen.Circuit
