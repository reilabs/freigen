import Freigen.CompM.Basic
import Freigen.Circuit.Context
import Freigen.Eff
import Freigen.Free.Basic

namespace Freigen.Circuit

inductive Scope : Type u where
| constraint
| hint

inductive ConstraintEff (F : Type) (ctx : Context F) where
| assertR1C (a b c : ctx.W)
| rangeCheck (n : Nat) (a : ctx.W)
| assertSpread (n : Nat) (a b : ctx.W)
| hint (n : Nat) (α : Type) (args : Vector ctx.W n)

inductive HintEff (F : Type) (ctx : Context F) : Type u where
| writeWitness (a : F)

def Eff (F : Type) (ctx : Context F) : Scope → Type _
| .constraint => ConstraintEff F ctx
| .hint => HintEff F ctx

instance {F : Type} [ctx : Context F] :
    Freigen.Eff.Spec (Γ := Scope) (Eff F ctx) where
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
  | .constraint, .hint n _ _ => fun _ => Vector F n
  | .hint, .writeWitness _ => nofun
  blockOutputs := fun
  | .constraint, .assertR1C _ _ _ => nofun
  | .constraint, .rangeCheck _ _ => nofun
  | .constraint, .assertSpread _ _ _ => nofun
  | .constraint, .hint _ α _ => fun _ => α
  | .hint, .writeWitness _ => nofun

end Circuit

def Circuit (F : Type) [ctx : Circuit.Context F] : Type → Type _ :=
  Free (Circuit.Eff F ctx) .constraint

instance {F : Type} [ctx : Circuit.Context F] : Monad (Circuit F) :=
  inferInstanceAs (Monad (Free (Circuit.Eff F ctx) .constraint))

instance {F : Type} [ctx : Circuit.Context F] : LawfulMonad (Circuit F) :=
  inferInstanceAs (LawfulMonad (Free (Circuit.Eff F ctx) .constraint))

namespace Circuit

variable {F : Type} [ctx : Context F]

def Hint (F : Type) [ctx : Context F] : Type → Type _ :=
  Free (Circuit.Eff F ctx) .hint

instance : Monad (Hint F) :=
  inferInstanceAs (Monad (Free (Circuit.Eff F ctx) .hint))

instance : LawfulMonad (Hint F) :=
  inferInstanceAs (LawfulMonad (Free (Circuit.Eff F ctx) .hint))

def assertR1C (a b c : ctx.W) :
    Circuit F (Cert (R1CSAssertion a b c)) :=
  Free.op (E := Circuit.Eff F ctx) (γ := .constraint)
    (.assertR1C a b c) nofun

def rangeCheck (n : Nat) (a : ctx.W) : Circuit F (WUInt F n) := do
  let cert ←
    Free.op (E := Circuit.Eff F ctx) (γ := .constraint)
      (.rangeCheck n a) nofun
  pure ⟨a, cert⟩

def assertSpread (n : Nat) (a b : ctx.W) :
    Circuit F (Cert (SpreadAssertion n a b)) :=
  Free.op (E := Circuit.Eff F ctx) (γ := .constraint)
    (.assertSpread n a b) nofun

def hint {α} (n : Nat) (args : Vector ctx.W n)
    (h : Vector F n → Hint F α) : Circuit F α :=
  Free.op (E := Circuit.Eff F ctx) (γ := .constraint) (.hint n α args)
    (fun _ inputs => h inputs)

def writeWitness (a : F) : Hint F ctx.W :=
  Free.op (E := Circuit.Eff F ctx) (γ := .hint) (.writeWitness a) nofun

end Freigen.Circuit
