import Freigen.CompM.Basic
import Freigen.Circuit.Context
import Freigen.Eff
import Freigen.Free.Basic

namespace Freigen.Circuit

inductive Scope : Type where
| constraint
| hint
deriving DecidableEq

inductive ConstraintEff (P : Nat) (ctx : Context P) where
| assertR1C (a b c : ctx.W)
| rangeCheck (n : Nat) (a : ctx.W)
| assertSpread (n : Nat) (a b : ctx.W)
/-- A hint over `n` wires, producing `m` witnesses. -/
| hint (n m : Nat) (args : Vector ctx.W n)

/-- Hint blocks have no effects (yet): their only output is their result. -/
inductive HintEff (P : Nat) (ctx : Context P) : Type u

def Eff (P : Nat) (ctx : Context P) : Scope → Type _
| .constraint => ConstraintEff P ctx
| .hint => HintEff P ctx

instance {P : Nat} [ctx : Context P] :
    Freigen.Eff.Spec (Γ := Scope) (Eff P ctx) where
  output := fun
  | .constraint, .assertR1C a b c => Cert (R1CSAssertion a b c)
  | .constraint, .rangeCheck n a => Cert (RangeAssertion n a)
  | .constraint, .assertSpread n a b => Cert (SpreadAssertion n a b)
  | .constraint, .hint _ m _ => Vector ctx.W m
  blockTag := fun
  | .constraint, .assertR1C _ _ _ => PEmpty
  | .constraint, .rangeCheck _ _ => PEmpty
  | .constraint, .assertSpread _ _ _ => PEmpty
  | .constraint, .hint _ _ _ => PUnit
  blockCtx := fun
  | .constraint, .assertR1C _ _ _ => nofun
  | .constraint, .rangeCheck _ _ => nofun
  | .constraint, .assertSpread _ _ _ => nofun
  | .constraint, .hint _ _ _ => fun _ => .hint
  blockInputs := fun
  | .constraint, .assertR1C _ _ _ => nofun
  | .constraint, .rangeCheck _ _ => nofun
  | .constraint, .assertSpread _ _ _ => nofun
  | .constraint, .hint n _ _ => fun _ => Vector (ZMod P) n
  blockOutputs := fun
  | .constraint, .assertR1C _ _ _ => nofun
  | .constraint, .rangeCheck _ _ => nofun
  | .constraint, .assertSpread _ _ _ => nofun
  | .constraint, .hint _ m _ => fun _ => Vector (ZMod P) m

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

/-- A hint: `m` fresh witnesses, computed by `h` from the values of `args`.
The constraints see only the wires; witness generation runs `h` on the
arguments' values and assigns its results to them, in order. Nothing
constrains them: whatever is assumed of them must be asserted. -/
def hint {n m : Nat} (args : Vector ctx.W n)
    (h : Vector (ZMod P) n → Hint P (Vector (ZMod P) m)) : Circuit P (Vector ctx.W m) :=
  Free.op (E := Circuit.Eff P ctx) (γ := .constraint) (.hint n m args)
    (fun _ inputs => h inputs)

-- def runWithHints (c : Circuit P α) : Option α :=

end Freigen.Circuit
