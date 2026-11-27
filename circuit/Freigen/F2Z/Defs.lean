import Freigen.F2Z.LC
import Freigen.F2Z.Eff

namespace Freigen.F2Z

abbrev Circuit : Type → Type _ :=
  Free Eff .constraint

instance : Monad (Circuit) :=
  inferInstanceAs (Monad (Free Eff .constraint))

instance : LawfulMonad (Circuit) :=
  inferInstanceAs (LawfulMonad (Free Eff .constraint))

abbrev Hint : Type → Type _ :=
  Free Eff .hint

instance : Monad (Hint) :=
  inferInstanceAs (Monad (Free Eff .hint))

instance : LawfulMonad (Hint) :=
  inferInstanceAs (LawfulMonad (Free Eff .hint))

def assertR1C (a b c : LC ℤ) : Circuit Unit :=
  Free.op (E := Eff) (γ := .constraint) (Eff.ConstraintEff.assertR1C a b c) nofun

def f2z (a : LC Bool) : Circuit (LC ℤ) :=
  Free.op (E := Eff) (γ := .constraint) (Eff.ConstraintEff.f2z a) nofun

def hint {n : Nat} {argTps : List Eff.WitnessSide}
    (args : HList Eff.WitnessSide.denoteW argTps)
    (body : HList Eff.WitnessSide.denoteF argTps → Hint (Vector Bool n)) :
    Circuit (Vector (LC Bool) n) :=
  Free.op (E := Eff) (γ := .constraint) (Eff.ConstraintEff.hint argTps args n) (fun _ => body)

def fail {α : Type} (msg : String) : Hint α :=
  Free.op (E := Eff) (γ := .hint) (Eff.HintEff.fail α msg) nofun

end Freigen.F2Z
