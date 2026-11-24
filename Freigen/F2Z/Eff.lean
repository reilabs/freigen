import Freigen.F2Z.LC
import Freigen.CompM.Basic
import Freigen.Eff
import Freigen.Free.Basic
import Freigen.Wheels

namespace Freigen.F2Z.Eff

inductive Scope : Type
| constraint : Scope
| hint : Scope

inductive WitnessSide
| z : WitnessSide
| f₂ : WitnessSide

def WitnessSide.denoteW : WitnessSide → Type
| WitnessSide.z  => LC ℤ
| WitnessSide.f₂ => LC Bool

def WitnessSide.denoteF : WitnessSide → Type
| WitnessSide.z  => ℤ
| WitnessSide.f₂ => Bool

unif_hint denoteW_z (side : WitnessSide) where
  side =?= WitnessSide.z
  ⊢ LC ℤ =?= side.denoteW

unif_hint denoteW_f₂ (side : WitnessSide) where
  side =?= WitnessSide.f₂
  ⊢ LC Bool =?= side.denoteW

/- Keep the witness sort visible to unification hints instead of reducing an
unknown sort to a stuck recursor.  The equations remain available explicitly
with `simp [WitnessSide.denoteW]`. -/
attribute [irreducible] WitnessSide.denoteW

inductive ConstraintEff : Type u where
| assertR1C (a b c : LC ℤ)
| f2z (a : LC Bool)
| hint (argTps : List WitnessSide)
    (args : HList WitnessSide.denoteW argTps) (n : Nat)

inductive HintEff where
| fail : Type → String → HintEff

end Eff

def Eff : Eff.Scope → Type _
| .constraint => Eff.ConstraintEff
| .hint => Eff.HintEff

namespace Eff

instance : Freigen.Eff.Spec (Γ := Eff.Scope) Eff where
  output := fun
    | .constraint, .assertR1C _ _ _ => Unit
    | .constraint, .f2z _ => LC ℤ
    | .constraint, .hint _ _ n => Vector (LC Bool) n
    | .hint, .fail α _ => α
  blockTag := fun
    | .constraint, .assertR1C _ _ _ => PEmpty
    | .constraint, .f2z _ => PEmpty
    | .constraint, .hint _ _ _ => PUnit
    | .hint, .fail _ _ => PEmpty
  blockCtx := fun
    | .constraint, .assertR1C _ _ _ => nofun
    | .constraint, .f2z _ => nofun
    | .constraint, .hint _ _ _ => fun _ => .hint
    | .hint, .fail _ _ => nofun
  blockInputs := fun
    | .constraint, .assertR1C _ _ _ => nofun
    | .constraint, .f2z _ => nofun
    | .constraint, .hint argTps _ _ => fun _ => HList WitnessSide.denoteF argTps
    | .hint, .fail _ _ => nofun
  blockOutputs := fun
    | .constraint, .assertR1C _ _ _ => nofun
    | .constraint, .f2z _ => fun _ => LC ℤ
    | .constraint, .hint _ _ n => fun _ => Vector Bool n
    | .hint, .fail _ _ => nofun

end Freigen.F2Z.Eff
