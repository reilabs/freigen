import Freigen.F2Z.Context
import Freigen.CompM.Basic
import Freigen.Eff
import Freigen.Free.Basic
import Freigen.Wheels

namespace Freigen.F2Z.Eff

inductive Scope : Type u
| constraint : Scope
| hint : Scope

inductive WitnessSide
| z : WitnessSide
| f₂ : WitnessSide

def WitnessSide.denoteW (ctx : Context) : WitnessSide → Type
| WitnessSide.z  => ctx.Wℤ
| WitnessSide.f₂ => ctx.WBool

def WitnessSide.denoteF : WitnessSide → Type
| WitnessSide.z  => ℤ
| WitnessSide.f₂ => Bool

unif_hint denoteW_z (ctx : Context) (side : WitnessSide) where
  side =?= WitnessSide.z
  ⊢ ctx.Wℤ =?= side.denoteW ctx

unif_hint denoteW_f₂ (ctx : Context) (side : WitnessSide) where
  side =?= WitnessSide.f₂
  ⊢ ctx.WBool =?= side.denoteW ctx

/- Keep the witness sort visible to unification hints instead of reducing an
unknown sort to a stuck recursor.  The equations remain available explicitly
with `simp [WitnessSide.denoteW]`. -/
-- `denoteW` stays reducible: context parameters now make both the witness
-- representation and the witness sort visible to unification.

inductive ConstraintEff (ctx : Context) : Type u where
| assertR1C (a b c : ctx.Wℤ)
| f2z (a : ctx.WBool)
| hint (argTps : List WitnessSide)
    (args : HList (WitnessSide.denoteW ctx) argTps) (n : Nat)

inductive HintEff (ctx : Context) where
| fail : Type → String → HintEff ctx

end Eff

def Eff (ctx : Context) : Eff.Scope → Type _
| .constraint => Eff.ConstraintEff ctx
| .hint => Eff.HintEff ctx

namespace Eff

instance (ctx : Context) : Freigen.Eff.Spec (Γ := Eff.Scope) (Eff ctx) where
  output := fun
    | .constraint, .assertR1C _ _ _ => Unit
    | .constraint, .f2z _ => ctx.Wℤ
    | .constraint, .hint _ _ n => Vector ctx.WBool n
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
    | .constraint, .f2z _ => fun _ => ctx.Wℤ
    | .constraint, .hint _ _ n => fun _ => Vector Bool n
    | .hint, .fail _ _ => nofun

end Freigen.F2Z.Eff
