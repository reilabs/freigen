import Freigen.CompM.Basic
import Freigen.ITree.Basic
import Freigen.Eff

namespace Freigen.CompM.Examples.Nondet

inductive Eff : Type
| rand
| print (z : Int)

abbrev Effects : Unit → Type := fun _ => Eff
abbrev Stack := Eff.Tau ⊕ₑ Effects

instance : Eff.Spec Effects where
  output
    | _, .rand => Int
    | _, .print _ => Unit
  blockTag := fun _ _ => Empty
  blockCtx := nofun
  blockInputs := nofun
  blockOutputs := nofun

end Nondet

abbrev Nondet α := CompM Nondet.Stack () α

namespace Nondet

def rand : Nondet Int :=
  CompM.op (E := Stack) (Sum.inr Eff.rand) nofun

def print (z : Int) : Nondet Unit :=
  CompM.op (E := Stack) (Sum.inr (Eff.print z)) nofun

def approxWith {α} (entropy : Nat → Int) (t : Nondet α) (n: Nat): List Int :=
  go (entropy, 0) n ((t.run pure).approx n) where
  go : (Nat → Int) × Nat → (n : Nat) →
      IxPoly.M.Approx (Eff.Step Unit Stack) n ((), α) →
      List Int := fun entropy n approx => match n, approx with
   | 0, IxPoly.M.Approx.zero _ => []
   | n+1, IxPoly.M.Approx._succ _ _ p k => match p with
     | .ret _ => []
     | .op (Sum.inr Eff.rand) => go (entropy.1, entropy.2 + 1) n (k $ .inl (entropy.1 entropy.2))
     | .op (Sum.inr (Eff.print z)) => z :: go entropy n (k $ .inl ())
     | .op (Sum.inl _) => go entropy n (k $ .inl ())

end Freigen.CompM.Examples.Nondet
