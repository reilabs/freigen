import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic

namespace Freigen.Circuit

open scoped BigOperators

structure Valuation
    (F W : Type) [Semiring F] [AddCommMonoid W] [One W] [Module F W] where
  toFun : W →ₗ[F] F
  one_map : toFun 1 = 1

instance {F W} [Semiring F] [AddCommMonoid W] [One W] [Module F W] : CoeFun (Valuation F W) fun _ => W → F where
  coe v := v.toFun

abbrev Assertion
    (F W : Type) [Semiring F] [AddCommMonoid W] [One W] [Module F W] :=
  Valuation F W → Prop

class CertLogic {World : Type} (Cert : (World → Prop) → Sort u) where
  derive
      {ι : Type}
      {P : ι → World → Prop}
      {Q : World → Prop} :
    (∀ world, (∀ i, P i world) → Q world) →
    ((i : ι) → Cert (P i)) →
    Cert Q

/-- A circuit context over the prime field `ZMod P`: wires form a module over
the field, and certificates witness assertions about every valuation. -/
class Context (P : Nat) where
  W : Type
  [addGroupW : AddCommGroup W]
  [oneW: One W]
  [moduleW : Module (ZMod P) W]
  /-- Certificates are data (`Type`), so that operations can return them, but
  carry no more information than a proof. -/
  Cert : Assertion (ZMod P) W → Type
  [certLogic : CertLogic Cert]
  [certSubsingleton : ∀ A, Subsingleton (Cert A)]

attribute [implicit_reducible]
  Context.addGroupW
  Context.moduleW
  Context.certLogic
  Context.oneW

attribute [instance]
  Context.addGroupW
  Context.moduleW
  Context.certLogic
  Context.oneW
  Context.certSubsingleton

abbrev Cert {P : Nat} [ctx : Context P]
    (A : Assertion (ZMod P) ctx.W) :=
  ctx.Cert A

def Cert.map {P : Nat} [ctx : Context P]
    {A B : Assertion (ZMod P) ctx.W}
    (f : ∀ ρ, A ρ → B ρ)
    (cert : Cert A) :
    Cert B :=
  ctx.certLogic.derive (ι := Unit) (fun _ f' => f _ (f' ()) ) (fun _ => cert)

structure CertW {P : Nat} [ctx : Context P]
    (Pred : ctx.W → Assertion (ZMod P) ctx.W) where
  val : ctx.W
  cert : Cert (Pred val)

instance {P : Nat} [ctx : Context P] {Q : ctx.W → Assertion (ZMod P) ctx.W} : CoeOut (CertW (P:=P) Q) ctx.W where
  coe c := c.val

namespace Cert

def derive {P : Nat} [ctx : Context P]
    {ι : Type}
    {A : ι → Assertion (ZMod P) ctx.W}
    {B : Assertion (ZMod P) ctx.W}
    (rule : ∀ ρ, (∀ i, A i ρ) → B ρ)
    (premises : (i : ι) → Cert (A i)) :
    Cert B :=
  CertLogic.derive rule premises

end Cert

def IsInRange {P : Nat} (n : Nat) (x : ZMod P) : Prop :=
  ∃ k : Nat, k < 2 ^ n ∧ x = (k : ZMod P)

def RangeAssertion {P : Nat} [ctx : Context P]
    (n : Nat) (x : ctx.W) : Assertion (ZMod P) ctx.W :=
  fun ρ => IsInRange n (ρ x)

def R1CSAssertion {P : Nat} [ctx : Context P]
    (a b c : ctx.W) : Assertion (ZMod P) ctx.W :=
  fun ρ => ρ a * ρ b = ρ c

def SpreadAssertion {P : Nat} [ctx : Context P]
    (n : Nat) (a b : ctx.W) : Assertion (ZMod P) ctx.W :=
  fun ρ =>
    ∃ bits : Fin n → Bool,
      ρ a = (∑ i, if bits i then (2 : ZMod P) ^ i.val else 0) ∧
      ρ b = (∑ i, if bits i then (2 : ZMod P) ^ (2 * i.val) else 0)

def ValueAssertion {P : Nat} [ctx : Context P]
    (a : ZMod P) (x : ctx.W) : Assertion (ZMod P) ctx.W :=
  fun ρ => ρ x = a

abbrev WUInt (P : Nat) [ctx : Context P] (n : Nat) :=
  CertW $ RangeAssertion (P:=P) n

abbrev WU32 (P : Nat) [Context P] := WUInt P 32

end Freigen.Circuit
