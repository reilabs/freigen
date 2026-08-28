import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.BooleanRing

namespace Freigen.F2Z

/-- An additive representation of linear combinations over `F`, including
the distinguished constant-one combination. -/
class ModuleWithOne (F : outParam (Type u)) (W : Type v)
    [Semiring F] [AddCommMonoid W] extends Module F W, One W

instance {F : Type u} [Semiring F] : ModuleWithOne F F where

/-- A semantics for an abstract representation of linear combinations. -/
structure Valuation (F : Type u) (W : Type v) [Semiring F]
    [AddCommMonoid W] [ModuleWithOne F W] where
  toFun : W →ₗ[F] F
  one_map : toFun 1 = 1

variable {F W} [Semiring F] [AddCommMonoid W] [ModuleWithOne F W]

instance : CoeFun (Valuation F W) fun _ => W → F where
  coe valuation := valuation.toFun

@[simp] theorem Valuation.one_apply (valuation : Valuation F W) :
    valuation (1 : W) = 1 := valuation.one_map

@[simp] theorem Valuation.zero_apply (valuation : Valuation F W) :
    valuation (0 : W) = 0 := valuation.toFun.map_zero

@[simp] theorem Valuation.add_apply (valuation : Valuation F W) (x y : W) :
    valuation (x + y) = valuation x + valuation y :=
  valuation.toFun.map_add x y

@[simp] theorem Valuation.smul_apply (valuation : Valuation F W)
    (factor : F) (x : W) :
    valuation (factor • x) = factor * valuation x :=
  valuation.toFun.map_smul factor x

@[simp] theorem Valuation.array_sum (valuation : Valuation F W)
    (xs : Array W) :
    valuation xs.sum = (xs.map valuation).sum := by
  rw [← Array.sum_toList, ← Array.sum_toList]
  simp only [Array.toList_map]
  induction xs.toList with
  | nil => simp
  | cons x xs ih => simp [ih]

@[simp] theorem Valuation.finset_sum {I : Type*} (valuation : Valuation F W)
    (s : Finset I) (f : I → W) :
    valuation (∑ i ∈ s, f i) = ∑ i ∈ s, valuation (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

@[simp] theorem Valuation.sub_apply {R W} [Ring R] [AddCommGroup W]
    [ModuleWithOne R W] (valuation : Valuation R W) (x y : W) :
    valuation (x - y) = valuation x - valuation y :=
  valuation.toFun.map_sub x y

/-- The two abstract witness representations available to an F2Z circuit.

Integer combinations form a group because circuit construction uses
subtraction. Boolean combinations only need their additive module structure.
-/
class Context where
  Wℤ : Type
  WBool : Type
  [addCommGroupWℤ : AddCommGroup Wℤ]
  [moduleWithOneWℤ : ModuleWithOne ℤ Wℤ]
  [addCommMonoidWBool : AddCommMonoid WBool]
  [moduleWithOneWBool : ModuleWithOne Bool WBool]

attribute [implicit_reducible]
  Context.addCommGroupWℤ Context.moduleWithOneWℤ
  Context.addCommMonoidWBool Context.moduleWithOneWBool

attribute [instance]
  Context.addCommGroupWℤ Context.moduleWithOneWℤ
  Context.addCommMonoidWBool Context.moduleWithOneWBool

namespace Context

/-- The pair of valuations used to compare or interpret a context. -/
structure Valuations (ctx : Context) where
  bool : Freigen.F2Z.Valuation Bool ctx.WBool
  int : Freigen.F2Z.Valuation ℤ ctx.Wℤ

/-- The valuation of the direct scalar representation. -/
def identityValuation (F : Type u) [Semiring F] : Valuation F F where
  toFun := LinearMap.id
  one_map := rfl

@[simp] theorem identityValuation_apply (F : Type u) [Semiring F] (x : F) :
    identityValuation F x = x := rfl

end Context

/-- Embed a scalar as a constant abstract linear combination. -/
def ofScalar {F W} [Semiring F] [AddCommMonoid W] [ModuleWithOne F W]
    (value : F) : W := value • 1

@[simp] theorem Valuation.ofScalar_apply
    (valuation : Valuation F W) (value : F) :
    valuation (ofScalar value) = value := by
  simp [ofScalar]

instance (priority := 100) {F W} [Semiring F] [AddCommMonoid W]
    [ModuleWithOne F W] : NatCast W where
  natCast value := value • (1 : W)

end Freigen.F2Z
