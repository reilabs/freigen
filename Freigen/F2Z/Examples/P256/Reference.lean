import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.ZMod
import Freigen.F2Z.Examples.P256.Impl

/-!
# Mathlib reference model for P-256

This file fixes the P-256 short Weierstrass curve over `ZMod baseModulus` and
exposes Mathlib's affine point group as the reference semantics for the circuit
implementation.  Primality of the published P-256 base modulus is deliberately
the only axiom in this comparison layer; every later group-law statement is a
theorem about Mathlib's elliptic-curve model.
-/

namespace Freigen.F2Z.Examples.P256.Reference

open Freigen.F2Z.Examples.P256

local instance : Context := lcContext

/-- The trusted boundary of the P-256 reference model. -/
axiom baseModulus_prime : Nat.Prime baseModulus

instance : Fact (Nat.Prime baseModulus) := ⟨baseModulus_prime⟩

instance : Fact (Nat.Prime base.modulus) := ⟨baseModulus_prime⟩

abbrev Field := ZMod base.modulus

/-- P-256 in Mathlib's general Weierstrass form:
`y^2 = x^3 - 3*x + b`. -/
def curve : WeierstrassCurve Field where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -3
  a₆ :=
    0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b

theorem curve_discriminant_ne_zero : curve.Δ ≠ 0 := by
  native_decide

instance : curve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr curve_discriminant_ne_zero⟩

abbrev Point := curve.toAffine.Point

theorem generator_equation : curve.toAffine.Equation
    (generatorX.val.intVal.constant.toNat : Field)
    (generatorY.val.intVal.constant.toNat : Field) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  native_decide

/-- The standard P-256 generator, now as a Mathlib affine point. -/
def generator : Point := .mk generator_equation

theorem equation_iff_short (x y : Field) :
    curve.toAffine.Equation x y ↔
      y ^ 2 = x ^ 3 - 3 * x +
        (0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b :
          Field) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [curve]
  ring_nf

/-- Turn a successful circuit curve equation into a point of Mathlib's
affine P-256 group. -/
def pointOfCircuit (ρ : WF.Valuation) (x y : Fp)
    (h : Projective.Lazy.OnCurveZModSpec ρ x y) : Point :=
  .mk ((equation_iff_short _ _).2 (by
    simpa [Projective.Lazy.OnCurveZModSpec] using h))

/-- Raw affine coordinates, with a separate constructor for the point at
infinity.  This is the shape implemented by `AffineSlope.Point`; unlike
`Point`, it does not carry an on-curve proof in every finite value. -/
inductive Coordinates where
  | infinity
  | finite (x y : Field)
  deriving DecidableEq

def coordinates : Point → Coordinates
  | 0 => .infinity
  | .some x y _ => .finite x y

/-- Interpret the optimized circuit representation as raw `ZMod` affine
coordinates.  `Represents` separately requires the infinity flag to be a bit,
so its non-one branch is the finite branch. -/
def circuitCoordinates (ρ : WF.Valuation)
    (P : AffineSlope.Point) : Coordinates :=
  if ρ.int P.infinity = 1 then .infinity
  else .finite (Modular.Lazy.evalZMod base P.X ρ)
    (Modular.Lazy.evalZMod base P.Y ρ)

def Represents (ρ : WF.Valuation) (P : AffineSlope.Point)
    (p : Point) : Prop :=
  (ρ.int P.infinity = 0 ∨ ρ.int P.infinity = 1) ∧
    circuitCoordinates ρ P = coordinates p

/-- Scalar multiplication keeps a canonical carrier for the identity.  This
extra invariant is needed by the selector-free doubling circuit, whose
inactive formula is evaluated at `(0,0)`. -/
def NormalizedRep (ρ : WF.Valuation) (P : AffineSlope.Point)
    (p : Point) : Prop :=
  Represents ρ P p ∧
    (p = 0 → Modular.Lazy.evalZMod base P.X ρ = 0 ∧
      Modular.Lazy.evalZMod base P.Y ρ = 0)

/-- The chord slope used by the generic branch of complete affine addition.
The signs are reversed together relative to Mathlib's presentation. -/
def chordSlope (x₁ y₁ x₂ y₂ : Field) : Field :=
  (y₂ - y₁) / (x₂ - x₁)

/-- The P-256 tangent slope used by complete doubling and the doubling branch
of complete affine addition. -/
def tangentSlope (x y : Field) : Field :=
  (3 * x ^ 2 - 3) / (2 * y)

def resultX (x₁ x₂ slope : Field) : Field :=
  slope ^ 2 - x₁ - x₂

def resultY (x₁ x₂ y₁ slope : Field) : Field :=
  slope * (x₁ - resultX x₁ x₂ slope) - y₁

/-- Pure branch-level semantics of `AffineSlope.addComplete`.  It deliberately
returns raw coordinates: the equivalence theorem in `P256` proves that these
are exactly the coordinates of Mathlib point addition. -/
def slopeAddCoordinates : Point → Point → Coordinates
  | 0, Q => coordinates Q
  | P, 0 => coordinates P
  | .some x₁ y₁ _, .some x₂ y₂ _ =>
      if x₁ = x₂ then
        if y₁ = curve.toAffine.negY x₂ y₂ then .infinity
        else
          let slope := tangentSlope x₁ y₁
          .finite (resultX x₁ x₂ slope) (resultY x₁ x₂ y₁ slope)
      else
        let slope := chordSlope x₁ y₁ x₂ y₂
        .finite (resultX x₁ x₂ slope) (resultY x₁ x₂ y₁ slope)

end Freigen.F2Z.Examples.P256.Reference
