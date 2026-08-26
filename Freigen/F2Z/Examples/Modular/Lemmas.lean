import Freigen.F2Z.Examples.Modular.Impl

/-!
# Auxiliary lemmas for modular arithmetic correctness

This module contains supporting facts used by the public soundness,
completeness, and well-formedness proofs.
-/

namespace Freigen.F2Z.Examples.Modular

open Std.Do
open scoped Std.Do

@[simp] theorem intCastRingHom_apply {R : Type} [Ring R] (x : Int) :
    Int.castRingHom R x = (x : R) := rfl

variable {n : Nat} (p : Params n)

namespace Elem

theorem nonneg {x : Elem p} (h : x.Valid ρ) :
    0 ≤ x.val.intVal.eval ρ.int :=
  U.intVal_nonneg x.val h.1

theorem evalNat_cast {x : Elem p} (h : x.Valid ρ) :
    (x.evalNat ρ : Int) = x.val.intVal.eval ρ.int := by
  simp [evalNat, Int.toNat_of_nonneg (Elem.nonneg (p := p) h)]

theorem evalNat_lt {x : Elem p} (h : x.Valid ρ) :
    x.evalNat ρ < p.modulus := by
  unfold evalNat
  exact (Int.toNat_lt (Elem.nonneg (p := p) h)).2 h.2


end Elem

theorem ofNat_valid (x : Nat) (hfit : x < 2 ^ n) (hlt : x < p.modulus) :
    (ofNat p x hfit hlt).Valid ρ := by
  constructor
  · exact U.valid_bitVec _
  · change ((BitVec.ofNat n x : U n).intVal.eval ρ.int) < p.modulus
    rw [U.intVal_eval_eq_eval_toNat _ (U.valid_bitVec _), U.eval_bitVec]
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]

theorem ofNat_evalNat (x : Nat) (hfit : x < 2 ^ n) (hlt : x < p.modulus) :
    (ofNat p x hfit hlt).evalNat ρ = x := by
  unfold Elem.evalNat
  change ((BitVec.ofNat n x : U n).intVal.eval ρ.int).toNat = x
  rw [U.intVal_eval_eq_eval_toNat _ (U.valid_bitVec _), U.eval_bitVec]
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]

namespace Lazy

@[simp] theorem evalZMod_ofElem (x : Elem p) :
    evalZMod p (ofElem p x) ρ = evalElemZMod p x ρ := rfl

@[simp] theorem evalZMod_add (x y : Rep p) :
    evalZMod p (add p x y) ρ = evalZMod p x ρ + evalZMod p y ρ := by
  simp [evalZMod, add, Int.cast_add]

@[simp] theorem evalZMod_sub (x y : Rep p) :
    evalZMod p (sub p x y) ρ = evalZMod p x ρ - evalZMod p y ρ := by
  simp [evalZMod, sub, Int.cast_sub, Int.cast_add]

@[simp] theorem evalZMod_scale (k : Nat) (x : Rep p) :
    evalZMod p (scale p k x) ρ = k * evalZMod p x ρ := by
  simp [evalZMod, scale, Int.cast_mul]

theorem ofElem_valid {x : Elem p} (hx : x.Valid ρ) :
    (ofElem p x).Valid ρ := by
  refine ⟨Elem.nonneg (p := p) hx, ?_⟩
  change x.val.intVal.eval ρ.int < ((2 * p.modulus : Nat) : Int)
  push_cast
  have hp : (0 : Int) < p.modulus := by exact_mod_cast p.positive
  nlinarith [hx.2]

theorem add_valid {x y : Rep p} (hx : x.Valid ρ) (hy : y.Valid ρ) :
    (add p x y).Valid ρ := by
  rcases hx with ⟨hx0, hxlt⟩
  rcases hy with ⟨hy0, hylt⟩
  constructor
  · simpa [add, Rep.Valid] using add_nonneg hx0 hy0
  · simp only [add, Rep.Valid, LC.eval_add]
    push_cast
    ring_nf
    nlinarith

theorem sub_valid {x y : Rep p} (hx : x.Valid ρ) (hy : y.Valid ρ) :
    (sub p x y).Valid ρ := by
  rcases hx with ⟨hx0, hxlt⟩
  rcases hy with ⟨hy0, hylt⟩
  constructor
  · simp only [sub, Rep.Valid, LC.eval_sub, LC.eval_add,
      LC.eval_ofConst]
    push_cast
    omega
  · simp only [sub, Rep.Valid, LC.eval_sub, LC.eval_add,
      LC.eval_ofConst]
    push_cast
    ring_nf
    nlinarith

theorem scale_valid {x : Rep p} (hx : x.Valid ρ) {k : Nat} (hk : 0 < k) :
    (scale p k x).Valid ρ := by
  rcases hx with ⟨hx0, hxlt⟩
  constructor
  · simp only [scale, Rep.Valid, LC.eval_nsmul, nsmul_eq_mul]
    positivity
  · simp only [scale, Rep.Valid, LC.eval_nsmul, nsmul_eq_mul]
    push_cast
    ring_nf
    have hk0 : (0 : Int) < k := by exact_mod_cast hk
    nlinarith

theorem toNat_lt_bound {x : Rep p} (hx : x.Valid ρ) :
    (x.intVal.eval ρ.int).toNat < x.bound * p.modulus :=
  (Int.toNat_lt hx.1).2 hx.2

theorem mul_quotient_fits {x y : Rep p}
    (hx : x.Valid ρ) (hy : y.Valid ρ)
    (hbound : x.bound * y.bound < 2 ^ quotientExtraBits) :
    (x.intVal.eval ρ.int).toNat * (y.intVal.eval ρ.int).toNat /
      p.modulus < 2 ^ (n + quotientExtraBits) := by
  let a := (x.intVal.eval ρ.int).toNat
  let b := (y.intVal.eval ρ.int).toNat
  have ha := toNat_lt_bound p hx
  have hb := toNat_lt_bound p hy
  have hproduct : a * b <
      (x.bound * y.bound * p.modulus) * p.modulus := by
    dsimp [a, b] at *
    nlinarith [p.positive]
  calc
    a * b / p.modulus < x.bound * y.bound * p.modulus :=
      Nat.div_lt_of_lt_mul (by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hproduct)
    _ < 2 ^ quotientExtraBits * 2 ^ n :=
      Nat.mul_lt_mul_of_lt_of_le hbound p.fits (by positivity)
    _ = 2 ^ (n + quotientExtraBits) := by
      rw [pow_add]
      ac_rfl

end Lazy

namespace Aux

def quotientBits (totalWidth n low high : Nat) :
    Vector Bool totalWidth :=
  Vector.ofFn fun i => if hi : i.val < n then
    low.testBit i.val
  else
    high.testBit (i.val - n)

theorem quotientBits_low {totalWidth n low high : Nat}
    (hwidth : n ≤ totalWidth) (hfit : low < 2 ^ n)
    (ρ : WF.Valuation) :
    (Word.eval ρ.bool {
      bitsLE := Vector.ofFn (n := n) fun i =>
        (Vector.map LC.ofConst
          (quotientBits totalWidth n low high))[i.val]'(by omega)
    }).toNat = low := by
  simp [quotientBits, Word.eval, BitVec.toNat_ofFnLE,
    Nat.ofBits_testBit, Nat.mod_eq_of_lt hfit]

theorem quotientBits_high {totalWidth n quotientWidth low high : Nat}
    (hwidth : n + quotientWidth ≤ totalWidth)
    (hfit : high < 2 ^ quotientWidth) (ρ : WF.Valuation) :
    (Word.eval ρ.bool {
      bitsLE := Vector.ofFn (n := quotientWidth) fun i =>
        (Vector.map LC.ofConst
          (quotientBits totalWidth n low high))[n + i.val]'(by omega)
    }).toNat = high := by
  simp [quotientBits, Word.eval, BitVec.toNat_ofFnLE,
    show ∀ i : Fin quotientWidth, ¬n + i.val < n by omega,
    Nat.ofBits_testBit, Nat.mod_eq_of_lt hfit]

theorem constWord_eval_toNat {n : Nat} (v : Nat)
    (hv : v < 2 ^ n) (ρ : WF.Valuation) :
    (Word.eval ρ.bool {
      bitsLE := Vector.ofFn (n := n) fun i => LC.ofConst (v.testBit i)
    }).toNat = v := by
  simp [Word.eval, BitVec.toNat_ofFnLE, Nat.ofBits_testBit,
    Nat.mod_eq_of_lt hv]

theorem WF.lceq_of_common_realizes
    {left right : Vector (LC Bool) m} {lv rv : WF.Valuation}
    (h : ∃ values : Vector Bool m,
      WF.RealizesBools lv.bool left values ∧
      WF.RealizesBools rv.bool right values)
    (i : Nat) (hi : i < m) :
    WF.LCEq lv.bool rv.bool left[i] right[i] := by
  rcases h with ⟨values, hleft, hright⟩
  exact (hleft i hi).trans (hright i hi).symm

/-- Any fixed slice of a common hint result gives related word bits.  Unlike
the older low/high helpers, this also covers quotient witnesses with a few
extra slack bits. -/
theorem WF.wordSlice_lceq_of_common_realizes
    {left right : Vector (LC Bool) m} {lv rv : WF.Valuation}
    (h : ∃ values : Vector Bool m,
      WF.RealizesBools lv.bool left values ∧
      WF.RealizesBools rv.bool right values)
    (offset width : Nat) (hfit : offset + width ≤ m) (i : Fin width) :
    WF.LCEq lv.bool rv.bool
      ({ bitsLE := Vector.ofFn fun j =>
          left[offset + j.val]'(by omega) } : Word width)[i]
      ({ bitsLE := Vector.ofFn fun j =>
          right[offset + j.val]'(by omega) } : Word width)[i] := by
  unfold WF.LCEq
  change LC.eval lv.bool
      (Vector.ofFn fun j : Fin width => left[offset + j.val]'(by omega))[i] =
    LC.eval rv.bool
      (Vector.ofFn fun j : Fin width => right[offset + j.val]'(by omega))[i]
  have hleft :
      (Vector.ofFn fun j : Fin width =>
        left[offset + j.val]'(by omega))[i] = left[offset + i.val] := by
    change (Vector.ofFn fun j : Fin width =>
      left[offset + j.val]'(by omega)).get i = _
    simp
  have hright :
      (Vector.ofFn fun j : Fin width =>
        right[offset + j.val]'(by omega))[i] = right[offset + i.val] := by
    change (Vector.ofFn fun j : Fin width =>
      right[offset + j.val]'(by omega)).get i = _
    simp
  rw [hleft, hright]
  exact WF.lceq_of_common_realizes h (offset + i.val) (by omega)

theorem WF.common_realizes_of_post
    {left right : Vector (LC Bool) m} {lv rv : WF.Valuation}
    {P Q : Prop} {A B : Vector Bool m → Prop}
    (h : (P ∧ ∃ values, A values ∧ B values ∧
      WF.RealizesBools lv.bool left values ∧
      WF.RealizesBools rv.bool right values) ∧ Q) :
    ∃ values, WF.RealizesBools lv.bool left values ∧
      WF.RealizesBools rv.bool right values := by
  rcases h.1.2 with ⟨values, _, _, hleft, hright⟩
  exact ⟨values, hleft, hright⟩

theorem WF.common_realizes_of_hint
    {left right : Vector (LC Bool) m} {lv rv : WF.Valuation}
    {R : Prop} {bodyL bodyR : Hint (Vector Bool m)}
    (h : R ∧ ∃ values, WF.HintReturns bodyL values ∧
      WF.HintReturns bodyR values ∧
      WF.RealizesBools lv.bool left values ∧
      WF.RealizesBools rv.bool right values) :
    ∃ values, WF.RealizesBools lv.bool left values ∧
      WF.RealizesBools rv.bool right values := by
  rcases h.2 with ⟨values, _, _, hleft, hright⟩
  exact ⟨values, hleft, hright⟩

end Aux

end Freigen.F2Z.Examples.Modular
