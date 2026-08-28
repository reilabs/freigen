import Freigen.F2Z.Examples.Modular.Impl

/-!
# Auxiliary lemmas for modular arithmetic correctness

This module contains supporting facts used by the public soundness,
completeness, and well-formedness proofs.
-/

namespace Freigen.F2Z.Examples.Modular

local instance : Context := lcContext

open Std.Do
open scoped Std.Do

@[simp] theorem intCastRingHom_apply {R : Type} [Ring R] (x : Int) :
    Int.castRingHom R x = (x : R) := rfl

variable {n : Nat} (p : Params n)

namespace Elem

theorem nonneg {x : Elem p} (h : x.Valid ρ) :
    0 ≤ ρ.int x.val.intVal :=
  by
    exact U.intVal_nonneg x.val h.1

theorem evalNat_cast {x : Elem p} (h : x.Valid ρ) :
    (x.evalNat ρ : Int) = ρ.int x.val.intVal := by
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
  · change ρ.int ((BitVec.ofNat n x : U n).intVal) < p.modulus
    rw [U.intVal_eval_eq_eval_toNat _ (U.valid_bitVec _), U.eval_bitVec]
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]

theorem ofNat_evalNat (x : Nat) (hfit : x < 2 ^ n) (hlt : x < p.modulus) :
    (ofNat p x hfit hlt).evalNat ρ = x := by
  unfold Elem.evalNat
  change (ρ.int ((BitVec.ofNat n x : U n).intVal)).toNat = x
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
  change ρ.int x.val.intVal < ((2 * p.modulus : Nat) : Int)
  push_cast
  have hp : (0 : Int) < p.modulus := by exact_mod_cast p.positive
  nlinarith [hx.2]

theorem add_valid {x y : Rep p} (hx : x.Valid ρ) (hy : y.Valid ρ) :
    (add p x y).Valid ρ := by
  rcases hx with ⟨hx0, hxlt⟩
  rcases hy with ⟨hy0, hylt⟩
  constructor
  · simpa [add, Rep.Valid] using add_nonneg hx0 hy0
  · simp only [add, Rep.Valid, Valuation.add_apply]
    push_cast
    ring_nf
    nlinarith

theorem sub_valid {x y : Rep p} (hx : x.Valid ρ) (hy : y.Valid ρ) :
    (sub p x y).Valid ρ := by
  rcases hx with ⟨hx0, hxlt⟩
  rcases hy with ⟨hy0, hylt⟩
  constructor
  · simp only [sub, Rep.Valid, Valuation.sub_apply, Valuation.add_apply,
      Valuation.ofScalar_apply]
    push_cast
    omega
  · simp only [sub, Rep.Valid, Valuation.sub_apply, Valuation.add_apply,
      Valuation.ofScalar_apply]
    push_cast
    ring_nf
    nlinarith

theorem scale_valid {x : Rep p} (hx : x.Valid ρ) {k : Nat} (hk : 0 < k) :
    (scale p k x).Valid ρ := by
  rcases hx with ⟨hx0, hxlt⟩
  constructor
  · simp only [scale, Rep.Valid, map_nsmul, nsmul_eq_mul]
    positivity
  · simp only [scale, Rep.Valid, map_nsmul, nsmul_eq_mul]
    push_cast
    ring_nf
    have hk0 : (0 : Int) < k := by exact_mod_cast hk
    nlinarith

theorem toNat_lt_bound {x : Rep p} (hx : x.Valid ρ) :
    (ρ.int x.intVal).toNat < x.bound * p.modulus :=
  (Int.toNat_lt hx.1).2 hx.2

theorem mul_quotient_fits {x y : Rep p}
    (hx : x.Valid ρ) (hy : y.Valid ρ)
    (hbound : x.bound * y.bound < 2 ^ quotientExtraBits) :
    (ρ.int x.intVal).toNat * (ρ.int y.intVal).toNat /
      p.modulus < 2 ^ (n + quotientExtraBits) := by
  let a := (ρ.int x.intVal).toNat
  let b := (ρ.int y.intVal).toNat
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
        (Vector.map ofScalar
          (quotientBits totalWidth n low high))[i.val]'(by omega)
    }).toNat = low := by
  simp [quotientBits, Word.eval, BitVec.toNat_ofFnLE,
    Nat.ofBits_testBit, Nat.mod_eq_of_lt hfit]

theorem quotientBits_low_lc {totalWidth n low high : Nat}
    (hwidth : n ≤ totalWidth) (hfit : low < 2 ^ n)
    (ρ : WF.Valuation) :
    (Word.eval ρ.bool {
      bitsLE := Vector.ofFn (n := n) fun i =>
        (Vector.map LC.ofConst
          (quotientBits totalWidth n low high))[i.val]'(by omega)
    }).toNat = low := by
  have hmap :
      Vector.map LC.ofConst (quotientBits totalWidth n low high) =
        Vector.map (fun bit => (ofScalar bit : LC Bool))
          (quotientBits totalWidth n low high) := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map]
    exact (LC.ofScalar_eq_ofConst (F := Bool)
      (quotientBits totalWidth n low high)[i]).symm
  rw [hmap]
  exact quotientBits_low hwidth hfit ρ

theorem quotientBits_high {totalWidth n quotientWidth low high : Nat}
    (hwidth : n + quotientWidth ≤ totalWidth)
    (hfit : high < 2 ^ quotientWidth) (ρ : WF.Valuation) :
    (Word.eval ρ.bool {
      bitsLE := Vector.ofFn (n := quotientWidth) fun i =>
        (Vector.map ofScalar
          (quotientBits totalWidth n low high))[n + i.val]'(by omega)
    }).toNat = high := by
  simp [quotientBits, Word.eval, BitVec.toNat_ofFnLE,
    show ∀ i : Fin quotientWidth, ¬n + i.val < n by omega,
    Nat.ofBits_testBit, Nat.mod_eq_of_lt hfit]

theorem quotientBits_high_lc {totalWidth n quotientWidth low high : Nat}
    (hwidth : n + quotientWidth ≤ totalWidth)
    (hfit : high < 2 ^ quotientWidth) (ρ : WF.Valuation) :
    (Word.eval ρ.bool {
      bitsLE := Vector.ofFn (n := quotientWidth) fun i =>
        (Vector.map LC.ofConst
          (quotientBits totalWidth n low high))[n + i.val]'(by omega)
    }).toNat = high := by
  have hmap :
      Vector.map LC.ofConst (quotientBits totalWidth n low high) =
        Vector.map (fun bit => (ofScalar bit : LC Bool))
          (quotientBits totalWidth n low high) := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map]
    exact (LC.ofScalar_eq_ofConst (F := Bool)
      (quotientBits totalWidth n low high)[i]).symm
  rw [hmap]
  exact quotientBits_high hwidth hfit ρ

theorem constWord_eval_toNat {n : Nat} (v : Nat)
    (hv : v < 2 ^ n) (ρ : WF.Valuation) :
    (Word.eval ρ.bool {
      bitsLE := Vector.ofFn (n := n) fun i => ofScalar (v.testBit i)
    }).toNat = v := by
  simp [Word.eval, BitVec.toNat_ofFnLE,
    Nat.ofBits_testBit,
    Nat.mod_eq_of_lt hv]

theorem constWord_eval_toNat_lc {n : Nat} (v : Nat)
    (hv : v < 2 ^ n) (ρ : WF.Valuation) :
    (Word.eval ρ.bool {
      bitsLE := Vector.ofFn (n := n) fun i => LC.ofConst (v.testBit i)
    }).toNat = v := by
  have hbits :
      (Vector.ofFn (n := n) fun i => LC.ofConst (v.testBit i)) =
        Vector.ofFn (n := n) fun i => (ofScalar (v.testBit i) : LC Bool) := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    exact (LC.ofScalar_eq_ofConst (F := Bool) (v.testBit i)).symm
  rw [hbits]
  exact constWord_eval_toNat v hv ρ

theorem WF.lceq_of_common_realizes
    {leftCtx rightCtx : Context}
    {left : Vector leftCtx.WBool m} {right : Vector rightCtx.WBool m}
    {lv : @WF.Valuation leftCtx} {rv : @WF.Valuation rightCtx}
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
    {leftCtx rightCtx : Context}
    {left : Vector leftCtx.WBool m} {right : Vector rightCtx.WBool m}
    {lv : @WF.Valuation leftCtx} {rv : @WF.Valuation rightCtx}
    (h : ∃ values : Vector Bool m,
      WF.RealizesBools lv.bool left values ∧
      WF.RealizesBools rv.bool right values)
    (offset width : Nat) (hfit : offset + width ≤ m) (i : Fin width) :
    WF.LCEq lv.bool rv.bool
      (@Word.bitsLE leftCtx width (@Word.mk leftCtx width
        (Vector.ofFn fun j : Fin width =>
          left[offset + j.val]'(by omega))))[i]
      (@Word.bitsLE rightCtx width (@Word.mk rightCtx width
        (Vector.ofFn fun j : Fin width =>
          right[offset + j.val]'(by omega))))[i] := by
  unfold WF.LCEq
  change lv.bool
      (Vector.ofFn fun j : Fin width => left[offset + j.val]'(by omega))[i] =
    rv.bool
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
    {leftCtx rightCtx : Context}
    {left : Vector leftCtx.WBool m} {right : Vector rightCtx.WBool m}
    {lv : @WF.Valuation leftCtx} {rv : @WF.Valuation rightCtx}
    {P Q : Prop} {A B : Vector Bool m → Prop}
    (h : (P ∧ ∃ values, A values ∧ B values ∧
      WF.RealizesBools lv.bool left values ∧
      WF.RealizesBools rv.bool right values) ∧ Q) :
    ∃ values, WF.RealizesBools lv.bool left values ∧
      WF.RealizesBools rv.bool right values := by
  rcases h.1.2 with ⟨values, _, _, hleft, hright⟩
  exact ⟨values, hleft, hright⟩

theorem WF.common_realizes_of_hint
    {leftCtx rightCtx : Context}
    {left : Vector leftCtx.WBool m} {right : Vector rightCtx.WBool m}
    {lv : @WF.Valuation leftCtx} {rv : @WF.Valuation rightCtx}
    {R : Prop} {bodyL : @Hint leftCtx (Vector Bool m)}
    {bodyR : @Hint rightCtx (Vector Bool m)}
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
