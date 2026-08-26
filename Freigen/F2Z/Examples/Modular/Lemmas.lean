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

/-- Strengthen the initial relational assumption of a well-formedness proof.
This small structural rule makes proved gadgets compositional when an outer
type carries more invariants than a callee consumes. -/
theorem WF.Rel.strengthen {Q : WF.Post α} {R S : WF.Assumption}
    {left right : Circuit α} (h : WF.Rel Q R left right)
    (hSR : ∀ lv rv, S lv rv → R lv rv) :
    WF.Rel Q S left right := by
  induction h generalizing S with
  | pure hpost =>
      exact .pure fun lv rv hS => hpost lv rv (hSR lv rv hS)
  | assertR1C ha hb hc _ ih =>
      exact .assertR1C
        (fun lv rv hS => ha lv rv (hSR lv rv hS))
        (fun lv rv hS => hb lv rv (hSR lv rv hS))
        (fun lv rv hS => hc lv rv (hSR lv rv hS))
        (ih hSR)
  | f2z ha _ ih =>
      apply WF.Rel.f2z (fun lv rv hS => ha lv rv (hSR lv rv hS))
      intro outL outR
      apply ih
      intro lv rv hS
      exact ⟨hSR lv rv hS.1, hS.2.1, hS.2.2⟩
  | hint hargs hbody _ ih =>
      apply WF.Rel.hint
        (fun lv rv hS => hargs lv rv (hSR lv rv hS))
        (fun lv rv hS => hbody lv rv (hSR lv rv hS))
      intro outL outR
      apply ih
      intro lv rv hS
      exact ⟨hSR lv rv hS.1, hS.2⟩

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

theorem ZeroTestZModSpec.value_eq_if {x : Rep p} {z : LC ℤ}
    (h : ZeroTestZModSpec p ρ x z) :
    z.eval ρ.int = if evalZMod p x ρ = 0 then 1 else 0 := h.2.2

end Lazy

namespace Aux

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

theorem WF.lowWord_lceq_of_common_realizes
    {left right : Vector (LC Bool) (2 * n)} {lv rv : WF.Valuation}
    (h : ∃ values : Vector Bool (2 * n),
      WF.RealizesBools lv.bool left values ∧
      WF.RealizesBools rv.bool right values)
    (i : Fin n) :
    WF.LCEq lv.bool rv.bool
      ({ bitsLE := Vector.ofFn fun j => left[j.val]'(by omega) } : Word n)[i]
      ({ bitsLE := Vector.ofFn fun j => right[j.val]'(by omega) } : Word n)[i] := by
  unfold WF.LCEq
  change LC.eval lv.bool (Vector.ofFn fun j : Fin n => left[j.val]'(by omega))[i] =
    LC.eval rv.bool (Vector.ofFn fun j : Fin n => right[j.val]'(by omega))[i]
  have hleft :
      (Vector.ofFn fun j : Fin n => left[j.val]'(by omega))[i] = left[i.val] := by
    change (Vector.ofFn fun j : Fin n => left[j.val]'(by omega)).get i = _
    simp
  have hright :
      (Vector.ofFn fun j : Fin n => right[j.val]'(by omega))[i] = right[i.val] := by
    change (Vector.ofFn fun j : Fin n => right[j.val]'(by omega)).get i = _
    simp
  rw [hleft, hright]
  exact WF.lceq_of_common_realizes h i.val (by omega)

theorem WF.highWord_lceq_of_common_realizes
    {left right : Vector (LC Bool) (2 * n)} {lv rv : WF.Valuation}
    (h : ∃ values : Vector Bool (2 * n),
      WF.RealizesBools lv.bool left values ∧
      WF.RealizesBools rv.bool right values)
    (i : Fin n) :
    WF.LCEq lv.bool rv.bool
      ({ bitsLE := Vector.ofFn fun j => left[n + j.val]'(by omega) } : Word n)[i]
      ({ bitsLE := Vector.ofFn fun j => right[n + j.val]'(by omega) } : Word n)[i] := by
  unfold WF.LCEq
  change LC.eval lv.bool
      (Vector.ofFn fun j : Fin n => left[n + j.val]'(by omega))[i] =
    LC.eval rv.bool
      (Vector.ofFn fun j : Fin n => right[n + j.val]'(by omega))[i]
  have hleft :
      (Vector.ofFn fun j : Fin n => left[n + j.val]'(by omega))[i] =
        left[n + i.val] := by
    change (Vector.ofFn fun j : Fin n => left[n + j.val]'(by omega)).get i = _
    simp
  have hright :
      (Vector.ofFn fun j : Fin n => right[n + j.val]'(by omega))[i] =
        right[n + i.val] := by
    change (Vector.ofFn fun j : Fin n => right[n + j.val]'(by omega)).get i = _
    simp
  rw [hleft, hright]
  exact WF.lceq_of_common_realizes h (n + i.val) (by omega)

theorem divRemSpec_of_rel {x y : LC ℤ} {r q : U n}
    (hr : U.Rel ρ r rv) (hq : U.Rel ρ q qv)
    (hlt : r.intVal.eval ρ.int < p.modulus)
    (heq : x.eval ρ.int * y.eval ρ.int =
      (r.intVal + p.modulus • q.intVal).eval ρ.int) :
    DivRemSpec p ρ x y (r, q) := by
  exact ⟨hr.1, hq.1, hlt, by
    simpa only [LC.eval_add, LC.eval_nsmul, nsmul_eq_mul] using heq⟩
theorem mulSpec_of_divRem {x y : Elem p} {r q : U n}
    (hx : x.Valid ρ) (hy : y.Valid ρ)
    (hdiv : DivRemSpec p ρ x.val.intVal y.val.intVal (r, q))
    (hrlt : r.intVal.eval ρ.int < p.modulus) :
    MulSpec p ρ x y ⟨r⟩ := by
  have hrValid : (⟨r⟩ : Elem p).Valid ρ := ⟨hdiv.1, hrlt⟩
  refine ⟨hrValid, ?_⟩
  have hq0 := U.intVal_nonneg q hdiv.2.1
  have hr0 := U.intVal_nonneg r hdiv.1
  have hnat : x.evalNat ρ * y.evalNat ρ =
      (r.intVal.eval ρ.int).toNat +
        p.modulus * (q.intVal.eval ρ.int).toNat := by
    have heq := hdiv.2.2.2
    rw [← Elem.evalNat_cast (p := p) hx,
      ← Elem.evalNat_cast (p := p) hy] at heq
    have heq' : (x.evalNat ρ * y.evalNat ρ : Int) =
        ((r.intVal.eval ρ.int).toNat +
          p.modulus * (q.intVal.eval ρ.int).toNat : Nat) := by
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      rw [Int.toNat_of_nonneg hr0, Int.toNat_of_nonneg hq0]
      exact heq
    exact_mod_cast heq'
  have hmod : x.evalNat ρ * y.evalNat ρ ≡
      (r.intVal.eval ρ.int).toNat [MOD p.modulus] := by
    rw [Nat.ModEq]
    simp [hnat, Nat.add_mod]
  have hrNatLt : (r.intVal.eval ρ.int).toNat < p.modulus :=
    (Int.toNat_lt hr0).2 hrlt
  unfold Elem.evalNat
  exact (Nat.mod_eq_of_modEq hmod hrNatLt).symm
theorem reduceSpec_of_divRem {x : LC ℤ} {r q : U n}
    (hx0 : 0 ≤ x.eval ρ.int)
    (hdiv : DivRemSpec p ρ x (LC.ofConst 1) (r, q)) :
    ReduceSpec p ρ x ⟨r⟩ := by
  have hr0 := U.intVal_nonneg r hdiv.1
  have hq0 := U.intVal_nonneg q hdiv.2.1
  have hnat : (x.eval ρ.int).toNat =
      (r.intVal.eval ρ.int).toNat +
        p.modulus * (q.intVal.eval ρ.int).toNat := by
    have heq := hdiv.2.2.2
    simp only [LC.eval_ofConst, mul_one] at heq
    have heq' : ((x.eval ρ.int).toNat : Int) =
        ((r.intVal.eval ρ.int).toNat +
          p.modulus * (q.intVal.eval ρ.int).toNat : Nat) := by
      simp only [Nat.cast_add, Nat.cast_mul]
      rw [Int.toNat_of_nonneg hx0, Int.toNat_of_nonneg hr0,
        Int.toNat_of_nonneg hq0]
      exact heq
    exact_mod_cast heq'
  have hmod : (x.eval ρ.int).toNat ≡
      (r.intVal.eval ρ.int).toNat [MOD p.modulus] := by
    rw [Nat.ModEq]
    simp [hnat, Nat.add_mod]
  have hrlt : (r.intVal.eval ρ.int).toNat < p.modulus :=
    (Int.toNat_lt hr0).2 hdiv.2.2.1
  exact ⟨⟨hdiv.1, hdiv.2.2.1⟩,
    (Nat.mod_eq_of_modEq hmod hrlt).symm⟩

theorem addQuotientFits {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ((x.val.intVal + y.val.intVal).eval ρ.int).toNat /
      p.modulus < 2 ^ n := by
  have hx0 := Elem.nonneg (p := p) hx
  have hy0 := Elem.nonneg (p := p) hy
  have hxlt := hx.2
  have hylt := hy.2
  simp only [LC.eval_add, Int.toNat_add hx0 hy0]
  by_cases hm : p.modulus = 1
  · have hxz : x.val.intVal.eval ρ.int = 0 := by omega
    have hyz : y.val.intVal.eval ρ.int = 0 := by omega
    simp [hxz, hyz]
  · have hm2 : 2 ≤ p.modulus := by omega
    have hprod :
        (x.val.intVal.eval ρ.int).toNat +
          (y.val.intVal.eval ρ.int).toNat < p.modulus * p.modulus := by
      have hxn := (Int.toNat_lt hx0).2 hxlt
      have hyn := (Int.toNat_lt hy0).2 hylt
      nlinarith
    exact (Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hprod)).trans_le
      p.fits

theorem subDividend_nonneg {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    0 ≤ (x.val.intVal + LC.ofConst (p.modulus : Int) - y.val.intVal).eval ρ.int := by
  simp only [LC.eval_sub, LC.eval_add, LC.eval_ofConst]
  have hx0 := Elem.nonneg (p := p) hx
  have hylt := hy.2
  omega

theorem subDividend_toNat {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ((x.val.intVal + LC.ofConst (p.modulus : Int) - y.val.intVal).eval ρ.int).toNat =
      x.evalNat ρ + p.modulus - y.evalNat ρ := by
  have hnonneg := subDividend_nonneg p hx hy
  apply Int.ofNat_inj.mp
  rw [Int.toNat_of_nonneg hnonneg]
  simp only [LC.eval_sub, LC.eval_add, LC.eval_ofConst]
  rw [Nat.cast_sub]
  · simp only [Nat.cast_add]
    rw [Elem.evalNat_cast (p := p) hx, Elem.evalNat_cast (p := p) hy]
  · exact (Elem.evalNat_lt (p := p) hy).le.trans
      (Nat.le_add_left p.modulus (x.evalNat ρ))

theorem subQuotientFits {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ((x.val.intVal + LC.ofConst (p.modulus : Int) - y.val.intVal).eval ρ.int).toNat /
      p.modulus < 2 ^ n := by
  rw [subDividend_toNat p hx hy]
  by_cases hm : p.modulus = 1
  · have hxz : x.evalNat ρ = 0 := by
      have := Elem.evalNat_lt (p := p) hx
      omega
    have hyz : y.evalNat ρ = 0 := by
      have := Elem.evalNat_lt (p := p) hy
      omega
    have hn : n ≠ 0 := Nat.ne_of_gt p.bitsPositive
    simp [hm, hxz, hyz, hn]
  · have hp := p.positive
    have hm2 : 2 ≤ p.modulus := by omega
    have hnum : x.evalNat ρ + p.modulus - y.evalNat ρ <
        p.modulus * p.modulus := by
      have hxlt := Elem.evalNat_lt (p := p) hx
      nlinarith [Nat.sub_le (x.evalNat ρ + p.modulus) (y.evalNat ρ)]
    exact (Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hnum)).trans_le
      p.fits

end Aux

end Freigen.F2Z.Examples.Modular
