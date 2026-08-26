import Freigen.F2Z.Examples.Modular.Lemmas

/-!
# Correctness of bounded modular arithmetic gadgets

The circuit implementations and their specifications are defined in
`Modular.Impl`; supporting proof lemmas are isolated in `Modular.Lemmas`.
This module exposes the main soundness, completeness, and well-formedness
results.
-/

namespace Freigen.F2Z.Examples.Modular

open Std.Do
open scoped Std.Do

variable {n : Nat} (p : Params n)

@[spec] theorem assertLt_sound {bound : Nat} {x : U n}
    (hvalid : x.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (assertLt (n := n) bound x)
    ⦃⇓ _ => ⌜x.intVal.eval ρ.int < bound⌝⦄ := by
  unfold assertLt
  rw [Sound.interp_bind]
  apply Triple.bind
    (Q := fun slack => ⌜slack.Valid ρ ∧
      slack.intVal.eval ρ.int =
        (LC.ofConst ((bound : Int) - 1) - x.intVal).eval ρ.int⌝)
  case hx => exact U.fromInt_sound
  case hf =>
    intro slack
    mvcgen
    rename_i hslack
    have hnonneg := U.intVal_nonneg slack hslack.1
    simp only [LC.eval_sub, LC.eval_ofConst] at hslack
    omega

@[spec] theorem assertLt_complete {bound : Nat} {x : U n}
    (hvalid : x.Valid ρ) (hbound : bound ≤ 2 ^ n)
    (hlt : x.intVal.eval ρ.int < bound) :
    ⦃⌜True⌝⦄ Complete.interp ρ (assertLt (n := n) bound x)
    ⦃⇓ _ => ⌜x.intVal.eval ρ.int < bound⌝⦄ := by
  unfold assertLt
  rw [Complete.interp_bind]
  apply Triple.bind
    (Q := fun slack => ⌜slack.Valid ρ ∧
      slack.intVal.eval ρ.int =
        (LC.ofConst ((bound : Int) - 1) - x.intVal).eval ρ.int⌝)
  case hx =>
    apply U.fromInt_complete
    · simp only [LC.eval_sub, LC.eval_ofConst]
      have hx0 := U.intVal_nonneg x hvalid
      omega
    · simp only [LC.eval_sub, LC.eval_ofConst]
      have hx0 := U.intVal_nonneg x hvalid
      have hb : (bound : Int) ≤ (2 ^ n : Nat) := by exact_mod_cast hbound
      rw [show (2 : Int) ^ n = ((2 ^ n : Nat) : Int) by norm_num]
      omega
  case hf =>
    intro slack
    mvcgen

theorem assertLt_wf :
    WF.GadgetSpec
      (fun lv rv (l r : U n) => U.WFRel lv rv l r)
      (assertLt (n := n) bound)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec assertLt
  intro left right
  wfgen' using [U.fromInt_wf_full]
@[spec] theorem ofU_sound {x : U n} (hx : x.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (ofU p x)
    ⦃⇓ out => ⌜out.Valid ρ ∧ out.val = x⌝⦄ := by
  mvcgen [ofU, Elem.Valid]

@[spec] theorem ofU_complete {x : U n} (hx : x.Valid ρ)
    (hlt : x.intVal.eval ρ.int < p.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ (ofU p x)
    ⦃⇓ out => ⌜out.Valid ρ ∧ out.val = x⌝⦄ := by
  mvcgen [ofU, Elem.Valid]
  case hbound => exact p.fits

theorem ofU_wf :
    WF.GadgetSpec U.WFRel (ofU p) (Elem.WFRel (p := p)) := by
  wfgen' using [assertLt_wf] unfold [ofU, Elem.WFRel]
@[spec] theorem divRemHint_sound {x y : LC ℤ} :
    ⦃⌜True⌝⦄ Sound.interp ρ (divRemHint p x y)
    ⦃⇓ out => ⌜DivRemSpec p ρ x y out⌝⦄ := by
  mvcgen [divRemHint]
  intro bits
  mvcgen [DivRemSpec]
  all_goals first
    | assumption
    | grind [U.Rel]
    | (apply Aux.divRemSpec_of_rel p <;> assumption)

@[spec] theorem divRemHint_complete {x y : LC ℤ}
    (hx0 : 0 ≤ x.eval ρ.int) (hy0 : 0 ≤ y.eval ρ.int)
    (hqBound : (x.eval ρ.int).toNat * (y.eval ρ.int).toNat /
      p.modulus < 2 ^ n) :
    ⦃⌜True⌝⦄ Complete.interp ρ (divRemHint p x y)
    ⦃⇓ out => ⌜DivRemSpec p ρ x y out⌝⦄ := by
  mvcgen [divRemHint]
  let a := (x.eval ρ.int).toNat
  let b := (y.eval ρ.int).toNat
  let bits : Vector Bool (2 * n) := Vector.ofFn fun i =>
    if hi : i.val < n then (a * b % p.modulus).testBit i.val
    else (a * b / p.modulus).testBit (i.val - n)
  refine ⟨bits, ?_, ?_⟩
  · simp [WF.evalArgs, WF.interpHint, hx0, hy0, bits, a, b]
  · mvcgen [DivRemSpec]
    rename_i r hr q hq
    have hrFit : a * b % p.modulus < 2 ^ n :=
      (Nat.mod_lt _ p.positive).trans_le p.fits
    have hqFit : a * b / p.modulus < 2 ^ n := hqBound
    have rWord :
        (Word.eval ρ.bool {
          bitsLE := Vector.ofFn (n := n) fun i =>
            (Vector.map LC.ofConst bits)[i.val]'(by omega)
        }).toNat = a * b % p.modulus := by
      simp [Word.eval, BitVec.toNat_ofFnLE, bits, Nat.ofBits_testBit,
        Nat.mod_eq_of_lt hrFit]
    have qWord :
        (Word.eval ρ.bool {
          bitsLE := Vector.ofFn (n := n) fun i =>
            (Vector.map LC.ofConst bits)[n + i.val]'(by omega)
        }).toNat = a * b / p.modulus := by
      simp [Word.eval, BitVec.toNat_ofFnLE, bits,
        show ∀ i : Fin n, ¬n + i.val < n by omega,
        Nat.ofBits_testBit, Nat.mod_eq_of_lt hqFit]
    have hrVal : r.intVal.eval ρ.int = (a * b % p.modulus : Nat) := by
      rw [U.Rel.intVal hr, rWord]
    have hqVal : q.intVal.eval ρ.int = (a * b / p.modulus : Nat) := by
      rw [U.Rel.intVal hq, qWord]
    have hxVal : x.eval ρ.int = (a : Nat) := by
      exact (Int.toNat_of_nonneg hx0).symm
    have hyVal : y.eval ρ.int = (b : Nat) := by
      exact (Int.toNat_of_nonneg hy0).symm
    constructor
    · simp only [LC.eval_add, LC.eval_nsmul, nsmul_eq_mul,
        hxVal, hyVal, hrVal, hqVal]
      exact_mod_cast (Nat.mod_add_div (a * b) p.modulus).symm
    · mvcgen
      · exact hr.1
      · exact p.fits
      · rw [hrVal]
        exact_mod_cast Nat.mod_lt (a * b) p.positive
      · exact ⟨hr.1, hq.1, by
          rw [hrVal]
          exact_mod_cast Nat.mod_lt (a * b) p.positive, by
          simp only [hxVal, hyVal, hrVal, hqVal]
          exact_mod_cast (Nat.mod_add_div (a * b) p.modulus).symm⟩

theorem divRemHint_wf :
    WF.GadgetSpec
      (fun lv rv (l r : LC ℤ × LC ℤ) =>
        WF.LCEq lv.int rv.int l.1 r.1 ∧
        WF.LCEq lv.int rv.int l.2 r.2)
      (fun x => divRemHint p x.1 x.2)
      (fun lv rv l r =>
        U.WFRel lv rv l.1 r.1 ∧ U.WFRel lv rv l.2 r.2) := by
  wfgen' using [U.fromWord_wf_rel, assertLt_wf] unfold [divRemHint]
  case vc1 =>
    simp_all [WF.LCEq, U.WFRel, Word.WFRel, WF.ArgsEq,
      WF.RealizesBools, WF.evalArgs, LC.eval_add, LC.eval_nsmul]
    grind
  case vc2 outBitsL outBitsR B =>
    rename_i qL qR
    apply Aux.WF.highWord_lceq_of_common_realizes
    have hp := outBitsR leftVal rightVal B
    exact Aux.WF.common_realizes_of_hint hp.1
  case vc3 =>
    rename_i h
    apply Aux.WF.lowWord_lceq_of_common_realizes
    exact Aux.WF.common_realizes_of_hint h
  case vc4 =>
    simp_all [WF.LCEq, WF.evalArgs]
  case vc5 =>
    simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]
@[spec] theorem mul_sound {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (mul p x y)
    ⦃⇓ out => ⌜MulSpec p ρ x y out⌝⦄ := by
  unfold mul
  mvcgen
  rename_i rq hdiv
  exact Aux.mulSpec_of_divRem p hx hy hdiv hdiv.2.2.1

@[spec] theorem mul_complete {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (mul p x y)
    ⦃⇓ out => ⌜MulSpec p ρ x y out⌝⦄ := by
  unfold mul
  mvcgen
  · exact Elem.nonneg (p := p) hx
  · exact Elem.nonneg (p := p) hy
  · have hxn := Elem.evalNat_lt (p := p) hx
    have hyn := Elem.evalNat_lt (p := p) hy
    have hab : x.evalNat ρ * y.evalNat ρ < p.modulus * p.modulus := by
      nlinarith
    exact (Nat.div_lt_of_lt_mul (by
      simpa [Elem.evalNat, Nat.mul_comm] using hab)).trans_le
      p.fits
  · rename_i rq hdiv
    exact Aux.mulSpec_of_divRem p hx hy hdiv hdiv.2.2.1

theorem mul_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Elem p × Elem p) =>
        Elem.WFRel lv rv l.1 r.1 ∧ Elem.WFRel lv rv l.2 r.2)
      (fun x => mul p x.1 x.2)
      (Elem.WFRel (p := p)) := by
  wfgen' using [U.fromWord_wf_rel, assertLt_wf]
    unfold [mul, divRemHint, Elem.WFRel]
  case vc1 =>
    simp_all [WF.LCEq, U.WFRel, Word.WFRel, WF.ArgsEq,
      WF.RealizesBools, WF.evalArgs, LC.eval_add, LC.eval_nsmul]
    grind
  case vc2 outBitsL outBitsR B =>
    rename_i qL qR
    apply Aux.WF.highWord_lceq_of_common_realizes
    have hp := outBitsR leftVal rightVal B
    exact Aux.WF.common_realizes_of_hint hp.1
  case vc3 =>
    rename_i h
    apply Aux.WF.lowWord_lceq_of_common_realizes
    exact Aux.WF.common_realizes_of_hint h
  case vc4 =>
    simp_all [U.WFRel, WF.LCEq, WF.evalArgs]
  case vc5 =>
    simp_all [U.WFRel, WF.LCEq, WF.ArgsEq, WF.evalArgs]
@[spec] theorem reduce_sound {x : LC ℤ} (hx0 : 0 ≤ x.eval ρ.int) :
    ⦃⌜True⌝⦄ Sound.interp ρ (reduce p x)
    ⦃⇓ out => ⌜ReduceSpec p ρ x out⌝⦄ := by
  mvcgen [reduce]
  exact Aux.reduceSpec_of_divRem p hx0 (by assumption)

@[spec] theorem reduce_complete {x : LC ℤ} (hx0 : 0 ≤ x.eval ρ.int)
    (hq : (x.eval ρ.int).toNat / p.modulus < 2 ^ n) :
    ⦃⌜True⌝⦄ Complete.interp ρ (reduce p x)
    ⦃⇓ out => ⌜ReduceSpec p ρ x out⌝⦄ := by
  mvcgen [reduce]
  · simp
  · simpa using hq
  · exact Aux.reduceSpec_of_divRem p hx0 (by assumption)

theorem reduce_wf :
    WF.GadgetSpec
      (fun lv rv (l r : LC ℤ) => WF.LCEq lv.int rv.int l r)
      (reduce p) (Elem.WFRel (p := p)) := by
  wfgen' using [U.fromWord_wf_rel, assertLt_wf]
    unfold [reduce, divRemHint, Elem.WFRel]
  case vc1 =>
    simp_all [WF.LCEq, U.WFRel, WF.RealizesBools, WF.evalArgs,
      LC.eval_add, LC.eval_nsmul]
    grind
  case vc2 outBitsL outBitsR B =>
    rename_i qL qR
    apply Aux.WF.highWord_lceq_of_common_realizes
    have hp := outBitsR leftVal rightVal B
    exact Aux.WF.common_realizes_of_hint hp.1
  case vc3 =>
    rename_i h
    apply Aux.WF.lowWord_lceq_of_common_realizes
    exact Aux.WF.common_realizes_of_hint h
  case vc4 =>
    simp_all [WF.LCEq, WF.evalArgs]
  case vc5 =>
    simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

@[spec] theorem add_sound {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (add p x y)
    ⦃⇓ out => ⌜AddSpec p ρ x y out⌝⦄ := by
  unfold add
  mvcgen
  · simpa only [LC.eval_add] using
      add_nonneg (Elem.nonneg (p := p) hx) (Elem.nonneg (p := p) hy)
  · intro hred
    refine ⟨hred.1, ?_⟩
    rw [hred.2]
    simp only [LC.eval_add, Int.toNat_add
      (Elem.nonneg (p := p) hx) (Elem.nonneg (p := p) hy), Elem.evalNat]

@[spec] theorem add_complete {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (add p x y)
    ⦃⇓ out => ⌜AddSpec p ρ x y out⌝⦄ := by
  unfold add
  mvcgen
  · simpa only [LC.eval_add] using
      add_nonneg (Elem.nonneg (p := p) hx) (Elem.nonneg (p := p) hy)
  · exact Aux.addQuotientFits p hx hy
  · intro hred
    refine ⟨hred.1, ?_⟩
    rw [hred.2]
    simp only [LC.eval_add, Int.toNat_add
      (Elem.nonneg (p := p) hx) (Elem.nonneg (p := p) hy), Elem.evalNat]

theorem add_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Elem p × Elem p) =>
        Elem.WFRel lv rv l.1 r.1 ∧ Elem.WFRel lv rv l.2 r.2)
      (fun x => add p x.1 x.2) (Elem.WFRel (p := p)) := by
  unfold WF.GadgetSpec add
  intro left right
  apply WF.Rel.strengthen
    (reduce_wf p (left.1.val.intVal + left.2.val.intVal)
      (right.1.val.intVal + right.2.val.intVal))
  intro lv rv h
  unfold Elem.WFRel U.WFRel WF.LCEq at h
  unfold WF.LCEq
  simp only [LC.eval_add]
  rw [h.1.1, h.2.1]
@[spec] theorem sub_sound {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (sub p x y)
    ⦃⇓ out => ⌜SubSpec p ρ x y out⌝⦄ := by
  unfold sub
  mvcgen
  · exact Aux.subDividend_nonneg p hx hy
  · intro hred
    exact ⟨hred.1, by rw [hred.2, Aux.subDividend_toNat p hx hy]⟩

@[spec] theorem sub_complete {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (sub p x y)
    ⦃⇓ out => ⌜SubSpec p ρ x y out⌝⦄ := by
  unfold sub
  mvcgen
  · exact Aux.subDividend_nonneg p hx hy
  · exact Aux.subQuotientFits p hx hy
  · intro hred
    exact ⟨hred.1, by rw [hred.2, Aux.subDividend_toNat p hx hy]⟩

theorem sub_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Elem p × Elem p) =>
        Elem.WFRel lv rv l.1 r.1 ∧ Elem.WFRel lv rv l.2 r.2)
      (fun x => sub p x.1 x.2) (Elem.WFRel (p := p)) := by
  unfold WF.GadgetSpec sub
  intro left right
  apply WF.Rel.strengthen
    (reduce_wf p
      (left.1.val.intVal + LC.ofConst (p.modulus : Int) - left.2.val.intVal)
      (right.1.val.intVal + LC.ofConst (p.modulus : Int) - right.2.val.intVal))
  intro lv rv h
  unfold Elem.WFRel U.WFRel WF.LCEq at h
  unfold WF.LCEq
  simp only [LC.eval_sub, LC.eval_add, LC.eval_ofConst]
  rw [h.1.1, h.2.1]
@[spec] theorem select_sound {b : LC ℤ} {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (select p b x y)
    ⦃⇓ out => ⌜SelectSpec p ρ b x y out⌝⦄ := by
  mvcgen [select, SelectSpec]
  intro bits
  mvcgen
  all_goals simp_all [SelectSpec, Elem.Valid, LC.eval_sub, U.Rel]
  all_goals nlinarith

@[spec] theorem select_complete {b : LC ℤ} {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ)
    (hb : b.eval ρ.int = 0 ∨ b.eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Complete.interp ρ (select p b x y)
    ⦃⇓ out => ⌜SelectSpec p ρ b x y out⌝⦄ := by
  mvcgen [select, SelectSpec]
  let chosen := if b.eval ρ.int = 0 then x.evalNat ρ else y.evalNat ρ
  let bits : Vector Bool n := Vector.ofFn fun i => chosen.testBit i
  refine ⟨bits, ?_, ?_⟩
  · rcases hb with hb | hb
    · simp [WF.interpHint, WF.evalArgs, hb, bits, chosen,
        Elem.evalNat, Int.toNat_of_nonneg (Elem.nonneg (p := p) hx)]
    · simp [WF.interpHint, WF.evalArgs, hb, bits, chosen,
        Elem.evalNat, Int.toNat_of_nonneg (Elem.nonneg (p := p) hy)]
  · mvcgen
    rename_i out hout
    have hchosenFit : chosen < 2 ^ n := by
      unfold chosen
      split
      · exact (Elem.evalNat_lt (p := p) hx).trans_le p.fits
      · exact (Elem.evalNat_lt (p := p) hy).trans_le p.fits
    have hword :
        (Word.eval ρ.bool { bitsLE := Vector.map LC.ofConst bits }).toNat =
          chosen := by
      simp [Word.eval, BitVec.toNat_ofFnLE, bits, Nat.ofBits_testBit,
        Nat.mod_eq_of_lt hchosenFit]
    have houtVal : out.intVal.eval ρ.int = (chosen : Nat) := by
      rw [U.Rel.intVal hout, hword]
    constructor
    · rcases hb with hb | hb
      · simp only [LC.eval_sub, hb, zero_mul, houtVal, chosen, if_pos hb]
        rw [← Elem.evalNat_cast (p := p) hx]
        ring
      · simp only [LC.eval_sub, hb, one_mul, houtVal, chosen,
          if_neg (by omega : ¬b.eval ρ.int = 0)]
        rw [← Elem.evalNat_cast (p := p) hx,
          ← Elem.evalNat_cast (p := p) hy]
    · mvcgen
      · exact hout.1
      · exact p.fits
      · rw [houtVal]
        unfold chosen
        split
        · exact_mod_cast Elem.evalNat_lt (p := p) hx
        · exact_mod_cast Elem.evalNat_lt (p := p) hy
      · constructor
        · exact ⟨hout.1, by
            rw [houtVal]
            unfold chosen
            split
            · exact_mod_cast Elem.evalNat_lt (p := p) hx
            · exact_mod_cast Elem.evalNat_lt (p := p) hy⟩
        · rcases hb with hb | hb
          · simp [houtVal, chosen, hb, Elem.evalNat_cast (p := p) hx]
          · simp [houtVal, chosen, hb]
            exact Elem.evalNat_cast (p := p) hy

theorem select_wf :
    WF.GadgetSpec
      (fun lv rv (l r : LC ℤ × Elem p × Elem p) =>
        WF.LCEq lv.int rv.int l.1 r.1 ∧
        Elem.WFRel lv rv l.2.1 r.2.1 ∧
        Elem.WFRel lv rv l.2.2 r.2.2)
      (fun z => select p z.1 z.2.1 z.2.2)
      (Elem.WFRel (p := p)) := by
  wfgen' using [U.fromWord_wf_rel, assertLt_wf]
    unfold [select, Elem.WFRel]
  case vc1 =>
    apply Aux.WF.lceq_of_common_realizes
    exact Aux.WF.common_realizes_of_hint (by assumption)
  case vc2 =>
    simp_all [WF.LCEq, U.WFRel, WF.ArgsEq, WF.evalArgs, LC.eval_sub]
  case vc3 =>
    simp_all [WF.LCEq, U.WFRel, WF.ArgsEq, WF.evalArgs]
@[spec] theorem assertEq_sound {x y : Elem p} :
    ⦃⌜True⌝⦄ Sound.interp ρ (assertEq p x y)
    ⦃⇓ _ => ⌜x.evalNat ρ = y.evalNat ρ⌝⦄ := by
  mvcgen [assertEq]
  intro h
  simp only [LC.eval_zero, zero_mul, LC.eval_sub] at h
  unfold Elem.evalNat
  have he : x.val.intVal.eval ρ.int = y.val.intVal.eval ρ.int := by omega
  rw [he]

@[spec] theorem assertEq_complete {x y : Elem p}
    (heq : x.evalNat ρ = y.evalNat ρ)
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (assertEq p x y)
    ⦃⇓ _ => ⌜x.evalNat ρ = y.evalNat ρ⌝⦄ := by
  have hz : x.val.intVal.eval ρ.int - y.val.intVal.eval ρ.int = 0 := by
    rw [← Elem.evalNat_cast (p := p) hx,
      ← Elem.evalNat_cast (p := p) hy, heq]
    simp
  mvcgen [assertEq]
  constructor
  · simpa only [LC.eval_zero, zero_mul, LC.eval_sub] using hz.symm
  · exact heq

theorem assertEq_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Elem p × Elem p) =>
        Elem.WFRel lv rv l.1 r.1 ∧ Elem.WFRel lv rv l.2 r.2)
      (fun z => assertEq p z.1 z.2) (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold assertEq
  apply WF.Rel.assertR1C_pure
  · simp [WF.LCEq]
  · simp [WF.LCEq]
  · intro lv rv h
    unfold Elem.WFRel U.WFRel at h
    unfold WF.LCEq at h ⊢
    simp only [LC.eval_sub]
    rw [h.1.1, h.2.1]
  · intro _ _ _
    trivial
@[spec] theorem checkedInv_sound {one x candidate : Elem p}
    (hone : one.Valid ρ) (hx : x.Valid ρ) (hc : candidate.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (checkedInv p one x candidate)
    ⦃⇓ out => ⌜InvSpec p ρ one x out⌝⦄ := by
  mvcgen [checkedInv, InvSpec]
  all_goals simp_all [MulSpec, InvSpec]

@[spec] theorem checkedInv_complete {one x candidate : Elem p}
    (hone : one.Valid ρ) (hx : x.Valid ρ) (hc : candidate.Valid ρ)
    (hinv : (x.evalNat ρ * candidate.evalNat ρ) % p.modulus =
      one.evalNat ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (checkedInv p one x candidate)
    ⦃⇓ out => ⌜InvSpec p ρ one x out⌝⦄ := by
  mvcgen [checkedInv, InvSpec]
  all_goals simp_all [MulSpec, InvSpec]

theorem checkedInv_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Elem p × Elem p × Elem p) =>
        Elem.WFRel lv rv l.1 r.1 ∧
        Elem.WFRel lv rv l.2.1 r.2.1 ∧ Elem.WFRel lv rv l.2.2 r.2.2)
      (fun z => checkedInv p z.1 z.2.1 z.2.2)
      (Elem.WFRel (p := p)) := by
  unfold WF.GadgetSpec
  intro left right
  unfold checkedInv
  apply WF.GadgetSpec.bind_rule (mul_wf p)
  · intro lv rv h
    exact ⟨h.2.1, h.2.2⟩
  · intro A productL productR hproduct
    unfold assertEq
    apply WF.Rel.assertR1C
    · intro _ _ _
      rfl
    · intro _ _ _
      rfl
    · intro lv rv hA
      have h := hproduct lv rv hA
      exact WF.eval_sub h.2.1 h.1.1.1
    · apply WF.Rel.pure
      intro lv rv hA
      exact (hproduct lv rv hA).1.2.2

namespace Relaxed

theorem reduceSmall_wf {n : Nat} (p : Params n) :
    WF.GadgetSpec
      (fun lv rv (left right : LC ℤ) => WF.LCEq lv.int rv.int left right)
      (reduceSmall p) (Elem.WFRel (p := p)) := by
  wfgen' using [U.fromWord_wf_rel]
    unfold [reduceSmall, Elem.WFRel]
  case vc1 =>
    rename_i hpost hB
    exact Aux.WF.wordSlice_lceq_of_common_realizes
      (Aux.WF.common_realizes_of_post (hpost leftVal rightVal hB))
      n 2 (by omega) i
  case vc2 =>
    rename_i h
    simpa only [zero_add] using
      Aux.WF.wordSlice_lceq_of_common_realizes
        (Aux.WF.common_realizes_of_hint h) 0 n (by omega) i
  case vc3 =>
    rename_i h
    unfold WF.LCEq at h
    simp [WF.evalArgs, h]
  case vc4 =>
    rename_i h
    unfold WF.LCEq at h
    simp [WF.ArgsEq, WF.evalArgs, h]

theorem mul_wf {n : Nat} (p : Params n) :
    WF.GadgetSpec
      (fun lv rv (left right : Elem p × Elem p) =>
        Elem.WFRel lv rv left.1 right.1 ∧
        Elem.WFRel lv rv left.2 right.2)
      (fun input => mul p input.1 input.2) (Elem.WFRel (p := p)) := by
  wfgen' using [U.fromWord_wf_rel] unfold [mul, Elem.WFRel]
  case vc1 =>
    simp_all [WF.LCEq, U.WFRel, WF.RealizesBools, WF.evalArgs,
      LC.eval_add, LC.eval_nsmul]
    grind
  case vc2 outBitsL outBitsR B =>
    rename_i qL qR
    have hp := outBitsR leftVal rightVal B
    apply Aux.WF.wordSlice_lceq_of_common_realizes
    · exact Aux.WF.common_realizes_of_hint hp.1
    · omega
  case vc3 =>
    rename_i h
    simpa only [zero_add] using
      Aux.WF.wordSlice_lceq_of_common_realizes
        (Aux.WF.common_realizes_of_hint h) 0 n (by omega) i
  all_goals simp_all [U.WFRel, WF.LCEq, WF.ArgsEq, WF.evalArgs]

@[spec] theorem mul_sound_zmod {x y : Elem p} :
    ⦃⌜True⌝⦄ Sound.interp ρ (mul p x y)
    ⦃⇓ out => ⌜out.val.Valid ρ ∧
      Lazy.evalElemZMod p out ρ =
        Lazy.evalElemZMod p x ρ * Lazy.evalElemZMod p y ρ⌝⦄ := by
  mvcgen [mul, Lazy.evalElemZMod]
  intro bits
  mvcgen
  rename_i r hr q hq heq
  refine ⟨hr.1, ?_⟩
  have hcast := congrArg (fun z : Int => (z : ZMod p.modulus)) heq
  simp only [LC.eval_add, LC.eval_nsmul, nsmul_eq_mul, Int.cast_mul,
    Int.cast_add, Int.cast_natCast, ZMod.natCast_self, zero_mul,
    add_zero] at hcast
  exact hcast.symm

@[spec] theorem mul_complete_zmod {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (mul p x y)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      Lazy.evalElemZMod p out ρ =
        Lazy.evalElemZMod p x ρ * Lazy.evalElemZMod p y ρ⌝⦄ := by
  mvcgen [mul]
  let a := x.val.intVal.eval ρ.int
  let b := y.val.intVal.eval ρ.int
  let value := a.toNat * b.toNat
  let bits : Vector Bool (2 * n + 2) := Vector.ofFn fun i =>
    if hi : i.val < n then (value % p.modulus).testBit i.val
    else (value / p.modulus).testBit (i.val - n)
  refine ⟨bits, ?_, ?_⟩
  · simp [WF.interpHint, WF.evalArgs, Modular.Elem.nonneg p hx,
      Modular.Elem.nonneg p hy, bits, value, a, b]
  · mvcgen
    rename_i r hr q hq
    have hrFit : value % p.modulus < 2 ^ n :=
      (Nat.mod_lt _ p.positive).trans_le p.fits
    have haVal : a.toNat = x.evalNat ρ := by rfl
    have hbVal : b.toNat = y.evalNat ρ := by rfl
    have hab : value < p.modulus * p.modulus := by
      dsimp [value]
      rw [haVal, hbVal]
      nlinarith [Modular.Elem.evalNat_lt p hx,
        Modular.Elem.evalNat_lt p hy]
    have hqSmall : value / p.modulus < p.modulus := by
      apply Nat.div_lt_of_lt_mul
      simpa [Nat.mul_comm] using hab
    have hqFit : value / p.modulus < 2 ^ (n + 2) :=
      hqSmall.trans_le (p.fits.trans
        (Nat.pow_le_pow_right (by omega) (by omega)))
    have hrWord :
        (Word.eval ρ.bool {
          bitsLE := Vector.ofFn (n := n) fun i =>
            (Vector.map LC.ofConst bits)[i.val]'(by omega)
        }).toNat = value % p.modulus := by
      simp [Word.eval, BitVec.toNat_ofFnLE, bits, Nat.ofBits_testBit,
        Nat.mod_eq_of_lt hrFit]
    have hqWord :
        (Word.eval ρ.bool {
          bitsLE := Vector.ofFn (n := n + 2) fun i =>
            (Vector.map LC.ofConst bits)[n + i.val]'(by omega)
        }).toNat = value / p.modulus := by
      simp [Word.eval, BitVec.toNat_ofFnLE, bits,
        show ∀ i : Fin (n + 2), ¬ n + i.val < n by omega,
        Nat.ofBits_testBit, Nat.mod_eq_of_lt hqFit]
    have hrVal : r.intVal.eval ρ.int = (value % p.modulus : Nat) := by
      rw [U.Rel.intVal hr, hrWord]
    have hqVal : q.intVal.eval ρ.int = (value / p.modulus : Nat) := by
      rw [U.Rel.intVal hq, hqWord]
    have haInt : (a.toNat : Int) = a :=
      Int.toNat_of_nonneg (Modular.Elem.nonneg p hx)
    have hbInt : (b.toNat : Int) = b :=
      Int.toNat_of_nonneg (Modular.Elem.nonneg p hy)
    constructor
    · simp only [LC.eval_add, LC.eval_nsmul, nsmul_eq_mul,
        hrVal, hqVal]
      change a * b = _
      rw [← haInt, ← hbInt]
      exact_mod_cast (Nat.mod_add_div value p.modulus).symm
    · mvcgen
      refine ⟨⟨hr.1, ?_⟩, ?_⟩
      · rw [hrVal]
        exact_mod_cast Nat.mod_lt value p.positive
      unfold Lazy.evalElemZMod
      have heq : a * b =
          (value % p.modulus : Nat) +
            p.modulus * (value / p.modulus) := by
        rw [← haInt, ← hbInt]
        exact_mod_cast (Nat.mod_add_div value p.modulus).symm
      have hcast := congrArg (fun z : Int => (z : ZMod p.modulus)) heq
      simpa [hrVal, value, a, b] using hcast.symm

@[spec] theorem reduceSmall_sound_zmod {x : LC ℤ} :
    ⦃⌜True⌝⦄ Sound.interp ρ (reduceSmall p x)
    ⦃⇓ out => ⌜out.val.Valid ρ ∧
      Lazy.evalElemZMod p out ρ =
        Int.castRingHom (ZMod p.modulus) (x.eval ρ.int)⌝⦄ := by
  mvcgen [reduceSmall, Lazy.evalElemZMod]
  intro bits
  mvcgen
  rename_i r hr q hq heq
  refine ⟨hr.1, ?_⟩
  have hcast := congrArg (fun z : Int => (z : ZMod p.modulus)) heq
  simp only [LC.eval_zero, LC.eval_sub, LC.eval_add, LC.eval_nsmul, nsmul_eq_mul,
    Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_self, zero_mul, add_zero] at hcast
  unfold Lazy.evalElemZMod
  exact (sub_eq_zero.mp (by simpa using hcast.symm)).symm

@[spec] theorem reduceSmall_complete_zmod {x : LC ℤ}
    (hx0 : 0 ≤ x.eval ρ.int)
    (hxBound : x.eval ρ.int < 4 * p.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ (reduceSmall p x)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      Lazy.evalElemZMod p out ρ =
        Int.castRingHom (ZMod p.modulus) (x.eval ρ.int)⌝⦄ := by
  mvcgen [reduceSmall]
  let a := x.eval ρ.int
  let bits : Vector Bool (n + 2) := Vector.ofFn fun i =>
    if hi : i.val < n then (a.toNat % p.modulus).testBit i.val
    else (a.toNat / p.modulus).testBit (i.val - n)
  refine ⟨bits, ?_, ?_⟩
  · simp [WF.interpHint, WF.evalArgs, hx0, bits, a]
  · mvcgen
    rename_i r hr q hq
    have hrFit : a.toNat % p.modulus < 2 ^ n :=
      (Nat.mod_lt _ p.positive).trans_le p.fits
    have haVal : (a.toNat : Int) = a := Int.toNat_of_nonneg hx0
    have haBound : a.toNat < 4 * p.modulus := by
      exact (Int.toNat_lt hx0).2 hxBound
    have hqFit : a.toNat / p.modulus < 2 ^ 2 := by
      norm_num
      exact (Nat.div_lt_iff_lt_mul p.positive).2 (by
        simpa [Nat.mul_comm] using haBound)
    have hqFit4 : a.toNat / p.modulus < 4 := by simpa using hqFit
    have hrWord :
        (Word.eval ρ.bool {
          bitsLE := Vector.ofFn (n := n) fun i =>
            (Vector.map LC.ofConst bits)[i.val]'(by omega)
        }).toNat = a.toNat % p.modulus := by
      simp [Word.eval, BitVec.toNat_ofFnLE, bits, Nat.ofBits_testBit,
        Nat.mod_eq_of_lt hrFit]
    have hqWord :
        (Word.eval ρ.bool {
          bitsLE := Vector.ofFn (n := 2) fun i =>
            (Vector.map LC.ofConst bits)[n + i.val]'(by omega)
        }).toNat = a.toNat / p.modulus := by
      simp [Word.eval, BitVec.toNat_ofFnLE, bits,
        show ∀ i : Fin 2, ¬ n + i.val < n by omega,
        Nat.ofBits_testBit, Nat.mod_eq_of_lt hqFit4]
    have hrVal : r.intVal.eval ρ.int = (a.toNat % p.modulus : Nat) := by
      rw [U.Rel.intVal hr, hrWord]
    have hqVal : q.intVal.eval ρ.int = (a.toNat / p.modulus : Nat) := by
      rw [U.Rel.intVal hq, hqWord]
    constructor
    · simp only [LC.eval_zero, zero_mul, LC.eval_sub, LC.eval_add,
        LC.eval_nsmul, nsmul_eq_mul, hrVal, hqVal]
      apply Eq.symm
      apply sub_eq_zero.mpr
      change a = _
      rw [← haVal]
      exact_mod_cast (Nat.mod_add_div a.toNat p.modulus).symm
    · mvcgen
      refine ⟨⟨hr.1, ?_⟩, ?_⟩
      · rw [hrVal]
        exact_mod_cast Nat.mod_lt a.toNat p.positive
      unfold Lazy.evalElemZMod
      have heq : a = (a.toNat % p.modulus : Nat) +
          p.modulus * (a.toNat / p.modulus) := by
        rw [← haVal]
        exact_mod_cast (Nat.mod_add_div a.toNat p.modulus).symm
      have hcast := congrArg (fun z : Int => (z : ZMod p.modulus)) heq
      simpa [hrVal, a] using hcast.symm

end Relaxed

namespace Lazy

theorem mul_wf {n : Nat} (p : Params n) :
    WF.GadgetSpec
      (fun lv rv (left right : Rep p × Rep p) =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2)
      (fun input => mul p input.1 input.2) Rep.WFRel := by
  wfgen' using [U.fromWord_wf_rel] unfold [mul, Rep.WFRel]
  case vc1 =>
    simp_all [WF.LCEq, U.WFRel, WF.RealizesBools, WF.evalArgs,
      LC.eval_add, LC.eval_nsmul]
    grind
  case vc2 outBitsL outBitsR B =>
    rename_i qL qR
    have hp := outBitsR leftVal rightVal B
    apply Aux.WF.wordSlice_lceq_of_common_realizes
    · exact Aux.WF.common_realizes_of_hint hp.1
    · omega
  case vc3 =>
    rename_i h
    simpa only [zero_add] using
      Aux.WF.wordSlice_lceq_of_common_realizes
        (Aux.WF.common_realizes_of_hint h) 0 n (by omega) i
  all_goals simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

theorem reduce_wf {n : Nat} (p : Params n) :
    WF.GadgetSpec Rep.WFRel (reduce p) (Elem.WFRel (p := p)) := by
  wfgen' using [U.fromWord_wf_rel, Modular.ofU_wf]
    unfold [reduce, Rep.WFRel, Elem.WFRel]
  case vc1 =>
    rename_i outBitsL outBitsR B0 rL rR hR
    apply WF.GadgetSpec.direct_rule (Modular.ofU_wf p)
    intro lv rv hB
    exact (rR lv rv (hR lv rv hB).1).2
  case vc2 outBitsL outBitsR B =>
    rename_i qL qR
    have hp := outBitsR leftVal rightVal B
    apply Aux.WF.wordSlice_lceq_of_common_realizes
    · exact Aux.WF.common_realizes_of_hint hp.1
    · omega
  case vc3 =>
    rename_i h
    simpa only [zero_add] using
      Aux.WF.wordSlice_lceq_of_common_realizes
        (Aux.WF.common_realizes_of_hint h) 0 n (by omega) i
  all_goals simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

theorem mulSubToElem_wf {n : Nat} (p : Params n) :
    WF.GadgetSpec
      (fun lv rv (left right : Rep p × Rep p × Rep p) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => mulSubToElem p input.1 input.2.1 input.2.2)
      (Elem.WFRel (p := p)) := by
  wfgen' using [U.fromWord_wf_rel]
    unfold [mulSubToElem, Rep.WFRel, Elem.WFRel]
  case vc1 =>
    simp_all [WF.LCEq, U.WFRel, WF.RealizesBools, WF.evalArgs]
    grind
  case vc2 outBitsL outBitsR B =>
    rename_i qL qR
    have hp := outBitsR leftVal rightVal B
    apply Aux.WF.wordSlice_lceq_of_common_realizes
    · exact Aux.WF.common_realizes_of_hint hp.1
    · omega
  case vc3 =>
    rename_i h
    simpa only [zero_add] using
      Aux.WF.wordSlice_lceq_of_common_realizes
        (Aux.WF.common_realizes_of_hint h) 0 n (by omega) i
  all_goals simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

theorem divide_wf {n : Nat} (p : Params n) :
    WF.GadgetSpec
      (fun lv rv (left right : Rep p × Rep p) =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2)
      (fun input => divide p input.1 input.2) Rep.WFRel := by
  wfgen' using [U.fromWord_wf_rel] unfold [divide, Rep.WFRel]
  case vc1 =>
    rename_i hHint hQ hB
    simp_all only [WF.LCEq, WF.evalArgs, LC.eval_ofConst]
    have hbounds := (hHint leftVal rightVal
      (hQ leftVal rightVal hB).1).1.1.2.1
    simp [hbounds]
  case vc2 outBitsL outBitsR B =>
    rename_i qL qR
    have hp := outBitsR leftVal rightVal B
    apply Aux.WF.wordSlice_lceq_of_common_realizes
    · exact Aux.WF.common_realizes_of_hint hp.1
    · omega
  case vc3 =>
    rename_i h
    simpa only [zero_add] using
      Aux.WF.wordSlice_lceq_of_common_realizes
        (Aux.WF.common_realizes_of_hint h) 0 n (by omega) i
  all_goals simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

theorem assertMulEq_wf {n : Nat} (p : Params n) :
    WF.GadgetSpec
      (fun lv rv (left right : Rep p × Rep p × Rep p) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => assertMulEq p input.1 input.2.1 input.2.2)
      (fun _ _ _ _ => True) := by
  wfgen' using [U.fromWord_wf_rel] unfold [assertMulEq, Rep.WFRel]
  case vc1 =>
    rename_i hrel
    apply WF.Rel.assertR1C_pure
    all_goals intro lv rv hB
    all_goals have h := hrel lv rv hB
    all_goals simp_all [WF.LCEq, U.WFRel, WF.evalArgs,
      LC.eval_add, LC.eval_sub, LC.eval_nsmul, LC.eval_ofConst]
  case vc2 =>
    rename_i h
    simpa only [zero_add] using
      Aux.WF.wordSlice_lceq_of_common_realizes
        (Aux.WF.common_realizes_of_hint h) 0 (n + quotientExtraBits)
          (by omega) i
  case vc3 =>
    simp_all [WF.LCEq, WF.evalArgs]
  case vc4 =>
    simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

set_option maxHeartbeats 1000000 in
theorem zeroTest_wf {n : Nat} (p : Params n) :
    WF.GadgetSpec Rep.WFRel (zeroTest p)
      (fun lv rv left right => WF.LCEq lv.int rv.int left right) := by
  wfgen' using [U.fromWord_wf_full, assertMulEq_wf]
    unfold [zeroTest, Rep.WFRel]
  case vc1 =>
    change 0 ≤ 0 ∧ 0 < 1 ∧ (0 - 0) % 1 = 0
    decide
  case vc3 =>
    change 0 ≤ 0 ∧ 0 < 1 ∧ (0 - 0) % 1 = 0
    decide
  case vc7 =>
    rename_i hZ hInv hB
    have hz := hZ leftVal rightVal (hInv leftVal rightVal hB).1
    have hbit := hz.2.2.1 (0 : Fin 1)
    unfold Rep.WFRel
    constructor
    · rfl
    · unfold WF.LCEq at hbit ⊢
      simp only [LC.eval_sub, LC.eval_ofConst]
      exact congrArg (fun x : Int => 1 - x) hbit
  case vc8 =>
    rename_i hZ hInv hB
    have hinv := hInv leftVal rightVal hB
    exact ⟨rfl, hinv.2.2.2⟩
  all_goals simp_all [WF.LCEq, WF.ArgsEq, WF.RealizesBools,
    WF.evalArgs, LC.eval_nsmul]
  all_goals try grind

@[spec] theorem mul_sound_zmod {x y : Rep p} :
    ⦃⌜True⌝⦄ Sound.interp ρ (mul p x y)
    ⦃⇓ out => ⌜MulZModSpec p ρ x y out⌝⦄ := by
  mvcgen [mul, MulZModSpec, evalZMod]
  intro bits
  mvcgen
  rename_i r q hr hq heq
  have hcast := congrArg (fun z : Int => (z : ZMod p.modulus)) heq
  simp only [LC.eval_add, LC.eval_nsmul, nsmul_eq_mul, Int.cast_mul,
    Int.cast_add, Int.cast_natCast, ZMod.natCast_self, zero_mul,
    add_zero] at hcast
  exact hcast.symm

@[spec] theorem mul_complete_zmod {x y : Rep p}
    (hx : x.Valid ρ) (hy : y.Valid ρ)
    (hbound : x.bound * y.bound < 2 ^ quotientExtraBits) :
    ⦃⌜True⌝⦄ Complete.interp ρ (mul p x y)
    ⦃⇓ out => ⌜MulZModSpec p ρ x y out ∧ out.Valid ρ ∧
      out.bound = 2⌝⦄ := by
  mvcgen [mul, MulZModSpec, evalZMod]
  let a := x.intVal.eval ρ.int
  let b := y.intVal.eval ρ.int
  let value := a.toNat * b.toNat
  let bits : Vector Bool (2 * n + quotientExtraBits) := Vector.ofFn fun i =>
    if hi : i.val < n then (value % p.modulus).testBit i.val
    else (value / p.modulus).testBit (i.val - n)
  refine ⟨bits, ?_, ?_⟩
  · simp [WF.interpHint, WF.evalArgs, hx.1, hy.1, bits, value, a, b]
  · mvcgen
    rename_i r hr q hq
    have hrFit : value % p.modulus < 2 ^ n :=
      (Nat.mod_lt _ p.positive).trans_le p.fits
    have hqFit : value / p.modulus < 2 ^ (n + quotientExtraBits) := by
      simpa [value, a, b] using Lazy.mul_quotient_fits p hx hy hbound
    have hrWord :
        (Word.eval ρ.bool {
          bitsLE := Vector.ofFn (n := n) fun i =>
            (Vector.map LC.ofConst bits)[i.val]'(by omega)
        }).toNat = value % p.modulus := by
      simp [Word.eval, BitVec.toNat_ofFnLE, bits, Nat.ofBits_testBit,
        Nat.mod_eq_of_lt hrFit]
    have hqWord :
        (Word.eval ρ.bool {
          bitsLE := Vector.ofFn (n := n + quotientExtraBits) fun i =>
            (Vector.map LC.ofConst bits)[n + i.val]'(by omega)
        }).toNat = value / p.modulus := by
      simp [Word.eval, BitVec.toNat_ofFnLE, bits,
        show ∀ i : Fin (n + quotientExtraBits), ¬n + i.val < n by omega,
        Nat.ofBits_testBit, Nat.mod_eq_of_lt hqFit]
    have hrVal : r.intVal.eval ρ.int = (value % p.modulus : Nat) := by
      rw [U.Rel.intVal hr, hrWord]
    have hqVal : q.intVal.eval ρ.int = (value / p.modulus : Nat) := by
      rw [U.Rel.intVal hq, hqWord]
    have haVal : a.toNat = a := by exact_mod_cast Int.toNat_of_nonneg hx.1
    have hbVal : b.toNat = b := by exact_mod_cast Int.toNat_of_nonneg hy.1
    constructor
    · simp only [LC.eval_add, LC.eval_nsmul, nsmul_eq_mul,
        hrVal, hqVal, value, a, b]
      change a * b = _
      rw [← haVal, ← hbVal]
      exact_mod_cast (Nat.mod_add_div value p.modulus).symm
    · mvcgen
      constructor
      · unfold MulZModSpec evalZMod
        have heq : a * b =
            (value % p.modulus : Nat) + p.modulus * (value / p.modulus) := by
          rw [← haVal, ← hbVal]
          exact_mod_cast (Nat.mod_add_div value p.modulus).symm
        have hcast := congrArg (fun z : Int => (z : ZMod p.modulus)) heq
        simpa [hrVal, value, a, b] using hcast.symm
      · exact ⟨U.intVal_nonneg r hr.1, by
          rw [hrVal]
          have hmod := Nat.mod_lt value p.positive
          push_cast
          nlinarith [p.positive]⟩

@[spec] theorem reduce_sound_zmod {x : Rep p} :
    ⦃⌜True⌝⦄ Sound.interp ρ (reduce p x)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      evalElemZMod p out ρ = evalZMod p x ρ⌝⦄ := by
  mvcgen [reduce]
  intro bits
  mvcgen
  rename_i r hr q hq
  intro heq
  intro houtVal
  refine ⟨heq, ?_⟩
  unfold evalElemZMod evalZMod
  rw [houtVal]
  have hcast := congrArg (fun z : Int => (z : ZMod p.modulus)) q
  simp only [LC.eval_zero, zero_mul, LC.eval_sub, LC.eval_add,
    LC.eval_nsmul, nsmul_eq_mul, Int.cast_sub, Int.cast_add,
    Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul,
    add_zero] at hcast
  have hcast' := hcast.symm
  simp only [Int.cast_zero] at hcast'
  have hEq := (sub_eq_zero.mp hcast').symm
  simpa [evalElemZMod, evalZMod, houtVal] using hEq
  case vc2 =>
    intro _
    first
    | exact (show U.Rel ρ _ _ from ‹U.Rel ρ _ _›).1

@[spec] theorem reduce_complete_zmod {x : Rep p}
    (hx : x.Valid ρ) (hbound : x.bound < 2 ^ quotientExtraBits) :
    ⦃⌜True⌝⦄ Complete.interp ρ (reduce p x)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      evalElemZMod p out ρ = evalZMod p x ρ⌝⦄ := by
  mvcgen [reduce]
  let a := x.intVal.eval ρ.int
  let bits : Vector Bool (2 * n + quotientExtraBits) := Vector.ofFn fun i =>
    if hi : i.val < n then (a.toNat % p.modulus).testBit i.val
    else (a.toNat / p.modulus).testBit (i.val - n)
  refine ⟨bits, ?_, ?_⟩
  · simp [WF.interpHint, WF.evalArgs, hx.1, bits, a]
  · mvcgen
    rename_i r hr q hq
    have hrFit : a.toNat % p.modulus < 2 ^ n :=
      (Nat.mod_lt _ p.positive).trans_le p.fits
    have haVal : (a.toNat : Int) = a := Int.toNat_of_nonneg hx.1
    have haBound : a.toNat < x.bound * p.modulus := by
      exact (Int.toNat_lt hx.1).2 hx.2
    have hqSmall : a.toNat / p.modulus < x.bound :=
      (Nat.div_lt_iff_lt_mul p.positive).2 (by
        simpa [Nat.mul_comm] using haBound)
    have hqFit : a.toNat / p.modulus < 2 ^ (n + quotientExtraBits) :=
      hqSmall.trans (hbound.trans_le
        (Nat.pow_le_pow_right (by omega) (by omega)))
    have hrWord :
        (Word.eval ρ.bool {
          bitsLE := Vector.ofFn (n := n) fun i =>
            (Vector.map LC.ofConst bits)[i.val]'(by omega)
        }).toNat = a.toNat % p.modulus := by
      simp [Word.eval, BitVec.toNat_ofFnLE, bits, Nat.ofBits_testBit,
        Nat.mod_eq_of_lt hrFit]
    have hqWord :
        (Word.eval ρ.bool {
          bitsLE := Vector.ofFn (n := n + quotientExtraBits) fun i =>
            (Vector.map LC.ofConst bits)[n + i.val]'(by omega)
        }).toNat = a.toNat / p.modulus := by
      simp [Word.eval, BitVec.toNat_ofFnLE, bits,
        show ∀ i : Fin (n + quotientExtraBits), ¬n + i.val < n by omega,
        Nat.ofBits_testBit, Nat.mod_eq_of_lt hqFit]
    have hrVal : r.intVal.eval ρ.int = (a.toNat % p.modulus : Nat) := by
      rw [U.Rel.intVal hr, hrWord]
    have hqVal : q.intVal.eval ρ.int = (a.toNat / p.modulus : Nat) := by
      rw [U.Rel.intVal hq, hqWord]
    constructor
    · simp only [LC.eval_zero, zero_mul, LC.eval_sub, LC.eval_add,
        LC.eval_nsmul, nsmul_eq_mul, hrVal, hqVal]
      apply Eq.symm
      apply sub_eq_zero.mpr
      change a = _
      rw [← haVal]
      simp only [Int.toNat_natCast]
      exact_mod_cast (Nat.mod_add_div a.toNat p.modulus).symm
    · mvcgen
      · exact hr.1
      · rw [hrVal]
        exact_mod_cast Nat.mod_lt a.toNat p.positive
      · intro hout houtVal
        refine ⟨hout, ?_⟩
        unfold evalElemZMod evalZMod
        rw [houtVal, hrVal, ← haVal]
        simp [max_eq_left hx.1, a]

@[spec] theorem mulSubToElem_sound_zmod {x y target : Rep p} :
    ⦃⌜True⌝⦄ Sound.interp ρ (mulSubToElem p x y target)
    ⦃⇓ out => ⌜MulSubToElemZModSpec p ρ x y target out⌝⦄ := by
  mvcgen [mulSubToElem, MulSubToElemZModSpec, evalZMod,
    evalElemZMod]
  intro bits
  mvcgen
  rename_i r q hr hq heq
  rcases heq with ⟨_, heq⟩
  have hcast := congrArg (fun z : Int => (z : ZMod p.modulus)) heq
  simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul, LC.eval_ofConst,
    nsmul_eq_mul, Int.cast_mul, Int.cast_add, Int.cast_sub,
    Int.cast_natCast, Nat.cast_mul, ZMod.natCast_self, mul_zero,
    zero_mul, add_zero, sub_zero] at hcast
  exact (eq_sub_iff_add_eq).2 hcast.symm

@[spec] theorem mulSubToElem_complete_zmod {x y target : Rep p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) (htarget : target.Valid ρ)
    (hbound : x.bound * y.bound + target.bound <
      2 ^ quotientExtraBits) :
    ⦃⌜True⌝⦄ Complete.interp ρ (mulSubToElem p x y target)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      MulSubToElemZModSpec p ρ x y target out⌝⦄ := by
  mvcgen [mulSubToElem]
  let a := x.intVal.eval ρ.int
  let b := y.intVal.eval ρ.int
  let c := target.intVal.eval ρ.int
  let shifted := a * b + (target.bound * p.modulus : Nat) - c
  have hshifted : 0 ≤ shifted := by
    have hab : 0 ≤ a * b := mul_nonneg hx.1 hy.1
    have hc : c < (target.bound * p.modulus : Nat) := htarget.2
    change 0 ≤ a * b + (target.bound * p.modulus : Nat) - c
    omega
  have hcond : c ≤ a * b + (target.bound * p.modulus : Nat) := by
    change 0 ≤ a * b + (target.bound * p.modulus : Nat) - c at hshifted
    omega
  have hcond' : target.intVal.eval ρ.int ≤
      x.intVal.eval ρ.int * y.intVal.eval ρ.int +
        (target.bound : Int) * p.modulus := by
    simpa [a, b, c] using hcond
  let value := shifted.toNat
  let bits : Vector Bool (2 * n + quotientExtraBits) := Vector.ofFn fun i =>
    if hi : i.val < n then (value % p.modulus).testBit i.val
    else (value / p.modulus).testBit (i.val - n)
  refine ⟨bits, ?_, ?_⟩
  · simp [WF.interpHint, WF.evalArgs, a, b, c, shifted, hcond',
      bits, value]
  · mvcgen
    rename_i r hr q hq
    have hrFit : value % p.modulus < 2 ^ n :=
      (Nat.mod_lt _ p.positive).trans_le p.fits
    have hvalue : (value : Int) = shifted :=
      Int.toNat_of_nonneg hshifted
    have hablt : a * b <
        ((x.bound * p.modulus : Nat) : Int) *
          ((y.bound * p.modulus : Nat) : Int) := by
      have hyBoundPos : 0 < ((y.bound * p.modulus : Nat) : Int) :=
        lt_of_le_of_lt hy.1 hy.2
      exact (mul_le_mul_of_nonneg_left hy.2.le hx.1).trans_lt
        (mul_lt_mul_of_pos_right hx.2 hyBoundPos)
    have hshiftUpper : value <
        (x.bound * y.bound + target.bound) * p.modulus * p.modulus := by
      rw [show value = shifted.toNat by rfl]
      apply (Int.toNat_lt hshifted).2
      change shifted <
        (((x.bound * y.bound + target.bound) * p.modulus *
          p.modulus : Nat) : Int)
      have hc0 : 0 ≤ c := htarget.1
      have hp1 : (1 : Int) ≤ p.modulus := by exact_mod_cast p.positive
      have hpLeSq : (p.modulus : Int) ≤ (p.modulus : Int) ^ 2 := by
        nlinarith
      have hbiasLe : (p.modulus : Int) * target.bound ≤
          (p.modulus : Int) ^ 2 * target.bound :=
        mul_le_mul_of_nonneg_right hpLeSq (by positivity)
      dsimp [shifted]
      push_cast at hablt ⊢
      ring_nf at hablt ⊢
      linarith
    have hqSmall : value / p.modulus <
        (x.bound * y.bound + target.bound) * p.modulus :=
      (Nat.div_lt_iff_lt_mul p.positive).2 (by
        simpa [Nat.mul_assoc] using hshiftUpper)
    have hqFit : value / p.modulus < 2 ^ (n + quotientExtraBits) := by
      calc
        value / p.modulus <
            (x.bound * y.bound + target.bound) * p.modulus := hqSmall
        _ < 2 ^ quotientExtraBits * 2 ^ n :=
          Nat.mul_lt_mul_of_lt_of_le hbound p.fits (by positivity)
        _ = 2 ^ (n + quotientExtraBits) := by
          rw [pow_add]
          ac_rfl
    have hrWord :
        (Word.eval ρ.bool {
          bitsLE := Vector.ofFn (n := n) fun i =>
            (Vector.map LC.ofConst bits)[i.val]'(by omega)
        }).toNat = value % p.modulus := by
      simp [Word.eval, BitVec.toNat_ofFnLE, bits, Nat.ofBits_testBit,
        Nat.mod_eq_of_lt hrFit]
    have hqWord :
        (Word.eval ρ.bool {
          bitsLE := Vector.ofFn (n := n + quotientExtraBits) fun i =>
            (Vector.map LC.ofConst bits)[n + i.val]'(by omega)
        }).toNat = value / p.modulus := by
      simp [Word.eval, BitVec.toNat_ofFnLE, bits,
        show ∀ i : Fin (n + quotientExtraBits), ¬n + i.val < n by omega,
        Nat.ofBits_testBit, Nat.mod_eq_of_lt hqFit]
    have hrVal : r.intVal.eval ρ.int = (value % p.modulus : Nat) := by
      rw [U.Rel.intVal hr, hrWord]
    have hqVal : q.intVal.eval ρ.int = (value / p.modulus : Nat) := by
      rw [U.Rel.intVal hq, hqWord]
    constructor
    · simp only [LC.eval_add, LC.eval_sub, LC.eval_nsmul,
        LC.eval_ofConst, nsmul_eq_mul, hrVal, hqVal]
      have hdecomp : (value : Int) =
          ((value % p.modulus : Nat) : Int) +
            (p.modulus : Int) * ((value / p.modulus : Nat) : Int) := by
        exact_mod_cast (Nat.mod_add_div value p.modulus).symm
      dsimp [shifted, a, b, c] at hvalue
      omega
    · mvcgen
      constructor
      · exact ⟨hr.1, by
          rw [hrVal]
          exact_mod_cast Nat.mod_lt value p.positive⟩
      · unfold MulSubToElemZModSpec evalElemZMod evalZMod
        rw [hrVal]
        have hdecomp : (value : Int) =
            ((value % p.modulus : Nat) : Int) +
              (p.modulus : Int) * ((value / p.modulus : Nat) : Int) := by
          exact_mod_cast (Nat.mod_add_div value p.modulus).symm
        have hInt : (value % p.modulus : ZMod p.modulus) =
            (a : ZMod p.modulus) * (b : ZMod p.modulus) -
              (c : ZMod p.modulus) := by
          have hshift := hvalue
          dsimp [shifted] at hshift
          have hcast := congrArg (Int.castRingHom (ZMod p.modulus)) hshift
          simpa using hcast
        simpa [a, b, c] using hInt

@[spec] theorem divide_sound_zmod {denominator numerator : Rep p} :
    ⦃⌜True⌝⦄ Sound.interp ρ (divide p denominator numerator)
    ⦃⇓ out => ⌜DivideZModSpec p ρ denominator numerator out⌝⦄ := by
  mvcgen [divide, DivideZModSpec, evalZMod]
  intro bits
  mvcgen
  rename_i value q hv hq heq
  rcases heq with ⟨_, heq⟩
  have hcast := congrArg (fun z : Int => (z : ZMod p.modulus)) heq
  simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul, LC.eval_ofConst,
    nsmul_eq_mul, Int.cast_mul, Int.cast_add, Int.cast_sub,
    Int.cast_natCast, Nat.cast_mul, ZMod.natCast_self, mul_zero,
    zero_mul, add_zero, sub_zero] at hcast
  exact hcast

@[spec] theorem divide_complete_zmod [Fact (Nat.Prime p.modulus)]
    {denominator numerator : Rep p}
    (hdenominator : denominator.Valid ρ)
    (hnumerator : numerator.Valid ρ)
    (hden : evalZMod p denominator ρ ≠ 0)
    (hbound : denominator.bound + numerator.bound <
      2 ^ quotientExtraBits) :
    ⦃⌜True⌝⦄ Complete.interp ρ (divide p denominator numerator)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      DivideZModSpec p ρ denominator numerator out ∧ out.bound = 2⌝⦄ := by
  mvcgen [divide]
  let a := denominator.intVal.eval ρ.int
  let b := numerator.intVal.eval ρ.int
  have haNat : (a.toNat : Int) = a := Int.toNat_of_nonneg hdenominator.1
  have hbNat : (b.toNat : Int) = b := Int.toNat_of_nonneg hnumerator.1
  let d := a.toNat % p.modulus
  have hdlt : d < p.modulus := Nat.mod_lt _ p.positive
  have haZ : (a : ZMod p.modulus) = (a.toNat : ZMod p.modulus) := by
    rw [← Int.cast_natCast]
    exact congrArg (Int.castRingHom (ZMod p.modulus)) haNat.symm
  have hd : d ≠ 0 := by
    intro hd0
    apply hden
    unfold evalZMod
    change (a : ZMod p.modulus) = 0
    rw [haZ]
    simpa [d, hd0] using
      (show (a.toNat : ZMod p.modulus) =
          (a.toNat % p.modulus : ZMod p.modulus) by simp)
  have hgcd : Nat.gcd d p.modulus = 1 := by
    rw [Nat.gcd_comm]
    exact (Nat.coprime_of_lt_prime hd hdlt Fact.out).gcd_eq_one
  let inverse := ((Nat.gcdA d p.modulus) % (p.modulus : Int)).toNat
  let value := (inverse * (b.toNat % p.modulus)) % p.modulus
  have hinverse : (inverse : ZMod p.modulus) *
      (d : ZMod p.modulus) = 1 := by
    have hp0 : (p.modulus : Int) ≠ 0 := by exact_mod_cast p.positive.ne'
    have hinverseInt : (inverse : Int) =
        Nat.gcdA d p.modulus % (p.modulus : Int) := by
      exact Int.toNat_of_nonneg (Int.emod_nonneg _ hp0)
    have hinverseCast : (inverse : ZMod p.modulus) =
        (Nat.gcdA d p.modulus : ZMod p.modulus) := by
      rw [← Int.cast_natCast, hinverseInt]
      simp
    rw [hinverseCast]
    have hbezout := Nat.gcd_eq_gcd_ab d p.modulus
    have hcast := congrArg (Int.castRingHom (ZMod p.modulus)) hbezout
    simpa [hgcd, mul_comm] using hcast.symm
  have hbZ : (b.toNat : ZMod p.modulus) = (b : ZMod p.modulus) := by
    rw [← Int.cast_natCast]
    exact congrArg (Int.castRingHom (ZMod p.modulus)) hbNat
  have hvalueZ : (value : ZMod p.modulus) *
      (a : ZMod p.modulus) = (b : ZMod p.modulus) := by
    rw [haZ]
    have hvalueCast : (value : ZMod p.modulus) =
        (inverse : ZMod p.modulus) * (b.toNat : ZMod p.modulus) := by
      simp [value]
    have haMod : (a.toNat : ZMod p.modulus) =
        (d : ZMod p.modulus) := by simp [d]
    rw [hvalueCast, haMod]
    calc
      (inverse : ZMod p.modulus) * (b.toNat : ZMod p.modulus) * d =
          (inverse * d) * (b.toNat : ZMod p.modulus) := by ring
      _ = (b.toNat : ZMod p.modulus) := by rw [hinverse]; simp
      _ = (b : ZMod p.modulus) := hbZ
  let shifted : Int := (value : Int) * a +
    (numerator.bound * p.modulus : Nat) - b
  have hshifted : 0 ≤ shifted := by
    have hva : 0 ≤ (value : Int) * a :=
      mul_nonneg (by positivity) hdenominator.1
    have hbUpper : b < (numerator.bound * p.modulus : Nat) :=
      hnumerator.2
    dsimp [shifted]
    omega
  have hshiftCond : b ≤ (value : Int) * a +
      (numerator.bound * p.modulus : Nat) := by
    change 0 ≤ (value : Int) * a +
      (numerator.bound * p.modulus : Nat) - b at hshifted
    omega
  have hshiftDvd : (p.modulus : Int) ∣ shifted := by
    have hmod : (((value : Int) * a : Int) : ZMod p.modulus) =
        (b : ZMod p.modulus) := by simpa using hvalueZ
    have hdvdDiff : (p.modulus : Int) ∣ b - (value : Int) * a :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hmod
    have hdvdNeg : (p.modulus : Int) ∣ (value : Int) * a - b := by
      simpa [neg_sub] using dvd_neg.mpr hdvdDiff
    dsimp [shifted]
    rcases hdvdNeg with ⟨k, hk⟩
    refine ⟨k + numerator.bound, ?_⟩
    push_cast
    calc
      (value : Int) * a + numerator.bound * p.modulus - b =
          ((value : Int) * a - b) + numerator.bound * p.modulus := by ring
      _ = p.modulus * k + numerator.bound * p.modulus := by rw [hk]
      _ = p.modulus * (k + numerator.bound) := by ring
  let bits : Vector Bool (2 * n + quotientExtraBits) := Vector.ofFn fun i =>
    if hi : i.val < n then value.testBit i.val
    else (shifted.toNat / p.modulus).testBit (i.val - n)
  refine ⟨bits, ?_, ?_⟩
  · simp only [WF.evalArgs]
    rw [if_pos hdenominator.1, if_pos hnumerator.1,
      if_neg hd, if_pos hgcd, if_pos hshifted]
    rfl
  · mvcgen
    rename_i r hr q hq
    have hvalueFit : value < 2 ^ n :=
      (Nat.mod_lt _ p.positive).trans_le p.fits
    have hshiftEq : (shifted.toNat : Int) = shifted :=
      Int.toNat_of_nonneg hshifted
    have hvaUpper : (value : Int) * a <
        (p.modulus : Int) *
          ((denominator.bound * p.modulus : Nat) : Int) := by
      have hv : (value : Int) < p.modulus := by
        exact_mod_cast Nat.mod_lt (inverse * (b.toNat % p.modulus)) p.positive
      have hdenBoundPos : 0 <
          ((denominator.bound * p.modulus : Nat) : Int) :=
        lt_of_le_of_lt hdenominator.1 hdenominator.2
      exact (mul_le_mul_of_nonneg_left hdenominator.2.le (by positivity)).trans_lt
        (mul_lt_mul_of_pos_right hv hdenBoundPos)
    have hshiftUpper : shifted.toNat <
        (denominator.bound + numerator.bound) * p.modulus * p.modulus := by
      apply (Int.toNat_lt hshifted).2
      change shifted <
        (((denominator.bound + numerator.bound) * p.modulus *
          p.modulus : Nat) : Int)
      have hb0 : 0 ≤ b := hnumerator.1
      have hp1 : (1 : Int) ≤ p.modulus := by exact_mod_cast p.positive
      have hpLeSq : (p.modulus : Int) ≤ (p.modulus : Int) ^ 2 := by
        nlinarith
      have hbiasLe : (p.modulus : Int) * numerator.bound ≤
          (p.modulus : Int) ^ 2 * numerator.bound :=
        mul_le_mul_of_nonneg_right hpLeSq (by positivity)
      dsimp [shifted]
      push_cast at hvaUpper ⊢
      ring_nf at hvaUpper ⊢
      linarith
    have hqSmall : shifted.toNat / p.modulus <
        (denominator.bound + numerator.bound) * p.modulus :=
      (Nat.div_lt_iff_lt_mul p.positive).2 (by
        simpa [Nat.mul_assoc] using hshiftUpper)
    have hqFit : shifted.toNat / p.modulus <
        2 ^ (n + quotientExtraBits) := by
      calc
        shifted.toNat / p.modulus <
            (denominator.bound + numerator.bound) * p.modulus := hqSmall
        _ < 2 ^ quotientExtraBits * 2 ^ n :=
          Nat.mul_lt_mul_of_lt_of_le hbound p.fits (by positivity)
        _ = 2 ^ (n + quotientExtraBits) := by
          rw [pow_add]
          ac_rfl
    have hrWord :
        (Word.eval ρ.bool {
          bitsLE := Vector.ofFn (n := n) fun i =>
            (Vector.map LC.ofConst bits)[i.val]'(by omega)
        }).toNat = value := by
      simp [Word.eval, BitVec.toNat_ofFnLE, bits, Nat.ofBits_testBit,
        Nat.mod_eq_of_lt hvalueFit]
    have hqWord :
        (Word.eval ρ.bool {
          bitsLE := Vector.ofFn (n := n + quotientExtraBits) fun i =>
            (Vector.map LC.ofConst bits)[n + i.val]'(by omega)
        }).toNat = shifted.toNat / p.modulus := by
      simp [Word.eval, BitVec.toNat_ofFnLE, bits,
        show ∀ i : Fin (n + quotientExtraBits), ¬n + i.val < n by omega,
        Nat.ofBits_testBit, Nat.mod_eq_of_lt hqFit]
    have hrVal : r.intVal.eval ρ.int = (value : Nat) := by
      rw [U.Rel.intVal hr, hrWord]
    have hqVal : q.intVal.eval ρ.int =
        (shifted.toNat / p.modulus : Nat) := by
      rw [U.Rel.intVal hq, hqWord]
    have hshiftDvdNat : p.modulus ∣ shifted.toNat := by
      rcases hshiftDvd with ⟨k, hk⟩
      refine ⟨k.toNat, ?_⟩
      have hk0 : 0 ≤ k := by
        have hp : (0 : Int) < p.modulus := by exact_mod_cast p.positive
        rw [hk] at hshifted
        nlinarith
      have hkNat : (k.toNat : Int) = k := Int.toNat_of_nonneg hk0
      apply Int.ofNat_inj.mp
      calc
        (shifted.toNat : Int) = shifted := hshiftEq
        _ = (p.modulus : Int) * k := hk
        _ = (p.modulus : Int) * (k.toNat : Int) := by rw [hkNat]
        _ = ((p.modulus * k.toNat : Nat) : Int) := by norm_num
    have hshiftDecomp : (shifted.toNat : Int) =
        (p.modulus : Int) * (shifted.toNat / p.modulus : Nat) := by
      have hnat := Nat.mod_add_div shifted.toNat p.modulus
      rw [Nat.mod_eq_zero_of_dvd hshiftDvdNat] at hnat
      simp only [zero_add] at hnat
      exact_mod_cast hnat.symm
    constructor
    · simp only [LC.eval_add, LC.eval_sub, LC.eval_nsmul,
        LC.eval_ofConst, nsmul_eq_mul, hrVal, hqVal]
      change (value : Int) * a = b +
        (p.modulus : Int) * (shifted.toNat / p.modulus : Nat) -
          (numerator.bound * p.modulus : Nat)
      calc
        (value : Int) * a =
            shifted - (numerator.bound * p.modulus : Nat) + b := by
          dsimp [shifted]
          ring
        _ = (shifted.toNat : Int) -
            (numerator.bound * p.modulus : Nat) + b := by rw [hshiftEq]
        _ = (p.modulus : Int) *
            (shifted.toNat / p.modulus : Nat) -
              (numerator.bound * p.modulus : Nat) + b := by
          rw [hshiftDecomp]
        _ = b + (p.modulus : Int) *
            (shifted.toNat / p.modulus : Nat) -
              (numerator.bound * p.modulus : Nat) := by ring
    · mvcgen
      constructor
      · exact ⟨by
          rw [hrVal]
          exact_mod_cast Nat.zero_le value, by
          rw [hrVal]
          have hp : (value : Int) < 2 * p.modulus := by
            have hv : value < p.modulus := Nat.mod_lt _ p.positive
            exact_mod_cast hv.trans (by omega)
          exact hp⟩
      · unfold DivideZModSpec evalZMod
        rw [hrVal]
        simpa [a, b] using hvalueZ

@[spec] theorem assertMulEq_sound_zmod {x y target : Rep p} :
    ⦃⌜True⌝⦄ Sound.interp ρ (assertMulEq p x y target)
    ⦃⇓ _ => ⌜AssertMulEqZModSpec p ρ x y target⌝⦄ := by
  mvcgen [assertMulEq, AssertMulEqZModSpec, evalZMod]
  intro bits
  mvcgen
  intro heq
  have hcast := congrArg (fun z : Int => (z : ZMod p.modulus)) heq
  simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul, LC.eval_ofConst,
    nsmul_eq_mul, Int.cast_mul, Int.cast_add, Int.cast_sub,
    Int.cast_natCast, Nat.cast_mul, ZMod.natCast_self, mul_zero,
    zero_mul, add_zero, sub_zero] at hcast
  exact hcast

@[spec] theorem assertMulEq_complete_zmod {x y target : Rep p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) (htarget : target.Valid ρ)
    (hspec : AssertMulEqZModSpec p ρ x y target)
    (hbound : x.bound * y.bound + target.bound <
      2 ^ quotientExtraBits) :
    ⦃⌜True⌝⦄ Complete.interp ρ (assertMulEq p x y target)
    ⦃⇓ _ => ⌜AssertMulEqZModSpec p ρ x y target⌝⦄ := by
  mvcgen [assertMulEq]
  let a := x.intVal.eval ρ.int
  let b := y.intVal.eval ρ.int
  let c := target.intVal.eval ρ.int
  let shifted : Int := a * b + (target.bound * p.modulus : Nat) - c
  have hshifted : 0 ≤ shifted := by
    have hab : 0 ≤ a * b := mul_nonneg hx.1 hy.1
    have hc : c < (target.bound * p.modulus : Nat) := htarget.2
    dsimp [shifted]
    omega
  have hshiftDvd : (p.modulus : Int) ∣ shifted := by
    unfold AssertMulEqZModSpec evalZMod at hspec
    have hmod : ((a * b : Int) : ZMod p.modulus) =
        (c : ZMod p.modulus) := by simpa [a, b, c] using hspec
    have hdvdDiff : (p.modulus : Int) ∣ c - a * b :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hmod
    have hdvdNeg : (p.modulus : Int) ∣ a * b - c := by
      simpa [neg_sub] using dvd_neg.mpr hdvdDiff
    rcases hdvdNeg with ⟨k, hk⟩
    refine ⟨k + target.bound, ?_⟩
    push_cast
    dsimp [shifted]
    calc
      a * b + target.bound * p.modulus - c =
          (a * b - c) + target.bound * p.modulus := by ring
      _ = p.modulus * k + target.bound * p.modulus := by rw [hk]
      _ = p.modulus * (k + target.bound) := by ring
  let quotient := shifted.toNat / p.modulus
  let bits : Vector Bool (n + quotientExtraBits) := Vector.ofFn fun i =>
    quotient.testBit i.val
  refine ⟨bits, ?_, ?_⟩
  · simp only [WF.evalArgs]
    rw [if_pos hshifted]
    rfl
  · mvcgen
    rename_i q hq
    have hshiftEq : (shifted.toNat : Int) = shifted :=
      Int.toNat_of_nonneg hshifted
    have hablt : a * b <
        ((x.bound * p.modulus : Nat) : Int) *
          ((y.bound * p.modulus : Nat) : Int) := by
      have hyBoundPos : 0 < ((y.bound * p.modulus : Nat) : Int) :=
        lt_of_le_of_lt hy.1 hy.2
      exact (mul_le_mul_of_nonneg_left hy.2.le hx.1).trans_lt
        (mul_lt_mul_of_pos_right hx.2 hyBoundPos)
    have hshiftUpper : shifted.toNat <
        (x.bound * y.bound + target.bound) * p.modulus * p.modulus := by
      apply (Int.toNat_lt hshifted).2
      change shifted <
        (((x.bound * y.bound + target.bound) * p.modulus *
          p.modulus : Nat) : Int)
      have hc0 : 0 ≤ c := htarget.1
      have hp1 : (1 : Int) ≤ p.modulus := by exact_mod_cast p.positive
      have hpLeSq : (p.modulus : Int) ≤ (p.modulus : Int) ^ 2 := by
        nlinarith
      have hbiasLe : (p.modulus : Int) * target.bound ≤
          (p.modulus : Int) ^ 2 * target.bound :=
        mul_le_mul_of_nonneg_right hpLeSq (by positivity)
      dsimp [shifted]
      push_cast at hablt ⊢
      ring_nf at hablt ⊢
      linarith
    have hqSmall : quotient <
        (x.bound * y.bound + target.bound) * p.modulus := by
      dsimp [quotient]
      exact (Nat.div_lt_iff_lt_mul p.positive).2 (by
        simpa [Nat.mul_assoc] using hshiftUpper)
    have hqFit : quotient < 2 ^ (n + quotientExtraBits) := by
      calc
        quotient < (x.bound * y.bound + target.bound) * p.modulus := hqSmall
        _ < 2 ^ quotientExtraBits * 2 ^ n :=
          Nat.mul_lt_mul_of_lt_of_le hbound p.fits (by positivity)
        _ = 2 ^ (n + quotientExtraBits) := by rw [pow_add]; ac_rfl
    have hqWord :
        (Word.eval ρ.bool {
          bitsLE := Vector.ofFn (n := n + quotientExtraBits) fun i =>
            (Vector.map LC.ofConst bits)[i.val]
        }).toNat = quotient := by
      simp [Word.eval, BitVec.toNat_ofFnLE, bits, Nat.ofBits_testBit,
        Nat.mod_eq_of_lt hqFit]
    have hqVal : q.intVal.eval ρ.int = (quotient : Nat) := by
      rw [U.Rel.intVal hq, hqWord]
    have hshiftDvdNat : p.modulus ∣ shifted.toNat := by
      rcases hshiftDvd with ⟨k, hk⟩
      have hk0 : 0 ≤ k := by
        have hp : (0 : Int) < p.modulus := by exact_mod_cast p.positive
        rw [hk] at hshifted
        nlinarith
      refine ⟨k.toNat, ?_⟩
      apply Int.ofNat_inj.mp
      calc
        (shifted.toNat : Int) = shifted := hshiftEq
        _ = (p.modulus : Int) * k := hk
        _ = (p.modulus : Int) * (k.toNat : Int) := by
          rw [Int.toNat_of_nonneg hk0]
        _ = ((p.modulus * k.toNat : Nat) : Int) := by norm_num
    have hdecomp : (shifted.toNat : Int) =
        (p.modulus : Int) * (quotient : Nat) := by
      have hnat := Nat.mod_add_div shifted.toNat p.modulus
      rw [Nat.mod_eq_zero_of_dvd hshiftDvdNat] at hnat
      simp only [zero_add] at hnat
      dsimp [quotient]
      exact_mod_cast hnat.symm
    constructor
    · simp only [LC.eval_add, LC.eval_sub, LC.eval_nsmul,
        LC.eval_ofConst, nsmul_eq_mul, hqVal]
      change a * b = c + (p.modulus : Int) * quotient -
        (target.bound * p.modulus : Nat)
      calc
        a * b = shifted - (target.bound * p.modulus : Nat) + c := by
          dsimp [shifted]
          ring
        _ = (shifted.toNat : Int) -
            (target.bound * p.modulus : Nat) + c := by rw [hshiftEq]
        _ = (p.modulus : Int) * quotient -
            (target.bound * p.modulus : Nat) + c := by rw [hdecomp]
        _ = c + (p.modulus : Int) * quotient -
            (target.bound * p.modulus : Nat) := by ring
    · exact hspec

@[spec] theorem zeroTest_sound_zmod [Fact (Nat.Prime p.modulus)]
    {x : Rep p} :
    ⦃⌜True⌝⦄ Sound.interp ρ (zeroTest p x)
    ⦃⇓ z => ⌜ZeroTestZModSpec p ρ x z⌝⦄ := by
  mvcgen [zeroTest, ZeroTestZModSpec]
  intro bits
  mvcgen
  intro qbits
  mvcgen
  rename_i zWord hzWord inverse hInverse u hmul q hq hfinal
  rcases hfinal with ⟨_, hfinal⟩
  have hzBit : zWord.intBits[0].eval ρ.int = 0 ∨
      zWord.intBits[0].eval ρ.int = 1 := by
    have hz := hzWord.1 (0 : Fin 1)
    cases hb : zWord.bits.bitsLE[0].eval ρ.bool <;>
      simp [hb] at hz
    · exact Or.inl hz
    · exact Or.inr hz
  have hmul' : evalZMod p x ρ *
      ((inverse.intVal.eval ρ.int : Int) : ZMod p.modulus) =
      1 - ((zWord.intBits[0].eval ρ.int : Int) : ZMod p.modulus) := by
    simpa [AssertMulEqZModSpec, evalZMod, ofElem, LC.eval_sub,
      LC.eval_ofConst, Int.cast_sub, Int.cast_one] using hmul
  have hfinalCast :=
    congrArg (fun z : Int => (z : ZMod p.modulus)) hfinal
  simp only [LC.eval_nsmul, nsmul_eq_mul, Int.cast_mul,
    Int.cast_natCast, ZMod.natCast_self, zero_mul] at hfinalCast
  refine ⟨hzBit, ?_, ?_⟩
  · constructor
    · intro hz
      simpa [evalZMod, hz] using hfinalCast
    · intro hx
      rcases hzBit with hz | hz
      · have hzeroOne : (0 : ZMod p.modulus) = 1 := by
          simpa [hx, hz] using hmul'
        exact (zero_ne_one hzeroOne).elim
      · exact hz
  · rcases hzBit with hz | hz
    · have hx0 : evalZMod p x ρ ≠ 0 := by
        intro hx
        have hzeroOne : (0 : ZMod p.modulus) = 1 := by
          simpa [hx, hz] using hmul'
        exact zero_ne_one hzeroOne
      simp [hz, hx0]
    · have hx0 : evalZMod p x ρ = 0 := by
        simpa [evalZMod, hz] using hfinalCast
      simp [hz, hx0]

@[spec] theorem zeroTest_complete_zmod [Fact (Nat.Prime p.modulus)]
    {x : Rep p} (hx : x.Valid ρ)
    (hbound : x.bound * 2 + 1 < 2 ^ quotientExtraBits) :
    ⦃⌜True⌝⦄ Complete.interp ρ (zeroTest p x)
    ⦃⇓ z => ⌜ZeroTestZModSpec p ρ x z⌝⦄ := by
  mvcgen [zeroTest]
  let a := x.intVal.eval ρ.int
  have haNat : (a.toNat : Int) = a := Int.toNat_of_nonneg hx.1
  let d := a.toNat % p.modulus
  let isZero := d = 0
  let inverse := Nat.gcdA d p.modulus % (p.modulus : Int)
  have hpInt0 : (p.modulus : Int) ≠ 0 := by exact_mod_cast p.positive.ne'
  have hinverse0 : 0 ≤ inverse := by
    exact Int.emod_nonneg _ hpInt0
  have hinverseLtInt : inverse < p.modulus := by
    exact Int.emod_lt_of_pos _ (by exact_mod_cast p.positive)
  have hinverseLt : inverse.toNat < p.modulus :=
    (Int.toNat_lt hinverse0).2 hinverseLtInt
  have hinverseFit : inverse.toNat < 2 ^ n :=
    hinverseLt.trans_le p.fits
  let bits : Vector Bool (n + 1) := Vector.ofFn fun i =>
    if hi : i.val = 0 then isZero
    else inverse.toNat.testBit (i.val - 1)
  have inverseWordEval :
      (Word.eval ρ.bool {
        bitsLE := Vector.ofFn (n := n) fun i =>
          (Vector.map LC.ofConst bits)[i.val + 1]'(by omega)
      }).toNat = inverse.toNat := by
    simp [Word.eval, BitVec.toNat_ofFnLE, bits,
      Nat.ofBits_testBit, Nat.mod_eq_of_lt hinverseFit]
  have invValid (inv : U n) (hinv : U.Rel ρ inv
      (Word.eval ρ.bool {
        bitsLE := Vector.ofFn fun i =>
          (Vector.map LC.ofConst bits)[i.val + 1]'(by omega) })) :
      (ofElem p { val := inv }).Valid ρ := by
    apply ofElem_valid
    refine ⟨hinv.1, ?_⟩
    rw [U.Rel.intVal hinv, inverseWordEval]
    exact_mod_cast hinverseLt
  have zBitEval (z : U 1) (hz : U.Rel ρ z
      (Word.eval ρ.bool {
        bitsLE := Vector.ofFn (n := 1) fun _ =>
          (Vector.map LC.ofConst bits)[0] })) :
      z.intBits[0].eval ρ.int = if isZero then 1 else 0 := by
    have hzInt := U.Rel.intVal hz
    have hword :
        (Word.eval ρ.bool {
          bitsLE := Vector.ofFn (n := 1) fun _ =>
            (Vector.map LC.ofConst bits)[0] }).toNat =
          if isZero then 1 else 0 := by
      by_cases hzero : isZero
      · simp [Word.eval, BitVec.toNat_ofFnLE, bits, isZero, hzero,
          Nat.ofBits]
        native_decide
      · simp [Word.eval, BitVec.toNat_ofFnLE, bits, isZero, hzero,
          Nat.ofBits]
        native_decide
    have hzIntVal : z.intVal.eval ρ.int =
        if isZero then 1 else 0 := hzInt.trans (by exact_mod_cast hword)
    simpa [U.intVal] using hzIntVal
  have targetValid (z : U 1) (hz : U.Rel ρ z
      (Word.eval ρ.bool {
        bitsLE := Vector.ofFn (n := 1) fun _ =>
          (Vector.map LC.ofConst bits)[0] })) :
      ((⟨(LC.ofConst 1 : LC Int) - z.intBits[0], 1⟩ : Rep p).Valid ρ) := by
    have hzBit := zBitEval z hz
    unfold Rep.Valid
    constructor
    · simp only [LC.eval_sub, LC.eval_ofConst, hzBit]
      split <;> omega
    · simp only [LC.eval_sub, LC.eval_ofConst, hzBit]
      have hp2 : 2 ≤ p.modulus :=
        (Fact.out : Nat.Prime p.modulus).two_le
      split <;> push_cast <;> omega
  have zeroMulSpec (z : U 1) (hz : U.Rel ρ z
      (Word.eval ρ.bool {
        bitsLE := Vector.ofFn (n := 1) fun _ =>
          (Vector.map LC.ofConst bits)[0] }))
      (inv : U n) (hinv : U.Rel ρ inv
      (Word.eval ρ.bool {
        bitsLE := Vector.ofFn fun i =>
          (Vector.map LC.ofConst bits)[i.val + 1]'(by omega) })) :
      AssertMulEqZModSpec p ρ x (ofElem p { val := inv })
        { intVal := (LC.ofConst 1 : LC Int) - z.intBits[0],
          bound := 1 } := by
    have hzBit := zBitEval z hz
    have hinvVal : inv.intVal.eval ρ.int = inverse.toNat := by
      rw [U.Rel.intVal hinv, inverseWordEval]
    have haZ : (a : ZMod p.modulus) = (d : ZMod p.modulus) := by
      have haCast : (a : ZMod p.modulus) =
          (a.toNat : ZMod p.modulus) := by
        rw [← Int.cast_natCast]
        exact (congrArg (Int.castRingHom (ZMod p.modulus)) haNat).symm
      rw [haCast]
      simp [d]
    unfold AssertMulEqZModSpec evalZMod ofElem
    rw [hinvVal]
    simp only [LC.eval_sub, LC.eval_ofConst]
    have hmain : (a : ZMod p.modulus) *
        (inverse.toNat : ZMod p.modulus) =
        ((1 - z.intBits[0].eval ρ.int : Int) : ZMod p.modulus) := by
      rw [haZ, hzBit]
      by_cases hzero : d = 0
      · simp [isZero, hzero]
      · have hgcd : Nat.gcd d p.modulus = 1 := by
          rw [Nat.gcd_comm]
          exact (Nat.coprime_of_lt_prime hzero
            (Nat.mod_lt _ p.positive) Fact.out).gcd_eq_one
        have hinverseCast : (inverse.toNat : ZMod p.modulus) =
            (Nat.gcdA d p.modulus : ZMod p.modulus) := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg hinverse0]
          dsimp [inverse]
          simp
        rw [hinverseCast]
        have hbezout := Nat.gcd_eq_gcd_ab d p.modulus
        have hcast := congrArg (Int.castRingHom (ZMod p.modulus)) hbezout
        simpa [isZero, hzero, hgcd, mul_comm] using hcast.symm
    have hinverseCastZ : (inverse.toNat : ZMod p.modulus) =
        (inverse : ZMod p.modulus) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hinverse0]
    rw [hinverseCastZ] at hmain
    simpa [a, Int.cast_sub, Int.cast_one, max_eq_left hinverse0] using hmain
  refine ⟨bits, ?_, ?_⟩
  · simp [WF.interpHint, WF.evalArgs, hx.1, a, d, isZero, inverse, bits]
  · mvcgen <;> first
      | exact invValid _ (by assumption)
      | exact targetValid _ (by assumption)
      | exact zeroMulSpec _ (by assumption) _ (by assumption)
      | skip
    rename_i z hz inv hinv _ hmul
    have hzVal := zBitEval z hz
    let product := (z.intBits[0].eval ρ.int * a).toNat
    let quotient := product / p.modulus
    let qBits : Vector Bool quotientExtraBits := Vector.ofFn fun i =>
      quotient.testBit i.val
    refine ⟨qBits, ?_, ?_⟩
    · rfl
    · mvcgen
      rename_i q hq
      have hproduct0 : 0 ≤ z.intBits[0].eval ρ.int * a := by
        rw [hzVal]
        split
        · simpa using hx.1
        · simp
      have hproductEq : (product : Int) =
          z.intBits[0].eval ρ.int * a :=
        Int.toNat_of_nonneg hproduct0
      have hqSmall : quotient < x.bound := by
        dsimp [quotient, product]
        apply (Nat.div_lt_iff_lt_mul p.positive).2
        apply (Int.toNat_lt hproduct0).2
        rw [hzVal]
        split
        · simpa using hx.2
        · simp
          have hp : (0 : Int) < x.bound * p.modulus :=
            lt_of_le_of_lt hx.1 hx.2
          exact hp
      have hxb : x.bound < 2 ^ quotientExtraBits := by omega
      have hqFit : quotient < 2 ^ quotientExtraBits := hqSmall.trans hxb
      have hqWord :
          (Word.eval ρ.bool {
            bitsLE := Vector.ofFn (n := quotientExtraBits) fun i =>
              (Vector.map LC.ofConst qBits)[i.val]
          }).toNat = quotient := by
        simp [Word.eval, BitVec.toNat_ofFnLE, qBits, Nat.ofBits_testBit,
          Nat.mod_eq_of_lt hqFit]
      have hqVal : q.intVal.eval ρ.int = (quotient : Nat) := by
        rw [U.Rel.intVal hq, hqWord]
      constructor
      · simp only [LC.eval_nsmul, nsmul_eq_mul, hqVal]
        change z.intBits[0].eval ρ.int * a =
          (p.modulus : Int) * quotient
        by_cases hzero : isZero
        · have hd0 : d = 0 := hzero
          have hmod : a.toNat % p.modulus = 0 := by simpa [d] using hd0
          have hdecomp := Nat.mod_add_div a.toNat p.modulus
          rw [hmod] at hdecomp
          simp only [zero_add] at hdecomp
          have hproduct : product = a.toNat := by
            simp [product, hzVal, hzero]
          have hquotient : quotient = a.toNat / p.modulus := by
            simp [quotient, hproduct]
          rw [hzVal, if_pos hzero, hquotient]
          simp only [one_mul]
          calc
            a = (a.toNat : Int) := haNat.symm
            _ = (p.modulus : Int) * (a.toNat / p.modulus : Nat) := by
              exact_mod_cast hdecomp.symm
        · have hproduct : product = 0 := by
            simp [product, hzVal, hzero]
          have hquotient : quotient = 0 := by
            simp [quotient, hproduct]
          rw [hzVal, if_neg hzero, hquotient]
          simp
      · have hxZero : Modular.Lazy.evalZMod p x ρ = 0 ↔ isZero := by
          unfold evalZMod
          have haCast : (a : ZMod p.modulus) =
              (a.toNat : ZMod p.modulus) := by
            rw [← Int.cast_natCast]
            exact (congrArg (Int.castRingHom (ZMod p.modulus)) haNat).symm
          change (a : ZMod p.modulus) = 0 ↔ isZero
          rw [haCast, ZMod.natCast_eq_zero_iff]
          simp [isZero, d, Nat.dvd_iff_mod_eq_zero]
        mvcgen
        unfold ZeroTestZModSpec
        rw [hzVal]
        constructor
        · split <;> simp
        · constructor
          · rw [hxZero]
            by_cases hzero : isZero <;> simp [hzero]
          · by_cases hzero : isZero
            · have hxz : evalZMod p x ρ = 0 := hxZero.mpr hzero
              simp [hzero, hxz]
            · have hxz : evalZMod p x ρ ≠ 0 := fun h =>
                hzero (hxZero.mp h)
              simp [hzero, hxz]

end Lazy

end Freigen.F2Z.Examples.Modular
