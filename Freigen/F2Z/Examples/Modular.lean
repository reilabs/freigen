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

end Relaxed

namespace Lazy

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
    ⦃⇓ out => ⌜MulZModSpec p ρ x y out ∧ out.Valid ρ⌝⦄ := by
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

end Lazy

end Freigen.F2Z.Examples.Modular
