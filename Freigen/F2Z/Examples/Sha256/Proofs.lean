import Freigen.F2Z.Examples.Sha256.Model
import Freigen.F2Z.Correctness.U
import Mathlib.Data.Int.Bitwise

namespace Freigen.F2Z.Examples

open Std.Do
open scoped Std.Do

abbrev chBV (u v w : BitVec n) : BitVec n :=
  (u &&& v) ^^^ ((~~~u) &&& w)

abbrev majBV (u v w : BitVec n) : BitVec n :=
  (u &&& v) ^^^ (u &&& w) ^^^ (v &&& w)

private theorem optimized_ch_arith (u v w : BitVec n) :
    (v.toNat : Int) + w.toNat - (u ^^^ v).toNat + (u ^^^ w).toNat =
      2 * ((chBV u v w).toNat : Int) := by
  rw [BitVec.intCast_toNat_eq_sum, BitVec.intCast_toNat_eq_sum,
    BitVec.intCast_toNat_eq_sum, BitVec.intCast_toNat_eq_sum,
    BitVec.intCast_toNat_eq_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [chBV, BitVec.getElem_xor, BitVec.getElem_and,
    BitVec.getElem_not]
  generalize u[i.val] = ub
  generalize v[i.val] = vb
  generalize w[i.val] = wb
  cases ub <;> cases vb <;> cases wb <;> norm_num <;> ring

private theorem optimized_maj_arith (u v w : BitVec n) :
    (u.toNat : Int) + v.toNat + w.toNat - (u ^^^ v ^^^ w).toNat =
      2 * ((majBV u v w).toNat : Int) := by
  rw [BitVec.intCast_toNat_eq_sum, BitVec.intCast_toNat_eq_sum,
    BitVec.intCast_toNat_eq_sum, BitVec.intCast_toNat_eq_sum,
    BitVec.intCast_toNat_eq_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [majBV, BitVec.getElem_xor, BitVec.getElem_and]
  generalize u[i.val] = ub
  generalize v[i.val] = vb
  generalize w[i.val] = wb
  cases ub <;> cases vb <;> cases wb <;> norm_num <;> ring

theorem optimized_ch2_result {u v w uv uw : U n}
    (hu : u.Valid ρ) (hv : v.Valid ρ) (hw : w.Valid ρ)
    (huv : U.Rel ρ uv (Word.eval ρ.bool (u.bits ^^^ v.bits)))
    (huw : U.Rel ρ uw (Word.eval ρ.bool (u.bits ^^^ w.bits))) :
    (v.intVal + w.intVal - uv.intVal + uw.intVal).eval ρ.int =
      2 * ((chBV (u.eval ρ) (v.eval ρ) (w.eval ρ)).toNat : Int) := by
  simp only [LC.eval_add, LC.eval_sub]
  rw [U.intVal_eval_eq_eval_toNat v hv, U.intVal_eval_eq_eval_toNat w hw,
    U.Rel.intVal huv, U.Rel.intVal huw]
  simp only [Word.eval_xor, U.Rel.word_eval (U.Rel.refl hu),
    U.Rel.word_eval (U.Rel.refl hv), U.Rel.word_eval (U.Rel.refl hw)]
  exact optimized_ch_arith (u.eval ρ) (v.eval ρ) (w.eval ρ)

@[spec] theorem optimized_ch2_sound {u v w : U n} (hu : u.Valid ρ)
    (hv : v.Valid ρ) (hw : w.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (U.ch2 u v w)
    ⦃⇓ r => ⌜r.eval ρ.int =
      2 * ((chBV (u.eval ρ) (v.eval ρ) (w.eval ρ)).toNat : Int)⌝⦄ := by
  unfold U.ch2
  mvcgen
  exact optimized_ch2_result hu hv hw (by assumption) (by assumption)

@[spec] theorem optimized_ch2_complete {u v w : U n} (hu : u.Valid ρ)
    (hv : v.Valid ρ) (hw : w.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (U.ch2 u v w)
    ⦃⇓ r => ⌜r.eval ρ.int =
      2 * ((chBV (u.eval ρ) (v.eval ρ) (w.eval ρ)).toNat : Int)⌝⦄ := by
  unfold U.ch2
  mvcgen
  exact optimized_ch2_result hu hv hw (by assumption) (by assumption)

theorem optimized_maj2_result {u v w uvw : U n}
    (hu : u.Valid ρ) (hv : v.Valid ρ) (hw : w.Valid ρ)
    (huvw : U.Rel ρ uvw (Word.eval ρ.bool (u.bits ^^^ v.bits ^^^ w.bits))) :
    (u.intVal + v.intVal + w.intVal - uvw.intVal).eval ρ.int =
      2 * ((majBV (u.eval ρ) (v.eval ρ) (w.eval ρ)).toNat : Int) := by
  simp only [LC.eval_add, LC.eval_sub]
  rw [U.intVal_eval_eq_eval_toNat u hu, U.intVal_eval_eq_eval_toNat v hv,
    U.intVal_eval_eq_eval_toNat w hw, U.Rel.intVal huvw]
  simp only [Word.eval_xor, U.Rel.word_eval (U.Rel.refl hu),
    U.Rel.word_eval (U.Rel.refl hv), U.Rel.word_eval (U.Rel.refl hw)]
  exact optimized_maj_arith (u.eval ρ) (v.eval ρ) (w.eval ρ)

@[spec] theorem optimized_maj2_sound {u v w : U n} (hu : u.Valid ρ)
    (hv : v.Valid ρ) (hw : w.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (U.maj2 u v w)
    ⦃⇓ r => ⌜r.eval ρ.int =
      2 * ((majBV (u.eval ρ) (v.eval ρ) (w.eval ρ)).toNat : Int)⌝⦄ := by
  unfold U.maj2
  mvcgen
  exact optimized_maj2_result hu hv hw (by assumption)

@[spec] theorem optimized_maj2_complete {u v w : U n} (hu : u.Valid ρ)
    (hv : v.Valid ρ) (hw : w.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (U.maj2 u v w)
    ⦃⇓ r => ⌜r.eval ρ.int =
      2 * ((majBV (u.eval ρ) (v.eval ρ) (w.eval ρ)).toNat : Int)⌝⦄ := by
  unfold U.maj2
  mvcgen
  exact optimized_maj2_result hu hv hw (by assumption)

theorem optimized_ch2_wf :
    WF.GadgetSpec
      (fun lv rv (l r : U n × U n × U n) =>
        U.WFRel lv rv l.1 r.1 ∧ U.WFRel lv rv l.2.1 r.2.1 ∧
          U.WFRel lv rv l.2.2 r.2.2)
      (fun x => U.ch2 x.1 x.2.1 x.2.2)
      (fun lv rv l r => WF.LCEq lv.int rv.int l r) := by
  unfold WF.GadgetSpec
  intro left right
  unfold U.ch2
  wfgen' using [U.fromWord_wf_rel]
  all_goals first
    | exact (Word.WFRel.xor (U.WFRel.bits (by grind))
        (U.WFRel.bits (by grind))) i
    | (unfold WF.LCEq; simp only [U.WFRel, WF.LCEq, LC.eval_add,
        LC.eval_sub] at *; grind)

theorem optimized_maj2_wf :
    WF.GadgetSpec
      (fun lv rv (l r : U n × U n × U n) =>
        U.WFRel lv rv l.1 r.1 ∧ U.WFRel lv rv l.2.1 r.2.1 ∧
          U.WFRel lv rv l.2.2 r.2.2)
      (fun x => U.maj2 x.1 x.2.1 x.2.2)
      (fun lv rv l r => WF.LCEq lv.int rv.int l r) := by
  unfold WF.GadgetSpec
  intro left right
  unfold U.maj2
  wfgen' using [U.fromWord_wf_rel]
  exact (Word.WFRel.xor
    (Word.WFRel.xor (U.WFRel.bits (by grind))
      (U.WFRel.bits (by grind))) (U.WFRel.bits (by grind))) i

@[spec] theorem optimized_fromDoubledInt35_sound {x : LC ℤ} :
    ⦃⌜True⌝⦄ Sound.interp ρ (U.fromDoubledInt35 x)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      2 * out.intVal.eval ρ.int = x.eval ρ.int⌝⦄ := by
  mvcgen [U.fromDoubledInt35]
  intro b
  mvcgen
  rename_i r h hass
  refine ⟨h.1, ?_⟩
  simp only [LC.eval_zero, zero_mul, LC.eval_sub, two_nsmul,
    LC.eval_add] at hass
  omega

@[spec] theorem optimized_fromDoubledInt35_complete {x : LC ℤ} (q : Nat)
    (hx : x.eval ρ.int = 2 * q) (hq : q < 2 ^ 35) :
    ⦃⌜True⌝⦄ Complete.interp ρ (U.fromDoubledInt35 x)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      2 * out.intVal.eval ρ.int = x.eval ρ.int⌝⦄ := by
  mvcgen [U.fromDoubledInt35]
  simp only [WF.interpHint, WF.evalArgs, hx]
  rw [show (2 * (q : Int)) = Int.ofNat (2 * q) by norm_num [Nat.cast_mul]]
  simp only [Free.interp_pure, Option.pure_def, Option.some.injEq,
    exists_eq_left', Vector.map_ofFn]
  norm_num
  simp only [Function.comp_def]
  have ht :
      ⦃⌜True⌝⦄ (do
        let r ← Complete.interp ρ (U.fromWord
          { bitsLE := Vector.ofFn (n := 35) fun i => LC.ofConst (q.testBit i) })
        Complete.interp ρ (assertR1C 0 0 (x - 2 • r.intVal))
        pure r)
      ⦃⇓ out => ⌜out.Valid ρ ∧ out.intVal.eval ρ.int = q⌝⦄ := by
    apply Triple.bind (Q := fun r => ⌜r.bits =
      { bitsLE := Vector.ofFn (n := 35) fun i => LC.ofConst (q.testBit i) } ∧
        r.Valid ρ⌝)
    case hx => exact U.fromWord_complete
    case hf =>
      intro r
      mvcgen -trivial
      rename_i h
      have hbits : r.bits.evalZ ρ = q := by
        simp only [Word.evalZ, h.1, Vector.getElem_ofFn, Fin.getElem_fin]
        have hmod := Nat.mod_eq_of_lt hq
        simpa [Nat.ofBits_testBit] using congrArg Int.ofNat hmod
      have hintVal : r.intVal.eval ρ.int = (q : Int) :=
        (U.eval_intVal_eq_evalZ r h.2).trans (by simpa using hbits)
      constructor
      · simp [LC.eval_zero, LC.eval_sub, LC.eval_nsmul, hx, hintVal]
      · exact ⟨h.2, hintVal⟩
  rw [Triple.iff] at ht
  simp only [SPred.entails_nil, SPred.down_pure_nil] at ht
  exact ht True.intro

theorem optimized_fromDoubledInt35_wf_full :
    WF.GadgetSpec
      (fun lv rv (l r : LC ℤ) => WF.LCEq lv.int rv.int l r)
      U.fromDoubledInt35
      (fun lv rv l r =>
        (∀ i : Fin 35, WF.LCEq lv.bool rv.bool
          l.bits.bitsLE[i] r.bits.bitsLE[i]) ∧
        (∀ i : Fin 35, WF.LCEq lv.int rv.int l.intBits[i] r.intBits[i]) ∧
        WF.LCEq lv.int rv.int l.intVal r.intVal) := by
  wfgen' using [U.fromWord_wf_full] unfold [U.fromDoubledInt35]
  case vc1 hrel =>
    rcases hrel with ⟨_, values, _, _, hleft, hright⟩
    exact (hleft i.val i.isLt).trans (hright i.val i.isLt).symm
  case vc2 h =>
    unfold WF.LCEq at h
    simp only [WF.evalArgs]
    rw [h]
  case vc3 h =>
    unfold WF.ArgsEq WF.LCEq at *
    simpa only [WF.evalArgs] using congrArg (fun x => h![x]) h

@[spec] theorem optimized_fromDoubledInt34_sound {x : LC ℤ} :
    ⦃⌜True⌝⦄ Sound.interp ρ (U.fromDoubledInt34 x)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      2 * out.intVal.eval ρ.int = x.eval ρ.int⌝⦄ := by
  mvcgen [U.fromDoubledInt34]
  intro b
  mvcgen
  rename_i r h hass
  refine ⟨h.1, ?_⟩
  simp only [LC.eval_zero, zero_mul, LC.eval_sub, two_nsmul,
    LC.eval_add] at hass
  omega

@[spec] theorem optimized_fromDoubledInt34_complete {x : LC ℤ} (q : Nat)
    (hx : x.eval ρ.int = 2 * q) (hq : q < 2 ^ 34) :
    ⦃⌜True⌝⦄ Complete.interp ρ (U.fromDoubledInt34 x)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      2 * out.intVal.eval ρ.int = x.eval ρ.int⌝⦄ := by
  mvcgen [U.fromDoubledInt34]
  simp only [WF.interpHint, WF.evalArgs, hx]
  rw [show (2 * (q : Int)) = Int.ofNat (2 * q) by norm_num [Nat.cast_mul]]
  simp only [Free.interp_pure, Option.pure_def, Option.some.injEq,
    exists_eq_left', Vector.map_ofFn]
  norm_num
  simp only [Function.comp_def]
  have ht :
      ⦃⌜True⌝⦄ (do
        let r ← Complete.interp ρ (U.fromWord
          { bitsLE := Vector.ofFn (n := 34) fun i => LC.ofConst (q.testBit i) })
        Complete.interp ρ (assertR1C 0 0 (x - 2 • r.intVal))
        pure r)
      ⦃⇓ out => ⌜out.Valid ρ ∧ out.intVal.eval ρ.int = q⌝⦄ := by
    apply Triple.bind (Q := fun r => ⌜r.bits =
      { bitsLE := Vector.ofFn (n := 34) fun i => LC.ofConst (q.testBit i) } ∧
        r.Valid ρ⌝)
    case hx => exact U.fromWord_complete
    case hf =>
      intro r
      mvcgen -trivial
      rename_i h
      have hbits : r.bits.evalZ ρ = q := by
        simp only [Word.evalZ, h.1, Vector.getElem_ofFn, Fin.getElem_fin]
        have hmod := Nat.mod_eq_of_lt hq
        simpa [Nat.ofBits_testBit] using congrArg Int.ofNat hmod
      have hintVal : r.intVal.eval ρ.int = (q : Int) :=
        (U.eval_intVal_eq_evalZ r h.2).trans (by simpa using hbits)
      constructor
      · simp [LC.eval_zero, LC.eval_sub, LC.eval_nsmul, hx, hintVal]
      · exact ⟨h.2, hintVal⟩
  rw [Triple.iff] at ht
  simp only [SPred.entails_nil, SPred.down_pure_nil] at ht
  exact ht True.intro

theorem optimized_fromDoubledInt34_wf_full :
    WF.GadgetSpec
      (fun lv rv (l r : LC ℤ) => WF.LCEq lv.int rv.int l r)
      U.fromDoubledInt34
      (fun lv rv l r =>
        (∀ i : Fin 34, WF.LCEq lv.bool rv.bool
          l.bits.bitsLE[i] r.bits.bitsLE[i]) ∧
        (∀ i : Fin 34, WF.LCEq lv.int rv.int l.intBits[i] r.intBits[i]) ∧
        WF.LCEq lv.int rv.int l.intVal r.intVal) := by
  wfgen' using [U.fromWord_wf_full] unfold [U.fromDoubledInt34]
  case vc1 hrel =>
    rcases hrel with ⟨_, values, _, _, hleft, hright⟩
    exact (hleft i.val i.isLt).trans (hright i.val i.isLt).symm
  case vc2 h =>
    unfold WF.LCEq at h
    simp only [WF.evalArgs]
    rw [h]
  case vc3 h =>
    unfold WF.ArgsEq WF.LCEq at *
    simpa only [WF.evalArgs] using congrArg (fun x => h![x]) h

@[spec] theorem optimized_fromDoubledInt36_sound {x : LC ℤ} :
    ⦃⌜True⌝⦄ Sound.interp ρ (U.fromDoubledInt36 x)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      2 * out.intVal.eval ρ.int = x.eval ρ.int⌝⦄ := by
  mvcgen [U.fromDoubledInt36]
  intro b
  mvcgen
  rename_i r h hass
  refine ⟨h.1, ?_⟩
  simp only [LC.eval_zero, zero_mul, LC.eval_sub, two_nsmul,
    LC.eval_add] at hass
  omega

@[spec] theorem optimized_fromDoubledInt36_complete {x : LC ℤ} (q : Nat)
    (hx : x.eval ρ.int = 2 * q) (hq : q < 2 ^ 36) :
    ⦃⌜True⌝⦄ Complete.interp ρ (U.fromDoubledInt36 x)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      2 * out.intVal.eval ρ.int = x.eval ρ.int⌝⦄ := by
  mvcgen [U.fromDoubledInt36]
  simp only [WF.interpHint, WF.evalArgs, hx]
  rw [show (2 * (q : Int)) = Int.ofNat (2 * q) by norm_num [Nat.cast_mul]]
  simp only [Free.interp_pure, Option.pure_def, Option.some.injEq,
    exists_eq_left', Vector.map_ofFn]
  norm_num
  simp only [Function.comp_def]
  have ht :
      ⦃⌜True⌝⦄ (do
        let r ← Complete.interp ρ (U.fromWord
          { bitsLE := Vector.ofFn (n := 36) fun i => LC.ofConst (q.testBit i) })
        Complete.interp ρ (assertR1C 0 0 (x - 2 • r.intVal))
        pure r)
      ⦃⇓ out => ⌜out.Valid ρ ∧ out.intVal.eval ρ.int = q⌝⦄ := by
    apply Triple.bind (Q := fun r => ⌜r.bits =
      { bitsLE := Vector.ofFn (n := 36) fun i => LC.ofConst (q.testBit i) } ∧
        r.Valid ρ⌝)
    case hx => exact U.fromWord_complete
    case hf =>
      intro r
      mvcgen -trivial
      rename_i h
      have hbits : r.bits.evalZ ρ = q := by
        simp only [Word.evalZ, h.1, Vector.getElem_ofFn, Fin.getElem_fin]
        have hmod := Nat.mod_eq_of_lt hq
        simpa [Nat.ofBits_testBit] using congrArg Int.ofNat hmod
      have hintVal : r.intVal.eval ρ.int = (q : Int) :=
        (U.eval_intVal_eq_evalZ r h.2).trans (by simpa using hbits)
      constructor
      · simp [LC.eval_zero, LC.eval_sub, LC.eval_nsmul, hx, hintVal]
      · exact ⟨h.2, hintVal⟩
  rw [Triple.iff] at ht
  simp only [SPred.entails_nil, SPred.down_pure_nil] at ht
  exact ht True.intro

theorem optimized_fromDoubledInt36_wf_full :
    WF.GadgetSpec
      (fun lv rv (l r : LC ℤ) => WF.LCEq lv.int rv.int l r)
      U.fromDoubledInt36
      (fun lv rv l r =>
        (∀ i : Fin 36, WF.LCEq lv.bool rv.bool
          l.bits.bitsLE[i] r.bits.bitsLE[i]) ∧
        (∀ i : Fin 36, WF.LCEq lv.int rv.int l.intBits[i] r.intBits[i]) ∧
        WF.LCEq lv.int rv.int l.intVal r.intVal) := by
  wfgen' using [U.fromWord_wf_full] unfold [U.fromDoubledInt36]
  case vc1 hrel =>
    rcases hrel with ⟨_, values, _, _, hleft, hright⟩
    exact (hleft i.val i.isLt).trans (hright i.val i.isLt).symm
  case vc2 h =>
    unfold WF.LCEq at h
    simp only [WF.evalArgs]
    rw [h]
  case vc3 h =>
    unfold WF.ArgsEq WF.LCEq at *
    simpa only [WF.evalArgs] using congrArg (fun x => h![x]) h

theorem optimized_sum5Doubled1_result {a b c d e : U 32} {half : U 35} {x2 : LC ℤ}
    {x : BitVec 32} (ha : a.Valid ρ) (hb : b.Valid ρ) (hc : c.Valid ρ)
    (hd : d.Valid ρ) (he : e.Valid ρ)
    (hx : x2.eval ρ.int = 2 * (x.toNat : Int))
    (hhalf : half.Valid ρ ∧ 2 * half.intVal.eval ρ.int =
      (2 • (#[a, b, c, d, e].map (·.intVal) |>.sum) + #[x2].sum).eval ρ.int) :
    U.Rel ρ (half.takeLE 32 (by omega))
      (a.eval ρ + b.eval ρ + c.eval ρ + d.eval ρ + e.eval ρ + x) := by
  let q := (a.eval ρ).toNat + (b.eval ρ).toNat + (c.eval ρ).toNat +
    (d.eval ρ).toNat + (e.eval ρ).toNat + x.toNat
  have hhalf2 : half.intVal.eval ρ.int = q := by
    have htotal :
        (2 • (#[a, b, c, d, e].map (·.intVal) |>.sum) + #[x2].sum).eval ρ.int =
          2 * q := by
      rw [LC.eval_add, LC.eval_nsmul, LC.eval_array_sum, LC.eval_array_sum]
      norm_num [U.intVal_eval_eq_eval_toNat a ha,
        U.intVal_eval_eq_eval_toNat b hb, U.intVal_eval_eq_eval_toNat c hc,
        U.intVal_eval_eq_eval_toNat d hd, U.intVal_eval_eq_eval_toNat e he, hx]
      dsimp [q]
      omega
    rw [htotal] at hhalf
    omega
  have hhalfNat : (half.intVal.eval ρ.int).toNat = q := by
    rw [hhalf2]
    simp
  refine ⟨U.takeLE_valid half hhalf.1 (by omega), ?_⟩
  rw [U.takeLE_eval half hhalf.1 (by omega), hhalfNat]
  dsimp [q]
  simp [BitVec.ofNat_add]

@[spec] theorem optimized_sum5Doubled1_sound {a b c d e : U 32} {x2 : LC ℤ}
    {x : BitVec 32} (ha : a.Valid ρ) (hb : b.Valid ρ) (hc : c.Valid ρ)
    (hd : d.Valid ρ) (he : e.Valid ρ)
    (hx : x2.eval ρ.int = 2 * (x.toNat : Int)) :
    ⦃⌜True⌝⦄ Sound.interp ρ (U.sum5Doubled1 a b c d e x2)
    ⦃⇓ out => ⌜U.Rel ρ out
      (a.eval ρ + b.eval ρ + c.eval ρ + d.eval ρ + e.eval ρ + x)⌝⦄ := by
  unfold U.sum5Doubled1 U.sumDoubled32
  rw [Sound.interp_bind]
  apply Triple.bind (Q := fun half => ⌜half.Valid ρ ∧ 2 * half.intVal.eval ρ.int =
    (2 • (#[a, b, c, d, e].map (·.intVal) |>.sum) + #[x2].sum).eval ρ.int⌝)
  case hx => exact optimized_fromDoubledInt35_sound
  case hf =>
    intro half
    mvcgen -trivial
    exact optimized_sum5Doubled1_result ha hb hc hd he hx (by assumption)

@[spec] theorem optimized_sum5Doubled1_complete {a b c d e : U 32} {x2 : LC ℤ}
    {x : BitVec 32} (ha : a.Valid ρ) (hb : b.Valid ρ) (hc : c.Valid ρ)
    (hd : d.Valid ρ) (he : e.Valid ρ)
    (hx : x2.eval ρ.int = 2 * (x.toNat : Int)) :
    ⦃⌜True⌝⦄ Complete.interp ρ (U.sum5Doubled1 a b c d e x2)
    ⦃⇓ out => ⌜U.Rel ρ out
      (a.eval ρ + b.eval ρ + c.eval ρ + d.eval ρ + e.eval ρ + x)⌝⦄ := by
  let total := 2 • (#[a, b, c, d, e].map (·.intVal) |>.sum) + #[x2].sum
  have htotal : total.eval ρ.int = 2 * ((a.eval ρ).toNat +
      (b.eval ρ).toNat + (c.eval ρ).toNat + (d.eval ρ).toNat +
      (e.eval ρ).toNat + x.toNat) := by
    dsimp [total]
    rw [LC.eval_add, LC.eval_nsmul, LC.eval_array_sum, LC.eval_array_sum]
    norm_num [U.intVal_eval_eq_eval_toNat a ha,
      U.intVal_eval_eq_eval_toNat b hb, U.intVal_eval_eq_eval_toNat c hc,
      U.intVal_eval_eq_eval_toNat d hd, U.intVal_eval_eq_eval_toNat e he, hx]
    omega
  have h35 : (a.eval ρ).toNat + (b.eval ρ).toNat +
      (c.eval ρ).toNat + (d.eval ρ).toNat + (e.eval ρ).toNat +
      x.toNat < 2 ^ 35 := by
    have ha' := (a.eval ρ).isLt
    have hb' := (b.eval ρ).isLt
    have hc' := (c.eval ρ).isLt
    have hd' := (d.eval ρ).isLt
    have he' := (e.eval ρ).isLt
    have hx' := x.isLt
    norm_num at ha' hb' hc' hd' he' hx' ⊢
    omega
  unfold U.sum5Doubled1 U.sumDoubled32
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun half => ⌜half.Valid ρ ∧
    2 * half.intVal.eval ρ.int = total.eval ρ.int⌝)
  case hx => exact optimized_fromDoubledInt35_complete _ htotal h35
  case hf =>
    intro half
    mvcgen -trivial
    exact optimized_sum5Doubled1_result ha hb hc hd he hx (by assumption)

theorem optimized_sum5Doubled2_result {a b c d e : U 32} {half : U 35}
    {x2 y2 : LC ℤ} {x y : BitVec 32}
    (ha : a.Valid ρ) (hb : b.Valid ρ) (hc : c.Valid ρ)
    (hd : d.Valid ρ) (he : e.Valid ρ)
    (hx : x2.eval ρ.int = 2 * (x.toNat : Int))
    (hy : y2.eval ρ.int = 2 * (y.toNat : Int))
    (hhalf : half.Valid ρ ∧ 2 * half.intVal.eval ρ.int =
      (2 • (#[a, b, c, d, e].map (·.intVal) |>.sum) + #[x2, y2].sum).eval ρ.int) :
    U.Rel ρ (half.takeLE 32 (by omega))
      (a.eval ρ + b.eval ρ + c.eval ρ + d.eval ρ + e.eval ρ + x + y) := by
  let q := (a.eval ρ).toNat + (b.eval ρ).toNat + (c.eval ρ).toNat +
    (d.eval ρ).toNat + (e.eval ρ).toNat + x.toNat + y.toNat
  have hhalf2 : half.intVal.eval ρ.int = q := by
    have htotal :
        (2 • (#[a, b, c, d, e].map (·.intVal) |>.sum) + #[x2, y2].sum).eval ρ.int =
          2 * q := by
      rw [LC.eval_add, LC.eval_nsmul, LC.eval_array_sum, LC.eval_array_sum]
      norm_num [U.intVal_eval_eq_eval_toNat a ha,
        U.intVal_eval_eq_eval_toNat b hb, U.intVal_eval_eq_eval_toNat c hc,
        U.intVal_eval_eq_eval_toNat d hd, U.intVal_eval_eq_eval_toNat e he,
        hx, hy]
      dsimp [q]
      omega
    rw [htotal] at hhalf
    omega
  have hhalfNat : (half.intVal.eval ρ.int).toNat = q := by
    rw [hhalf2]
    simp
  refine ⟨U.takeLE_valid half hhalf.1 (by omega), ?_⟩
  rw [U.takeLE_eval half hhalf.1 (by omega), hhalfNat]
  dsimp [q]
  simp [BitVec.ofNat_add]

@[spec] theorem optimized_sum5Doubled2_sound {a b c d e : U 32} {x2 y2 : LC ℤ}
    {x y : BitVec 32} (ha : a.Valid ρ) (hb : b.Valid ρ) (hc : c.Valid ρ)
    (hd : d.Valid ρ) (he : e.Valid ρ)
    (hx : x2.eval ρ.int = 2 * (x.toNat : Int))
    (hy : y2.eval ρ.int = 2 * (y.toNat : Int)) :
    ⦃⌜True⌝⦄ Sound.interp ρ (U.sum5Doubled2 a b c d e x2 y2)
    ⦃⇓ out => ⌜U.Rel ρ out
      (a.eval ρ + b.eval ρ + c.eval ρ + d.eval ρ + e.eval ρ + x + y)⌝⦄ := by
  unfold U.sum5Doubled2 U.sumDoubled32
  rw [Sound.interp_bind]
  apply Triple.bind (Q := fun half => ⌜half.Valid ρ ∧ 2 * half.intVal.eval ρ.int =
    (2 • (#[a, b, c, d, e].map (·.intVal) |>.sum) + #[x2, y2].sum).eval ρ.int⌝)
  case hx => exact optimized_fromDoubledInt35_sound
  case hf =>
    intro half
    mvcgen -trivial
    exact optimized_sum5Doubled2_result ha hb hc hd he hx hy (by assumption)

theorem optimized_sum5Doubled1_wf :
    WF.GadgetSpec
      (fun lv rv (l r : U 32 × U 32 × U 32 × U 32 × U 32 × LC ℤ) =>
        U.WFRel lv rv l.1 r.1 ∧ U.WFRel lv rv l.2.1 r.2.1 ∧
        U.WFRel lv rv l.2.2.1 r.2.2.1 ∧ U.WFRel lv rv l.2.2.2.1 r.2.2.2.1 ∧
        U.WFRel lv rv l.2.2.2.2.1 r.2.2.2.2.1 ∧
        WF.LCEq lv.int rv.int l.2.2.2.2.2 r.2.2.2.2.2)
      (fun z => U.sum5Doubled1 z.1 z.2.1 z.2.2.1 z.2.2.2.1
        z.2.2.2.2.1 z.2.2.2.2.2) U.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold U.sum5Doubled1 U.sumDoubled32
  apply WF.GadgetSpec.bind_rule optimized_fromDoubledInt35_wf_full
  · intro lv rv h
    unfold WF.LCEq at h ⊢
    simp only [LC.eval_add, LC.eval_nsmul, LC.eval_array_sum]
    simp only [U.WFRel, WF.LCEq] at h
    norm_num
    grind
  · intro A outL outR hout
    apply WF.Rel.pure
    intro lv rv hA
    have h := hout lv rv hA
    constructor
    · apply WF.LCEq.uIntVal
      intro i
      simpa [U.takeLE, Fin.getElem_fin] using h.2.2.1 (i.castLE (by omega))
    · intro i
      simpa [U.takeLE, Fin.getElem_fin] using h.2.1 (i.castLE (by omega))

theorem optimized_sum5Doubled2_wf :
    WF.GadgetSpec
      (fun lv rv (l r : U 32 × U 32 × U 32 × U 32 × U 32 × LC ℤ × LC ℤ) =>
        U.WFRel lv rv l.1 r.1 ∧ U.WFRel lv rv l.2.1 r.2.1 ∧
        U.WFRel lv rv l.2.2.1 r.2.2.1 ∧ U.WFRel lv rv l.2.2.2.1 r.2.2.2.1 ∧
        U.WFRel lv rv l.2.2.2.2.1 r.2.2.2.2.1 ∧
        WF.LCEq lv.int rv.int l.2.2.2.2.2.1 r.2.2.2.2.2.1 ∧
        WF.LCEq lv.int rv.int l.2.2.2.2.2.2 r.2.2.2.2.2.2)
      (fun z => U.sum5Doubled2 z.1 z.2.1 z.2.2.1 z.2.2.2.1
        z.2.2.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2) U.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold U.sum5Doubled2 U.sumDoubled32
  apply WF.GadgetSpec.bind_rule optimized_fromDoubledInt35_wf_full
  · intro lv rv h
    unfold WF.LCEq at h ⊢
    simp only [LC.eval_add, LC.eval_nsmul, LC.eval_array_sum]
    simp only [U.WFRel, WF.LCEq] at h
    norm_num
    grind
  · intro A outL outR hout
    apply WF.Rel.pure
    intro lv rv hA
    have h := hout lv rv hA
    constructor
    · apply WF.LCEq.uIntVal
      intro i
      simpa [U.takeLE, Fin.getElem_fin] using h.2.2.1 (i.castLE (by omega))
    · intro i
      simpa [U.takeLE, Fin.getElem_fin] using h.2.1 (i.castLE (by omega))

@[spec] theorem optimized_sum5Doubled2_complete {a b c d e : U 32} {x2 y2 : LC ℤ}
    {x y : BitVec 32} (ha : a.Valid ρ) (hb : b.Valid ρ) (hc : c.Valid ρ)
    (hd : d.Valid ρ) (he : e.Valid ρ)
    (hx : x2.eval ρ.int = 2 * (x.toNat : Int))
    (hy : y2.eval ρ.int = 2 * (y.toNat : Int)) :
    ⦃⌜True⌝⦄ Complete.interp ρ (U.sum5Doubled2 a b c d e x2 y2)
    ⦃⇓ out => ⌜U.Rel ρ out
      (a.eval ρ + b.eval ρ + c.eval ρ + d.eval ρ + e.eval ρ + x + y)⌝⦄ := by
  let total := 2 • (#[a, b, c, d, e].map (·.intVal) |>.sum) + #[x2, y2].sum
  have htotal : total.eval ρ.int = 2 * ((a.eval ρ).toNat +
      (b.eval ρ).toNat + (c.eval ρ).toNat + (d.eval ρ).toNat +
      (e.eval ρ).toNat + x.toNat + y.toNat) := by
    dsimp [total]
    rw [LC.eval_add, LC.eval_nsmul, LC.eval_array_sum, LC.eval_array_sum]
    norm_num [U.intVal_eval_eq_eval_toNat a ha,
      U.intVal_eval_eq_eval_toNat b hb, U.intVal_eval_eq_eval_toNat c hc,
      U.intVal_eval_eq_eval_toNat d hd, U.intVal_eval_eq_eval_toNat e he,
      hx, hy]
    omega
  have h35 : (a.eval ρ).toNat + (b.eval ρ).toNat +
      (c.eval ρ).toNat + (d.eval ρ).toNat + (e.eval ρ).toNat +
      x.toNat + y.toNat < 2 ^ 35 := by
    have ha' := (a.eval ρ).isLt
    have hb' := (b.eval ρ).isLt
    have hc' := (c.eval ρ).isLt
    have hd' := (d.eval ρ).isLt
    have he' := (e.eval ρ).isLt
    have hx' := x.isLt
    have hy' := y.isLt
    norm_num at ha' hb' hc' hd' he' hx' hy' ⊢
    omega
  unfold U.sum5Doubled2 U.sumDoubled32
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun half => ⌜half.Valid ρ ∧
    2 * half.intVal.eval ρ.int = total.eval ρ.int⌝)
  case hx => exact optimized_fromDoubledInt35_complete _ htotal h35
  case hf =>
    intro half
    mvcgen -trivial
    exact optimized_sum5Doubled2_result ha hb hc hd he hx hy (by assumption)

theorem optimized_sum8Doubled1_result {a b c d e f g h : U 32}
    {half : U 36} {x2 : LC ℤ} {x : BitVec 32}
    (ha : a.Valid ρ) (hb : b.Valid ρ) (hc : c.Valid ρ) (hd : d.Valid ρ)
    (he : e.Valid ρ) (hf : f.Valid ρ) (hg : g.Valid ρ) (hh : h.Valid ρ)
    (hx : x2.eval ρ.int = 2 * (x.toNat : Int))
    (hhalf : half.Valid ρ ∧ 2 * half.intVal.eval ρ.int =
      (2 • (#[a, b, c, d, e, f, g, h].map (·.intVal) |>.sum) + x2).eval ρ.int) :
    U.Rel ρ (half.takeLE 32 (by omega))
      (a.eval ρ + b.eval ρ + c.eval ρ + d.eval ρ + e.eval ρ + f.eval ρ +
        g.eval ρ + h.eval ρ + x) := by
  let q := (a.eval ρ).toNat + (b.eval ρ).toNat + (c.eval ρ).toNat +
    (d.eval ρ).toNat + (e.eval ρ).toNat + (f.eval ρ).toNat +
    (g.eval ρ).toNat + (h.eval ρ).toNat + x.toNat
  have hhalf2 : half.intVal.eval ρ.int = q := by
    have htotal :
        (2 • (#[a, b, c, d, e, f, g, h].map (·.intVal) |>.sum) + x2).eval ρ.int =
          2 * q := by
      rw [LC.eval_add, LC.eval_nsmul, LC.eval_array_sum]
      norm_num [U.intVal_eval_eq_eval_toNat a ha,
        U.intVal_eval_eq_eval_toNat b hb, U.intVal_eval_eq_eval_toNat c hc,
        U.intVal_eval_eq_eval_toNat d hd, U.intVal_eval_eq_eval_toNat e he,
        U.intVal_eval_eq_eval_toNat f hf, U.intVal_eval_eq_eval_toNat g hg,
        U.intVal_eval_eq_eval_toNat h hh, hx]
      dsimp [q]
      omega
    rw [htotal] at hhalf
    omega
  have hhalfNat : (half.intVal.eval ρ.int).toNat = q := by
    rw [hhalf2]
    simp
  refine ⟨U.takeLE_valid half hhalf.1 (by omega), ?_⟩
  rw [U.takeLE_eval half hhalf.1 (by omega), hhalfNat]
  dsimp [q]
  simp [BitVec.ofNat_add]

@[spec] theorem optimized_sum8Doubled1_sound {a b c d e f g h : U 32}
    {x2 : LC ℤ} {x : BitVec 32}
    (ha : a.Valid ρ) (hb : b.Valid ρ) (hc : c.Valid ρ) (hd : d.Valid ρ)
    (he : e.Valid ρ) (hf : f.Valid ρ) (hg : g.Valid ρ) (hh : h.Valid ρ)
    (hx : x2.eval ρ.int = 2 * (x.toNat : Int)) :
    ⦃⌜True⌝⦄ Sound.interp ρ (U.sum8Doubled1 a b c d e f g h x2)
    ⦃⇓ out => ⌜U.Rel ρ out
      (a.eval ρ + b.eval ρ + c.eval ρ + d.eval ρ + e.eval ρ + f.eval ρ +
        g.eval ρ + h.eval ρ + x)⌝⦄ := by
  unfold U.sum8Doubled1
  rw [Sound.interp_bind]
  apply Triple.bind (Q := fun half => ⌜half.Valid ρ ∧
    2 * half.intVal.eval ρ.int =
      (2 • (#[a, b, c, d, e, f, g, h].map (·.intVal) |>.sum) + x2).eval ρ.int⌝)
  case hx => exact optimized_fromDoubledInt36_sound
  case hf =>
    intro half
    mvcgen -trivial
    exact optimized_sum8Doubled1_result ha hb hc hd he hf hg hh hx (by assumption)

@[spec] theorem optimized_sum8Doubled1_complete {a b c d e f g h : U 32}
    {x2 : LC ℤ} {x : BitVec 32}
    (ha : a.Valid ρ) (hb : b.Valid ρ) (hc : c.Valid ρ) (hd : d.Valid ρ)
    (he : e.Valid ρ) (hf : f.Valid ρ) (hg : g.Valid ρ) (hh : h.Valid ρ)
    (hx : x2.eval ρ.int = 2 * (x.toNat : Int)) :
    ⦃⌜True⌝⦄ Complete.interp ρ (U.sum8Doubled1 a b c d e f g h x2)
    ⦃⇓ out => ⌜U.Rel ρ out
      (a.eval ρ + b.eval ρ + c.eval ρ + d.eval ρ + e.eval ρ + f.eval ρ +
        g.eval ρ + h.eval ρ + x)⌝⦄ := by
  let q := (a.eval ρ).toNat + (b.eval ρ).toNat + (c.eval ρ).toNat +
    (d.eval ρ).toNat + (e.eval ρ).toNat + (f.eval ρ).toNat +
    (g.eval ρ).toNat + (h.eval ρ).toNat + x.toNat
  let total := 2 • (#[a, b, c, d, e, f, g, h].map (·.intVal) |>.sum) + x2
  have htotal : total.eval ρ.int = 2 * q := by
    dsimp [total]
    rw [LC.eval_add, LC.eval_nsmul, LC.eval_array_sum]
    norm_num [U.intVal_eval_eq_eval_toNat a ha,
      U.intVal_eval_eq_eval_toNat b hb, U.intVal_eval_eq_eval_toNat c hc,
      U.intVal_eval_eq_eval_toNat d hd, U.intVal_eval_eq_eval_toNat e he,
      U.intVal_eval_eq_eval_toNat f hf, U.intVal_eval_eq_eval_toNat g hg,
      U.intVal_eval_eq_eval_toNat h hh, hx]
    dsimp [q]
    omega
  have h36 : q < 2^36 := by
    have ha' := (a.eval ρ).isLt
    have hb' := (b.eval ρ).isLt
    have hc' := (c.eval ρ).isLt
    have hd' := (d.eval ρ).isLt
    have he' := (e.eval ρ).isLt
    have hf' := (f.eval ρ).isLt
    have hg' := (g.eval ρ).isLt
    have hh' := (h.eval ρ).isLt
    have hx' := x.isLt
    dsimp [q]
    norm_num at ha' hb' hc' hd' he' hf' hg' hh' hx' ⊢
    omega
  unfold U.sum8Doubled1
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun half => ⌜half.Valid ρ ∧
    2 * half.intVal.eval ρ.int = total.eval ρ.int⌝)
  case hx => exact optimized_fromDoubledInt36_complete q htotal h36
  case hf =>
    intro half
    mvcgen -trivial
    exact optimized_sum8Doubled1_result ha hb hc hd he hf hg hh hx (by assumption)

theorem optimized_sum9Doubled1_result {a b c d e f g h i : U 32}
    {half : U 36} {x2 : LC ℤ} {x : BitVec 32}
    (ha : a.Valid ρ) (hb : b.Valid ρ) (hc : c.Valid ρ) (hd : d.Valid ρ)
    (he : e.Valid ρ) (hf : f.Valid ρ) (hg : g.Valid ρ) (hh : h.Valid ρ)
    (hi : i.Valid ρ) (hx : x2.eval ρ.int = 2 * (x.toNat : Int))
    (hhalf : half.Valid ρ ∧ 2 * half.intVal.eval ρ.int =
      (2 • (#[a, b, c, d, e, f, g, h, i].map (·.intVal) |>.sum) + x2).eval ρ.int) :
    U.Rel ρ (half.takeLE 32 (by omega))
      (a.eval ρ + b.eval ρ + c.eval ρ + d.eval ρ + e.eval ρ + f.eval ρ +
        g.eval ρ + h.eval ρ + i.eval ρ + x) := by
  let q := (a.eval ρ).toNat + (b.eval ρ).toNat + (c.eval ρ).toNat +
    (d.eval ρ).toNat + (e.eval ρ).toNat + (f.eval ρ).toNat +
    (g.eval ρ).toNat + (h.eval ρ).toNat + (i.eval ρ).toNat + x.toNat
  have htotal :
      (2 • (#[a, b, c, d, e, f, g, h, i].map (·.intVal) |>.sum) + x2).eval ρ.int =
        2 * q := by
    simp only [LC.eval_add, LC.eval_nsmul, LC.eval_array_sum]
    norm_num [U.intVal_eval_eq_eval_toNat a ha,
      U.intVal_eval_eq_eval_toNat b hb, U.intVal_eval_eq_eval_toNat c hc,
      U.intVal_eval_eq_eval_toNat d hd, U.intVal_eval_eq_eval_toNat e he,
      U.intVal_eval_eq_eval_toNat f hf, U.intVal_eval_eq_eval_toNat g hg,
      U.intVal_eval_eq_eval_toNat h hh, U.intVal_eval_eq_eval_toNat i hi, hx]
    dsimp [q]
    omega
  have hhalf2 : half.intVal.eval ρ.int = q := by
    rw [htotal] at hhalf
    omega
  have hhalfNat : (half.intVal.eval ρ.int).toNat = q := by rw [hhalf2]; simp
  refine ⟨U.takeLE_valid half hhalf.1 (by omega), ?_⟩
  rw [U.takeLE_eval half hhalf.1 (by omega), hhalfNat]
  dsimp [q]
  simp [BitVec.ofNat_add]

@[spec] theorem optimized_sum9Doubled1_sound {a b c d e f g h i : U 32}
    {x2 : LC ℤ} {x : BitVec 32}
    (ha : a.Valid ρ) (hb : b.Valid ρ) (hc : c.Valid ρ) (hd : d.Valid ρ)
    (he : e.Valid ρ) (hf : f.Valid ρ) (hg : g.Valid ρ) (hh : h.Valid ρ)
    (hi : i.Valid ρ) (hx : x2.eval ρ.int = 2 * (x.toNat : Int)) :
    ⦃⌜True⌝⦄ Sound.interp ρ (U.sum9Doubled1 a b c d e f g h i x2)
    ⦃⇓ out => ⌜U.Rel ρ out
      (a.eval ρ + b.eval ρ + c.eval ρ + d.eval ρ + e.eval ρ + f.eval ρ +
        g.eval ρ + h.eval ρ + i.eval ρ + x)⌝⦄ := by
  unfold U.sum9Doubled1
  rw [Sound.interp_bind]
  apply Triple.bind (Q := fun half => ⌜half.Valid ρ ∧
    2 * half.intVal.eval ρ.int =
      (2 • (#[a, b, c, d, e, f, g, h, i].map (·.intVal) |>.sum) + x2).eval ρ.int⌝)
  case hx => exact optimized_fromDoubledInt36_sound
  case hf =>
    intro half
    mvcgen -trivial
    exact optimized_sum9Doubled1_result ha hb hc hd he hf hg hh hi hx (by assumption)

@[spec] theorem optimized_sum9Doubled1_complete {a b c d e f g h i : U 32}
    {x2 : LC ℤ} {x : BitVec 32}
    (ha : a.Valid ρ) (hb : b.Valid ρ) (hc : c.Valid ρ) (hd : d.Valid ρ)
    (he : e.Valid ρ) (hf : f.Valid ρ) (hg : g.Valid ρ) (hh : h.Valid ρ)
    (hi : i.Valid ρ) (hx : x2.eval ρ.int = 2 * (x.toNat : Int)) :
    ⦃⌜True⌝⦄ Complete.interp ρ (U.sum9Doubled1 a b c d e f g h i x2)
    ⦃⇓ out => ⌜U.Rel ρ out
      (a.eval ρ + b.eval ρ + c.eval ρ + d.eval ρ + e.eval ρ + f.eval ρ +
        g.eval ρ + h.eval ρ + i.eval ρ + x)⌝⦄ := by
  let q := (a.eval ρ).toNat + (b.eval ρ).toNat + (c.eval ρ).toNat +
    (d.eval ρ).toNat + (e.eval ρ).toNat + (f.eval ρ).toNat +
    (g.eval ρ).toNat + (h.eval ρ).toNat + (i.eval ρ).toNat + x.toNat
  have htotal :
      (2 • (#[a, b, c, d, e, f, g, h, i].map (·.intVal) |>.sum) + x2).eval ρ.int =
        2 * q := by
    simp only [LC.eval_add, LC.eval_nsmul, LC.eval_array_sum]
    norm_num [U.intVal_eval_eq_eval_toNat a ha,
      U.intVal_eval_eq_eval_toNat b hb, U.intVal_eval_eq_eval_toNat c hc,
      U.intVal_eval_eq_eval_toNat d hd, U.intVal_eval_eq_eval_toNat e he,
      U.intVal_eval_eq_eval_toNat f hf, U.intVal_eval_eq_eval_toNat g hg,
      U.intVal_eval_eq_eval_toNat h hh, U.intVal_eval_eq_eval_toNat i hi, hx]
    dsimp [q]
    omega
  have h36 : q < 2^36 := by
    have ha' := (a.eval ρ).isLt; have hb' := (b.eval ρ).isLt
    have hc' := (c.eval ρ).isLt; have hd' := (d.eval ρ).isLt
    have he' := (e.eval ρ).isLt; have hf' := (f.eval ρ).isLt
    have hg' := (g.eval ρ).isLt; have hh' := (h.eval ρ).isLt
    have hi' := (i.eval ρ).isLt; have hx' := x.isLt
    dsimp [q]
    norm_num at ha' hb' hc' hd' he' hf' hg' hh' hi' hx' ⊢
    omega
  unfold U.sum9Doubled1
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun half => ⌜half.Valid ρ ∧
    2 * half.intVal.eval ρ.int =
      (2 • (#[a, b, c, d, e, f, g, h, i].map (·.intVal) |>.sum) + x2).eval ρ.int⌝)
  case hx => exact optimized_fromDoubledInt36_complete q htotal h36
  case hf =>
    intro half
    mvcgen -trivial
    exact optimized_sum9Doubled1_result ha hb hc hd he hf hg hh hi hx (by assumption)

theorem optimized_sum8Doubled1_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Vector (U 32) 8 × LC ℤ) =>
        WF.VectorRel U.WFRel lv rv l.1 r.1 ∧
        WF.LCEq lv.int rv.int l.2 r.2)
      (fun z => U.sum8Doubled1 z.1[0] z.1[1] z.1[2] z.1[3]
        z.1[4] z.1[5] z.1[6] z.1[7] z.2) U.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold U.sum8Doubled1
  apply WF.GadgetSpec.bind_rule optimized_fromDoubledInt36_wf_full
  · intro lv rv h
    unfold WF.LCEq at h ⊢
    simp only [LC.eval_add, LC.eval_nsmul, LC.eval_array_sum]
    simp only [WF.VectorRel, U.WFRel, WF.LCEq] at h
    have h0 := (h.1 (0 : Fin 8)).1
    have h1 := (h.1 (1 : Fin 8)).1
    have h2 := (h.1 (2 : Fin 8)).1
    have h3 := (h.1 (3 : Fin 8)).1
    have h4 := (h.1 (4 : Fin 8)).1
    have h5 := (h.1 (5 : Fin 8)).1
    have h6 := (h.1 (6 : Fin 8)).1
    have h7 := (h.1 (7 : Fin 8)).1
    norm_num at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
    omega
  · intro A outL outR hout
    apply WF.Rel.pure
    intro lv rv hA
    have h := hout lv rv hA
    constructor
    · apply WF.LCEq.uIntVal
      intro i
      simpa [U.takeLE, Fin.getElem_fin] using h.2.2.1 (i.castLE (by omega))
    · intro i
      simpa [U.takeLE, Fin.getElem_fin] using h.2.1 (i.castLE (by omega))

theorem optimized_sum9Doubled1_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Vector (U 32) 9 × LC ℤ) =>
        WF.VectorRel U.WFRel lv rv l.1 r.1 ∧ WF.LCEq lv.int rv.int l.2 r.2)
      (fun z => U.sum9Doubled1 z.1[0] z.1[1] z.1[2] z.1[3]
        z.1[4] z.1[5] z.1[6] z.1[7] z.1[8] z.2) U.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold U.sum9Doubled1
  apply WF.GadgetSpec.bind_rule optimized_fromDoubledInt36_wf_full
  · intro lv rv h
    unfold WF.LCEq at h ⊢
    simp only [LC.eval_add, LC.eval_nsmul, LC.eval_array_sum]
    simp only [WF.VectorRel, U.WFRel, WF.LCEq] at h
    have h0 := (h.1 (0 : Fin 9)).1; have h1 := (h.1 (1 : Fin 9)).1
    have h2 := (h.1 (2 : Fin 9)).1; have h3 := (h.1 (3 : Fin 9)).1
    have h4 := (h.1 (4 : Fin 9)).1; have h5 := (h.1 (5 : Fin 9)).1
    have h6 := (h.1 (6 : Fin 9)).1; have h7 := (h.1 (7 : Fin 9)).1
    have h8 := (h.1 (8 : Fin 9)).1
    norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    omega
  · intro A outL outR hout
    apply WF.Rel.pure
    intro lv rv hA
    have h := hout lv rv hA
    constructor
    · apply WF.LCEq.uIntVal
      intro i
      simpa [U.takeLE, Fin.getElem_fin] using h.2.2.1 (i.castLE (by omega))
    · intro i
      simpa [U.takeLE, Fin.getElem_fin] using h.2.1 (i.castLE (by omega))

theorem optimized_sumAFromE_result {d newE S0 : U 32} {half : U 34}
    {maj2 : LC ℤ} {maj : BitVec 32}
    (hd : d.Valid ρ) (he : newE.Valid ρ) (hS0 : S0.Valid ρ)
    (hmaj : maj2.eval ρ.int = 2 * (maj.toNat : Int))
    (hhalf : half.Valid ρ ∧ 2 * half.intVal.eval ρ.int =
      (2 • (newE.intVal + S0.intVal - d.intVal) + maj2 +
        LC.ofConst (2^33 : ℤ)).eval ρ.int) :
    U.Rel ρ (half.takeLE 32 (by omega))
      (newE.eval ρ + S0.eval ρ + maj - d.eval ρ) := by
  let q := (newE.eval ρ).toNat + (S0.eval ρ).toNat + maj.toNat +
    2^32 - (d.eval ρ).toNat
  have hd' := (d.eval ρ).isLt
  have he' := (newE.eval ρ).isLt
  have hs' := (S0.eval ρ).isLt
  have hm' := maj.isLt
  have hdle : (d.eval ρ).toNat ≤
      (newE.eval ρ).toNat + (S0.eval ρ).toNat + maj.toNat + 2^32 := by
    norm_num at hd' he' hs' hm' ⊢
    omega
  have htotal :
      (2 • (newE.intVal + S0.intVal - d.intVal) + maj2 +
        LC.ofConst (2^33 : ℤ)).eval ρ.int =
        2 * q := by
    simp only [LC.eval_add, LC.eval_sub, LC.eval_nsmul, LC.eval_ofConst,
      U.intVal_eval_eq_eval_toNat newE he,
      U.intVal_eval_eq_eval_toNat S0 hS0,
      U.intVal_eval_eq_eval_toNat d hd, hmaj]
    dsimp [q]
    have hsub := Int.ofNat_sub hdle
    norm_num at hsub
    rw [hsub]
    norm_num
    ring
  have hhalf2 : half.intVal.eval ρ.int = q := by
    rw [htotal] at hhalf
    omega
  have hhalfNat : (half.intVal.eval ρ.int).toNat = q := by
    rw [hhalf2]
    simp
  refine ⟨U.takeLE_valid half hhalf.1 (by omega), ?_⟩
  rw [U.takeLE_eval half hhalf.1 (by omega), hhalfNat]
  dsimp [q]
  apply BitVec.eq_sub_iff_add_eq.mpr
  have hdOf : BitVec.ofNat 32 (d.eval ρ).toNat = d.eval ρ := by
    simp [BitVec.ofNat_toNat]
  calc
    BitVec.ofNat 32
          ((newE.eval ρ).toNat + (S0.eval ρ).toNat + maj.toNat + 2 ^ 32 -
            (d.eval ρ).toNat) + d.eval ρ =
        BitVec.ofNat 32
          ((newE.eval ρ).toNat + (S0.eval ρ).toNat + maj.toNat + 2 ^ 32 -
            (d.eval ρ).toNat) + BitVec.ofNat 32 (d.eval ρ).toNat := by rw [hdOf]
    _ = BitVec.ofNat 32
          (((newE.eval ρ).toNat + (S0.eval ρ).toNat + maj.toNat + 2 ^ 32 -
            (d.eval ρ).toNat) + (d.eval ρ).toNat) := by
          rw [BitVec.ofNat_add]
    _ = newE.eval ρ + S0.eval ρ + maj := by
          rw [Nat.sub_add_cancel hdle]
          simp [BitVec.ofNat_add, BitVec.ofNat_toNat]

theorem optimized_sumAFinal_result {d outE S0 stateA stateE : U 32}
    {half : U 35} {maj2 : LC ℤ} {maj : BitVec 32}
    (hd : d.Valid ρ) (he : outE.Valid ρ) (hS0 : S0.Valid ρ)
    (hA : stateA.Valid ρ) (hE : stateE.Valid ρ)
    (hmaj : maj2.eval ρ.int = 2 * (maj.toNat : Int))
    (hhalf : half.Valid ρ ∧ 2 * half.intVal.eval ρ.int =
      (2 • (outE.intVal + S0.intVal + stateA.intVal - stateE.intVal - d.intVal) +
        maj2 + LC.ofConst (2^34 : ℤ)).eval ρ.int) :
    U.Rel ρ (half.takeLE 32 (by omega))
      (outE.eval ρ + S0.eval ρ + stateA.eval ρ + maj - stateE.eval ρ - d.eval ρ) := by
  let pos := (outE.eval ρ).toNat + (S0.eval ρ).toNat +
    (stateA.eval ρ).toNat + maj.toNat + 2^33
  let neg := (stateE.eval ρ).toNat + (d.eval ρ).toNat
  let q := pos - neg
  have hle : neg ≤ pos := by
    have hd' := (d.eval ρ).isLt; have he' := (outE.eval ρ).isLt
    have hs' := (S0.eval ρ).isLt; have ha' := (stateA.eval ρ).isLt
    have hse' := (stateE.eval ρ).isLt; have hm' := maj.isLt
    dsimp [neg, pos]
    norm_num at hd' he' hs' ha' hse' hm' ⊢
    omega
  have htotal :
      (2 • (outE.intVal + S0.intVal + stateA.intVal - stateE.intVal - d.intVal) +
        maj2 + LC.ofConst (2^34 : ℤ)).eval ρ.int = 2 * q := by
    simp only [LC.eval_add, LC.eval_sub, LC.eval_nsmul, LC.eval_ofConst,
      U.intVal_eval_eq_eval_toNat outE he,
      U.intVal_eval_eq_eval_toNat S0 hS0,
      U.intVal_eval_eq_eval_toNat stateA hA,
      U.intVal_eval_eq_eval_toNat stateE hE,
      U.intVal_eval_eq_eval_toNat d hd, hmaj]
    rw [show (q : Int) = (pos : Int) - neg by
      rw [Int.ofNat_sub hle]]
    dsimp [pos, neg]
    ring
  have hhalf2 : half.intVal.eval ρ.int = q := by rw [htotal] at hhalf; omega
  have hhalfNat : (half.intVal.eval ρ.int).toNat = q := by rw [hhalf2]; simp
  refine ⟨U.takeLE_valid half hhalf.1 (by omega), ?_⟩
  rw [U.takeLE_eval half hhalf.1 (by omega), hhalfNat]
  apply BitVec.eq_sub_iff_add_eq.mpr
  apply BitVec.eq_sub_iff_add_eq.mpr
  calc
    BitVec.ofNat 32 q + d.eval ρ + stateE.eval ρ =
        BitVec.ofNat 32 (q + (d.eval ρ).toNat + (stateE.eval ρ).toNat) := by
      simp [BitVec.ofNat_add, BitVec.ofNat_toNat]
    _ = BitVec.ofNat 32 pos := by
      congr 1
      dsimp [q, pos, neg]
      omega
    _ = outE.eval ρ + S0.eval ρ + stateA.eval ρ + maj := by
      dsimp [pos]
      simp [BitVec.ofNat_add, BitVec.ofNat_toNat]

@[spec] theorem optimized_sumAFinal_sound {d outE S0 stateA stateE : U 32}
    {maj2 : LC ℤ} {maj : BitVec 32}
    (hd : d.Valid ρ) (he : outE.Valid ρ) (hS0 : S0.Valid ρ)
    (hA : stateA.Valid ρ) (hE : stateE.Valid ρ)
    (hmaj : maj2.eval ρ.int = 2 * (maj.toNat : Int)) :
    ⦃⌜True⌝⦄ Sound.interp ρ (U.sumAFinal d outE S0 stateA stateE maj2)
    ⦃⇓ out => ⌜U.Rel ρ out
      (outE.eval ρ + S0.eval ρ + stateA.eval ρ + maj - stateE.eval ρ - d.eval ρ)⌝⦄ := by
  unfold U.sumAFinal
  rw [Sound.interp_bind]
  apply Triple.bind (Q := fun half => ⌜half.Valid ρ ∧
    2 * half.intVal.eval ρ.int =
      (2 • (outE.intVal + S0.intVal + stateA.intVal - stateE.intVal - d.intVal) +
        maj2 + LC.ofConst (2^34 : ℤ)).eval ρ.int⌝)
  case hx => exact optimized_fromDoubledInt35_sound
  case hf =>
    intro half
    mvcgen -trivial
    exact optimized_sumAFinal_result hd he hS0 hA hE hmaj (by assumption)

@[spec] theorem optimized_sumAFinal_complete {d outE S0 stateA stateE : U 32}
    {maj2 : LC ℤ} {maj : BitVec 32}
    (hd : d.Valid ρ) (he : outE.Valid ρ) (hS0 : S0.Valid ρ)
    (hA : stateA.Valid ρ) (hE : stateE.Valid ρ)
    (hmaj : maj2.eval ρ.int = 2 * (maj.toNat : Int)) :
    ⦃⌜True⌝⦄ Complete.interp ρ (U.sumAFinal d outE S0 stateA stateE maj2)
    ⦃⇓ out => ⌜U.Rel ρ out
      (outE.eval ρ + S0.eval ρ + stateA.eval ρ + maj - stateE.eval ρ - d.eval ρ)⌝⦄ := by
  let pos := (outE.eval ρ).toNat + (S0.eval ρ).toNat +
    (stateA.eval ρ).toNat + maj.toNat + 2^33
  let neg := (stateE.eval ρ).toNat + (d.eval ρ).toNat
  let q := pos - neg
  have hle : neg ≤ pos := by
    have hd' := (d.eval ρ).isLt; have he' := (outE.eval ρ).isLt
    have hs' := (S0.eval ρ).isLt; have ha' := (stateA.eval ρ).isLt
    have hse' := (stateE.eval ρ).isLt; have hm' := maj.isLt
    dsimp [neg, pos]
    norm_num at hd' he' hs' ha' hse' hm' ⊢
    omega
  have htotal :
      (2 • (outE.intVal + S0.intVal + stateA.intVal - stateE.intVal - d.intVal) +
        maj2 + LC.ofConst (2^34 : ℤ)).eval ρ.int = 2 * q := by
    simp only [LC.eval_add, LC.eval_sub, LC.eval_nsmul, LC.eval_ofConst,
      U.intVal_eval_eq_eval_toNat outE he,
      U.intVal_eval_eq_eval_toNat S0 hS0,
      U.intVal_eval_eq_eval_toNat stateA hA,
      U.intVal_eval_eq_eval_toNat stateE hE,
      U.intVal_eval_eq_eval_toNat d hd, hmaj]
    rw [show (q : Int) = (pos : Int) - neg by rw [Int.ofNat_sub hle]]
    dsimp [pos, neg]
    ring
  have h35 : q < 2^35 := by
    apply lt_of_le_of_lt (Nat.sub_le _ _)
    dsimp [pos]
    have he' := (outE.eval ρ).isLt; have hs' := (S0.eval ρ).isLt
    have ha' := (stateA.eval ρ).isLt; have hm' := maj.isLt
    norm_num at he' hs' ha' hm' ⊢
    omega
  unfold U.sumAFinal
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun half => ⌜half.Valid ρ ∧
    2 * half.intVal.eval ρ.int =
      (2 • (outE.intVal + S0.intVal + stateA.intVal - stateE.intVal - d.intVal) +
        maj2 + LC.ofConst (2^34 : ℤ)).eval ρ.int⌝)
  case hx => exact optimized_fromDoubledInt35_complete q htotal h35
  case hf =>
    intro half
    mvcgen -trivial
    exact optimized_sumAFinal_result hd he hS0 hA hE hmaj (by assumption)

@[spec] theorem optimized_sumAFromE_sound {d newE S0 : U 32} {maj2 : LC ℤ}
    {maj : BitVec 32} (hd : d.Valid ρ) (he : newE.Valid ρ)
    (hS0 : S0.Valid ρ)
    (hmaj : maj2.eval ρ.int = 2 * (maj.toNat : Int)) :
    ⦃⌜True⌝⦄ Sound.interp ρ (U.sumAFromE d newE S0 maj2)
    ⦃⇓ out => ⌜U.Rel ρ out
      (newE.eval ρ + S0.eval ρ + maj - d.eval ρ)⌝⦄ := by
  unfold U.sumAFromE
  rw [Sound.interp_bind]
  apply Triple.bind (Q := fun half => ⌜half.Valid ρ ∧
    2 * half.intVal.eval ρ.int =
      (2 • (newE.intVal + S0.intVal - d.intVal) + maj2 +
        LC.ofConst (2^33 : ℤ)).eval ρ.int⌝)
  case hx => exact optimized_fromDoubledInt34_sound
  case hf =>
    intro half
    mvcgen -trivial
    exact optimized_sumAFromE_result hd he hS0 hmaj (by assumption)

@[spec] theorem optimized_sumAFromE_complete {d newE S0 : U 32} {maj2 : LC ℤ}
    {maj : BitVec 32} (hd : d.Valid ρ) (he : newE.Valid ρ)
    (hS0 : S0.Valid ρ)
    (hmaj : maj2.eval ρ.int = 2 * (maj.toNat : Int)) :
    ⦃⌜True⌝⦄ Complete.interp ρ (U.sumAFromE d newE S0 maj2)
    ⦃⇓ out => ⌜U.Rel ρ out
      (newE.eval ρ + S0.eval ρ + maj - d.eval ρ)⌝⦄ := by
  let q := (newE.eval ρ).toNat + (S0.eval ρ).toNat + maj.toNat +
    2^32 - (d.eval ρ).toNat
  let total := 2 • (newE.intVal + S0.intVal - d.intVal) + maj2 +
    LC.ofConst (2^33 : ℤ)
  have hd' := (d.eval ρ).isLt
  have he' := (newE.eval ρ).isLt
  have hs' := (S0.eval ρ).isLt
  have hm' := maj.isLt
  have hdle : (d.eval ρ).toNat ≤
      (newE.eval ρ).toNat + (S0.eval ρ).toNat + maj.toNat + 2^32 := by
    norm_num at hd' he' hs' hm' ⊢
    omega
  have htotal : total.eval ρ.int = 2 * q := by
    dsimp [total]
    simp only [LC.eval_add, LC.eval_sub, LC.eval_nsmul, LC.eval_ofConst,
      U.intVal_eval_eq_eval_toNat newE he,
      U.intVal_eval_eq_eval_toNat S0 hS0,
      U.intVal_eval_eq_eval_toNat d hd, hmaj]
    dsimp [q]
    have hsub := Int.ofNat_sub hdle
    norm_num at hsub
    rw [hsub]
    norm_num
    ring
  have h34 : q < 2^34 := by
    dsimp [q]
    norm_num at hd' he' hs' hm' ⊢
    omega
  unfold U.sumAFromE
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun half => ⌜half.Valid ρ ∧
    2 * half.intVal.eval ρ.int = total.eval ρ.int⌝)
  case hx => exact optimized_fromDoubledInt34_complete q htotal h34
  case hf =>
    intro half
    mvcgen -trivial
    exact optimized_sumAFromE_result hd he hS0 hmaj (by assumption)

theorem optimized_sumAFromE_wf :
    WF.GadgetSpec
      (fun lv rv (l r : U 32 × U 32 × U 32 × LC ℤ) =>
        U.WFRel lv rv l.1 r.1 ∧ U.WFRel lv rv l.2.1 r.2.1 ∧
        U.WFRel lv rv l.2.2.1 r.2.2.1 ∧
        WF.LCEq lv.int rv.int l.2.2.2 r.2.2.2)
      (fun z => U.sumAFromE z.1 z.2.1 z.2.2.1 z.2.2.2) U.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold U.sumAFromE
  apply WF.GadgetSpec.bind_rule optimized_fromDoubledInt34_wf_full
  · intro lv rv h
    unfold WF.LCEq at h ⊢
    simp only [LC.eval_add, LC.eval_sub, LC.eval_nsmul, LC.eval_ofConst]
    simp only [U.WFRel, WF.LCEq] at h
    grind
  · intro A outL outR hout
    apply WF.Rel.pure
    intro lv rv hA
    have h := hout lv rv hA
    constructor
    · apply WF.LCEq.uIntVal
      intro i
      simpa [U.takeLE, Fin.getElem_fin] using h.2.2.1 (i.castLE (by omega))
    · intro i
      simpa [U.takeLE, Fin.getElem_fin] using h.2.1 (i.castLE (by omega))

theorem optimized_sumAFinal_wf :
    WF.GadgetSpec
      (fun lv rv (l r : U 32 × U 32 × U 32 × U 32 × U 32 × LC ℤ) =>
        U.WFRel lv rv l.1 r.1 ∧ U.WFRel lv rv l.2.1 r.2.1 ∧
        U.WFRel lv rv l.2.2.1 r.2.2.1 ∧ U.WFRel lv rv l.2.2.2.1 r.2.2.2.1 ∧
        U.WFRel lv rv l.2.2.2.2.1 r.2.2.2.2.1 ∧
        WF.LCEq lv.int rv.int l.2.2.2.2.2 r.2.2.2.2.2)
      (fun z => U.sumAFinal z.1 z.2.1 z.2.2.1 z.2.2.2.1
        z.2.2.2.2.1 z.2.2.2.2.2) U.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold U.sumAFinal
  apply WF.GadgetSpec.bind_rule optimized_fromDoubledInt35_wf_full
  · intro lv rv h
    unfold WF.LCEq at h ⊢
    simp only [LC.eval_add, LC.eval_sub, LC.eval_nsmul, LC.eval_ofConst]
    simp only [U.WFRel, WF.LCEq] at h
    grind
  · intro A outL outR hout
    apply WF.Rel.pure
    intro lv rv hA
    have h := hout lv rv hA
    constructor
    · apply WF.LCEq.uIntVal
      intro i
      simpa [U.takeLE, Fin.getElem_fin] using h.2.2.1 (i.castLE (by omega))
    · intro i
      simpa [U.takeLE, Fin.getElem_fin] using h.2.1 (i.castLE (by omega))


def roundVector (r : RoundState α) : Vector α 8 :=
  #v[r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1,
    r.2.2.2.2.2.1, r.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2]

def structured (m : Vector (Word 32) 16) (s : Vector (Word 32) 8) :
    Circuit (Vector (U 32) 8) := permCircuit m s

set_option maxHeartbeats 1000000 in
theorem structured_eq (m : Vector (Word 32) 16) (s : Vector (Word 32) 8) :
    structured m s = permCircuit m s := by
  rfl

def RoundState.eval (ρ : WF.Valuation) (r : RoundState (U n)) :
    RoundState (BitVec n) :=
  ⟨r.1.eval ρ, r.2.1.eval ρ, r.2.2.1.eval ρ, r.2.2.2.1.eval ρ,
    r.2.2.2.2.1.eval ρ, r.2.2.2.2.2.1.eval ρ,
    r.2.2.2.2.2.2.1.eval ρ, r.2.2.2.2.2.2.2.eval ρ⟩

def RoundState.Valid (ρ : WF.Valuation) (r : RoundState (U n)) : Prop :=
  r.1.Valid ρ ∧ r.2.1.Valid ρ ∧ r.2.2.1.Valid ρ ∧ r.2.2.2.1.Valid ρ ∧
  r.2.2.2.2.1.Valid ρ ∧ r.2.2.2.2.2.1.Valid ρ ∧
  r.2.2.2.2.2.2.1.Valid ρ ∧ r.2.2.2.2.2.2.2.Valid ρ

def RoundState.Rel (ρ : WF.Valuation) (us : RoundState (U n))
    (xs : RoundState (BitVec n)) : Prop :=
  us.Valid ρ ∧ us.eval ρ = xs

theorem RoundState.Rel.eval_eq {n : Nat} {r : RoundState (U n)}
    {rv : RoundState (BitVec n)} (h : RoundState.Rel ρ r rv) :
    r.eval ρ = rv := h.2

theorem RoundState.Rel.refl {n : Nat} {r : RoundState (U n)} (h : r.Valid ρ) :
    RoundState.Rel ρ r (r.eval ρ) := ⟨h, rfl⟩

theorem RoundState.Rel.a (h : RoundState.Rel ρ r rv) : U.Rel ρ r.1 rv.1 :=
  ⟨h.1.1, congrArg (fun x => x.1) h.2⟩

theorem RoundState.Rel.b (h : RoundState.Rel ρ r rv) : U.Rel ρ r.2.1 rv.2.1 :=
  ⟨h.1.2.1, congrArg (fun x => x.2.1) h.2⟩

theorem RoundState.Rel.c (h : RoundState.Rel ρ r rv) : U.Rel ρ r.2.2.1 rv.2.2.1 :=
  ⟨h.1.2.2.1, congrArg (fun x => x.2.2.1) h.2⟩

theorem RoundState.Rel.d (h : RoundState.Rel ρ r rv) : U.Rel ρ r.2.2.2.1 rv.2.2.2.1 :=
  ⟨h.1.2.2.2.1, congrArg (fun x => x.2.2.2.1) h.2⟩

theorem RoundState.Rel.e (h : RoundState.Rel ρ r rv) : U.Rel ρ r.2.2.2.2.1 rv.2.2.2.2.1 :=
  ⟨h.1.2.2.2.2.1, congrArg (fun x => x.2.2.2.2.1) h.2⟩

theorem RoundState.Rel.f (h : RoundState.Rel ρ r rv) : U.Rel ρ r.2.2.2.2.2.1 rv.2.2.2.2.2.1 :=
  ⟨h.1.2.2.2.2.2.1, congrArg (fun x => x.2.2.2.2.2.1) h.2⟩

theorem RoundState.Rel.g (h : RoundState.Rel ρ r rv) : U.Rel ρ r.2.2.2.2.2.2.1 rv.2.2.2.2.2.2.1 :=
  ⟨h.1.2.2.2.2.2.2.1, congrArg (fun x => x.2.2.2.2.2.2.1) h.2⟩

theorem RoundState.Rel.h (h : RoundState.Rel ρ r rv) : U.Rel ρ r.2.2.2.2.2.2.2 rv.2.2.2.2.2.2.2 :=
  ⟨h.1.2.2.2.2.2.2.2, congrArg (fun x => x.2.2.2.2.2.2.2) h.2⟩

theorem RoundState.Rel.vector (h : RoundState.Rel ρ r rv) :
    Vector.Rel ρ (roundVector r) (roundVector rv) := by
  intro i
  fin_cases i <;>
    first | exact h.a | exact h.b | exact h.c | exact h.d |
      exact h.e | exact h.f | exact h.g | exact h.h

def scheduleStepBV (i : Nat) (w : Vector (BitVec 32) 64) : BitVec 32 :=
  let s0 := w[i - 15]!.rotateRight 7 ^^^ w[i - 15]!.rotateRight 18 ^^^
    (w[i - 15]! >>> 3)
  let s1 := w[i - 2]!.rotateRight 17 ^^^ w[i - 2]!.rotateRight 19 ^^^
    (w[i - 2]! >>> 10)
  #[w[i - 16]!, s0, w[i - 7]!, s1].sum

def roundStepBV (i : Nat)
    (w : Vector (BitVec 32) 64) (r : RoundState (BitVec 32)) :
    RoundState (BitVec 32) :=
  let S1 := r.2.2.2.2.1.rotateRight 6 ^^^ r.2.2.2.2.1.rotateRight 11 ^^^
    r.2.2.2.2.1.rotateRight 25
  let ch := chBV r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1
  let S0 := r.1.rotateRight 2 ^^^ r.1.rotateRight 13 ^^^ r.1.rotateRight 22
  let maj := majBV r.1 r.2.1 r.2.2.1
  let newE := #[r.2.2.2.1, r.2.2.2.2.2.2.2, S1, ch, k[i]!, w[i]!].sum
  let newA := #[r.2.2.2.2.2.2.2, S1, ch, k[i]!, w[i]!, S0, maj].sum
  ⟨newA, r.1, r.2.1, r.2.2.1, newE,
    r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1⟩

def scheduleRoundStepBV (i : Nat)
    (x : RoundState (BitVec 32) × Vector (BitVec 32) 64) :
    RoundState (BitVec 32) × Vector (BitVec 32) 64 :=
  let w := x.2.set! i (scheduleStepBV i x.2)
  (roundStepBV i w x.1, w)

@[simp] theorem scheduleRoundStepBV_fst (i : Nat)
    (x : RoundState (BitVec 32) × Vector (BitVec 32) 64) :
    (scheduleRoundStepBV i x).1 =
      roundStepBV i (x.2.set! i (scheduleStepBV i x.2)) x.1 := rfl

@[simp] theorem scheduleRoundStepBV_snd (i : Nat)
    (x : RoundState (BitVec 32) × Vector (BitVec 32) 64) :
    (scheduleRoundStepBV i x).2 =
      x.2.set! i (scheduleStepBV i x.2) := rfl

def inlineScheduleRoundBV (i : Nat) (w : Vector (BitVec 32) 64)
    (r : RoundState (BitVec 32)) : RoundState (BitVec 32) :=
  let S1 := r.2.2.2.2.1.rotateRight 6 ^^^ r.2.2.2.2.1.rotateRight 11 ^^^
    r.2.2.2.2.1.rotateRight 25
  let ch := chBV r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1
  let S0 := r.1.rotateRight 2 ^^^ r.1.rotateRight 13 ^^^ r.1.rotateRight 22
  let maj := majBV r.1 r.2.1 r.2.2.1
  let wi := scheduleStepBV i w
  let newE := #[r.2.2.2.1, r.2.2.2.2.2.2.2, S1, ch, k[i]!, wi].sum
  let newA := #[r.2.2.2.2.2.2.2, S1, ch, k[i]!, wi, S0, maj].sum
  ⟨newA, r.1, r.2.1, r.2.2.1, newE,
    r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1⟩

set_option maxHeartbeats 1000000 in
private theorem inlineScheduleRoundBV_a (i : Nat) (w : Vector (BitVec 32) 64)
    (r : RoundState (BitVec 32)) :
    (inlineScheduleRoundBV i w r).1 =
      #[r.2.2.2.2.2.2.2,
        r.2.2.2.2.1.rotateRight 6 ^^^ r.2.2.2.2.1.rotateRight 11 ^^^
          r.2.2.2.2.1.rotateRight 25,
        chBV r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1, k[i]!,
        scheduleStepBV i w,
        r.1.rotateRight 2 ^^^ r.1.rotateRight 13 ^^^ r.1.rotateRight 22,
        majBV r.1 r.2.1 r.2.2.1].sum := rfl

set_option maxHeartbeats 1000000 in
private theorem inlineScheduleRoundBV_e (i : Nat) (w : Vector (BitVec 32) 64)
    (r : RoundState (BitVec 32)) :
    (inlineScheduleRoundBV i w r).2.2.2.2.1 =
      #[r.2.2.2.1, r.2.2.2.2.2.2.2,
        r.2.2.2.2.1.rotateRight 6 ^^^ r.2.2.2.2.1.rotateRight 11 ^^^
          r.2.2.2.2.1.rotateRight 25,
        chBV r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1, k[i]!,
        scheduleStepBV i w].sum := rfl

@[spec] theorem U.fromIntWithLowBit_sound {x : LC ℤ} {low : LC Bool} :
    ⦃⌜True⌝⦄ Sound.interp ρ (U.fromIntWithLowBit n x low)
    ⦃⇓ out => ⌜out.Valid ρ ∧ out.intVal.eval ρ.int = x.eval ρ.int⌝⦄ := by
  mvcgen [U.fromIntWithLowBit]
  intro b
  mvcgen
  rename_i r h hassert
  constructor
  · exact h.1
  · simp only [LC.eval_zero, mul_zero, LC.eval_sub] at hassert
    omega

@[spec] theorem U.fromIntWithLowBit_complete {x : LC ℤ} {low : LC Bool}
    (h0 : x.eval ρ.int ≥ 0) (h2 : x.eval ρ.int < 2 ^ (n + 1))
    (hlow : low.eval ρ.bool = Int.bodd (x.eval ρ.int)) :
    ⦃⌜True⌝⦄ Complete.interp ρ (U.fromIntWithLowBit n x low)
    ⦃⇓ out => ⌜out.Valid ρ ∧ out.intVal.eval ρ.int = x.eval ρ.int⌝⦄ := by
  mvcgen [U.fromIntWithLowBit]
  have : ∃ x', x.eval ρ.int = Int.ofNat x' := by
    exists (x.eval ρ.int).toNat
    simp_all
  rcases this with ⟨x', hx'⟩
  simp only [WF.interpHint, WF.evalArgs, hx', Int.ofNat_eq_natCast, Free.interp_pure,
    Option.pure_def, Option.some.injEq, exists_eq_left', Vector.map_ofFn]
  mvcgen
  rename_i r h
  have hxlt : x' < 2 ^ (n + 1) := by
    rw [hx'] at h2
    exact Int.ofNat_lt.mp (by simpa using h2)
  have hword := congrArg BitVec.toNat h.2
  simp only [Word.eval, Vector.getElem_ofFn, BitVec.toNat_ofFnLE,
    Function.comp_apply] at hword
  have hfn : (fun i : Fin (n + 1) =>
      LC.eval ρ.bool (Vector.ofFn fun i => if hi : i.val = 0 then low else
        LC.ofConst (x'.testBit (i.val - 1 + 1)))[i]) =
      fun i => x'.testBit i.val := by
    funext i
    by_cases hi : i.val = 0
    · simp [hi, hx', hlow, Int.bodd_coe, Nat.bodd]
    · have hi' : i ≠ 0 := by
        intro hzero
        apply hi
        simpa [hzero]
      simp [hi', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi)]
  rw [hfn, Nat.ofBits_testBit, Nat.mod_eq_of_lt hxlt] at hword
  have hintVal : r.intVal.eval ρ.int = (x' : Int) :=
    (U.intVal_eval_eq_eval_toNat r h.1).trans
      (congrArg (fun z : Nat => (z : Int)) hword)
  constructor
  · simp [LC.eval_zero, LC.eval_sub, hx', hintVal]
  · exact ⟨h.1, hintVal⟩

private theorem U.lowBit_eq_bodd (u : U (n + 1)) (hvalid : u.Valid ρ) :
    u.bits.bitsLE[0].eval ρ.bool = Int.bodd (u.intVal.eval ρ.int) := by
  rw [U.intVal_eval_eq_eval_toNat u hvalid, Int.bodd_coe]
  change u.bits.bitsLE[0].eval ρ.bool = (u.eval ρ).toNat.testBit 0
  have h := congrArg (fun x : BitVec (n + 1) => x[0])
    (U.eval_eq_ofFnLE u hvalid)
  have h0 : (u.eval ρ)[0] = u.bits.bitsLE[0].eval ρ.bool := by
    simpa only [BitVec.getElem_ofFnLE, Fin.getElem_fin] using h
  exact h0.symm.trans (BitVec.getElem_eq_testBit_toNat (u.eval ρ) 0 (by omega))

private theorem boolSum_bodd (xs : List ℤ) :
    Int.bodd xs.sum = (xs.map Int.bodd).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.sum_cons, Int.bodd_add, List.map_cons, List.sum_cons, ih]
      rfl

private theorem vectorValid_toArray {us : Vector (U n) m}
    (hvalid : ∀ i : Fin m, us[i].Valid ρ) :
    ∀ u ∈ us.toArray, u.Valid ρ := by
  intro u hu
  rw [Array.mem_iff_getElem] at hu
  obtain ⟨i, hi, rfl⟩ := hu
  simpa using hvalid ⟨i, by simpa using hi⟩

private theorem U.lowSum_eq_bodd (us : Vector (U 32) m)
    (hvalid : ∀ i : Fin m, us[i].Valid ρ) :
    ((us.toArray.map (fun u : U 32 => u.bits.bitsLE[0])).sum).eval ρ.bool =
      Int.bodd ((us.toArray.map (fun u : U 32 => u.intVal)).sum.eval ρ.int) := by
  rw [LC.eval_array_sum, LC.eval_array_sum]
  rw [← Array.sum_toList, ← Array.sum_toList]
  simp only [Array.toList_map, List.map_map]
  rw [boolSum_bodd]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro u hu
  exact U.lowBit_eq_bodd u (vectorValid_toArray hvalid u (by simpa using hu))

@[spec] theorem U.sumFixedAffineLow_sound {us : Vector (U 32) m}
    (hvalid : ∀ i : Fin m, us[i].Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (U.sumFixedAffineLow us)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      out.eval ρ = (us.toArray.map (·.eval ρ)).sum⌝⦄ := by
  unfold U.sumFixedAffineLow
  unfold U.fromIntWithLowBitPair
  mvcgen
  case vc1.h.success r h =>
    let hle : 32 ≤ 31 + Nat.clog 2 m + 1 := by omega
    exact ⟨U.takeLE_valid r h.1 hle, by
      rw [U.takeLE_eval r h.1 hle, h.2]
      exact U.sumValue_eq_sum us.toArray (vectorValid_toArray hvalid)⟩

@[spec] theorem U.sumFixedAffineLow_complete {us : Vector (U 32) m}
    (hvalid : ∀ i : Fin m, us[i].Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (U.sumFixedAffineLow us)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      out.eval ρ = (us.toArray.map (·.eval ρ)).sum⌝⦄ := by
  unfold U.sumFixedAffineLow
  unfold U.fromIntWithLowBitPair
  mvcgen
  case vc1.h0 => exact U.sum_nonneg us.toArray (vectorValid_toArray hvalid)
  case vc2.h2 =>
    have hcap := U.sum_lt_capacity us.toArray (vectorValid_toArray hvalid)
    simpa only [Vector.size_toArray,
      show 31 + Nat.clog 2 m + 1 = 32 + Nat.clog 2 m by omega] using hcap
  case vc3.hlow => exact U.lowSum_eq_bodd us hvalid
  case vc4.h.success r h =>
    let hle : 32 ≤ 31 + Nat.clog 2 m + 1 := by omega
    exact ⟨U.takeLE_valid r h.1 hle, by
      rw [U.takeLE_eval r h.1 hle, h.2]
      exact U.sumValue_eq_sum us.toArray (vectorValid_toArray hvalid)⟩

private theorem scheduleResult {w : Vector (U 32) 64}
    {wv : Vector (BitVec 32) 64} (hw : Vector.Rel ρ w wv)
    (i : Nat) (hi : i ∈ [16:64]) {s0 s1 out : U 32}
    (hs0 : U.Rel ρ s0 (Word.eval ρ.bool
      (w[i - 15]!.bits.rotateRight 7 ^^^
        w[i - 15]!.bits.rotateRight 18 ^^^ (w[i - 15]!.bits >>> 3))))
    (hs1 : U.Rel ρ s1 (Word.eval ρ.bool
      (w[i - 2]!.bits.rotateRight 17 ^^^
        w[i - 2]!.bits.rotateRight 19 ^^^ (w[i - 2]!.bits >>> 10))))
    (hout : U.Rel ρ out
      (#[w[i - 16]!, s0, w[i - 7]!, s1].map (·.eval ρ)).sum) :
    U.Rel ρ out (scheduleStepBV i wv) := by
  have hs0' := (hw.getElem! (i := i - 15) (by grind)).rotateXorShift
    (by decide) (by decide) hs0
  have hs1' := (hw.getElem! (i := i - 2) (by grind)).rotateXorShift
    (by decide) (by decide) hs1
  refine ⟨hout.1, ?_⟩
  unfold scheduleStepBV
  rw [hout.2, ← Array.sum_toList, ← Array.sum_toList]
  simp only [Array.toList_map, List.map_cons, List.map_nil, hs0'.2, hs1'.2,
    (hw.getElem! (i := i - 16) (by grind)).2,
    (hw.getElem! (i := i - 7) (by grind)).2]

@[spec] theorem scheduleStep_sound {w : Vector (U 32) 64}
    (hw : ∀ i : Fin 64, w[i].Valid ρ) (i : Nat) (hi : i ∈ [16:64]) :
    ⦃⌜True⌝⦄ Sound.interp ρ (scheduleStep i w)
    ⦃⇓ out => ⌜U.Rel ρ out (scheduleStepBV i (w.map (·.eval ρ)))⌝⦄ := by
  unfold scheduleStep
  mvcgen
  case vc1.success.success =>
    intro hvalid heval
    exact scheduleResult (Vector.Rel.refl hw) i hi
      (by assumption) (by assumption) ⟨hvalid, heval⟩
  case vc2 =>
    intro hs1 j
    fin_cases j
    · exact U.valid_getElem! hw (by grind)
    · exact (by assumption : U.Rel ρ _ _).1
    · exact U.valid_getElem! hw (by grind)
    · exact hs1.1

@[spec] theorem scheduleStep_complete {w : Vector (U 32) 64}
    (hw : ∀ i : Fin 64, w[i].Valid ρ) (i : Nat) (hi : i ∈ [16:64]) :
    ⦃⌜True⌝⦄ Complete.interp ρ (scheduleStep i w)
    ⦃⇓ out => ⌜U.Rel ρ out (scheduleStepBV i (w.map (·.eval ρ)))⌝⦄ := by
  unfold scheduleStep
  mvcgen
  case vc1.success.success =>
    intro hvalid heval
    exact scheduleResult (Vector.Rel.refl hw) i hi
      (by assumption) (by assumption) ⟨hvalid, heval⟩
  case vc2 =>
    intro hs1 j
    fin_cases j
    · exact U.valid_getElem! hw (by grind)
    · exact (by assumption : U.Rel ρ _ _).1
    · exact U.valid_getElem! hw (by grind)
    · exact hs1.1

private theorem coupledRound_arith
    (d h S1 ki wi ch S0 maj : BitVec 32) :
    ((((((d + h) + S1) + ki) + wi) + ch) + S0 + maj) - d =
      (((((h + S1) + ki) + wi) + S0) + ch) + maj := by
  apply BitVec.sub_eq_iff_eq_add.mpr
  ac_rfl

private theorem roundResult {w : Vector (U 32) 64}
    {wv : Vector (BitVec 32) 64} (hw : Vector.Rel ρ w wv)
    {r : RoundState (U 32)} {rv : RoundState (BitVec 32)}
    (hr : RoundState.Rel ρ r rv) (i : Nat) (hi : i ∈ [0:64])
    {S1 S0 newE newA : U 32} {ch2 maj2 : LC ℤ}
    (hS1 : U.Rel ρ S1 (Word.eval ρ.bool
      (r.2.2.2.2.1.bits.rotateRight 6 ^^^
        r.2.2.2.2.1.bits.rotateRight 11 ^^^
        r.2.2.2.2.1.bits.rotateRight 25)))
    (_hch : ch2.eval ρ.int = 2 * (chBV (r.2.2.2.2.1.eval ρ)
      (r.2.2.2.2.2.1.eval ρ) (r.2.2.2.2.2.2.1.eval ρ)).toNat)
    (hS0 : U.Rel ρ S0 (Word.eval ρ.bool
      (r.1.bits.rotateRight 2 ^^^ r.1.bits.rotateRight 13 ^^^
        r.1.bits.rotateRight 22)))
    (_hmaj : maj2.eval ρ.int =
      2 * (majBV (r.1.eval ρ) (r.2.1.eval ρ) (r.2.2.1.eval ρ)).toNat)
    (hE : U.Rel ρ newE (r.2.2.2.1.eval ρ + r.2.2.2.2.2.2.2.eval ρ +
      S1.eval ρ + (k[i] : U 32).eval ρ + w[i].eval ρ +
      chBV (r.2.2.2.2.1.eval ρ) (r.2.2.2.2.2.1.eval ρ)
        (r.2.2.2.2.2.2.1.eval ρ)))
    (hA : U.Rel ρ newA (newE.eval ρ + S0.eval ρ +
      majBV (r.1.eval ρ) (r.2.1.eval ρ) (r.2.2.1.eval ρ) -
      r.2.2.2.1.eval ρ)) :
    RoundState.Rel ρ
      ⟨newA, r.1, r.2.1, r.2.2.1, newE,
        r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1⟩
      (roundStepBV i wv rv) := by
  have hS1' := hr.e.rotateXor3 (by decide) (by decide) (by decide) hS1
  have hS0' := hr.a.rotateXor3 (by decide) (by decide) (by decide) hS0
  have hwi : w[i].eval ρ = wv[i] := by
    simpa only [Fin.getElem_fin] using (hw ⟨i, by grind⟩).2
  have hA' : newA.eval ρ =
      r.2.2.2.2.2.2.2.eval ρ + S1.eval ρ + (k[i] : U 32).eval ρ +
        w[i].eval ρ + S0.eval ρ +
        chBV (r.2.2.2.2.1.eval ρ) (r.2.2.2.2.2.1.eval ρ)
          (r.2.2.2.2.2.2.1.eval ρ) +
        majBV (r.1.eval ρ) (r.2.1.eval ρ) (r.2.2.1.eval ρ) := by
    rw [hA.2, hE.2]
    exact coupledRound_arith _ _ _ _ _ _ _ _
  refine ⟨⟨hA.1, hr.a.1, hr.b.1, hr.c.1, hE.1,
    hr.e.1, hr.f.1, hr.g.1⟩, ?_⟩
  unfold RoundState.eval roundStepBV
  simp only [getElem!_pos k i (by grind), getElem!_pos wv i (by grind)]
  rw [hA', hr.a.2, hr.b.2, hr.c.2, hE.2, hr.e.2, hr.f.2, hr.g.2,
    hr.h.2, hr.d.2, hS1'.2, hS0'.2, hwi]
  simp only [U.eval_bitVec]
  simp only [← Array.sum_toList]
  simp only [List.sum_cons, List.sum_nil]
  congr 1 <;> ac_rfl

theorem roundStep_sound_rel {w : Vector (U 32) 64}
    {wv : Vector (BitVec 32) 64} (hw : Vector.Rel ρ w wv)
    {r : RoundState (U 32)} {rv : RoundState (BitVec 32)}
    (hr : RoundState.Rel ρ r rv) (i : Nat) (hi : i ∈ [0:64]) :
    ⦃⌜True⌝⦄ Sound.interp ρ (roundStep i hi (w, r))
    ⦃⇓ out => ⌜RoundState.Rel ρ out (roundStepBV i wv rv)⌝⦄ := by
  have hwi : w[i].Valid ρ := (hw ⟨i, by grind⟩).1
  unfold roundStep
  mvcgen -trivial
  case vc1.hu | vc2.hv | vc3.hw | vc4.hu | vc5.hv | vc6.hw =>
    first | exact hr.a.1 | exact hr.b.1 | exact hr.c.1 |
      exact hr.e.1 | exact hr.f.1 | exact hr.g.1
  case vc7.x =>
    exact chBV (r.2.2.2.2.1.eval ρ) (r.2.2.2.2.2.1.eval ρ)
      (r.2.2.2.2.2.2.1.eval ρ)
  case vc8.ha => exact hr.d.1
  case vc9.hb => exact hr.h.1
  case vc10.hc => grind [U.Rel]
  case vc11.hd => exact U.valid_bitVec _
  case vc12.he => exact hwi
  case vc13.hx => assumption
  case vc14.maj => exact majBV (r.1.eval ρ) (r.2.1.eval ρ) (r.2.2.1.eval ρ)
  case vc15.hd => exact hr.d.1
  case vc16.he | vc17.hS0 => grind [U.Rel]
  case vc18.hmaj => assumption
  case vc19.success =>
    rename_i S1 hS1 ch2 hch S0 hS0 maj2 hmaj E hE A hA
    exact roundResult hw hr i hi hS1 hch hS0 hmaj hE hA

@[spec] theorem roundStep_sound {w : Vector (U 32) 64}
    (hw : ∀ i : Fin 64, w[i].Valid ρ) {r : RoundState (U 32)}
    (hr : r.Valid ρ) (i : Nat) (hi : i ∈ [0:64]) :
    ⦃⌜True⌝⦄ Sound.interp ρ (roundStep i hi (w, r))
    ⦃⇓ out => ⌜RoundState.Rel ρ out
      (roundStepBV i (w.map (·.eval ρ)) (r.eval ρ))⌝⦄ :=
  roundStep_sound_rel (Vector.Rel.refl hw) (RoundState.Rel.refl hr) i hi

@[spec] theorem roundStep_complete {w : Vector (U 32) 64}
    (hw : ∀ i : Fin 64, w[i].Valid ρ) {r : RoundState (U 32)}
    (hr : r.Valid ρ) (i : Nat) (hi : i ∈ [0:64]) :
    ⦃⌜True⌝⦄ Complete.interp ρ (roundStep i hi (w, r))
    ⦃⇓ out => ⌜out.Valid ρ⌝⦄ := by
  have hwi : w[i].Valid ρ := hw ⟨i, by grind⟩
  unfold roundStep
  mvcgen -trivial
  case vc1.hu | vc2.hv | vc3.hw | vc4.hu | vc5.hv | vc6.hw =>
    first | exact hr.1 | exact hr.2.1 | exact hr.2.2.1 |
      exact hr.2.2.2.2.1 | exact hr.2.2.2.2.2.1 |
      exact hr.2.2.2.2.2.2.1
  case vc7.x =>
    exact chBV (r.2.2.2.2.1.eval ρ) (r.2.2.2.2.2.1.eval ρ)
      (r.2.2.2.2.2.2.1.eval ρ)
  case vc8.ha => exact hr.2.2.2.1
  case vc9.hb => exact hr.2.2.2.2.2.2.2
  case vc10.hc => grind [U.Rel]
  case vc11.hd => exact U.valid_bitVec _
  case vc12.he => exact hwi
  case vc13.hx => assumption
  case vc14.maj => exact majBV (r.1.eval ρ) (r.2.1.eval ρ) (r.2.2.1.eval ρ)
  case vc15.hd => exact hr.2.2.2.1
  case vc16.he | vc17.hS0 => grind [U.Rel]
  case vc18.hmaj => assumption
  case vc19.success => grind [RoundState.Valid, U.Rel]

private theorem mem_range16_62_to_64 {i : Nat} (hi : i ∈ [16:62]) :
    i ∈ [16:64] := by
  change 16 ≤ i ∧ i < 62 ∧ (i - 16) % 1 = 0 at hi
  change 16 ≤ i ∧ i < 64 ∧ (i - 16) % 1 = 0
  exact ⟨hi.1, by omega, hi.2.2⟩

private theorem mem_range0_62_to_64 {i : Nat} (hi : i ∈ [0:62]) :
    i ∈ [0:64] := by
  change 0 ≤ i ∧ i < 62 ∧ (i - 0) % 1 = 0 at hi
  change 0 ≤ i ∧ i < 64 ∧ (i - 0) % 1 = 0
  exact ⟨hi.1, by omega, hi.2.2⟩

@[spec] theorem scheduleRoundStep_sound
    {x : RoundState (U 32) × Vector (U 32) 64}
    {xv : RoundState (BitVec 32) × Vector (BitVec 32) 64}
    (hx : RoundState.Rel ρ x.1 xv.1 ∧ Vector.Rel ρ x.2 xv.2)
    (i : Nat) (hi : i ∈ [16:62]) :
    ⦃⌜True⌝⦄ Sound.interp ρ (scheduleRoundStep i hi x)
    ⦃⇓ out => ⌜RoundState.Rel ρ out.1
        (roundStepBV i (xv.2.set! i (scheduleStepBV i xv.2)) xv.1) ∧
      Vector.Rel ρ out.2 (xv.2.set! i (scheduleStepBV i xv.2))⌝⦄ := by
  unfold scheduleRoundStep
  mvcgen -trivial
  case vc1.hw => exact Vector.Rel.valid hx.2
  case vc2.hi => exact mem_range16_62_to_64 hi
  case vc3.hw => exact Vector.Rel.valid (hx.2.set! (by assumption) i)
  case vc4.hr => exact hx.1.1
  case vc5.success =>
    rename_i wi hwi out hout
    rw [Vector.Rel.eval_eq hx.2] at hwi
    have hw := hx.2.set! hwi i
    rw [Vector.Rel.eval_eq hw, RoundState.Rel.eval_eq hx.1] at hout
    exact ⟨hout, hw⟩

@[spec] theorem scheduleRoundStep_complete
    {x : RoundState (U 32) × Vector (U 32) 64}
    (hx : x.1.Valid ρ ∧ ∀ j : Fin 64, x.2[j].Valid ρ)
    (i : Nat) (hi : i ∈ [16:62]) :
    ⦃⌜True⌝⦄ Complete.interp ρ (scheduleRoundStep i hi x)
    ⦃⇓ out => ⌜out.1.Valid ρ ∧ ∀ j : Fin 64, out.2[j].Valid ρ⌝⦄ := by
  unfold scheduleRoundStep
  mvcgen -trivial
  case vc1.hw => exact hx.2
  case vc2.hi => exact mem_range16_62_to_64 hi
  case vc3.hw => exact U.allValid_set! hx.2 (by grind [U.Rel]) _
  case vc4.hr => exact hx.1
  case vc5.success => exact ⟨by assumption,
    U.allValid_set! hx.2 (by grind [U.Rel]) _⟩

private theorem inlineCoupledRound_arith
    (d h S1 ki w16 s0 w7 s1 ch S0 maj : BitVec 32) :
    (((((((((d + h) + S1) + ki) + w16) + s0) + w7) + s1) + ch) + S0 + maj) - d =
      ((((((((h + S1) + ki) + w16) + s0) + w7) + s1) + S0) + ch) + maj := by
  apply BitVec.sub_eq_iff_eq_add.mpr
  ac_rfl

set_option maxHeartbeats 1000000 in
private theorem inlineScheduleRoundResult {w : Vector (U 32) 64}
    {wv : Vector (BitVec 32) 64} (hw : Vector.Rel ρ w wv)
    {r : RoundState (U 32)} {rv : RoundState (BitVec 32)}
    (hr : RoundState.Rel ρ r rv) (i : Nat) (hi : i ∈ [16:64])
    {s0 s1 S1 S0 newE newA : U 32} {ch2 maj2 : LC ℤ}
    (hs0 : U.Rel ρ s0 (Word.eval ρ.bool
      (w[i - 15]!.bits.rotateRight 7 ^^^ w[i - 15]!.bits.rotateRight 18 ^^^
        (w[i - 15]!.bits >>> 3))))
    (hs1 : U.Rel ρ s1 (Word.eval ρ.bool
      (w[i - 2]!.bits.rotateRight 17 ^^^ w[i - 2]!.bits.rotateRight 19 ^^^
        (w[i - 2]!.bits >>> 10))))
    (hS1 : U.Rel ρ S1 (Word.eval ρ.bool
      (r.2.2.2.2.1.bits.rotateRight 6 ^^^ r.2.2.2.2.1.bits.rotateRight 11 ^^^
        r.2.2.2.2.1.bits.rotateRight 25)))
    (_hch : ch2.eval ρ.int = 2 * (chBV (r.2.2.2.2.1.eval ρ)
      (r.2.2.2.2.2.1.eval ρ) (r.2.2.2.2.2.2.1.eval ρ)).toNat)
    (hS0 : U.Rel ρ S0 (Word.eval ρ.bool
      (r.1.bits.rotateRight 2 ^^^ r.1.bits.rotateRight 13 ^^^
        r.1.bits.rotateRight 22)))
    (_hmaj : maj2.eval ρ.int =
      2 * (majBV (r.1.eval ρ) (r.2.1.eval ρ) (r.2.2.1.eval ρ)).toNat)
    (hE : U.Rel ρ newE
      (r.2.2.2.1.eval ρ + r.2.2.2.2.2.2.2.eval ρ + S1.eval ρ +
        (k[i] : U 32).eval ρ + w[i - 16]!.eval ρ + s0.eval ρ +
        w[i - 7]!.eval ρ + s1.eval ρ +
        chBV (r.2.2.2.2.1.eval ρ) (r.2.2.2.2.2.1.eval ρ)
          (r.2.2.2.2.2.2.1.eval ρ)))
    (hA : U.Rel ρ newA (newE.eval ρ + S0.eval ρ +
      majBV (r.1.eval ρ) (r.2.1.eval ρ) (r.2.2.1.eval ρ) -
      r.2.2.2.1.eval ρ)) :
    RoundState.Rel ρ
      ⟨newA, r.1, r.2.1, r.2.2.1, newE,
        r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1⟩
      (inlineScheduleRoundBV i wv rv) := by
  have hs0' := (hw.getElem! (i := i - 15) (by grind)).rotateXorShift
    (by decide) (by decide) hs0
  have hs1' := (hw.getElem! (i := i - 2) (by grind)).rotateXorShift
    (by decide) (by decide) hs1
  have hS1' := hr.e.rotateXor3 (by decide) (by decide) (by decide) hS1
  have hS0' := hr.a.rotateXor3 (by decide) (by decide) (by decide) hS0
  have hw16 := (hw.getElem! (i := i - 16) (by grind)).2
  have hw7 := (hw.getElem! (i := i - 7) (by grind)).2
  have hA' : newA.eval ρ =
      r.2.2.2.2.2.2.2.eval ρ + S1.eval ρ + (k[i] : U 32).eval ρ +
        w[i - 16]!.eval ρ + s0.eval ρ + w[i - 7]!.eval ρ + s1.eval ρ +
        S0.eval ρ + chBV (r.2.2.2.2.1.eval ρ)
          (r.2.2.2.2.2.1.eval ρ) (r.2.2.2.2.2.2.1.eval ρ) +
        majBV (r.1.eval ρ) (r.2.1.eval ρ) (r.2.2.1.eval ρ) := by
    rw [hA.2, hE.2]
    exact inlineCoupledRound_arith _ _ _ _ _ _ _ _ _ _ _
  refine ⟨⟨hA.1, hr.a.1, hr.b.1, hr.c.1, hE.1,
    hr.e.1, hr.f.1, hr.g.1⟩, ?_⟩
  unfold RoundState.eval inlineScheduleRoundBV scheduleStepBV
  simp only [getElem!_pos k i (by grind)]
  rw [hA', hr.a.2, hr.b.2, hr.c.2, hE.2, hr.e.2, hr.f.2, hr.g.2,
    hr.h.2, hr.d.2, hS1'.2, hS0'.2, hs0'.2, hs1'.2, hw16, hw7]
  simp only [U.eval_bitVec, ← Array.sum_toList, List.sum_cons, List.sum_nil]
  congr 1 <;> ac_rfl

@[spec] theorem terminalScheduleParts_sound {w : Vector (U 32) 64}
    (hw : ∀ j : Fin 64, w[j].Valid ρ) (i : Nat) (hi : i ∈ [16:64]) :
    ⦃⌜True⌝⦄ Sound.interp ρ (terminalScheduleParts i w)
    ⦃⇓ out => ⌜U.Rel ρ out.1 (Word.eval ρ.bool
        (w[i - 15]!.bits.rotateRight 7 ^^^ w[i - 15]!.bits.rotateRight 18 ^^^
          (w[i - 15]!.bits >>> 3))) ∧
      U.Rel ρ out.2 (Word.eval ρ.bool
        (w[i - 2]!.bits.rotateRight 17 ^^^ w[i - 2]!.bits.rotateRight 19 ^^^
          (w[i - 2]!.bits >>> 10)))⌝⦄ := by
  unfold terminalScheduleParts
  mvcgen

@[spec] theorem terminalScheduleParts_complete {w : Vector (U 32) 64}
    (hw : ∀ j : Fin 64, w[j].Valid ρ) (i : Nat) (hi : i ∈ [16:64]) :
    ⦃⌜True⌝⦄ Complete.interp ρ (terminalScheduleParts i w)
    ⦃⇓ out => ⌜out.1.Valid ρ ∧ out.2.Valid ρ⌝⦄ := by
  unfold terminalScheduleParts
  mvcgen
  case vc1.success =>
    exact ⟨(by assumption : U.Rel ρ _ _).1,
      (by assumption : U.Rel ρ _ _).1⟩

set_option maxHeartbeats 1000000 in
@[spec] theorem roundWithScheduleParts_sound_rel {w : Vector (U 32) 64}
    {wv : Vector (BitVec 32) 64} (hw : Vector.Rel ρ w wv)
    {r : RoundState (U 32)} {rv : RoundState (BitVec 32)}
    (hr : RoundState.Rel ρ r rv) (i : Nat) (hi : i ∈ [16:64])
    {s0 s1 : U 32} :
    ⦃⌜U.Rel ρ s0 (Word.eval ρ.bool
        (w[i - 15]!.bits.rotateRight 7 ^^^ w[i - 15]!.bits.rotateRight 18 ^^^
          (w[i - 15]!.bits >>> 3))) ∧
      U.Rel ρ s1 (Word.eval ρ.bool
        (w[i - 2]!.bits.rotateRight 17 ^^^ w[i - 2]!.bits.rotateRight 19 ^^^
          (w[i - 2]!.bits >>> 10)))⌝⦄
    Sound.interp ρ (roundWithScheduleParts i hi (w, r, s0, s1))
    ⦃⇓ out => ⌜RoundState.Rel ρ out (inlineScheduleRoundBV i wv rv)⌝⦄ := by
  unfold roundWithScheduleParts
  mvcgen -trivial
  case vc1.hu | vc2.hv | vc3.hw | vc4.hu | vc5.hv | vc6.hw =>
    first | exact hr.a.1 | exact hr.b.1 | exact hr.c.1 |
      exact hr.e.1 | exact hr.f.1 | exact hr.g.1
  case vc7.x =>
    exact chBV (r.2.2.2.2.1.eval ρ) (r.2.2.2.2.2.1.eval ρ)
      (r.2.2.2.2.2.2.1.eval ρ)
  case vc8.ha => exact hr.d.1
  case vc9.hb => exact hr.h.1
  case vc10.hc => grind [U.Rel]
  case vc11.hd => exact U.valid_bitVec _
  case vc12.he => exact U.valid_getElem! (Vector.Rel.valid hw) (by grind)
  case vc13.hf =>
    have hp : U.Rel ρ s0 (Word.eval ρ.bool
          (w[i - 15]!.bits.rotateRight 7 ^^^ w[i - 15]!.bits.rotateRight 18 ^^^
            (w[i - 15]!.bits >>> 3))) ∧
        U.Rel ρ s1 (Word.eval ρ.bool
          (w[i - 2]!.bits.rotateRight 17 ^^^ w[i - 2]!.bits.rotateRight 19 ^^^
            (w[i - 2]!.bits >>> 10))) := by assumption
    exact hp.1.1
  case vc14.hg => exact U.valid_getElem! (Vector.Rel.valid hw) (by grind)
  case vc15.hh =>
    have hp : U.Rel ρ s0 (Word.eval ρ.bool
          (w[i - 15]!.bits.rotateRight 7 ^^^ w[i - 15]!.bits.rotateRight 18 ^^^
            (w[i - 15]!.bits >>> 3))) ∧
        U.Rel ρ s1 (Word.eval ρ.bool
          (w[i - 2]!.bits.rotateRight 17 ^^^ w[i - 2]!.bits.rotateRight 19 ^^^
            (w[i - 2]!.bits >>> 10))) := by assumption
    exact hp.2.1
  case vc16.hx => assumption
  case vc17.maj =>
    exact majBV (r.1.eval ρ) (r.2.1.eval ρ) (r.2.2.1.eval ρ)
  case vc18.hd => exact hr.d.1
  case vc19.he | vc20.hS0 => grind [U.Rel]
  case vc21.hmaj => assumption
  case vc22.success =>
    rename_i S1 hS1 ch2 hch S0 hS0 maj2 hmaj E hE A hA
    have hp : U.Rel ρ s0 (Word.eval ρ.bool
          (w[i - 15]!.bits.rotateRight 7 ^^^ w[i - 15]!.bits.rotateRight 18 ^^^
            (w[i - 15]!.bits >>> 3))) ∧
        U.Rel ρ s1 (Word.eval ρ.bool
          (w[i - 2]!.bits.rotateRight 17 ^^^ w[i - 2]!.bits.rotateRight 19 ^^^
            (w[i - 2]!.bits >>> 10))) := by assumption
    exact inlineScheduleRoundResult hw hr i hi hp.1 hp.2 hS1 hch hS0 hmaj hE hA

set_option maxHeartbeats 1000000 in
@[spec] theorem roundWithScheduleParts_complete {w : Vector (U 32) 64}
    (hw : ∀ j : Fin 64, w[j].Valid ρ) {r : RoundState (U 32)}
    (hr : r.Valid ρ) (i : Nat) (hi : i ∈ [16:64])
    {s0 s1 : U 32} :
    ⦃⌜s0.Valid ρ ∧ s1.Valid ρ⌝⦄
    Complete.interp ρ (roundWithScheduleParts i hi (w, r, s0, s1))
    ⦃⇓ out => ⌜out.Valid ρ⌝⦄ := by
  unfold roundWithScheduleParts
  mvcgen -trivial
  case vc1.hu | vc2.hv | vc3.hw | vc4.hu | vc5.hv | vc6.hw =>
    first | exact hr.1 | exact hr.2.1 | exact hr.2.2.1 |
      exact hr.2.2.2.2.1 | exact hr.2.2.2.2.2.1 |
      exact hr.2.2.2.2.2.2.1
  case vc7.x =>
    exact chBV (r.2.2.2.2.1.eval ρ) (r.2.2.2.2.2.1.eval ρ)
      (r.2.2.2.2.2.2.1.eval ρ)
  case vc8.ha => exact hr.2.2.2.1
  case vc9.hb => exact hr.2.2.2.2.2.2.2
  case vc10.hc => grind [U.Rel]
  case vc11.hd => exact U.valid_bitVec _
  case vc12.he => exact U.valid_getElem! hw (by grind)
  case vc13.hf => exact (by assumption : s0.Valid ρ ∧ s1.Valid ρ).1
  case vc14.hg => exact U.valid_getElem! hw (by grind)
  case vc15.hh => exact (by assumption : s0.Valid ρ ∧ s1.Valid ρ).2
  case vc16.hx => assumption
  case vc17.maj =>
    exact majBV (r.1.eval ρ) (r.2.1.eval ρ) (r.2.2.1.eval ρ)
  case vc18.hd => exact hr.2.2.2.1
  case vc19.he | vc20.hS0 => grind [U.Rel]
  case vc21.hmaj => assumption
  case vc22.success => grind [RoundState.Valid, U.Rel]

@[spec] theorem inlineScheduleRound_sound_rel {w : Vector (U 32) 64}
    {wv : Vector (BitVec 32) 64} (hw : Vector.Rel ρ w wv)
    {r : RoundState (U 32)} {rv : RoundState (BitVec 32)}
    (hr : RoundState.Rel ρ r rv) (i : Nat) (hi : i ∈ [16:64]) :
    ⦃⌜True⌝⦄ Sound.interp ρ (inlineScheduleRound i hi (w, r))
    ⦃⇓ out => ⌜RoundState.Rel ρ out (inlineScheduleRoundBV i wv rv)⌝⦄ := by
  unfold inlineScheduleRound
  rw [Sound.interp_bind]
  apply Triple.bind (Q := fun parts =>
    ⌜U.Rel ρ parts.1 (Word.eval ρ.bool
        (w[i - 15]!.bits.rotateRight 7 ^^^ w[i - 15]!.bits.rotateRight 18 ^^^
          (w[i - 15]!.bits >>> 3))) ∧
      U.Rel ρ parts.2 (Word.eval ρ.bool
        (w[i - 2]!.bits.rotateRight 17 ^^^ w[i - 2]!.bits.rotateRight 19 ^^^
          (w[i - 2]!.bits >>> 10)))⌝)
  case hx => exact terminalScheduleParts_sound (Vector.Rel.valid hw) i hi
  case hf =>
    intro parts
    exact roundWithScheduleParts_sound_rel hw hr i hi

@[spec] theorem inlineScheduleRound_complete {w : Vector (U 32) 64}
    (hw : ∀ j : Fin 64, w[j].Valid ρ) {r : RoundState (U 32)}
    (hr : r.Valid ρ) (i : Nat) (hi : i ∈ [16:64]) :
    ⦃⌜True⌝⦄ Complete.interp ρ (inlineScheduleRound i hi (w, r))
    ⦃⇓ out => ⌜out.Valid ρ⌝⦄ := by
  unfold inlineScheduleRound
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun parts => ⌜parts.1.Valid ρ ∧ parts.2.Valid ρ⌝)
  case hx => exact terminalScheduleParts_complete hw i hi
  case hf =>
    intro parts
    exact roundWithScheduleParts_complete hw hr i hi

def finishBV (s : Vector (BitVec 32) 8) (r : RoundState (BitVec 32)) :
    Vector (BitVec 32) 8 :=
  #v[s[0] + r.1, s[1] + r.2.1, s[2] + r.2.2.1,
    s[3] + r.2.2.2.1, s[4] + r.2.2.2.2.1,
    s[5] + r.2.2.2.2.2.1, s[6] + r.2.2.2.2.2.2.1,
    s[7] + r.2.2.2.2.2.2.2]

theorem finishBV_get (s : Vector (BitVec 32) 8)
    (r : RoundState (BitVec 32)) (i : Fin 8) :
    (finishBV s r)[i] = s[i] + (roundVector r)[i] := by
  fin_cases i <;> rfl

def finalRoundCoreBV (i : Nat) (w : Vector (BitVec 32) 64)
    (r : RoundState (BitVec 32)) (s : Vector (BitVec 32) 8) :
    BitVec 32 × BitVec 32 :=
  let S1 := r.2.2.2.2.1.rotateRight 6 ^^^ r.2.2.2.2.1.rotateRight 11 ^^^
    r.2.2.2.2.1.rotateRight 25
  let ch := chBV r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1
  let S0 := r.1.rotateRight 2 ^^^ r.1.rotateRight 13 ^^^ r.1.rotateRight 22
  let maj := majBV r.1 r.2.1 r.2.2.1
  let wi := scheduleStepBV i w
  let outE := s[4] +
    #[r.2.2.2.1, r.2.2.2.2.2.2.2, S1, ch, k[i]!, wi].sum
  let outA := outE + S0 + s[0] + maj - s[4] - r.2.2.2.1
  (outA, outE)

theorem finalRoundCoreBV_eq (i : Nat) (w : Vector (BitVec 32) 64)
    (r : RoundState (BitVec 32)) (s : Vector (BitVec 32) 8) :
    finalRoundCoreBV i w r s =
      ((finishBV s (inlineScheduleRoundBV i w r))[0],
        (finishBV s (inlineScheduleRoundBV i w r))[4]) := by
  apply Prod.ext
  · change (finalRoundCoreBV i w r s).1 =
      s[0] + (inlineScheduleRoundBV i w r).1
    unfold finalRoundCoreBV inlineScheduleRoundBV
    simp only [← Array.sum_toList, List.sum_cons, List.sum_nil]
    apply BitVec.sub_eq_iff_eq_add.mpr
    apply BitVec.sub_eq_iff_eq_add.mpr
    ac_rfl
  · change (finalRoundCoreBV i w r s).2 =
      s[4] + (inlineScheduleRoundBV i w r).2.2.2.2.1
    unfold finalRoundCoreBV inlineScheduleRoundBV
    simp only [← Array.sum_toList, List.sum_cons, List.sum_nil]

theorem finish_eq (s : Vector (U 32) 8) (r : RoundState (U 32)) :
    finish (s, r) = Vector.ofFnM (fun i =>
      U.sumFixed #v[s[i], (roundVector r)[i]]) := by
  simp [finish, Vector.ofFnM_succ, Vector.ofFnM_zero, roundVector,
    U.sum2_eq_sumFixed]

@[spec] theorem finish_sound {s : Vector (U 32) 8}
    {sv : Vector (BitVec 32) 8} (hs : Vector.Rel ρ s sv)
    {r : RoundState (U 32)} {rv : RoundState (BitVec 32)}
    (hr : RoundState.Rel ρ r rv) :
    ⦃⌜True⌝⦄ Sound.interp ρ (finish (s, r))
    ⦃⇓ out => ⌜Vector.Rel ρ out (finishBV sv rv)⌝⦄ := by
  rw [finish_eq]
  apply Sound.vectorOfFnM
    (R := fun i out => U.Rel ρ out (finishBV sv rv)[i])
  intro i
  rw [finishBV_get]
  exact U.sumPair_sound (hs i) (hr.vector i)

@[spec] theorem finish_complete {s : Vector (U 32) 8}
    (hs : ∀ i : Fin 8, s[i].Valid ρ)
    {r : RoundState (U 32)} (hr : r.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (finish (s, r))
    ⦃⇓ out => ⌜∀ i : Fin 8, out[i].Valid ρ⌝⦄ := by
  rw [finish_eq]
  apply Complete.vectorOfFnM
    (f := fun i : Fin 8 => U.sumFixed #v[s[i], (roundVector r)[i]])
    (R := fun (_ : Fin 8) out => out.Valid ρ)
  intro i
  exact Triple.iff_conseq.mp
    (U.sumPair_complete (U.Rel.refl (hs i))
      ((RoundState.Rel.refl hr).vector i)) (by simp) (by
        simp only [PostCond.entails, SPred.entails_nil]
        exact ⟨fun _ h => h.1, ExceptConds.entails.refl _⟩)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 100000 in
@[spec] theorem finalRoundCore_sound {w : Vector (U 32) 64}
    {wv : Vector (BitVec 32) 64} (hw : Vector.Rel ρ w wv)
    {r : RoundState (U 32)} {rv : RoundState (BitVec 32)}
    (hr : RoundState.Rel ρ r rv) {s : Vector (U 32) 8}
    {sv : Vector (BitVec 32) 8} (hs : Vector.Rel ρ s sv)
    (i : Nat) (hi : i ∈ [16:64]) :
    ⦃⌜True⌝⦄ Sound.interp ρ (finalRoundCore i hi (w, r, s))
    ⦃⇓ out => ⌜U.Rel ρ out.1 (finalRoundCoreBV i wv rv sv).1 ∧
      U.Rel ρ out.2 (finalRoundCoreBV i wv rv sv).2⌝⦄ := by
  unfold finalRoundCore finalRoundBody finalRoundTransforms finalRoundSums
  mvcgen -trivial
  case vc1.hw => exact Vector.Rel.valid hw
  case vc2.hi => exact hi
  case vc3.hu | vc4.hv | vc5.hw | vc6.hu | vc7.hv | vc8.hw =>
    first | exact hr.a.1 | exact hr.b.1 | exact hr.c.1 |
      exact hr.e.1 | exact hr.f.1 | exact hr.g.1
  case vc9.x =>
    exact chBV (r.2.2.2.2.1.eval ρ) (r.2.2.2.2.2.1.eval ρ)
      (r.2.2.2.2.2.2.1.eval ρ)
  case vc10.ha => exact hr.d.1
  case vc11.hb => exact hr.h.1
  case vc12.hc => grind [U.Rel]
  case vc13.hd => exact U.valid_bitVec _
  case vc14.he => exact U.valid_getElem! (Vector.Rel.valid hw) (by grind)
  case vc15.hf => grind [U.Rel]
  case vc16.hg => exact U.valid_getElem! (Vector.Rel.valid hw) (by grind)
  case vc17.hh => grind [U.Rel]
  case vc18.hi => exact (hs 4).1
  case vc19.hx => assumption
  case vc20.maj => exact majBV (r.1.eval ρ) (r.2.1.eval ρ) (r.2.2.1.eval ρ)
  case vc21.hd => exact hr.d.1
  case vc22.he => grind [U.Rel]
  case vc23.hS0 => grind [U.Rel]
  case vc24.hA => exact (hs 0).1
  case vc25.hE => exact (hs 4).1
  case vc26.hmaj => assumption
  case vc27.success =>
    rename_i parts hparts S1 hS1 ch2 hch S0 hS0 maj2 hmaj
      outE houtE outA houtA
    have hs0' := (hw.getElem! (i := i - 15) (by grind)).rotateXorShift
      (by decide) (by decide) hparts.1
    have hs1' := (hw.getElem! (i := i - 2) (by grind)).rotateXorShift
      (by decide) (by decide) hparts.2
    have hS1' := hr.e.rotateXor3 (by decide) (by decide) (by decide) hS1
    have hS0' := hr.a.rotateXor3 (by decide) (by decide) (by decide) hS0
    have houtE' : outE.eval ρ = (finalRoundCoreBV i wv rv sv).2 := by
      unfold finalRoundCoreBV scheduleStepBV
      simp only [getElem!_pos k i (by grind)]
      simp only [houtE.2, hS1'.2, hr.d.2, hr.h.2, (hs 4).2,
        hs0'.2, hs1'.2,
        (hw.getElem! (i := i - 16) (by grind)).2,
        (hw.getElem! (i := i - 7) (by grind)).2]
      rw [show s[4].eval ρ = sv[4] from (hs 4).2]
      rw [show chBV (r.2.2.2.2.1.eval ρ) (r.2.2.2.2.2.1.eval ρ)
          (r.2.2.2.2.2.2.1.eval ρ) =
          chBV rv.2.2.2.2.1 rv.2.2.2.2.2.1 rv.2.2.2.2.2.2.1 by
        rw [hr.e.2, hr.f.2, hr.g.2]]
      simp only [U.eval_bitVec, ← Array.sum_toList, List.sum_cons, List.sum_nil]
      ac_rfl
    have houtA' : outA.eval ρ = (finalRoundCoreBV i wv rv sv).1 := by
      unfold finalRoundCoreBV
      simp only [houtA.2, houtE', hS0'.2, (hs 0).2, (hs 4).2, hr.d.2]
      rw [show s[0].eval ρ = sv[0] from (hs 0).2,
        show s[4].eval ρ = sv[4] from (hs 4).2]
      rw [show majBV (r.1.eval ρ) (r.2.1.eval ρ) (r.2.2.1.eval ρ) =
          majBV rv.1 rv.2.1 rv.2.2.1 by rw [hr.a.2, hr.b.2, hr.c.2]]
      rfl
    constructor
    · exact ⟨houtA.1, houtA'⟩
    · exact ⟨houtE.1, houtE'⟩

set_option maxHeartbeats 100000 in
@[spec] theorem finalRoundCore_complete {w : Vector (U 32) 64}
    (hw : ∀ j : Fin 64, w[j].Valid ρ) {r : RoundState (U 32)}
    (hr : r.Valid ρ) {s : Vector (U 32) 8}
    (hs : ∀ j : Fin 8, s[j].Valid ρ) (i : Nat) (hi : i ∈ [16:64]) :
    ⦃⌜True⌝⦄ Complete.interp ρ (finalRoundCore i hi (w, r, s))
    ⦃⇓ out => ⌜out.1.Valid ρ ∧ out.2.Valid ρ⌝⦄ := by
  unfold finalRoundCore finalRoundBody finalRoundTransforms finalRoundSums
  mvcgen -trivial
  case vc1.hw => exact hw
  case vc2.hi => exact hi
  case vc3.hu | vc4.hv | vc5.hw | vc6.hu | vc7.hv | vc8.hw =>
    first | exact hr.1 | exact hr.2.1 | exact hr.2.2.1 |
      exact hr.2.2.2.2.1 | exact hr.2.2.2.2.2.1 |
      exact hr.2.2.2.2.2.2.1
  case vc9.x =>
    exact chBV (r.2.2.2.2.1.eval ρ) (r.2.2.2.2.2.1.eval ρ)
      (r.2.2.2.2.2.2.1.eval ρ)
  case vc10.ha => exact hr.2.2.2.1
  case vc11.hb => exact hr.2.2.2.2.2.2.2
  case vc12.hc => grind [U.Rel]
  case vc13.hd => exact U.valid_bitVec _
  case vc14.he => exact U.valid_getElem! hw (by grind)
  case vc15.hf => grind
  case vc16.hg => exact U.valid_getElem! hw (by grind)
  case vc17.hh => grind
  case vc18.hi => exact hs 4
  case vc19.hx => assumption
  case vc20.maj => exact majBV (r.1.eval ρ) (r.2.1.eval ρ) (r.2.2.1.eval ρ)
  case vc21.hd => exact hr.2.2.2.1
  case vc22.he | vc23.hS0 => grind [U.Rel]
  case vc24.hA => exact hs 0
  case vc25.hE => exact hs 4
  case vc26.hmaj => assumption
  case vc27.success => grind [U.Rel]

@[spec] theorem finalRound_sound {w : Vector (U 32) 64}
    {wv : Vector (BitVec 32) 64} (hw : Vector.Rel ρ w wv)
    {r : RoundState (U 32)} {rv : RoundState (BitVec 32)}
    (hr : RoundState.Rel ρ r rv) {s : Vector (U 32) 8}
    {sv : Vector (BitVec 32) 8} (hs : Vector.Rel ρ s sv)
    (i : Nat) (hi : i ∈ [16:64]) :
    ⦃⌜True⌝⦄ Sound.interp ρ (finalRound i hi (w, r, s))
    ⦃⇓ out => ⌜Vector.Rel ρ out (finishBV sv (inlineScheduleRoundBV i wv rv))⌝⦄ := by
  unfold finalRound finalRoundTail
  mvcgen -trivial
  case vc1.wv => exact wv
  case vc2.hw => exact hw
  case vc3.rv => exact rv
  case vc4.hr => exact hr
  case vc5.sv => exact sv
  case vc6.hs => exact hs
  case vc7.hvalid => simpa using And.intro (hs 1).1 hr.a.1
  case vc8.hvalid => simpa using And.intro (hs 2).1 hr.b.1
  case vc9.hvalid => simpa using And.intro (hs 3).1 hr.c.1
  case vc10.hvalid => simpa using And.intro (hs 5).1 hr.e.1
  case vc11.hvalid => simpa using And.intro (hs 6).1 hr.f.1
  case vc12.hvalid => simpa using And.intro (hs 7).1 hr.g.1
  case vc13.success =>
    rename_i out hout o1 ho1 o2 ho2 o3 ho3 o5 ho5 o6 ho6 o7 ho7
    rw [finalRoundCoreBV_eq] at hout
    intro j
    fin_cases j
    · exact hout.1
    · refine ⟨ho1.1, ?_⟩
      change o1.eval ρ = _
      calc
        _ = (#[s[1], r.1].map (·.eval ρ)).sum := ho1.2
        _ = sv[1] + rv.1 := by
          simp [← Array.sum_toList]
          exact congrArg₂ (· + ·) (hs 1).2 hr.a.2
    · refine ⟨ho2.1, ?_⟩
      change o2.eval ρ = _
      calc
        _ = (#[s[2], r.2.1].map (·.eval ρ)).sum := ho2.2
        _ = sv[2] + rv.2.1 := by
          simp [← Array.sum_toList]
          exact congrArg₂ (· + ·) (hs 2).2 hr.b.2
    · refine ⟨ho3.1, ?_⟩
      change o3.eval ρ = _
      calc
        _ = (#[s[3], r.2.2.1].map (·.eval ρ)).sum := ho3.2
        _ = sv[3] + rv.2.2.1 := by
          simp [← Array.sum_toList]
          exact congrArg₂ (· + ·) (hs 3).2 hr.c.2
    · exact hout.2
    · refine ⟨ho5.1, ?_⟩
      change o5.eval ρ = _
      calc
        _ = (#[s[5], r.2.2.2.2.1].map (·.eval ρ)).sum := ho5.2
        _ = sv[5] + rv.2.2.2.2.1 := by
          simp [← Array.sum_toList]
          exact congrArg₂ (· + ·) (hs 5).2 hr.e.2
    · refine ⟨ho6.1, ?_⟩
      change o6.eval ρ = _
      calc
        _ = (#[s[6], r.2.2.2.2.2.1].map (·.eval ρ)).sum := ho6.2
        _ = sv[6] + rv.2.2.2.2.2.1 := by
          simp [← Array.sum_toList]
          exact congrArg₂ (· + ·) (hs 6).2 hr.f.2
    · refine ⟨ho7.1, ?_⟩
      change o7.eval ρ = _
      calc
        _ = (#[s[7], r.2.2.2.2.2.2.1].map (·.eval ρ)).sum := ho7.2
        _ = sv[7] + rv.2.2.2.2.2.2.1 := by
          simp [← Array.sum_toList]
          exact congrArg₂ (· + ·) (hs 7).2 hr.g.2

@[spec] theorem finalRound_complete {w : Vector (U 32) 64}
    (hw : ∀ j : Fin 64, w[j].Valid ρ) {r : RoundState (U 32)}
    (hr : r.Valid ρ) {s : Vector (U 32) 8}
    (hs : ∀ j : Fin 8, s[j].Valid ρ) (i : Nat) (hi : i ∈ [16:64]) :
    ⦃⌜True⌝⦄ Complete.interp ρ (finalRound i hi (w, r, s))
    ⦃⇓ out => ⌜∀ j : Fin 8, out[j].Valid ρ⌝⦄ := by
  unfold finalRound finalRoundTail
  mvcgen -trivial
  case vc1.hw => exact hw
  case vc2.hr => exact hr
  case vc3.hs => exact hs
  case vc4.hvalid => simpa using And.intro (hs 1) hr.1
  case vc5.hvalid => simpa using And.intro (hs 2) hr.2.1
  case vc6.hvalid => simpa using And.intro (hs 3) hr.2.2.1
  case vc7.hvalid => simpa using And.intro (hs 5) hr.2.2.2.2.1
  case vc8.hvalid => simpa using And.intro (hs 6) hr.2.2.2.2.2.1
  case vc9.hvalid => simpa using And.intro (hs 7) hr.2.2.2.2.2.2.1
  case vc10.success =>
    rename_i out hout o1 ho1 o2 ho2 o3 ho3 o5 ho5 o6 ho6 o7 ho7
    intro j
    fin_cases j
    · exact hout.1
    · exact ho1.1
    · exact ho2.1
    · exact ho3.1
    · exact hout.2
    · exact ho5.1
    · exact ho6.1
    · exact ho7.1

def terminalRoundsBV (w : Vector (BitVec 32) 64)
    (r : RoundState (BitVec 32)) (s : Vector (BitVec 32) 8) :
    Vector (BitVec 32) 8 :=
  finishBV s (inlineScheduleRoundBV 63 w (inlineScheduleRoundBV 62 w r))

set_option maxHeartbeats 1000000 in
@[spec] theorem terminalRounds_sound {w : Vector (U 32) 64}
    {wv : Vector (BitVec 32) 64} (hw : Vector.Rel ρ w wv)
    {r : RoundState (U 32)} {rv : RoundState (BitVec 32)}
    (hr : RoundState.Rel ρ r rv) {s : Vector (U 32) 8}
    {sv : Vector (BitVec 32) 8} (hs : Vector.Rel ρ s sv) :
    ⦃⌜True⌝⦄ Sound.interp ρ (terminalRounds (w, r, s))
    ⦃⇓ out => ⌜Vector.Rel ρ out (terminalRoundsBV wv rv sv)⌝⦄ := by
  unfold terminalRounds terminalRoundsBV
  rw [Sound.interp_bind]
  apply Triple.bind (Q := fun r62 =>
    ⌜RoundState.Rel ρ r62 (inlineScheduleRoundBV 62 wv rv)⌝)
  case hx => exact inlineScheduleRound_sound_rel hw hr 62 (by
    change 16 ≤ 62 ∧ 62 < 64 ∧ (62 - 16) % 1 = 0
    norm_num)
  case hf =>
    intro r62
    mvcgen [finalRound_sound]
    case vc1 => exact fun _ => hw
    case vc2 => exact fun h => h
    case vc3 => exact fun _ => hs

set_option maxHeartbeats 1000000 in
@[spec] theorem terminalRounds_complete {w : Vector (U 32) 64}
    (hw : ∀ j : Fin 64, w[j].Valid ρ) {r : RoundState (U 32)}
    (hr : r.Valid ρ) {s : Vector (U 32) 8}
    (hs : ∀ j : Fin 8, s[j].Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (terminalRounds (w, r, s))
    ⦃⇓ out => ⌜∀ j : Fin 8, out[j].Valid ρ⌝⦄ := by
  unfold terminalRounds
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun r62 => ⌜r62.Valid ρ⌝)
  case hx => exact inlineScheduleRound_complete hw hr 62 (by
    change 16 ≤ 62 ∧ 62 < 64 ∧ (62 - 16) % 1 = 0
    norm_num)
  case hf =>
    intro r62
    mvcgen [finalRound_complete]
    case vc1 => exact fun _ => hw
    case vc2 => exact fun h => h
    case vc3 => exact fun _ => hs

@[spec] theorem terminalRounds_sound_rel {w : Vector (U 32) 64}
    {wv : Vector (BitVec 32) 64} {r : RoundState (U 32)}
    {rv : RoundState (BitVec 32)} {s : Vector (U 32) 8}
    {sv : Vector (BitVec 32) 8} :
    ⦃⌜Vector.Rel ρ w wv ∧ RoundState.Rel ρ r rv ∧ Vector.Rel ρ s sv⌝⦄
      Sound.interp ρ (terminalRounds (w, r, s))
    ⦃⇓ out => ⌜Vector.Rel ρ out (terminalRoundsBV wv rv sv)⌝⦄ := by
  mvcgen [terminalRounds_sound]
  case vc1 => exact fun hw _ _ => hw
  case vc2 => exact fun _ hr _ => hr
  case vc3 => exact fun _ _ hs => hs

@[spec] theorem terminalRounds_complete_rel {w : Vector (U 32) 64}
    {r : RoundState (U 32)} {s : Vector (U 32) 8} :
    ⦃⌜(∀ j : Fin 64, w[j].Valid ρ) ∧ r.Valid ρ ∧
        (∀ j : Fin 8, s[j].Valid ρ)⌝⦄
      Complete.interp ρ (terminalRounds (w, r, s))
    ⦃⇓ out => ⌜∀ j : Fin 8, out[j].Valid ρ⌝⦄ := by
  mvcgen [terminalRounds_complete]
  case vc1 => exact fun hw _ _ => hw
  case vc2 => exact fun _ hr _ => hr
  case vc3 => exact fun _ _ hs => hs

def initialSchedule (m : Vector (BitVec 32) 16) : Vector (BitVec 32) 64 :=
  ([0:16].toList).foldl (fun w i => w.set! i m[i]!) default

theorem initialSchedule_words {ρ : WF.Valuation} (m : Vector (Word 32) 16) :
    ([0:16].toList).foldl
        (fun w i => w.set! i ((m[i]!).eval ρ.bool)) default =
      initialSchedule (m.map (Word.eval ρ.bool)) := by
  unfold initialSchedule
  apply List.foldl_congr_of_mem
  intro i hi w
  rw [Vector.getElem!_map m (Word.eval ρ.bool) i (by grind)]

def scheduleBV (m : Vector (BitVec 32) 16) : Vector (BitVec 32) 64 :=
  ([16:64].toList).foldl (fun w i => w.set! i (scheduleStepBV i w))
    (initialSchedule m)

theorem scheduleBV_eq (m : Vector (BitVec 32) 16) :
    ([16:64].toList).foldl
        (fun w i => w.set! i (scheduleStepBV i w)) (initialSchedule m) =
      scheduleBV m := rfl

def initialRound (s : Vector (BitVec 32) 8) : RoundState (BitVec 32) :=
  ⟨s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]⟩

theorem initialRound_eval (s : Vector (U 32) 8) :
    (show RoundState (U 32) from
      ⟨s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]⟩).eval ρ =
      initialRound (s.map (·.eval ρ)) := by
  unfold RoundState.eval initialRound
  simp only [Vector.getElem_map]

def roundsBV (w : Vector (BitVec 32) 64) (s : Vector (BitVec 32) 8) :
    RoundState (BitVec 32) :=
  ([0:64].toList).foldl (fun r i => roundStepBV i w r) (initialRound s)

theorem roundsBV_eq (w : Vector (BitVec 32) 64)
    (s : Vector (BitVec 32) 8) :
    ([0:64].toList).foldl (fun r i => roundStepBV i w r) (initialRound s) =
      roundsBV w s := rfl

def scheduleBV62 (m : Vector (BitVec 32) 16) : Vector (BitVec 32) 64 :=
  ([16:62].toList).foldl (fun w i => w.set! i (scheduleStepBV i w))
    (initialSchedule m)

def roundsBV62 (w : Vector (BitVec 32) 64) (s : Vector (BitVec 32) 8) :
    RoundState (BitVec 32) :=
  ([0:62].toList).foldl (fun r i => roundStepBV i w r) (initialRound s)

def roundsBV16 (w : Vector (BitVec 32) 64) (s : Vector (BitVec 32) 8) :
    RoundState (BitVec 32) :=
  ([0:16].toList).foldl (fun r i => roundStepBV i w r) (initialRound s)

/-- Pure model of the physically merged schedule/round prefix. -/
def fusedPrefixBV (m : Vector (BitVec 32) 16) (s : Vector (BitVec 32) 8) :
    RoundState (BitVec 32) × Vector (BitVec 32) 64 :=
  ([16:62].toList).foldl (fun x i => scheduleRoundStepBV i x)
    (roundsBV16 (initialSchedule m) s, initialSchedule m)

private theorem Vector.setBang_eq_setIfInBounds (xs : Vector α n)
    (i : Nat) (x : α) : xs.set! i x = xs.setIfInBounds i x := by
  rfl

private theorem scheduleFold_getElem!_of_not_mem
    (xs : List Nat) (w : Vector (BitVec 32) 64) (i : Nat)
    (hi : i < 64) (hnot : i ∉ xs) :
    (xs.foldl (fun w j => w.set! j (scheduleStepBV j w)) w)[i]! = w[i]! := by
  induction xs generalizing w with
  | nil => rfl
  | cons j js ih =>
      simp only [List.foldl_cons]
      have hji : j ≠ i := by
        intro h
        subst j
        simp at hnot
      have hnot' : i ∉ js := by
        have hn : i ≠ j ∧ i ∉ js := by
          simpa only [List.mem_cons, not_or] using hnot
        exact hn.2
      rw [ih _ hnot']
      rw [getElem!_pos _ i hi, getElem!_pos _ i hi,
        Vector.setBang_eq_setIfInBounds]
      rw [Vector.getElem_setIfInBounds_ne hi (by omega)]

private theorem roundStepBV_eq_of_getElem!
    (i : Nat) (w v : Vector (BitVec 32) 64) (r : RoundState (BitVec 32))
    (h : w[i]! = v[i]!) :
    roundStepBV i w r = roundStepBV i v r := by
  unfold roundStepBV
  rw [h]

private theorem scheduleRoundFold_eq (xs : List Nat) (hxs : xs.Nodup)
    (r : RoundState (BitVec 32)) (w : Vector (BitVec 32) 64)
    (hbound : ∀ i ∈ xs, i < 64) :
    xs.foldl (fun x i => scheduleRoundStepBV i x) (r, w) =
      let w' := xs.foldl (fun w i => w.set! i (scheduleStepBV i w)) w
      (xs.foldl (fun r i => roundStepBV i w' r) r, w') := by
  induction xs generalizing r w with
  | nil => rfl
  | cons i is ih =>
      have hi : i < 64 := hbound i (by simp)
      have hni : i ∉ is := (List.nodup_cons.mp hxs).1
      have hnis : is.Nodup := (List.nodup_cons.mp hxs).2
      let w1 := w.set! i (scheduleStepBV i w)
      let wf := is.foldl (fun w i => w.set! i (scheduleStepBV i w)) w1
      have hget : wf[i]! = w1[i]! := by
        exact scheduleFold_getElem!_of_not_mem is w1 i hi hni
      have hround : roundStepBV i w1 r = roundStepBV i wf r :=
        roundStepBV_eq_of_getElem! i w1 wf r hget.symm
      simp only [List.foldl_cons]
      change
        is.foldl (fun x i => scheduleRoundStepBV i x)
          (roundStepBV i w1 r, w1) = _
      rw [ih hnis _ _ (fun j hj => hbound j (by simp [hj]))]
      change
        (is.foldl (fun r j => roundStepBV j wf r) (roundStepBV i w1 r), wf) =
          (is.foldl (fun r j => roundStepBV j wf r) (roundStepBV i wf r), wf)
      rw [hround]

def optimizedModel (m : Vector (BitVec 32) 16)
    (s : Vector (BitVec 32) 8) : Vector (BitVec 32) 8 :=
  let p := fusedPrefixBV m s
  let r := p.1
  let w := p.2
  finishBV s (inlineScheduleRoundBV 63 w (inlineScheduleRoundBV 62 w r))

private theorem scheduleBV_terminal (m : Vector (BitVec 32) 16) :
    scheduleBV m =
      let w := scheduleBV62 m
      let w := w.set! 62 (scheduleStepBV 62 w)
      w.set! 63 (scheduleStepBV 63 w) := by
  have hrange : [16:64].toList = [16:62].toList ++ [62, 63] := by decide
  unfold scheduleBV scheduleBV62
  rw [hrange, List.foldl_append]
  rfl

private theorem scheduleBV_get_lt62 (m : Vector (BitVec 32) 16)
    (j : Fin 64) (hj : j.val < 62) :
    (scheduleBV m)[j] = (scheduleBV62 m)[j] := by
  rw [scheduleBV_terminal]
  simp only [Vector.setBang_eq_setIfInBounds, Fin.getElem_fin]
  rw [Vector.getElem_setIfInBounds_ne j.isLt (by omega),
    Vector.getElem_setIfInBounds_ne j.isLt (by omega)]

private theorem roundStepBV_schedule_lt62 (m : Vector (BitVec 32) 16)
    (i : Nat) (hi : i ∈ [0:62]) (r : RoundState (BitVec 32)) :
    roundStepBV i (scheduleBV m) r = roundStepBV i (scheduleBV62 m) r := by
  change 0 ≤ i ∧ i < 62 ∧ (i - 0) % 1 = 0 at hi
  have hi62 : i < 62 := hi.2.1
  have hi64 : i < 64 := lt_trans hi62 (by omega)
  have hwi : (scheduleBV m)[i]! = (scheduleBV62 m)[i]! := by
    rw [getElem!_pos (scheduleBV m) i hi64,
      getElem!_pos (scheduleBV62 m) i hi64]
    exact scheduleBV_get_lt62 m ⟨i, hi64⟩ hi62
  unfold roundStepBV
  rw [hwi]

private theorem roundsBV62_schedule_eq (m : Vector (BitVec 32) 16)
    (s : Vector (BitVec 32) 8) :
    roundsBV62 (scheduleBV m) s = roundsBV62 (scheduleBV62 m) s := by
  unfold roundsBV62
  apply List.foldl_congr_of_mem
  intro i hi r
  apply roundStepBV_schedule_lt62
  apply Std.Legacy.Range.mem_of_mem_range'
  exact hi

private theorem scheduleBV_get_62 (m : Vector (BitVec 32) 16) :
    (scheduleBV m)[62]! = scheduleStepBV 62 (scheduleBV62 m) := by
  rw [scheduleBV_terminal]
  simp only [Vector.setBang_eq_setIfInBounds]
  rw [getElem!_pos _ 62 (by omega),
    Vector.getElem_setIfInBounds_ne (by omega) (by omega)]
  simp [Vector.getElem_setIfInBounds]

private theorem scheduleBV_get_63 (m : Vector (BitVec 32) 16) :
    (scheduleBV m)[63]! = scheduleStepBV 63 (scheduleBV62 m) := by
  rw [scheduleBV_terminal]
  simp only [Vector.setBang_eq_setIfInBounds]
  rw [getElem!_pos _ 63 (by omega)]
  simp only [Vector.getElem_setIfInBounds]
  unfold scheduleStepBV
  simp [Vector.getElem_setIfInBounds]

private theorem inlineScheduleRoundBV_eq_roundStepBV
    (i : Nat) (wFull w : Vector (BitVec 32) 64)
    (r : RoundState (BitVec 32))
    (hwi : wFull[i]! = scheduleStepBV i w) :
    inlineScheduleRoundBV i w r = roundStepBV i wFull r := by
  unfold inlineScheduleRoundBV roundStepBV
  rw [hwi]

private theorem roundsBV_terminal (w : Vector (BitVec 32) 64)
    (s : Vector (BitVec 32) 8) :
    roundsBV w s = roundStepBV 63 w (roundStepBV 62 w (roundsBV62 w s)) := by
  have hrange : [0:64].toList = [0:62].toList ++ [62, 63] := by decide
  unfold roundsBV roundsBV62
  rw [hrange, List.foldl_append]
  rfl

def model (m : Vector (BitVec 32) 16) (s : Vector (BitVec 32) 8) :
    Vector (BitVec 32) 8 :=
  finishBV s (roundsBV (scheduleBV m) s)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
private theorem fusedPrefixBV_eq (m : Vector (BitVec 32) 16)
    (s : Vector (BitVec 32) 8) :
    fusedPrefixBV m s =
      (roundsBV62 (scheduleBV62 m) s, scheduleBV62 m) := by
  unfold fusedPrefixBV roundsBV16 roundsBV62 scheduleBV62
  rw [scheduleRoundFold_eq ([16:62].toList) (by decide) _ _ (by
    intro i hi
    have := Std.Legacy.Range.mem_of_mem_range' hi
    change 16 ≤ i ∧ i < 62 ∧ (i - 16) % 1 = 0 at this
    omega)]
  have hround16 :
      ([0:16].toList).foldl
          (fun r i => roundStepBV i (initialSchedule m) r) (initialRound s) =
        ([0:16].toList).foldl
          (fun r i => roundStepBV i
            (([16:62].toList).foldl
              (fun w i => w.set! i (scheduleStepBV i w))
              (initialSchedule m)) r) (initialRound s) := by
    apply List.foldl_congr_of_mem
    intro i hi r
    apply roundStepBV_eq_of_getElem!
    apply Eq.symm
    apply scheduleFold_getElem!_of_not_mem
    · have := Std.Legacy.Range.mem_of_mem_range' hi
      change 0 ≤ i ∧ i < 16 ∧ (i - 0) % 1 = 0 at this
      omega
    · intro himem
      have hi0 := Std.Legacy.Range.mem_of_mem_range' hi
      have hi16 := Std.Legacy.Range.mem_of_mem_range' himem
      change 0 ≤ i ∧ i < 16 ∧ (i - 0) % 1 = 0 at hi0
      change 16 ≤ i ∧ i < 62 ∧ (i - 16) % 1 = 0 at hi16
      omega
  have hrange : [0:62].toList = [0:16].toList ++ [16:62].toList := by decide
  rw [hround16]
  rw [hrange, List.foldl_append]

private theorem optimizedRounds_eq (m : Vector (BitVec 32) 16)
    (s : Vector (BitVec 32) 8) :
    inlineScheduleRoundBV 63 (scheduleBV62 m)
        (inlineScheduleRoundBV 62 (scheduleBV62 m)
          (roundsBV62 (scheduleBV62 m) s)) =
      roundsBV (scheduleBV m) s := by
  rw [← roundsBV62_schedule_eq m s,
    inlineScheduleRoundBV_eq_roundStepBV 62 (scheduleBV m) (scheduleBV62 m)
      _ (scheduleBV_get_62 m),
    inlineScheduleRoundBV_eq_roundStepBV 63 (scheduleBV m) (scheduleBV62 m)
      _ (scheduleBV_get_63 m),
    roundsBV_terminal]

theorem optimizedModel_eq_model (m : Vector (BitVec 32) 16)
    (s : Vector (BitVec 32) 8) : optimizedModel m s = model m s := by
  dsimp only [optimizedModel, model]
  rw [fusedPrefixBV_eq]
  rw [optimizedRounds_eq]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 1000000 in
@[spec] theorem permPrefix_sound {m : Vector (Word 32) 16}
    {su : Vector (U 32) 8} {sv : Vector (BitVec 32) 8}
    (hsu : Vector.Rel ρ su sv) :
    ⦃⌜True⌝⦄ Sound.interp ρ (permPrefix m su)
    ⦃⇓ out => ⌜Vector.Rel ρ out.1
        (fusedPrefixBV (m.map (Word.eval ρ.bool)) sv).2 ∧
      RoundState.Rel ρ out.2.1
        (fusedPrefixBV (m.map (Word.eval ρ.bool)) sv).1 ∧
      Vector.Rel ρ out.2.2 sv⌝⦄ := by
    unfold permPrefix
    mvcgen -trivial invariants
    · ⇓⟨cur, w⟩ => ⌜Vector.Rel ρ w
        (cur.prefix.foldl
          (fun w i => w.set! i ((m[i]!).eval ρ.bool)) default)⌝
    · ⇓⟨cur, r⟩ => ⌜RoundState.Rel ρ r
        (cur.prefix.foldl
          (fun r i => roundStepBV i
            (initialSchedule (m.map (Word.eval ρ.bool))) r)
          (initialRound sv))⌝
    · ⇓⟨cur, x⟩ =>
        let p := cur.prefix.foldl (fun x i => scheduleRoundStepBV i x)
          (roundsBV16 (initialSchedule (m.map (Word.eval ρ.bool))) sv,
            initialSchedule (m.map (Word.eval ρ.bool)))
        ⌜RoundState.Rel ρ x.1 p.1 ∧ Vector.Rel ρ x.2 p.2⌝
    case vc1 =>
      rename_i pref cur suff hsplit w hw out hout
      simpa [List.foldl_append, getElem!_pos m cur (by grind)]
        using hw.set! hout cur
    case vc2.h.pre => simpa using (Vector.Rel.default (valuation := ρ) (n := 32) (m := 64))
    case vc3.hw => exact Vector.Rel.valid (by assumption)
    case vc4.hr => exact (by assumption : RoundState.Rel ρ _ _).1
    case vc5 =>
      rename_i w hw _ cur _ _ r hr out hout
      rw [initialSchedule_words] at hw
      rw [Vector.Rel.eval_eq hw, RoundState.Rel.eval_eq hr] at hout
      simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using hout
    case vc6.h.pre =>
      simp only [List.foldl_nil]
      refine ⟨⟨(hsu 0).1, (hsu 1).1, (hsu 2).1, (hsu 3).1,
        (hsu 4).1, (hsu 5).1, (hsu 6).1, (hsu 7).1⟩, ?_⟩
      rw [initialRound_eval, Vector.Rel.eval_eq hsu]
    case vc7.xv =>
      rename_i pref _ _ _ _ _
      exact pref.foldl (fun x i => scheduleRoundStepBV i x)
        (roundsBV16 (initialSchedule (m.map (Word.eval ρ.bool))) sv,
          initialSchedule (m.map (Word.eval ρ.bool)))
    case vc8.hx => exact (by assumption)
    case vc9 =>
      rename_i pref cur suff hsplit x hx out hout
      simpa [List.foldl_append] using hout
    case vc10.h.pre =>
      simp only [List.foldl_nil]
      rename_i r hr w hw
      rw [initialSchedule_words] at hr
      exact ⟨by simpa only [roundsBV16] using hw, hr⟩
    case vc11.h.post.success =>
      rename_i _ _ _ _ x hx
      exact ⟨hx.2, hx.1, hsu⟩

@[spec] theorem permPrefix_sound_rel {m : Vector (Word 32) 16}
    {su : Vector (U 32) 8} {sv : Vector (BitVec 32) 8} :
    ⦃⌜Vector.Rel ρ su sv⌝⦄ Sound.interp ρ (permPrefix m su)
    ⦃⇓ out => ⌜Vector.Rel ρ out.1
        (fusedPrefixBV (m.map (Word.eval ρ.bool)) sv).2 ∧
      RoundState.Rel ρ out.2.1
        (fusedPrefixBV (m.map (Word.eval ρ.bool)) sv).1 ∧
      Vector.Rel ρ out.2.2 sv⌝⦄ := by
  mvcgen [permPrefix_sound]
  case vc1 => exact fun h => h

set_option maxRecDepth 2000 in
set_option maxHeartbeats 1000000 in
@[spec] theorem structured_sound {m : Vector (Word 32) 16}
    {s : Vector (Word 32) 8} :
    ⦃⌜True⌝⦄ Sound.interp ρ (structured m s)
    ⦃⇓ out => ⌜Vector.Rel ρ out
      (model (m.map (Word.eval ρ.bool))
        (s.map (Word.eval ρ.bool)))⌝⦄ := by
  unfold structured permCircuit
  rw [Sound.interp_bind]
  apply Triple.bind (Q := fun su =>
    ⌜Vector.Rel ρ su (s.map (Word.eval ρ.bool))⌝)
  case hx => exact U.mapM_fromWord_sound
  case hf =>
    intro su
    rw [Sound.interp_bind]
    apply Triple.bind (Q := fun wr =>
      ⌜Vector.Rel ρ wr.1
          (fusedPrefixBV (m.map (Word.eval ρ.bool))
            (s.map (Word.eval ρ.bool))).2 ∧
        RoundState.Rel ρ wr.2.1
          (fusedPrefixBV (m.map (Word.eval ρ.bool))
            (s.map (Word.eval ρ.bool))).1 ∧
        Vector.Rel ρ wr.2.2 (s.map (Word.eval ρ.bool))⌝)
    case hx => exact permPrefix_sound_rel
    case hf =>
      intro wr
      apply Triple.iff_conseq.mp (terminalRounds_sound_rel
        (wv := (fusedPrefixBV (m.map (Word.eval ρ.bool))
          (s.map (Word.eval ρ.bool))).2)
        (rv := (fusedPrefixBV (m.map (Word.eval ρ.bool))
          (s.map (Word.eval ρ.bool))).1)
        (sv := s.map (Word.eval ρ.bool))) (by simp)
      simp only [PostCond.entails, SPred.entails_nil]
      refine ⟨?_, ExceptConds.entails.refl _⟩
      intro out h
      unfold terminalRoundsBV at h
      change Vector.Rel ρ out
        (optimizedModel (m.map (Word.eval ρ.bool))
          (s.map (Word.eval ρ.bool))) at h
      rw [optimizedModel_eq_model] at h
      exact h

set_option maxRecDepth 2000 in
set_option maxHeartbeats 5000000 in
@[spec] theorem permPrefix_complete {m : Vector (Word 32) 16}
    {su : Vector (U 32) 8} (hsu : ∀ i : Fin 8, su[i].Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (permPrefix m su)
    ⦃⇓ out => ⌜(∀ j : Fin 64, out.1[j].Valid ρ) ∧ out.2.1.Valid ρ ∧
      (∀ j : Fin 8, out.2.2[j].Valid ρ)⌝⦄ := by
    unfold permPrefix
    mvcgen -trivial invariants
    · ⇓⟨_, w⟩ => ⌜∀ j : Fin 64, w[j].Valid ρ⌝
    · ⇓⟨_, r⟩ => ⌜r.Valid ρ⌝
    · ⇓⟨_, x⟩ => ⌜x.1.Valid ρ ∧ ∀ j : Fin 64, x.2[j].Valid ρ⌝
    case vc1 =>
      exact U.allValid_set! (by assumption) (by grind [U.Rel]) _
    case vc2.h.pre =>
      intro j
      rw [U.vector_default_get]
      exact U.valid_default
    case vc3.hw => assumption
    case vc4.hr => assumption
    case vc5 => assumption
    case vc6.h.pre =>
      exact ⟨hsu 0, hsu 1, hsu 2, hsu 3,
        hsu 4, hsu 5, hsu 6, hsu 7⟩
    case vc7.hx => exact (by assumption)
    case vc8 => exact (by assumption)
    case vc9.h.pre => exact ⟨by assumption, by assumption⟩
    case vc10.h.post.success =>
      rename_i _ _ _ _ x hx
      exact ⟨hx.2, hx.1, hsu⟩

@[spec] theorem permPrefix_complete_rel {m : Vector (Word 32) 16}
    {su : Vector (U 32) 8} {sv : Vector (BitVec 32) 8} :
    ⦃⌜Vector.Rel ρ su sv⌝⦄ Complete.interp ρ (permPrefix m su)
    ⦃⇓ out => ⌜(∀ j : Fin 64, out.1[j].Valid ρ) ∧ out.2.1.Valid ρ ∧
      (∀ j : Fin 8, out.2.2[j].Valid ρ)⌝⦄ := by
  mvcgen [permPrefix_complete]
  case vc1 => exact fun h => Vector.Rel.valid h

set_option maxRecDepth 2000 in
set_option maxHeartbeats 1000000 in
@[spec] theorem structured_complete {m : Vector (Word 32) 16}
    {s : Vector (Word 32) 8} :
    ⦃⌜True⌝⦄ Complete.interp ρ (structured m s)
    ⦃⇓ out => ⌜∀ i : Fin 8, out[i].Valid ρ⌝⦄ := by
  unfold structured permCircuit
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun su =>
    ⌜Vector.Rel ρ su (s.map (Word.eval ρ.bool))⌝)
  case hx => exact U.mapM_fromWord_complete
  case hf =>
    intro su
    rw [Complete.interp_bind]
    apply Triple.bind (Q := fun wr =>
      ⌜(∀ j : Fin 64, wr.1[j].Valid ρ) ∧ wr.2.1.Valid ρ ∧
        (∀ j : Fin 8, wr.2.2[j].Valid ρ)⌝)
    case hx => exact permPrefix_complete_rel
    case hf =>
      intro wr
      exact terminalRounds_complete_rel

def RoundState.WFRel : WF.Post (RoundState (U n)) :=
  fun lv rv l r => U.WFRel lv rv l.1 r.1 ∧
    U.WFRel lv rv l.2.1 r.2.1 ∧ U.WFRel lv rv l.2.2.1 r.2.2.1 ∧
    U.WFRel lv rv l.2.2.2.1 r.2.2.2.1 ∧
    U.WFRel lv rv l.2.2.2.2.1 r.2.2.2.2.1 ∧
    U.WFRel lv rv l.2.2.2.2.2.1 r.2.2.2.2.2.1 ∧
    U.WFRel lv rv l.2.2.2.2.2.2.1 r.2.2.2.2.2.2.1 ∧
    U.WFRel lv rv l.2.2.2.2.2.2.2 r.2.2.2.2.2.2.2

theorem U.fromIntWithLowBit_wf_full :
    WF.GadgetSpec
      (fun lv rv (l r : LC ℤ × LC Bool) =>
        WF.LCEq lv.int rv.int l.1 r.1 ∧ WF.LCEq lv.bool rv.bool l.2 r.2)
      (U.fromIntWithLowBitPair n)
      (fun lv rv l r =>
        (∀ i : Fin (n + 1), WF.LCEq lv.bool rv.bool
          l.bits.bitsLE[i] r.bits.bitsLE[i]) ∧
        (∀ i : Fin (n + 1), WF.LCEq lv.int rv.int l.intBits[i] r.intBits[i]) ∧
        WF.LCEq lv.int rv.int l.intVal r.intVal) := by
  unfold U.fromIntWithLowBitPair
  wfgen' using [U.fromWord_wf_full] unfold [U.fromIntWithLowBit]
  case vc1 hrel =>
    rcases hrel with ⟨_, values, _, _, hleft, hright⟩
    by_cases hi : i = 0
    · simp [hi, WF.LCEq]
      exact (by assumption :
        WF.LCEq leftVal.int rightVal.int left.1 right.1 ∧
        WF.LCEq leftVal.bool rightVal.bool left.2 right.2).2
    · have hiv : i.val ≠ 0 := by
        intro hzero
        apply hi
        exact Fin.ext hzero
      simpa [hi, WF.LCEq, Fin.getElem_fin] using
        (hleft (i.val - 1) (by omega)).trans
          (hright (i.val - 1) (by omega)).symm
  case vc2 h =>
    unfold WF.LCEq at h
    simp only [WF.evalArgs]
    rw [h.1]
  case vc3 h =>
    unfold WF.ArgsEq
    simp only [WF.evalArgs]
    exact congrArg (fun x => h![x]) h.1

theorem U.lceq_lowBit_sum {left right : Vector (U 32) m}
    (h : WF.VectorRel U.WFRel lv rv left right) :
    WF.LCEq lv.bool rv.bool
      (left.toArray.map (fun x => x.bits.bitsLE[0])).sum
      (right.toArray.map (fun x => x.bits.bitsLE[0])).sum := by
  unfold WF.LCEq
  rw [LC.eval_array_sum, LC.eval_array_sum]
  apply congrArg Array.sum
  apply Array.ext
  · simp
  · intro i hiLeft hiRight
    simp only [Array.getElem_map]
    exact (h ⟨i, by simpa using hiLeft⟩).2 0

theorem U.sumFixedAffineLow_wf :
    WF.GadgetSpec (WF.VectorRel (U.WFRel (n := 32)))
      (U.sumFixedAffineLow (m := m)) U.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold U.sumFixedAffineLow
  apply WF.GadgetSpec.bind_rule U.fromIntWithLowBit_wf_full
  · intro lv rv h
    exact ⟨U.lceq_intVal_sum h, U.lceq_lowBit_sum h⟩
  · intro A outL outR hout
    apply WF.Rel.pure
    intro lv rv hA
    have h := hout lv rv hA
    let hle : 32 ≤ 31 + Nat.clog 2 m + 1 := by omega
    constructor
    · apply WF.LCEq.uIntVal
      intro i
      simpa [U.takeLE, Fin.getElem_fin] using h.2.2.1 (i.castLE hle)
    · intro i
      simpa [U.takeLE, Fin.getElem_fin] using h.2.1 (i.castLE hle)

theorem scheduleStep_wf (i : Nat) (hi : i ∈ [16:64]) :
    WF.GadgetSpec (WF.VectorRel U.WFRel) (scheduleStep i) U.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold scheduleStep
  simp only [U.sum4_eq_sumFixed]
  apply WF.GadgetSpec.bind_rule U.fromWord_wf_rel
  · intro lv rv h
    have hw := h.getElem! (i := i - 15) (by grind) |>.2
    change Word.WFRel lv rv _ _ at hw
    exact ((hw.rotateRight 7).xor (hw.rotateRight 18)).xor (hw.shiftRight 3)
  · intro A s0L s0R hs0
    apply WF.GadgetSpec.bind_rule U.fromWord_wf_rel
    · intro lv rv h
      have hw := (hs0 lv rv h).1.getElem! (i := i - 2) (by grind) |>.2
      change Word.WFRel lv rv _ _ at hw
      exact ((hw.rotateRight 17).xor (hw.rotateRight 19)).xor (hw.shiftRight 10)
    · intro B s1L s1R hs1
      apply WF.Rel.mono (U.sumFixedAffineLow_wf.relHom B
        #v[left[i - 16]!, s0L, left[i - 7]!, s1L]
        #v[right[i - 16]!, s0R, right[i - 7]!, s1R] (by
          intro lv rv h
          have h1 := hs1 lv rv h
          have h0 := hs0 lv rv h1.1
          intro j
          fin_cases j
          · exact h0.1.getElem! (i := i - 16) (by grind)
          · exact h0.2
          · exact h0.1.getElem! (i := i - 7) (by grind)
          · exact h1.2))
      exact fun _ _ _ _ h => h.2

theorem terminalScheduleParts_wf (i : Nat) (hi : i ∈ [16:64]) :
    WF.GadgetSpec (WF.VectorRel U.WFRel) (terminalScheduleParts i)
      (fun lv rv l r => U.WFRel lv rv l.1 r.1 ∧ U.WFRel lv rv l.2 r.2) := by
  unfold WF.GadgetSpec
  intro left right
  unfold terminalScheduleParts
  apply WF.GadgetSpec.bind_rule U.fromWord_wf_rel
  · intro lv rv h
    have hw := h.getElem! (i := i - 15) (by grind) |>.2
    change Word.WFRel lv rv _ _ at hw
    exact ((hw.rotateRight 7).xor (hw.rotateRight 18)).xor (hw.shiftRight 3)
  · intro A s0L s0R hs0
    apply WF.GadgetSpec.bind_rule U.fromWord_wf_rel
    · intro lv rv h
      have hw := (hs0 lv rv h).1.getElem! (i := i - 2) (by grind) |>.2
      change Word.WFRel lv rv _ _ at hw
      exact ((hw.rotateRight 17).xor (hw.rotateRight 19)).xor (hw.shiftRight 10)
    · intro B s1L s1R hs1
      apply WF.Rel.pure
      intro lv rv h
      exact ⟨(hs0 lv rv (hs1 lv rv h).1).2, (hs1 lv rv h).2⟩

set_option maxHeartbeats 1000000 in
theorem roundWithScheduleParts_wf (i : Nat) (hi : i ∈ [16:64]) :
    WF.GadgetSpec
      (fun lv rv
          (l r : Vector (U 32) 64 × RoundState (U 32) × U 32 × U 32) =>
        WF.VectorRel U.WFRel lv rv l.1 r.1 ∧
        RoundState.WFRel lv rv l.2.1 r.2.1 ∧
        U.WFRel lv rv l.2.2.1 r.2.2.1 ∧ U.WFRel lv rv l.2.2.2 r.2.2.2)
      (roundWithScheduleParts i hi) RoundState.WFRel := by
  unfold WF.GadgetSpec
  rintro ⟨wL, rL, s0L, s1L⟩ ⟨wR, rR, s0R, s1R⟩
  unfold roundWithScheduleParts
  apply WF.GadgetSpec.bind_rule U.fromWord_wf_rel
  · intro lv rv h
    have hin : WF.VectorRel U.WFRel lv rv wL wR ∧
        RoundState.WFRel lv rv rL rR ∧ U.WFRel lv rv s0L s0R ∧
        U.WFRel lv rv s1L s1R := h
    have he := hin.2.1.2.2.2.2.1.2
    change Word.WFRel lv rv _ _ at he
    exact ((he.rotateRight 6).xor (he.rotateRight 11)).xor (he.rotateRight 25)
  · intro A S1L S1R hS1
    apply WF.GadgetSpec.bind_rule
      (left := ⟨rL.2.2.2.2.1, rL.2.2.2.2.2.1, rL.2.2.2.2.2.2.1⟩)
      (right := ⟨rR.2.2.2.2.1, rR.2.2.2.2.2.1, rR.2.2.2.2.2.2.1⟩)
      optimized_ch2_wf
    · intro lv rv h
      have hin : WF.VectorRel U.WFRel lv rv wL wR ∧
          RoundState.WFRel lv rv rL rR ∧ U.WFRel lv rv s0L s0R ∧
          U.WFRel lv rv s1L s1R := (hS1 lv rv h).1
      have hr := hin.2.1
      exact ⟨hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1⟩
    · intro B chL chR hch
      apply WF.GadgetSpec.bind_rule U.fromWord_wf_rel
      · intro lv rv h
        have hin : WF.VectorRel U.WFRel lv rv wL wR ∧
            RoundState.WFRel lv rv rL rR ∧ U.WFRel lv rv s0L s0R ∧
            U.WFRel lv rv s1L s1R :=
          (hS1 lv rv (hch lv rv h).1).1
        have ha := hin.2.1.1.2
        change Word.WFRel lv rv _ _ at ha
        exact ((ha.rotateRight 2).xor (ha.rotateRight 13)).xor (ha.rotateRight 22)
      · intro C S0L S0R hS0
        apply WF.GadgetSpec.bind_rule
          (left := ⟨rL.1, rL.2.1, rL.2.2.1⟩)
          (right := ⟨rR.1, rR.2.1, rR.2.2.1⟩) optimized_maj2_wf
        · intro lv rv h
          have hr := (hS1 lv rv (hch lv rv (hS0 lv rv h).1).1).1.2.1
          exact ⟨hr.1, hr.2.1, hr.2.2.1⟩
        · intro D majL majR hmaj
          apply WF.GadgetSpec.bind_rule
            (left := ⟨#v[rL.2.2.2.1, rL.2.2.2.2.2.2.2, S1L,
              (k[i] : U 32), wL[i - 16]!, s0L, wL[i - 7]!, s1L], chL⟩)
            (right := ⟨#v[rR.2.2.2.1, rR.2.2.2.2.2.2.2, S1R,
              (k[i] : U 32), wR[i - 16]!, s0R, wR[i - 7]!, s1R], chR⟩)
            optimized_sum8Doubled1_wf
          · intro lv rv h
            have hD := hmaj lv rv h
            have hC := hS0 lv rv hD.1
            have hB := hch lv rv hC.1
            have hA := hS1 lv rv hB.1
            have hin := hA.1
            have hw := hin.1
            have hr := hin.2.1
            exact ⟨(by
              intro j
              fin_cases j
              · exact hr.2.2.2.1
              · exact hr.2.2.2.2.2.2.2
              · exact hA.2
              · exact U.wfRel_bitVec _ _ _
              · exact hw.getElem! (i := i - 16) (by grind)
              · exact hin.2.2.1
              · exact hw.getElem! (i := i - 7) (by grind)
              · exact hin.2.2.2), hB.2⟩
          · intro E newEL newER hnewE
            apply WF.GadgetSpec.bind_rule
              (left := ⟨rL.2.2.2.1, newEL, S0L, majL⟩)
              (right := ⟨rR.2.2.2.1, newER, S0R, majR⟩)
              optimized_sumAFromE_wf
            · intro lv rv h
              have hE := hnewE lv rv h
              have hD := hmaj lv rv hE.1
              have hC := hS0 lv rv hD.1
              have hB := hch lv rv hC.1
              have hA := hS1 lv rv hB.1
              have hr := hA.1.2.1
              exact ⟨hr.2.2.2.1, hE.2, hC.2, hD.2⟩
            · intro F newAL newAR hnewA
              apply WF.Rel.pure
              intro lv rv h
              have hF := hnewA lv rv h
              have hE := hnewE lv rv hF.1
              have hD := hmaj lv rv hE.1
              have hC := hS0 lv rv hD.1
              have hB := hch lv rv hC.1
              have hA := hS1 lv rv hB.1
              have hr := hA.1.2.1
              exact ⟨hF.2, hr.1, hr.2.1, hr.2.2.1, hE.2,
                hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1⟩

theorem inlineScheduleRound_wf (i : Nat) (hi : i ∈ [16:64]) :
    WF.GadgetSpec
      (fun lv rv (l r : Vector (U 32) 64 × RoundState (U 32)) =>
        WF.VectorRel U.WFRel lv rv l.1 r.1 ∧ RoundState.WFRel lv rv l.2 r.2)
      (inlineScheduleRound i hi) RoundState.WFRel := by
  unfold WF.GadgetSpec
  rintro ⟨wL, rL⟩ ⟨wR, rR⟩
  unfold inlineScheduleRound
  apply WF.GadgetSpec.bind_rule (terminalScheduleParts_wf i hi)
  · exact fun _ _ h => h.1
  · intro A partsL partsR hparts
    apply WF.Rel.mono ((roundWithScheduleParts_wf i hi).relHom A
      (wL, rL, partsL.1, partsL.2) (wR, rR, partsR.1, partsR.2) (by
        intro lv rv h
        have hp := hparts lv rv h
        exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩))
    exact fun _ _ _ _ h => h.2

set_option maxHeartbeats 1000000 in
theorem roundStep_wf (i : Nat) (hi : i ∈ [0:64]) :
    WF.GadgetSpec
      (fun lv rv (l r : Vector (U 32) 64 × RoundState (U 32)) =>
        WF.VectorRel U.WFRel lv rv l.1 r.1 ∧ RoundState.WFRel lv rv l.2 r.2)
      (roundStep i hi) RoundState.WFRel := by
  unfold WF.GadgetSpec
  rintro ⟨wL, rL⟩ ⟨wR, rR⟩
  unfold roundStep
  apply WF.GadgetSpec.bind_rule U.fromWord_wf_rel
  · intro lv rv h
    have he := h.2.2.2.2.2.1.2
    change Word.WFRel lv rv _ _ at he
    exact ((he.rotateRight 6).xor (he.rotateRight 11)).xor (he.rotateRight 25)
  · intro A S1L S1R hS1
    apply WF.GadgetSpec.bind_rule
      (left := ⟨rL.2.2.2.2.1, rL.2.2.2.2.2.1, rL.2.2.2.2.2.2.1⟩)
      (right := ⟨rR.2.2.2.2.1, rR.2.2.2.2.2.1, rR.2.2.2.2.2.2.1⟩)
      optimized_ch2_wf
    · intro lv rv h
      have hr := (hS1 lv rv h).1.2
      exact ⟨hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1⟩
    · intro B chL chR hch
      apply WF.GadgetSpec.bind_rule U.fromWord_wf_rel
      · intro lv rv h
        have ha := (hS1 lv rv (hch lv rv h).1).1.2.1.2
        change Word.WFRel lv rv _ _ at ha
        exact ((ha.rotateRight 2).xor (ha.rotateRight 13)).xor
          (ha.rotateRight 22)
      · intro C S0L S0R hS0
        apply WF.GadgetSpec.bind_rule
          (left := ⟨rL.1, rL.2.1, rL.2.2.1⟩)
          (right := ⟨rR.1, rR.2.1, rR.2.2.1⟩) optimized_maj2_wf
        · intro lv rv h
          have hr := (hS1 lv rv (hch lv rv (hS0 lv rv h).1).1).1.2
          exact ⟨hr.1, hr.2.1, hr.2.2.1⟩
        · intro D majL majR hmaj
          apply WF.GadgetSpec.bind_rule
            (left := ⟨rL.2.2.2.1, rL.2.2.2.2.2.2.2, S1L,
              (k[i] : U 32), wL[i], chL⟩)
            (right := ⟨rR.2.2.2.1, rR.2.2.2.2.2.2.2, S1R,
              (k[i] : U 32), wR[i], chR⟩) optimized_sum5Doubled1_wf
          · intro lv rv h
            have hD := hmaj lv rv h
            have hC := hS0 lv rv hD.1
            have hB := hch lv rv hC.1
            have hA := hS1 lv rv hB.1
            have hw := hA.1.1
            have hr := hA.1.2
            exact ⟨hr.2.2.2.1, hr.2.2.2.2.2.2.2, hA.2,
              U.wfRel_bitVec _ _ _, hw ⟨i, by grind⟩, hB.2⟩
          · intro E newEL newER hnewE
            apply WF.GadgetSpec.bind_rule
              (left := ⟨rL.2.2.2.1, newEL, S0L, majL⟩)
              (right := ⟨rR.2.2.2.1, newER, S0R, majR⟩)
              optimized_sumAFromE_wf
            · intro lv rv h
              have hE := hnewE lv rv h
              have hD := hmaj lv rv hE.1
              have hC := hS0 lv rv hD.1
              have hB := hch lv rv hC.1
              have hA := hS1 lv rv hB.1
              have hr := hA.1.2
              exact ⟨hr.2.2.2.1, hE.2, hC.2, hD.2⟩
            · intro F newAL newAR hnewA
              apply WF.Rel.pure
              intro lv rv h
              have hF := hnewA lv rv h
              have hE := hnewE lv rv hF.1
              have hD := hmaj lv rv hE.1
              have hC := hS0 lv rv hD.1
              have hB := hch lv rv hC.1
              have hA := hS1 lv rv hB.1
              have hr := hA.1.2
              exact ⟨hF.2, hr.1, hr.2.1, hr.2.2.1, hE.2,
                hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1⟩

theorem scheduleRoundStep_wf (i : Nat) (hi : i ∈ [16:62]) :
    WF.GadgetSpec
      (fun lv rv
          (l r : RoundState (U 32) × Vector (U 32) 64) =>
        RoundState.WFRel lv rv l.1 r.1 ∧
          WF.VectorRel U.WFRel lv rv l.2 r.2)
      (scheduleRoundStep i hi)
      (fun lv rv l r => RoundState.WFRel lv rv l.1 r.1 ∧
        WF.VectorRel U.WFRel lv rv l.2 r.2) := by
  unfold WF.GadgetSpec
  rintro ⟨rL, wL⟩ ⟨rR, wR⟩
  unfold scheduleRoundStep
  apply WF.GadgetSpec.bind_rule
    (scheduleStep_wf i (mem_range16_62_to_64 hi))
  · exact fun _ _ h => h.2
  · intro A wiL wiR hwi
    apply WF.GadgetSpec.bind_rule
      (roundStep_wf i (by
        change 16 ≤ i ∧ i < 62 ∧ (i - 16) % 1 = 0 at hi
        change 0 ≤ i ∧ i < 64 ∧ (i - 0) % 1 = 0
        exact ⟨by omega, by omega, Nat.mod_one _⟩))
    · intro lv rv h
      have ho := hwi lv rv h
      exact ⟨WF.VectorRel.set! ho.1.2 ho.2 i, ho.1.1⟩
    · intro B outL outR hout
      apply WF.Rel.pure
      intro lv rv h
      have hr := hout lv rv h
      have hw := hwi lv rv hr.1
      exact ⟨hr.2, WF.VectorRel.set! hw.1.2 hw.2 i⟩

theorem RoundState.WFRel.ofVector
    {sL sR : Vector (U 32) 8}
    (h : WF.VectorRel U.WFRel lv rv sL sR) :
    RoundState.WFRel lv rv
      ⟨sL[0], sL[1], sL[2], sL[3], sL[4], sL[5], sL[6], sL[7]⟩
      ⟨sR[0], sR[1], sR[2], sR[3], sR[4], sR[5], sR[6], sR[7]⟩ :=
  ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7⟩

theorem finish_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Vector (U 32) 8 × RoundState (U 32)) =>
        WF.VectorRel U.WFRel lv rv l.1 r.1 ∧ RoundState.WFRel lv rv l.2 r.2)
      finish (WF.VectorRel U.WFRel) := by
  unfold WF.GadgetSpec
  rintro ⟨sL, rL⟩ ⟨sR, rR⟩
  rw [finish_eq, finish_eq]
  apply WF.Rel.mono (WF.Rel.vectorOfFnM (S := fun _ => U.WFRel) ?_)
  · exact fun _ _ _ _ h => h.2
  · intro i A _ _ hA
    apply U.sumFixed_wf.relHom
    intro lv rv h
    have hin := hA lv rv h
    intro j
    fin_cases j
    · exact hin.1 i
    · unfold roundVector
      fin_cases i <;> simp only [Fin.getElem_fin] <;>
        first | exact hin.2.1 | exact hin.2.2.1 |
          exact hin.2.2.2.1 | exact hin.2.2.2.2.1 |
          exact hin.2.2.2.2.2.1 | exact hin.2.2.2.2.2.2.1 |
          exact hin.2.2.2.2.2.2.2.1 | exact hin.2.2.2.2.2.2.2.2

set_option maxHeartbeats 1000000 in
theorem finalRoundTransforms_wf :
    WF.GadgetSpec RoundState.WFRel finalRoundTransforms
      (fun lv rv l r => U.WFRel lv rv l.1 r.1 ∧
        WF.LCEq lv.int rv.int l.2.1 r.2.1 ∧
        U.WFRel lv rv l.2.2.1 r.2.2.1 ∧
        WF.LCEq lv.int rv.int l.2.2.2 r.2.2.2) := by
  unfold WF.GadgetSpec
  intro rL rR
  unfold finalRoundTransforms
  apply WF.GadgetSpec.bind_rule U.fromWord_wf_rel
  · intro lv rv h
    have he := h.2.2.2.2.1.2
    change Word.WFRel lv rv _ _ at he
    exact ((he.rotateRight 6).xor (he.rotateRight 11)).xor (he.rotateRight 25)
  · intro A S1L S1R hS1
    apply WF.GadgetSpec.bind_rule
      (left := ⟨rL.2.2.2.2.1, rL.2.2.2.2.2.1, rL.2.2.2.2.2.2.1⟩)
      (right := ⟨rR.2.2.2.2.1, rR.2.2.2.2.2.1, rR.2.2.2.2.2.2.1⟩)
      optimized_ch2_wf
    · intro lv rv h
      have hr := (hS1 lv rv h).1
      exact ⟨hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1⟩
    · intro B chL chR hch
      apply WF.GadgetSpec.bind_rule U.fromWord_wf_rel
      · intro lv rv h
        have ha := (hS1 lv rv (hch lv rv h).1).1.1.2
        change Word.WFRel lv rv _ _ at ha
        exact ((ha.rotateRight 2).xor (ha.rotateRight 13)).xor (ha.rotateRight 22)
      · intro C S0L S0R hS0
        apply WF.GadgetSpec.bind_rule
          (left := ⟨rL.1, rL.2.1, rL.2.2.1⟩)
          (right := ⟨rR.1, rR.2.1, rR.2.2.1⟩) optimized_maj2_wf
        · intro lv rv h
          have hr := (hS1 lv rv (hch lv rv (hS0 lv rv h).1).1).1
          exact ⟨hr.1, hr.2.1, hr.2.2.1⟩
        · intro D majL majR hmaj
          apply WF.Rel.pure
          intro lv rv h
          have hD := hmaj lv rv h
          have hC := hS0 lv rv hD.1
          have hB := hch lv rv hC.1
          have hA := hS1 lv rv hB.1
          exact ⟨hA.2, hB.2, hC.2, hD.2⟩

set_option maxHeartbeats 1000000 in
theorem finalRoundSums_wf (i : Nat) (hi : i ∈ [16:64]) :
    WF.GadgetSpec
      (fun lv rv (l r : Vector (U 32) 64 × RoundState (U 32) ×
          Vector (U 32) 8 × U 32 × U 32 × U 32 × LC ℤ × U 32 × LC ℤ) =>
        WF.VectorRel U.WFRel lv rv l.1 r.1 ∧
        RoundState.WFRel lv rv l.2.1 r.2.1 ∧
        WF.VectorRel U.WFRel lv rv l.2.2.1 r.2.2.1 ∧
        U.WFRel lv rv l.2.2.2.1 r.2.2.2.1 ∧
        U.WFRel lv rv l.2.2.2.2.1 r.2.2.2.2.1 ∧
        U.WFRel lv rv l.2.2.2.2.2.1 r.2.2.2.2.2.1 ∧
        WF.LCEq lv.int rv.int l.2.2.2.2.2.2.1 r.2.2.2.2.2.2.1 ∧
        U.WFRel lv rv l.2.2.2.2.2.2.2.1 r.2.2.2.2.2.2.2.1 ∧
        WF.LCEq lv.int rv.int l.2.2.2.2.2.2.2.2 r.2.2.2.2.2.2.2.2)
      (finalRoundSums i hi)
      (fun lv rv l r => U.WFRel lv rv l.1 r.1 ∧ U.WFRel lv rv l.2 r.2) := by
  unfold WF.GadgetSpec
  rintro ⟨wL, rL, sL, s0L, s1L, S1L, chL, S0L, majL⟩
    ⟨wR, rR, sR, s0R, s1R, S1R, chR, S0R, majR⟩
  unfold finalRoundSums
  apply WF.GadgetSpec.bind_rule
    (left := ⟨#v[rL.2.2.2.1, rL.2.2.2.2.2.2.2, S1L, (k[i] : U 32),
      wL[i - 16]!, s0L, wL[i - 7]!, s1L, sL[4]], chL⟩)
    (right := ⟨#v[rR.2.2.2.1, rR.2.2.2.2.2.2.2, S1R, (k[i] : U 32),
      wR[i - 16]!, s0R, wR[i - 7]!, s1R, sR[4]], chR⟩)
    optimized_sum9Doubled1_wf
  · intro lv rv h
    exact ⟨(by
      intro j
      fin_cases j
      · exact h.2.1.2.2.2.1
      · exact h.2.1.2.2.2.2.2.2.2
      · exact h.2.2.2.2.2.1
      · exact U.wfRel_bitVec _ _ _
      · exact h.1.getElem! (i := i - 16) (by grind)
      · exact h.2.2.2.1
      · exact h.1.getElem! (i := i - 7) (by grind)
      · exact h.2.2.2.2.1
      · exact h.2.2.1 4), h.2.2.2.2.2.2.1⟩
  · intro A outEL outER houtE
    apply WF.GadgetSpec.bind_rule
      (left := ⟨rL.2.2.2.1, outEL, S0L, sL[0], sL[4], majL⟩)
      (right := ⟨rR.2.2.2.1, outER, S0R, sR[0], sR[4], majR⟩)
      optimized_sumAFinal_wf
    · intro lv rv h
      have hE := houtE lv rv h
      have hin := hE.1
      exact ⟨hin.2.1.2.2.2.1, hE.2, hin.2.2.2.2.2.2.2.1,
        hin.2.2.1 0, hin.2.2.1 4, hin.2.2.2.2.2.2.2.2⟩
    · intro B outAL outAR houtA
      apply WF.Rel.pure
      intro lv rv h
      have hA := houtA lv rv h
      have hE := houtE lv rv hA.1
      exact ⟨hA.2, hE.2⟩

set_option maxHeartbeats 1000000 in
theorem finalRoundBody_wf (i : Nat) (hi : i ∈ [16:64]) :
    WF.GadgetSpec
      (fun lv rv (l r : Vector (U 32) 64 × RoundState (U 32) ×
          Vector (U 32) 8 × U 32 × U 32) =>
        WF.VectorRel U.WFRel lv rv l.1 r.1 ∧
        RoundState.WFRel lv rv l.2.1 r.2.1 ∧
        WF.VectorRel U.WFRel lv rv l.2.2.1 r.2.2.1 ∧
        U.WFRel lv rv l.2.2.2.1 r.2.2.2.1 ∧
        U.WFRel lv rv l.2.2.2.2 r.2.2.2.2)
      (finalRoundBody i hi)
      (fun lv rv l r => U.WFRel lv rv l.1 r.1 ∧ U.WFRel lv rv l.2 r.2) := by
  unfold WF.GadgetSpec
  rintro ⟨wL, rL, sL, s0L, s1L⟩ ⟨wR, rR, sR, s0R, s1R⟩
  unfold finalRoundBody
  apply WF.GadgetSpec.bind_rule finalRoundTransforms_wf
  · exact fun lv rv h => h.2.1
  · intro A tL tR ht
    apply WF.Rel.mono ((finalRoundSums_wf i hi).relHom A
      (wL, rL, sL, s0L, s1L, tL.1, tL.2.1, tL.2.2.1, tL.2.2.2)
      (wR, rR, sR, s0R, s1R, tR.1, tR.2.1, tR.2.2.1, tR.2.2.2) (by
        intro lv rv h
        have hT := ht lv rv h
        exact ⟨hT.1.1, hT.1.2.1, hT.1.2.2.1, hT.1.2.2.2.1,
          hT.1.2.2.2.2, hT.2.1, hT.2.2.1, hT.2.2.2.1, hT.2.2.2.2⟩))
    exact fun _ _ _ _ h => h.2

set_option maxHeartbeats 1000000 in
theorem finalRoundCore_wf (i : Nat) (hi : i ∈ [16:64]) :
    WF.GadgetSpec
      (fun lv rv
          (l r : Vector (U 32) 64 × RoundState (U 32) × Vector (U 32) 8) =>
        WF.VectorRel U.WFRel lv rv l.1 r.1 ∧
        RoundState.WFRel lv rv l.2.1 r.2.1 ∧
        WF.VectorRel U.WFRel lv rv l.2.2 r.2.2)
      (finalRoundCore i hi)
      (fun lv rv l r => U.WFRel lv rv l.1 r.1 ∧ U.WFRel lv rv l.2 r.2) := by
  unfold WF.GadgetSpec
  rintro ⟨wL, rL, sL⟩ ⟨wR, rR, sR⟩
  unfold finalRoundCore
  apply WF.GadgetSpec.bind_rule (terminalScheduleParts_wf i hi)
  · exact fun lv rv h => h.1
  · intro A partsL partsR hparts
    apply WF.Rel.mono ((finalRoundBody_wf i hi).relHom A
      (wL, rL, sL, partsL.1, partsL.2)
      (wR, rR, sR, partsR.1, partsR.2) (by
        intro lv rv h
        have hp := hparts lv rv h
        exact ⟨hp.1.1, hp.1.2.1, hp.1.2.2, hp.2.1, hp.2.2⟩))
    exact fun _ _ _ _ h => h.2

private def finalRoundTailState (r : RoundState α) : Vector α 8 :=
  #v[r.1, r.1, r.2.1, r.2.2.1, r.2.2.2.2.1,
    r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1]

private def finalRoundTailAt (out : U 32 × U 32) (r : RoundState (U 32))
    (s : Vector (U 32) 8) (i : Fin 8) : Circuit (U 32) :=
  if i = 0 then pure out.1
  else if i = 4 then pure out.2
  else U.sumFixedAffineLow #v[s[i], (finalRoundTailState r)[i]]

private theorem finalRoundTail_eq (out : U 32 × U 32)
    (r : RoundState (U 32)) (s : Vector (U 32) 8) :
    finalRoundTail (out, r, s) =
      Vector.ofFnM (finalRoundTailAt out r s) := by
  simp [finalRoundTail, finalRoundTailAt, Vector.ofFnM_succ,
    Vector.ofFnM_zero, finalRoundTailState]

theorem finalRoundTail_wf :
    WF.GadgetSpec
      (fun lv rv (l r : (U 32 × U 32) × RoundState (U 32) × Vector (U 32) 8) =>
        (U.WFRel lv rv l.1.1 r.1.1 ∧ U.WFRel lv rv l.1.2 r.1.2) ∧
        RoundState.WFRel lv rv l.2.1 r.2.1 ∧
        WF.VectorRel U.WFRel lv rv l.2.2 r.2.2)
      finalRoundTail (WF.VectorRel U.WFRel) := by
  unfold WF.GadgetSpec
  rintro ⟨outL, rL, sL⟩ ⟨outR, rR, sR⟩
  rw [finalRoundTail_eq, finalRoundTail_eq]
  apply WF.Rel.mono (WF.Rel.vectorOfFnM (S := fun _ => U.WFRel) ?_)
  · exact fun _ _ _ _ h => h.2
  · intro i A _ _ hA
    unfold finalRoundTailAt
    split
    · apply WF.Rel.pure
      intro lv rv h
      exact ⟨h, (hA lv rv h).1.1⟩
    · split
      · apply WF.Rel.pure
        intro lv rv h
        exact ⟨h, (hA lv rv h).1.2⟩
      · apply U.sumFixedAffineLow_wf.relHom
        intro lv rv h
        have hin := hA lv rv h
        intro j
        fin_cases j
        · exact hin.2.2 i
        · unfold finalRoundTailState
          fin_cases i <;> simp only [Fin.getElem_fin] <;>
            first | exact hin.2.1.1 | exact hin.2.1.2.1 |
              exact hin.2.1.2.2.1 | exact hin.2.1.2.2.2.1 |
              exact hin.2.1.2.2.2.2.1 | exact hin.2.1.2.2.2.2.2.1 |
              exact hin.2.1.2.2.2.2.2.2.1

set_option maxHeartbeats 1000000 in
theorem finalRound_wf (i : Nat) (hi : i ∈ [16:64]) :
    WF.GadgetSpec
      (fun lv rv
          (l r : Vector (U 32) 64 × RoundState (U 32) × Vector (U 32) 8) =>
        WF.VectorRel U.WFRel lv rv l.1 r.1 ∧
        RoundState.WFRel lv rv l.2.1 r.2.1 ∧
        WF.VectorRel U.WFRel lv rv l.2.2 r.2.2)
      (finalRound i hi) (WF.VectorRel U.WFRel) := by
  unfold WF.GadgetSpec
  rintro ⟨wL, rL, sL⟩ ⟨wR, rR, sR⟩
  unfold finalRound
  apply WF.GadgetSpec.bind_rule (finalRoundCore_wf i hi)
  · exact fun _ _ h => h
  · intro A outL outR hout
    apply WF.Rel.mono (finalRoundTail_wf.relHom A
      (outL, rL, sL) (outR, rR, sR) (by
        intro lv rv h
        have ho := hout lv rv h
        exact ⟨ho.2, ho.1.2.1, ho.1.2.2⟩))
    exact fun _ _ _ _ h => h.2

theorem terminalRounds_wf :
    WF.GadgetSpec
      (fun lv rv
          (l r : Vector (U 32) 64 × RoundState (U 32) × Vector (U 32) 8) =>
        WF.VectorRel U.WFRel lv rv l.1 r.1 ∧
        RoundState.WFRel lv rv l.2.1 r.2.1 ∧
        WF.VectorRel U.WFRel lv rv l.2.2 r.2.2)
      terminalRounds (WF.VectorRel U.WFRel) := by
  unfold WF.GadgetSpec
  rintro ⟨wL, rL, sL⟩ ⟨wR, rR, sR⟩
  unfold terminalRounds
  apply WF.GadgetSpec.bind_rule
    (inlineScheduleRound_wf 62 (by
      change 16 ≤ 62 ∧ 62 < 64 ∧ (62 - 16) % 1 = 0
      norm_num))
  · intro lv rv h
    exact ⟨h.1, h.2.1⟩
  · intro A r62L r62R hr62
    apply WF.Rel.mono ((finalRound_wf 63 (by
      change 16 ≤ 63 ∧ 63 < 64 ∧ (63 - 16) % 1 = 0
      norm_num)).relHom A ⟨wL, r62L, sL⟩ ⟨wR, r62R, sR⟩ (by
        intro lv rv hA
        have h62 := hr62 lv rv hA
        exact ⟨h62.1.1, h62.2, h62.1.2.2⟩))
    exact fun _ _ _ _ h => h.2

set_option maxHeartbeats 1000000 in
theorem permPrefix_wf :
    WF.GadgetSpec
      (fun lv rv
          (l r : Vector (Word 32) 16 × Vector (U 32) 8) =>
        WF.VectorRel Word.WFRel lv rv l.1 r.1 ∧
          WF.VectorRel U.WFRel lv rv l.2 r.2)
      (fun x => permPrefix x.1 x.2)
      (fun lv rv l r =>
        WF.VectorRel U.WFRel lv rv l.1 r.1 ∧
        RoundState.WFRel lv rv l.2.1 r.2.1 ∧
        WF.VectorRel U.WFRel lv rv l.2.2 r.2.2) := by
  unfold WF.GadgetSpec
  intro left right
  unfold permPrefix
  wfgen' using [U.fromWord_wf_rel, scheduleStep_wf, roundStep_wf]
  case inv1 => exact WF.VectorRel U.WFRel
  case vc1 =>
    exact fun lv rv _ => U.vector_default_wfRel lv rv
  case vc2 =>
    intro i hi P wL wR hw
    apply WF.GadgetSpec.bind_rule U.fromWord_wf_rel
    · intro lv rv h
      exact (hw lv rv h).1.1 ⟨i, by grind⟩
    · intro B outL outR hout
      apply WF.Rel.pure
      intro lv rv hB
      have ho := hout lv rv hB
      have hin := hw lv rv ho.1
      exact ⟨ho.1, hin.1, WF.VectorRel.set! hin.2 ho.2 i⟩
  case vc3 =>
    intro B wL wR hw
    apply WF.Rel.forIn'_range_map_yield_bind_rule
      (I := RoundState.WFRel)
      (fL := fun i hi r => roundStep i (by
        change 0 ≤ i ∧ i < 64 ∧ (i - 0) % 1 = 0
        have hil : i < 16 := by simpa using hi.upper
        exact ⟨by omega, by omega, Nat.mod_one _⟩) (wL, r))
      (fR := fun i hi r => roundStep i (by
        change 0 ≤ i ∧ i < 64 ∧ (i - 0) % 1 = 0
        have hil : i < 16 := by simpa using hi.upper
        exact ⟨by omega, by omega, Nat.mod_one _⟩) (wR, r))
      (nextL := fun _ _ _ out => out)
      (nextR := fun _ _ _ out => out)
    case hinit =>
      intro lv rv h
      exact RoundState.WFRel.ofVector (hw lv rv h).1.2
    case hstep =>
      intro i hi P rL rR hP
      have hstep := (roundStep_wf i (by
        change 0 ≤ i ∧ i < 64 ∧ (i - 0) % 1 = 0
        have hil : i < 16 := by simpa using hi.upper
        exact ⟨by omega, by omega, Nat.mod_one _⟩)).relHom P
        (wL, rL) (wR, rR) (by
          intro lv rv h
          have hp := hP lv rv h
          exact ⟨(hw lv rv hp.1).2, hp.2⟩)
      apply WF.Rel.mono hstep
      exact fun lv rv _ _ hout => ⟨hout.1, (hP lv rv hout.1).1, hout.2⟩
    case hcont =>
      intro C rL rR hround
      apply WF.Rel.forIn'_range_map_yield_bind_rule
        (I := fun lv rv
          (l r : RoundState (U 32) × Vector (U 32) 64) =>
          RoundState.WFRel lv rv l.1 r.1 ∧
            WF.VectorRel U.WFRel lv rv l.2 r.2)
        (fL := fun i hi x => scheduleRoundStep i hi x)
        (fR := fun i hi x => scheduleRoundStep i hi x)
        (nextL := fun _ _ _ out => out)
        (nextR := fun _ _ _ out => out)
      case hinit =>
        intro lv rv h
        have hr := hround lv rv h
        exact ⟨hr.2, (hw lv rv hr.1).2⟩
      case hstep =>
        intro i hi P xL xR hP
        have hstep := (scheduleRoundStep_wf i hi).relHom P xL xR
          (fun lv rv h => (hP lv rv h).2)
        apply WF.Rel.mono hstep
        exact fun lv rv _ _ hout => ⟨hout.1, (hP lv rv hout.1).1, hout.2⟩
      case hcont =>
        intro D xL xR hx
        apply WF.Rel.pure
        intro lv rv hD
        have hp := hx lv rv hD
        have hc := hround lv rv hp.1
        have h0 := hw lv rv hc.1
        exact ⟨hp.2.2, hp.2.1, h0.1.2⟩

set_option maxHeartbeats 1000000 in
theorem structured_wf :
    WF.GadgetSpec
      (fun lv rv
          (l r : Vector (Word 32) 16 × Vector (Word 32) 8) =>
        WF.VectorRel Word.WFRel lv rv l.1 r.1 ∧
          WF.VectorRel Word.WFRel lv rv l.2 r.2)
      (fun x => structured x.1 x.2) (WF.VectorRel U.WFRel) := by
  unfold WF.GadgetSpec
  intro left right
  unfold structured permCircuit
  apply WF.GadgetSpec.bind_rule
    (left := left.2) (right := right.2) U.mapM_fromWord_wf
  · exact fun lv rv h => h.2
  · intro A sL sR hs
    apply WF.GadgetSpec.bind_rule
      (left := (left.1, sL)) (right := (right.1, sR)) permPrefix_wf
    · intro lv rv h
      have hsu := hs lv rv h
      exact ⟨hsu.1.1, hsu.2⟩
    · intro B wrL wrR hwr
      apply WF.Rel.mono (terminalRounds_wf.relHom B wrL wrR (by
        intro lv rv hB
        exact (hwr lv rv hB).2))
      exact fun _ _ _ _ h => h.2

private def permScheduleStepBV (i : Nat)
    (w : Vector (BitVec 32) 64) :=
  w.set! i
    (w[i - 16]! +
      (w[i - 15]!.rotateRight 7 ^^^ w[i - 15]!.rotateRight 18 ^^^
        (w[i - 15]! >>> 3)) + w[i - 7]! +
      (w[i - 2]!.rotateRight 17 ^^^ w[i - 2]!.rotateRight 19 ^^^
        (w[i - 2]! >>> 10)))

private theorem permScheduleStepBV_eq (i : Nat)
    (w : Vector (BitVec 32) 64) :
    permScheduleStepBV i w = w.set! i (scheduleStepBV i w) := by
  unfold permScheduleStepBV scheduleStepBV
  congr 1
  rw [← Array.sum_toList]
  simp only [List.sum_cons, List.sum_nil]
  ac_rfl

private def permRoundStepBV (i : Nat) (hi : i ∈ [0:64])
    (w : Vector (BitVec 32) 64) (r : RoundState (BitVec 32)) :
    RoundState (BitVec 32) :=
  ⟨r.2.2.2.2.2.2.2 +
      (r.2.2.2.2.1.rotateRight 6 ^^^ r.2.2.2.2.1.rotateRight 11 ^^^
        r.2.2.2.2.1.rotateRight 25) +
      chBV r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1 + k[i] + w[i] +
      ((r.1.rotateRight 2 ^^^ r.1.rotateRight 13 ^^^ r.1.rotateRight 22) +
        majBV r.1 r.2.1 r.2.2.1),
    r.1, r.2.1, r.2.2.1,
    r.2.2.2.1 + (r.2.2.2.2.2.2.2 +
      (r.2.2.2.2.1.rotateRight 6 ^^^ r.2.2.2.2.1.rotateRight 11 ^^^
        r.2.2.2.2.1.rotateRight 25) +
      chBV r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1 + k[i] + w[i]),
    r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1⟩

private theorem permRoundStepBV_eq (i : Nat) (hi : i ∈ [0:64])
    (w : Vector (BitVec 32) 64) (r : RoundState (BitVec 32)) :
    permRoundStepBV i hi w r = roundStepBV i w r := by
  unfold permRoundStepBV roundStepBV
  simp only [getElem!_pos k i (by grind), getElem!_pos w i (by grind)]
  simp only [← Array.sum_toList, List.sum_cons, List.sum_nil]
  congr 1 <;> ac_rfl

theorem perm_eq_model (m : Vector (BitVec 32) 16)
    (s : Vector (BitVec 32) 8) : perm m s = model m s := by
  unfold perm model finishBV roundsBV scheduleBV initialSchedule initialRound
  simp only [Id.run, forIn_eq_forIn', pure_bind]
  have hinit :
      (forIn' [0:16] (Vector.replicate 64 (0 : BitVec 32)) fun i hi w =>
        (pure (ForInStep.yield (w.set! i m[i])) : Id _)) =
      pure (([0:16].toList).foldl (fun w i => w.set! i m[i]!) default) := by
    apply Std.Legacy.Range.id_forIn'_yield_congr
    intro i hi w
    rw [getElem!_pos m i (by grind)]
  conv_lhs => enter [1]; rw [hinit]
  simp only [pure_bind]
  let init := ([0:16].toList).foldl (fun w i => w.set! i m[i]!)
    (default : Vector (BitVec 32) 64)
  have hschedule :
      (forIn' [16:64] init fun i _ w =>
        (pure (ForInStep.yield (permScheduleStepBV i w)) : Id _)) =
      pure (([16:64].toList).foldl
        (fun w i => w.set! i (scheduleStepBV i w)) init) := by
    apply Std.Legacy.Range.id_forIn'_yield_congr
    exact fun i _ w => permScheduleStepBV_eq i w
  have hscheduleRaw := hschedule
  dsimp only [permScheduleStepBV] at hscheduleRaw
  conv_lhs => enter [1]; rw [hscheduleRaw]
  simp only [pure_bind]
  let w := ([16:64].toList).foldl
    (fun w i => w.set! i (scheduleStepBV i w)) init
  have hround :
      (forIn' [0:64]
        ⟨s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]⟩
        fun i hi r =>
          (pure (ForInStep.yield (permRoundStepBV i hi w r)) : Id _)) =
      pure (([0:64].toList).foldl (fun r i => roundStepBV i w r)
        ⟨s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]⟩) := by
    apply Std.Legacy.Range.id_forIn'_yield_congr
    exact fun i hi r => permRoundStepBV_eq i hi w r
  have hroundRaw := hround
  dsimp only [permRoundStepBV, chBV, majBV] at hroundRaw
  dsimp only [w, init] at hroundRaw
  conv_lhs => enter [1]; exact hroundRaw
  simp only [pure_bind]

def messageInput (inp : Vector (LC Bool) 768) : Vector (Word 32) 16 :=
  Vector.ofFn fun wi => Word.mk (Vector.ofFn fun bi =>
    inp[wi.val * 32 + bi.val])

def stateInput (inp : Vector (LC Bool) 768) : Vector (Word 32) 8 :=
  Vector.ofFn fun si => Word.mk (Vector.ofFn fun bi =>
    inp[512 + si.val * 32 + bi.val])

def flattenOutput (out : Vector (U 32) 8) : Vector (LC Bool) 256 :=
  Vector.ofFn fun i => out[i.val / 32].bits.bitsLE[i.val % 32]

theorem permCirc'_eq (inp : Vector (LC Bool) 768) :
    permCirc' inp = (do
      let out ← structured (messageInput inp) (stateInput inp)
      pure (flattenOutput out)) := rfl

theorem inputWords_wf (index : Fin n → Fin 32 → Fin 768)
    (h : WF.VectorRel (fun lv rv (l r : LC Bool) =>
      WF.LCEq lv.bool rv.bool l r) lv rv left right) :
    WF.VectorRel Word.WFRel lv rv
      (Vector.ofFn fun wi => Word.mk (Vector.ofFn fun bi => left[index wi bi]))
      (Vector.ofFn fun wi => Word.mk (Vector.ofFn fun bi => right[index wi bi])) := by
  intro wi bi
  simpa only [Word.WFRel, Vector.getElem_ofFn, Fin.getElem_fin] using
    h (index wi bi)

attribute [irreducible] messageInput stateInput flattenOutput

theorem permCirc'_wf :
    WF.GadgetSpec
      (WF.VectorRel fun lv rv (l r : LC Bool) =>
        WF.LCEq lv.bool rv.bool l r)
      permCirc'
      (WF.VectorRel fun lv rv (l r : LC Bool) =>
        WF.LCEq lv.bool rv.bool l r) := by
  unfold WF.GadgetSpec
  intro left right
  rw [permCirc'_eq, permCirc'_eq]
  apply WF.GadgetSpec.bind_rule
    (left := ⟨messageInput left, stateInput left⟩)
    (right := ⟨messageInput right, stateInput right⟩) structured_wf
  · intro lv rv h
    constructor
    · unfold messageInput
      exact inputWords_wf
        (fun wi bi => ⟨wi.val * 32 + bi.val, by omega⟩) h
    · unfold stateInput
      exact inputWords_wf
        (fun si bi => ⟨512 + si.val * 32 + bi.val, by omega⟩) h
  · intro A outL outR hout
    apply WF.Rel.pure
    intro lv rv hA i
    change WF.LCEq lv.bool rv.bool
      (flattenOutput outL)[i] (flattenOutput outR)[i]
    rw [show (flattenOutput outL)[i] =
      outL[i.val / 32].bits.bitsLE[i.val % 32] by
        unfold flattenOutput; simp,
      show (flattenOutput outR)[i] =
      outR[i.val / 32].bits.bitsLE[i.val % 32] by
        unfold flattenOutput; simp]
    exact ((hout lv rv hA).2 ⟨i.val / 32, by omega⟩).2
      ⟨i.val % 32, by omega⟩

theorem permCirc'_complete_triple (inputWires : Vector (LC Bool) 768) :
    ⦃⌜True⌝⦄ Complete.interp ρ (permCirc' inputWires)
    ⦃⇓ _ => ⌜True⌝⦄ := by
  rw [permCirc'_eq, Complete.interp_bind]
  apply Triple.bind (Q := fun out => ⌜∀ i : Fin 8, out[i].Valid ρ⌝)
  case hx => exact structured_complete
  case hf => intro out; mvcgen

theorem inputWords_eval (values : Vector Bool 768) (valuation : Nat → Bool)
    (hvalues : ∀ i : Fin 768, valuation i.val = values[i])
    (index : Fin n → Fin 32 → Fin 768) :
    (Vector.ofFn fun wi => Word.mk (Vector.ofFn fun bi =>
      ({(index wi bi).val} : LC Bool))).map (Word.eval valuation) =
    Vector.ofFn fun wi =>
      BitVec.ofNat 32 (Nat.ofBits fun bi => values[(index wi bi).val]) := by
  apply Vector.ext
  intro wi hwi
  apply BitVec.eq_of_getElem_eq
  intro bi hbi
  simp only [Vector.getElem_map, Vector.getElem_ofFn, Word.eval,
    BitVec.getElem_ofFnLE, Fin.getElem_fin,
    Vector.getElem_ofFn, LC.eval_singleton]
  rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow _),
    Nat.testBit_ofBits_lt _ _ hbi]
  exact hvalues (index ⟨wi, hwi⟩ ⟨bi, hbi⟩)

theorem flatten_eval {out : Vector (U 32) 8}
    {value : Vector (BitVec 32) 8} (h : Vector.Rel ρ out value) :
    (Vector.ofFn fun i : Fin 256 =>
      out[i.val / 32].bits.bitsLE[i.val % 32]).map
        (fun x => x.eval ρ.bool) =
      Vector.ofFn fun i : Fin 256 =>
        value[i.val / 32].toNat.testBit (i.val % 32) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  have hu := h ⟨i / 32, by omega⟩
  have hbit := congrArg (fun x : BitVec 32 => x[i % 32]'(by omega))
    (U.eval_eq_ofFnLE _ hu.1)
  rw [hu.2] at hbit
  simp only [BitVec.getElem_ofFnLE] at hbit
  rw [BitVec.getElem_eq_testBit_toNat] at hbit
  exact hbit.symm

def permSoundPost (wireInputs : Vector (LC Bool) 768)
    (valuation : WF.Valuation) (out : Vector (U 32) 8) : Prop :=
  Vector.Rel valuation out
    (model
      ((messageInput wireInputs).map (Word.eval valuation.bool))
      ((stateInput wireInputs).map (Word.eval valuation.bool)))

theorem permCirc'_sound_triple (inputs : Vector Bool 768)
    (wit : Nat → Bool)
    (hinputs : ∀ i : Fin 768, wit i.val = inputs[i])
    (cs : Semantics.CS) :
    ⦃⌜True⌝⦄ Sound.interp (Sound.csValuation cs wit)
    (permCirc' (Vector.ofFn fun i => ({i.val} : LC Bool)))
    ⦃⇓ out => ⌜out.map (fun x => x.eval wit) = perm' inputs⌝⦄ := by
  rw [permCirc'_eq, Sound.interp_bind]
  apply Triple.bind
    (Q := fun out => ⌜permSoundPost
      (Vector.ofFn fun i => ({i.val} : LC Bool))
      (Sound.csValuation cs wit) out⌝)
  case hx =>
    unfold permSoundPost
    exact structured_sound
  case hf =>
    intro out
    apply Triple.pure
    simp only [SPred.entails_nil]
    intro hout
    unfold permSoundPost at hout
    unfold messageInput stateInput at hout
    unfold flattenOutput
    simp only [Sound.csValuation] at hout ⊢
    simp only [Vector.getElem_ofFn] at hout
    rw [flatten_eval hout]
    have hperm := congrArg₂ model
      (inputWords_eval inputs wit hinputs
        (fun wi bi => ⟨wi.val * 32 + bi.val, by omega⟩))
      (inputWords_eval inputs wit hinputs
        (fun si bi => ⟨512 + si.val * 32 + bi.val, by omega⟩))
    rw [hperm]
    simp only [perm', perm_eq_model]
    exact True.intro

end Freigen.F2Z.Examples
