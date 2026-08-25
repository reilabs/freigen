import Freigen.F2Z.Examples.Sha256.Model
import Freigen.F2Z.Correctness.U

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


abbrev RoundState (α : Type) :=
  MProd α (MProd α (MProd α (MProd α (MProd α (MProd α (MProd α α))))))

def roundVector (r : RoundState α) : Vector α 8 :=
  #v[r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1,
    r.2.2.2.2.2.1, r.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2]

def scheduleStep (i : Nat) (w : Vector (U 32) 64) : Circuit (U 32) := do
  let wi15 := w[i - 15]!.bits
  let s0 ← U.fromWord $
    wi15.rotateRight 7 ^^^ wi15.rotateRight 18 ^^^ (wi15 >>> 3)
  let wi2 := w[i - 2]!.bits
  let s1 ← U.fromWord $
    wi2.rotateRight 17 ^^^ wi2.rotateRight 19 ^^^ (wi2 >>> 10)
  U.sum #[w[i - 16]!, s0, w[i - 7]!, s1]

def roundStep (i : Nat) (hi : i ∈ [0:64])
    (x : Vector (U 32) 64 × RoundState (U 32)) : Circuit (RoundState (U 32)) := do
  let w := x.1
  let r := x.2
  let S1 ← U.fromWord $ r.2.2.2.2.1.bits.rotateRight 6 ^^^
    r.2.2.2.2.1.bits.rotateRight 11 ^^^ r.2.2.2.2.1.bits.rotateRight 25
  let ch2 ← U.ch2 r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1
  let S0 ← U.fromWord $ r.1.bits.rotateRight 2 ^^^
    r.1.bits.rotateRight 13 ^^^ r.1.bits.rotateRight 22
  let maj2 ← U.maj2 r.1 r.2.1 r.2.2.1
  let newE ← U.sum5Doubled1 r.2.2.2.1 r.2.2.2.2.2.2.2 S1 k[i] w[i] ch2
  let newA ← U.sum5Doubled2 r.2.2.2.2.2.2.2 S1 k[i] w[i] S0 ch2 maj2
  pure ⟨newA, r.1, r.2.1, r.2.2.1, newE,
    r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1⟩

def finish (x : Vector (U 32) 8 × RoundState (U 32)) :
    Circuit (Vector (U 32) 8) := do
  let s := x.1
  let r := x.2
  pure #v[
    ←U.sum #[s[0], r.1],
    ←U.sum #[s[1], r.2.1],
    ←U.sum #[s[2], r.2.2.1],
    ←U.sum #[s[3], r.2.2.2.1],
    ←U.sum #[s[4], r.2.2.2.2.1],
    ←U.sum #[s[5], r.2.2.2.2.2.1],
    ←U.sum #[s[6], r.2.2.2.2.2.2.1],
    ←U.sum #[s[7], r.2.2.2.2.2.2.2]]

def structured (m : Vector (Word 32) 16) (s : Vector (Word 32) 8) :
    Circuit (Vector (U 32) 8) := do
  let su ← s.mapM U.fromWord
  let mut w : Vector (U 32) 64 := default
  for h:i in [0:16] do
    w := w.set! i $ ←U.fromWord m[i]
  for hi:i in [16:64] do
    w := w.set! i $ ←scheduleStep i w
  let mut r : RoundState (U 32) :=
    ⟨su[0], su[1], su[2], su[3], su[4], su[5], su[6], su[7]⟩
  for hi:i in [0:64] do
    r ← roundStep i hi (w, r)
  finish (su, r)

theorem structured_eq (m : Vector (Word 32) 16) (s : Vector (Word 32) 8) :
    structured m s = permCircuit m s := by
  unfold structured permCircuit scheduleStep roundStep finish
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
    intro hs1 u hu
    simp only [Array.mem_def, List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact U.valid_getElem! hw (by grind)
    · exact (by assumption : U.Rel ρ u _).1
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
    intro hs1 u hu
    simp only [Array.mem_def, List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact U.valid_getElem! hw (by grind)
    · exact (by assumption : U.Rel ρ u _).1
    · exact U.valid_getElem! hw (by grind)
    · exact hs1.1

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
    (hA : U.Rel ρ newA (r.2.2.2.2.2.2.2.eval ρ + S1.eval ρ +
      (k[i] : U 32).eval ρ + w[i].eval ρ + S0.eval ρ +
      chBV (r.2.2.2.2.1.eval ρ) (r.2.2.2.2.2.1.eval ρ)
        (r.2.2.2.2.2.2.1.eval ρ) +
      majBV (r.1.eval ρ) (r.2.1.eval ρ) (r.2.2.1.eval ρ))) :
    RoundState.Rel ρ
      ⟨newA, r.1, r.2.1, r.2.2.1, newE,
        r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1⟩
      (roundStepBV i wv rv) := by
  have hS1' := hr.e.rotateXor3 (by decide) (by decide) (by decide) hS1
  have hS0' := hr.a.rotateXor3 (by decide) (by decide) (by decide) hS0
  have hwi : w[i].eval ρ = wv[i] := by
    simpa only [Fin.getElem_fin] using (hw ⟨i, by grind⟩).2
  refine ⟨⟨hA.1, hr.a.1, hr.b.1, hr.c.1, hE.1,
    hr.e.1, hr.f.1, hr.g.1⟩, ?_⟩
  unfold RoundState.eval roundStepBV
  simp only [getElem!_pos k i (by grind), getElem!_pos wv i (by grind)]
  rw [hA.2, hr.a.2, hr.b.2, hr.c.2, hE.2, hr.e.2, hr.f.2, hr.g.2,
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
  case vc14.x =>
    exact chBV (r.2.2.2.2.1.eval ρ) (r.2.2.2.2.2.1.eval ρ)
      (r.2.2.2.2.2.2.1.eval ρ)
  case vc15.y => exact majBV (r.1.eval ρ) (r.2.1.eval ρ) (r.2.2.1.eval ρ)
  case vc16.ha => exact hr.h.1
  case vc17.hb => grind [U.Rel]
  case vc18.hc => exact U.valid_bitVec _
  case vc19.hd => exact hwi
  case vc20.he => grind [U.Rel]
  case vc21.hx | vc22.hy => assumption
  case vc23.success =>
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
  case vc14.x =>
    exact chBV (r.2.2.2.2.1.eval ρ) (r.2.2.2.2.2.1.eval ρ)
      (r.2.2.2.2.2.2.1.eval ρ)
  case vc15.y => exact majBV (r.1.eval ρ) (r.2.1.eval ρ) (r.2.2.1.eval ρ)
  case vc16.ha => exact hr.2.2.2.2.2.2.2
  case vc17.hb => grind [U.Rel]
  case vc18.hc => exact U.valid_bitVec _
  case vc19.hd => exact hwi
  case vc20.he => grind [U.Rel]
  case vc21.hx | vc22.hy => assumption
  case vc23.success => grind [RoundState.Valid, U.Rel]

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

def model (m : Vector (BitVec 32) 16) (s : Vector (BitVec 32) 8) :
    Vector (BitVec 32) 8 :=
  finishBV s (roundsBV (scheduleBV m) s)

@[spec] theorem structured_sound {m : Vector (Word 32) 16}
    {s : Vector (Word 32) 8} :
    ⦃⌜True⌝⦄ Sound.interp ρ (structured m s)
    ⦃⇓ out => ⌜Vector.Rel ρ out
      (model (m.map (Word.eval ρ.bool)) (s.map (Word.eval ρ.bool)))⌝⦄ := by
  unfold structured
  rw [Sound.interp_bind]
  apply Triple.bind (Q := fun su =>
    ⌜Vector.Rel ρ su (s.map (Word.eval ρ.bool))⌝)
  case hx => exact U.mapM_fromWord_sound
  case hf =>
    intro su
    mvcgen -trivial invariants
    · ⇓⟨cur, w⟩ => ⌜Vector.Rel ρ w
        (cur.prefix.foldl
          (fun w i => w.set! i ((m[i]!).eval ρ.bool)) default)⌝
    · ⇓⟨cur, w⟩ => ⌜Vector.Rel ρ w
        (cur.prefix.foldl (fun w i => w.set! i (scheduleStepBV i w))
          (initialSchedule (m.map (Word.eval ρ.bool))))⌝
    · ⇓⟨cur, r⟩ => ⌜RoundState.Rel ρ r
        (cur.prefix.foldl
          (fun r i => roundStepBV i (scheduleBV (m.map (Word.eval ρ.bool))) r)
          (initialRound (s.map (Word.eval ρ.bool))))⌝
    case vc1 =>
      rename_i pref cur suff hsplit w hw out hout
      simpa [List.foldl_append, getElem!_pos m cur (by grind)]
        using hw.set! hout cur
    case vc2.h.pre => simpa using (Vector.Rel.default (valuation := ρ) (n := 32) (m := 64))
    case vc3.hw => exact fun i => (by assumption : Vector.Rel ρ _ _) i |>.1
    case vc4.hi =>
      apply Std.Legacy.Range.mem_of_mem_range'
      apply List.mem_of_range'_eq_append_cons
      assumption
    case vc5 =>
      rename_i _ cur _ _ w hw out hout
      rw [Vector.Rel.eval_eq hw] at hout
      simpa [List.foldl_append] using hw.set! hout cur
    case vc6.h.pre =>
      rename_i w hw
      rw [initialSchedule_words] at hw
      simpa only [List.foldl_nil] using hw
    case vc7.hw =>
      exact Vector.Rel.valid (by assumption)
    case vc8.hr =>
      exact (by assumption : RoundState.Rel ρ _ _).1
    case vc9 =>
      rename_i hsu w0 hw0 w hw pref cur suff hsplit b hr out hout
      have hw' : Vector.Rel ρ w
          (scheduleBV (m.map (Word.eval ρ.bool))) := by
        rw [← scheduleBV_eq]
        exact hw
      rw [Vector.Rel.eval_eq hw', RoundState.Rel.eval_eq hr] at hout
      simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using hout
    case vc10.h.pre =>
      simp only [List.foldl_nil]
      have hsu : Vector.Rel ρ su (s.map (Word.eval ρ.bool)) := by assumption
      refine ⟨⟨(hsu 0).1, (hsu 1).1, (hsu 2).1, (hsu 3).1,
        (hsu 4).1, (hsu 5).1, (hsu 6).1, (hsu 7).1⟩, ?_⟩
      rw [initialRound_eval, Vector.Rel.eval_eq hsu]
    case vc11 =>
      exact fun _ => (by assumption : Vector.Rel ρ su _)
    case vc12 =>
      intro h
      rw [roundsBV_eq] at h
      exact h

@[spec] theorem structured_complete {m : Vector (Word 32) 16}
    {s : Vector (Word 32) 8} :
    ⦃⌜True⌝⦄ Complete.interp ρ (structured m s)
    ⦃⇓ out => ⌜∀ i : Fin 8, out[i].Valid ρ⌝⦄ := by
  unfold structured
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun su =>
    ⌜Vector.Rel ρ su (s.map (Word.eval ρ.bool))⌝)
  case hx => exact U.mapM_fromWord_complete
  case hf =>
    intro su
    mvcgen -trivial invariants
    · ⇓⟨_, w⟩ => ⌜∀ j : Fin 64, w[j].Valid ρ⌝
    · ⇓⟨_, w⟩ => ⌜∀ j : Fin 64, w[j].Valid ρ⌝
    · ⇓⟨_, r⟩ => ⌜r.Valid ρ⌝
    case vc1 =>
      exact U.allValid_set! (by assumption) (by grind [U.Rel]) _
    case vc2.h.pre =>
      intro j
      rw [U.vector_default_get]
      exact U.valid_default
    case vc3.hw => assumption
    case vc4.hi =>
      apply Std.Legacy.Range.mem_of_mem_range'
      apply List.mem_of_range'_eq_append_cons
      assumption
    case vc5 =>
      exact U.allValid_set! (by assumption) (by grind [U.Rel]) _
    case vc6.h.pre => assumption
    case vc7.hw => assumption
    case vc8.hr => assumption
    case vc9 => assumption
    case vc10.h.pre =>
      have hsu : ∀ i : Fin 8, su[i].Valid ρ :=
        Vector.Rel.valid (by assumption)
      exact ⟨hsu 0, hsu 1, hsu 2, hsu 3,
        hsu 4, hsu 5, hsu 6, hsu 7⟩
    case vc11 =>
      intro _
      exact Vector.Rel.valid (by assumption)
    case vc12 => exact fun h => h

def RoundState.WFRel : WF.Post (RoundState (U n)) :=
  fun lv rv l r => U.WFRel lv rv l.1 r.1 ∧
    U.WFRel lv rv l.2.1 r.2.1 ∧ U.WFRel lv rv l.2.2.1 r.2.2.1 ∧
    U.WFRel lv rv l.2.2.2.1 r.2.2.2.1 ∧
    U.WFRel lv rv l.2.2.2.2.1 r.2.2.2.2.1 ∧
    U.WFRel lv rv l.2.2.2.2.2.1 r.2.2.2.2.2.1 ∧
    U.WFRel lv rv l.2.2.2.2.2.2.1 r.2.2.2.2.2.2.1 ∧
    U.WFRel lv rv l.2.2.2.2.2.2.2 r.2.2.2.2.2.2.2

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
      apply WF.Rel.mono (U.sumFixed_wf.relHom B
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
              (left := ⟨rL.2.2.2.2.2.2.2, S1L, (k[i] : U 32), wL[i],
                S0L, chL, majL⟩)
              (right := ⟨rR.2.2.2.2.2.2.2, S1R, (k[i] : U 32), wR[i],
                S0R, chR, majR⟩) optimized_sum5Doubled2_wf
            · intro lv rv h
              have hE := hnewE lv rv h
              have hD := hmaj lv rv hE.1
              have hC := hS0 lv rv hD.1
              have hB := hch lv rv hC.1
              have hA := hS1 lv rv hB.1
              have hw := hA.1.1
              have hr := hA.1.2
              exact ⟨hr.2.2.2.2.2.2.2, hA.2, U.wfRel_bitVec _ _ _,
                hw ⟨i, by grind⟩, hC.2, hB.2, hD.2⟩
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
      fin_cases i <;> simp only [Fin.getElem_fin]
      · exact hin.2.1
      · exact hin.2.2.1
      · exact hin.2.2.2.1
      · exact hin.2.2.2.2.1
      · exact hin.2.2.2.2.2.1
      · exact hin.2.2.2.2.2.2.1
      · exact hin.2.2.2.2.2.2.2.1
      · exact hin.2.2.2.2.2.2.2.2

theorem structured_wf :
    WF.GadgetSpec
      (fun lv rv
          (l r : Vector (Word 32) 16 × Vector (Word 32) 8) =>
        WF.VectorRel Word.WFRel lv rv l.1 r.1 ∧
          WF.VectorRel Word.WFRel lv rv l.2 r.2)
      (fun x => structured x.1 x.2) (WF.VectorRel U.WFRel) := by
  unfold WF.GadgetSpec
  intro left right
  unfold structured
  apply WF.GadgetSpec.bind_rule U.mapM_fromWord_wf
  · exact fun lv rv h => h.2
  · intro A sL sR hs
    wfgen' using [U.fromWord_wf_rel, scheduleStep_wf,
      roundStep_wf, finish_wf]
    case inv1 => exact WF.VectorRel U.WFRel
    case vc1 =>
      exact fun lv rv _ => U.vector_default_wfRel lv rv
    case vc2 =>
      intro i hi P wL wR hw
      apply WF.GadgetSpec.bind_rule U.fromWord_wf_rel
      · intro lv rv h
        exact (hs lv rv (hw lv rv h).1).1.1 ⟨i, by grind⟩
      · intro B outL outR hout
        apply WF.Rel.pure
        intro lv rv hB
        have ho := hout lv rv hB
        have hin := hw lv rv ho.1
        exact ⟨ho.1, hin.1, WF.VectorRel.set! hin.2 ho.2 i⟩
    case vc3 =>
      intro B wL wR hw
      apply WF.Rel.forIn'_range_map_yield_bind_rule
        (I := WF.VectorRel U.WFRel)
        (fL := fun i _ w => scheduleStep i w)
        (fR := fun i _ w => scheduleStep i w)
        (nextL := fun i _ w out => w.set! i out)
        (nextR := fun i _ w out => w.set! i out)
      case hinit => exact fun lv rv h => (hw lv rv h).2
      case hstep =>
        intro i hi P left right hP
        apply WF.GadgetSpec.bind_rule (scheduleStep_wf i hi)
        · exact fun lv rv h => (hP lv rv h).2
        · intro C outL outR hout
          apply WF.Rel.pure
          intro lv rv hC
          have ho := hout lv rv hC
          have hin := hP lv rv ho.1
          exact ⟨ho.1, hin.1, WF.VectorRel.set! hin.2 ho.2 i⟩
      case hcont =>
        intro C wL wR hschedule
        apply WF.Rel.forIn'_range_map_yield_bind_rule
          (I := RoundState.WFRel)
          (fL := fun i hi r => roundStep i hi (wL, r))
          (fR := fun i hi r => roundStep i hi (wR, r))
          (nextL := fun _ _ _ out => out)
          (nextR := fun _ _ _ out => out)
        case hinit =>
          intro lv rv hC
          have h0 := hschedule lv rv hC
          have h1 := hw lv rv h0.1
          exact RoundState.WFRel.ofVector (hs lv rv h1.1).2
        case hstep =>
          intro i hi P rL rR hP
          have hstep := (roundStep_wf i hi).relHom P
            ⟨wL, rL⟩ ⟨wR, rR⟩ (by
              intro lv rv h
              have hp := hP lv rv h
              exact ⟨(hschedule lv rv hp.1).2, hp.2⟩)
          apply WF.Rel.mono hstep
          exact fun lv rv _ _ hout =>
            ⟨hout.1, (hP lv rv hout.1).1, hout.2⟩
        case hcont =>
          intro D rL rR hr
          apply WF.Rel.mono (finish_wf.relHom D
            ⟨sL, rL⟩ ⟨sR, rR⟩ (by
              intro lv rv hD
              have hround := hr lv rv hD
              have h0 := hschedule lv rv hround.1
              have h1 := hw lv rv h0.1
              exact ⟨( hs lv rv h1.1).2, hround.2⟩))
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
