import Freigen.F2Z.Examples.EcdsaP256.Lemmas
import Freigen.F2Z.Examples.EcdsaP256.Radix32Impl
import Freigen.F2Z.Examples.P256.IncompleteLemmas

/-!
# Signed radix-32 ECDSA-P256 lemmas

The experimental radix-32 verifier proofs live in this module so proof
iterations do not repeatedly elaborate the much larger legacy lemma file.
-/

namespace Freigen.F2Z.Examples.EcdsaP256

open Std.Do
open scoped Std.Do
open BigOperators
open Modular
open P256
open P256.Projective

set_option maxRecDepth 10000

def Radix32TableSpec (rho : WF.Valuation) (table : Radix32Table)
    (q : P256.Reference.Point) : Prop :=
  (∀ i : Fin 16,
    P256.Reference.NormalizedRep rho table.low[i] (i.val • q)) ∧
  P256.Reference.NormalizedRep rho table.p16 (16 • q)

def Radix32TableValid (rho : WF.Valuation) (table : Radix32Table) : Prop :=
  (∀ i : Fin 16, table.low[i].Valid rho) ∧ table.p16.Valid rho

private theorem table_nsmul_ne_zero {q : P256.Reference.Point}
    (hq : q ≠ 0) (horder : P256.scalarModulus • q = 0)
    {k : Nat} (hk0 : k ≠ 0) (hk : k < P256.scalarModulus) :
    k • q ≠ 0 := by
  intro hzero
  have hdvd : P256.scalarModulus ∣ k := by
    rw [← Reference.Aux.addOrderOf_eq_scalarModulus hq horder,
      addOrderOf_dvd_iff_nsmul_eq_zero]
    exact hzero
  exact (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk0) hk) hdvd

private theorem table_multiple_ne_self {q : P256.Reference.Point}
    (hq : q ≠ 0) (horder : P256.scalarModulus • q = 0)
    {k : Nat} (hk : 1 < k) (hklt : k - 1 < P256.scalarModulus) :
    k • q ≠ q := by
  intro heq
  have hsplit : k = (k - 1) + 1 := by omega
  rw [hsplit, add_nsmul, one_nsmul] at heq
  have hcancel : (k - 1) • q + q = 0 + q := by simpa using heq
  have hz : (k - 1) • q = 0 := add_right_cancel hcancel
  exact table_nsmul_ne_zero hq horder (by omega) hklt hz

private theorem table_multiple_ne_neg {q : P256.Reference.Point}
    (hq : q ≠ 0) (horder : P256.scalarModulus • q = 0)
    {k : Nat} (hklt : k + 1 < P256.scalarModulus) :
    k • q ≠ -q := by
  intro heq
  have hz : (k + 1) • q = 0 := by
    rw [add_nsmul, one_nsmul, heq, neg_add_cancel]
  exact table_nsmul_ne_zero hq horder (by omega) hklt hz

private theorem table_chord_safe {q : P256.Reference.Point}
    (hq : q ≠ 0) (horder : P256.scalarModulus • q = 0)
    {k : Nat} (hk : 1 < k) (hklt : k + 1 < P256.scalarModulus) :
    k • q ≠ 0 ∧ q ≠ 0 ∧ k • q ≠ q ∧ k • q ≠ -q := by
  exact ⟨table_nsmul_ne_zero hq horder (by omega) (by omega), hq,
    table_multiple_ne_self hq horder hk (by omega),
    table_multiple_ne_neg hq horder hklt⟩

@[spec] theorem addRadix32Multiple_sound
    {P Q : P256.AffineSlope.Point} {q : P256.Reference.Point} {k : Nat}
    (hP : P256.Reference.NormalizedRep ρ P (k • q))
    (hQ : P256.Reference.NormalizedRep ρ Q q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (addRadix32Multiple k P Q)
    ⦃⇓ out => ⌜P256.Reference.NormalizedRep ρ out ((k + 1) • q)⌝⦄ := by
  unfold addRadix32Multiple
  apply Triple.iff_conseq.mp
    (P256.AffineSlope.addIncompleteChecked_sound_mathlib hP.1 hQ.1) (by simp)
  simp only [PostCond.entails, SPred.entails_nil]
  exact ⟨fun _ h => by simpa only [add_nsmul, one_nsmul] using h,
    ExceptConds.entails.refl _⟩

@[spec] theorem addRadix32Multiple_complete
    {P Q : P256.AffineSlope.Point} {q : P256.Reference.Point} {k : Nat}
    (hPvalid : P.Valid ρ) (hQvalid : Q.Valid ρ)
    (hP : P256.Reference.NormalizedRep ρ P (k • q))
    (hQ : P256.Reference.NormalizedRep ρ Q q)
    (hq : q ≠ 0) (horder : P256.scalarModulus • q = 0)
    (hk : 1 < k) (hklt : k + 1 < P256.scalarModulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ (addRadix32Multiple k P Q)
    ⦃⇓ out => ⌜out.Valid ρ ∧ P256.Reference.NormalizedRep ρ out
      ((k + 1) • q)⌝⦄ := by
  rcases table_chord_safe hq horder hk hklt with ⟨hP0, hq0, hne, hneNeg⟩
  unfold addRadix32Multiple
  apply Triple.iff_conseq.mp
    (P256.AffineSlope.addIncompleteChecked_complete_mathlib
      hPvalid hQvalid hP hQ hP0 hq0 hne hneNeg) (by simp)
  simp only [PostCond.entails, SPred.entails_nil]
  exact ⟨fun _ h => ⟨h.1, by
      simpa only [add_nsmul, one_nsmul] using h.2⟩,
    ExceptConds.entails.refl _⟩

@[spec] theorem materializeRadix32Multiples_sound {P : P256.Projective}
    {q : P256.Reference.Point}
    (hP : P256.Reference.Represents ρ
      (P256.AffineSlope.ofElems P.X P.Y) q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (materializeRadix32Multiples P)
    ⦃⇓ table => ⌜Radix32TableSpec ρ table q⌝⦄ := by
  have hP' : P256.Reference.NormalizedRep ρ
      (P256.AffineSlope.ofElems P.X P.Y) q := by
    refine ⟨hP, ?_⟩
    intro hq
    have hinf := P256.Reference.Aux.represents_zero (hq ▸ hP)
    simp [P256.AffineSlope.ofElems] at hinf
  mvcgen [addRadix32Multiple_sound, materializeRadix32Multiples,
    Radix32TableSpec]
  case vc38.success =>
    rename_i p2 hp2 p3 hp3 p4 hp4 p5 hp5 p6 hp6 p7 hp7 p8 hp8
      p9 hp9 p10 hp10 p11 hp11 p12 hp12 p13 hp13 p14 hp14 p15 hp15
      p16 hp16
    constructor
    · intro i
      fin_cases i
      · simp [P256.AffineSlope.infinity,
          P256.Reference.NormalizedRep, P256.Reference.Represents,
          P256.Reference.circuitCoordinates, P256.Reference.coordinates]
      · simpa using hP'
      · simpa using hp2
      · simpa using hp3
      · simpa using hp4
      · simpa using hp5
      · simpa using hp6
      · simpa using hp7
      · simpa using hp8
      · simpa using hp9
      · simpa using hp10
      · simpa using hp11
      · simpa using hp12
      · simpa using hp13
      · simpa using hp14
      · simpa using hp15
    · simpa using hp16

set_option maxHeartbeats 1000000 in
@[spec] theorem materializeRadix32Multiples_complete {P : P256.Projective}
    {q : P256.Reference.Point}
    (hPvalid : P.Valid ρ)
    (hP : P256.Reference.Represents ρ
      (P256.AffineSlope.ofElems P.X P.Y) q)
    (horder : P256.scalarModulus • q = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (materializeRadix32Multiples P)
    ⦃⇓ table => ⌜Radix32TableValid ρ table ∧
      Radix32TableSpec ρ table q⌝⦄ := by
  have hP' : P256.Reference.NormalizedRep ρ
      (P256.AffineSlope.ofElems P.X P.Y) q := by
    refine ⟨hP, ?_⟩
    intro hq
    have hinf := P256.Reference.Aux.represents_zero (hq ▸ hP)
    simp [P256.AffineSlope.ofElems] at hinf
  have hq : q ≠ 0 := by
    intro hzero
    have hinf := P256.Reference.Aux.represents_zero (hzero ▸ hP)
    simp [P256.AffineSlope.ofElems] at hinf
  have hPvalid' := ofElems_valid hPvalid
  have hInfinityValid : P256.AffineSlope.infinity.Valid ρ := by
    have hz : P256.zero.Valid ρ :=
      Modular.ofNat_valid P256.base 0 (by native_decide) (by native_decide)
    exact ⟨rfl, Modular.Lazy.ofElem_valid P256.base hz, hz.2,
      rfl, Modular.Lazy.ofElem_valid P256.base hz, hz.2,
      by simp [P256.AffineSlope.infinity]⟩
  mvcgen [addRadix32Multiple_complete, doubleMultiple_complete,
    materializeRadix32Multiples, Radix32TableValid, Radix32TableSpec]
  all_goals first
    | exact q
    | exact horder
    | exact hq
    | exact hPvalid'
    | exact hP'
    | exact hInfinityValid
    | omega
    | (apply And.left <;> assumption)
    | (apply And.right <;> assumption)
    | skip
  case vc96.success =>
    rename_i p2 hp2 p3 hp3 p4 hp4 p5 hp5 p6 hp6 p7 hp7 p8 hp8
      p9 hp9 p10 hp10 p11 hp11 p12 hp12 p13 hp13 p14 hp14 p15 hp15
      p16 hp16
    constructor
    · constructor
      · intro i
        fin_cases i
        · exact hInfinityValid
        · exact hPvalid'
        · exact hp2.1
        · exact hp3.1
        · exact hp4.1
        · exact hp5.1
        · exact hp6.1
        · exact hp7.1
        · exact hp8.1
        · exact hp9.1
        · exact hp10.1
        · exact hp11.1
        · exact hp12.1
        · exact hp13.1
        · exact hp14.1
        · exact hp15.1
      · exact hp16.1
    · constructor
      · intro i
        fin_cases i
        · simp [P256.AffineSlope.infinity,
            P256.Reference.NormalizedRep, P256.Reference.Represents,
            P256.Reference.circuitCoordinates, P256.Reference.coordinates]
        · simpa using hP'
        · simpa using hp2.2
        · simpa using hp3.2
        · simpa using hp4.2
        · simpa using hp5.2
        · simpa using hp6.2
        · simpa using hp7.2
        · simpa using hp8.2
        · simpa using hp9.2
        · simpa using hp10.2
        · simpa using hp11.2
        · simpa using hp12.2
        · simpa using hp13.2
        · simpa using hp14.2
        · simpa using hp15.2
      · simpa using hp16.2

def SignedDigitSpec (rho : WF.Valuation) (value : LC ℤ)
    (digit : SignedDigit) : Prop :=
  digit.oneHot.Valid rho ∧ ∃ slot : Fin 33,
    digit.oneHot.intBits[slot].eval rho.int = 1 ∧
    value.eval rho.int = (slot.val : Int) - 16 ∧
    ∀ other : Fin 33,
      digit.oneHot.intBits[other].eval rho.int = 1 → other = slot

private theorem SignedDigitSpec.bit_zero_or_one
    (h : SignedDigitSpec ρ value digit) (slot : Fin 33) :
    digit.oneHot.intBits[slot].eval ρ.int = 0 ∨
      digit.oneHot.intBits[slot].eval ρ.int = 1 := by
  have hbit := h.1 slot
  cases hb : digit.oneHot.bits.bitsLE[slot].eval ρ.bool <;>
    rw [hb] at hbit <;> simp at hbit
  · exact Or.inl hbit
  · exact Or.inr hbit

private theorem SignedDigitSpec.bit_zero_of_ne
    (h : SignedDigitSpec ρ value digit) {chosen other : Fin 33}
    (hchosen : digit.oneHot.intBits[chosen].eval ρ.int = 1)
    (hunique : ∀ j : Fin 33,
      digit.oneHot.intBits[j].eval ρ.int = 1 → j = chosen)
    (hne : other ≠ chosen) :
    digit.oneHot.intBits[other].eval ρ.int = 0 := by
  rcases h.bit_zero_or_one other with hzero | hone
  · exact hzero
  · exact (hne (hunique other hone)).elim

private theorem SignedDigitSpec.weighted_eval
    (h : SignedDigitSpec ρ value digit) (f : Fin 33 → Int)
    {chosen : Fin 33}
    (hchosen : digit.oneHot.intBits[chosen].eval ρ.int = 1)
    (hunique : ∀ j : Fin 33,
      digit.oneHot.intBits[j].eval ρ.int = 1 → j = chosen) :
    (∑ slot : Fin 33, f slot • digit.oneHot.intBits[slot]).eval ρ.int =
      f chosen := by
  rw [LC.eval_sum]
  simp only [LC.eval_smul]
  apply Aux.sum_mul_oneHot
  · exact hchosen
  · intro other hne
    exact h.bit_zero_of_ne hchosen hunique hne

theorem SignedDigitSpec.value_eval (h : SignedDigitSpec ρ value digit) :
    digit.value.eval ρ.int = value.eval ρ.int := by
  rcases h.2 with ⟨chosen, hchosen, hvalue, hunique⟩
  unfold SignedDigit.value
  rw [h.weighted_eval (fun slot => (slot.val : Int) - 16)
    hchosen hunique, hvalue]

theorem SignedDigitSpec.magnitude_eval
    (h : SignedDigitSpec ρ value digit) :
    digit.magnitude.eval ρ.int = (value.eval ρ.int).natAbs := by
  rcases h.2 with ⟨chosen, hchosen, hvalue, hunique⟩
  unfold SignedDigit.magnitude
  rw [LC.eval_sum]
  simp only [LC.eval_nsmul, nsmul_eq_mul]
  rw [Aux.sum_mul_oneHot
    (fun slot : Fin 33 => (Int.natAbs ((slot.val : Int) - 16) : Int))
    (fun slot => digit.oneHot.intBits[slot].eval ρ.int) chosen hchosen]
  · rw [hvalue]
  · intro other hne
    exact h.bit_zero_of_ne hchosen hunique hne

theorem SignedDigitSpec.negative_eval
    (h : SignedDigitSpec ρ value digit) :
    digit.negative.eval ρ.int = if value.eval ρ.int < 0 then 1 else 0 := by
  rcases h.2 with ⟨chosen, hchosen, hvalue, hunique⟩
  unfold SignedDigit.negative
  rw [h.weighted_eval
    (fun slot => if slot.val < 16 then (1 : Int) else 0)
    hchosen hunique]
  split <;> split <;> simp_all <;> omega

theorem SignedDigitSpec.isSixteen_eval
    (h : SignedDigitSpec ρ value digit) :
    digit.isSixteen.eval ρ.int =
      if value.eval ρ.int = -16 ∨ value.eval ρ.int = 16 then 1 else 0 := by
  rcases h.2 with ⟨chosen, hchosen, hvalue, hunique⟩
  unfold SignedDigit.isSixteen
  rw [h.weighted_eval
    (fun slot => if slot.val = 0 ∨ slot.val = 32 then (1 : Int) else 0)
    hchosen hunique]
  split <;> split <;> simp_all <;> omega

theorem SignedDigitSpec.bounds (h : SignedDigitSpec ρ value digit) :
    -16 ≤ value.eval ρ.int ∧ value.eval ρ.int ≤ 16 := by
  rcases h.2 with ⟨chosen, _, hvalue, _⟩
  have hchosen : chosen.val < 33 := chosen.isLt
  omega

theorem SignedDigitSpec.magnitude_nonneg
    (h : SignedDigitSpec ρ value digit) :
    0 ≤ digit.magnitude.eval ρ.int := by
  rw [h.magnitude_eval]
  exact_mod_cast Nat.zero_le _

private theorem natAbs_cast_eq_neg_of_nonpos {x : Int} (hx : x ≤ 0) :
    (x.natAbs : Int) = -x := by
  have h := Int.natAbs_of_nonneg (a := -x) (by omega)
  simpa only [Int.natAbs_neg] using h

theorem SignedDigitSpec.magnitude_le_sixteen
    (h : SignedDigitSpec ρ value digit) :
    digit.magnitude.eval ρ.int ≤ 16 := by
  rw [h.magnitude_eval]
  rcases h.bounds with ⟨hlow, hhigh⟩
  by_cases hnonneg : 0 ≤ value.eval ρ.int
  · rw [Int.natAbs_of_nonneg hnonneg]
    exact_mod_cast hhigh
  · have hnonpos : value.eval ρ.int ≤ 0 := le_of_lt (lt_of_not_ge hnonneg)
    rw [natAbs_cast_eq_neg_of_nonpos hnonpos]
    omega

theorem SignedDigitSpec.isSixteen_eq_one_iff
    (h : SignedDigitSpec ρ value digit) :
    digit.isSixteen.eval ρ.int = 1 ↔
      digit.magnitude.eval ρ.int = 16 := by
  rw [h.isSixteen_eval, h.magnitude_eval]
  rcases h.bounds with ⟨hlow, hhigh⟩
  by_cases hsixteen : value.eval ρ.int = -16 ∨ value.eval ρ.int = 16
  · simp only [if_pos hsixteen, true_iff]
    rcases hsixteen with hneg | hpos
    · rw [hneg]
      decide
    · rw [hpos]
      decide
  · simp only [if_neg hsixteen, false_iff, ne_eq]
    by_cases hnonneg : 0 ≤ value.eval ρ.int
    · rw [Int.natAbs_of_nonneg hnonneg]
      omega
    · have hnonpos : value.eval ρ.int ≤ 0 := le_of_lt (lt_of_not_ge hnonneg)
      rw [natAbs_cast_eq_neg_of_nonpos hnonpos]
      omega

theorem SignedDigitSpec.isSixteen_bit
    (h : SignedDigitSpec ρ value digit) :
    digit.isSixteen.eval ρ.int = 0 ∨ digit.isSixteen.eval ρ.int = 1 := by
  rw [h.isSixteen_eval]
  split <;> simp

theorem SignedDigitSpec.lowMagnitude_bounds
    (h : SignedDigitSpec ρ value digit) :
    let lowMagnitude := digit.magnitude - 16 • digit.isSixteen
    0 ≤ lowMagnitude.eval ρ.int ∧ lowMagnitude.eval ρ.int < 16 := by
  dsimp
  simp only [LC.eval_sub, LC.eval_nsmul, nsmul_eq_mul]
  have hm0 := h.magnitude_nonneg
  have hm16 := h.magnitude_le_sixteen
  have hs := h.isSixteen_eval
  by_cases hsixteen : value.eval ρ.int = -16 ∨ value.eval ρ.int = 16
  · rw [if_pos hsixteen] at hs
    have hm : digit.magnitude.eval ρ.int = 16 :=
      h.isSixteen_eq_one_iff.mp hs
    omega
  · rw [if_neg hsixteen] at hs
    have hmne : digit.magnitude.eval ρ.int ≠ 16 := by
      intro hm
      have hsone : digit.isSixteen.eval ρ.int = 1 :=
        h.isSixteen_eq_one_iff.mpr hm
      omega
    omega

private theorem SignedDigitSpec.magnitude_eq_zero_of_center
    (h : SignedDigitSpec ρ value digit)
    (hcenter : digit.oneHot.intBits[16].eval ρ.int = 1) :
    digit.magnitude.eval ρ.int = 0 := by
  rcases h.2 with ⟨chosen, hchosen, hvalue, hunique⟩
  have hchosenCenter : chosen = (16 : Fin 33) :=
    (hunique 16 hcenter).symm
  rw [h.magnitude_eval, hvalue, hchosenCenter]
  decide

private theorem SignedDigitSpec.magnitude_eq_succ_of_gate
    (h : SignedDigitSpec ρ value digit) (i : Nat) (hi : i < 16)
    (hgate : (signedNonzeroMagnitudeGate digit i hi).eval ρ.int = 1) :
    digit.magnitude.eval ρ.int = i + 1 := by
  rcases h.2 with ⟨chosen, hchosen, hvalue, hunique⟩
  let negativeSlot : Fin 33 := ⟨15 - i, by omega⟩
  let positiveSlot : Fin 33 := ⟨17 + i, by omega⟩
  have hnegative := h.bit_zero_or_one negativeSlot
  have hpositive := h.bit_zero_or_one positiveSlot
  have hsum : digit.oneHot.intBits[negativeSlot].eval ρ.int +
      digit.oneHot.intBits[positiveSlot].eval ρ.int = 1 := by
    simpa [signedNonzeroMagnitudeGate, negativeSlot, positiveSlot,
      LC.eval_add] using hgate
  rcases hnegative with hnegative | hnegative <;>
      rcases hpositive with hpositive | hpositive
  · omega

  · have hchosenPositive : chosen = positiveSlot :=
      (hunique positiveSlot hpositive).symm
    rw [h.magnitude_eval, hvalue, hchosenPositive]
    simp only [positiveSlot]
    have : ((17 + i : Nat) : Int) - 16 = (i + 1 : Nat) := by omega
    rw [this]
    exact Int.natAbs_of_nonneg (by omega)
  · have hchosenNegative : chosen = negativeSlot :=
      (hunique negativeSlot hnegative).symm
    rw [h.magnitude_eval, hvalue, hchosenNegative]
    simp only [negativeSlot]
    have : (((15 - i : Nat) : Int) - 16) = -((i + 1 : Nat) : Int) := by
      omega
    rw [this, Int.natAbs_neg, Int.natAbs_of_nonneg (by omega)]
    norm_num
  · omega

private theorem SignedDigitSpec.nonzeroMagnitudeGate_bit
    (h : SignedDigitSpec ρ value digit) (i : Nat) (hi : i < 16) :
    (signedNonzeroMagnitudeGate digit i hi).eval ρ.int = 0 ∨
      (signedNonzeroMagnitudeGate digit i hi).eval ρ.int = 1 := by
  let negativeSlot : Fin 33 := ⟨15 - i, by omega⟩
  let positiveSlot : Fin 33 := ⟨17 + i, by omega⟩
  rcases h.bit_zero_or_one negativeSlot with hnegative | hnegative <;>
      rcases h.bit_zero_or_one positiveSlot with hpositive | hpositive
  · left
    have hn : digit.oneHot.intBits[15 - i].eval ρ.int = 0 := by
      simpa [negativeSlot] using hnegative
    have hp : digit.oneHot.intBits[17 + i].eval ρ.int = 0 := by
      simpa [positiveSlot] using hpositive
    simp [signedNonzeroMagnitudeGate, LC.eval_add, hn, hp]
  · right
    have hn : digit.oneHot.intBits[15 - i].eval ρ.int = 0 := by
      simpa [negativeSlot] using hnegative
    have hp : digit.oneHot.intBits[17 + i].eval ρ.int = 1 := by
      simpa [positiveSlot] using hpositive
    simp [signedNonzeroMagnitudeGate, LC.eval_add, hn, hp]
  · right
    have hn : digit.oneHot.intBits[15 - i].eval ρ.int = 1 := by
      simpa [negativeSlot] using hnegative
    have hp : digit.oneHot.intBits[17 + i].eval ρ.int = 0 := by
      simpa [positiveSlot] using hpositive
    simp [signedNonzeroMagnitudeGate, LC.eval_add, hn, hp]
  · have hne : negativeSlot ≠ positiveSlot := by
      intro heq
      have := congrArg Fin.val heq
      dsimp [negativeSlot, positiveSlot] at this
      omega
    exact (hne ((h.2.choose_spec.2.2 negativeSlot hnegative).trans
      (h.2.choose_spec.2.2 positiveSlot hpositive).symm)).elim

private theorem SignedDigitSpec.center_eq_one_of_magnitude_zero
    (h : SignedDigitSpec ρ value digit)
    (hm : digit.magnitude.eval ρ.int = 0) :
    digit.oneHot.intBits[16].eval ρ.int = 1 := by
  rcases h.2 with ⟨chosen, hchosen, hvalue, hunique⟩
  have habsInt : ((value.eval ρ.int).natAbs : Int) = 0 :=
    h.magnitude_eval.symm.trans hm
  have habs : (value.eval ρ.int).natAbs = 0 := by
    exact_mod_cast habsInt
  have hv : value.eval ρ.int = 0 := Int.natAbs_eq_zero.mp habs
  have hc : chosen = (16 : Fin 33) := by
    apply Fin.eq_of_val_eq
    omega
  simpa [hc] using hchosen

private theorem SignedDigitSpec.gate_eq_one_of_magnitude_succ
    (h : SignedDigitSpec ρ value digit) (i : Nat) (hi : i < 16)
    (hm : digit.magnitude.eval ρ.int = i + 1) :
    (signedNonzeroMagnitudeGate digit i hi).eval ρ.int = 1 := by
  rcases h.2 with ⟨chosen, hchosen, hvalue, hunique⟩
  have habsInt : ((value.eval ρ.int).natAbs : Int) = i + 1 :=
    h.magnitude_eval.symm.trans hm
  by_cases hv : 0 ≤ value.eval ρ.int
  · rw [Int.natAbs_of_nonneg hv] at habsInt
    have hc : chosen.val = 17 + i := by omega
    have hpos : digit.oneHot.intBits[17 + i].eval ρ.int = 1 := by
      simpa [show chosen = ⟨17 + i, by omega⟩ from Fin.eq_of_val_eq hc]
        using hchosen
    have hneg : digit.oneHot.intBits[15 - i].eval ρ.int = 0 := by
      change digit.oneHot.intBits[(⟨15 - i, by omega⟩ : Fin 33)].eval ρ.int = 0
      apply h.bit_zero_of_ne hchosen hunique
      intro heq
      have heqVal := congrArg Fin.val heq
      simp only at heqVal
      omega
    simp [signedNonzeroMagnitudeGate, LC.eval_add, hneg, hpos]
  · have hv' : value.eval ρ.int ≤ 0 := le_of_lt (lt_of_not_ge hv)
    rw [natAbs_cast_eq_neg_of_nonpos hv'] at habsInt
    have hc : chosen.val = 15 - i := by omega
    have hneg : digit.oneHot.intBits[15 - i].eval ρ.int = 1 := by
      simpa [show chosen = ⟨15 - i, by omega⟩ from Fin.eq_of_val_eq hc]
        using hchosen
    have hpos : digit.oneHot.intBits[17 + i].eval ρ.int = 0 := by
      change digit.oneHot.intBits[(⟨17 + i, by omega⟩ : Fin 33)].eval ρ.int = 0
      apply h.bit_zero_of_ne hchosen hunique
      intro heq
      have heqVal := congrArg Fin.val heq
      simp only at heqVal
      omega
    simp [signedNonzeroMagnitudeGate, LC.eval_add, hneg, hpos]

def SignedMagnitudeChoiceSpec (ρ : WF.Valuation) (digit : SignedDigit) : Prop :=
  (digit.oneHot.intBits[16].eval ρ.int = 1 ∧
    digit.magnitude.eval ρ.int = 0) ∨
  ∃ i : Fin 16,
    (signedNonzeroMagnitudeGate digit i.val i.isLt).eval ρ.int = 1 ∧
      digit.magnitude.eval ρ.int = i.val + 1

private theorem SignedDigitSpec.magnitude_choice
    (h : SignedDigitSpec ρ value digit) :
    SignedMagnitudeChoiceSpec ρ digit := by
  rcases h.2 with ⟨chosen, hchosen, hvalue, hunique⟩
  by_cases hcenter : chosen.val = 16
  · left
    have hc : chosen = (16 : Fin 33) := Fin.eq_of_val_eq hcenter
    have hone : digit.oneHot.intBits[16].eval ρ.int = 1 := by
      simpa [hc] using hchosen
    exact ⟨hone, h.magnitude_eq_zero_of_center hone⟩
  · right
    by_cases hnegative : chosen.val < 16
    · let i : Fin 16 := ⟨15 - chosen.val, by omega⟩
      have hm : digit.magnitude.eval ρ.int = i.val + 1 := by
        rw [h.magnitude_eval, hvalue]
        have hv : (chosen.val : Int) - 16 = -((i.val + 1 : Nat) : Int) := by
          dsimp [i]
          omega
        rw [hv, Int.natAbs_neg, Int.natAbs_of_nonneg (by omega)]
        norm_num
      exact ⟨i, h.gate_eq_one_of_magnitude_succ i.val i.isLt hm, hm⟩
    · have hpositive : 16 < chosen.val := by omega
      let i : Fin 16 := ⟨chosen.val - 17, by omega⟩
      have hm : digit.magnitude.eval ρ.int = i.val + 1 := by
        rw [h.magnitude_eval, hvalue]
        have hv : (chosen.val : Int) - 16 = (i.val + 1 : Nat) := by
          dsimp [i]
          omega
        rw [hv, Int.natAbs_of_nonneg (by omega)]
        norm_num
      exact ⟨i, h.gate_eq_one_of_magnitude_succ i.val i.isLt hm, hm⟩
def Radix32MagnitudeSpec (ρ : WF.Valuation) (value : LC ℤ)
    (out : P256.AffineSlope.Point) (q : P256.Reference.Point) : Prop :=
  P256.Reference.NormalizedRep ρ out ((value.eval ρ.int).natAbs • q)

def SignedMagnitudeLookupRepSpec (ρ : WF.Valuation) (digit : SignedDigit)
    (values : Vector P256.AffineSlope.Rep 17)
    (out : P256.AffineSlope.Rep) : Prop :=
  (digit.oneHot.intBits[16].eval ρ.int = 1 →
    Modular.Lazy.evalZMod P256.base out ρ =
      Modular.Lazy.evalZMod P256.base values[0] ρ) ∧
  ∀ i : Fin 16,
    (signedNonzeroMagnitudeGate digit i.val i.isLt).eval ρ.int = 1 →
      Modular.Lazy.evalZMod P256.base out ρ =
        Modular.Lazy.evalZMod P256.base
          (values[i.val + 1]'(by omega)) ρ

def SignedMagnitudeLookupFlagSpec (ρ : WF.Valuation) (digit : SignedDigit)
    (values : Vector (LC ℤ) 17) (out : LC ℤ) : Prop :=
  (digit.oneHot.intBits[16].eval ρ.int = 1 →
    out.eval ρ.int = values[0].eval ρ.int) ∧
  ∀ i : Fin 16,
    (signedNonzeroMagnitudeGate digit i.val i.isLt).eval ρ.int = 1 →
      out.eval ρ.int = (values[i.val + 1]'(by omega)).eval ρ.int

@[spec] theorem lookupSignedMagnitudeRep_sound
    {digit : SignedDigit} {values : Vector P256.AffineSlope.Rep 17} :
    ⦃⌜True⌝⦄ Sound.interp ρ (lookupSignedMagnitudeRep digit values)
    ⦃⇓ out => ⌜SignedMagnitudeLookupRepSpec ρ digit values out⌝⦄ := by
  mvcgen [lookupSignedMagnitudeRep]
  intro bits
  mvcgen
  rename_i word hword hzero
  mvcgen [WF.foldRange] invariants
  · ⇓⟨cur, _⟩ => ⌜∀ i : Fin 16, i.val < cur.prefix.length →
      (signedNonzeroMagnitudeGate digit i.val i.isLt).eval ρ.int = 1 →
      Modular.Lazy.evalZMod P256.base ⟨word.intVal, 2⟩ ρ =
        Modular.Lazy.evalZMod P256.base
          (values[i.val + 1]'(by omega)) ρ⌝
  case vc1 pref cur suff hsplit _ hprev hassert =>
    intro i hi hone
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i.val < pref.length
    · exact hprev i hlt hone
    · have hieq : i.val = cur := by
        have hcur : cur = pref.length := by grind
        omega
      subst cur
      rcases hassert with ⟨_, hassert⟩
      simp only [LC.eval_sub, LC.eval_zero] at hassert
      rw [show (signedNonzeroMagnitudeGate digit i.val i.isLt).eval
          ρ.int = 1 by simpa using hone, one_mul] at hassert
      have houtEq : word.intVal.eval ρ.int =
          (values[i.val + 1]'(by omega)).intVal.eval ρ.int := by
        simpa only [Fin.getElem_fin] using sub_eq_zero.mp hassert
      unfold Modular.Lazy.evalZMod
      rw [houtEq]
  case vc2 => simp
  case vc3 hloop =>
    constructor
    · intro hcenter
      simp only [LC.eval_sub, LC.eval_zero, hcenter, one_mul] at hzero
      unfold Modular.Lazy.evalZMod
      rw [sub_eq_zero.mp hzero]
    · simpa using hloop

@[spec] theorem lookupSignedMagnitudeFlag_sound
    {digit : SignedDigit} {values : Vector (LC ℤ) 17} :
    ⦃⌜True⌝⦄ Sound.interp ρ (lookupSignedMagnitudeFlag digit values)
    ⦃⇓ out => ⌜SignedMagnitudeLookupFlagSpec ρ digit values out⌝⦄ := by
  mvcgen [lookupSignedMagnitudeFlag]
  intro bits
  mvcgen
  rename_i out hout hzero
  mvcgen [WF.foldRange] invariants
  · ⇓⟨cur, _⟩ => ⌜∀ i : Fin 16, i.val < cur.prefix.length →
      (signedNonzeroMagnitudeGate digit i.val i.isLt).eval ρ.int = 1 →
      out.eval ρ.int = (values[i.val + 1]'(by omega)).eval ρ.int⌝
  case vc1 pref cur suff hsplit _ hprev hassert =>
    intro i hi hone
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i.val < pref.length
    · exact hprev i hlt hone
    · have hieq : i.val = cur := by
        have hcur : cur = pref.length := by grind
        omega
      subst cur
      rcases hassert with ⟨_, hassert⟩
      simp only [LC.eval_sub, LC.eval_zero] at hassert
      rw [show (signedNonzeroMagnitudeGate digit i.val i.isLt).eval
          ρ.int = 1 by simpa using hone, one_mul] at hassert
      simpa only [Fin.getElem_fin] using sub_eq_zero.mp hassert
  case vc2 => simp
  case vc3 hloop =>
    constructor
    · intro hcenter
      simp only [LC.eval_sub, LC.eval_zero, hcenter, one_mul] at hzero
      exact sub_eq_zero.mp hzero
    · simpa using hloop

@[spec] theorem lookupSignedMagnitudeRep_complete
    {digit : SignedDigit} {values : Vector P256.AffineSlope.Rep 17}
    (hdigit : SignedDigitSpec ρ value digit)
    (hvalues : ∀ i : Fin 17, values[i].Valid ρ ∧
      values[i].intVal.eval ρ.int < P256.base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ (lookupSignedMagnitudeRep digit values)
    ⦃⇓ out => ⌜SignedMagnitudeLookupRepSpec ρ digit values out ∧
      out.Valid ρ ∧ out.intVal.eval ρ.int < P256.base.modulus ∧
      out.bound = 2⌝⦄ := by
  mvcgen [lookupSignedMagnitudeRep]
  let chosen : Fin 17 := ⟨(digit.magnitude.eval ρ.int).toNat,
    (Int.toNat_lt hdigit.magnitude_nonneg).2
      (lt_of_le_of_lt hdigit.magnitude_le_sixteen (by omega))⟩
  let valuesRaw : Array Int := #[values[0].intVal.eval ρ.int,
    values[1].intVal.eval ρ.int, values[2].intVal.eval ρ.int,
    values[3].intVal.eval ρ.int, values[4].intVal.eval ρ.int,
    values[5].intVal.eval ρ.int, values[6].intVal.eval ρ.int,
    values[7].intVal.eval ρ.int, values[8].intVal.eval ρ.int,
    values[9].intVal.eval ρ.int, values[10].intVal.eval ρ.int,
    values[11].intVal.eval ρ.int, values[12].intVal.eval ρ.int,
    values[13].intVal.eval ρ.int, values[14].intVal.eval ρ.int,
    values[15].intVal.eval ρ.int, values[16].intVal.eval ρ.int]
  let selected := valuesRaw[(digit.magnitude.eval ρ.int).toNat]!
  let bits : Vector Bool 256 :=
    Vector.ofFn fun i => selected.toNat.testBit i.val
  have hraw (i : Fin 17) :
      valuesRaw[i.val] = values[i].intVal.eval ρ.int := by
    fin_cases i <;> rfl
  have hselected : selected = values[chosen].intVal.eval ρ.int := by
    unfold selected
    rw [getElem!_pos valuesRaw _ (by
      simpa [valuesRaw] using
        lt_of_le_of_lt hdigit.magnitude_le_sixteen (by omega))]
    exact hraw chosen
  have hselected0 : 0 ≤ selected := hselected ▸ (hvalues chosen).1.1
  refine ⟨bits, ?_, ?_⟩
  · simp only [WF.interpHint, WF.evalArgs, signedMagnitudeLookupRepHint,
      signedMagnitudeLookupArgs, Vector.getElem_map]
    split
    · simp [bits, selected, valuesRaw]
    · rename_i hnegative
      exfalso
      apply hnegative
      simpa [selected, valuesRaw] using hselected0
  · have hselectedLt : selected < P256.base.modulus :=
      hselected ▸ (hvalues chosen).2
    have hfit : selected.toNat < 2 ^ 256 := by
      apply (Int.toNat_lt hselected0).2
      exact hselectedLt.trans (by
        norm_num [P256.base, P256.baseModulus])
    have houtFacts (out : U 256)
        (hout : U.Rel ρ out
          (Word.eval ρ.bool { bitsLE := Vector.map LC.ofConst bits })) :
        out.intVal.eval ρ.int = selected ∧
          (⟨out.intVal, 2⟩ : P256.AffineSlope.Rep).Valid ρ ∧
          out.intVal.eval ρ.int < P256.base.modulus := by
      have hword :
          (Word.eval ρ.bool { bitsLE := Vector.map LC.ofConst bits }).toNat =
            selected.toNat := by
        rw [show Vector.map LC.ofConst bits =
            Vector.ofFn (n := 256) fun i =>
              LC.ofConst (selected.toNat.testBit i.val) by
          ext i
          simp [bits]]
        exact Modular.Aux.constWord_eval_toNat selected.toNat hfit ρ
      have houtVal : out.intVal.eval ρ.int = selected := by
        rw [U.Rel.intVal hout, hword, Int.toNat_of_nonneg hselected0]
      exact ⟨houtVal, ⟨U.intVal_nonneg out hout.1, by
        rw [houtVal]
        have hp : (0 : Int) < P256.base.modulus := by
          exact_mod_cast P256.base.positive
        simpa using hselectedLt.trans (by nlinarith)⟩, by
        simpa [houtVal] using hselectedLt⟩
    mvcgen -trivial
    case vc1.vc1.refine_2.success =>
      rename_i out hout
      have houtVal := (houtFacts out hout).1
      have hcenterSelect
          (hcenter : digit.oneHot.intBits[16].eval ρ.int = 1) :
          out.intVal.eval ρ.int = values[0].intVal.eval ρ.int := by
        have hm := hdigit.magnitude_eq_zero_of_center hcenter
        have hchosen0 : chosen = 0 := by
          apply Fin.eq_of_val_eq
          simp [chosen, hm]
        rw [houtVal, hselected, hchosen0]
        rfl
      have hgateSelect (i : Fin 16)
          (hgate : (signedNonzeroMagnitudeGate digit i.val i.isLt).eval
            ρ.int = 1) :
          out.intVal.eval ρ.int =
            (values[i.val + 1]'(by omega)).intVal.eval ρ.int := by
        have hm := hdigit.magnitude_eq_succ_of_gate i.val i.isLt hgate
        have hchosen : chosen = ⟨i.val + 1, by omega⟩ := by
          apply Fin.eq_of_val_eq
          simp [chosen, hm]
        rw [houtVal, hselected, hchosen]
        rfl
      constructor
      · rcases hdigit.bit_zero_or_one 16 with hzero | hone
        · have hzero' :
              digit.oneHot.intBits[(16 : Fin 33)].eval ρ.int = 0 := hzero
          change digit.oneHot.intBits[(16 : Fin 33)].eval ρ.int *
              (out.intVal - values[0].intVal).eval ρ.int = 0
          rw [hzero']
          simp
        · have hdiff : (out.intVal - values[0].intVal).eval ρ.int = 0 := by
            simp [LC.eval_sub, hcenterSelect hone]
          rw [hdiff, mul_zero, LC.eval_zero]
      · mvcgen [WF.foldRange] invariants
        · ⇓⟨cur, _⟩ => ⌜∀ i : Fin 16, i.val < cur.prefix.length →
            (signedNonzeroMagnitudeGate digit i.val i.isLt).eval ρ.int = 1 →
            out.intVal.eval ρ.int =
              (values[i.val + 1]'(by omega)).intVal.eval ρ.int⌝
        case vc1 pref cur suff hsplit _ hprev =>
          have hcur16 : cur < 16 := by grind
          let fi : Fin 16 := ⟨cur, hcur16⟩
          constructor
          · rcases hdigit.nonzeroMagnitudeGate_bit cur hcur16 with hzero | hone
            · rw [show (signedNonzeroMagnitudeGate digit cur hcur16).eval
                  ρ.int = 0 by simpa using hzero]
              simp
            · have hdiff :
                  (out.intVal - values[cur + 1].intVal).eval ρ.int = 0 := by
                have hsel : out.intVal.eval ρ.int =
                    values[cur + 1].intVal.eval ρ.int := by
                  simpa [fi] using
                    hgateSelect fi (by simpa [fi] using hone)
                simp [LC.eval_sub, hsel]
              rw [hdiff, mul_zero, LC.eval_zero]
          · mvcgen
            intro i hi hone
            simp only [List.length_append, List.length_singleton] at hi
            by_cases hlt : i.val < pref.length
            · exact hprev i hlt hone
            · have hieq : i.val = cur := by
                have hcur : cur = pref.length := by grind
                omega
              subst cur
              exact hgateSelect i hone
        case vc2 => simp
        case vc3 hloop =>
          refine ⟨?_, (houtFacts out hout).2.1, (houtFacts out hout).2.2⟩
          constructor
          · intro hcenter
            unfold Modular.Lazy.evalZMod
            rw [hcenterSelect hcenter]
          · intro i hgate
            unfold Modular.Lazy.evalZMod
            rw [hloop i (by simp) hgate]

@[spec] theorem lookupSignedMagnitudeFlag_complete
    {digit : SignedDigit} {values : Vector (LC ℤ) 17}
    (hdigit : SignedDigitSpec ρ value digit)
    (hvalues : ∀ i : Fin 17,
      values[i].eval ρ.int = 0 ∨ values[i].eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Complete.interp ρ (lookupSignedMagnitudeFlag digit values)
    ⦃⇓ out => ⌜SignedMagnitudeLookupFlagSpec ρ digit values out ∧
      (out.eval ρ.int = 0 ∨ out.eval ρ.int = 1)⌝⦄ := by
  mvcgen [lookupSignedMagnitudeFlag]
  let chosen : Fin 17 := ⟨(digit.magnitude.eval ρ.int).toNat,
    (Int.toNat_lt hdigit.magnitude_nonneg).2
      (lt_of_le_of_lt hdigit.magnitude_le_sixteen (by omega))⟩
  let valuesRaw : Array Int := #[values[0].eval ρ.int,
    values[1].eval ρ.int, values[2].eval ρ.int,
    values[3].eval ρ.int, values[4].eval ρ.int,
    values[5].eval ρ.int, values[6].eval ρ.int,
    values[7].eval ρ.int, values[8].eval ρ.int,
    values[9].eval ρ.int, values[10].eval ρ.int,
    values[11].eval ρ.int, values[12].eval ρ.int,
    values[13].eval ρ.int, values[14].eval ρ.int,
    values[15].eval ρ.int, values[16].eval ρ.int]
  let selected := valuesRaw[(digit.magnitude.eval ρ.int).toNat]!
  let selectedBit : Bool := selected = 1
  let bits : Vector Bool 1 := Vector.ofFn fun _ => selectedBit
  have hraw (i : Fin 17) : valuesRaw[i.val] = values[i].eval ρ.int := by
    fin_cases i <;> rfl
  have hselected : selected = values[chosen].eval ρ.int := by
    unfold selected
    rw [getElem!_pos valuesRaw _ (by
      simpa [valuesRaw] using
        lt_of_le_of_lt hdigit.magnitude_le_sixteen (by omega))]
    exact hraw chosen
  have hselectedBit : selected = 0 ∨ selected = 1 := hselected ▸ hvalues chosen
  refine ⟨bits, ?_, ?_⟩
  · simp [WF.interpHint, WF.evalArgs, signedMagnitudeLookupFlagHint,
      signedMagnitudeLookupArgs, Vector.getElem_map, bits, selectedBit,
      selected, valuesRaw]
  · mvcgen
    rename_i out hout
    have houtVal : out.eval ρ.int = selected := by
      rw [hout]
      rcases hselectedBit with hzero | hone
      · simp [bits, selectedBit, hzero]
      · simp [bits, selectedBit, hone]
    have hcenterSelect
        (hcenter : digit.oneHot.intBits[16].eval ρ.int = 1) :
        out.eval ρ.int = values[0].eval ρ.int := by
      have hm := hdigit.magnitude_eq_zero_of_center hcenter
      have hchosen0 : chosen = 0 := by
        apply Fin.eq_of_val_eq
        simp [chosen, hm]
      rw [houtVal, hselected, hchosen0]
      rfl
    have hgateSelect (i : Fin 16)
        (hgate : (signedNonzeroMagnitudeGate digit i.val i.isLt).eval
          ρ.int = 1) :
        out.eval ρ.int =
          (values[i.val + 1]'(by omega)).eval ρ.int := by
      have hm := hdigit.magnitude_eq_succ_of_gate i.val i.isLt hgate
      have hchosen : chosen = ⟨i.val + 1, by omega⟩ := by
        apply Fin.eq_of_val_eq
        simp [chosen, hm]
      rw [houtVal, hselected, hchosen]
      rfl
    constructor
    · rcases hdigit.bit_zero_or_one 16 with hzero | hone
      · have hzero' :
            digit.oneHot.intBits[(16 : Fin 33)].eval ρ.int = 0 := hzero
        change digit.oneHot.intBits[(16 : Fin 33)].eval ρ.int *
            (out - values[0]).eval ρ.int = 0
        rw [hzero']
        simp
      · have hdiff : (out - values[0]).eval ρ.int = 0 := by
          simp [LC.eval_sub, hcenterSelect hone]
        rw [hdiff, mul_zero, LC.eval_zero]
    · mvcgen [WF.foldRange] invariants
      · ⇓⟨cur, _⟩ => ⌜∀ i : Fin 16, i.val < cur.prefix.length →
          (signedNonzeroMagnitudeGate digit i.val i.isLt).eval ρ.int = 1 →
          out.eval ρ.int =
            (values[i.val + 1]'(by omega)).eval ρ.int⌝
      case vc1 pref cur suff hsplit _ hprev =>
        have hcur16 : cur < 16 := by grind
        let fi : Fin 16 := ⟨cur, hcur16⟩
        constructor
        · rcases hdigit.nonzeroMagnitudeGate_bit cur hcur16 with hzero | hone
          · rw [show (signedNonzeroMagnitudeGate digit cur hcur16).eval
                ρ.int = 0 by simpa using hzero]
            simp
          · have hdiff : (out - values[cur + 1]).eval ρ.int = 0 := by
              have hsel : out.eval ρ.int =
                  values[cur + 1].eval ρ.int := by
                simpa [fi] using hgateSelect fi (by simpa [fi] using hone)
              simp [LC.eval_sub, hsel]
            rw [hdiff, mul_zero, LC.eval_zero]
        · mvcgen
          intro i hi hone
          simp only [List.length_append, List.length_singleton] at hi
          by_cases hlt : i.val < pref.length
          · exact hprev i hlt hone
          · have hieq : i.val = cur := by
              have hcur : cur = pref.length := by grind
              omega
            subst cur
            exact hgateSelect i hone
      case vc2 => simp
      case vc3 hloop =>
        refine ⟨?_, ?_⟩
        · constructor
          · exact hcenterSelect
          · intro i hgate
            exact hloop i (by simp) hgate
        · simpa [houtVal] using hselectedBit

private theorem normalizedRep_of_coordinate_eq
    {source out : P256.AffineSlope.Point} {q : P256.Reference.Point}
    (hsource : P256.Reference.NormalizedRep ρ source q)
    (hinfinity : out.infinity.eval ρ.int = source.infinity.eval ρ.int)
    (hX : Modular.Lazy.evalZMod P256.base out.X ρ =
      Modular.Lazy.evalZMod P256.base source.X ρ)
    (hY : Modular.Lazy.evalZMod P256.base out.Y ρ =
      Modular.Lazy.evalZMod P256.base source.Y ρ) :
    P256.Reference.NormalizedRep ρ out q := by
  rcases hsource with ⟨⟨hbit, hcoordinates⟩, hnormalized⟩
  constructor
  · constructor
    · simpa [hinfinity] using hbit
    · unfold P256.Reference.circuitCoordinates at hcoordinates ⊢
      rw [hinfinity, hX, hY]
      exact hcoordinates
  · intro hq
    rcases hnormalized hq with ⟨hx, hy⟩
    exact ⟨hX.trans hx, hY.trans hy⟩

private theorem nsmul_ne_zero_of_prime_order {q : P256.Reference.Point}
    (hq : q ≠ 0) (horder : P256.scalarModulus • q = 0)
    {k : Nat} (hk0 : k ≠ 0) (hk : k < P256.scalarModulus) :
    k • q ≠ 0 := by
  intro hzero
  have hdvd : P256.scalarModulus ∣ k := by
    rw [← Reference.Aux.addOrderOf_eq_scalarModulus hq horder,
      addOrderOf_dvd_iff_nsmul_eq_zero]
    exact hzero
  exact (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk0) hk) hdvd

def SelectBitSpec (rho : WF.Valuation) (choose whenOne whenZero out : LC ℤ) :
    Prop :=
  (choose.eval rho.int = 1 → out.eval rho.int = whenOne.eval rho.int) ∧
  (choose.eval rho.int = 0 → out.eval rho.int = whenZero.eval rho.int) ∧
  (out.eval rho.int = 0 ∨ out.eval rho.int = 1)

@[spec] theorem selectBit_sound {choose whenOne whenZero : LC ℤ} :
    ⦃⌜True⌝⦄ Sound.interp ρ (selectBit choose whenOne whenZero)
    ⦃⇓ out => ⌜SelectBitSpec ρ choose whenOne whenZero out⌝⦄ := by
  mvcgen [selectBit, SelectBitSpec]
  intro bits
  mvcgen
  rename_i out hout hmul
  constructor
  · intro hc
    simp only [LC.eval_sub, hc, one_mul] at hmul
    omega
  · constructor
    · intro hc
      simp only [LC.eval_sub, hc, zero_mul] at hmul
      omega
    · have hz := hout.1 (0 : Fin 1)
      cases hb : out.bits.bitsLE[0].eval ρ.bool <;> simp [hb] at hz
      · left
        simp [U.intVal, hz]
      · right
        simp [U.intVal, hz]

@[spec] theorem selectBit_complete {choose whenOne whenZero : LC ℤ}
    (hchoose : choose.eval ρ.int = 0 ∨ choose.eval ρ.int = 1)
    (hone : whenOne.eval ρ.int = 0 ∨ whenOne.eval ρ.int = 1)
    (hzero : whenZero.eval ρ.int = 0 ∨ whenZero.eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Complete.interp ρ (selectBit choose whenOne whenZero)
    ⦃⇓ out => ⌜SelectBitSpec ρ choose whenOne whenZero out⌝⦄ := by
  mvcgen [selectBit]
  let value : Bool := if choose.eval ρ.int = 1 then
    whenOne.eval ρ.int = 1 else whenZero.eval ρ.int = 1
  let bits : Vector Bool 1 := Vector.ofFn fun _ => value
  refine ⟨bits, ?_, ?_⟩
  · simp [WF.interpHint, WF.evalArgs, bits, value]
  · mvcgen
    rename_i out hout
    have hword :
        (Word.eval ρ.bool { bitsLE := Vector.map LC.ofConst bits }).toNat =
          if value then 1 else 0 := by
      cases hv : value <;>
        simp [Word.eval, BitVec.toNat_ofFnLE, bits, hv, Nat.ofBits] <;>
        native_decide
    have houtVal : out.intVal.eval ρ.int = if value then 1 else 0 := by
      rw [U.Rel.intVal hout]
      exact_mod_cast hword
    constructor
    · rcases hchoose with hc | hc <;> rcases hone with ho | ho <;>
        rcases hzero with hz | hz <;>
        simp [value, hc, ho, hz] at houtVal ⊢ <;> omega
    · mvcgen
      unfold SelectBitSpec
      rcases hchoose with hc | hc <;> rcases hone with ho | ho <;>
        rcases hzero with hz | hz <;>
        simp [value, hc, ho, hz] at houtVal ⊢ <;> omega

private theorem radix32MagnitudeSpec_of_select
    {value : LC ℤ} {q : P256.Reference.Point}
    (hdigit : SignedDigitSpec ρ value digit)
    (htable : Radix32TableSpec ρ table q)
    {low : P256.AffineSlope.Point} {X Y : P256.AffineSlope.Rep}
    {infinity : LC ℤ}
    (hlowExists : ∃ i : Fin 16,
      (digit.magnitude - 16 • digit.isSixteen).eval ρ.int = i.val ∧
      P256.Reference.NormalizedRep ρ low (i.val • q))
    (hX : P256.AffineSlope.SelectZModSpec ρ digit.isSixteen
      table.p16.X low.X X)
    (hY : P256.AffineSlope.SelectZModSpec ρ digit.isSixteen
      table.p16.Y low.Y Y)
    (hinfinity : SelectBitSpec ρ digit.isSixteen
      table.p16.infinity low.infinity infinity) :
    Radix32MagnitudeSpec ρ value
      ⟨X, Y, infinity⟩ q := by
  rcases hlowExists with ⟨i, hilow, hlow⟩
  have hs := hdigit.isSixteen_eval
  by_cases hsixteen : value.eval ρ.int = -16 ∨ value.eval ρ.int = 16
  · rw [if_pos hsixteen] at hs
    have hm : digit.magnitude.eval ρ.int = 16 :=
      hdigit.isSixteen_eq_one_iff.mp hs
    have hi0 : i.val = 0 := by
      simp only [LC.eval_sub, LC.eval_nsmul, nsmul_eq_mul, hs, hm] at hilow
      omega
    have hieq : i = 0 := Fin.eq_of_val_eq hi0
    subst i
    unfold Radix32MagnitudeSpec
    have habs : (value.eval ρ.int).natAbs = 16 := by
      rcases hsixteen with hneg | hpos
      · rw [hneg]
        decide
      · rw [hpos]
        decide
    rw [habs]
    apply normalizedRep_of_coordinate_eq htable.2
    · exact hinfinity.1 hs
    · exact hX.1 hs
    · exact hY.1 hs
  · rw [if_neg hsixteen] at hs
    have hiAbs : i.val = (value.eval ρ.int).natAbs := by
      simp only [LC.eval_sub, LC.eval_nsmul, nsmul_eq_mul, hs,
        hdigit.magnitude_eval] at hilow
      omega
    have hlow' : P256.Reference.NormalizedRep ρ low
        ((value.eval ρ.int).natAbs • q) := by
      simpa [hiAbs] using hlow
    apply normalizedRep_of_coordinate_eq hlow'
    · exact hinfinity.2.1 hs
    · exact hX.2 hs
    · exact hY.2 hs

@[spec] theorem selectRadix32Magnitude_sound
    {value : LC ℤ} {q : P256.Reference.Point}
    (hdigit : SignedDigitSpec ρ value digit)
    (htable : Radix32TableSpec ρ table q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (selectRadix32Magnitude digit table)
    ⦃⇓ out => ⌜Radix32MagnitudeSpec ρ value out q⌝⦄ := by
  mvcgen [selectRadix32Magnitude, Radix32MagnitudeSpec]
  case vc1.success =>
    rename_i X hX Y hY infinity hinfinity
    rcases hdigit.magnitude_choice with hcenter | ⟨i, hgate, hm⟩
    · rcases hcenter with ⟨hcenter, hm⟩
      have habsInt : ((value.eval ρ.int).natAbs : Int) = 0 :=
        hdigit.magnitude_eval.symm.trans hm
      have habs : (value.eval ρ.int).natAbs = 0 := by
        exact_mod_cast habsInt
      unfold Radix32MagnitudeSpec
      rw [habs]
      apply normalizedRep_of_coordinate_eq (htable.1 0)
      · simpa [radix32MagnitudeValues] using hinfinity.1 hcenter
      · simpa [radix32MagnitudeValues] using hX.1 hcenter
      · simpa [radix32MagnitudeValues] using hY.1 hcenter
    · have habsInt : ((value.eval ρ.int).natAbs : Int) = i.val + 1 :=
        hdigit.magnitude_eval.symm.trans hm
      have habs : (value.eval ρ.int).natAbs = i.val + 1 := by
        exact_mod_cast habsInt
      unfold Radix32MagnitudeSpec
      rw [habs]
      by_cases hi : i.val < 15
      · let j : Fin 16 := ⟨i.val + 1, by omega⟩
        have hij : i.val + 1 < 16 := by omega
        apply normalizedRep_of_coordinate_eq (htable.1 j)
        · simpa [radix32MagnitudeValues, j, hij] using hinfinity.2 i hgate
        · simpa [radix32MagnitudeValues, j, hij] using hX.2 i hgate
        · simpa [radix32MagnitudeValues, j, hij] using hY.2 i hgate
      · have hieq : i = (15 : Fin 16) := Fin.eq_of_val_eq (by omega)
        subst i
        apply normalizedRep_of_coordinate_eq htable.2
        · simpa [radix32MagnitudeValues] using hinfinity.2 (15 : Fin 16) hgate
        · simpa [radix32MagnitudeValues] using hX.2 (15 : Fin 16) hgate
        · simpa [radix32MagnitudeValues] using hY.2 (15 : Fin 16) hgate

@[spec] theorem selectRadix32Magnitude_complete
    {value : LC ℤ} {q : P256.Reference.Point}
    (hdigit : SignedDigitSpec ρ value digit)
    (htableValid : Radix32TableValid ρ table)
    (htable : Radix32TableSpec ρ table q)
    (hq : q ≠ 0) (horder : P256.scalarModulus • q = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (selectRadix32Magnitude digit table)
    ⦃⇓ out => ⌜out.Valid ρ ∧ Radix32MagnitudeSpec ρ value out q⌝⦄ := by
  mvcgen [selectRadix32Magnitude, Radix32MagnitudeSpec,
    Radix32TableValid]
  case vc3.hvalues =>
    intro i
    by_cases hi : i.val < 16
    · have hv := htableValid.1 ⟨i.val, hi⟩
      simpa [radix32MagnitudeValues, hi] using
        (show (table.low[i.val]'hi).X.Valid ρ ∧
            (table.low[i.val]'hi).X.intVal.eval ρ.int <
              P256.base.modulus from ⟨hv.2.1, hv.2.2.1⟩)
    · have hieq : i = (16 : Fin 17) := Fin.eq_of_val_eq (by omega)
      subst i
      simpa [radix32MagnitudeValues] using
        (show table.p16.X.Valid ρ ∧
            table.p16.X.intVal.eval ρ.int < P256.base.modulus from
          ⟨htableValid.2.2.1, htableValid.2.2.2.1⟩)
  case vc6.hvalues =>
    intro i
    by_cases hi : i.val < 16
    · have hv := htableValid.1 ⟨i.val, hi⟩
      simpa [radix32MagnitudeValues, hi] using
        (show (table.low[i.val]'hi).Y.Valid ρ ∧
            (table.low[i.val]'hi).Y.intVal.eval ρ.int <
              P256.base.modulus from ⟨hv.2.2.2.2.1, hv.2.2.2.2.2.1⟩)
    · have hieq : i = (16 : Fin 17) := Fin.eq_of_val_eq (by omega)
      subst i
      simpa [radix32MagnitudeValues] using
        (show table.p16.Y.Valid ρ ∧
            table.p16.Y.intVal.eval ρ.int < P256.base.modulus from
          ⟨htableValid.2.2.2.2.2.1, htableValid.2.2.2.2.2.2.1⟩)
  case vc9.hvalues =>
    intro i
    by_cases hi : i.val < 16
    · have hv := htableValid.1 ⟨i.val, hi⟩
      simpa [radix32MagnitudeValues, hi] using hv.2.2.2.2.2.2
    · have hieq : i = (16 : Fin 17) := Fin.eq_of_val_eq (by omega)
      subst i
      simpa [radix32MagnitudeValues] using htableValid.2.2.2.2.2.2.2
  case vc10.success =>
    rename_i X hX Y hY infinity hinfinity
    have hspec : Radix32MagnitudeSpec ρ value ⟨X, Y, infinity⟩ q := by
      rcases hdigit.magnitude_choice with hcenter | ⟨i, hgate, hm⟩
      · rcases hcenter with ⟨hcenter, hm⟩
        have habsInt : ((value.eval ρ.int).natAbs : Int) = 0 :=
          hdigit.magnitude_eval.symm.trans hm
        have habs : (value.eval ρ.int).natAbs = 0 := by
          exact_mod_cast habsInt
        unfold Radix32MagnitudeSpec
        rw [habs]
        apply normalizedRep_of_coordinate_eq (htable.1 0)
        · simpa [radix32MagnitudeValues] using hinfinity.1.1 hcenter
        · simpa [radix32MagnitudeValues] using hX.1.1 hcenter
        · simpa [radix32MagnitudeValues] using hY.1.1 hcenter
      · have habsInt : ((value.eval ρ.int).natAbs : Int) = i.val + 1 :=
          hdigit.magnitude_eval.symm.trans hm
        have habs : (value.eval ρ.int).natAbs = i.val + 1 := by
          exact_mod_cast habsInt
        unfold Radix32MagnitudeSpec
        rw [habs]
        by_cases hi : i.val < 15
        · let j : Fin 16 := ⟨i.val + 1, by omega⟩
          have hij : i.val + 1 < 16 := by omega
          apply normalizedRep_of_coordinate_eq (htable.1 j)
          · simpa [radix32MagnitudeValues, j, hij] using
              hinfinity.1.2 i hgate
          · simpa [radix32MagnitudeValues, j, hij] using hX.1.2 i hgate
          · simpa [radix32MagnitudeValues, j, hij] using hY.1.2 i hgate
        · have hieq : i = (15 : Fin 16) := Fin.eq_of_val_eq (by omega)
          subst i
          apply normalizedRep_of_coordinate_eq htable.2
          · simpa [radix32MagnitudeValues] using
              hinfinity.1.2 (15 : Fin 16) hgate
          · simpa [radix32MagnitudeValues] using hX.1.2 (15 : Fin 16) hgate
          · simpa [radix32MagnitudeValues] using hY.1.2 (15 : Fin 16) hgate
    exact ⟨⟨hX.2.2.2, hX.2.1, hX.2.2.1,
      hY.2.2.2, hY.2.1, hY.2.2.1, hinfinity.2⟩, hspec⟩

def ApplyPointSignSpec (ρ : WF.Valuation) (negative : LC ℤ)
    (out : P256.AffineSlope.Point) (q : P256.Reference.Point) : Prop :=
  P256.Reference.NormalizedRep ρ out
    (if negative.eval ρ.int = 1 then -q else q)

private theorem normalizedRep_neg_of_coordinate_eq
    {source out : P256.AffineSlope.Point} {q : P256.Reference.Point}
    (hsource : P256.Reference.NormalizedRep ρ source q)
    (hinfinity : out.infinity.eval ρ.int = source.infinity.eval ρ.int)
    (hX : Modular.Lazy.evalZMod P256.base out.X ρ =
      Modular.Lazy.evalZMod P256.base source.X ρ)
    (hY : Modular.Lazy.evalZMod P256.base out.Y ρ =
      -Modular.Lazy.evalZMod P256.base source.Y ρ) :
    P256.Reference.NormalizedRep ρ out (-q) := by
  rcases q with _ | ⟨qx, qy, hcurve⟩
  · change P256.Reference.NormalizedRep ρ out 0
    have hsourceY : Modular.Lazy.evalZMod P256.base source.Y ρ = 0 :=
      (hsource.2 rfl).2
    apply normalizedRep_of_coordinate_eq hsource hinfinity hX
    rw [hY, hsourceY]
    simp
  · obtain ⟨hsourceInfinity, hsourceX, hsourceY⟩ :=
      P256.Reference.Aux.represents_some hsource.1
    constructor
    · constructor
      · exact Or.inl (hinfinity.trans hsourceInfinity)
      · unfold P256.Reference.circuitCoordinates
        rw [if_neg (by rw [hinfinity, hsourceInfinity]; omega)]
        simp only [P256.Reference.coordinates,
          WeierstrassCurve.Affine.Point.neg_some]
        apply congrArg₂ P256.Reference.Coordinates.finite
        · exact hX.trans hsourceX
        · rw [hY, hsourceY]
          exact P256.Reference.negY_eq qx qy |>.symm
    · intro hzero
      simp at hzero

private theorem normalizedRep_y_pos_of_nonzero_order
    {P : P256.AffineSlope.Point} {q : P256.Reference.Point}
    (hPvalid : P.Valid ρ) (hP : P256.Reference.NormalizedRep ρ P q)
    (hq : q ≠ 0) (horder : P256.scalarModulus • q = 0) :
    0 < P.Y.intVal.eval ρ.int := by
  have htwo : q + q ≠ 0 :=
    (Reference.Aux.no_two_torsion_of_order horder).resolve_left hq
  rcases q with _ | ⟨qx, qy, hcurve⟩
  · exact (hq rfl).elim
  · obtain ⟨_, _, hPyeq⟩ := P256.Reference.Aux.represents_some hP.1
    have hyneg : qy ≠ P256.Reference.curve.toAffine.negY qx qy := by
      intro hy
      exact htwo (WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy)
    have hrawne : P.Y.intVal.eval ρ.int ≠ 0 := by
      intro hzero
      apply hyneg
      rw [P256.Reference.negY_eq, ← hPyeq]
      change (Int.castRingHom (ZMod P256.base.modulus))
          (P.Y.intVal.eval ρ.int) =
        -(Int.castRingHom (ZMod P256.base.modulus))
          (P.Y.intVal.eval ρ.int)
      rw [hzero]
      simp
    exact lt_of_le_of_ne hPvalid.2.2.2.2.1.1 hrawne.symm

@[spec] theorem applyPointSign_sound
    (hnegative : negative.eval ρ.int = 0 ∨ negative.eval ρ.int = 1)
    (hP : P256.Reference.NormalizedRep ρ P q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (applyPointSign negative P)
    ⦃⇓ out => ⌜ApplyPointSignSpec ρ negative out q⌝⦄ := by
  mvcgen [applyPointSign, ApplyPointSignSpec]
  intro bits
  mvcgen
  case vc1.vc1.success =>
    rename_i outY _ hassert
    rcases hnegative with hnegative | hnegative
    · unfold ApplyPointSignSpec
      rw [if_neg (by omega)]
      apply normalizedRep_of_coordinate_eq
        (out := ⟨P.X, ⟨outY.intVal, 2⟩, P.infinity⟩) hP rfl rfl
      have houtYInt : outY.intVal.eval ρ.int = P.Y.intVal.eval ρ.int := by
        simp only [LC.eval_sub, LC.eval_nsmul, nsmul_eq_mul,
          LC.eval_ofConst, hnegative, zero_mul] at hassert
        omega
      change (Int.castRingHom (ZMod P256.base.modulus))
          (outY.intVal.eval ρ.int) =
        (Int.castRingHom (ZMod P256.base.modulus))
          (P.Y.intVal.eval ρ.int)
      rw [houtYInt]
    · unfold ApplyPointSignSpec
      rw [if_pos hnegative]
      apply normalizedRep_neg_of_coordinate_eq
        (out := ⟨P.X, ⟨outY.intVal, 2⟩, P.infinity⟩) hP rfl rfl
      have houtYInt : outY.intVal.eval ρ.int =
          (P256.base.modulus : Int) - P.Y.intVal.eval ρ.int := by
        simp only [LC.eval_sub, LC.eval_nsmul, nsmul_eq_mul,
          LC.eval_ofConst, hnegative, one_mul] at hassert
        omega
      change (Int.castRingHom (ZMod P256.base.modulus))
          (outY.intVal.eval ρ.int) =
        -(Int.castRingHom (ZMod P256.base.modulus))
          (P.Y.intVal.eval ρ.int)
      rw [houtYInt]
      norm_num

@[spec] theorem applyPointSign_complete
    (hnegative : negative.eval ρ.int = 0 ∨ negative.eval ρ.int = 1)
    (hPvalid : P.Valid ρ)
    (hP : P256.Reference.NormalizedRep ρ P q)
    (hnegativeNonzero : negative.eval ρ.int = 1 → q ≠ 0)
    (horder : P256.scalarModulus • q = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (applyPointSign negative P)
    ⦃⇓ out => ⌜out.Valid ρ ∧ ApplyPointSignSpec ρ negative out q⌝⦄ := by
  mvcgen [applyPointSign, ApplyPointSignSpec]
  let value := if negative.eval ρ.int = 1 then
    (P256.base.modulus : Int) - P.Y.intVal.eval ρ.int
    else P.Y.intVal.eval ρ.int
  have hvalue0 : 0 ≤ value := by
    rcases hnegative with hzero | hone
    · simp [value, hzero, hPvalid.2.2.2.2.1.1]
    · have hylt := hPvalid.2.2.2.2.2.1
      simp [value, hone]
      omega
  have hvalueLt : value < P256.base.modulus := by
    rcases hnegative with hzero | hone
    · simpa [value, hzero] using hPvalid.2.2.2.2.2.1
    · have hypos := normalizedRep_y_pos_of_nonzero_order hPvalid hP
          (hnegativeNonzero hone) horder
      simp [value, hone]
      omega
  let bits : Vector Bool 256 :=
    Vector.ofFn fun i => value.toNat.testBit i.val
  refine ⟨bits, ?_, ?_⟩
  · simp [WF.interpHint, WF.evalArgs, bits, value, hvalue0]
  · mvcgen
    rename_i outY houtY
    have hfit : value.toNat < 2 ^ 256 := by
      apply (Int.toNat_lt hvalue0).2
      exact hvalueLt.trans (by native_decide)
    have hword :
        (Word.eval ρ.bool { bitsLE := Vector.map LC.ofConst bits }).toNat =
          value.toNat := by
      rw [show Vector.map LC.ofConst bits =
          Vector.ofFn (n := 256) fun i =>
            LC.ofConst (value.toNat.testBit i.val) by
        ext i
        simp [bits]]
      exact Modular.Aux.constWord_eval_toNat value.toNat hfit ρ
    have houtVal : outY.intVal.eval ρ.int = value := by
      rw [U.Rel.intVal houtY, hword, Int.toNat_of_nonneg hvalue0]
    constructor
    · rcases hnegative with hzero | hone
      · simp [LC.eval_sub, LC.eval_nsmul, nsmul_eq_mul,
          LC.eval_ofConst, hzero, value, houtVal]
      · simp [LC.eval_sub, LC.eval_nsmul, nsmul_eq_mul,
          LC.eval_ofConst, hone, value, houtVal]
        ring
    · mvcgen
      constructor
      · refine ⟨hPvalid.1, hPvalid.2.1, hPvalid.2.2.1, rfl,
          ⟨U.intVal_nonneg outY houtY.1, ?_⟩, ?_,
          hPvalid.2.2.2.2.2.2⟩
        · rw [houtVal]
          change value < (2 : Int) * P256.base.modulus
          have hp : 0 < P256.base.modulus := by native_decide
          omega
        · simpa [houtVal] using hvalueLt
      · rcases hnegative with hzero | hone
        · unfold ApplyPointSignSpec
          rw [if_neg (by omega)]
          apply normalizedRep_of_coordinate_eq
            (out := ⟨P.X, ⟨outY.intVal, 2⟩, P.infinity⟩) hP rfl rfl
          change (Int.castRingHom (ZMod P256.base.modulus))
              (outY.intVal.eval ρ.int) =
            (Int.castRingHom (ZMod P256.base.modulus))
              (P.Y.intVal.eval ρ.int)
          rw [houtVal]
          simp [value, hzero]
        · unfold ApplyPointSignSpec
          rw [if_pos hone]
          apply normalizedRep_neg_of_coordinate_eq
            (out := ⟨P.X, ⟨outY.intVal, 2⟩, P.infinity⟩) hP rfl rfl
          change (Int.castRingHom (ZMod P256.base.modulus))
              (outY.intVal.eval ρ.int) =
            -(Int.castRingHom (ZMod P256.base.modulus))
              (P.Y.intVal.eval ρ.int)
          rw [houtVal]
          simp [value, hone]

def SignedRadix32PointSpec (ρ : WF.Valuation) (value : LC ℤ)
    (out : P256.AffineSlope.Point) (q : P256.Reference.Point) : Prop :=
  P256.Reference.NormalizedRep ρ out
    (if value.eval ρ.int < 0 then
      -((value.eval ρ.int).natAbs • q)
    else (value.eval ρ.int).natAbs • q)

private theorem signedPoint_eq_zsmul (x : Int)
    (q : P256.Reference.Point) :
    (if x < 0 then -(x.natAbs • q) else x.natAbs • q) = x • q := by
  cases x with
  | ofNat n => simp
  | negSucc n => simp

theorem SignedRadix32PointSpec.zsmul
    (h : SignedRadix32PointSpec ρ value out q) :
    P256.Reference.NormalizedRep ρ out (value.eval ρ.int • q) := by
  unfold SignedRadix32PointSpec at h
  rw [signedPoint_eq_zsmul] at h
  exact h

@[spec] theorem selectSignedRadix32Point_sound
    {value : LC ℤ} {q : P256.Reference.Point}
    (hdigit : SignedDigitSpec ρ value digit)
    (htable : Radix32TableSpec ρ table q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (selectSignedRadix32Point digit table)
    ⦃⇓ out => ⌜SignedRadix32PointSpec ρ value out q⌝⦄ := by
  mvcgen [selectSignedRadix32Point, SignedRadix32PointSpec]
  case vc5.success.success =>
    intro hout
    simpa [ApplyPointSignSpec, SignedRadix32PointSpec,
      hdigit.negative_eval] using hout
  case vc7 =>
    intro _
    rw [hdigit.negative_eval]
    split <;> simp
  case vc8 =>
    intro h
    exact h

@[spec] theorem selectSignedRadix32Point_complete
    {value : LC ℤ} {q : P256.Reference.Point}
    (hdigit : SignedDigitSpec ρ value digit)
    (htableValid : Radix32TableValid ρ table)
    (htable : Radix32TableSpec ρ table q)
    (hq : q ≠ 0) (horder : P256.scalarModulus • q = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (selectSignedRadix32Point digit table)
    ⦃⇓ out => ⌜out.Valid ρ ∧ SignedRadix32PointSpec ρ value out q⌝⦄ := by
  mvcgen [selectSignedRadix32Point, SignedRadix32PointSpec]
  case vc8.success.success =>
    intro houtValid hout
    exact ⟨houtValid, by simpa [ApplyPointSignSpec,
      SignedRadix32PointSpec, hdigit.negative_eval] using hout⟩
  case vc10 =>
    intros
    rw [hdigit.negative_eval]
    split <;> simp
  case vc11 =>
    intro hvalid _
    exact hvalid
  case vc12 =>
    intro h
    exact h.2
  case vc13 =>
    intro h hnegative
    have hvalueNeg : value.eval ρ.int < 0 := by
      rw [hdigit.negative_eval] at hnegative
      split at hnegative <;> omega
    apply nsmul_ne_zero_of_prime_order hq horder
    · exact Int.natAbs_ne_zero.mpr (by omega)
    · have hm := hdigit.magnitude_le_sixteen
      rw [hdigit.magnitude_eval] at hm
      exact lt_of_le_of_lt (by exact_mod_cast hm) (by native_decide)
  case vc14 =>
    intro _
    exact Reference.Aux.order_nsmul horder _

private theorem signedDigitSpec_of_indicators {value : LC ℤ} {oneHot : U 33}
    (h : IndicatorsSpec ρ (value + 16) oneHot) :
    SignedDigitSpec ρ value ⟨oneHot⟩ := by
  rcases h with ⟨hvalid, slot, hslot, hvalue, hunique⟩
  refine ⟨hvalid, slot, hslot, ?_, hunique⟩
  have h16 : LC.eval ρ.int (16 : LC ℤ) = 16 := LC.eval_natCast ρ.int 16
  rw [LC.eval_add, h16] at hvalue
  omega

@[spec] theorem signedDigitIndicators_sound {value : LC ℤ} :
    ⦃⌜True⌝⦄ Sound.interp ρ (signedDigitIndicators value)
    ⦃⇓ digit => ⌜SignedDigitSpec ρ value digit⌝⦄ := by
  mvcgen [signedDigitIndicators, SignedDigitSpec, IndicatorsSpec]
  exact signedDigitSpec_of_indicators ‹IndicatorsSpec ρ (value + 16) _›

@[spec] theorem signedDigitIndicators_complete {value : LC ℤ}
    (hlow : -16 ≤ value.eval ρ.int)
    (hhigh : value.eval ρ.int ≤ 16) :
    ⦃⌜True⌝⦄ Complete.interp ρ (signedDigitIndicators value)
    ⦃⇓ digit => ⌜SignedDigitSpec ρ value digit⌝⦄ := by
  mvcgen [signedDigitIndicators, SignedDigitSpec, IndicatorsSpec]
  case vc1.hd0 =>
    have h16 : LC.eval ρ.int (16 : LC ℤ) = 16 := LC.eval_natCast ρ.int 16
    rw [LC.eval_add, h16]
    omega
  case vc2.hdlt =>
    have h16 : LC.eval ρ.int (16 : LC ℤ) = 16 := LC.eval_natCast ρ.int 16
    rw [LC.eval_add, h16]
    omega
  case vc3.success =>
    exact signedDigitSpec_of_indicators ‹IndicatorsSpec ρ (value + 16) _›

theorem boothDigit_bounds {k : P256.Fn} (hk : k.val.Valid ρ)
    (i : Nat) (hi : i < 52) :
    -16 ≤ (boothDigit k i hi).eval ρ.int ∧
      (boothDigit k i hi).eval ρ.int ≤ 16 := by
  unfold boothDigit
  split
  · rename_i hlt
    have hlow := windowValue_eval hk (5 * i) 4 (by omega)
    have hlow0 : 0 ≤ (windowValue k (5 * i) 4 (by omega)).eval ρ.int := by
      rw [hlow]
      exact_mod_cast Nat.zero_le _
    have hlow16 : (windowValue k (5 * i) 4 (by omega)).eval ρ.int < 16 := by
      rw [hlow]
      exact_mod_cast (BitVec.extractLsb' (5 * i) 4 (k.val.eval ρ)).isLt
    have htop := windowValue_eval hk (5 * i + 4) 1 (by omega)
    have htop0 : 0 ≤ (windowValue k (5 * i + 4) 1 (by omega)).eval ρ.int := by
      rw [htop]
      exact_mod_cast Nat.zero_le _
    have htop2 : (windowValue k (5 * i + 4) 1 (by omega)).eval ρ.int < 2 := by
      rw [htop]
      exact_mod_cast (BitVec.extractLsb' (5 * i + 4) 1 (k.val.eval ρ)).isLt
    by_cases hzero : i = 0
    · simp only [if_pos hzero, LC.eval_sub, LC.eval_add, LC.eval_zero,
        LC.eval_nsmul, nsmul_eq_mul, add_zero]
      omega
    · have hp := windowValue_eval hk (5 * i - 1) 1 (by omega)
      have hp0 : 0 ≤ (windowValue k (5 * i - 1) 1 (by omega)).eval ρ.int := by
        rw [hp]
        exact_mod_cast Nat.zero_le _
      have hp2 : (windowValue k (5 * i - 1) 1 (by omega)).eval ρ.int < 2 := by
        rw [hp]
        exact_mod_cast (BitVec.extractLsb' (5 * i - 1) 1 (k.val.eval ρ)).isLt
      simp only [if_neg hzero, LC.eval_sub, LC.eval_add, LC.eval_nsmul,
        nsmul_eq_mul]
      omega
  · have h254 := windowValue_eval hk 254 1 (by omega)
    have h255 := windowValue_eval hk 255 1 (by omega)
    have h2540 : 0 ≤ (windowValue k 254 1 (by omega)).eval ρ.int := by
      rw [h254]
      exact_mod_cast Nat.zero_le _
    have h2542 : (windowValue k 254 1 (by omega)).eval ρ.int < 2 := by
      rw [h254]
      exact_mod_cast (BitVec.extractLsb' 254 1 (k.val.eval ρ)).isLt
    have h2550 : 0 ≤ (windowValue k 255 1 (by omega)).eval ρ.int := by
      rw [h255]
      exact_mod_cast Nat.zero_le _
    have h2552 : (windowValue k 255 1 (by omega)).eval ρ.int < 2 := by
      rw [h255]
      exact_mod_cast (BitVec.extractLsb' 255 1 (k.val.eval ρ)).isLt
    simp only [LC.eval_add]
    omega

def radix32ChunkValue (rho : WF.Valuation) (k : P256.Fn)
    (i : Nat) : Nat :=
  (BitVec.extractLsb' (5 * i) 5 (k.val.eval rho)).toNat

def boothTopBitValue (rho : WF.Valuation) (k : P256.Fn)
    (i : Nat) : Nat :=
  (BitVec.extractLsb' (5 * i + 4) 1 (k.val.eval rho)).toNat

theorem radix32ChunkValue_split {k : P256.Fn} {i : Nat} :
    radix32ChunkValue ρ k i =
      (BitVec.extractLsb' (5 * i) 4 (k.val.eval ρ)).toNat +
        16 * boothTopBitValue ρ k i := by
  unfold radix32ChunkValue boothTopBitValue
  simp only [BitVec.extractLsb'_toNat, Nat.reducePow]
  rw [show 5 * i + 4 = 5 * i + 4 by omega, Nat.shiftRight_add]
  omega

theorem boothDigit_eval_regular {k : P256.Fn} (hk : k.val.Valid ρ)
    (i : Nat) (hi : i < 51) :
    (boothDigit k i (by omega)).eval ρ.int =
      (radix32ChunkValue ρ k i : Int) +
        (if i = 0 then 0 else (boothTopBitValue ρ k (i - 1) : Int)) -
        32 * (boothTopBitValue ρ k i : Int) := by
  unfold boothDigit
  simp only [dif_pos hi, LC.eval_sub, LC.eval_add, LC.eval_nsmul,
    nsmul_eq_mul]
  rw [windowValue_eval hk, windowValue_eval hk]
  have hsplit := radix32ChunkValue_split (ρ := ρ) (k := k) (i := i)
  have htop :
      ((BitVec.extractLsb' (5 * i + 4) 1
        (k.val.eval ρ)).toNat : Int) = boothTopBitValue ρ k i := rfl
  rw [htop]
  by_cases hzero : i = 0
  · simp [hzero] at hsplit ⊢
    omega
  · simp only [if_neg hzero]
    rw [windowValue_eval hk]
    have hstart : 5 * i - 1 = 5 * (i - 1) + 4 := by omega
    rw [hstart]
    change ((BitVec.extractLsb' (5 * i) 4
        (k.val.eval ρ)).toNat : Int) +
        (boothTopBitValue ρ k (i - 1) : Int) -
        16 * (boothTopBitValue ρ k i : Int) = _
    omega

def radix32Prefix (rho : WF.Valuation) (k : P256.Fn)
    (count : Nat) : Nat :=
  (k.val.eval rho).toNat / 2 ^ (255 - 5 * count)

theorem radix32Prefix_succ {k : P256.Fn} {count : Nat}
    (hcount : count < 51) :
    radix32Prefix ρ k (count + 1) =
      32 * radix32Prefix ρ k count +
        radix32ChunkValue ρ k (50 - count) := by
  unfold radix32Prefix radix32ChunkValue
  simp only [BitVec.extractLsb'_toNat, Nat.reducePow]
  rw [show 255 - 5 * count = (250 - 5 * count) + 5 by omega,
    show 255 - 5 * (count + 1) = 250 - 5 * count by omega,
    show 5 * (50 - count) = 250 - 5 * count by omega,
    Nat.shiftRight_eq_div_pow, pow_add]
  norm_num
  rw [← Nat.div_div_eq_div_mul]
  exact (Nat.div_add_mod _ 32).symm

theorem boothDigit_eval_top {k : P256.Fn} (hk : k.val.Valid ρ) :
    (boothDigit k 51 (by omega)).eval ρ.int =
      (radix32Prefix ρ k 0 : Int) +
        (boothTopBitValue ρ k 50 : Int) := by
  unfold boothDigit radix32Prefix boothTopBitValue
  rw [dif_neg (by omega)]
  simp only [LC.eval_add]
  rw [windowValue_eval hk, windowValue_eval hk]
  simp only [BitVec.extractLsb'_toNat, Nat.reducePow]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  norm_num
  have hklt := (k.val.eval ρ).isLt
  omega

theorem boothDigit_prefix_succ {k : P256.Fn} (hk : k.val.Valid ρ)
    {count : Nat} (hcount : count < 51) :
    32 * ((radix32Prefix ρ k count : Int) +
      boothTopBitValue ρ k (50 - count)) +
        (boothDigit k (50 - count) (by omega)).eval ρ.int =
      (radix32Prefix ρ k (count + 1) : Int) +
        (if count + 1 = 51 then 0
          else boothTopBitValue ρ k (50 - (count + 1))) := by
  rw [boothDigit_eval_regular hk (50 - count) (by omega),
    radix32Prefix_succ hcount]
  by_cases hlast : count + 1 = 51
  · rw [if_pos hlast]
    have hi : 50 - count = 0 := by omega
    simp [hi]
    push_cast
    ring
  · rw [if_neg hlast]
    have hi : 50 - count ≠ 0 := by omega
    rw [if_neg hi]
    have hindex : 50 - count - 1 = 50 - (count + 1) := by omega
    rw [hindex]
    push_cast
    ring

def boothHorner (rho : WF.Valuation) (k : P256.Fn) : Nat → Int
  | 0 => (boothDigit k 51 (by omega)).eval rho.int
  | count + 1 =>
      32 * boothHorner rho k count +
        if hcount : count < 51 then
          (boothDigit k (50 - count) (by omega)).eval rho.int
        else 0

theorem boothHorner_eq_prefix {k : P256.Fn} (hk : k.val.Valid ρ)
    {count : Nat} (hcount : count ≤ 51) :
    boothHorner ρ k count =
      (radix32Prefix ρ k count : Int) +
        (if count = 51 then 0
          else boothTopBitValue ρ k (50 - count)) := by
  induction count with
  | zero =>
      simp [boothHorner, boothDigit_eval_top hk]
  | succ count ih =>
      have hcountLt : count < 51 := by omega
      rw [boothHorner, dif_pos hcountLt, ih (by omega),
        if_neg (by omega : count ≠ 51),
        boothDigit_prefix_succ hk hcountLt]

theorem boothHorner_full {k : P256.Fn} (hk : k.val.Valid ρ) :
    boothHorner ρ k 51 = ((k.val.eval ρ).toNat : Int) := by
  rw [boothHorner_eq_prefix hk (by omega)]
  simp [radix32Prefix]

def SignedRadix32StepPoint (rho : WF.Valuation) (u1 u2 : P256.Fn)
    (q : P256.Reference.Point) (i : Nat)
    (acc : P256.Reference.Point) : P256.Reference.Point :=
  let exponent := 254 - i
  let doubled := 2 • acc
  let withQ := if hq : exponent % 5 = 0 then
    doubled + (boothDigit u2 (exponent / 5) (by omega)).eval rho.int • q
  else doubled
  if exponent % 8 = 0 then
    withQ + (BitVec.extractLsb' exponent 8 (u1.val.eval rho)).toNat •
      P256.Reference.generator
  else withQ

private theorem order_zsmul {q : P256.Reference.Point}
    (horder : P256.scalarModulus • q = 0) (k : Int) :
    P256.scalarModulus • (k • q) = 0 := by
  cases k with
  | ofNat n =>
      simpa using Reference.Aux.order_nsmul horder n
  | negSucc n =>
      have h := Reference.Aux.order_nsmul horder (n + 1)
      rw [negSucc_zsmul, neg_nsmul, h, neg_zero]

theorem SignedRadix32StepPoint.order
    {u1 u2 : P256.Fn} {q acc : P256.Reference.Point} {i : Nat}
    (hacc : P256.scalarModulus • acc = 0)
    (hq : P256.scalarModulus • q = 0) :
    P256.scalarModulus • SignedRadix32StepPoint ρ u1 u2 q i acc = 0 := by
  let exponent := 254 - i
  have hdouble : P256.scalarModulus • (2 • acc) = 0 :=
    Reference.Aux.order_nsmul hacc 2
  by_cases hqDigit : exponent % 5 = 0
  · have hqTerm := order_zsmul hq
      (LC.eval ρ.int (boothDigit u2 (exponent / 5) (by omega)))
    have hwithQ := Reference.Aux.order_add hdouble hqTerm
    by_cases hgenerator : exponent % 8 = 0
    · have hpoint : SignedRadix32StepPoint ρ u1 u2 q i acc =
          (2 • acc) + LC.eval ρ.int
              (boothDigit u2 (exponent / 5) (by omega)) • q +
            (BitVec.extractLsb' exponent 8
              (u1.val.eval ρ)).toNat • P256.Reference.generator := by
        simp [SignedRadix32StepPoint, exponent, hqDigit, hgenerator]
      rw [hpoint]
      exact Reference.Aux.order_add hwithQ
        (Reference.Aux.order_nsmul Reference.Aux.generator_order _)
    · have hpoint : SignedRadix32StepPoint ρ u1 u2 q i acc =
          (2 • acc) + LC.eval ρ.int
            (boothDigit u2 (exponent / 5) (by omega)) • q := by
        simp [SignedRadix32StepPoint, exponent, hqDigit, hgenerator]
      rw [hpoint]
      exact hwithQ
  · by_cases hgenerator : exponent % 8 = 0
    · have hpoint : SignedRadix32StepPoint ρ u1 u2 q i acc =
          (2 • acc) + (BitVec.extractLsb' exponent 8
            (u1.val.eval ρ)).toNat • P256.Reference.generator := by
        simp [SignedRadix32StepPoint, exponent, hqDigit, hgenerator]
      rw [hpoint]
      exact Reference.Aux.order_add hdouble
        (Reference.Aux.order_nsmul Reference.Aux.generator_order _)
    · have hpoint : SignedRadix32StepPoint ρ u1 u2 q i acc = 2 • acc := by
        simp [SignedRadix32StepPoint, exponent, hqDigit, hgenerator]
      rw [hpoint]
      exact hdouble

private theorem generatorWindowRep_of_lookup {u : P256.Fn}
    (hu : u.val.Valid ρ) {start : Nat} {hfit : start + 8 ≤ 256}
    {out : P256.AffineSlope.Point}
    (h : ∃ j : Fin 256,
      (windowValue u start 8 hfit).eval ρ.int = j.val ∧
        P256.Reference.NormalizedRep ρ out
          (j.val • P256.Reference.generator)) :
    P256.Reference.NormalizedRep ρ out
      ((BitVec.extractLsb' start 8 (u.val.eval ρ)).toNat •
        P256.Reference.generator) := by
  rcases h with ⟨j, hj, hout⟩
  have hw := windowValue_eval hu start 8 hfit
  rw [hw] at hj
  have hjval : j.val =
      (BitVec.extractLsb' start 8 (u.val.eval ρ)).toNat := by
    exact_mod_cast hj.symm
  simpa [hjval] using hout

@[spec] theorem signedRadix32Step_sound
    {u1 u2 : P256.Fn} {q : P256.Reference.Point}
    {i : Nat} {hi : i < 255} {acc : P256.AffineSlope.Point}
    {accPoint : P256.Reference.Point}
    (hu1 : u1.val.Valid ρ) (hu2 : u2.val.Valid ρ)
    (hacc : P256.Reference.NormalizedRep ρ acc accPoint)
    (htable : Radix32TableSpec ρ qTable q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (signedRadix32Step u1 u2 qTable i hi acc)
    ⦃⇓ out => ⌜P256.Reference.NormalizedRep ρ out
      (SignedRadix32StepPoint ρ u1 u2 q i accPoint)⌝⦄ := by
  mvcgen [signedRadix32Step, SignedRadix32StepPoint]
  case vc3.success =>
    intro hdouble
    split <;> mvcgen -trivial
    case vc1.value =>
      exact boothDigit u2 ((254 - i) / 5) (by omega)
    case vc2.q => exact q
    case vc3.hdigit => assumption
    case vc4.htable => exact htable
    case vc5.p => exact accPoint + accPoint
    case vc6.q =>
      exact (boothDigit u2 ((254 - i) / 5) (by omega)).eval ρ.int • q
    case vc7.hP => exact hdouble
    case vc8.hQ => exact SignedRadix32PointSpec.zsmul (by assumption)
    case vc9.success =>
      intro hwithQ
      split <;> mvcgen -trivial
      case vc2 =>
        intro _
        exact accPoint + accPoint +
          (boothDigit u2 ((254 - i) / 5) (by omega)).eval ρ.int • q
      case vc3 =>
        intro _
        exact (BitVec.extractLsb' (254 - i) 8
          (u1.val.eval ρ)).toNat • P256.Reference.generator
      case vc4 =>
        intro _
        exact hwithQ
      case vc5 =>
        intro hlookup
        exact generatorWindowRep_of_lookup hu1 hlookup
      case vc1.h.success.success =>
        intro hout
        unfold SignedRadix32StepPoint
        simp_all [two_nsmul]
      case vc1.isFalse =>
        unfold SignedRadix32StepPoint
        simp_all [two_nsmul]
    case vc1.h =>
      split <;> mvcgen -trivial
      case vc2 =>
        intro _
        exact accPoint + accPoint
      case vc3 =>
        intro _
        exact (BitVec.extractLsb' (254 - i) 8
          (u1.val.eval ρ)).toNat • P256.Reference.generator
      case vc4 =>
        intro _
        exact hdouble
      case vc5 =>
        intro hlookup
        exact generatorWindowRep_of_lookup hu1 hlookup
      case vc1.h.success.success =>
        intro hout
        unfold SignedRadix32StepPoint
        simp_all [two_nsmul]
      case vc1.isFalse =>
        unfold SignedRadix32StepPoint
        simp_all [two_nsmul]

@[spec] theorem signedRadix32Step_complete
    {u1 u2 : P256.Fn} {q : P256.Reference.Point}
    {i : Nat} {hi : i < 255} {acc : P256.AffineSlope.Point}
    {accPoint : P256.Reference.Point}
    (hu1 : u1.val.Valid ρ) (hu2 : u2.val.Valid ρ)
    (haccValid : acc.Valid ρ)
    (hacc : P256.Reference.NormalizedRep ρ acc accPoint)
    (haccOrder : P256.scalarModulus • accPoint = 0)
    (htableValid : Radix32TableValid ρ qTable)
    (htable : Radix32TableSpec ρ qTable q)
    (hq : q ≠ 0) (horder : P256.scalarModulus • q = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (signedRadix32Step u1 u2 qTable i hi acc)
    ⦃⇓ out => ⌜out.Valid ρ ∧ P256.Reference.NormalizedRep ρ out
      (SignedRadix32StepPoint ρ u1 u2 q i accPoint)⌝⦄ := by
  mvcgen [signedRadix32Step, SignedRadix32StepPoint]
  case vc4.hdouble =>
    exact Reference.Aux.no_two_torsion_of_order haccOrder
  case vc5.success =>
    rename_i accD
    intro haccDValid hdouble
    split <;> mvcgen -trivial
    case vc1.hlow =>
      exact (boothDigit_bounds hu2 ((254 - i) / 5) (by omega)).1
    case vc2.hhigh =>
      exact (boothDigit_bounds hu2 ((254 - i) / 5) (by omega)).2
    case vc3.value =>
      exact boothDigit u2 ((254 - i) / 5) (by omega)
    case vc4.q => exact q
    case vc5.hdigit => assumption
    case vc6.htableValid => exact htableValid
    case vc7.htable => exact htable
    case vc8.hq => exact hq
    case vc9.horder => exact horder
    case vc10.q =>
      exact (boothDigit u2 ((254 - i) / 5) (by omega)).eval ρ.int • q
    case vc11.p => exact accPoint + accPoint
    case vc12.hPvalid => exact haccDValid
    case vc13.hQvalid => exact ‹_ ∧ SignedRadix32PointSpec _ _ _ _› |>.1
    case vc14.hP => exact hdouble
    case vc15.hQ =>
      exact SignedRadix32PointSpec.zsmul
        (‹_ ∧ SignedRadix32PointSpec _ _ _ _› |>.2)
    case vc16.hnoTwoTorsion =>
      apply Reference.Aux.no_two_torsion_of_order
      simpa [two_nsmul] using Reference.Aux.order_nsmul haccOrder 2
    case vc17.success =>
      rename_i digit hdigit qPoint hqPoint accQ
      intro haccQValid hwithQ
      split <;> mvcgen -trivial
      case vc1.hd0 =>
        rw [windowValue_eval hu1]
        exact_mod_cast Nat.zero_le _
      case vc2.hdlt =>
        rw [windowValue_eval hu1]
        exact_mod_cast (BitVec.extractLsb' (254 - i) 8
          (u1.val.eval ρ)).isLt
      case vc4 =>
        intro _
        exact accPoint + accPoint +
          (boothDigit u2 ((254 - i) / 5) (by omega)).eval ρ.int • q
      case vc5 =>
        intro _
        exact (BitVec.extractLsb' (254 - i) 8
          (u1.val.eval ρ)).toNat • P256.Reference.generator
      case vc6 => intros; exact haccQValid
      case vc7 => intro hvalid _; exact hvalid
      case vc8 => intro _; exact hwithQ
      case vc9 =>
        intro hlookup
        exact generatorWindowRep_of_lookup hu1 hlookup.2
      case vc10 =>
        intro _
        apply Reference.Aux.no_two_torsion_of_order
        exact Reference.Aux.order_add
          (Reference.Aux.order_nsmul haccOrder 2)
          (order_zsmul horder
            ((boothDigit u2 ((254 - i) / 5) (by omega)).eval ρ.int))
      case vc3.h.success.success =>
        intro houtValid hout
        exact ⟨houtValid, by
          unfold SignedRadix32StepPoint
          simp_all [two_nsmul]⟩
      case vc1.isFalse =>
        exact ⟨haccQValid, by
          unfold SignedRadix32StepPoint
          simp_all [two_nsmul]⟩
    case vc1.h =>
      split <;> mvcgen -trivial
      case vc1.hd0 =>
        rw [windowValue_eval hu1]
        exact_mod_cast Nat.zero_le _
      case vc2.hdlt =>
        rw [windowValue_eval hu1]
        exact_mod_cast (BitVec.extractLsb' (254 - i) 8
          (u1.val.eval ρ)).isLt
      case vc4 =>
        intro _
        exact accPoint + accPoint
      case vc5 =>
        intro _
        exact (BitVec.extractLsb' (254 - i) 8
          (u1.val.eval ρ)).toNat • P256.Reference.generator
      case vc6 => intros; exact haccDValid
      case vc7 => intro hvalid _; exact hvalid
      case vc8 => intro _; exact hdouble
      case vc9 =>
        intro hlookup
        exact generatorWindowRep_of_lookup hu1 hlookup.2
      case vc10 =>
        intro _
        apply Reference.Aux.no_two_torsion_of_order
        exact Reference.Aux.order_nsmul haccOrder 2
      case vc3.h.success.success =>
        intro houtValid hout
        exact ⟨houtValid, by
          unfold SignedRadix32StepPoint
          simp_all [two_nsmul]⟩
      case vc1.isFalse =>
        exact ⟨haccDValid, by
          unfold SignedRadix32StepPoint
          simp_all [two_nsmul]⟩

def SignedRadix32FoldPoint (rho : WF.Valuation) (u1 u2 : P256.Fn)
    (q : P256.Reference.Point) (indices : List Nat) :
    P256.Reference.Point :=
  indices.foldl (fun acc i =>
    SignedRadix32StepPoint rho u1 u2 q i acc)
    ((boothDigit u2 51 (by omega)).eval rho.int • q)

@[spec] theorem signedRadix32JointScalarMul_sound
    {u1 u2 : P256.Fn} {Q : P256.Projective}
    {q : P256.Reference.Point}
    (hu1 : u1.val.Valid ρ) (hu2 : u2.val.Valid ρ)
    (hQ : P256.Reference.Represents ρ
      (P256.AffineSlope.ofElems Q.X Q.Y) q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (signedRadix32JointScalarMul u1 u2 Q)
    ⦃⇓ out => ⌜P256.Reference.NormalizedRep ρ out
      (SignedRadix32FoldPoint ρ u1 u2 q [:255].toList)⌝⦄ := by
  mvcgen -trivial [signedRadix32JointScalarMul, WF.foldRange] invariants
  · ⇓⟨cur, out⟩ => ⌜P256.Reference.NormalizedRep ρ out
      (SignedRadix32FoldPoint ρ u1 u2 q cur.prefix)⌝
  case vc1.q => exact q
  case vc2.hP => exact hQ
  case vc3.value => exact boothDigit u2 51 (by omega)
  case vc4.q => exact q
  case vc5.hdigit => assumption
  case vc6.htable => assumption
  case vc7.q => exact q
  case vc8.accPoint pref cur suff hsplit b hprev =>
    exact SignedRadix32FoldPoint ρ u1 u2 q pref
  case vc9.hu1 => exact hu1
  case vc10.hu2 => exact hu2
  case vc11.hacc => assumption
  case vc12.htable => assumption
  case vc13.success pref cur hstep =>
    unfold SignedRadix32FoldPoint at hstep ⊢
    rw [List.foldl_append]
    simpa using hstep
  case vc14.pre =>
    unfold SignedRadix32FoldPoint
    simpa using SignedRadix32PointSpec.zsmul ‹SignedRadix32PointSpec _ _ _ _›
  case vc15.post.success => intro h; exact h

@[spec] theorem signedRadix32JointScalarMul_complete
    {u1 u2 : P256.Fn} {Q : P256.Projective}
    {q : P256.Reference.Point}
    (hu1 : u1.val.Valid ρ) (hu2 : u2.val.Valid ρ)
    (hQvalid : Q.Valid ρ)
    (hQ : P256.Reference.Represents ρ
      (P256.AffineSlope.ofElems Q.X Q.Y) q)
    (hq : q ≠ 0) (horder : P256.scalarModulus • q = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (signedRadix32JointScalarMul u1 u2 Q)
    ⦃⇓ out => ⌜out.Valid ρ ∧ P256.Reference.NormalizedRep ρ out
      (SignedRadix32FoldPoint ρ u1 u2 q [:255].toList)⌝⦄ := by
  mvcgen -trivial [signedRadix32JointScalarMul, WF.foldRange] invariants
  · ⇓⟨cur, out⟩ => ⌜out.Valid ρ ∧
      P256.Reference.NormalizedRep ρ out
        (SignedRadix32FoldPoint ρ u1 u2 q cur.prefix) ∧
      P256.scalarModulus •
        SignedRadix32FoldPoint ρ u1 u2 q cur.prefix = 0⌝
  case vc1.q => exact q
  case vc2.hPvalid => exact hQvalid
  case vc3.hP => exact hQ
  case vc4.horder => exact horder
  case vc5.hlow => exact (boothDigit_bounds hu2 51 (by omega)).1
  case vc6.hhigh => exact (boothDigit_bounds hu2 51 (by omega)).2
  case vc7.value => exact boothDigit u2 51 (by omega)
  case vc8.q => exact q
  case vc9.hdigit => assumption
  case vc10.htableValid => exact (by aesop)
  case vc11.htable => exact (by aesop)
  case vc12.hq => exact hq
  case vc13.horder => exact horder
  case vc14.q => exact q
  case vc15.accPoint pref cur suff hsplit b hprev =>
    exact SignedRadix32FoldPoint ρ u1 u2 q pref
  case vc16.hu1 => exact hu1
  case vc17.hu2 => exact hu2
  case vc18.haccValid => exact (by aesop)
  case vc19.hacc => exact (by aesop)
  case vc20.haccOrder => exact (by aesop)
  case vc21.htableValid => exact (by aesop)
  case vc22.htable => exact (by aesop)
  case vc23.hq => exact hq
  case vc24.horder => exact horder
  case vc25.success pref cur hstep =>
    rename_i table htable suff hsplit acc hprev
    refine ⟨hstep.1, ?_, ?_⟩
    · unfold SignedRadix32FoldPoint at hstep ⊢
      rw [List.foldl_append]
      simpa using hstep.2
    · unfold SignedRadix32FoldPoint
      rw [List.foldl_append]
      exact SignedRadix32StepPoint.order
        (ρ := ρ) (i := suff) pref.2.2 horder
  case vc26.pre =>
    rename_i table htable digit hdigit initial hinitial
    refine ⟨hinitial.1, ?_, ?_⟩
    · unfold SignedRadix32FoldPoint
      simpa using SignedRadix32PointSpec.zsmul hinitial.2
    · unfold SignedRadix32FoldPoint
      exact order_zsmul horder _
  case vc27.post.success =>
    intro hvalid hnormalized _
    exact ⟨hvalid, hnormalized⟩

def signedRadix32GeneratorCoeff (rho : WF.Valuation) (u1 : P256.Fn) :
    Nat → Nat
  | 0 => 0
  | count + 1 =>
      2 * signedRadix32GeneratorCoeff rho u1 count +
        if h : (254 - count) % 8 = 0 then
          (BitVec.extractLsb' (254 - count) 8 (u1.val.eval rho)).toNat
        else 0

def signedRadix32BoothCoeff (rho : WF.Valuation) (u2 : P256.Fn) :
    Nat → Int
  | 0 => (boothDigit u2 51 (by omega)).eval rho.int
  | count + 1 =>
      2 * signedRadix32BoothCoeff rho u2 count +
        if h : (254 - count) % 5 = 0 then
          (boothDigit u2 ((254 - count) / 5) (by omega)).eval rho.int
        else 0

theorem SignedRadix32FoldPoint_range (u1 u2 : P256.Fn)
    (q : P256.Reference.Point) {count : Nat} (hcount : count ≤ 255) :
    SignedRadix32FoldPoint ρ u1 u2 q (List.range count) =
      signedRadix32GeneratorCoeff ρ u1 count • P256.Reference.generator +
        signedRadix32BoothCoeff ρ u2 count • q := by
  induction count with
  | zero =>
      simp [SignedRadix32FoldPoint, signedRadix32GeneratorCoeff,
        signedRadix32BoothCoeff]
  | succ count ih =>
      rw [List.range_succ, SignedRadix32FoldPoint, List.foldl_append]
      change SignedRadix32StepPoint ρ u1 u2 q count
        (SignedRadix32FoldPoint ρ u1 u2 q (List.range count)) = _
      rw [ih (by omega)]
      unfold SignedRadix32StepPoint
      simp only [signedRadix32GeneratorCoeff, signedRadix32BoothCoeff]
      split <;> split
      all_goals
        simp_all [nsmul_add, add_nsmul, add_zsmul, mul_zsmul]
        have hgeneratorDouble :
            2 • (signedRadix32GeneratorCoeff ρ u1 count •
              P256.Reference.generator) =
              (2 * signedRadix32GeneratorCoeff ρ u1 count) •
                P256.Reference.generator := by
          rw [← mul_nsmul, Nat.mul_comm]
        rw [hgeneratorDouble]
        abel

theorem signedRadix32BoothCoeff_five_mul (u2 : P256.Fn)
    {count : Nat} (hcount : count ≤ 51) :
    signedRadix32BoothCoeff ρ u2 (5 * count) = boothHorner ρ u2 count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have hcountLt : count < 51 := by omega
      have h0 : (254 - (5 * count)) % 5 ≠ 0 := by omega
      have h1 : (254 - (5 * count + 1)) % 5 ≠ 0 := by omega
      have h2 : (254 - (5 * count + 2)) % 5 ≠ 0 := by omega
      have h3 : (254 - (5 * count + 3)) % 5 ≠ 0 := by omega
      have h4 : (254 - (5 * count + 4)) % 5 = 0 := by omega
      have hindex : (254 - (5 * count + 4)) / 5 = 50 - count := by omega
      rw [show 5 * (count + 1) = 5 * count + 5 by omega]
      simp only [show 5 * count + 5 = ((((5 * count + 1) + 1) + 1) + 1) + 1
        by omega, signedRadix32BoothCoeff]
      rw [dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h4,
        ih (by omega), boothHorner, dif_pos hcountLt]
      simp only [hindex]
      ring

theorem signedRadix32GeneratorCoeff_event (u1 : P256.Fn)
    {block : Nat} (hblock : block < 32) :
    signedRadix32GeneratorCoeff ρ u1 (8 * block + 7) =
      scalarPrefix ρ u1 (block + 1) := by
  induction block with
  | zero =>
      rw [show 8 * 0 + 7 = ((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1 by
        omega]
      simp only [signedRadix32GeneratorCoeff]
      norm_num
      rw [scalarPrefix_succ (ρ := ρ) (k := u1) (i := 0) (by omega),
        scalarPrefix_zero]
      simp [byteValue]
  | succ block ih =>
      have hblockLt : block + 1 < 32 := by omega
      let start := 8 * block + 7
      have h0 : (254 - start) % 8 ≠ 0 := by dsimp [start]; omega
      have h1 : (254 - (start + 1)) % 8 ≠ 0 := by dsimp [start]; omega
      have h2 : (254 - (start + 2)) % 8 ≠ 0 := by dsimp [start]; omega
      have h3 : (254 - (start + 3)) % 8 ≠ 0 := by dsimp [start]; omega
      have h4 : (254 - (start + 4)) % 8 ≠ 0 := by dsimp [start]; omega
      have h5 : (254 - (start + 5)) % 8 ≠ 0 := by dsimp [start]; omega
      have h6 : (254 - (start + 6)) % 8 ≠ 0 := by dsimp [start]; omega
      have h7 : (254 - (start + 7)) % 8 = 0 := by dsimp [start]; omega
      have hindex : 254 - (start + 7) = 248 - 8 * (block + 1) := by
        dsimp [start]
        omega
      rw [show 8 * (block + 1) + 7 = start + 8 by dsimp [start]; omega]
      simp only [show start + 8 = (((((((start + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1
        by omega, signedRadix32GeneratorCoeff]
      rw [dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4,
        dif_neg h5, dif_neg h6, dif_pos h7, ih (by omega)]
      rw [scalarPrefix_succ (ρ := ρ) (k := u1) (i := block + 1) hblockLt]
      simp only [hindex, byteValue]
      ring

theorem signedRadix32GeneratorCoeff_full (u1 : P256.Fn) :
    signedRadix32GeneratorCoeff ρ u1 255 = (u1.val.eval ρ).toNat := by
  rw [show 255 = 8 * 31 + 7 by norm_num,
    signedRadix32GeneratorCoeff_event (ρ := ρ) u1 (block := 31) (by omega),
    scalarPrefix_full]

theorem signedRadix32BoothCoeff_full {u2 : P256.Fn}
    (hu2 : u2.val.Valid ρ) :
    signedRadix32BoothCoeff ρ u2 255 = ((u2.val.eval ρ).toNat : Int) := by
  rw [show 255 = 5 * 51 by norm_num,
    signedRadix32BoothCoeff_five_mul (ρ := ρ) u2 (count := 51) (by omega),
    boothHorner_full hu2]

theorem SignedRadix32FoldPoint_full (u1 u2 : P256.Fn)
    (q : P256.Reference.Point) (hu2 : u2.val.Valid ρ) :
    SignedRadix32FoldPoint ρ u1 u2 q [:255].toList =
      (u1.val.eval ρ).toNat • P256.Reference.generator +
        (u2.val.eval ρ).toNat • q := by
  rw [show [:255].toList = List.range 255 by rfl,
    SignedRadix32FoldPoint_range u1 u2 q (by omega),
    signedRadix32GeneratorCoeff_full,
    signedRadix32BoothCoeff_full hu2]
  rfl

theorem signedRadix32FoldPoint_eq_verificationPoint
    {digest : U 256} {sig : Signature}
    {r s sInv z u1Relaxed u2Relaxed u1 u2 : P256.Fn}
    (hdigest : digest.Valid ρ)
    (hr : r.Valid ρ) (hsInv : sInv.Valid ρ)
    (hu1 : u1.Valid ρ) (hu2 : u2.Valid ρ)
    (hrNat : r.evalNat ρ = (sig.r.eval ρ).toNat)
    (hsNat : s.evalNat ρ = (sig.s.eval ρ).toNat)
    (hsMul : (s.evalNat ρ : ZMod P256.scalar.modulus) *
      (sInv.evalNat ρ : ZMod P256.scalar.modulus) = 1)
    (hz : Modular.Lazy.evalElemZMod P256.scalar z ρ =
      Int.castRingHom (ZMod P256.scalar.modulus) (digest.intVal.eval ρ.int))
    (hu1Relaxed : Modular.Lazy.evalElemZMod P256.scalar u1Relaxed ρ =
      Modular.Lazy.evalElemZMod P256.scalar z ρ *
        Modular.Lazy.evalElemZMod P256.scalar sInv ρ)
    (hu2Relaxed : Modular.Lazy.evalElemZMod P256.scalar u2Relaxed ρ =
      Modular.Lazy.evalElemZMod P256.scalar r ρ *
        Modular.Lazy.evalElemZMod P256.scalar sInv ρ)
    (hu1Canonical : Modular.Lazy.evalElemZMod P256.scalar u1 ρ =
      Modular.Lazy.evalElemZMod P256.scalar u1Relaxed ρ)
    (hu2Canonical : Modular.Lazy.evalElemZMod P256.scalar u2 ρ =
      Modular.Lazy.evalElemZMod P256.scalar u2Relaxed ρ)
    (publicKey : Reference.Point) :
    SignedRadix32FoldPoint ρ u1 u2 publicKey [:255].toList =
      Reference.verificationPoint (digest.eval ρ).toNat
        (sig.r.eval ρ).toNat (sig.s.eval ρ).toNat publicKey := by
  rw [SignedRadix32FoldPoint_full u1 u2 publicKey hu2.1]
  rw [← JointFoldPoint_full (ρ := ρ) u1 u2 publicKey]
  exact jointFoldPoint_eq_verificationPoint hdigest hr hsInv hu1 hu2
    hrNat hsNat hsMul hz hu1Relaxed hu2Relaxed hu1Canonical hu2Canonical
    publicKey

end Freigen.F2Z.Examples.EcdsaP256
