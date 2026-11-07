import Freigen.F2Z.Examples.EcdsaP256.DirectTerminalBlockImpl
import Freigen.F2Z.Examples.EcdsaP256.DirectTerminalLemmas
import Freigen.F2Z.Examples.EcdsaP256.Lemmas

/-!
# Semantics of block-comparator direct terminal acceptance

The selected outer byte and inner bit prove the strict comparison
`r < p - n`.  Inner predicates need not be unique; the circuit only requires
the selector witnesses themselves to be one-hot.
-/

namespace Freigen.F2Z.Examples.EcdsaP256

open Std.Do
open scoped Std.Do
open Modular
open P256
open AffineSlope AffineSlope.Aux

namespace DeltaBlock

abbrev delta : Nat := P256.base.modulus - P256.scalar.modulus

theorem delta_lt_pow128 : delta < 2 ^ 128 := by
  norm_num [delta, P256.base, P256.baseModulus,
    P256.scalar, P256.scalarModulus]

theorem delta_lt_pow127 : delta < 2 ^ 127 := by
  norm_num [delta, P256.base, P256.baseModulus,
    P256.scalar, P256.scalarModulus]

def MostSignificantDifference (r k d : Nat) : Prop :=
  d < 128 ∧
    r / 2 ^ d + 1 = k / 2 ^ d ∧
    r / 2 ^ (d + 1) = k / 2 ^ (d + 1)

theorem exists_mostSignificantDifference {r k : Nat}
    (hrk : r < k) (hk : k < 2 ^ 128) :
    ∃ d, MostSignificantDifference r k d := by
  have hr : r < 2 ^ 128 := hrk.trans hk
  let pred : Nat → Prop := fun i => r / 2 ^ i = k / 2 ^ i
  have hex : ∃ i, pred i := by
    refine ⟨128, ?_⟩
    simp only [pred]
    rw [Nat.div_eq_of_lt hr, Nat.div_eq_of_lt hk]
  let first := Nat.find hex
  have hfirst : pred first := Nat.find_spec hex
  have hfirst_le : first ≤ 128 := by
    apply Nat.find_min' hex
    simp only [pred]
    rw [Nat.div_eq_of_lt hr, Nat.div_eq_of_lt hk]
  have hfirst_pos : 0 < first := by
    by_contra h
    have hzero : first = 0 := by omega
    rw [hzero] at hfirst
    simp only [pred, pow_zero, Nat.div_one] at hfirst
    omega
  let d := first - 1
  have hd_succ : d + 1 = first := by
    dsimp [d]
    omega
  have hprev_ne : r / 2 ^ d ≠ k / 2 ^ d := by
    intro heq
    have hmin : first ≤ d := Nat.find_min' hex (by
      simpa only [pred] using heq)
    omega
  have hprefix_lt : r / 2 ^ d < k / 2 ^ d := by
    have hle := Nat.div_le_div_right hrk.le (c := 2 ^ d)
    omega
  have hhigher : r / 2 ^ (d + 1) = k / 2 ^ (d + 1) := by
    rw [hd_succ]
    exact hfirst
  have hhalf : (r / 2 ^ d) / 2 = (k / 2 ^ d) / 2 := by
    simpa only [Nat.div_div_eq_div_mul, pow_succ] using hhigher
  have hrmod := Nat.mod_lt (r / 2 ^ d) (by omega : 0 < 2)
  have hkmod := Nat.mod_lt (k / 2 ^ d) (by omega : 0 < 2)
  have hrdecomp := Nat.mod_add_div (r / 2 ^ d) 2
  have hkdecomp := Nat.mod_add_div (k / 2 ^ d) 2
  refine ⟨d, ?_, ?_, hhigher⟩ <;> omega

def CorrectedSelectorSemantics (r k b j : Nat) : Prop :=
  b < 16 ∧ j < 8 ∧
    r / 2 ^ (8 * (b + 1)) = k / 2 ^ (8 * (b + 1)) ∧
    r / 2 ^ (8 * b + j) + 1 = k / 2 ^ (8 * b + j)

theorem correctedSelector_sound {r k b j : Nat}
    (h : CorrectedSelectorSemantics r k b j) : r < k := by
  rcases h with ⟨_, _, _, hprefix⟩
  by_contra hnot
  have hle : k ≤ r := by omega
  have hdiv := Nat.div_le_div_right hle (c := 2 ^ (8 * b + j))
  omega

theorem correctedSelector_complete {r k : Nat}
    (hrk : r < k) (hk : k < 2 ^ 128) :
    ∃ b j, CorrectedSelectorSemantics r k b j := by
  rcases exists_mostSignificantDifference hrk hk with
    ⟨d, hdlt, hprefix, hhigher⟩
  let b := d / 8
  let j := d % 8
  have hb : b < 16 := by
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < 8)]
    simpa [b] using hdlt
  have hj : j < 8 := Nat.mod_lt d (by omega)
  have hd : 8 * b + j = d := by
    dsimp [b, j]
    omega
  have hblockExp : d + 1 ≤ 8 * (b + 1) := by omega
  let gap := 8 * (b + 1) - (d + 1)
  have hgap : d + 1 + gap = 8 * (b + 1) := by
    dsimp [gap]
    omega
  have hhigherBlock := congrArg (fun x : Nat => x / 2 ^ gap) hhigher
  have hhigherBlock' :
      r / 2 ^ (8 * (b + 1)) = k / 2 ^ (8 * (b + 1)) := by
    simpa only [Nat.div_div_eq_div_mul, ← pow_add, hgap]
      using hhigherBlock
  refine ⟨b, j, hb, hj, hhigherBlock', ?_⟩
  simpa only [hd] using hprefix

def CorrectedBlockEquations (r k b j selected : Nat) : Prop :=
  b < 16 ∧ j < 8 ∧ selected < 2 ^ 8 ∧
    r / 2 ^ (8 * b) =
      selected + 2 ^ 8 * (k / 2 ^ (8 * b + 8)) ∧
    selected / 2 ^ j + 1 =
      k / 2 ^ (8 * b + j) % 2 ^ (8 - j)

private theorem quotient_decompose (x start width : Nat) :
    x / 2 ^ start =
      x / 2 ^ start % 2 ^ width +
        2 ^ width * (x / 2 ^ (start + width)) := by
  have h := Nat.mod_add_div (x / 2 ^ start) (2 ^ width)
  rw [Nat.div_div_eq_div_mul, ← pow_add] at h
  omega

theorem correctedBlockEquations_sound {r k b j selected : Nat}
    (h : CorrectedBlockEquations r k b j selected) :
    CorrectedSelectorSemantics r k b j := by
  rcases h with ⟨hb, hj, hselected, houter, hinner⟩
  have hjle : j ≤ 8 := hj.le
  have hpow : 2 ^ 8 = 2 ^ j * 2 ^ (8 - j) := by
    rw [← pow_add, Nat.add_sub_of_le hjle]
  have hhigh := congrArg (fun x : Nat => x / 2 ^ 8) houter
  have hhigh' :
      r / 2 ^ (8 * (b + 1)) = k / 2 ^ (8 * (b + 1)) := by
    rw [Nat.div_div_eq_div_mul] at hhigh
    have hselectedDiv : selected / 2 ^ 8 = 0 :=
      Nat.div_eq_of_lt hselected
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 8),
      hselectedDiv, zero_add] at hhigh
    simpa only [← pow_add, Nat.mul_add] using hhigh
  have hrPrefix := congrArg (fun x : Nat => x / 2 ^ j) houter
  have hrPrefix' :
      r / 2 ^ (8 * b + j) = selected / 2 ^ j +
        2 ^ (8 - j) * (k / 2 ^ (8 * b + 8)) := by
    rw [Nat.div_div_eq_div_mul] at hrPrefix
    rw [hpow, Nat.mul_assoc,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos j)] at hrPrefix
    simpa only [← pow_add] using hrPrefix
  have hkPrefix := quotient_decompose k (8 * b + j) (8 - j)
  have hkPrefix' :
      k / 2 ^ (8 * b + j) =
        k / 2 ^ (8 * b + j) % 2 ^ (8 - j) +
          2 ^ (8 - j) * (k / 2 ^ (8 * b + 8)) := by
    have hexp : 8 * b + j + (8 - j) = 8 * b + 8 := by omega
    simpa only [hexp] using hkPrefix
  refine ⟨hb, hj, hhigh', ?_⟩
  omega

theorem correctedBlockEquations_strict {r k b j selected : Nat}
    (h : CorrectedBlockEquations r k b j selected) : r < k :=
  correctedSelector_sound (correctedBlockEquations_sound h)

theorem correctedSelector_toBlockEquations {r k b j : Nat}
    (h : CorrectedSelectorSemantics r k b j) :
    ∃ selected, CorrectedBlockEquations r k b j selected := by
  rcases h with ⟨hb, hj, hhigh, hprefix⟩
  let selected := r / 2 ^ (8 * b) % 2 ^ 8
  have hselected : selected < 2 ^ 8 :=
    Nat.mod_lt _ (Nat.two_pow_pos 8)
  have houterDecomp := quotient_decompose r (8 * b) 8
  have houter :
      r / 2 ^ (8 * b) =
        selected + 2 ^ 8 * (k / 2 ^ (8 * b + 8)) := by
    have hexp : 8 * (b + 1) = 8 * b + 8 := by omega
    rw [hexp] at hhigh
    simpa only [selected, hhigh] using houterDecomp
  have hjle : j ≤ 8 := hj.le
  have hpow : 2 ^ 8 = 2 ^ j * 2 ^ (8 - j) := by
    rw [← pow_add, Nat.add_sub_of_le hjle]
  have hrPrefix := congrArg (fun x : Nat => x / 2 ^ j) houter
  have hrPrefix' :
      r / 2 ^ (8 * b + j) = selected / 2 ^ j +
        2 ^ (8 - j) * (k / 2 ^ (8 * b + 8)) := by
    rw [Nat.div_div_eq_div_mul] at hrPrefix
    rw [hpow, Nat.mul_assoc,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos j)] at hrPrefix
    simpa only [← pow_add] using hrPrefix
  have hkPrefix := quotient_decompose k (8 * b + j) (8 - j)
  have hkPrefix' :
      k / 2 ^ (8 * b + j) =
        k / 2 ^ (8 * b + j) % 2 ^ (8 - j) +
          2 ^ (8 - j) * (k / 2 ^ (8 * b + 8)) := by
    have hexp : 8 * b + j + (8 - j) = 8 * b + 8 := by omega
    simpa only [hexp] using hkPrefix
  refine ⟨selected, hb, hj, hselected, houter, ?_⟩
  omega

theorem correctedBlockEquations_complete {r k : Nat}
    (hrk : r < k) (hk : k < 2 ^ 128) :
    ∃ b j selected, CorrectedBlockEquations r k b j selected := by
  rcases correctedSelector_complete hrk hk with ⟨b, j, h⟩
  rcases correctedSelector_toBlockEquations h with ⟨selected, hs⟩
  exact ⟨b, j, selected, hs⟩

theorem correctedBlockEquations_complete_selected {r k : Nat}
    (hrk : r < k) (hk : k < 2 ^ 128) :
    ∃ b j,
      CorrectedBlockEquations r k b j (r / 2 ^ (8 * b) % 2 ^ 8) := by
  rcases correctedBlockEquations_complete hrk hk with
    ⟨b, j, selected, hb, hj, hselected, houter, hinner⟩
  have hselectedEq : r / 2 ^ (8 * b) % 2 ^ 8 = selected := by
    calc
      r / 2 ^ (8 * b) % 2 ^ 8 =
          (selected + 2 ^ 8 * (k / 2 ^ (8 * b + 8))) % 2 ^ 8 :=
        congrArg (· % 2 ^ 8) houter
      _ = selected % 2 ^ 8 := by simp [Nat.add_mod, Nat.mul_mod]
      _ = selected := Nat.mod_eq_of_lt hselected
  refine ⟨b, j, ?_⟩
  rw [hselectedEq]
  exact ⟨hb, hj, hselected, houter, hinner⟩

theorem correctedBlockEquations_iff {r k : Nat} (hk : k < 2 ^ 128) :
    (∃ b j selected, CorrectedBlockEquations r k b j selected) ↔ r < k := by
  constructor
  · rintro ⟨b, j, selected, h⟩
    exact correctedBlockEquations_strict h
  · exact fun hrk => correctedBlockEquations_complete hrk hk

theorem corrected_accepts_delta_sub_one :
    ∃ b j selected,
      CorrectedBlockEquations (delta - 1) delta b j selected := by
  apply correctedBlockEquations_complete
  · have hdelta : 0 < delta := by
      norm_num [delta, P256.base, P256.baseModulus,
        P256.scalar, P256.scalarModulus]
    omega
  · exact delta_lt_pow128

theorem inner_offsets_not_unique_at_boundary :
    CorrectedBlockEquations (delta - 1) delta 0 0
        ((delta - 1) % 256) ∧
      CorrectedBlockEquations (delta - 1) delta 0 1
        ((delta - 1) % 256) := by
  norm_num [CorrectedBlockEquations, delta, P256.base,
    P256.baseModulus, P256.scalar, P256.scalarModulus]

theorem correctedComparator_iff_slack127 {r : Nat} :
    (∃ b j selected, CorrectedBlockEquations r delta b j selected) ↔
      ∃ slack, slack < 2 ^ 127 ∧ r + slack + 1 = delta := by
  rw [correctedBlockEquations_iff delta_lt_pow128]
  constructor
  · intro hr
    refine ⟨delta - 1 - r, ?_, ?_⟩
    · exact (Nat.sub_le _ _).trans_lt
        ((Nat.sub_le delta 1).trans_lt delta_lt_pow127)
    · omega
  · rintro ⟨slack, _, heq⟩
    omega

end DeltaBlock

theorem deltaBlockPairSatisfies_iff {r b j : Nat}
    (hb : b < 16) (hj : j < 8) :
    deltaBlockPairSatisfies r b j = true ↔
      DeltaBlock.CorrectedBlockEquations r DeltaBlock.delta b j
        (r / 2 ^ (8 * b) % 2 ^ 8) := by
  simp only [deltaBlockPairSatisfies, Bool.and_eq_true]
  unfold DeltaBlock.CorrectedBlockEquations
  constructor
  · rintro ⟨houter, hinner⟩
    exact ⟨hb, hj, Nat.mod_lt _ (Nat.two_pow_pos 8),
      by simpa [DeltaBlock.delta, blockTerminalDelta] using houter,
      by simpa [DeltaBlock.delta, blockTerminalDelta] using hinner⟩
  · rintro ⟨_, _, _, houter, hinner⟩
    exact ⟨by simpa [DeltaBlock.delta, blockTerminalDelta] using houter,
      by simpa [DeltaBlock.delta, blockTerminalDelta] using hinner⟩

theorem exists_deltaBlockPairSatisfies {r : Nat}
    (hr : r < DeltaBlock.delta) :
    ∃ index, index < 16 * 8 ∧
      deltaBlockPairSatisfies r (index / 8) (index % 8) = true := by
  rcases DeltaBlock.correctedBlockEquations_complete_selected hr
      DeltaBlock.delta_lt_pow128 with ⟨b, j, hpair⟩
  refine ⟨8 * b + j, ?_, ?_⟩
  · rcases hpair with ⟨hb, hj, _⟩
    omega
  · have hb : b < 16 := hpair.1
    have hj : j < 8 := hpair.2.1
    have hdiv : (8 * b + j) / 8 = b := by omega
    have hmod : (8 * b + j) % 8 = j := by omega
    rw [hdiv, hmod]
    exact (deltaBlockPairSatisfies_iff hb hj).2 hpair

theorem firstDeltaBlockPair_spec {r : Nat}
    (hr : r < DeltaBlock.delta) :
    let pair := firstDeltaBlockPair r
    pair.1 < 16 ∧ pair.2 < 8 ∧
      DeltaBlock.CorrectedBlockEquations r DeltaBlock.delta pair.1 pair.2
        (r / 2 ^ (8 * pair.1) % 2 ^ 8) := by
  rcases exists_deltaBlockPairSatisfies hr with ⟨index, hindex, hsatisfies⟩
  have hisSome :
      ((List.range (16 * 8)).find? fun index =>
        deltaBlockPairSatisfies r (index / 8) (index % 8)).isSome = true := by
    rw [List.find?_isSome]
    exact ⟨index, List.mem_range.mpr hindex, hsatisfies⟩
  cases hfind : (List.range (16 * 8)).find? fun index =>
      deltaBlockPairSatisfies r (index / 8) (index % 8) with
  | none => simp [hfind] at hisSome
  | some found =>
      have hfoundMem := List.mem_of_find?_eq_some hfind
      have hfoundLt : found < 16 * 8 := List.mem_range.mp hfoundMem
      have hfoundSat := List.find?_some hfind
      have hb : found / 8 < 16 := by omega
      have hj : found % 8 < 8 := Nat.mod_lt _ (by omega)
      simp only [firstDeltaBlockPair, hfind]
      exact ⟨hb, hj, (deltaBlockPairSatisfies_iff hb hj).1 hfoundSat⟩

theorem deltaScalarBitsFrom_eval_windowValue {ρ : WF.Valuation}
    (r : Fn) (start : Nat) (hstart : start ≤ 256) :
    (deltaScalarBitsFrom r start).eval ρ.int =
      (windowValue r start (256 - start) (by omega)).eval ρ.int := by
  unfold deltaScalarBitsFrom windowValue
  simp only [LC.eval_sum, apply_ite, LC.eval_nsmul, nsmul_eq_mul,
    LC.eval_zero]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (fun i hi => (⟨i.val - start, by
      have := (Finset.mem_filter.mp hi).2
      omega⟩ : Fin (256 - start))) ?_ ?_ ?_ ?_
  · simp
  · intro a ha b hb hab
    apply Fin.eq_of_val_eq
    have habv := congrArg Fin.val hab
    simp only at habv
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    omega
  · intro j hj
    let i : Fin 256 := ⟨start + j.val, by omega⟩
    refine ⟨i, ?_, ?_⟩
    · simp [i]
    · apply Fin.eq_of_val_eq
      simp [i]
  · intro i hi
    simp only
    have hi' : start ≤ i.val := (Finset.mem_filter.mp hi).2
    have hbound : start + (i.val - start) < 256 := by omega
    let j : Fin 256 := ⟨start + (i.val - start), hbound⟩
    have hij : i = j := by
      apply Fin.eq_of_val_eq
      simp [j]
      omega
    have hget : r.val.intBits[i] =
        r.val.intBits[start + (i.val - start)]'(by omega) := by
      change r.val.intBits[i] = r.val.intBits[j]
      exact congrArg (fun x : Fin 256 => r.val.intBits[x]) hij
    rw [hget]

theorem deltaScalarBitsFrom_eval (r : Fn) (hr : r.val.Valid ρ)
    (start : Nat) (hstart : start ≤ 256) :
    (deltaScalarBitsFrom r start).eval ρ.int =
      (r.evalNat ρ / 2 ^ start : Nat) := by
  rw [deltaScalarBitsFrom_eval_windowValue r start hstart,
    windowValue_eval hr]
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have hlt : (r.val.eval ρ).toNat / 2 ^ start < 2 ^ (256 - start) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos start)]
    rw [← pow_add, Nat.sub_add_cancel hstart]
    exact (r.val.eval ρ).isLt
  rw [Nat.mod_eq_of_lt hlt]
  unfold Modular.Elem.evalNat
  rw [U.intVal_eval_eq_eval_toNat r.val hr]
  simp

theorem deltaSelectedBitsFrom_eval_window {ρ : WF.Valuation}
    (selected : U 8) (start : Nat) (hstart : start ≤ 8) :
    (deltaSelectedBitsFrom selected start).eval ρ.int =
      (∑ j : Fin (8 - start), (2 ^ j.val : Int) *
        (selected.intBits[start + j.val]'(by omega)).eval ρ.int) := by
  unfold deltaSelectedBitsFrom
  simp only [LC.eval_sum, apply_ite, LC.eval_nsmul, nsmul_eq_mul,
    LC.eval_zero]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (fun i hi => (⟨i.val - start, by
      have := (Finset.mem_filter.mp hi).2
      omega⟩ : Fin (8 - start))) ?_ ?_ ?_ ?_
  · simp
  · intro a ha b hb hab
    apply Fin.eq_of_val_eq
    have habv := congrArg Fin.val hab
    simp only at habv
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    omega
  · intro j hj
    let i : Fin 8 := ⟨start + j.val, by omega⟩
    refine ⟨i, ?_, ?_⟩
    · simp [i]
    · apply Fin.eq_of_val_eq
      simp [i]
  · intro i hi
    simp only
    have hi' : start ≤ i.val := (Finset.mem_filter.mp hi).2
    have hbound : start + (i.val - start) < 8 := by omega
    let j : Fin 8 := ⟨start + (i.val - start), hbound⟩
    have hij : i = j := by
      apply Fin.eq_of_val_eq
      simp [j]
      omega
    have hget : selected.intBits[i] =
        selected.intBits[start + (i.val - start)]'(by omega) := by
      change selected.intBits[i] = selected.intBits[j]
      exact congrArg (fun x : Fin 8 => selected.intBits[x]) hij
    rw [hget]
    norm_cast

theorem deltaSelectedBitsFrom_eval (selected : U 8)
    (hselected : selected.Valid ρ) (start : Nat) (hstart : start ≤ 8) :
    (deltaSelectedBitsFrom selected start).eval ρ.int =
      ((selected.eval ρ).toNat / 2 ^ start : Nat) := by
  rw [deltaSelectedBitsFrom_eval_window selected start hstart]
  let f : Fin (8 - start) → Bool := fun j =>
    selected.bits.bitsLE[start + j.val]'(by omega) |>.eval ρ.bool
  have heval := U.eval_eq_ofFnLE selected hselected
  have hextract : BitVec.extractLsb' start (8 - start) (selected.eval ρ) =
      BitVec.ofFnLE f := by
    apply BitVec.eq_of_getElem_eq
    intro j hj
    rw [BitVec.getElem_extractLsb' hj, heval,
      BitVec.getLsbD_eq_getElem (by omega)]
    simp [BitVec.getElem_ofFnLE, f]
  have hbits :
      (∑ j : Fin (8 - start), (2 ^ j.val : Int) *
        (selected.intBits[start + j.val]'(by omega)).eval ρ.int) =
      ∑ j : Fin (8 - start), (2 ^ j.val : Int) * (f j).toInt := by
    apply Finset.sum_congr rfl
    intro j hj
    apply congrArg (fun z : Int => (2 ^ j.val : Int) * z)
    simpa [f] using hselected ⟨start + j.val, by omega⟩
  rw [hbits]
  rw [← Aux.natCast_ofBits_eq_sum]
  rw [← BitVec.toNat_ofFnLE, ← hextract,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have hlt : (selected.eval ρ).toNat / 2 ^ start < 2 ^ (8 - start) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos start)]
    rw [← pow_add, Nat.sub_add_cancel hstart]
    exact (selected.eval ρ).isLt
  rw [Nat.mod_eq_of_lt hlt]

private theorem validBit_zero_or_one {u : U n} (hu : u.Valid ρ)
    (i : Fin n) :
    u.intBits[i].eval ρ.int = 0 ∨ u.intBits[i].eval ρ.int = 1 := by
  have hi := hu i
  cases hb : u.bits.bitsLE[i].eval ρ.bool <;>
    rw [hb] at hi <;> simp at hi
  · exact Or.inl hi
  · exact Or.inr hi

private def deltaBlockHintBits
    (qBaseNat qScalarNat rNat block offset : Nat) : Vector Bool 34 :=
  Vector.ofFn fun i =>
    if _ : i.val = 0 then qBaseNat.testBit 0
    else if _ : i.val = 1 then qScalarNat.testBit 0
    else if _ : i.val < 18 then
      qScalarNat.testBit 0 && i.val - 2 = block
    else if _ : i.val < 26 then
      qScalarNat.testBit 0 && i.val - 18 = offset
    else rNat.testBit (8 * block + (i.val - 26))

private theorem firstDeltaBlockPair_bounds (r : Nat) :
    (firstDeltaBlockPair r).1 < 16 ∧ (firstDeltaBlockPair r).2 < 8 := by
  unfold firstDeltaBlockPair
  split
  · rename_i index hindex
    have hmem := List.mem_of_find?_eq_some hindex
    have hlt : index < 16 * 8 := List.mem_range.mp hmem
    exact ⟨by omega, Nat.mod_lt _ (by omega)⟩
  · norm_num

private theorem deltaBlockBaseQWord_value
    {qBaseNat qScalarNat rNat block offset : Nat}
    (hqBaseLt : qBaseNat < 2) {qBase : U 1}
    (hqBase : U.Rel ρ qBase
      (Word.eval ρ.bool (deltaBlockBaseQWord
        (Vector.map LC.ofConst
          (deltaBlockHintBits qBaseNat qScalarNat rNat block offset))))) :
    qBase.intVal.eval ρ.int = qBaseNat := by
  rw [U.Rel.intVal hqBase]
  have hwordInt := congrArg Int.ofNat
    (Modular.Aux.constWord_eval_toNat (n := 1) qBaseNat hqBaseLt ρ)
  simpa [deltaBlockBaseQWord, deltaBlockHintBits, Function.comp_def]
    using hwordInt

private theorem deltaBlockScalarQWord_value
    {qBaseNat qScalarNat rNat block offset : Nat}
    (hqScalarLt : qScalarNat < 2) {qScalar : U 1}
    (hqScalar : U.Rel ρ qScalar
      (Word.eval ρ.bool (deltaBlockScalarQWord
        (Vector.map LC.ofConst
          (deltaBlockHintBits qBaseNat qScalarNat rNat block offset))))) :
    qScalar.intVal.eval ρ.int = qScalarNat := by
  rw [U.Rel.intVal hqScalar]
  have hwordInt := congrArg Int.ofNat
    (Modular.Aux.constWord_eval_toNat (n := 1) qScalarNat hqScalarLt ρ)
  simpa [deltaBlockScalarQWord, deltaBlockHintBits, Function.comp_def]
    using hwordInt

private theorem deltaBlockOuterWord_bit_value
    {qBaseNat qScalarNat rNat block offset : Nat}
    (hqScalarLt : qScalarNat < 2) {outer : U 16}
    (houter : U.Rel ρ outer
      (Word.eval ρ.bool (deltaBlockOuterWord
        (Vector.map LC.ofConst
          (deltaBlockHintBits qBaseNat qScalarNat rNat block offset)))))
    (i : Fin 16) :
    outer.intBits[i].eval ρ.int =
      if qScalarNat = 1 ∧ i.val = block then 1 else 0 := by
  have hi := houter.1 i
  have hiBool := congrArg (fun x : BitVec 16 => x[i.val]) houter.word_eval
  have hiRange : i.val + 2 < 18 := by omega
  interval_cases qScalarNat <;> by_cases hib : i.val = block <;>
    simp_all [deltaBlockOuterWord, deltaBlockHintBits,
      Word.eval, Function.comp_def]

private theorem deltaBlockInnerWord_bit_value
    {qBaseNat qScalarNat rNat block offset : Nat}
    (hqScalarLt : qScalarNat < 2) {inner : U 8}
    (hinner : U.Rel ρ inner
      (Word.eval ρ.bool (deltaBlockInnerWord
        (Vector.map LC.ofConst
          (deltaBlockHintBits qBaseNat qScalarNat rNat block offset)))))
    (j : Fin 8) :
    inner.intBits[j].eval ρ.int =
      if qScalarNat = 1 ∧ j.val = offset then 1 else 0 := by
  have hj := hinner.1 j
  have hjBool := congrArg (fun x : BitVec 8 => x[j.val]) hinner.word_eval
  have hjRange : j.val + 18 < 26 := by omega
  interval_cases qScalarNat <;> by_cases hjo : j.val = offset <;>
    simp_all [deltaBlockInnerWord, deltaBlockHintBits,
      Word.eval, Function.comp_def]

private theorem deltaBlockOuterWord_sum_value
    {qBaseNat qScalarNat rNat block offset : Nat}
    (hqScalarLt : qScalarNat < 2) (hblock : block < 16)
    {outer : U 16}
    (houter : U.Rel ρ outer
      (Word.eval ρ.bool (deltaBlockOuterWord
        (Vector.map LC.ofConst
          (deltaBlockHintBits qBaseNat qScalarNat rNat block offset))))) :
    (∑ i : Fin 16, outer.intBits[i].eval ρ.int) = qScalarNat := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp
      (Nat.lt_succ_iff.mp hqScalarLt) with hq | hq
  · subst qScalarNat
    simp_rw [deltaBlockOuterWord_bit_value (by norm_num) houter]
    simp
  · subst qScalarNat
    simp_rw [deltaBlockOuterWord_bit_value (by norm_num) houter]
    let chosen : Fin 16 := ⟨block, hblock⟩
    have hiff (i : Fin 16) : i.val = block ↔ i = chosen := by
      simp [chosen, Fin.ext_iff]
    simp only [true_and, hiff]
    simp

private theorem deltaBlockInnerWord_sum_value
    {qBaseNat qScalarNat rNat block offset : Nat}
    (hqScalarLt : qScalarNat < 2) (hoffset : offset < 8)
    {inner : U 8}
    (hinner : U.Rel ρ inner
      (Word.eval ρ.bool (deltaBlockInnerWord
        (Vector.map LC.ofConst
          (deltaBlockHintBits qBaseNat qScalarNat rNat block offset))))) :
    (∑ j : Fin 8, inner.intBits[j].eval ρ.int) = qScalarNat := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp
      (Nat.lt_succ_iff.mp hqScalarLt) with hq | hq
  · subst qScalarNat
    simp_rw [deltaBlockInnerWord_bit_value (by norm_num) hinner]
    simp
  · subst qScalarNat
    simp_rw [deltaBlockInnerWord_bit_value (by norm_num) hinner]
    let chosen : Fin 8 := ⟨offset, hoffset⟩
    have hiff (j : Fin 8) : j.val = offset ↔ j = chosen := by
      simp [chosen, Fin.ext_iff]
    simp only [true_and, hiff]
    simp

private theorem outerSelectedDeltaBlockFrom_value
    {qBaseNat qScalarNat rNat block offset : Nat}
    (hqScalarLt : qScalarNat < 2) (hqScalar : qScalarNat = 1)
    (hblock : block < 16) {outer : U 16}
    (houter : U.Rel ρ outer
      (Word.eval ρ.bool (deltaBlockOuterWord
        (Vector.map LC.ofConst
          (deltaBlockHintBits qBaseNat qScalarNat rNat block offset)))))
    (start : Nat) :
    (outerSelectedDeltaBlockFrom outer start).eval ρ.int =
      (blockTerminalDelta / 2 ^ (8 * block + start) %
        2 ^ (8 - start) : Nat) := by
  unfold outerSelectedDeltaBlockFrom
  simp only [LC.eval_sum, LC.eval_nsmul, nsmul_eq_mul]
  simp_rw [deltaBlockOuterWord_bit_value hqScalarLt houter]
  let chosen : Fin 16 := ⟨block, hblock⟩
  have hiff (i : Fin 16) : i.val = block ↔ i = chosen := by
    simp [chosen, Fin.ext_iff]
  simp only [hqScalar, true_and, hiff]
  simp [chosen]

private theorem deltaBlockSelectedWord_value
    {qBaseNat qScalarNat rNat block offset : Nat}
    {selectedBlock : U 8}
    (hselectedBlock : U.Rel ρ selectedBlock
      (Word.eval ρ.bool (deltaBlockSelectedWord
        (Vector.map LC.ofConst
          (deltaBlockHintBits qBaseNat qScalarNat rNat block offset))))) :
    selectedBlock.intVal.eval ρ.int =
      rNat / 2 ^ (8 * block) % 2 ^ 8 := by
  rw [U.Rel.intVal hselectedBlock]
  have hselectedLt : rNat / 2 ^ (8 * block) % 2 ^ 8 < 2 ^ 8 :=
    Nat.mod_lt _ (Nat.two_pow_pos 8)
  have hwordInt := congrArg Int.ofNat
    (Modular.Aux.constWord_eval_toNat
      (rNat / 2 ^ (8 * block) % 2 ^ 8) hselectedLt ρ)
  have hwordEq :
      deltaBlockSelectedWord
          (Vector.map LC.ofConst
            (deltaBlockHintBits qBaseNat qScalarNat rNat block offset)) =
        { bitsLE := Vector.ofFn fun i =>
            LC.ofConst
              ((rNat / 2 ^ (8 * block) % 2 ^ 8).testBit i) } := by
    unfold deltaBlockSelectedWord
    congr 1
    apply Vector.ext
    intro i hi
    have hi8 : i < 8 := by omega
    have hi0 : i + 26 ≠ 0 := by omega
    have hi1 : i + 26 ≠ 1 := by omega
    have hi18 : ¬ i + 26 < 18 := by omega
    have hi26 : ¬ i + 26 < 26 := by omega
    have hiSub : i + 26 - 26 = i := by omega
    simp only [deltaBlockSelectedWord, deltaBlockHintBits,
      Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_map,
      Bool.and_eq_true, decide_eq_true_eq]
    rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simp [hi0, hi1, hi18, hi26, hiSub, hi8, Nat.add_comm]
  rw [hwordEq]
  exact hwordInt

private theorem oneHot_of_sum {u : U n} (hu : u.Valid ρ)
    (hsum : ∑ i : Fin n, u.intBits[i].eval ρ.int = 1) :
    ∃ chosen : Fin n,
      u.intBits[chosen].eval ρ.int = 1 ∧
        ∀ other : Fin n,
          u.intBits[other].eval ρ.int = 1 → other = chosen := by
  exact Aux.oneHot (fun i => validBit_zero_or_one hu i) hsum

private theorem bit_zero_of_ne {u : U n} (hu : u.Valid ρ)
    {chosen other : Fin n}
    (hchosen : u.intBits[chosen].eval ρ.int = 1)
    (hunique : ∀ j : Fin n,
      u.intBits[j].eval ρ.int = 1 → j = chosen)
    (hne : other ≠ chosen) :
    u.intBits[other].eval ρ.int = 0 := by
  rcases validBit_zero_or_one hu other with hzero | hone
  · exact hzero
  · exact (hne (hunique other hone)).elim

private theorem weighted_oneHot {u : U n} (hu : u.Valid ρ)
    (f : Fin n → Int) {chosen : Fin n}
    (hchosen : u.intBits[chosen].eval ρ.int = 1)
    (hunique : ∀ j : Fin n,
      u.intBits[j].eval ρ.int = 1 → j = chosen) :
    (∑ i : Fin n, f i • u.intBits[i]).eval ρ.int = f chosen := by
  rw [LC.eval_sum]
  simp only [LC.eval_smul]
  apply Aux.sum_mul_oneHot
  · exact hchosen
  · intro other hne
    exact bit_zero_of_ne hu hchosen hunique hne

def DeltaBlockComparatorSpec (ρ : WF.Valuation)
    (input : DeltaBlockComparatorInput) : Prop :=
  input.qScalar.intVal.eval ρ.int = 1 →
    input.r.evalNat ρ < DeltaBlock.delta

@[spec] theorem deltaBlockComparator_sound
    {input : DeltaBlockComparatorInput}
    (hr : input.r.val.Valid ρ)
    (hqScalar : input.qScalar.Valid ρ)
    (houterValid : input.outer.Valid ρ)
    (hinnerValid : input.inner.Valid ρ)
    (hselectedValid : input.selectedBlock.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (deltaBlockComparator input)
    ⦃⇓ _ => ⌜DeltaBlockComparatorSpec ρ input⌝⦄ := by
  mvcgen [deltaBlockComparator, WF.foldRange] invariants
  · ⇓⟨cur, _⟩ => ⌜∀ i : Fin 16, i.val < cur.prefix.length →
      input.outer.intBits[i].eval ρ.int *
        (deltaScalarBitsFrom input.r (8 * i.val) -
          (input.selectedBlock.intVal + LC.ofConst
            (256 * (blockTerminalDelta /
              2 ^ (8 * i.val + 8) : Nat) : Int))).eval ρ.int = 0⌝
  · ⇓⟨cur, _⟩ => ⌜∀ j : Fin 8, j.val < cur.prefix.length →
      input.inner.intBits[j].eval ρ.int *
        (deltaSelectedBitsFrom input.selectedBlock j.val -
          (outerSelectedDeltaBlockFrom input.outer j.val - 1)).eval
            ρ.int = 0⌝
  case vc1 pref cur suff hsplit _ hprev hassert =>
    intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i.val < pref.length
    · exact hprev i hlt
    · have hieq : i.val = cur := by
        have hcur : cur = pref.length := by grind
        omega
      subst cur
      simpa only [Fin.getElem_fin, LC.eval_zero] using hassert.2
  case vc2 => simp
  case vc3 pref cur suff hsplit _ hprev hassert =>
    intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j.val < pref.length
    · exact hprev j hlt
    · have hjeq : j.val = cur := by
        have hcur : cur = pref.length := by grind
        omega
      subst cur
      simpa only [Fin.getElem_fin, LC.eval_zero] using hassert.2
  case vc4 => simp
  case vc5 =>
    rename_i hsumOuterR1 hsumInnerR1 _ houter _ hinner
    unfold DeltaBlockComparatorSpec
    intro hq
    have hsumOuter :
        ∑ i : Fin 16, input.outer.intBits[i].eval ρ.int = 1 := by
      simp only [LC.eval_one, LC.eval_sub, LC.eval_sum, LC.eval_zero,
        one_mul] at hsumOuterR1
      omega
    have hsumInner :
        ∑ j : Fin 8, input.inner.intBits[j].eval ρ.int = 1 := by
      simp only [LC.eval_one, LC.eval_sub, LC.eval_sum, LC.eval_zero,
        one_mul] at hsumInnerR1
      omega
    rcases oneHot_of_sum houterValid hsumOuter with
      ⟨b, hb, hbUnique⟩
    rcases oneHot_of_sum hinnerValid hsumInner with
      ⟨j, hj, hjUnique⟩
    have houterEq := houter b (by simp)
    have hinnerEq := hinner j (by simp)
    have hselectedInt := U.intVal_eval_eq_eval_toNat
      input.selectedBlock hselectedValid
    have houterSelected :
        (outerSelectedDeltaBlockFrom input.outer j.val).eval ρ.int =
          (blockTerminalDelta / 2 ^ (8 * b.val + j.val) %
            2 ^ (8 - j.val) : Nat) := by
      unfold outerSelectedDeltaBlockFrom
      rw [LC.eval_sum]
      simp only [LC.eval_nsmul, nsmul_eq_mul]
      rw [Aux.sum_mul_oneHot
        (fun i : Fin 16 =>
          ((blockTerminalDelta / 2 ^ (8 * i.val + j.val) %
            2 ^ (8 - j.val) : Nat) : Int))
        (fun i => input.outer.intBits[i].eval ρ.int) b hb]
      intro other hne
      exact bit_zero_of_ne houterValid hb hbUnique hne
    have houterEq' :
        (input.r.evalNat ρ / 2 ^ (8 * b.val) : Nat) =
          (input.selectedBlock.eval ρ).toNat +
            2 ^ 8 *
              (blockTerminalDelta / 2 ^ (8 * b.val + 8)) := by
      simp only [hb, one_mul, LC.eval_sub, LC.eval_add, LC.eval_ofConst]
        at houterEq
      rw [deltaScalarBitsFrom_eval input.r hr _ (by omega),
        hselectedInt] at houterEq
      norm_num at houterEq ⊢
      have houterEqInt :
          (input.r.evalNat ρ / 2 ^ (8 * b.val) : Int) =
            (input.selectedBlock.eval ρ).toNat +
              256 * (blockTerminalDelta / 2 ^ (8 * b.val + 8)) := by
        omega
      exact_mod_cast houterEqInt
    have hinnerEq' :
        (input.selectedBlock.eval ρ).toNat / 2 ^ j.val + 1 =
          blockTerminalDelta / 2 ^ (8 * b.val + j.val) %
            2 ^ (8 - j.val) := by
      simp only [hj, one_mul, LC.eval_sub, LC.eval_one] at hinnerEq
      rw [deltaSelectedBitsFrom_eval input.selectedBlock hselectedValid
          j.val (by omega), houterSelected] at hinnerEq
      have hinnerEqInt :
          (((input.selectedBlock.eval ρ).toNat / 2 ^ j.val : Nat) : Int) +
              1 =
            ((blockTerminalDelta / 2 ^ (8 * b.val + j.val) %
              2 ^ (8 - j.val) : Nat) : Int) := by
        omega
      exact_mod_cast hinnerEqInt
    apply DeltaBlock.correctedBlockEquations_strict
      (r := input.r.evalNat ρ) (k := DeltaBlock.delta)
      (b := b.val) (j := j.val)
      (selected := (input.selectedBlock.eval ρ).toNat)
    exact ⟨b.isLt, j.isLt, (input.selectedBlock.eval ρ).isLt,
      by simpa [DeltaBlock.delta, blockTerminalDelta] using houterEq',
      by simpa [DeltaBlock.delta, blockTerminalDelta] using hinnerEq'⟩

def DeltaBlockComparatorWitnessSpec (ρ : WF.Valuation)
    (input : DeltaBlockComparatorInput) : Prop :=
  input.outer.Valid ρ ∧ input.inner.Valid ρ ∧
    input.selectedBlock.Valid ρ ∧
    (∑ i : Fin 16, input.outer.intBits[i].eval ρ.int) =
      input.qScalar.intVal.eval ρ.int ∧
    (∑ j : Fin 8, input.inner.intBits[j].eval ρ.int) =
      input.qScalar.intVal.eval ρ.int ∧
    (∀ i : Fin 16, input.outer.intBits[i].eval ρ.int = 1 →
      (deltaScalarBitsFrom input.r (8 * i.val)).eval ρ.int =
        (input.selectedBlock.intVal + LC.ofConst
          (256 * (blockTerminalDelta /
            2 ^ (8 * i.val + 8) : Nat) : Int)).eval ρ.int) ∧
    (∀ j : Fin 8, input.inner.intBits[j].eval ρ.int = 1 →
      (deltaSelectedBitsFrom input.selectedBlock j.val).eval ρ.int =
        (outerSelectedDeltaBlockFrom input.outer j.val - 1).eval ρ.int) ∧
    DeltaBlockComparatorSpec ρ input

private def deltaBlockOuterChecks
    (input : DeltaBlockComparatorInput) : Circuit Unit :=
  forIn' [:16] PUnit.unit fun i h _ => do
    let start := 8 * i
    let expected := input.selectedBlock.intVal + LC.ofConst
      (2 ^ 8 * (blockTerminalDelta / 2 ^ (start + 8) : Nat) : Int)
    assertR1C input.outer.intBits[i]
      (deltaScalarBitsFrom input.r start - expected) 0
    pure (ForInStep.yield PUnit.unit)

private def deltaBlockInnerChecks
    (input : DeltaBlockComparatorInput) : Circuit Unit :=
  forIn' [:8] PUnit.unit fun j h _ => do
    assertR1C input.inner.intBits[j]
      (deltaSelectedBitsFrom input.selectedBlock j -
        (outerSelectedDeltaBlockFrom input.outer j - 1)) 0
    pure (ForInStep.yield PUnit.unit)

private def deltaBlockAllChecks
    (input : DeltaBlockComparatorInput) : Circuit Unit := do
  deltaBlockOuterChecks input
  deltaBlockInnerChecks input
  pure PUnit.unit

@[spec] theorem deltaBlockOuterLoop_complete
    {input : DeltaBlockComparatorInput}
    (houterValid : input.outer.Valid ρ)
    (houterGate : ∀ i : Fin 16,
      input.outer.intBits[i].eval ρ.int = 1 →
      (deltaScalarBitsFrom input.r (8 * i.val)).eval ρ.int =
        (input.selectedBlock.intVal + LC.ofConst
          (256 * (blockTerminalDelta /
            2 ^ (8 * i.val + 8) : Nat) : Int)).eval ρ.int) :
    ⦃⌜True⌝⦄ Complete.interp ρ (deltaBlockOuterChecks input)
    ⦃⇓ _ => ⌜True⌝⦄ := by
  have houterBit (i : Fin 16) :
      input.outer.intBits[i].eval ρ.int = 0 ∨
        input.outer.intBits[i].eval ρ.int = 1 :=
    validBit_zero_or_one houterValid i
  mvcgen [deltaBlockOuterChecks, WF.foldRange] invariants
  · ⇓⟨cur, _⟩ => ⌜True⌝
  case vc1 pref cur suff hsplit _ _ =>
    have hcur : cur < 16 := by grind
    let i : Fin 16 := ⟨cur, hcur⟩
    rcases houterBit i with hzero | hone
    · have hzero' : input.outer.intBits[cur].eval ρ.int = 0 := by
        simpa [i] using hzero
      constructor
      · rw [hzero']
        simp
      · mvcgen
    · have hone' : input.outer.intBits[cur].eval ρ.int = 1 := by
        simpa [i] using hone
      have hgate := sub_eq_zero.mpr (houterGate i hone)
      norm_num at hgate
      constructor
      · rw [hone']
        simp only [one_mul, LC.eval_sub, LC.eval_zero]
        simpa [i] using hgate
      · mvcgen
  all_goals simp

@[spec] theorem deltaBlockInnerLoop_complete
    {input : DeltaBlockComparatorInput}
    (hinnerValid : input.inner.Valid ρ)
    (hinnerGate : ∀ j : Fin 8,
      input.inner.intBits[j].eval ρ.int = 1 →
      (deltaSelectedBitsFrom input.selectedBlock j.val).eval ρ.int =
        (outerSelectedDeltaBlockFrom input.outer j.val - 1).eval ρ.int) :
    ⦃⌜True⌝⦄ Complete.interp ρ (deltaBlockInnerChecks input)
    ⦃⇓ _ => ⌜True⌝⦄ := by
  have hinnerBit (j : Fin 8) :
      input.inner.intBits[j].eval ρ.int = 0 ∨
        input.inner.intBits[j].eval ρ.int = 1 :=
    validBit_zero_or_one hinnerValid j
  mvcgen [deltaBlockInnerChecks, WF.foldRange] invariants
  · ⇓⟨cur, _⟩ => ⌜True⌝
  case vc1 pref cur suff hsplit _ _ =>
    have hcur : cur < 8 := by grind
    let j : Fin 8 := ⟨cur, hcur⟩
    rcases hinnerBit j with hzero | hone
    · have hzero' : input.inner.intBits[cur].eval ρ.int = 0 := by
        simpa [j] using hzero
      constructor
      · rw [hzero']
        simp
      · mvcgen
    · have hone' : input.inner.intBits[cur].eval ρ.int = 1 := by
        simpa [j] using hone
      have hgate := sub_eq_zero.mpr (hinnerGate j hone)
      constructor
      · rw [hone']
        simp only [one_mul, LC.eval_sub, LC.eval_zero]
        simpa [j] using hgate
      · mvcgen
  all_goals simp

@[spec] theorem deltaBlockAllChecks_complete
    {input : DeltaBlockComparatorInput}
    (houterValid : input.outer.Valid ρ)
    (hinnerValid : input.inner.Valid ρ)
    (houterGate : ∀ i : Fin 16,
      input.outer.intBits[i].eval ρ.int = 1 →
      (deltaScalarBitsFrom input.r (8 * i.val)).eval ρ.int =
        (input.selectedBlock.intVal + LC.ofConst
          (256 * (blockTerminalDelta /
            2 ^ (8 * i.val + 8) : Nat) : Int)).eval ρ.int)
    (hinnerGate : ∀ j : Fin 8,
      input.inner.intBits[j].eval ρ.int = 1 →
      (deltaSelectedBitsFrom input.selectedBlock j.val).eval ρ.int =
        (outerSelectedDeltaBlockFrom input.outer j.val - 1).eval ρ.int)
    (hspec : DeltaBlockComparatorSpec ρ input) :
    ⦃⌜True⌝⦄ Complete.interp ρ (deltaBlockAllChecks input)
    ⦃⇓ _ => ⌜DeltaBlockComparatorSpec ρ input⌝⦄ := by
  mvcgen [deltaBlockAllChecks]
  all_goals first
    | exact houterValid
    | exact hinnerValid
    | exact houterGate
    | exact hinnerGate
    | exact hspec
    | trivial

theorem deltaBlockAllChecksInterp_complete
    {input : DeltaBlockComparatorInput}
    (houterValid : input.outer.Valid ρ)
    (hinnerValid : input.inner.Valid ρ)
    (houterGate : ∀ i : Fin 16,
      input.outer.intBits[i].eval ρ.int = 1 →
      (deltaScalarBitsFrom input.r (8 * i.val)).eval ρ.int =
        (input.selectedBlock.intVal + LC.ofConst
          (256 * (blockTerminalDelta /
            2 ^ (8 * i.val + 8) : Nat) : Int)).eval ρ.int)
    (hinnerGate : ∀ j : Fin 8,
      input.inner.intBits[j].eval ρ.int = 1 →
      (deltaSelectedBitsFrom input.selectedBlock j.val).eval ρ.int =
        (outerSelectedDeltaBlockFrom input.outer j.val - 1).eval ρ.int)
    (hspec : DeltaBlockComparatorSpec ρ input) :
    ⦃⌜True⌝⦄ (do
      Complete.interp ρ (deltaBlockOuterChecks input)
      Complete.interp ρ (deltaBlockInnerChecks input)
      pure PUnit.unit)
    ⦃⇓ _ => ⌜DeltaBlockComparatorSpec ρ input⌝⦄ := by
  mvcgen
  all_goals first
    | exact houterValid
    | exact hinnerValid
    | exact houterGate
    | exact hinnerGate
    | exact hspec
    | trivial

@[spec] theorem deltaBlockComparator_complete
    {input : DeltaBlockComparatorInput}
    (hinput : DeltaBlockComparatorWitnessSpec ρ input) :
    ⦃⌜True⌝⦄ Complete.interp ρ (deltaBlockComparator input)
    ⦃⇓ _ => ⌜DeltaBlockComparatorSpec ρ input⌝⦄ := by
  rcases hinput with
    ⟨houterValid, hinnerValid, hselectedValid, hsumOuter, hsumInner,
      houterGate, hinnerGate, hspec⟩
  mvcgen [deltaBlockComparator]
  case vc1 =>
    constructor
    · simp only [LC.eval_one, LC.eval_sub, LC.eval_sum, LC.eval_zero,
        one_mul]
      omega
    · mvcgen
      case vc1 =>
      constructor
      · simp only [LC.eval_one, LC.eval_sub, LC.eval_sum, LC.eval_zero,
          one_mul]
        omega
      · simpa only [deltaBlockOuterChecks, deltaBlockInnerChecks,
          Nat.reducePow, Int.reducePow] using
          (deltaBlockAllChecksInterp_complete (ρ := ρ)
            houterValid hinnerValid houterGate hinnerGate hspec (by trivial))

def DeltaBlockSelectSpec (rho : WF.Valuation) (r : Fn)
    (P Q : AffineSlope.Point) (control : AffineSlope.AddControl)
    (candidateX : AffineSlope.Rep) : Prop :=
  ∃ qScalar qBase : U 1,
    qScalar.Valid rho ∧ qBase.Valid rho ∧
    ∃ bothInfinity oppositePair finiteOpposite : LC ℤ,
      Gated3Spec rho control.active P.infinity
        (Q.infinity - bothInfinity) candidateX Q.X P.X
        (directTerminalTarget r qScalar qBase) ∧
      AndBitSpec rho P.infinity Q.infinity bothInfinity ∧
      AndBitSpec rho control.sameX control.oppositeY oppositePair ∧
      AndBitSpec rho control.finite oppositePair finiteOpposite ∧
      bothInfinity.eval rho.int + finiteOpposite.eval rho.int = 0 ∧
      (qScalar.intVal.eval rho.int = 1 →
        r.evalNat rho < DeltaBlock.delta)

@[spec] theorem selectAddOutputDeltaBlock_sound
    {r : Fn} {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl} {candidateX : AffineSlope.Rep}
    (hr : r.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (selectAddOutputDeltaBlock r P Q control candidateX)
    ⦃⇓ _ => ⌜DeltaBlockSelectSpec ρ r P Q control candidateX⌝⦄ := by
  mvcgen [selectAddOutputDeltaBlock]
  case vc1.success =>
    rename_i bothInfinity hbothInfinity
    intro bits
    mvcgen
    case vc1.hr => exact hr.1
    case vc2.hqScalar => exact (by assumption : U.Rel ρ _ _).1
    case vc3.houterValid => exact (by assumption : U.Rel ρ _ _).1
    case vc4.hinnerValid => exact (by assumption : U.Rel ρ _ _).1
    case vc5.hselectedValid => exact (by assumption : U.Rel ρ _ _).1
    case vc6.success =>
      rename_i qBase hqBase qScalar hqScalar outer houter inner hinner
        selectedBlock hselectedBlock hactive hPInfinity hQInfinity _
        hcomparator finiteOpposite hfiniteOpposite
      intro hinfinity
      rcases hfiniteOpposite with
        ⟨oppositePair, hoppositePair, hfiniteOpposite⟩
      refine ⟨qScalar, qBase, hqScalar.1, hqBase.1,
        bothInfinity, oppositePair, finiteOpposite, ?_, hbothInfinity,
        hoppositePair, hfiniteOpposite, ?_, hcomparator⟩
      · unfold Gated3Spec directTerminalTarget
        constructor
        · intro hgate
          have heq := hactive.2
          simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul,
            LC.eval_zero, nsmul_eq_mul, hgate, one_mul] at heq
          have heqInt : candidateX.intVal.eval ρ.int =
              r.val.intVal.eval ρ.int +
                scalar.modulus * qScalar.intVal.eval ρ.int +
                base.modulus * qBase.intVal.eval ρ.int := by omega
          apply congrArg (Int.castRingHom (ZMod base.modulus)) at heqInt
          simpa [Modular.Lazy.evalZMod] using heqInt.symm
        constructor
        · intro hgate
          have heq := hPInfinity.2
          simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul,
            LC.eval_zero, nsmul_eq_mul, hgate, one_mul] at heq
          have heqInt : Q.X.intVal.eval ρ.int =
              r.val.intVal.eval ρ.int +
                scalar.modulus * qScalar.intVal.eval ρ.int +
                base.modulus * qBase.intVal.eval ρ.int := by omega
          apply congrArg (Int.castRingHom (ZMod base.modulus)) at heqInt
          simpa [Modular.Lazy.evalZMod] using heqInt.symm
        · intro hgate
          have heq := hQInfinity.2
          simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul,
            LC.eval_zero, nsmul_eq_mul, hgate, one_mul] at heq
          have heqInt : P.X.intVal.eval ρ.int =
              r.val.intVal.eval ρ.int +
                scalar.modulus * qScalar.intVal.eval ρ.int +
                base.modulus * qBase.intVal.eval ρ.int := by omega
          apply congrArg (Int.castRingHom (ZMod base.modulus)) at heqInt
          simpa [Modular.Lazy.evalZMod] using heqInt.symm
      · simpa [LC.eval_add] using hinfinity.symm

theorem DeltaBlockSelectSpec.accepts_mathlib
    {r : Fn} {P Q : AffineSlope.Point}
    {p q : Reference.Point} {control : AffineSlope.AddControl}
    {candidateX : AffineSlope.Rep}
    (hr : r.Valid ρ)
    (hP : Reference.Represents ρ P p)
    (hQ : Reference.Represents ρ Q q)
    (hcontrol : AddControlSpec ρ P Q control)
    (hcandidate : AddCandidateXSpec ρ P Q control candidateX)
    (hselect : DeltaBlockSelectSpec ρ r P Q control candidateX) :
    TerminalPointAcceptanceSpec ρ r (p + q) := by
  rcases hselect with
    ⟨qScalar, qBase, hqScalar, hqBase,
      bothInfinity, oppositePair, finiteOpposite, htarget,
      hbothInfinity, hoppositePair, hfiniteOpposite, hinfinity, hstrict⟩
  have hqScalar0 := U.intVal_nonneg qScalar hqScalar
  have hqScalarLt := U.intVal_lt_two_pow qScalar hqScalar
  have hqScalarCases : qScalar.intVal.eval ρ.int = 0 ∨
      qScalar.intVal.eval ρ.int = 1 := by
    norm_num at hqScalarLt
    omega
  let slackNat := if qScalar.intVal.eval ρ.int = 1 then
      DeltaBlock.delta - 1 - r.evalNat ρ else 0
  have hslackLt : slackNat < 2 ^ 127 := by
    simp only [slackNat]
    split
    · exact (Nat.sub_le _ _).trans_lt ((Nat.sub_le _ _).trans_lt
        DeltaBlock.delta_lt_pow127)
    · norm_num
  let slackBits : BitVec 127 := BitVec.ofNat 127 slackNat
  let slack : U 127 := slackBits
  have hslackValid : slack.Valid ρ := U.valid_bitVec slackBits
  have hslackValue : slack.intVal.eval ρ.int = slackNat := by
    rw [U.intVal_eval_eq_eval_toNat slack hslackValid,
      U.eval_bitVec slackBits]
    simp only [slack, slackBits, BitVec.toNat_ofNat]
    exact_mod_cast Nat.mod_eq_of_lt hslackLt
  have hcanonical : qScalar.intVal.eval ρ.int *
      (r.val.intVal.eval ρ.int + slack.intVal.eval ρ.int + 1 -
        (base.modulus - scalar.modulus : Nat)) = 0 := by
    rcases hqScalarCases with hq0 | hq1
    · rw [hq0]
      simp
    · have hrDelta : r.evalNat ρ < DeltaBlock.delta := hstrict hq1
      have hslackEq : r.evalNat ρ + slackNat + 1 =
          DeltaBlock.delta := by
        simp only [slackNat, if_pos hq1]
        omega
      have hr0 := U.intVal_nonneg r.val hr.1
      have hrCast := Int.toNat_of_nonneg hr0
      have hslackEqInt :
          r.val.intVal.eval ρ.int + slackNat + 1 =
            (DeltaBlock.delta : Int) := by
        calc
          _ = (r.evalNat ρ : Int) + slackNat + 1 := by
            unfold Elem.evalNat
            rw [hrCast]
          _ = ((r.evalNat ρ + slackNat + 1 : Nat) : Int) := by
            push_cast
            ring
          _ = (DeltaBlock.delta : Int) := by exact_mod_cast hslackEq
      rw [hq1, hslackValue]
      simp only [one_mul, DeltaBlock.delta]
      have hdeltaInt :
          (DeltaBlock.delta : Int) =
            (base.modulus : Int) - scalar.modulus := by
        change ((base.modulus - scalar.modulus : Nat) : Int) = _
        norm_num [base, baseModulus, scalar, scalarModulus]
      omega
  apply DirectTerminalSelectSpec.accepts_mathlib hr hP hQ hcontrol
    hcandidate
  exact ⟨qScalar, qBase, slack, hqScalar, hqBase, hslackValid,
    bothInfinity, oppositePair, finiteOpposite, htarget, hbothInfinity,
    hoppositePair, hfiniteOpposite, hinfinity, hcanonical⟩

@[spec] theorem addCompleteCollapsedDeltaBlock_sound_mathlib
    {r : Fn} {P Q : AffineSlope.Point} {p q : Reference.Point}
    (hr : r.Valid ρ)
    (hP : Reference.Represents ρ P p)
    (hQ : Reference.Represents ρ Q q) :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (addCompleteCollapsedDeltaBlock r P Q)
    ⦃⇓ _ => ⌜TerminalPointAcceptanceSpec ρ r (p + q)⌝⦄ := by
  mvcgen [addCompleteCollapsedDeltaBlock]
  case vc2.success.success.success =>
    intro hselect
    exact hselect.accepts_mathlib hr hP hQ (by assumption) (by assumption)
  case vc3 =>
    intro _
    exact hr

@[spec] theorem selectAddOutputDeltaBlock_complete
    {r : Fn} {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl} {candidateX : AffineSlope.Rep}
    (hr : r.Valid ρ) (hP : P.Valid ρ) (hQ : Q.Valid ρ)
    (hcontrol : AddControlSpec ρ P Q control)
    (hcandidate : candidateX.Valid ρ)
    (hcandidateCanonical : candidateX.intVal.eval ρ.int < base.modulus)
    (hresultFinite :
      P.infinity.eval ρ.int * Q.infinity.eval ρ.int +
        control.finite.eval ρ.int *
          (control.sameX.eval ρ.int * control.oppositeY.eval ρ.int) = 0)
    (hsourceAccept :
      let source := if control.active.eval ρ.int = 1 then
          candidateX.intVal.eval ρ.int
        else if P.infinity.eval ρ.int = 1 then Q.X.intVal.eval ρ.int
        else if Q.infinity.eval ρ.int = 1 then P.X.intVal.eval ρ.int
        else 0
      source.toNat % scalar.modulus = r.evalNat ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (selectAddOutputDeltaBlock r P Q control candidateX)
    ⦃⇓ _ => ⌜DeltaBlockSelectSpec ρ r P Q control candidateX⌝⦄ := by
  mvcgen [selectAddOutputDeltaBlock]
  case vc1.hx => exact hP.2.2.2.2.2.2
  case vc2.hy => exact hQ.2.2.2.2.2.2
  case vc3.success =>
    rename_i bothInfinity hbothInfinity
    let source : Int := if control.active.eval ρ.int = 1 then
        candidateX.intVal.eval ρ.int
      else if P.infinity.eval ρ.int = 1 then Q.X.intVal.eval ρ.int
      else if Q.infinity.eval ρ.int = 1 then P.X.intVal.eval ρ.int
      else 0
    have hsource0 : 0 ≤ source := by
      simp only [source]
      split_ifs <;> first
        | exact hcandidate.1
        | exact hQ.2.1.1
        | exact hP.2.1.1
        | omega
    have hsourceLt : source < base.modulus := by
      simp only [source]
      split_ifs <;> first
        | exact hcandidateCanonical
        | exact hQ.2.2.1
        | exact hP.2.2.1
        | norm_num [base, baseModulus]
    have hsourceNatLt : source.toNat < base.modulus :=
      (Int.toNat_lt hsource0).2 hsourceLt
    have hmod : source.toNat % scalar.modulus = r.evalNat ρ := by
      simpa [source] using hsourceAccept
    let qScalarNat := source.toNat / scalar.modulus
    have hqScalarLt : qScalarNat < 2 := by
      rw [Nat.div_lt_iff_lt_mul scalar.positive]
      exact hsourceNatLt.trans (by
        norm_num [base, baseModulus, scalar, scalarModulus])
    have hqScalarCases : qScalarNat = 0 ∨ qScalarNat = 1 :=
      Nat.le_one_iff_eq_zero_or_eq_one.mp
        (Nat.lt_succ_iff.mp hqScalarLt)
    have hdecomp : source.toNat =
        r.evalNat ρ + scalar.modulus * qScalarNat := by
      calc
        source.toNat = source.toNat % scalar.modulus +
            scalar.modulus * (source.toNat / scalar.modulus) :=
          (Nat.mod_add_div source.toNat scalar.modulus).symm
        _ = r.evalNat ρ + scalar.modulus * qScalarNat := by rw [hmod]
    have hquotientCalc :
        (source.toNat - r.evalNat ρ) / scalar.modulus = qScalarNat := by
      rw [hdecomp, Nat.add_sub_cancel_left]
      exact Nat.mul_div_right qScalarNat scalar.positive
    have hquotientCalc' :
        (source.toNat - (r.val.intVal.eval ρ.int).toNat) /
          scalar.modulus = qScalarNat := by
      simpa [Elem.evalNat] using hquotientCalc
    let pair := firstDeltaBlockPair (r.evalNat ρ)
    let block := pair.1
    let offset := pair.2
    let bits : Vector Bool 34 := Vector.ofFn fun i =>
      if i.val = 0 then false
      else if i.val = 1 then qScalarNat.testBit 0
      else if i.val < 18 then qScalarNat.testBit 0 && i.val - 2 = block
      else if i.val < 26 then qScalarNat.testBit 0 && i.val - 18 = offset
      else (r.evalNat ρ).testBit (8 * block + (i.val - 26))
    refine ⟨bits, ?_, ?_⟩
    · simp [WF.interpHint, WF.evalArgs, deltaBlockTerminalHint,
        source, bits, pair, block, offset, hsource0,
        Nat.mod_eq_of_lt hsourceNatLt, Nat.div_eq_of_lt hsourceNatLt,
        Elem.evalNat, U.intVal_nonneg r.val hr.1, hquotientCalc']
      rfl
    · mvcgen
      rename_i qBase hqBase qScalar hqScalar outer houter inner hinner
        selectedBlock hselectedBlock
      have hbitsDef : bits =
          deltaBlockHintBits 0 qScalarNat (r.evalNat ρ) block offset := by
        rfl
      rw [hbitsDef] at hqBase hqScalar houter hinner hselectedBlock
      have hqScalarValue : qScalar.intVal.eval ρ.int = qScalarNat := by
        exact deltaBlockScalarQWord_value hqScalarLt hqScalar
      have hqBaseValue : qBase.intVal.eval ρ.int = 0 := by
        exact deltaBlockBaseQWord_value (by norm_num) hqBase
      have houterBit (i : Fin 16) :
          outer.intBits[i].eval ρ.int =
            (qScalarNat.testBit 0 && i.val = block).toInt := by
        have hi := deltaBlockOuterWord_bit_value hqScalarLt houter i
        rcases hqScalarCases with hq0 | hq1
        · simpa [hq0] using hi
        · by_cases hib : i.val = block
          · simpa [hq1, hib] using hi
          · simpa [hq1, hib] using hi
      have hinnerBit (j : Fin 8) :
          inner.intBits[j].eval ρ.int =
            (qScalarNat.testBit 0 && j.val = offset).toInt := by
        have hj := deltaBlockInnerWord_bit_value hqScalarLt hinner j
        rcases hqScalarCases with hq0 | hq1
        · simpa [hq0] using hj
        · by_cases hjo : j.val = offset
          · simpa [hq1, hjo] using hj
          · simpa [hq1, hjo] using hj
      have hselectedValue : selectedBlock.intVal.eval ρ.int =
          r.evalNat ρ / 2 ^ (8 * block) % 2 ^ 8 := by
        exact deltaBlockSelectedWord_value hselectedBlock
      have hbounds := firstDeltaBlockPair_bounds (r.evalNat ρ)
      have hblock : block < 16 := by simpa [block, pair] using hbounds.1
      have hoffset : offset < 8 := by simpa [offset, pair] using hbounds.2
      have hsumOuter :
          ∑ i : Fin 16, outer.intBits[i].eval ρ.int = qScalarNat :=
        deltaBlockOuterWord_sum_value hqScalarLt hblock houter
      have hsumInner :
          ∑ j : Fin 8, inner.intBits[j].eval ρ.int = qScalarNat :=
        deltaBlockInnerWord_sum_value hqScalarLt hoffset hinner
      have hrDelta (hq1 : qScalarNat = 1) :
          r.evalNat ρ < DeltaBlock.delta := by
        have hpEq : base.modulus = scalar.modulus + DeltaBlock.delta := by
          norm_num [DeltaBlock.delta, base, baseModulus, scalar,
            scalarModulus]
        rw [hq1] at hdecomp
        omega
      have hcorrected (hq1 : qScalarNat = 1) :
          DeltaBlock.CorrectedBlockEquations
            (r.evalNat ρ) DeltaBlock.delta block offset
              (r.evalNat ρ / 2 ^ (8 * block) % 2 ^ 8) := by
        simpa [pair, block, offset] using
          (firstDeltaBlockPair_spec (hrDelta hq1)).2.2
      have hselectedNat : (selectedBlock.eval ρ).toNat =
          r.evalNat ρ / 2 ^ (8 * block) % 2 ^ 8 := by
        have hcast : ((selectedBlock.eval ρ).toNat : Int) =
            (r.evalNat ρ / 2 ^ (8 * block) % 2 ^ 8 : Nat) := by
          calc
            _ = selectedBlock.intVal.eval ρ.int :=
              (U.intVal_eval_eq_eval_toNat selectedBlock hselectedBlock.1).symm
            _ = _ := hselectedValue
        exact_mod_cast hcast
      have houterGate (i : Fin 16)
          (hone : outer.intBits[i].eval ρ.int = 1) :
          (deltaScalarBitsFrom r (8 * i.val)).eval ρ.int =
            (selectedBlock.intVal + LC.ofConst
              (256 * (blockTerminalDelta /
                2 ^ (8 * i.val + 8) : Nat) : Int)).eval ρ.int := by
        rcases hqScalarCases with hq0 | hq1
        · have hi0 : outer.intBits[i].eval ρ.int = 0 := by
            simpa [hq0] using houterBit i
          rw [hone] at hi0
          norm_num at hi0
        · have hiEq : i.val = block := by
            by_contra hne
            have hi0 : outer.intBits[i].eval ρ.int = 0 := by
              simpa [hq1, hne] using houterBit i
            rw [hone] at hi0
            norm_num at hi0
          have hc := (hcorrected hq1).2.2.2.1
          rw [deltaScalarBitsFrom_eval r hr.1 _ (by omega)]
          simp only [LC.eval_add, LC.eval_ofConst, hselectedValue]
          rw [hiEq]
          exact_mod_cast hc
      have hinnerGate (j : Fin 8)
          (hone : inner.intBits[j].eval ρ.int = 1) :
          (deltaSelectedBitsFrom selectedBlock j.val).eval ρ.int =
            (outerSelectedDeltaBlockFrom outer j.val - 1).eval ρ.int := by
        rcases hqScalarCases with hq0 | hq1
        · have hj0 : inner.intBits[j].eval ρ.int = 0 := by
            simpa [hq0] using hinnerBit j
          rw [hone] at hj0
          norm_num at hj0
        · have hjEq : j.val = offset := by
            by_contra hne
            have hj0 : inner.intBits[j].eval ρ.int = 0 := by
              simpa [hq1, hne] using hinnerBit j
            rw [hone] at hj0
            norm_num at hj0
          have hc := (hcorrected hq1).2.2.2.2
          rw [deltaSelectedBitsFrom_eval selectedBlock hselectedBlock.1
            j.val (by omega), hselectedNat]
          simp only [LC.eval_sub, LC.eval_one]
          rw [outerSelectedDeltaBlockFrom_value hqScalarLt hq1 hblock
            houter j.val]
          rw [hjEq]
          have hc' :
              r.evalNat ρ / 2 ^ (8 * block) % 2 ^ 8 / 2 ^ offset + 1 =
                blockTerminalDelta / 2 ^ (8 * block + offset) %
                  2 ^ (8 - offset) := by
            simpa [DeltaBlock.delta, blockTerminalDelta] using hc
          have hcInt := congrArg Int.ofNat hc'
          push_cast at hcInt
          omega
      have hcomparator : DeltaBlockComparatorWitnessSpec ρ
          ⟨r, qScalar, outer, inner, selectedBlock⟩ := by
        refine ⟨houter.1, hinner.1, hselectedBlock.1, ?_, ?_,
          houterGate, hinnerGate, ?_⟩
        · rw [hsumOuter, hqScalarValue]
        · rw [hsumInner, hqScalarValue]
        · intro hq1
          apply hrDelta
          exact_mod_cast hqScalarValue.symm.trans hq1
      clear hbitsDef houterBit hinnerBit hselectedValue hbounds hblock
        hoffset hsumOuter hsumInner hrDelta hcorrected hselectedNat
        houterGate hinnerGate
      have hr0 := U.intVal_nonneg r.val hr.1
      have hsourceInt : source = r.val.intVal.eval ρ.int +
          scalar.modulus * qScalarNat := by
        have hdecompInt := congrArg Int.ofNat hdecomp
        simpa [Elem.evalNat, Int.toNat_of_nonneg hsource0,
          Int.toNat_of_nonneg hr0] using hdecompInt
      have hcases := hcontrol.x_output_gated_cases
        hP.2.2.2.2.2.2 hQ.2.2.2.2.2.2 hbothInfinity
      constructor
      · simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul,
          LC.eval_zero, nsmul_eq_mul, hqScalarValue, hqBaseValue]
        rcases hcases with hc | hc | hc | hc <;>
          simp_all [source, AndBitSpec]
      · mvcgen
        case vc1.h =>
          constructor
          · have hPgate :
                P.infinity.eval ρ.int *
                  (Q.X.intVal.eval ρ.int -
                    (r.val.intVal.eval ρ.int +
                      scalar.modulus * qScalar.intVal.eval ρ.int +
                      base.modulus * qBase.intVal.eval ρ.int)) = 0 := by
              rcases hcases with hc | hc | hc | hc <;>
                simp_all [source, AndBitSpec]
            simpa [LC.eval_sub, LC.eval_add, LC.eval_nsmul,
              LC.eval_zero, nsmul_eq_mul] using hPgate
          · mvcgen
            case vc1.h =>
              constructor
              · have hQgate :
                    (Q.infinity - bothInfinity).eval ρ.int *
                      (P.X.intVal.eval ρ.int -
                        (r.val.intVal.eval ρ.int +
                          scalar.modulus * qScalar.intVal.eval ρ.int +
                          base.modulus * qBase.intVal.eval ρ.int)) = 0 := by
                    rcases hcases with hc | hc | hc | hc <;>
                      simp_all [source, AndBitSpec]
                simpa [LC.eval_sub, LC.eval_add, LC.eval_nsmul,
                  LC.eval_zero, nsmul_eq_mul] using hQgate
              · mvcgen
                all_goals first
                  | exact hcomparator
                  | exact hcontrol.1.1
                  | exact hcontrol.2.1.1
                  | exact hcontrol.2.2.1.2
                  | skip
                case vc5.success =>
                  rename_i _ hcomparatorSpec finiteOpposite hfiniteOpposite
                  constructor
                  · rcases hfiniteOpposite with
                      ⟨oppositePair, hoppositePair, hfiniteOpposite⟩
                    have hinfinity : bothInfinity.eval ρ.int +
                        finiteOpposite.eval ρ.int = 0 := by
                      rw [hbothInfinity.1, hfiniteOpposite.1,
                        hoppositePair.1]
                      exact hresultFinite
                    simpa [LC.eval_add] using hinfinity.symm
                  · rcases hfiniteOpposite with
                      ⟨oppositePair, hoppositePair, hfiniteOpposite⟩
                    refine ⟨qScalar, qBase, hqScalar.1, hqBase.1,
                      bothInfinity, oppositePair, finiteOpposite, ?_,
                      hbothInfinity, hoppositePair, hfiniteOpposite, ?_,
                      hcomparatorSpec⟩
                    · unfold Gated3Spec
                      rcases hcases with hc | hc | hc | hc <;>
                        simp_all [source, directTerminalTarget,
                          Modular.Lazy.evalZMod, AndBitSpec]
                    · simp_all [AndBitSpec]

@[spec] theorem addCompleteCollapsedDeltaBlock_complete_mathlib
    {r : Fn} {P Q : AffineSlope.Point} {q p : Reference.Point}
    (hr : r.Valid ρ) (hPvalid : P.Valid ρ) (hQvalid : Q.Valid ρ)
    (hP : Reference.NormalizedRep ρ P p)
    (hQ : Reference.NormalizedRep ρ Q q)
    (hnoTwoTorsion : p = 0 ∨ p + p ≠ 0)
    (haccept : TerminalPointAcceptanceSpec ρ r (p + q)) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (addCompleteCollapsedDeltaBlock r P Q)
    ⦃⇓ _ => ⌜TerminalPointAcceptanceSpec ρ r (p + q)⌝⦄ := by
  mvcgen [addCompleteCollapsedDeltaBlock]
  all_goals first
    | exact hr
    | exact hPvalid
    | exact hQvalid
    | exact hP.1
    | exact hQ.1
    | exact hnoTwoTorsion
    | exact haccept
    | assumption
    | skip
  case vc16 =>
    rename_i control hcontrol candidateX
    intros hcandidateValid _ hcandidateCanonical hcandidate
    exact (directTerminal_complete_conditions hr hPvalid hQvalid hP hQ
      hcontrol hcandidate hcandidateValid hcandidateCanonical haccept).1
  case vc17 =>
    rename_i control hcontrol candidateX
    intros hcandidateValid _ hcandidateCanonical hcandidate
    exact (directTerminal_complete_conditions hr hPvalid hQvalid hP hQ
      hcontrol hcandidate hcandidateValid hcandidateCanonical haccept).2
  all_goals aesop

end Freigen.F2Z.Examples.EcdsaP256
