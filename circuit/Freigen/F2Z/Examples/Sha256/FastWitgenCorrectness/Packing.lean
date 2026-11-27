import Freigen.F2Z.Examples.Sha256.FastWitgenCorrectness.Full
import Freigen.F2Z.Examples.Sha256.FastWitgen

namespace Freigen.F2Z.Examples

open Freigen.F2Z.Semantics

noncomputable section

namespace Sha256FastWitgen

/-! ## The packed witness builder

This is the only part of the refinement proof which knows about `UInt64`
word boundaries.  The SHA proofs below use `WitnessBuilder.Refines` and the
single `appendBitsLE_refines` lemma. -/

def UInt64CleanAbove (x : UInt64) (width : Nat) : Prop :=
  ∀ i, width ≤ i → x.toBitVec.getLsbD i = false

def uint64PrefixBits (x : UInt64) (width : Nat) : List Bool :=
  List.ofFn fun i : Fin width => x.toBitVec.getLsbD i

@[simp] theorem uint64PrefixBits_length (x : UInt64) (width : Nat) :
    (uint64PrefixBits x width).length = width := by
  simp [uint64PrefixBits]

@[simp] theorem uint64PrefixBits_getElem (x : UInt64) (width i : Nat)
    (hi : i < width) :
    (uint64PrefixBits x width)[i]'(by simpa using hi) =
      x.toBitVec.getLsbD i := by
  simp [uint64PrefixBits]

theorem uint64PrefixBits_eq_natBits (x : UInt64) (width : Nat) :
    uint64PrefixBits x width = (natBits width x.toNat).toList := by
  apply List.ext_getElem (by simp)
  intro i hi1 hi2
  have hi : i < width := by simpa using hi1
  rw [uint64PrefixBits_getElem x width i hi]
  simp [uint64PrefixBits, natBits, BitVec.getLsbD,
    UInt64.toNat_toBitVec]

theorem uint64CleanAbove_of_lt (x : UInt64) {width : Nat}
    (hx : x.toNat < 2 ^ width) : UInt64CleanAbove x width := by
  intro i hi
  unfold BitVec.getLsbD
  rw [UInt64.toNat_toBitVec]
  apply Nat.testBit_lt_two_pow
  exact lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hi)

theorem uint64CleanAbove_sixtyFour (x : UInt64) : UInt64CleanAbove x 64 :=
  uint64CleanAbove_of_lt x x.toNat_lt

theorem uint64_shiftAmount (p : Nat) (hp : p < 64) :
    (UInt64.ofNat p).toBitVec % 64 = BitVec.ofNat 64 p := by
  rw [BitVec.toNat_eq]
  have hp64 : p < 18446744073709551616 := by omega
  simpa [Nat.mod_eq_of_lt hp] using (Nat.mod_eq_of_lt hp64).symm

theorem uint64_completed_getLsbD (pending value : UInt64) (p i : Nat)
    (hp : p < 64) (hclean : UInt64CleanAbove pending p) (hi : i < 64) :
    (pending ||| (value <<< UInt64.ofNat p)).toBitVec.getLsbD i =
      if i < p then pending.toBitVec.getLsbD i
      else value.toBitVec.getLsbD (i - p) := by
  rw [UInt64.toBitVec_or, BitVec.getLsbD_or, UInt64.toBitVec_shiftLeft]
  rw [uint64_shiftAmount p hp]
  rw [show value.toBitVec <<< BitVec.ofNat 64 p =
      value.toBitVec <<< p by
    change value.toBitVec <<< (BitVec.ofNat 64 p).toNat = _
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : p < 2 ^ 64)]]
  rw [BitVec.getLsbD_shiftLeft]
  split <;> rename_i h
  · have hip : i < p := by simp_all
    simp [hip]
  · have hpi : p ≤ i := by omega
    rw [hclean i hpi]
    simp [hpi, hi]

theorem uint64_shifted_getLsbD (value : UInt64) (consumed i : Nat)
    (hc : consumed < 64) :
    (value >>> UInt64.ofNat consumed).toBitVec.getLsbD i =
      value.toBitVec.getLsbD (consumed + i) := by
  rw [UInt64.toBitVec_shiftRight, uint64_shiftAmount consumed hc]
  change (value.toBitVec >>> (BitVec.ofNat 64 consumed).toNat).getLsbD i = _
  rw [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : consumed < 2 ^ 64)]
  exact BitVec.getLsbD_ushiftRight value.toBitVec consumed i

theorem uint64PrefixBits_completed_short (pending value : UInt64)
    (p width : Nat) (hp : p < 64) (htotal : p + width < 64)
    (hclean : UInt64CleanAbove pending p) :
    uint64PrefixBits (pending ||| (value <<< UInt64.ofNat p)) (p + width) =
      uint64PrefixBits pending p ++ uint64PrefixBits value width := by
  apply List.ext_getElem (by simp)
  intro i hi1 hi2
  have hi : i < p + width := by simpa using hi1
  rw [uint64PrefixBits_getElem _ _ _ hi]
  rw [uint64_completed_getLsbD pending value p i hp hclean (by omega)]
  rw [List.getElem_append]
  split <;> simp_all [uint64PrefixBits]

theorem uint64PrefixBits_completed_full (pending value : UInt64)
    (p width : Nat) (hp : p < 64) (hwidth : width < 64)
    (htotal : 64 ≤ p + width) (hclean : UInt64CleanAbove pending p) :
    uint64PrefixBits (pending ||| (value <<< UInt64.ofNat p)) 64 ++
        uint64PrefixBits (value >>> UInt64.ofNat (64 - p)) (p + width - 64) =
      uint64PrefixBits pending p ++ uint64PrefixBits value width := by
  have hp0 : 0 < p := by omega
  have hc : 64 - p < 64 := by omega
  have hlen : 64 + (p + width - 64) = p + width := by omega
  apply List.ext_getElem (by
    simp only [uint64PrefixBits_length, List.length_append]
    omega)
  intro i hi1 hi2
  have hi : i < p + width := by
    simpa only [uint64PrefixBits_length, List.length_append, hlen] using hi1
  rw [List.getElem_append, List.getElem_append]
  simp only [uint64PrefixBits_length]
  split <;> rename_i hi64
  · rw [uint64PrefixBits_getElem _ _ _ (by simpa using hi64)]
    rw [uint64_completed_getLsbD pending value p i hp hclean hi64]
    by_cases hip : i < p
    · simp only [dif_pos hip]
      rw [uint64PrefixBits_getElem _ _ _ hip]
      simp [hip]
    · simp only [dif_neg hip]
      rw [uint64PrefixBits_getElem _ _ _ (by omega)]
      simp [hip]
  · have h64i : 64 ≤ i := by omega
    have hirem : i - 64 < p + width - 64 := by omega
    rw [uint64PrefixBits_getElem _ _ _ hirem]
    rw [uint64_shifted_getLsbD value (64 - p) (i - 64) hc]
    have harith : 64 - p + (i - 64) = i - p := by omega
    rw [harith]
    have hip : ¬i < p := by omega
    simp only [dif_neg hip]
    rw [uint64PrefixBits_getElem _ _ _ (by omega)]

theorem uint64_completed_clean (pending value : UInt64) (p width : Nat)
    (hp : p < 64) (htotal : p + width < 64)
    (hpending : UInt64CleanAbove pending p)
    (hvalue : UInt64CleanAbove value width) :
    UInt64CleanAbove (pending ||| (value <<< UInt64.ofNat p)) (p + width) := by
  intro i hi
  by_cases hi64 : i < 64
  · rw [uint64_completed_getLsbD pending value p i hp hpending hi64]
    simp only [if_neg (by omega : ¬i < p)]
    exact hvalue (i - p) (by omega)
  · exact uint64CleanAbove_sixtyFour
      (pending ||| (value <<< UInt64.ofNat p)) i (by omega)

theorem uint64_shifted_clean (value : UInt64) (p width : Nat)
    (hp : p < 64) (hwidth : width < 64) (htotal : 64 ≤ p + width)
    (hvalue : UInt64CleanAbove value width) :
    UInt64CleanAbove (value >>> UInt64.ofNat (64 - p))
      (p + width - 64) := by
  have hc : 64 - p < 64 := by omega
  intro i hi
  rw [uint64_shifted_getLsbD value (64 - p) i hc]
  apply hvalue
  omega

def WitnessBuilder.bits (builder : WitnessBuilder) : List Bool :=
  builder.words.toList.flatMap (fun word => uint64PrefixBits word 64) ++
    uint64PrefixBits builder.pending builder.pendingBits

structure BuilderRefines (builder : WitnessBuilder)
    (bits : List Bool) : Prop where
  pendingBits_lt : builder.pendingBits < 64
  pending_clean : UInt64CleanAbove builder.pending builder.pendingBits
  bits_eq : builder.bits = bits

theorem appendBitsLE_refines
    {builder : WitnessBuilder} {bits : List Bool}
    (hbuilder : BuilderRefines builder bits) (value : UInt64) (width : Nat)
    (hwidth : width < 64) (hvalue : value.toNat < 2 ^ width) :
    BuilderRefines (appendBitsLE builder value width)
      (bits ++ uint64PrefixBits value width) := by
  have hvalueClean : UInt64CleanAbove value width :=
    uint64CleanAbove_of_lt value hvalue
  unfold appendBitsLE
  dsimp only
  split <;> rename_i htotal
  · constructor
    · exact htotal
    · exact uint64_completed_clean builder.pending value
        builder.pendingBits width hbuilder.pendingBits_lt htotal
        hbuilder.pending_clean hvalueClean
    · unfold WitnessBuilder.bits
      dsimp only
      rw [uint64PrefixBits_completed_short builder.pending value
        builder.pendingBits width hbuilder.pendingBits_lt htotal
        hbuilder.pending_clean]
      rw [← hbuilder.bits_eq]
      unfold WitnessBuilder.bits
      simp only [List.append_assoc]
  · have htotal' : 64 ≤ builder.pendingBits + width := by omega
    constructor
    · dsimp only
      have hp := hbuilder.pendingBits_lt
      omega
    · exact uint64_shifted_clean value builder.pendingBits width
        hbuilder.pendingBits_lt hwidth htotal' hvalueClean
    · unfold WitnessBuilder.bits
      dsimp only
      rw [Array.toList_push, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [List.append_assoc]
      rw [uint64PrefixBits_completed_full builder.pending value
        builder.pendingBits width hbuilder.pendingBits_lt hwidth htotal'
        hbuilder.pending_clean]
      rw [← hbuilder.bits_eq]
      unfold WitnessBuilder.bits
      simp only [List.append_assoc]

end Sha256FastWitgen

end
end Freigen.F2Z.Examples
