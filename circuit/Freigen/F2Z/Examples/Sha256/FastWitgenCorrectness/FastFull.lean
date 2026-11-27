import Freigen.F2Z.Examples.Sha256.FastWitgenCorrectness.FastCompression

namespace Freigen.F2Z.Examples

open Freigen.F2Z.Semantics

noncomputable section

namespace Sha256FastWitgen

/-! ## Packed input representation -/

structure PackedMessageRel (packed : Sha2562KBPackedMessage)
    (message : Vector Bool sha2562KBMessageBits) : Prop where
  bits_eq : packed.toList.flatMap
      (fun word => uint64PrefixBits word 64) = message.toList
  bit_eq : ∀ word (_hword : word < 256) bit (_hbit : bit < 64),
    packed[word]!.toBitVec.getLsbD bit = message[word * 64 + bit]!

theorem withInput_refines (h : PackedMessageRel packed message) :
    BuilderRefines (WitnessBuilder.withInput packed)
      (sha256InputState message).bools.toList := by
  constructor
  · simp [WitnessBuilder.withInput]
  · exact uint64CleanAbove_of_lt 0 (by norm_num)
  · unfold WitnessBuilder.bits WitnessBuilder.withInput sha256InputState
    simp only [Array.mkEmpty_eq]
    rw [show #[].append packed.toArray = packed.toArray from Array.empty_append]
    rw [Vector.toList_toArray, h.bits_eq]
    simp [uint64PrefixBits, Vector.toList_toArray]

def reverseBV (x : BitVec 32) : BitVec 32 :=
  BitVec.ofFnLE fun i => x[31 - i.val]'(by omega)

theorem reverseBits32_toBitVec (x : UInt32) :
    (reverseBits32 x).toBitVec = reverseBV x.toBitVec := by
  unfold reverseBits32
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_and,
    UInt32.toBitVec_shiftRight, UInt32.toBitVec_shiftLeft,
    UInt32.toBitVec_ofNat]
  apply BitVec.eq_of_getElem_eq
  intro i hi
  unfold reverseBV
  rw [BitVec.getElem_ofFnLE]
  generalize x.toBitVec = y
  interval_cases i <;> bv_decide

theorem packedHalfWord_eq (h : PackedMessageRel packed message)
    (global : Nat) (hglobal : global < 512) :
    let packedWord := packed[global / 2]!
    let word := if global % 2 = 0 then packedWord.toUInt32
      else (packedWord >>> 32).toUInt32
    (reverseBits32 word).toBitVec =
      BitVec.ofFnLE fun bit : Fin 32 =>
        message[global * 32 + (31 - bit.val)]! := by
  dsimp only
  by_cases heven : global % 2 = 0
  · simp [heven]
    rw [reverseBits32_toBitVec]
    apply BitVec.eq_of_getElem_eq
    intro bit hbit
    unfold reverseBV
    rw [BitVec.getElem_ofFnLE, BitVec.getElem_ofFnLE]
    simp only [UInt64.toBitVec_toUInt32, BitVec.getElem_setWidth]
    rw [h.bit_eq (global / 2) (by omega) (31 - bit) (by omega)]
    congr 1
    omega
  · have hodd : global % 2 = 1 := by omega
    simp [heven]
    rw [reverseBits32_toBitVec]
    apply BitVec.eq_of_getElem_eq
    intro bit hbit
    unfold reverseBV
    rw [BitVec.getElem_ofFnLE, BitVec.getElem_ofFnLE]
    simp only [UInt64.toBitVec_toUInt32, UInt64.toBitVec_shiftRight]
    have hshift : UInt64.toBitVec 32 % 64 = BitVec.ofNat 64 32 := by
      change (UInt64.ofNat 32).toBitVec % 64 = BitVec.ofNat 64 32
      exact uint64_shiftAmount 32 (by omega)
    simp only [hshift]
    simp only [BitVec.getElem_setWidth]
    rw [BitVec.ushiftRight_ofNat_eq]
    norm_num
    rw [h.bit_eq (global / 2) (by omega) (32 + (31 - bit)) (by omega)]
    congr 1
    omega

def preparedBlockValues (message : Vector Bool sha2562KBMessageBits)
    (block : Nat) (_hblock : block < 33) : Vector (BitVec 32) 16 :=
  if h : block < 32 then messageBlockValues message block h
  else sha256PaddingValues

theorem messageBlockValues_get (message : Vector Bool sha2562KBMessageBits)
    (block : Nat) (hblock : block < 32) (word : Nat) (hword : word < 16) :
    (messageBlockValues message block hblock)[word]! =
      BitVec.ofFnLE fun bit : Fin 32 =>
        message[block * 512 + word * 32 + (31 - bit.val)]'(
          by simp [sha2562KBMessageBits, sha2562KBMessageBytes]; omega) := by
  rw [getElem!_pos (messageBlockValues message block hblock) word hword]
  unfold messageBlockValues
  rw [Vector.getElem_ofFn]

theorem preparePackedInput_block_rel (h : PackedMessageRel packed message)
    (block : Nat) (hblock : block < 33) :
    BlockArrayRel (preparePackedInput packed).1 block
      (preparedBlockValues message block hblock) := by
  intro word hword
  unfold preparePackedInput
  simp only [Prod.fst]
  rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]
  by_cases hmessage : block < 32
  · have hglobal : block * 16 + word < 512 := by omega
    simp only [show block * 16 + word < 32 * 16 by omega, if_pos]
    have hp := packedHalfWord_eq h (block * 16 + word) hglobal
    dsimp only at hp
    have hactual :
        (if (block * 16 + word) % 2 = 0 then
            reverseBits32 packed[(block * 16 + word) / 2]!.toUInt32
          else reverseBits32
            (packed[(block * 16 + word) / 2]! >>> 32).toUInt32).toBitVec =
          BitVec.ofFnLE fun bit : Fin 32 =>
            message[(block * 16 + word) * 32 + (31 - bit.val)]! := by
      by_cases heven : (block * 16 + word) % 2 = 0
      · simpa [heven] using hp
      · simpa [heven] using hp
    rw [hactual]
    unfold preparedBlockValues
    simp only [hmessage, dif_pos]
    rw [messageBlockValues_get message block hmessage word hword]
    apply BitVec.eq_of_getElem_eq
    intro bit hbit
    rw [BitVec.getElem_ofFnLE, BitVec.getElem_ofFnLE]
    rw [getElem!_pos _ _ (by
      simp [sha2562KBMessageBits, sha2562KBMessageBytes]
      omega)]
    congr 1
    simp [Nat.add_mul, Nat.mul_assoc]
  · have hblock32 : block = 32 := by omega
    subst block
    unfold preparedBlockValues
    simp only [dif_neg (by omega : ¬32 < 32)]
    interval_cases word <;>
      simp [sha256PaddingValues]

theorem preparePackedInput_refines (h : PackedMessageRel packed message) :
    let prepared := preparePackedInput packed
    (∀ block (hblock : block < 33),
      BlockArrayRel prepared.1 block
        (preparedBlockValues message block hblock)) ∧
    BuilderRefines prepared.2 (sha256InputState message).bools.toList := by
  exact ⟨preparePackedInput_block_rel h, withInput_refines h⟩

/-! ## The outer compression loop

`PreparedBlocksTrace` is deliberately recursive on the same `remaining`
counter as `compressBlocksLoop`.  The proof below therefore exposes exactly
one compression at each induction step; it never asks definitional equality
to unfold the 33-block computation. -/

structure PreparedBlocksTrace where
  state : Witgen.State
  hash : Vector (BitVec 32) 8

def preparedBlocksTrace (message : Vector Bool sha2562KBMessageBits) :
    (block remaining : Nat) → (block + remaining ≤ 33) →
      Witgen.State → Vector (BitVec 32) 8 → PreparedBlocksTrace
  | _, 0, _, state, hash => ⟨state, hash⟩
  | block, remaining + 1, hbound, state, hash =>
      let mv := preparedBlockValues message block (by omega)
      preparedBlocksTrace message (block + 1) remaining (by omega)
        (permutationFinalState state mv hash) (model mv hash)

theorem compressBlocksLoop_refines
    (message : Vector Bool sha2562KBMessageBits)
    (blocks : Array UInt32) (block remaining : Nat)
    (hbound : block + remaining ≤ 33)
    (hash : HashState) (builder : WitnessBuilder)
    (witState : Witgen.State) (hashValues : Vector (BitVec 32) 8)
    (hblocks : ∀ i (hi : i < 33),
      BlockArrayRel blocks i (preparedBlockValues message i hi))
    (hhash : hash.toVector = hashValues)
    (hbuilder : BuilderRefines builder witState.bools.toList) :
    let result := compressBlocksLoop blocks block remaining hash builder
    let trace := preparedBlocksTrace message block remaining hbound
      witState hashValues
    result.1.toVector = trace.hash ∧
      BuilderRefines result.2 trace.state.bools.toList := by
  induction remaining generalizing block hash builder witState hashValues with
  | zero =>
      simp [compressBlocksLoop, preparedBlocksTrace, hhash, hbuilder]
  | succ remaining ih =>
      have hblock : block < 33 := by omega
      let mv := preparedBlockValues message block hblock
      generalize hresult : compress blocks block hash builder = result
      rcases result with ⟨hash1, builder1⟩
      have hone := compress_refines blocks block hash builder witState mv
        hashValues (hblocks block hblock) hhash hbuilder
      rw [hresult] at hone
      obtain ⟨hhash1, hbuilder1⟩ := hone
      have htail := ih (block := block + 1) (hash := hash1)
        (builder := builder1)
        (witState := permutationFinalState witState mv hashValues)
        (hashValues := model mv hashValues) (by omega) hhash1 hbuilder1
      simp only [compressBlocksLoop, preparedBlocksTrace]
      rw [hresult]
      exact htail

theorem preparedBlocksTrace_messageThenPadding
    (message : Vector Bool sha2562KBMessageBits)
    (block remaining : Nat) (hend : block + remaining = 32)
    (state : Witgen.State) (hash : Vector (BitVec 32) 8) :
    (preparedBlocksTrace message block (remaining + 1)
      (by omega) state hash).state =
        permutationFinalState
          (messageBlocksTrace message (List.range' block remaining) (by
            intro i hi
            have hi' := List.mem_range'.mp hi
            omega) state hash).state
          sha256PaddingValues
          (messageBlocksTrace message (List.range' block remaining) (by
            intro i hi
            have hi' := List.mem_range'.mp hi
            omega) state hash).hash ∧
    (preparedBlocksTrace message block (remaining + 1)
      (by omega) state hash).hash =
        model sha256PaddingValues
          (messageBlocksTrace message (List.range' block remaining) (by
            intro i hi
            have hi' := List.mem_range'.mp hi
            omega) state hash).hash := by
  induction remaining generalizing block state hash with
  | zero =>
      have hblock : block = 32 := by omega
      subst block
      rw [preparedBlocksTrace]
      rw [preparedBlocksTrace]
      simp only [List.range'_zero]
      rw [messageBlocksTrace.eq_def]
      simp only [preparedBlockValues, dif_neg (by omega : ¬32 < 32)]
      exact ⟨True.intro, True.intro⟩
  | succ remaining ih =>
      have hblock : block < 32 := by omega
      rw [preparedBlocksTrace]
      simp only [List.range'_succ]
      rw [messageBlocksTrace.eq_def]
      simp only [preparedBlockValues, hblock, dif_pos]
      exact ih (block := block + 1)
        (state := permutationFinalState state
          (messageBlockValues message block hblock) hash)
        (hash := model (messageBlockValues message block hblock) hash) (by omega)

theorem preparedFullTrace_state
    (message : Vector Bool sha2562KBMessageBits) :
    (preparedBlocksTrace message 0 33 (by omega)
      (sha256InputState message) sha256InitialValues).state =
        sha256GenericFinalState message := by
  have h := preparedBlocksTrace_messageThenPadding message 0 32 (by omega)
    (sha256InputState message) sha256InitialValues
  unfold sha256GenericFinalState sha256MessageTrace
  simp only [show [0:32].size = 32 by native_decide]
  exact h.1

end Sha256FastWitgen

end
end Freigen.F2Z.Examples
