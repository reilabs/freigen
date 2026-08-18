import Freigen.F2Z.Examples.Sha256.FastWitgenCorrectness.FastFull

namespace Freigen.F2Z.Examples

open Freigen.F2Z.Semantics

noncomputable section

namespace Sha256FastWitgen

/-! ## The Boolean-input adapter -/

theorem list_ofFn_eq_map_ofFn_id {n : Nat} {α : Type}
    (f : Fin n → α) :
    List.ofFn f = List.map f (List.ofFn id) := by
  rw [List.map_ofFn]
  rfl

theorem vector_ofFn_flatten_toList {n m : Nat} {α : Type}
    (f : Fin n → Fin m → α) :
    (Vector.ofFn fun i => Vector.ofFn (f i)).flatten.toList =
      List.flatMap (fun i => List.ofFn (f i)) (List.ofFn id) := by
  unfold Vector.toList Vector.flatten
  rw [Array.toList_flatten, Array.toList_map]
  simp only [Vector.toArray_ofFn, Array.toList_ofFn]
  rw [list_ofFn_eq_map_ofFn_id]
  simp only [List.map_map, Function.comp_def, Vector.toArray_ofFn,
    Array.toList_ofFn]
  rfl

def PackWordRel (packed : UInt64)
    (message : Vector Bool sha2562KBMessageBits) (base next : Nat) : Prop :=
  ∀ bit (_hbit : bit < 64), packed.toBitVec.getLsbD bit =
    if bit < next then message[base + bit]! else false

theorem uint64_shifted_one_getLsbD (bit i : Nat) (hbit : bit < 64) :
    ((1 : UInt64) <<< UInt64.ofNat bit).toBitVec.getLsbD i = decide (i = bit) := by
  rw [UInt64.toBitVec_shiftLeft, uint64_shiftAmount bit hbit]
  rw [UInt64.toBitVec_ofNat]
  rw [BitVec.shiftLeft_ofNat_eq]
  norm_num
  rw [Nat.mod_eq_of_lt (by omega : bit < 18446744073709551616)]
  by_cases hieq : i = bit
  · subst i
    simp [hbit]
  · by_cases hi : i < 64
    · simp [hieq, hi]
      omega
    · simp [hieq, hi]

theorem packMessageWordLoop_refines
    (message : Vector Bool sha2562KBMessageBits) (base bit remaining : Nat)
    (hremaining : bit + remaining ≤ 64)
    (packed : UInt64) (hpacked : PackWordRel packed message base bit) :
    PackWordRel (packMessageWordLoop message base bit remaining packed)
      message base (bit + remaining) := by
  induction remaining generalizing bit packed with
  | zero => simpa [packMessageWordLoop] using hpacked
  | succ remaining ih =>
      have hbit : bit < 64 := by omega
      let value := message[base + bit]!
      let packed' := if value then packed ||| (1 <<< UInt64.ofNat bit)
        else packed
      have hpacked' : PackWordRel packed' message base (bit + 1) := by
        intro i hi
        unfold packed' value
        cases hvalue : message[base + bit]!
        · simp only [Bool.false_eq_true, if_false]
          rw [hpacked i hi]
          by_cases hieq : i = bit
          · subst i
            simp [hvalue]
          · by_cases hil : i < bit
            · have hil' : i < bit + 1 := by omega
              simp [hil, hil']
            · have hil' : ¬i < bit + 1 := by omega
              simp [hil, hil']
        · simp only [if_true, UInt64.toBitVec_or, BitVec.getLsbD_or,
            uint64_shifted_one_getLsbD bit i hbit]
          rw [hpacked i hi]
          by_cases hieq : i = bit
          · subst i
            simp [hvalue]
          · by_cases hil : i < bit
            · have hil' : i < bit + 1 := by omega
              simp [hieq, hil, hil']
            · have hil' : ¬i < bit + 1 := by omega
              simp [hieq, hil, hil']
      rw [packMessageWordLoop]
      change PackWordRel
        (packMessageWordLoop message base (bit + 1) remaining packed')
        message base (bit + (remaining + 1))
      convert ih (bit := bit + 1) (packed := packed') (by omega) hpacked' using 1 <;> omega

theorem packMessageWordLoop_final_bit
    (message : Vector Bool sha2562KBMessageBits) (base bit : Nat)
    (hbit : bit < 64) :
    (packMessageWordLoop message base 0 64 0).toBitVec.getLsbD bit =
      message[base + bit]! := by
  have hinitial : PackWordRel 0 message base 0 := by
    intro i hi
    simp
  have hfinal := packMessageWordLoop_refines message base 0 64
    (by omega) 0 hinitial
  simpa [hbit] using hfinal bit hbit

theorem packSha2562KBMessage_bit (message : Vector Bool sha2562KBMessageBits)
    (word : Nat) (hword : word < 256) (bit : Nat) (hbit : bit < 64) :
    (packSha2562KBMessage message)[word]!.toBitVec.getLsbD bit =
      message[word * 64 + bit]! := by
  rw [getElem!_pos (packSha2562KBMessage message) word hword]
  unfold packSha2562KBMessage
  rw [Vector.getElem_ofFn]
  exact packMessageWordLoop_final_bit message (word * 64) bit hbit

theorem packSha2562KBMessage_rel
    (message : Vector Bool sha2562KBMessageBits) :
    PackedMessageRel (packSha2562KBMessage message) message := by
  constructor
  · unfold packSha2562KBMessage
    simp only [Vector.toList_ofFn]
    have hchunk (word : Fin 256) :
        uint64PrefixBits
            (packMessageWordLoop message (word.val * 64) 0 64 0) 64 =
          List.ofFn fun bit : Fin 64 =>
            message[word.val * 64 + bit.val]'(by
              simp [sha2562KBMessageBits, sha2562KBMessageBytes]
              omega) := by
      apply List.ext_getElem (by simp)
      intro i hi1 hi2
      have hi : i < 64 := by simpa using hi1
      rw [uint64PrefixBits_getElem _ 64 i hi]
      rw [packMessageWordLoop_final_bit message (word.val * 64) i hi]
      rw [List.getElem_ofFn]
      rw [getElem!_pos message (word.val * 64 + i) (by
        simp [sha2562KBMessageBits, sha2562KBMessageBytes]
        omega)]
    have hmap :
        (List.ofFn fun word : Fin 256 =>
          packMessageWordLoop message (word.val * 64) 0 64 0) =
          List.map (fun word : Fin 256 =>
            packMessageWordLoop message (word.val * 64) 0 64 0)
            (List.ofFn id) := by
      exact list_ofFn_eq_map_ofFn_id _
    rw [hmap, List.flatMap_map]
    simp_rw [hchunk]
    let chunks : Vector (Vector Bool 64) 256 :=
      Vector.ofFn fun word => Vector.ofFn fun bit =>
        message[word.val * 64 + bit.val]'(by
          simp [sha2562KBMessageBits, sha2562KBMessageBytes]
          omega)
    have hflatten : chunks.flatten = message := by
      apply Vector.ext
      intro i hi
      rw [Vector.getElem_flatten hi]
      simp only [chunks, Vector.getElem_ofFn]
      congr 1
      omega
    have hchunksList : chunks.flatten.toList =
        List.flatMap (fun word : Fin 256 =>
          List.ofFn fun bit : Fin 64 =>
            message[word.val * 64 + bit.val]'(by
              simp [sha2562KBMessageBits, sha2562KBMessageBytes]
              omega)) (List.ofFn id) := by
      exact vector_ofFn_flatten_toList _
    rw [← hchunksList, hflatten]
    rfl
  · exact packSha2562KBMessage_bit message

theorem fastBuilder_refines (h : PackedMessageRel packed message) :
    let prepared := preparePackedInput packed
    let result := compressBlocksLoop prepared.1 0 33 initialState prepared.2
    BuilderRefines result.2 (sha256GenericFinalState message).bools.toList := by
  generalize hprepared : preparePackedInput packed = prepared
  rcases prepared with ⟨blocks, builder⟩
  have hpreparedRefines := preparePackedInput_refines h
  rw [hprepared] at hpreparedRefines
  obtain ⟨hblocks, hbuilder⟩ := hpreparedRefines
  generalize hresult : compressBlocksLoop blocks 0 33 initialState builder = result
  generalize htrace : preparedBlocksTrace message 0 33 (by omega)
    (sha256InputState message) sha256InitialValues = trace
  have hloop := compressBlocksLoop_refines message blocks 0 33 (by omega)
    initialState builder (sha256InputState message) sha256InitialValues
    hblocks initialState_toVector hbuilder
  rw [hresult, htrace] at hloop
  dsimp only at hloop
  have htraceState : trace.state = sha256GenericFinalState message := by
    rw [← htrace]
    exact preparedFullTrace_state message
  rw [htraceState] at hloop
  change BuilderRefines (compressBlocksLoop blocks 0 33 initialState builder).2
    (sha256GenericFinalState message).bools.toList
  rw [hresult]
  exact hloop.2

/-! ## Packed-output embedding -/

/-- `Embeds witness bits` means that unpacking the witness words in
least-significant-bit-first order, and retaining exactly the logical witness
length, gives `bits`.  It intentionally does not require an `Array Bool`
materialization. -/
def Sha2562KBPackedWitness.Embeds (witness : Sha2562KBPackedWitness)
    (bits : List Bool) : Prop :=
  (witness.words.toList.flatMap (fun word => uint64PrefixBits word 64)).take
    bits.length = bits

theorem uint64PrefixBits_take (word : UInt64) (width : Nat)
    (hwidth : width ≤ 64) :
    (uint64PrefixBits word 64).take width = uint64PrefixBits word width := by
  apply List.ext_getElem (by simp [hwidth])
  intro i hi1 hi2
  have hi : i < width := by simpa using hi2
  rw [List.getElem_take]
  rw [uint64PrefixBits_getElem word 64 i (by omega)]
  rw [uint64PrefixBits_getElem word width i hi]

theorem finishWords_embeds (builder : WitnessBuilder) (bits : List Bool)
    (hbuilder : BuilderRefines builder bits) :
    let words := if builder.pendingBits = 0 then builder.words
      else builder.words.push builder.pending
    Sha2562KBPackedWitness.Embeds ⟨words⟩ bits := by
  have hpending_lt := hbuilder.pendingBits_lt
  rw [← hbuilder.bits_eq]
  unfold Sha2562KBPackedWitness.Embeds WitnessBuilder.bits
  by_cases hpending : builder.pendingBits = 0
  · simp [hpending, uint64PrefixBits]
  · simp only [hpending, if_false, Array.toList_push, List.flatMap_append,
      List.flatMap_singleton, List.length_append, uint64PrefixBits_length]
    rw [List.take_append]
    rw [List.take_of_length_le (by omega)]
    rw [show (builder.words.toList.flatMap
        (fun word => uint64PrefixBits word 64)).length + builder.pendingBits -
          (builder.words.toList.flatMap
            (fun word => uint64PrefixBits word 64)).length =
        builder.pendingBits by omega]
    rw [uint64PrefixBits_take builder.pending builder.pendingBits
      (by omega : builder.pendingBits ≤ 64)]

theorem sha2562KBFastWitgen_eq_finish (packed : Sha2562KBPackedMessage) :
    sha2562KBFastWitgen packed =
      let prepared := preparePackedInput packed
      let result := compressBlocksLoop prepared.1 0 33 initialState prepared.2
      let builder := result.2
      ⟨if builder.pendingBits = 0 then builder.words
        else builder.words.push builder.pending⟩ := by
  rfl

theorem sha2562KBFastWitgen_embeds (h : PackedMessageRel packed message) :
    Sha256FastWitgen.Sha2562KBPackedWitness.Embeds
      (sha2562KBFastWitgen packed)
      (sha256GenericFinalState message).bools.toList := by
  rw [sha2562KBFastWitgen_eq_finish]
  exact finishWords_embeds _ _ (fastBuilder_refines h)

/-! ## End-to-end statement against the generic interpreter -/

theorem sha2562KBFastWitgen_correct (h : PackedMessageRel packed message) :
    Witgen.runWithInputs sha2562KBCircuit message =
        some (sha256GenericFinalState message).bools ∧
      Sha256FastWitgen.Sha2562KBPackedWitness.Embeds
        (sha2562KBFastWitgen packed)
        (sha256GenericFinalState message).bools.toList :=
  ⟨witgen_sha2562KBCircuit_eq_genericState message,
    sha2562KBFastWitgen_embeds h⟩

/-- The optimized packed witgen is equal to `Witgen.runWithInputs`, up to
the explicit least-significant-bit-first embedding of packed `UInt64` words. -/
theorem sha2562KBFastWitgen_eq_runWithInputs_upToEmbedding
    (h : PackedMessageRel packed message) :
    ∃ bits : Array Bool,
      Witgen.runWithInputs sha2562KBCircuit message = some bits ∧
      Sha256FastWitgen.Sha2562KBPackedWitness.Embeds
        (sha2562KBFastWitgen packed) bits.toList := by
  exact ⟨(sha256GenericFinalState message).bools,
    witgen_sha2562KBCircuit_eq_genericState message,
    sha2562KBFastWitgen_embeds h⟩

end Sha256FastWitgen

end
end Freigen.F2Z.Examples
