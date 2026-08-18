import Freigen.F2Z.Examples.Sha256.FastWitgenCorrectness.Compression

namespace Freigen.F2Z.Examples

open Freigen.F2Z.Semantics

noncomputable section

@[simp] theorem Vector.getElem_fin_ofFn (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f)[i] = f i := by
  change (Vector.ofFn f)[i.val]'i.isLt = f i
  rw [Vector.getElem_ofFn]

@[simp] theorem BitVec.getElem_fin_ofFn (f : Fin n → Bool) (i : Fin n) :
    (BitVec.ofFnLE f)[i] = f i := by
  change (BitVec.ofFnLE f)[i.val]'i.isLt = f i
  rw [BitVec.getElem_ofFnLE]

/-! ## The fixed 2 KiB circuit

The message-word definitions below are shared by the block-loop invariant.
They make the stream-order reversal explicit instead of hiding it in index
arithmetic inside the proof. -/

def sha256InputLC : Vector (LC Bool) sha2562KBMessageBits :=
  Vector.ofFn fun i => {i.val}

def sha256InputState
    (message : Vector Bool sha2562KBMessageBits) : Witgen.State :=
  { bools := message.toArray }

def messageBlockWords (block : Nat) (hblock : block < 32) :
    Vector (Word 32) 16 :=
  Vector.ofFn fun word =>
    { bitsLE := Vector.ofFn fun bit =>
        sha256InputLC[block * 512 + word.val * 32 + (31 - bit.val)]'(by
          simp [sha2562KBMessageBits, sha2562KBMessageBytes]
          omega) }

def messageBlockValues (message : Vector Bool sha2562KBMessageBits)
    (block : Nat) (hblock : block < 32) : Vector (BitVec 32) 16 :=
  Vector.ofFn fun word => BitVec.ofFnLE fun bit =>
    message[block * 512 + word.val * 32 + (31 - bit.val)]'(by
      simp [sha2562KBMessageBits, sha2562KBMessageBytes]
      omega)

theorem messageBlockWords_traceRel
    (message : Vector Bool sha2562KBMessageBits)
    (block : Nat) (hblock : block < 32) :
    Word.VectorTraceRel (sha256InputState message)
      (messageBlockWords block hblock)
      (messageBlockValues message block hblock) := by
  intro word
  constructor
  · intro extra
    apply BitVec.eq_of_getElem_eq
    intro bit hbit
    simp only [messageBlockWords, Word.eval, sha256InputLC, sha256InputState,
      appendBools, Witgen.State.boolWitness, Vector.getElem_fin_ofFn,
      Vector.getElem_ofFn, LC.eval_singleton, BitVec.getElem_ofFnLE]
    rw [getElem!_pos, getElem!_pos, Array.getElem_append_left]
    all_goals simp [sha2562KBMessageBits, sha2562KBMessageBytes]
    all_goals omega
  · apply BitVec.eq_of_getElem_eq
    intro bit hbit
    simp only [messageBlockWords, messageBlockValues, Word.eval, sha256InputLC,
      sha256InputState, Witgen.State.boolWitness, Vector.getElem_fin_ofFn,
      Vector.getElem_ofFn, LC.eval_singleton, BitVec.getElem_ofFnLE]
    rw [getElem!_pos]
    · rw [Vector.getElem_toArray]
    · simp [sha2562KBMessageBits, sha2562KBMessageBytes]
      omega

def sha256InitialValues : Vector (BitVec 32) 8 := #v[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

def sha256PaddingValues : Vector (BitVec 32) 16 := #v[
  0x80000000, 0x00000000, 0x00000000, 0x00000000,
  0x00000000, 0x00000000, 0x00000000, 0x00000000,
  0x00000000, 0x00000000, 0x00000000, 0x00000000,
  0x00000000, 0x00000000, 0x00000000, 0x00004000]

theorem sha256Word_traceRel (state : Witgen.State) (value : BitVec 32) :
    Word.TraceRel state (sha256Word value) value := by
  constructor
  · intro extra
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp [sha256Word, Word.eval]
  · apply BitVec.eq_of_getElem_eq
    intro i hi
    simp [sha256Word, Word.eval]

theorem sha256InitialState_traceRel (state : Witgen.State) :
    Word.VectorTraceRel state sha256InitialState sha256InitialValues := by
  intro i
  fin_cases i <;> exact sha256Word_traceRel state _

theorem sha256PaddingBlock_traceRel (state : Witgen.State) :
    Word.VectorTraceRel state sha2562KBPaddingBlock sha256PaddingValues := by
  intro i
  fin_cases i <;> exact sha256Word_traceRel state _

theorem Word.VectorTraceRel.lift (h : Word.VectorTraceRel s ws values)
    (extra : Array Bool) : Word.VectorTraceRel (appendBools s extra) ws values :=
  fun i => (h i).lift extra

theorem scheduleTrace_preserves_words (xs : List Nat)
    (h : Word.VectorTraceRel s ws values) (wv : Vector (BitVec 32) 64) :
    Word.VectorTraceRel (scheduleTrace xs s wv).state ws values := by
  induction xs generalizing s wv with
  | nil => exact h
  | cons i xs ih =>
      exact ih (h.lift (natBits 34 (scheduleWide i wv)).toArray)
        (wv.set! i (scheduleStepBV i wv))

theorem roundsTrace_preserves_words (xs : List Nat)
    (wv : Vector (BitVec 32) 64) (rv : RoundState (BitVec 32))
    (h : Word.VectorTraceRel s ws values) :
    Word.VectorTraceRel (roundsTrace xs s wv rv).state ws values := by
  induction xs generalizing s rv with
  | nil => exact h
  | cons i xs ih =>
      exact ih (roundStepBV i wv rv)
        ((h.lift (natBits 35 (roundEWide i wv rv)).toArray).lift
          (natBits 35 (roundAWide i wv rv)).toArray)

theorem finishState_preserves_words (count : Nat) (hcount : count ≤ 8)
    (sv : Vector (BitVec 32) 8) (rv : RoundState (BitVec 32))
    (h : Word.VectorTraceRel s ws values) :
    Word.VectorTraceRel (finishState count hcount s sv rv) ws values := by
  induction count with
  | zero => exact h
  | succ count ih =>
      exact (ih (by omega)).lift
        (natBits 33 (finishWide ⟨count, by omega⟩ sv rv)).toArray

theorem permutationFinalState_preserves_words
    (state : Witgen.State) (mv : Vector (BitVec 32) 16)
    (sv : Vector (BitVec 32) 8) (h : Word.VectorTraceRel state ws values) :
    Word.VectorTraceRel (permutationFinalState state mv sv) ws values := by
  apply finishState_preserves_words
  apply roundsTrace_preserves_words
  apply scheduleTrace_preserves_words
  exact h

structure MessageBlocksTrace where
  state : Witgen.State
  hash : Vector (BitVec 32) 8

def messageBlocksTrace : (message : Vector Bool sha2562KBMessageBits) →
    (xs : List Nat) → (∀ i ∈ xs, i < 32) → Witgen.State →
    Vector (BitVec 32) 8 → MessageBlocksTrace
  | _, [], _, state, sv => ⟨state, sv⟩
  | message, i :: xs, hxs, state, sv =>
      let mv := messageBlockValues message i (hxs i (by simp))
      let state' := permutationFinalState state mv sv
      let sv' := model mv sv
      messageBlocksTrace message xs (fun j hj => hxs j (by simp [hj])) state' sv'

theorem runMessageBlocks (message : Vector Bool sha2562KBMessageBits)
    (xs : List Nat) (hxs : ∀ i ∈ xs, i < 32)
    (state : Witgen.State)
    {s : Vector (Word 32) 8} {sv : Vector (BitVec 32) 8}
    (hs : Word.VectorTraceRel state s sv)
    (hmessage : ∀ (block : Nat) (hblock : block < 32),
      Word.VectorTraceRel state (messageBlockWords block hblock)
        (messageBlockValues message block hblock)) :
    ∃ out : Vector (Word 32) 8,
      StateT.run
          (forIn' xs s fun block hi acc => Witgen.runAt (do
            let next ← permCircuit
              (messageBlockWords block (hxs block hi)) acc
            pure PUnit.unit
            pure (ForInStep.yield (next.map (·.bits))))) state =
        some (out, (messageBlocksTrace message xs hxs state sv).state) ∧
      Word.VectorTraceRel (messageBlocksTrace message xs hxs state sv).state
        out (messageBlocksTrace message xs hxs state sv).hash ∧
      ∀ (block : Nat) (hblock : block < 32),
        Word.VectorTraceRel
          (messageBlocksTrace message xs hxs state sv).state
          (messageBlockWords block hblock)
          (messageBlockValues message block hblock) := by
  induction xs generalizing state s sv with
  | nil => exact ⟨s, rfl, hs, hmessage⟩
  | cons i xs ih =>
      have hi : i < 32 := hxs i (by simp)
      obtain ⟨next, hrun, hnext⟩ :=
        runAt_permCircuit state (hmessage i hi) hs
      let mv := messageBlockValues message i hi
      let state1 := permutationFinalState state mv sv
      let sv1 := model mv sv
      let words1 := next.map (·.bits)
      have hwords1 : Word.VectorTraceRel state1 words1 sv1 := hnext.words
      have hmessage1 : ∀ (block : Nat) (hblock : block < 32),
          Word.VectorTraceRel state1 (messageBlockWords block hblock)
            (messageBlockValues message block hblock) := by
        intro block hblock
        exact permutationFinalState_preserves_words state mv sv
          (hmessage block hblock)
      obtain ⟨out, hloop, hout, hmessageOut⟩ :=
        ih (fun j hj => hxs j (by simp [hj])) state1 hwords1 hmessage1
      refine ⟨out, ?_, hout, hmessageOut⟩
      simp only [List.forIn'_cons, StateT.run_bind]
      rw [Witgen.runAt_bind, StateT.run_bind, hrun]
      simp only [Option.bind_eq_bind, Option.bind_some, Witgen.runAt_pure,
        StateT.run_pure]
      change StateT.run
        (forIn' xs words1 fun block hi acc => Witgen.runAt (do
          let next ← permCircuit
            (messageBlockWords block (hxs block (by simp [hi]))) acc
          pure PUnit.unit
          pure (ForInStep.yield (next.map (·.bits))))) state1 = _
      rw [hloop]
      rfl

def sha256MessageTrace (message : Vector Bool sha2562KBMessageBits) :
    MessageBlocksTrace :=
  messageBlocksTrace message (List.range' 0 [0:32].size) (by
    intro i hi
    simpa using hi)
    (sha256InputState message) sha256InitialValues

def sha256GenericFinalState
    (message : Vector Bool sha2562KBMessageBits) : Witgen.State :=
  let trace := sha256MessageTrace message
  permutationFinalState trace.state sha256PaddingValues trace.hash

def sha2562KBCircuitWitgen : Circuit (Vector (LC Bool) 256) := do
  let mut state := sha256InitialState
  for hi:block in (List.range' 0 [0:32].size) do
    let words := messageBlockWords block (by simpa using hi)
    let nextState ← permCircuit words state
    state := nextState.map (·.bits)
  let digest ← permCircuit sha2562KBPaddingBlock state
  pure $ Vector.ofFn fun i =>
    digest[i.val / 32].bits.bitsLE[31 - (i.val % 32)]

theorem sha2562KBCircuitWitgen_eq :
    sha2562KBCircuitWitgen = sha2562KBCircuit sha256InputLC := by
  unfold sha2562KBCircuitWitgen sha2562KBCircuit
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range']
  rfl

theorem runAt_sha2562KBCircuit
    (message : Vector Bool sha2562KBMessageBits) :
    ∃ digest : Vector (U 32) 8,
      StateT.run (Witgen.runAt sha2562KBCircuitWitgen)
          (sha256InputState message) =
        some
          (Vector.ofFn (fun i =>
            digest[i.val / 32].bits.bitsLE[31 - (i.val % 32)]),
            sha256GenericFinalState message) := by
  have hblocks : ∀ i ∈ List.range' 0 [0:32].size, i < 32 := by
    intro i hi
    simpa using hi
  obtain ⟨stateWords, hMessageRun, hStateWords, _⟩ :=
    runMessageBlocks message (List.range' 0 [0:32].size) hblocks
      (sha256InputState message)
      (sha256InitialState_traceRel (sha256InputState message))
      (fun block hblock => messageBlockWords_traceRel message block hblock)
  let trace := sha256MessageTrace message
  have htraceEq : messageBlocksTrace message (List.range' 0 [0:32].size)
      hblocks (sha256InputState message) sha256InitialValues = trace := by
    unfold trace sha256MessageTrace
    rfl
  rw [htraceEq] at hMessageRun hStateWords
  obtain ⟨digest, hPaddingRun, _⟩ :=
    runAt_permCircuit trace.state
      (sha256PaddingBlock_traceRel trace.state) hStateWords
  refine ⟨digest, ?_⟩
  unfold sha2562KBCircuitWitgen
  rw [Witgen.runAt_bind, StateT.run_bind]
  rw [Witgen.runAt_forIn'_list]
  change StateT.run
    (forIn' (List.range' 0 [0:32].size) sha256InitialState fun block hi acc =>
      Witgen.runAt (do
        let next ← permCircuit (messageBlockWords block (hblocks block hi)) acc
        pure PUnit.unit
        pure (ForInStep.yield (next.map (·.bits)))))
      (sha256InputState message) >>= _ = _
  rw [hMessageRun, Option.bind_eq_bind, Option.bind_some]
  rw [Witgen.runAt_bind, StateT.run_bind]
  simp only [Prod.fst, Prod.snd]
  change StateT.run (Witgen.runAt
      (permCircuit sha2562KBPaddingBlock stateWords)) trace.state >>= _ = _
  rw [hPaddingRun, Option.bind_eq_bind, Option.bind_some]
  simp [Witgen.runAt, sha256GenericFinalState, trace]

theorem witgen_sha2562KBCircuit_eq_genericState
    (message : Vector Bool sha2562KBMessageBits) :
    Witgen.runWithInputs sha2562KBCircuit message =
      some (sha256GenericFinalState message).bools := by
  unfold Witgen.runWithInputs
  change Witgen.run (sha2562KBCircuit sha256InputLC)
    (sha256InputState message) = _
  obtain ⟨digest, hrun⟩ := runAt_sha2562KBCircuit message
  rw [← sha2562KBCircuitWitgen_eq]
  unfold Witgen.run Witgen.run'
  rw [hrun]
  rfl


end
end Freigen.F2Z.Examples
