import Freigen.F2Z.Examples.Sha256.FastWitgenCorrectness.Interpreter

namespace Freigen.F2Z.Examples

open Freigen.F2Z.Semantics

noncomputable section

/-! ## Composition boundaries

These lemmas are deliberately phrased over the recursive trace objects.  In
particular, proving stability by induction here prevents the simplifier from
ever unfolding all 48 schedule steps or all 64 rounds. -/

theorem scheduleTrace_preserves (xs : List Nat)
    (h : Vector.TraceRel s us values) (wv : Vector (BitVec 32) 64) :
    Vector.TraceRel (scheduleTrace xs s wv).state us values := by
  induction xs generalizing s wv with
  | nil => exact h
  | cons i xs ih =>
      exact ih (h.lift (natBits 34 (scheduleWide i wv)).toArray)
        (wv.set! i (scheduleStepBV i wv))

theorem roundsTrace_preserves (xs : List Nat) (wv : Vector (BitVec 32) 64)
    (rv : RoundState (BitVec 32)) (h : Vector.TraceRel s us values) :
    Vector.TraceRel (roundsTrace xs s wv rv).state us values := by
  induction xs generalizing s rv with
  | nil => exact h
  | cons i xs ih =>
      exact ih (roundStepBV i wv rv)
        ((h.lift (natBits 35 (roundEWide i wv rv)).toArray).lift
          (natBits 35 (roundAWide i wv rv)).toArray)

theorem finishValues_eight (hcount : 8 ≤ 8) (sv : Vector (BitVec 32) 8)
    (rv : RoundState (BitVec 32)) :
    finishValues 8 hcount sv rv = finishBV sv rv := by
  unfold finishValues
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_ofFn]
  change BitVec.ofNat 32
      (finishWide (Fin.castLE hcount (show Fin 8 from ⟨i, hi⟩)) sv rv) =
    (finishBV sv rv)[(show Fin 8 from ⟨i, hi⟩)]
  have hfin : Fin.castLE hcount (show Fin 8 from ⟨i, hi⟩) = ⟨i, hi⟩ :=
    Fin.ext rfl
  rw [hfin]
  rw [finishBV_get]
  unfold finishWide
  rw [BitVec.ofNat_add]
  simp

def permutationScheduleTrace (state : Witgen.State)
    (mv : Vector (BitVec 32) 16) : ScheduleTrace :=
  scheduleTrace [16:64].toList state (initialSchedule mv)

def permutationRoundsTrace (state : Witgen.State)
    (mv : Vector (BitVec 32) 16) (sv : Vector (BitVec 32) 8) : RoundsTrace :=
  let sched := permutationScheduleTrace state mv
  roundsTrace [0:64].toList sched.state sched.words (initialRound sv)

def permutationFinalState (state : Witgen.State)
    (mv : Vector (BitVec 32) 16) (sv : Vector (BitVec 32) 8) : Witgen.State :=
  let rounds := permutationRoundsTrace state mv sv
  finishState 8 (by omega) rounds.state sv rounds.round

theorem permutationScheduleTrace_words (state : Witgen.State)
    (mv : Vector (BitVec 32) 16) :
    (permutationScheduleTrace state mv).words = scheduleBV mv := by
  rfl

theorem permutationRoundsTrace_round (state : Witgen.State)
    (mv : Vector (BitVec 32) 16) (sv : Vector (BitVec 32) 8) :
    (permutationRoundsTrace state mv sv).round =
      roundsBV (scheduleBV mv) sv := by
  rfl

theorem initialRound_traceRel (h : Vector.TraceRel s us values) :
    RoundState.TraceRel s
      ⟨us[0], us[1], us[2], us[3], us[4], us[5], us[6], us[7]⟩
      (initialRound values) := by
  exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7⟩

def structuredWitgen (m : Vector (Word 32) 16)
    (s : Vector (Word 32) 8) : Circuit (Vector (U 32) 8) := do
  let su ← s.mapM U.fromWord
  let mut w : Vector (U 32) 64 := default
  for _hi:i in (List.range' [0:16].start [0:16].size [0:16].step) do
    w := w.set! i $ ←U.fromWord m[i]!
  for _hi:i in (List.range' [16:64].start [16:64].size [16:64].step) do
    w := w.set! i $ ←scheduleStep i w
  let mut r : RoundState (U 32) :=
    ⟨su[0], su[1], su[2], su[3], su[4], su[5], su[6], su[7]⟩
  for hi:i in (List.range' [0:64].start [0:64].size [0:64].step) do
    r ← roundStep i (Std.Legacy.Range.mem_of_mem_range' hi) (w, r)
  finish (su, r)

theorem structuredWitgen_eq (m : Vector (Word 32) 16)
    (s : Vector (Word 32) 8) : structuredWitgen m s = structured m s := by
  unfold structuredWitgen structured
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range']
  rfl

theorem runAt_structuredWitgen (state : Witgen.State)
    {m : Vector (Word 32) 16} {mv : Vector (BitVec 32) 16}
    (hm : Word.VectorTraceRel state m mv)
    {s : Vector (Word 32) 8} {sv : Vector (BitVec 32) 8}
    (hs : Word.VectorTraceRel state s sv) :
    ∃ out : Vector (U 32) 8,
      StateT.run (Witgen.runAt (structuredWitgen m s)) state =
        some (out, permutationFinalState state mv sv) ∧
      Vector.TraceRel (permutationFinalState state mv sv) out (model mv sv) := by
  let su : Vector (U 32) 8 := Vector.ofFn fun i => fromWordResult state s[i]
  have hsu : Vector.TraceRel state su sv := fromWordVector_traceRel state hs
  let wDefault : Vector (U 32) 64 := default
  let wvDefault : Vector (BitVec 32) 64 := default
  obtain ⟨wInitial, hInitialRun, hwInitial⟩ :=
    runInitialWordsLoop
      (List.range' 0 [0:16].size) state
      (Vector.traceRel_default state) hm (by
        intro i hi
        simpa using hi)
  have hwInitial' : Vector.TraceRel state wInitial (initialSchedule mv) := by
    exact hwInitial
  obtain ⟨wSchedule, hScheduleRun, hwSchedule⟩ :=
    runScheduleLoop
      (List.range' 16 [16:64].size)
      state hwInitial' (by
      intro i hi
      exact Std.Legacy.Range.mem_of_mem_range' hi)
  let sched := permutationScheduleTrace state mv
  have hwSchedule' : Vector.TraceRel sched.state wSchedule (scheduleBV mv) := by
    rw [← permutationScheduleTrace_words state mv]
    exact hwSchedule
  have hsuSchedule : Vector.TraceRel sched.state su sv := by
    exact scheduleTrace_preserves [16:64].toList hsu (initialSchedule mv)
  let rInitial : RoundState (U 32) :=
    ⟨su[0], su[1], su[2], su[3], su[4], su[5], su[6], su[7]⟩
  have hrInitial : RoundState.TraceRel sched.state rInitial (initialRound sv) :=
    initialRound_traceRel hsuSchedule
  obtain ⟨rFinal, hRoundsRun, hrFinal⟩ :=
    runRoundsLoop
      (List.range' 0 [0:64].size)
      sched.state hwSchedule' hrInitial (by
      intro i hi
      exact Std.Legacy.Range.mem_of_mem_range' hi)
  let rounds := permutationRoundsTrace state mv sv
  have hrFinal' : RoundState.TraceRel rounds.state rFinal
      (roundsBV (scheduleBV mv) sv) := by
    rw [← permutationRoundsTrace_round state mv sv]
    exact hrFinal
  have hsuRounds : Vector.TraceRel rounds.state su sv := by
    exact roundsTrace_preserves [0:64].toList (scheduleBV mv)
      (initialRound sv) hsuSchedule
  obtain ⟨out, hFinishRun, hout, _, _⟩ :=
    runFinishPrefix 8 (by omega) rounds.state hsuRounds hrFinal'
  refine ⟨out, ?_, ?_⟩
  · unfold structuredWitgen
    rw [Freigen.F2Z.Vector.mapM_eq_ofFnM]
    rw [Witgen.runAt_bind, StateT.run_bind, runAt_ofFnM_fromWord]
    rw [Option.bind_eq_bind, Option.bind_some]
    simp only [Prod.fst, Prod.snd]
    rw [Witgen.runAt_bind, StateT.run_bind]
    rw [Witgen.runAt_forIn'_list]
    change StateT.run
      (forIn' (List.range' 0 [0:16].size) wDefault fun i hi acc =>
        Witgen.runAt (do
          let next ← U.fromWord m[i]!
          pure PUnit.unit
          pure (ForInStep.yield (acc.set! i next)))) state >>= _ = _
    rw [hInitialRun, Option.bind_eq_bind, Option.bind_some]
    rw [Witgen.runAt_bind, StateT.run_bind]
    rw [Witgen.runAt_forIn'_list]
    change StateT.run
      (forIn' (List.range' 16 [16:64].size) wInitial fun i hi acc =>
        Witgen.runAt (do
          let next ← scheduleStep i acc
          pure PUnit.unit
          pure (ForInStep.yield (acc.set! i next)))) state >>= _ = _
    rw [hScheduleRun, Option.bind_eq_bind, Option.bind_some]
    rw [Witgen.runAt_bind, StateT.run_bind]
    rw [Witgen.runAt_forIn'_list]
    change StateT.run
      (forIn' (List.range' 0 [0:64].size) rInitial fun i hi acc =>
        Witgen.runAt (do
          let next ← roundStep i
            (Std.Legacy.Range.mem_of_mem_range' hi) (wSchedule, acc)
          pure PUnit.unit
          pure (ForInStep.yield next))) sched.state >>= _ = _
    rw [hRoundsRun, Option.bind_eq_bind, Option.bind_some]
    rw [finish_eq]
    exact hFinishRun
  · rw [show permutationFinalState state mv sv =
        finishState 8 (by omega) rounds.state sv
          (roundsBV (scheduleBV mv) sv) by rfl]
    rw [show model mv sv = finishBV sv (roundsBV (scheduleBV mv) sv) by rfl]
    rw [← finishValues_eight (by omega) sv (roundsBV (scheduleBV mv) sv)]
    exact hout

theorem runAt_permCircuit (state : Witgen.State)
    {m : Vector (Word 32) 16} {mv : Vector (BitVec 32) 16}
    (hm : Word.VectorTraceRel state m mv)
    {s : Vector (Word 32) 8} {sv : Vector (BitVec 32) 8}
    (hs : Word.VectorTraceRel state s sv) :
    ∃ out : Vector (U 32) 8,
      StateT.run (Witgen.runAt (permCircuit m s)) state =
        some (out, permutationFinalState state mv sv) ∧
      Vector.TraceRel (permutationFinalState state mv sv) out (model mv sv) := by
  rw [← structured_eq, ← structuredWitgen_eq]
  exact runAt_structuredWitgen state hm hs

theorem U.TraceRel.word {n : Nat} {u : U n} {value : BitVec n}
    (h : U.TraceRel state u value) :
    Word.TraceRel state u.bits value := ⟨h.2.2, h.word_eval⟩

theorem Vector.TraceRel.words {n count : Nat} {us : Vector (U n) count}
    {values : Vector (BitVec n) count}
    (h : Vector.TraceRel state us values) :
    Word.VectorTraceRel state (us.map (·.bits)) values := by
  have hmap : us.map (·.bits) = Vector.ofFn (fun i => us[i].bits) := by
    apply Vector.ext
    intro i hi
    simp
  rw [hmap]
  intro i
  have hi : (Vector.ofFn (fun i => us[i].bits))[i] = us[i].bits := by
    change (Vector.ofFn (fun i => us[i].bits))[i.val]'i.isLt =
      (us[i.val]'i.isLt).bits
    rw [Vector.getElem_ofFn]
    rfl
  rw [hi]
  exact (h i).word


end
end Freigen.F2Z.Examples
