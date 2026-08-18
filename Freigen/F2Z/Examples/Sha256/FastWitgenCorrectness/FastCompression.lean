import Freigen.F2Z.Examples.Sha256.FastWitgenCorrectness.Packing

namespace Freigen.F2Z.Examples

open Freigen.F2Z.Semantics

noncomputable section

namespace Sha256FastWitgen

/-! ## `UInt32` SHA operations -/

def HashState.toVector (s : HashState) : Vector (BitVec 32) 8 :=
  #v[s.s0.toBitVec, s.s1.toBitVec, s.s2.toBitVec, s.s3.toBitVec,
    s.s4.toBitVec, s.s5.toBitVec, s.s6.toBitVec, s.s7.toBitVec]

theorem initialState_toVector : initialState.toVector = sha256InitialValues := by
  rfl

theorem smallSigma0_toBitVec (x : UInt32) :
    (smallSigma0 x).toBitVec = smallSigma0BV x.toBitVec := by
  unfold smallSigma0 smallSigma0BV rotateRight BitVec.rotateRight
    BitVec.rotateRightAux
  simp only [UInt32.toBitVec_xor, UInt32.toBitVec_or,
    UInt32.toBitVec_shiftRight, UInt32.toBitVec_shiftLeft]
  generalize x.toBitVec = y
  bv_decide

theorem smallSigma1_toBitVec (x : UInt32) :
    (smallSigma1 x).toBitVec = smallSigma1BV x.toBitVec := by
  unfold smallSigma1 smallSigma1BV rotateRight BitVec.rotateRight
    BitVec.rotateRightAux
  simp only [UInt32.toBitVec_xor, UInt32.toBitVec_or,
    UInt32.toBitVec_shiftRight, UInt32.toBitVec_shiftLeft]
  generalize x.toBitVec = y
  bv_decide

theorem bigSigma0_toBitVec (x : UInt32) :
    (bigSigma0 x).toBitVec = bigSigma0BV x.toBitVec := by
  unfold bigSigma0 bigSigma0BV rotateRight BitVec.rotateRight
    BitVec.rotateRightAux
  simp only [UInt32.toBitVec_xor, UInt32.toBitVec_or,
    UInt32.toBitVec_shiftRight, UInt32.toBitVec_shiftLeft]
  generalize x.toBitVec = y
  bv_decide

theorem bigSigma1_toBitVec (x : UInt32) :
    (bigSigma1 x).toBitVec = bigSigma1BV x.toBitVec := by
  unfold bigSigma1 bigSigma1BV rotateRight BitVec.rotateRight
    BitVec.rotateRightAux
  simp only [UInt32.toBitVec_xor, UInt32.toBitVec_or,
    UInt32.toBitVec_shiftRight, UInt32.toBitVec_shiftLeft]
  generalize x.toBitVec = y
  bv_decide

theorem choose_toBitVec (e f g : UInt32) :
    (choose e f g).toBitVec = chBV e.toBitVec f.toBitVec g.toBitVec := by
  rfl

theorem majority_toBitVec (a b c : UInt32) :
    (majority a b c).toBitVec = majBV a.toBitVec b.toBitVec c.toBitVec := by
  rfl

/-! ## Array and working-state representations -/

def ScheduleArrayRel (schedule : Array UInt32) (count : Nat)
    (values : Vector (BitVec 32) 64) : Prop :=
  schedule.size = count ∧
    ∀ i (hi : i < schedule.size), schedule[i].toBitVec = values[i]!

theorem Vector.set!_eq_set (values : Vector α n) (i : Nat) (value : α)
    (hi : i < n) : values.set! i value = values.set i value hi := by
  unfold Vector.set! Array.set! Array.setIfInBounds
  simp [hi, Vector.set]

theorem ScheduleArrayRel.getElem! (h : ScheduleArrayRel schedule count values)
    (i : Nat) (hi : i < count) : schedule[i]!.toBitVec = values[i]! := by
  rw [getElem!_pos schedule i (by rw [h.1]; exact hi)]
  exact h.2 i (by rw [h.1]; exact hi)

theorem ScheduleArrayRel.push (h : ScheduleArrayRel schedule count values)
    (value : UInt32) (hvalue : value.toBitVec = next) (hcount : count < 64) :
    ScheduleArrayRel (schedule.push value) (count + 1)
      (values.set! count next) := by
  constructor
  · simpa using h.1
  · intro i hi
    rw [Array.getElem_push]
    rw [Vector.set!_eq_set values count next hcount]
    split <;> rename_i hold
    · have hi64 : i < 64 := by rw [h.1] at hold; omega
      have hine : count ≠ i := by rw [h.1] at hold; omega
      rw [getElem!_pos (values.set count next hcount) i hi64]
      rw [Vector.getElem_set_ne hcount hi64 hine]
      simpa [getElem!_pos values i hi64] using h.2 i hold
    · have hic : i = count := by
        simp only [Array.size_push, h.1] at hi
        rw [h.1] at hold
        omega
      subst i
      rw [getElem!_pos (values.set count next hcount) count (by omega)]
      rw [Vector.getElem_set]
      simp only [if_pos rfl]
      exact hvalue

def BlockArrayRel (blocks : Array UInt32) (block : Nat)
    (values : Vector (BitVec 32) 16) : Prop :=
  ∀ i (hi : i < 16), blocks[block * 16 + i]!.toBitVec = values[i]!

theorem initialScheduleRange_rel (blocks : Array UInt32) (block start len : Nat)
    (hbound : start + len ≤ 16) (hblock : BlockArrayRel blocks block mv)
    (hrel : ScheduleArrayRel schedule start values) :
    ScheduleArrayRel
      ((List.range' start len).foldl
        (fun schedule i => schedule.push blocks[block * 16 + i]!) schedule)
      (start + len)
      ((List.range' start len).foldl
        (fun values i => values.set! i mv[i]!) values) := by
  induction len generalizing start schedule values with
  | zero => simpa using hrel
  | succ len ih =>
      rw [List.range'_succ, List.foldl_cons, List.foldl_cons]
      have hnext := hrel.push blocks[block * 16 + start]!
        (hblock start (by omega)) (by omega)
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (start + 1) (by omega) hnext

theorem initialScheduleWordsLoop_eq_fold (blocks : Array UInt32)
    (block start len : Nat) (schedule : Array UInt32) :
    initialScheduleWordsLoop blocks block start len schedule =
      (List.range' start len).foldl
        (fun schedule i => schedule.push blocks[block * 16 + i]!) schedule := by
  induction len generalizing start schedule with
  | zero => rfl
  | succ len ih =>
      rw [List.range'_succ, List.foldl_cons]
      unfold initialScheduleWordsLoop
      exact ih (start + 1) (schedule.push blocks[block * 16 + start]!)

theorem initialScheduleWords_rel (blocks : Array UInt32) (block : Nat)
    (hblock : BlockArrayRel blocks block mv) :
    ScheduleArrayRel (initialScheduleWords blocks block) 16
      (initialSchedule mv) := by
  unfold initialScheduleWords
  rw [initialScheduleWordsLoop_eq_fold]
  have hrange : [0:16].toList = List.range' 0 16 := by native_decide
  simp only [initialSchedule, hrange]
  simpa using
    (initialScheduleRange_rel blocks block 0 16 (by omega) hblock
      (schedule := Array.mkEmpty 64) (values := default)
      (by constructor <;> simp [ScheduleArrayRel]))

def WorkingState.toRoundState (working : WorkingState) :
    RoundState (BitVec 32) :=
  ⟨working.a.toBitVec, working.b.toBitVec, working.c.toBitVec,
    working.d.toBitVec, working.e.toBitVec, working.f.toBitVec,
    working.g.toBitVec, working.h.toBitVec⟩

theorem WorkingState.ofHashState_toRoundState (state : HashState) :
    (WorkingState.ofHashState state).toRoundState =
      initialRound state.toVector := by
  rfl

/-! ## Exact wide arithmetic -/

theorem uint64Sum2_toNat (a b : UInt32) :
    (a.toUInt64 + b.toUInt64).toNat = a.toNat + b.toNat := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  simp only [UInt64.toNat_add, UInt32.toNat_toUInt64]
  norm_num at ha hb ⊢
  omega

theorem uint64Sum4_toNat (a b c d : UInt32) :
    (a.toUInt64 + b.toUInt64 + c.toUInt64 + d.toUInt64).toNat =
      a.toNat + b.toNat + c.toNat + d.toNat := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  simp only [UInt64.toNat_add, UInt32.toNat_toUInt64]
  norm_num at ha hb hc hd ⊢
  omega

theorem uint64Sum6_toNat (a b c d e f : UInt32) :
    (a.toUInt64 + b.toUInt64 + c.toUInt64 + d.toUInt64 +
      e.toUInt64 + f.toUInt64).toNat =
      a.toNat + b.toNat + c.toNat + d.toNat + e.toNat + f.toNat := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  have he := e.toNat_lt
  have hf := f.toNat_lt
  simp only [UInt64.toNat_add, UInt32.toNat_toUInt64]
  norm_num at ha hb hc hd he hf ⊢
  omega

theorem uint64Sum7_toNat (a b c d e f g : UInt32) :
    (a.toUInt64 + b.toUInt64 + c.toUInt64 + d.toUInt64 +
      e.toUInt64 + f.toUInt64 + g.toUInt64).toNat =
      a.toNat + b.toNat + c.toNat + d.toNat + e.toNat + f.toNat +
        g.toNat := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  have he := e.toNat_lt
  have hf := f.toNat_lt
  have hg := g.toNat_lt
  simp only [UInt64.toNat_add, UInt32.toNat_toUInt64]
  norm_num at ha hb hc hd he hf hg ⊢
  omega

theorem UInt32.toNat_eq_of_toBitVec_eq {x : UInt32} {value : BitVec 32}
    (h : x.toBitVec = value) : x.toNat = value.toNat := by
  rw [← UInt32.toNat_toBitVec]
  exact congrArg BitVec.toNat h

theorem UInt64.toUInt32_toBitVec (x : UInt64) :
    x.toUInt32.toBitVec = BitVec.ofNat 32 x.toNat := by
  rw [BitVec.toNat_eq]
  simp [UInt64.toNat_toUInt32]

def fastScheduleWide (schedule : Array UInt32) (i : Nat) : UInt64 :=
  schedule[i - 16]!.toUInt64 +
    (smallSigma0 schedule[i - 15]!).toUInt64 +
    schedule[i - 7]!.toUInt64 +
    (smallSigma1 schedule[i - 2]!).toUInt64

theorem fastScheduleWide_toNat (h : ScheduleArrayRel schedule count values)
    (i : Nat) (hi16 : 16 ≤ i) (hicount : i - 2 < count) :
    (fastScheduleWide schedule i).toNat = scheduleWide i values := by
  have h16 := h.getElem! (i - 16) (by omega)
  have h15 := h.getElem! (i - 15) (by omega)
  have h7 := h.getElem! (i - 7) (by omega)
  have h2 := h.getElem! (i - 2) (by omega)
  unfold fastScheduleWide scheduleWide
  rw [uint64Sum4_toNat]
  rw [UInt32.toNat_eq_of_toBitVec_eq h16]
  rw [UInt32.toNat_eq_of_toBitVec_eq h7]
  rw [UInt32.toNat_eq_of_toBitVec_eq
    (smallSigma0_toBitVec schedule[i - 15]!)]
  rw [UInt32.toNat_eq_of_toBitVec_eq
    (smallSigma1_toBitVec schedule[i - 2]!)]
  rw [h15, h2]

theorem fastScheduleWide_toBitVec
    (h : ScheduleArrayRel schedule count values)
    (i : Nat) (hi16 : 16 ≤ i) (hicount : i - 2 < count) :
    (fastScheduleWide schedule i).toUInt32.toBitVec =
      scheduleStepBV i values := by
  rw [UInt64.toUInt32_toBitVec, fastScheduleWide_toNat h i hi16 hicount]
  exact (scheduleStepBV_eq i values).symm

structure FastScheduleState where
  builder : WitnessBuilder
  schedule : Array UInt32

def fastScheduleStep (i : Nat) (x : FastScheduleState) :
    FastScheduleState :=
  let wide := fastScheduleWide x.schedule i
  { builder := appendBitsLE x.builder wide 34
    schedule := x.schedule.push wide.toUInt32 }

def fastScheduleLoop (xs : List Nat) (x : FastScheduleState) :
    FastScheduleState := xs.foldl (fun x i => fastScheduleStep i x) x

theorem extendScheduleWordsLoop_eq_fast (start len : Nat)
    (schedule : Array UInt32) (builder : WitnessBuilder) :
    extendScheduleWordsLoop start len schedule builder =
      let result := fastScheduleLoop (List.range' start len)
        ⟨builder, schedule⟩
      (result.schedule, result.builder) := by
  induction len generalizing start schedule builder with
  | zero => rfl
  | succ len ih =>
      rw [List.range'_succ]
      unfold fastScheduleLoop
      rw [List.foldl_cons]
      unfold extendScheduleWordsLoop fastScheduleStep fastScheduleWide
      exact ih (start + 1) _ _

theorem appendNatBits_bools_toList (state : Witgen.State) (width value : Nat) :
    (appendNatBits state width value).bools.toList =
      state.bools.toList ++ (natBits width value).toList := by
  simp only [appendNatBits, Array.toList_append]
  rw [Vector.toList_toArray]

theorem fastScheduleRange_refines (start len : Nat)
    (hstart : 16 ≤ start) (hbound : start + len ≤ 64)
    (hschedule : ScheduleArrayRel schedule start values)
    (hbuilder : BuilderRefines builder state.bools.toList) :
    let result := fastScheduleLoop (List.range' start len)
      ⟨builder, schedule⟩
    let trace := scheduleTrace (List.range' start len) state values
    ScheduleArrayRel result.schedule (start + len) trace.words ∧
      BuilderRefines result.builder trace.state.bools.toList := by
  induction len generalizing start schedule values state builder with
  | zero => exact ⟨hschedule, hbuilder⟩
  | succ len ih =>
      rw [List.range'_succ]
      simp only [fastScheduleLoop, List.foldl_cons, scheduleTrace,
        scheduleTraceStep]
      let wide := fastScheduleWide schedule start
      have hwideNat : wide.toNat = scheduleWide start values :=
        fastScheduleWide_toNat hschedule start hstart (by omega)
      have hwideBV : wide.toUInt32.toBitVec =
          scheduleStepBV start values :=
        fastScheduleWide_toBitVec hschedule start hstart (by omega)
      have hwideLt : wide.toNat < 2 ^ 34 := by
        rw [hwideNat]
        exact scheduleWide_lt start values
      have hbuilder' : BuilderRefines (appendBitsLE builder wide 34)
          (appendNatBits state 34 (scheduleWide start values)).bools.toList := by
        have happend := appendBitsLE_refines hbuilder wide 34 (by omega) hwideLt
        rw [appendNatBits_bools_toList]
        rw [uint64PrefixBits_eq_natBits, hwideNat] at happend
        exact happend
      have hschedule' : ScheduleArrayRel (schedule.push wide.toUInt32)
          (start + 1) (values.set! start (scheduleStepBV start values)) :=
        hschedule.push wide.toUInt32 hwideBV (by omega)
      have hcount : start + (len + 1) = start + 1 + len := by omega
      rw [hcount]
      simpa only [fastScheduleLoop, scheduleTrace, scheduleTraceStep,
        fastScheduleStep, wide,
        Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using
        ih (start + 1) (by omega) (by omega) hschedule' hbuilder'

theorem extendScheduleWords_refines
    (hschedule : ScheduleArrayRel schedule 16 values)
    (hbuilder : BuilderRefines builder state.bools.toList) :
    let result := extendScheduleWords schedule builder
    let trace := scheduleTrace [16:64].toList state values
    ScheduleArrayRel result.1 64 trace.words ∧
      BuilderRefines result.2 trace.state.bools.toList := by
  unfold extendScheduleWords
  rw [extendScheduleWordsLoop_eq_fast]
  have hrange : [16:64].toList = List.range' 16 48 := by native_decide
  rw [hrange]
  simpa [fastScheduleLoop] using
    (fastScheduleRange_refines 16 48 (by omega) (by omega)
      hschedule hbuilder)

/-! ## Round body and round loop -/

theorem roundConstants_toBitVec (i : Nat) (hi : i < 64) :
    roundConstants[i]!.toBitVec = k[i]! := by
  interval_cases i <;> native_decide

theorem roundEWideUInt64_toNat
    (hschedule : ScheduleArrayRel schedule 64 values)
    (i : Nat) (hi : i < 64) (working : WorkingState) :
    (roundEWideUInt64 schedule i working).toNat =
      roundEWide i values working.toRoundState := by
  have hwi := hschedule.getElem! i hi
  unfold roundEWideUInt64 roundEWide WorkingState.toRoundState
  rw [uint64Sum6_toNat]
  rw [UInt32.toNat_eq_of_toBitVec_eq
    (bigSigma1_toBitVec working.e)]
  rw [UInt32.toNat_eq_of_toBitVec_eq
    (choose_toBitVec working.e working.f working.g)]
  rw [UInt32.toNat_eq_of_toBitVec_eq (roundConstants_toBitVec i hi)]
  rw [UInt32.toNat_eq_of_toBitVec_eq hwi]
  rfl

theorem roundAWideUInt64_toNat
    (hschedule : ScheduleArrayRel schedule 64 values)
    (i : Nat) (hi : i < 64) (working : WorkingState) :
    (roundAWideUInt64 schedule i working).toNat =
      roundAWide i values working.toRoundState := by
  have hwi := hschedule.getElem! i hi
  unfold roundAWideUInt64 roundAWide WorkingState.toRoundState
  rw [uint64Sum7_toNat]
  rw [UInt32.toNat_eq_of_toBitVec_eq
    (bigSigma1_toBitVec working.e)]
  rw [UInt32.toNat_eq_of_toBitVec_eq
    (bigSigma0_toBitVec working.a)]
  rw [UInt32.toNat_eq_of_toBitVec_eq
    (choose_toBitVec working.e working.f working.g)]
  rw [UInt32.toNat_eq_of_toBitVec_eq
    (majority_toBitVec working.a working.b working.c)]
  rw [UInt32.toNat_eq_of_toBitVec_eq (roundConstants_toBitVec i hi)]
  rw [UInt32.toNat_eq_of_toBitVec_eq hwi]
  rfl

theorem WorkingState.next_toRoundState (working : WorkingState)
    (newA newE : UInt64) :
    (working.next newA.toUInt32 newE.toUInt32).toRoundState =
      ⟨BitVec.ofNat 32 newA.toNat, working.a.toBitVec,
        working.b.toBitVec, working.c.toBitVec,
        BitVec.ofNat 32 newE.toNat, working.e.toBitVec,
        working.f.toBitVec, working.g.toBitVec⟩ := by
  unfold WorkingState.next WorkingState.toRoundState
  rw [UInt64.toUInt32_toBitVec, UInt64.toUInt32_toBitVec]

theorem WorkingState.next_eq_roundStep
    (hschedule : ScheduleArrayRel schedule 64 values)
    (i : Nat) (hi : i < 64) (working : WorkingState) :
    let eWide := roundEWideUInt64 schedule i working
    let aWide := roundAWideUInt64 schedule i working
    (working.next aWide.toUInt32 eWide.toUInt32).toRoundState =
      roundStepBV i values working.toRoundState := by
  dsimp only
  rw [WorkingState.next_toRoundState]
  rw [roundEWideUInt64_toNat hschedule i hi]
  rw [roundAWideUInt64_toNat hschedule i hi]
  exact (roundStepBV_eq_wide i values working.toRoundState).symm

theorem runRoundsLoop_refines (start len : Nat)
    (hbound : start + len ≤ 64)
    (hschedule : ScheduleArrayRel schedule 64 values)
    (hbuilder : BuilderRefines builder state.bools.toList) :
    let result := runRoundsLoop schedule start len working builder
    let trace := roundsTrace (List.range' start len) state values
      working.toRoundState
    result.1.toRoundState = trace.round ∧
      BuilderRefines result.2 trace.state.bools.toList := by
  induction len generalizing start working builder state with
  | zero => exact ⟨rfl, hbuilder⟩
  | succ len ih =>
      rw [List.range'_succ]
      simp only [roundsTrace, List.foldl_cons, roundsTraceStep]
      let eWide := roundEWideUInt64 schedule start working
      let aWide := roundAWideUInt64 schedule start working
      have hstart : start < 64 := by omega
      have heNat : eWide.toNat =
          roundEWide start values working.toRoundState :=
        roundEWideUInt64_toNat hschedule start hstart working
      have haNat : aWide.toNat =
          roundAWide start values working.toRoundState :=
        roundAWideUInt64_toNat hschedule start hstart working
      have heLt : eWide.toNat < 2 ^ 35 := by
        rw [heNat]
        exact roundEWide_lt start values working.toRoundState
      have haLt : aWide.toNat < 2 ^ 35 := by
        rw [haNat]
        exact roundAWide_lt start values working.toRoundState
      let stateE := appendNatBits state 35
        (roundEWide start values working.toRoundState)
      let stateA := appendNatBits stateE 35
        (roundAWide start values working.toRoundState)
      have hbuilderE : BuilderRefines (appendBitsLE builder eWide 35)
          stateE.bools.toList := by
        have happend := appendBitsLE_refines hbuilder eWide 35 (by omega) heLt
        rw [appendNatBits_bools_toList]
        rw [uint64PrefixBits_eq_natBits, heNat] at happend
        exact happend
      have hbuilderA : BuilderRefines
          (appendBitsLE (appendBitsLE builder eWide 35) aWide 35)
          stateA.bools.toList := by
        have happend := appendBitsLE_refines hbuilderE aWide 35 (by omega) haLt
        rw [appendNatBits_bools_toList]
        rw [uint64PrefixBits_eq_natBits, haNat] at happend
        exact happend
      let working' := working.next aWide.toUInt32 eWide.toUInt32
      have hworking' : working'.toRoundState =
          roundStepBV start values working.toRoundState :=
        WorkingState.next_eq_roundStep hschedule start hstart working
      unfold runRoundsLoop
      simpa only [roundsTrace, roundsTraceStep, eWide, aWide, working',
        stateE, stateA, hworking',
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (start + 1) (working := working') (state := stateA)
          (by omega) hbuilderA

theorem runRounds_refines
    (hschedule : ScheduleArrayRel schedule 64 values)
    (hbuilder : BuilderRefines builder state.bools.toList) :
    let result := runRounds schedule working builder
    let trace := roundsTrace [0:64].toList state values working.toRoundState
    result.1.toRoundState = trace.round ∧
      BuilderRefines result.2 trace.state.bools.toList := by
  unfold runRounds
  have hrange : [0:64].toList = List.range' 0 64 := by native_decide
  rw [hrange]
  exact runRoundsLoop_refines 0 64 (by omega) hschedule hbuilder

/-! ## Final-state additions -/

def fastFinishWide (state : HashState) (working : WorkingState)
    (i : Fin 8) : UInt64 :=
  finishWideUInt64 state working i.val

theorem fastFinishWide_toNat (state : HashState) (working : WorkingState)
    (i : Fin 8) :
    (fastFinishWide state working i).toNat =
      finishWide i state.toVector working.toRoundState := by
  fin_cases i <;> exact uint64Sum2_toNat _ _

theorem finishBuilder_refines (state : HashState) (working : WorkingState)
    (count : Nat) (hcount : count ≤ 8)
    (hbuilder : BuilderRefines builder witState.bools.toList) :
    BuilderRefines (finishBuilder state working count builder)
      (finishState count hcount witState state.toVector
        working.toRoundState).bools.toList := by
  induction count with
  | zero => exact hbuilder
  | succ count ih =>
      unfold finishBuilder finishState
      let priorState := finishState count (by omega) witState state.toVector
        working.toRoundState
      have hprior : BuilderRefines
          (finishBuilder state working count builder)
          priorState.bools.toList := ih (by omega)
      let wide := fastFinishWide state working ⟨count, by omega⟩
      have hwideNat : wide.toNat = finishWide ⟨count, by omega⟩
          state.toVector working.toRoundState :=
        fastFinishWide_toNat state working ⟨count, by omega⟩
      have hwideLt : wide.toNat < 2 ^ 33 := by
        rw [hwideNat]
        exact finishWide_lt ⟨count, by omega⟩ state.toVector
          working.toRoundState
      have happend := appendBitsLE_refines hprior wide 33 (by omega) hwideLt
      rw [appendNatBits_bools_toList]
      rw [uint64PrefixBits_eq_natBits, hwideNat] at happend
      exact happend

theorem finishCompression_builder (state : HashState) (working : WorkingState)
    (builder : WitnessBuilder) :
    (finishCompression state working builder).2 =
      finishBuilder state working 8 builder := by
  simp only [finishCompression]

theorem finishCompression_hash (state : HashState) (working : WorkingState)
    (builder : WitnessBuilder) :
    (finishCompression state working builder).1.toVector =
      finishBV state.toVector working.toRoundState := by
  apply Vector.ext
  intro i hi
  rw [show (finishBV state.toVector working.toRoundState)[i]'hi =
      state.toVector[i]'hi +
        (roundVector working.toRoundState)[i]'hi by
    exact finishBV_get state.toVector working.toRoundState ⟨i, hi⟩]
  interval_cases i <;>
    simp [finishCompression, HashState.toVector, WorkingState.toRoundState,
      roundVector, UInt64.toUInt32_toBitVec, uint64Sum2_toNat]

theorem finishCompression_refines (state : HashState) (working : WorkingState)
    (hbuilder : BuilderRefines builder witState.bools.toList) :
    let result := finishCompression state working builder
    result.1.toVector = finishBV state.toVector working.toRoundState ∧
      BuilderRefines result.2
        (finishState 8 (by omega) witState state.toVector
          working.toRoundState).bools.toList := by
  constructor
  · exact finishCompression_hash state working builder
  · rw [finishCompression_builder]
    exact finishBuilder_refines state working 8 (by omega) hbuilder

/-! ## One complete compression -/

theorem compress_eq_phases (blocks : Array UInt32) (block : Nat)
    (hash : HashState) (builder : WitnessBuilder) :
    compress blocks block hash builder =
      let initial := initialScheduleWords blocks block
      let extended := extendScheduleWords initial builder
      let working0 := WorkingState.ofHashState hash
      let rounded := runRounds extended.1 working0 extended.2
      finishCompression hash rounded.1 rounded.2 := by
  unfold compress
  rfl

theorem compress_refines (blocks : Array UInt32) (block : Nat)
    (hash : HashState) (builder : WitnessBuilder) (witState : Witgen.State)
    (mv : Vector (BitVec 32) 16) (sv : Vector (BitVec 32) 8)
    (hblock : BlockArrayRel blocks block mv)
    (hhash : hash.toVector = sv)
    (hbuilder : BuilderRefines builder witState.bools.toList) :
    let result := compress blocks block hash builder
    result.1.toVector = model mv sv ∧
      BuilderRefines result.2
        (permutationFinalState witState mv sv).bools.toList := by
  let initial := initialScheduleWords blocks block
  have hinitial : ScheduleArrayRel initial 16 (initialSchedule mv) :=
    initialScheduleWords_rel blocks block hblock
  generalize hextended : extendScheduleWords initial builder = extended
  rcases extended with ⟨schedule, builder1⟩
  let schedTrace := permutationScheduleTrace witState mv
  have hextendedRefines := extendScheduleWords_refines hinitial hbuilder
  rw [hextended] at hextendedRefines
  obtain ⟨hschedule, hbuilderSchedule⟩ := hextendedRefines
  let working0 := WorkingState.ofHashState hash
  have hworking0 : working0.toRoundState = initialRound sv := by
    rw [WorkingState.ofHashState_toRoundState, hhash]
  generalize hroundedEq : runRounds schedule working0 builder1 = rounded
  rcases rounded with ⟨working, builder2⟩
  let roundsTrace := permutationRoundsTrace witState mv sv
  have hroundedRefines := runRounds_refines (working := working0)
    hschedule hbuilderSchedule
  rw [hroundedEq] at hroundedRefines
  obtain ⟨hrounded, hbuilderRounds⟩ := hroundedRefines
  have hrounded' : working.toRoundState = roundsTrace.round := by
    rw [show working0.toRoundState = initialRound sv from hworking0] at hrounded
    exact hrounded
  have hbuilderRounds' : BuilderRefines builder2
      roundsTrace.state.bools.toList := by
    rw [show working0.toRoundState = initialRound sv from hworking0] at hbuilderRounds
    exact hbuilderRounds
  let finished := finishCompression hash working builder2
  obtain ⟨hfinishedHash, hfinishedBuilder⟩ :=
    finishCompression_refines hash working hbuilderRounds'
  have hmodel : finished.1.toVector = model mv sv := by
    rw [hfinishedHash, hhash, hrounded']
    rw [permutationRoundsTrace_round]
    rfl
  have hfinalBuilder : BuilderRefines finished.2
      (permutationFinalState witState mv sv).bools.toList := by
    rw [hhash, hrounded'] at hfinishedBuilder
    exact hfinishedBuilder
  have hcompress : compress blocks block hash builder = finished := by
    rw [compress_eq_phases]
    change finishCompression hash
      (runRounds (extendScheduleWords initial builder).1 working0
        (extendScheduleWords initial builder).2).1
      (runRounds (extendScheduleWords initial builder).1 working0
        (extendScheduleWords initial builder).2).2 = finished
    rw [hextended, hroundedEq]
  rw [hcompress]
  exact ⟨hmodel, hfinalBuilder⟩

end Sha256FastWitgen

end
end Freigen.F2Z.Examples
