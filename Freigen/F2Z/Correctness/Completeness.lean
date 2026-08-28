import Freigen.F2Z.Semantics
import Freigen.F2Z.Nondet
import Freigen.F2Z.Correctness.WF
import Std.Tactic.Do

namespace Freigen.F2Z.Complete

open Std.Do
open scoped Std.Do

local instance : Context := lcContext

/-- The proof-facing semantics has no allocator or mutable state. -/
abbrev InterpM (_ : Eff.Scope) := Option

instance : (scope : Eff.Scope) → Monad (InterpM scope)
  | .constraint => inferInstance
  | .hint => inferInstance

instance : (scope : Eff.Scope) → LawfulMonad (InterpM scope)
  | .constraint => inferInstance
  | .hint => inferInstance

def interpHandler (valuation : WF.Valuation) :
    Freigen.Eff.Handler (Eff lcContext) InterpM :=
  @fun
    | .constraint, .assertR1C a b c, _ =>
        if a.eval valuation.int * b.eval valuation.int = c.eval valuation.int then
          some ()
        else
          none
    | .constraint, .f2z a, _ =>
        some (LC.ofConst (a.eval valuation.bool).toInt)
    | .constraint, .hint _ args _, block => do
        let values ← block PUnit.unit (WF.evalArgs lcContext valuation args)
        pure (values.map LC.ofConst)
    | .hint, .fail _ _, _ => none

/-- Stateless denotation of a circuit under a total valuation. -/
def interp (valuation : WF.Valuation) (circ : Circuit α) : Option α :=
  Free.interp (interpHandler valuation) circ

@[simp, spec]
theorem interp_pure (valuation : WF.Valuation) (value : α) :
    interp valuation (pure value : Circuit α) = pure value := by
  rfl

@[simp, spec]
theorem interp_bind (valuation : WF.Valuation)
    (circ : Circuit α) (k : α → Circuit β) :
    interp valuation (circ >>= k) =
      (interp valuation circ >>= fun value => interp valuation (k value)) := by
  simp [interp, Free.interp_bind]

/-- MVCGen-facing form of `interp_bind`. -/
@[spec]
theorem interp_bind_spec {valuation : WF.Valuation}
    {circ : Circuit α} {k : α → Circuit β}
    {P : SPred []} {Q : PostCond β (.except PUnit .pure)}
    (h : Triple
      (do
        let value ← interp valuation circ
        interp valuation (k value))
      P Q) :
    Triple (interp valuation (circ >>= k)) P Q := by
  rwa [interp_bind]

/-- MVCGen-facing form of `interp_pure`. -/
@[spec]
theorem interp_pure_spec {valuation : WF.Valuation} (value : α)
    (Q : PostCond α (.except PUnit .pure)) :
    Triple (interp valuation (pure value : Circuit α)) (Q.1 value) Q := by
  rw [interp_pure]
  exact Std.Do.Spec.pure

/-- Interpretation commutes with `forIn'` over lists. -/
theorem interp_forIn'_list (valuation : WF.Valuation)
    (xs : List α) (init : β)
    (f : (a : α) → a ∈ xs → β → Circuit (ForInStep β)) :
    interp valuation (forIn' xs init f) =
      forIn' xs init fun a h b => interp valuation (f a h b) := by
  induction xs generalizing init with
  | nil => simp [interp_pure]
  | cons x xs ih =>
      simp only [List.forIn'_cons, interp_bind]
      congr 1
      funext step
      cases step with
      | done b => simp [interp_pure]
      | yield b =>
          simpa using ih b
            (fun a h b => f a (List.mem_cons_of_mem x h) b)

/-- Interpretation commutes with `forIn'` over legacy ranges. -/
theorem interp_forIn'_range (valuation : WF.Valuation)
    (xs : Std.Legacy.Range) (init : β)
    (f : (a : Nat) → a ∈ xs → β → Circuit (ForInStep β)) :
    interp valuation (forIn' xs init f) =
      forIn' xs init fun a h b => interp valuation (f a h b) := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range',
    Std.Legacy.Range.forIn'_eq_forIn'_range']
  simpa using interp_forIn'_list valuation xs.toList init
    (fun a h b => f a (Std.Legacy.Range.mem_of_mem_range' h) b)

/-- Expose an interpreted range loop as a native `Option` range loop so that
MVCGen can apply its standard loop rule and request an invariant. -/
@[spec]
theorem interp_forIn'_range_spec
    {valuation : WF.Valuation} {xs : Std.Legacy.Range} {init : β}
    {f : (a : Nat) → a ∈ xs → β → Circuit (ForInStep β)}
    {P : SPred []} {Q : PostCond β (.except PUnit .pure)}
    (h : Triple
      (forIn' xs init fun a h b => interp valuation (f a h b)) P Q) :
    Triple (interp valuation (forIn' xs init f)) P Q := by
  rwa [interp_forIn'_range]

-- @[simp]
theorem interp_assertR1C (valuation : WF.Valuation) (a b c : LC ℤ) :
    interp valuation (F2Z.assertR1C a b c) =
      if a.eval valuation.int * b.eval valuation.int = c.eval valuation.int then
        pure ()
      else
        none := by
  unfold interp F2Z.assertR1C
  rw [Free.interp_op]
  rfl

@[simp]
theorem interp_f2z (valuation : WF.Valuation) (a : LC Bool) :
    interp valuation (F2Z.f2z a) =
      pure (LC.ofConst (a.eval valuation.bool).toInt) := by
  unfold interp F2Z.f2z
  rw [Free.interp_op]
  rfl

theorem interpHint_eq (valuation : WF.Valuation) (body : Hint α) :
    WF.interpHint body =
      Free.interp (interpHandler valuation) body := by
  let motive := fun (scope : Eff.Scope) (alpha : Type)
      (body : Free (Eff lcContext) scope alpha) =>
    match scope with
    | .constraint => True
    | .hint => WF.interpHint body =
        Free.interp (interpHandler valuation) body
  apply Free.recOn (motive := motive) body
  · intro scope alpha value
    cases scope <;> trivial
  · intro scope alpha e blocks k _ _
    cases scope with
    | constraint => trivial
    | hint =>
      cases e with
      | fail out msg =>
        dsimp [motive]
        simp only [WF.interpHint, Free.interp_bind]
        rw [Free.interp_op, Free.interp_op]
        change none = none
        rfl

@[simp]
theorem interp_hint (valuation : WF.Valuation)
    {argTps : List Eff.WitnessSide}
    (args : HList (Eff.WitnessSide.denoteW lcContext) argTps)
    (body : HList Eff.WitnessSide.denoteF argTps → Hint (Vector Bool n)) :
    interp valuation (F2Z.hint args body) =
      (do
        let values ← Free.interp (interpHandler valuation)
          (body (WF.evalArgs lcContext valuation args))
        pure (values.map LC.ofConst)) := by
  unfold interp F2Z.hint
  rw [Free.interp_op]
  rfl

@[spec]
theorem option_some_spec (value : α)
    (Q : PostCond α (.except PUnit .pure)) :
    Triple (some value) (Q.1 value) Q := by
  apply Triple.iff.mpr
  exact SPred.entails.rfl

/-- Completeness must establish an assertion before execution can continue. -/
@[spec]
theorem assertR1C (valuation : WF.Valuation) (a b c : LC ℤ)
    (Q : PostCond Unit (.except PUnit .pure)) :
    Triple (interp valuation (F2Z.assertR1C a b c))
      spred(⌜valuation.int a * valuation.int b =
        valuation.int c⌝ ∧ Q.1 ()) Q := by
  rw [interp_assertR1C, Triple.iff]
  split
  · intro hpre
    exact hpre.2
  · rename_i h
    have h' : ¬valuation.int a * valuation.int b = valuation.int c := by
      simpa only [← LC.Valuation.apply_eq_eval] using h
    simp [h']

/-- A complete hint execution must return actual values, and the postcondition
must hold for their constant-LC embedding. -/
@[spec]
theorem hint (valuation : WF.Valuation)
    {argTps : List Eff.WitnessSide}
    (args : HList (Eff.WitnessSide.denoteW lcContext) argTps)
    (body : HList Eff.WitnessSide.denoteF argTps → Hint (Vector Bool n))
    (Q : PostCond (Vector (LC Bool) n) (.except PUnit .pure)) :
    Triple (interp valuation (F2Z.hint args body))
      spred(∃ values,
        ⌜WF.interpHint (body (WF.evalArgs lcContext valuation args)) = some values⌝ ∧
        Q.1 (values.map LC.ofConst)) Q := by
  rw [interp_hint, ← interpHint_eq, Triple.iff]
  generalize WF.interpHint (body (WF.evalArgs lcContext valuation args)) = result
  cases result with
  | none => simp
  | some values =>
      simp
      exact Triple.iff.mp (option_some_spec (values.map LC.ofConst) Q)

@[spec]
theorem interp_f2z_spec {a : LC Bool} {valuation : WF.Valuation} :
    ⦃ ⌜True⌝ ⦄ interp valuation (F2Z.f2z a)
    ⦃⇓ result =>
      ⌜valuation.int result = (valuation.bool a).toInt⌝⦄ := by
  rw [interp_f2z]
  mvcgen
  rw [LC.Valuation.ofConst_apply]
  exact congrArg Bool.toInt
    (LC.Valuation.apply_eq_eval valuation.bool a).symm

@[simp, spec]
theorem interp_map (valuation : WF.Valuation)
    (f : α → β) (circ : Circuit α) :
    interp valuation (f <$> circ) = f <$> interp valuation circ := by
  rw [← bind_pure_comp, interp_bind]
  generalize interp valuation circ = result
  cases result <;> rfl

private theorem interp_list_mapM (valuation : WF.Valuation)
    (xs : List α) (f : α → Circuit β) :
    interp valuation (xs.mapM f) =
      xs.mapM (fun x => interp valuation (f x)) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.mapM_cons, interp_bind, ih]
      generalize interp valuation (f x) = headResult
      generalize List.mapM (fun x => interp valuation (f x)) xs = tailResult
      cases headResult <;> cases tailResult <;> rfl

private theorem interp_array_mapM (valuation : WF.Valuation)
    (xs : Array α) (f : α → Circuit β) :
    interp valuation (xs.mapM f) =
      xs.mapM (fun x => interp valuation (f x)) := by
  simp only [Array.mapM_eq_mapM_toList, interp_map,
    interp_list_mapM]

@[simp, spec]
theorem interp_mapM (valuation : WF.Valuation)
    (xs : Vector α n) (f : α → Circuit β) :
    interp valuation (xs.mapM f) =
      xs.mapM (fun x => interp valuation (f x)) := by
  apply Vector.map_toArray_inj.mp
  rw [← interp_map, Vector.toArray_mapM,
    interp_array_mapM, Vector.toArray_mapM]

/-- Interpretation commutes with constructing a vector effectfully by index. -/
@[simp, spec]
theorem interp_ofFnM (valuation : WF.Valuation) (f : Fin n → Circuit α) :
    interp valuation (Vector.ofFnM f) =
      Vector.ofFnM (fun i => interp valuation (f i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Vector.ofFnM_succ, interp_bind, interp_pure, ih]

/- The former completeness argument interpreted the same `LC` circuit twice.
It is retained temporarily in the history, but superseded below by the
cross-context argument.  -/
/-
private def BoolsRealize (ws : Semantics.Witgen.State)
    (valuation : Nat → Bool) : Prop :=
  ∀ i, i < ws.bools.size → valuation i = ws.boolWitness i

private structure RightRealizes (cs : Semantics.CSBuilder)
    (ws : Semantics.Witgen.State) (valuation : WF.Valuation) : Prop where
  bools : BoolsRealize ws valuation.bool
  ints : ∀ (i : Nat) (hi : i < cs.result.m.size),
    valuation.int i =
      (valuation.bool (cs.result.m[i]'hi)).toInt

private structure Compatible (cs : Semantics.CSBuilder)
    (ws : Semantics.Witgen.State) (leftVal rightVal : WF.Valuation) : Prop where
  left_bools : BoolsRealize ws leftVal.bool
  right : RightRealizes cs ws rightVal

private def leftValuation (ws : Semantics.Witgen.State) : WF.Valuation where
  bool := ws.boolWitness
  int := Semantics.Witgen.zeroWitness

private def rightValuation (cs : Semantics.CSBuilder)
    (ws : Semantics.Witgen.State) : WF.Valuation where
  bool := ws.boolWitness
  int := cs.result.intWitness ws.boolWitness

private theorem BoolsRealize.self (ws : Semantics.Witgen.State) :
    BoolsRealize ws ws.boolWitness := by
  intro i hi
  rfl

private theorem RightRealizes.canonical (cs : Semantics.CSBuilder)
    (ws : Semantics.Witgen.State) :
    RightRealizes cs ws (rightValuation cs ws) := by
  constructor
  · exact BoolsRealize.self ws
  · intro i hi
    simp only [rightValuation, Semantics.CS.intWitness]
    rw [getElem!_pos _ _ (by simpa using hi), Array.getElem_map]
    rfl

private def ConstraintsValid (cs : Semantics.CSBuilder)
    (ws : Semantics.Witgen.State) : Prop :=
  ∀ valuation, RightRealizes cs ws valuation →
    ∀ r ∈ cs.result.r1cs, r.satisfies valuation.int

private theorem boolWitness_append (ws : Semantics.Witgen.State)
    (values : Array Bool) {i : Nat} (hi : i < ws.bools.size) :
    ws.boolWitness i = ({ ws with bools := ws.bools ++ values }).boolWitness i := by
  unfold Semantics.Witgen.State.boolWitness
  rw [getElem!_pos ws.bools i hi,
    getElem!_pos (ws.bools ++ values) i (by simp; omega)]
  exact (Array.getElem_append_left hi).symm

private theorem BoolsRealize.of_append {ws : Semantics.Witgen.State}
    {values : Array Bool} {valuation : Nat → Bool}
    (h : BoolsRealize { ws with bools := ws.bools ++ values } valuation) :
    BoolsRealize ws valuation := by
  intro i hi
  rw [h i (by simp; omega)]
  exact boolWitness_append ws values hi |>.symm

private theorem evalArgs_canonical (ws : Semantics.Witgen.State) :
    {argTps : List Eff.WitnessSide} →
    (args : HList Eff.WitnessSide.denoteW argTps) →
    WF.evalArgs (leftValuation ws) args = Semantics.Witgen.evalArgs ws args
  | [], .nil => rfl
  | .z :: _, .cons x xs => by
      change HList.cons (a := .z) (show ℤ from
          (show LC ℤ from x).eval Semantics.Witgen.zeroWitness)
        (WF.evalArgs (leftValuation ws) xs) =
        HList.cons (a := .z) (show ℤ from
            (show LC ℤ from x).eval Semantics.Witgen.zeroWitness)
          (Semantics.Witgen.evalArgs ws xs)
      rw [evalArgs_canonical ws xs]
  | .f₂ :: _, .cons x xs => by
      change HList.cons (a := .f₂) (show Bool from
          (show LC Bool from x).eval ws.boolWitness)
        (WF.evalArgs (leftValuation ws) xs) =
        HList.cons (a := .f₂) (show Bool from
            (show LC Bool from x).eval ws.boolWitness)
          (Semantics.Witgen.evalArgs ws xs)
      rw [evalArgs_canonical ws xs]

private def csHintOut (cs : Semantics.CSBuilder) (n : Nat) :
    Vector (LC Bool) n :=
  Vector.ofFn fun i => ({cs.nextWit + i.val} : LC Bool)

private def pushR1C (cs : Semantics.CSBuilder) (a b c : LC ℤ) :
    Semantics.CSBuilder :=
  { cs with result := { cs.result with
      r1cs := cs.result.r1cs.push { a, b, c } } }

private def pushF2Z (cs : Semantics.CSBuilder) (a : LC Bool) :
    Semantics.CSBuilder :=
  { cs with result := { cs.result with m := cs.result.m.push a } }

private def pushHint (cs : Semantics.CSBuilder) (n : Nat) :
    Semantics.CSBuilder :=
  { cs with nextWit := cs.nextWit + n }

private def appendHint (ws : Semantics.Witgen.State) (values : Vector Bool n) :
    Semantics.Witgen.State :=
  { ws with bools := ws.bools ++ values.toArray }

private theorem csHintOut_realizes
    (cs : Semantics.CSBuilder) (ws : Semantics.Witgen.State)
    (values : Vector Bool n) (valuation : Nat → Bool)
    (hnext : cs.nextWit = ws.bools.size)
    (h : BoolsRealize (appendHint ws values) valuation) :
    WF.RealizesBools valuation (csHintOut cs n) values := by
  intro i hi
  simp only [csHintOut, Vector.getElem_ofFn, LC.eval_singleton]
  rw [hnext]
  rw [h (ws.bools.size + i) (by simp [appendHint]; omega)]
  unfold Semantics.Witgen.State.boolWitness appendHint
  rw [getElem!_pos _ _ (by simp; omega)]
  rw [Array.getElem_append_right (by omega)]
  simp

private theorem RightRealizes.of_pushR1C
    {cs : Semantics.CSBuilder} {ws : Semantics.Witgen.State}
    {valuation : WF.Valuation} {a b c : LC ℤ}
    (h : RightRealizes (pushR1C cs a b c) ws valuation) :
    RightRealizes cs ws valuation := by
  exact ⟨h.bools, by intro i hi; simpa [pushR1C] using h.ints i hi⟩

private theorem RightRealizes.of_pushF2Z
    {cs : Semantics.CSBuilder} {ws : Semantics.Witgen.State}
    {valuation : WF.Valuation} {a : LC Bool}
    (h : RightRealizes (pushF2Z cs a) ws valuation) :
    RightRealizes cs ws valuation := by
  refine ⟨h.bools, ?_⟩
  intro i hi
  simpa [pushF2Z, Array.getElem_push_lt hi] using
    h.ints i (by simp [pushF2Z]; omega)

private theorem RightRealizes.of_pushHint
    {cs : Semantics.CSBuilder} {ws : Semantics.Witgen.State}
    {valuation : WF.Valuation} {values : Vector Bool n}
    (h : RightRealizes (pushHint cs n) (appendHint ws values) valuation) :
    RightRealizes cs ws valuation := by
  refine ⟨BoolsRealize.of_append h.bools, ?_⟩
  intro i hi
  simpa [pushHint, appendHint] using h.ints i hi

private theorem Compatible.leftCanonical
    {cs : Semantics.CSBuilder} {ws : Semantics.Witgen.State}
    {rightVal : WF.Valuation} (h : RightRealizes cs ws rightVal) :
    Compatible cs ws (leftValuation ws) rightVal :=
  ⟨BoolsRealize.self ws, h⟩

private theorem constBools_realizes (valuation : Nat → Bool)
    (values : Vector Bool n) :
    WF.RealizesBools valuation (values.map LC.ofConst) values := by
  intro i hi
  simp

private theorem hintInterp_witgen (body : Hint α) :
    WF.interpHint body = Semantics.Witgen.runAt body := by
  let motive := fun (scope : Eff.Scope) (alpha : Type)
      (body : Free Eff scope alpha) =>
    match scope with
    | .constraint => True
    | .hint => WF.interpHint body = Semantics.Witgen.runAt body
  apply Free.recOn (motive := motive) body
  · intro scope alpha value
    cases scope <;> trivial
  · intro scope alpha e blocks k _ _
    cases scope with
    | constraint => trivial
    | hint =>
      cases e with
      | fail out msg =>
        dsimp [motive]
        simp only [WF.interpHint, Semantics.Witgen.runAt,
          Free.interp_bind]
        rw [Free.interp_op, Free.interp_op]
        change none = none
        rfl

private theorem hintRel_witgen (h : WF.HintRel R left right) :
    Option.Rel R (Semantics.Witgen.runAt left)
      (Semantics.Witgen.runAt right) := by
  unfold WF.HintRel at h
  rwa [hintInterp_witgen, hintInterp_witgen] at h

private theorem hintReturns_witgen (h : WF.HintReturns body value) :
    Semantics.Witgen.runAt body = some value := by
  unfold WF.HintReturns at h
  rwa [hintInterp_witgen] at h

private theorem hintReturns_of_witgen (body : Hint α) {value : α}
    (h : Semantics.Witgen.runAt body = some value) :
    WF.HintReturns body value := by
  unfold WF.HintReturns
  rwa [hintInterp_witgen]

private theorem hintReturns_interp (valuation : WF.Valuation)
    (h : WF.HintReturns body value) :
    Free.interp (interpHandler valuation) body = some value := by
  unfold WF.HintReturns at h
  rwa [interpHint_eq valuation] at h

private theorem optionRel_eq_some
    (h : Option.Rel Eq (some value) result) : result = some value := by
  cases h with
  | some h => subst h; rfl

private theorem optionRel_eq_some_right
    (h : Option.Rel Eq result (some value)) : result = some value := by
  cases h with
  | some h => subst h; rfl

private theorem runAt_interp_adequate
    {P : WF.Assumption} {left right : Circuit α}
    {ws ws' : Semantics.Witgen.State} {value : α}
    (hrel : WF.Rel (fun _ _ _ _ => True) P left right)
    (rightVal : WF.Valuation)
    (hP : ∀ leftVal, BoolsRealize ws leftVal.bool →
      P leftVal rightVal)
    (hrun : StateT.run (Semantics.Witgen.runAt left) ws =
      some (value, ws')) :
    ∃ result, interp rightVal right = some result := by
  induction hrel generalizing ws ws' value with
  | pure hpost =>
      simp [Semantics.Witgen.runAt] at hrun
      exact ⟨_, rfl⟩
  | @assertR1C P aL bL cL aR bR cR kL kR ha hb hc hcont ih =>
      unfold Semantics.Witgen.runAt at hrun
      rw [Free.interp_bind] at hrun
      unfold F2Z.assertR1C at hrun
      rw [Free.interp_op] at hrun
      by_cases hsat :
          aL.eval Semantics.Witgen.zeroWitness *
            bL.eval Semantics.Witgen.zeroWitness =
            cL.eval Semantics.Witgen.zeroWitness
      · simp [Semantics.Witgen.handler, hsat] at hrun
        have hp := hP (leftValuation ws) (BoolsRealize.self ws)
        have ha' := ha (leftValuation ws) rightVal hp
        have hb' := hb (leftValuation ws) rightVal hp
        have hc' := hc (leftValuation ws) rightVal hp
        unfold WF.LCEq at ha' hb' hc'
        have hsatRight :
            aR.eval rightVal.int * bR.eval rightVal.int =
              cR.eval rightVal.int := by
          rw [← ha', ← hb', ← hc']
          exact hsat
        obtain ⟨result, hresult⟩ := ih hP hrun
        refine ⟨result, ?_⟩
        unfold interp
        rw [Free.interp_bind]
        unfold F2Z.assertR1C
        rw [Free.interp_op]
        simp [interpHandler, hsatRight]
        exact hresult
      · simp [Semantics.Witgen.handler, hsat] at hrun
  | @f2z P aL aR kL kR ha hcont ih =>
      let outL : LC ℤ := LC.ofConst (aL.eval ws.boolWitness).toInt
      let outR : LC ℤ := LC.ofConst (aR.eval rightVal.bool).toInt
      have hP' : ∀ leftVal, BoolsRealize ws leftVal.bool →
          (P leftVal rightVal ∧
            outL.eval leftVal.int = (aL.eval leftVal.bool).toInt ∧
            outR.eval rightVal.int = (aR.eval rightVal.bool).toInt) := by
        intro leftVal hleft
        have hp := hP leftVal hleft
        have hpCanonical := hP (leftValuation ws) (BoolsRealize.self ws)
        have harg := ha leftVal rightVal hp
        have hargCanonical := ha (leftValuation ws) rightVal hpCanonical
        unfold WF.LCEq at harg hargCanonical
        refine ⟨hp, ?_, ?_⟩
        · simp only [outL, LC.eval_ofConst]
          exact congrArg Bool.toInt (hargCanonical.trans harg.symm)
        · exact LC.Valuation.ofConst_apply rightVal.int _
      unfold Semantics.Witgen.runAt at hrun
      rw [Free.interp_bind] at hrun
      unfold F2Z.f2z at hrun
      rw [Free.interp_op] at hrun
      simp [Semantics.Witgen.handler] at hrun
      obtain ⟨result, hresult⟩ := ih outL outR hP' hrun
      refine ⟨result, ?_⟩
      unfold interp
      rw [Free.interp_bind]
      unfold F2Z.f2z
      rw [Free.interp_op]
      simp [interpHandler]
      exact hresult
  | @hint P n argTps argsL argsR bodyL bodyR kL kR
      hargs hbody hcont ih =>
      unfold Semantics.Witgen.runAt at hrun
      rw [Free.interp_bind] at hrun
      unfold F2Z.hint at hrun
      rw [Free.interp_op] at hrun
      simp only [Semantics.Witgen.handler] at hrun
      generalize hbodyRun :
          Free.interp (fun {scope} => Semantics.Witgen.handler)
            (bodyL (Semantics.Witgen.evalArgs ws argsL)) = bodyResult at hrun
      cases bodyResult with
      | none => simp [hbodyRun] at hrun
      | some valuesL =>
        have hpCanonical := hP (leftValuation ws) (BoolsRealize.self ws)
        have hbodyCanonical := hbody (leftValuation ws) rightVal hpCanonical
        rw [evalArgs_canonical] at hbodyCanonical
        have hbodyRuns := hintRel_witgen hbodyCanonical
        unfold Semantics.Witgen.runAt at hbodyRuns
        rw [hbodyRun] at hbodyRuns
        have hrightRun := optionRel_eq_some hbodyRuns
        have hreturnsR := hintReturns_of_witgen _ hrightRun
        have hrightInterp := hintReturns_interp rightVal hreturnsR
        let outL : Vector (LC Bool) n := valuesL.map LC.ofConst
        let outR : Vector (LC Bool) n := valuesL.map LC.ofConst
        let wsNext := appendHint ws valuesL
        have hP' : ∀ leftVal, BoolsRealize wsNext leftVal.bool →
            (P leftVal rightVal ∧ ∃ actual,
              WF.HintReturns (bodyL (WF.evalArgs leftVal argsL)) actual ∧
              WF.HintReturns (bodyR (WF.evalArgs rightVal argsR)) actual ∧
              WF.RealizesBools leftVal.bool outL actual ∧
              WF.RealizesBools rightVal.bool outR actual) := by
          intro leftVal hleft
          have hleftOld := BoolsRealize.of_append hleft
          have hp := hP leftVal hleftOld
          have hbodyAny := hbody leftVal rightVal hp
          have hbodyRunsAny := hintRel_witgen hbodyAny
          unfold Semantics.Witgen.runAt at hbodyRunsAny hrightRun
          rw [hrightRun] at hbodyRunsAny
          have hleftRun := optionRel_eq_some_right hbodyRunsAny
          refine ⟨hp, valuesL, ?_, ?_, ?_, ?_⟩
          · exact hintReturns_of_witgen _ hleftRun
          · exact hreturnsR
          · exact constBools_realizes leftVal.bool valuesL
          · exact constBools_realizes rightVal.bool valuesL
        simp [hbodyRun] at hrun
        obtain ⟨result, hresult⟩ := ih outL outR hP' hrun
        refine ⟨result, ?_⟩
        unfold interp
        rw [Free.interp_bind]
        unfold F2Z.hint
        rw [Free.interp_op]
        simp [interpHandler, hrightInterp]
        exact hresult

private theorem interp_runAt_adequate
    {P : WF.Assumption} {left right : Circuit α}
    {ws : Semantics.Witgen.State} {rightVal : WF.Valuation} {result : α}
    (hrel : WF.Rel (fun _ _ _ _ => True) P left right)
    (hP : ∀ leftVal, BoolsRealize ws leftVal.bool →
      P leftVal rightVal)
    (hinterp : interp rightVal right = some result) :
    ∃ value ws', StateT.run (Semantics.Witgen.runAt left) ws =
      some (value, ws') := by
  induction hrel generalizing ws result with
  | pure hpost =>
      simp [interp, Semantics.Witgen.runAt] at hinterp ⊢
  | @assertR1C P aL bL cL aR bR cR kL kR ha hb hc hcont ih =>
      unfold interp at hinterp
      rw [Free.interp_bind] at hinterp
      unfold F2Z.assertR1C at hinterp
      rw [Free.interp_op] at hinterp
      by_cases hsatRight :
          aR.eval rightVal.int * bR.eval rightVal.int =
            cR.eval rightVal.int
      · simp [interpHandler, hsatRight] at hinterp
        have hp := hP (leftValuation ws) (BoolsRealize.self ws)
        have ha' := ha (leftValuation ws) rightVal hp
        have hb' := hb (leftValuation ws) rightVal hp
        have hc' := hc (leftValuation ws) rightVal hp
        unfold WF.LCEq at ha' hb' hc'
        have hsatLeft :
            aL.eval Semantics.Witgen.zeroWitness *
              bL.eval Semantics.Witgen.zeroWitness =
              cL.eval Semantics.Witgen.zeroWitness := by
          change aL.eval (leftValuation ws).int *
              bL.eval (leftValuation ws).int =
            cL.eval (leftValuation ws).int
          rw [ha', hb', hc']
          exact hsatRight
        obtain ⟨value, ws', hrun⟩ := ih hP hinterp
        refine ⟨value, ws', ?_⟩
        unfold Semantics.Witgen.runAt
        rw [Free.interp_bind]
        unfold F2Z.assertR1C
        rw [Free.interp_op]
        simp [Semantics.Witgen.handler, hsatLeft]
        exact hrun
      · simp [interpHandler, hsatRight] at hinterp
  | @f2z P aL aR kL kR ha hcont ih =>
      let outL : LC ℤ := LC.ofConst (aL.eval ws.boolWitness).toInt
      let outR : LC ℤ := LC.ofConst (aR.eval rightVal.bool).toInt
      have hP' : ∀ leftVal, BoolsRealize ws leftVal.bool →
          (P leftVal rightVal ∧
            outL.eval leftVal.int = (aL.eval leftVal.bool).toInt ∧
            outR.eval rightVal.int = (aR.eval rightVal.bool).toInt) := by
        intro leftVal hleft
        have hp := hP leftVal hleft
        have hpCanonical := hP (leftValuation ws) (BoolsRealize.self ws)
        have harg := ha leftVal rightVal hp
        have hargCanonical := ha (leftValuation ws) rightVal hpCanonical
        unfold WF.LCEq at harg hargCanonical
        refine ⟨hp, ?_, ?_⟩
        · simp only [outL, LC.eval_ofConst]
          exact congrArg Bool.toInt (hargCanonical.trans harg.symm)
        · simp [outR]
      unfold interp at hinterp
      rw [Free.interp_bind] at hinterp
      unfold F2Z.f2z at hinterp
      rw [Free.interp_op] at hinterp
      simp [interpHandler] at hinterp
      obtain ⟨value, ws', hrun⟩ := ih outL outR hP' hinterp
      refine ⟨value, ws', ?_⟩
      unfold Semantics.Witgen.runAt
      rw [Free.interp_bind]
      unfold F2Z.f2z
      rw [Free.interp_op]
      simp [Semantics.Witgen.handler]
      exact hrun
  | @hint P n argTps argsL argsR bodyL bodyR kL kR
      hargs hbody hcont ih =>
      unfold interp at hinterp
      rw [Free.interp_bind] at hinterp
      unfold F2Z.hint at hinterp
      rw [Free.interp_op] at hinterp
      simp only [interpHandler] at hinterp
      generalize hbodyRun :
          Free.interp (interpHandler rightVal)
            (bodyR (WF.evalArgs rightVal argsR)) = bodyResult at hinterp
      cases bodyResult with
      | none => simp at hinterp
      | some values =>
        have hpCanonical := hP (leftValuation ws) (BoolsRealize.self ws)
        have hbodyCanonical := hbody (leftValuation ws) rightVal hpCanonical
        rw [evalArgs_canonical] at hbodyCanonical
        have hrightReturns : WF.HintReturns
            (bodyR (WF.evalArgs rightVal argsR)) values := by
          unfold WF.HintReturns
          rw [interpHint_eq rightVal]
          exact hbodyRun
        have hleftReturns : WF.HintReturns
            (bodyL (Semantics.Witgen.evalArgs ws argsL)) values := by
          unfold WF.HintRel at hbodyCanonical
          unfold WF.HintReturns
          rw [hrightReturns] at hbodyCanonical
          exact optionRel_eq_some_right hbodyCanonical
        let outL : Vector (LC Bool) n := values.map LC.ofConst
        let outR : Vector (LC Bool) n := values.map LC.ofConst
        let wsNext := appendHint ws values
        have hP' : ∀ leftVal, BoolsRealize wsNext leftVal.bool →
            (P leftVal rightVal ∧ ∃ actual,
              WF.HintReturns (bodyL (WF.evalArgs leftVal argsL)) actual ∧
              WF.HintReturns (bodyR (WF.evalArgs rightVal argsR)) actual ∧
              WF.RealizesBools leftVal.bool outL actual ∧
              WF.RealizesBools rightVal.bool outR actual) := by
          intro leftVal hleft
          have hleftOld := BoolsRealize.of_append hleft
          have hp := hP leftVal hleftOld
          have hbodyAny := hbody leftVal rightVal hp
          unfold WF.HintRel at hbodyAny
          unfold WF.HintReturns at hrightReturns
          rw [hrightReturns] at hbodyAny
          have hleftAny := optionRel_eq_some_right hbodyAny
          refine ⟨hp, values, ?_, ?_, ?_, ?_⟩
          · exact hleftAny
          · exact hrightReturns
          · exact constBools_realizes leftVal.bool values
          · exact constBools_realizes rightVal.bool values
        simp at hinterp
        obtain ⟨value, ws', hrun⟩ := ih outL outR hP' hinterp
        refine ⟨value, ws', ?_⟩
        unfold Semantics.Witgen.runAt
        rw [Free.interp_bind]
        unfold F2Z.hint
        rw [Free.interp_op]
        have hleftRun := hintReturns_witgen hleftReturns
        unfold Semantics.Witgen.runAt at hleftRun
        simp only [Semantics.Witgen.handler]
        simp [hleftRun]
        simpa [Semantics.Witgen.runAt, wsNext, appendHint, outL] using hrun

/-- The valuation induced by a completed witness-generator run. -/
def witnessValuation (wit : Array Bool) : WF.Valuation where
  bool := fun i => wit[i]!
  int := Semantics.Witgen.zeroWitness

private theorem runAt_adequate {P : WF.Assumption} {left right : Circuit α}
    {cs : Semantics.CSBuilder} {ws ws' : Semantics.Witgen.State} {value : α}
    (hrel : WF.Rel (fun _ _ _ _ => True) P left right)
    (hnext : cs.nextWit = ws.bools.size)
    (hP : ∀ leftVal rightVal,
      Compatible cs ws leftVal rightVal → P leftVal rightVal)
    (hvalid : ConstraintsValid cs ws)
    (hrun : StateT.run (Semantics.Witgen.runAt left) ws = some (value, ws')) :
    let result := StateT.run (Semantics.CSBuilder.runAt right) cs
    result.2.nextWit = ws'.bools.size ∧ ConstraintsValid result.2 ws' := by
  induction hrel generalizing cs ws ws' value with
  | pure hpost =>
      simp [Semantics.Witgen.runAt] at hrun
      rcases hrun with ⟨rfl, rfl⟩
      change cs.nextWit = ws.bools.size ∧ ConstraintsValid cs ws
      exact ⟨hnext, hvalid⟩
  | @assertR1C P aL bL cL aR bR cR kL kR ha hb hc hcont ih =>
      unfold Semantics.Witgen.runAt at hrun
      rw [Free.interp_bind] at hrun
      unfold F2Z.assertR1C at hrun
      rw [Free.interp_op] at hrun
      unfold Semantics.CSBuilder.runAt
      rw [Free.interp_bind]
      unfold F2Z.assertR1C
      rw [Free.interp_op]
      by_cases hsat :
          aL.eval Semantics.Witgen.zeroWitness *
            bL.eval Semantics.Witgen.zeroWitness =
            cL.eval Semantics.Witgen.zeroWitness
      · simp [Semantics.Witgen.handler, Semantics.CSBuilder.handler, hsat] at hrun ⊢
        let cs' := pushR1C cs aR bR cR
        have hP' : ∀ leftVal rightVal,
            Compatible cs' ws leftVal rightVal → P leftVal rightVal := by
          intro leftVal rightVal hcompat
          exact hP leftVal rightVal
            ⟨hcompat.left_bools, hcompat.right.of_pushR1C⟩
        have hvalid' : ConstraintsValid cs' ws := by
          intro valuation hrealizes r hr
          simp only [cs', pushR1C, Array.mem_push] at hr
          rcases hr with hr | rfl
          · exact hvalid valuation hrealizes.of_pushR1C r hr
          · have hp := hP (leftValuation ws) valuation
                (Compatible.leftCanonical hrealizes.of_pushR1C)
            have ha' := ha (leftValuation ws) valuation hp
            have hb' := hb (leftValuation ws) valuation hp
            have hc' := hc (leftValuation ws) valuation hp
            unfold WF.LCEq at ha' hb' hc'
            unfold Semantics.R1C.satisfies
            rw [← ha', ← hb', ← hc']
            exact hsat
        exact ih hnext hP' hvalid' hrun
      · simp [Semantics.Witgen.handler, hsat] at hrun
  | @f2z P aL aR kL kR ha hcont ih =>
      let outL : LC ℤ := LC.ofConst (aL.eval ws.boolWitness).toInt
      let outR : LC ℤ := {cs.result.m.size}
      let cs' := pushF2Z cs aR
      have hP' : ∀ leftVal rightVal,
          Compatible cs' ws leftVal rightVal →
          (P leftVal rightVal ∧
            outL.eval leftVal.int = (aL.eval leftVal.bool).toInt ∧
            outR.eval rightVal.int = (aR.eval rightVal.bool).toInt) := by
        intro leftVal rightVal hcompat
        have hrightOld := hcompat.right.of_pushF2Z
        have hp := hP leftVal rightVal
          ⟨hcompat.left_bools, hrightOld⟩
        have hpCanonical := hP (leftValuation ws) rightVal
          (Compatible.leftCanonical hrightOld)
        have harg := ha leftVal rightVal hp
        have hargCanonical := ha (leftValuation ws) rightVal hpCanonical
        unfold WF.LCEq at harg hargCanonical
        refine ⟨hp, ?_, ?_⟩
        · simp only [outL, LC.eval_ofConst]
          exact congrArg Bool.toInt (hargCanonical.trans harg.symm)
        · have hnew := hcompat.right.ints cs.result.m.size
              (by simp [cs', pushF2Z])
          simpa [outR, cs', pushF2Z] using hnew
      have hvalid' : ConstraintsValid cs' ws := by
        intro valuation hrealizes r hr
        apply hvalid valuation hrealizes.of_pushF2Z r
        simpa [cs', pushF2Z] using hr
      unfold Semantics.Witgen.runAt at hrun
      rw [Free.interp_bind] at hrun
      unfold F2Z.f2z at hrun
      rw [Free.interp_op] at hrun
      unfold Semantics.CSBuilder.runAt
      rw [Free.interp_bind]
      unfold F2Z.f2z
      rw [Free.interp_op]
      simp [Semantics.Witgen.handler, Semantics.CSBuilder.handler] at hrun ⊢
      exact ih outL outR hnext hP' hvalid' hrun
  | @hint P n argTps argsL argsR bodyL bodyR kL kR
      hargs hbody hcont ih =>
      unfold Semantics.Witgen.runAt at hrun
      rw [Free.interp_bind] at hrun
      unfold F2Z.hint at hrun
      rw [Free.interp_op] at hrun
      simp only [Semantics.Witgen.handler] at hrun
      generalize hbodyRun :
          Free.interp (fun {scope} => Semantics.Witgen.handler)
            (bodyL (Semantics.Witgen.evalArgs ws argsL)) = bodyResult at hrun
      cases bodyResult with
      | none => simp [hbodyRun] at hrun
      | some values =>
        let outL : Vector (LC Bool) n := values.map LC.ofConst
        let outR := csHintOut cs n
        let cs' := pushHint cs n
        let wsNext := appendHint ws values
        have hP' : ∀ leftVal rightVal,
            Compatible cs' wsNext leftVal rightVal →
            (P leftVal rightVal ∧ ∃ actual,
              WF.HintReturns
                (bodyL (WF.evalArgs leftVal argsL)) actual ∧
              WF.HintReturns
                (bodyR (WF.evalArgs rightVal argsR)) actual ∧
              WF.RealizesBools leftVal.bool outL actual ∧
              WF.RealizesBools rightVal.bool outR actual) := by
          intro leftVal rightVal hcompat
          have hleftOld := BoolsRealize.of_append hcompat.left_bools
          have hrightOld := hcompat.right.of_pushHint
          have hp := hP leftVal rightVal ⟨hleftOld, hrightOld⟩
          have hpCanonical := hP (leftValuation ws) rightVal
            (Compatible.leftCanonical hrightOld)
          have hbodyCanonical :=
            hbody (leftValuation ws) rightVal hpCanonical
          rw [evalArgs_canonical] at hbodyCanonical
          have hbodyCanonicalRuns := hintRel_witgen hbodyCanonical
          unfold Semantics.Witgen.runAt at hbodyCanonicalRuns
          rw [hbodyRun] at hbodyCanonicalRuns
          have hrightRun := optionRel_eq_some hbodyCanonicalRuns
          have hbodyAny := hbody leftVal rightVal hp
          have hbodyAnyRuns := hintRel_witgen hbodyAny
          unfold Semantics.Witgen.runAt at hbodyAnyRuns
          rw [hrightRun] at hbodyAnyRuns
          have hleftRun := optionRel_eq_some_right hbodyAnyRuns
          have hright := csHintOut_realizes cs ws values rightVal.bool
            hnext hcompat.right.bools
          refine ⟨hp, values, ?_, ?_, ?_, ?_⟩
          · exact hintReturns_of_witgen _ hleftRun
          · exact hintReturns_of_witgen _ hrightRun
          · exact constBools_realizes leftVal.bool values
          · exact hright
        have hvalid' : ConstraintsValid cs' wsNext := by
          intro valuation hrealizes r hr
          apply hvalid valuation hrealizes.of_pushHint r
          simpa [cs', pushHint] using hr
        have hnext' : cs'.nextWit = wsNext.bools.size := by
          simp [cs', pushHint, wsNext, appendHint, hnext]
        simp [hbodyRun] at hrun
        unfold Semantics.CSBuilder.runAt
        rw [Free.interp_bind]
        unfold F2Z.hint
        rw [Free.interp_op]
        simp [Semantics.CSBuilder.handler]
        exact ih outL outR hnext' hP' hvalid' hrun

private theorem ConstraintsValid.satisfies
    {cs : Semantics.CSBuilder} {ws : Semantics.Witgen.State}
    (h : ConstraintsValid cs ws) :
    cs.result.satisfies ws.boolWitness := by
  intro r hr
  exact h (rightValuation cs ws) (RightRealizes.canonical cs ws) r hr

private theorem triple_succeeds {x : Option α}
    (h : ⦃ ⌜True⌝ ⦄ x ⦃ ⇓ _ => ⌜True⌝ ⦄) :
    ∃ value, x = some value := by
  cases hx : x with
  | none =>
      rw [hx, Triple.iff] at h
      simp only [SPred.entails_nil] at h
      change True → False at h
      exact False.elim (h trivial)
  | some value => exact ⟨value, rfl⟩

/--
A completeness proof in the stateless semantics produces a concrete witness, and
that witness satisfies the constraints generated from the same external input.
-/
theorem adequate {circ : Vector (LC Bool) n → Circuit α}
    {inputs : Vector Bool n} {Q : WF.Post α}
    (hwf : WF.GadgetSpec
      (WF.VectorRel fun leftVal rightVal left right =>
        WF.LCEq leftVal.bool rightVal.bool left right)
      (fun {ctx} input => circ ctx input) Q)
    (hcomplete :
      ⦃ ⌜True⌝ ⦄
        interp (witnessValuation inputs.toArray)
          (circ (Vector.ofFn fun i => ({i.val} : LC Bool)))
      ⦃ ⇓ _ => ⌜True⌝ ⦄) :
    ∃ wit,
      Semantics.Witgen.runWithInputs circ inputs = some wit ∧
      (Semantics.CSBuilder.runWithInputs circ).2.satisfies (wit[·]!) := by
  let inputWires : Vector (LC Bool) n :=
    Vector.ofFn fun i => ({i.val} : LC Bool)
  let initialWs : Semantics.Witgen.State := { bools := inputs.toArray }
  let initialCs : Semantics.CSBuilder :=
    { result := { r1cs := #[], m := #[] }, nextWit := n }
  let inputVal := witnessValuation inputs.toArray
  have hrel : WF.Rel (fun _ _ _ _ => True)
      (fun leftVal rightVal => WF.VectorRel
        (fun leftVal rightVal left right =>
          WF.LCEq leftVal.bool rightVal.bool left right)
        leftVal rightVal inputWires inputWires)
      (circ inputWires) (circ inputWires) :=
    (hwf inputWires inputWires).mono fun _ _ _ _ _ => True.intro
  have hinterp : ∃ result, interp inputVal (circ inputWires) = some result := by
    apply triple_succeeds
    simpa [inputVal, inputWires] using hcomplete
  obtain ⟨result, hinterp⟩ := hinterp
  obtain ⟨value, ws, hwitgen⟩ := interp_runAt_adequate hrel
    (rightVal := inputVal) (ws := initialWs) (result := result) (by
      intro leftVal hleft i
      unfold WF.LCEq
      simp only [inputWires, Fin.getElem_fin, Vector.getElem_ofFn,
        LC.eval_singleton]
      rw [hleft i.val (by simp [initialWs])]
      rfl) hinterp
  refine ⟨ws.bools, ?_, ?_⟩
  · simp only [Semantics.Witgen.runWithInputs, Semantics.Witgen.run,
      Semantics.Witgen.run']
    simp [initialWs, inputWires, hwitgen]
  · have hvalid : ConstraintsValid initialCs initialWs := by
      intro valuation hrealizes r hr
      simp [initialCs] at hr
    have hconstraints := runAt_adequate hrel
      (cs := initialCs) (ws := initialWs) (ws' := ws) (value := value)
      (by simp [initialCs, initialWs]) (by
        intro leftVal rightVal hcompat i
        unfold WF.LCEq
        simp only [inputWires, Fin.getElem_fin, Vector.getElem_ofFn,
          LC.eval_singleton]
        rw [hcompat.left_bools i.val (by simp [initialWs]),
          hcompat.right.bools i.val (by simp [initialWs])])
      hvalid hwitgen
    simp only [Semantics.CSBuilder.runWithInputs,
      Semantics.CSBuilder.run, Semantics.CSBuilder.run'] at ⊢
    generalize hcs :
      StateT.run (Semantics.CSBuilder.runAt (circ inputWires)) initialCs =
        csResult at hconstraints ⊢
    rcases csResult with ⟨csValue, cs⟩
    exact hconstraints.2.satisfies
-/

/-- The symbolic valuation induced by a concrete Boolean witness. -/
def witnessValuation (wit : Array Bool) : WF.Valuation where
  bool := LC.valuation fun i => wit[i]!
  int := LC.valuation Semantics.Witgen.zeroWitness

private def BoolsRealize (ws : Semantics.Witgen.State)
    (valuation : Freigen.F2Z.Valuation Bool (LC Bool)) : Prop :=
  ∀ i, i < ws.bools.size → valuation ({i} : LC Bool) = ws.boolWitness i

private structure RightRealizes (cs : Semantics.CSBuilder)
    (ws : Semantics.Witgen.State) (valuation : WF.Valuation) : Prop where
  bools : BoolsRealize ws valuation.bool
  ints : ∀ (i : Nat) (hi : i < cs.result.m.size),
    valuation.int ({i} : LC ℤ) =
      (valuation.bool (cs.result.m[i]'hi)).toInt

private def ConstraintsValid (cs : Semantics.CSBuilder)
    (ws : Semantics.Witgen.State) : Prop :=
  ∀ valuation, RightRealizes cs ws valuation →
    ∀ r ∈ cs.result.r1cs,
      valuation.int r.a * valuation.int r.b = valuation.int r.c

private def csValuation (cs : Semantics.CSBuilder)
    (ws : Semantics.Witgen.State) : WF.Valuation where
  bool := LC.valuation ws.boolWitness
  int := LC.valuation (cs.result.intWitness ws.boolWitness)

private theorem BoolsRealize.self (ws : Semantics.Witgen.State) :
    BoolsRealize ws (LC.valuation ws.boolWitness) := by
  intro i hi
  rfl

private theorem RightRealizes.canonical (cs : Semantics.CSBuilder)
    (ws : Semantics.Witgen.State) :
    RightRealizes cs ws (csValuation cs ws) := by
  constructor
  · exact BoolsRealize.self ws
  · intro i hi
    rw [LC.Valuation.apply_eq_eval, LC.eval_singleton]
    change cs.result.intWitness ws.boolWitness i = _
    unfold Semantics.CS.intWitness
    rw [getElem!_pos _ _ (by simpa using hi), Array.getElem_map]
    rw [LC.Valuation.apply_eq_eval]
    rfl

private def pushR1C (cs : Semantics.CSBuilder) (a b c : LC ℤ) :
    Semantics.CSBuilder :=
  { cs with result := { cs.result with
      r1cs := cs.result.r1cs.push { a, b, c } } }

private def pushF2Z (cs : Semantics.CSBuilder) (a : LC Bool) :
    Semantics.CSBuilder :=
  { cs with result := { cs.result with m := cs.result.m.push a } }

private def pushHint (cs : Semantics.CSBuilder) (n : Nat) :
    Semantics.CSBuilder := { cs with nextWit := cs.nextWit + n }

private def appendHint (ws : Semantics.Witgen.State)
    (values : Vector Bool n) : Semantics.Witgen.State :=
  { ws with bools := ws.bools ++ values.toArray }

private def csHintOut (cs : Semantics.CSBuilder) (n : Nat) :
    Vector (LC Bool) n :=
  Vector.ofFn fun i => ({cs.nextWit + i.val} : LC Bool)

private theorem BoolsRealize.of_append {ws : Semantics.Witgen.State}
    {values : Vector Bool n} {valuation : Freigen.F2Z.Valuation Bool (LC Bool)}
    (h : BoolsRealize (appendHint ws values) valuation) :
    BoolsRealize ws valuation := by
  intro i hi
  rw [h i (by simp [appendHint]; omega)]
  unfold Semantics.Witgen.State.boolWitness appendHint
  rw [getElem!_pos ws.bools i hi]
  rw [getElem!_pos (ws.bools ++ values.toArray) i (by simp; omega)]
  exact Array.getElem_append_left hi

private theorem RightRealizes.of_pushR1C
    (h : RightRealizes (pushR1C cs a b c) ws valuation) :
    RightRealizes cs ws valuation := by
  exact ⟨h.bools, by intro i hi; simpa [pushR1C] using h.ints i hi⟩

private theorem RightRealizes.of_pushF2Z
    (h : RightRealizes (pushF2Z cs a) ws valuation) :
    RightRealizes cs ws valuation := by
  refine ⟨h.bools, ?_⟩
  intro i hi
  simpa [pushF2Z, Array.getElem_push_lt hi] using
    h.ints i (by simp [pushF2Z]; omega)

private theorem RightRealizes.of_pushHint
    (h : RightRealizes (pushHint cs n) (appendHint ws values) valuation) :
    RightRealizes cs ws valuation := by
  refine ⟨BoolsRealize.of_append h.bools, ?_⟩
  intro i hi
  simpa [pushHint, appendHint] using h.ints i hi

private theorem csHintOut_realizes {n : Nat} {cs : Semantics.CSBuilder}
    {ws : Semantics.Witgen.State} {values : Vector Bool n}
    {valuation : Freigen.F2Z.Valuation Bool (LC Bool)}
    (hnext : cs.nextWit = ws.bools.size)
    (h : BoolsRealize (appendHint ws values) valuation) :
    WF.RealizesBools valuation (csHintOut cs n) values := by
  intro i hi
  simp only [csHintOut, Vector.getElem_ofFn]
  rw [hnext]
  rw [h (ws.bools.size + i) (by simp [appendHint]; omega)]
  unfold Semantics.Witgen.State.boolWitness appendHint
  rw [getElem!_pos _ _ (by simp; omega), Array.getElem_append_right (by omega)]
  simp

private theorem value_evalArgs (ws : Semantics.Witgen.State) :
    {argTps : List Eff.WitnessSide} →
    (args : HList (Eff.WitnessSide.denoteW valueContext) argTps) →
    WF.evalArgs valueContext valueValuation args =
      Semantics.Witgen.evalArgs ws args
  | [], .nil => rfl
  | .z :: _, .cons x xs => by
      simp only [Eff.WitnessSide.denoteW] at x
      simp [WF.evalArgs, Semantics.Witgen.evalArgs, valueValuation,
        Context.identityValuation]
      exact value_evalArgs ws xs
  | .f₂ :: _, .cons x xs => by
      simp only [Eff.WitnessSide.denoteW] at x
      simp [WF.evalArgs, Semantics.Witgen.evalArgs, valueValuation,
        Context.identityValuation]
      exact value_evalArgs ws xs

private theorem hintInterp_witgen
    (body : @Hint valueContext α) :
    WF.interpHint body = Semantics.Witgen.runAt body := by
  let motive := fun (scope : Eff.Scope) (alpha : Type)
      (body : Free (Eff valueContext) scope alpha) =>
    match scope with
    | .constraint => True
    | .hint => WF.interpHint body = Semantics.Witgen.runAt body
  apply Free.recOn (motive := motive) body
  · intro scope alpha value
    cases scope <;> trivial
  · intro scope alpha e blocks k _ _
    cases scope with
    | constraint => trivial
    | hint =>
      cases e with
      | fail out msg =>
        dsimp [motive]
        simp only [WF.interpHint, Semantics.Witgen.runAt, Free.interp_bind]
        rw [Free.interp_op, Free.interp_op]
        simp [Semantics.Witgen.handler]

private theorem hintReturns_witgen
    {body : @Hint valueContext α} (h : WF.HintReturns body value) :
    Semantics.Witgen.runAt body = some value := by
  unfold WF.HintReturns at h
  rwa [hintInterp_witgen] at h

private theorem hintReturns_interp (valuation : WF.Valuation)
    {body : @Hint lcContext α} (h : WF.HintReturns body value) :
    Free.interp (interpHandler valuation) body = some value := by
  unfold WF.HintReturns at h
  rwa [interpHint_eq valuation] at h

private theorem optionRel_eq_some
    (h : Option.Rel Eq (some value) result) : result = some value := by
  cases h with
  | some h => subst h; rfl

private theorem optionRel_eq_some_right
    (h : Option.Rel Eq result (some value)) : result = some value := by
  cases h with
  | some h => subst h; rfl

/-- A successful symbolic interpretation implies successful execution in the
direct value representation. -/
private theorem interp_runAt_adequate
    {P : WF.Assumption valueContext lcContext}
    {left : @Circuit valueContext αL} {right : @Circuit lcContext αR}
    {ws : Semantics.Witgen.State} {result : αR}
    (hrel : WF.Rel (fun _ _ _ _ => True) P left right)
    (rightVal : @WF.Valuation lcContext)
    (hP : P valueValuation rightVal)
    (hinterp : interp rightVal right = some result) :
    ∃ value ws', StateT.run (Semantics.Witgen.runAt left) ws =
      some (value, ws') := by
  induction hrel generalizing ws result with
  | pure hpost => simp [interp, Semantics.Witgen.runAt] at hinterp ⊢
  | @assertR1C P aL bL cL aR bR cR kL kR ha hb hc hcont ih =>
      change ℤ at aL bL cL
      change LC ℤ at aR bR cR
      unfold interp at hinterp
      rw [Free.interp_bind] at hinterp
      unfold F2Z.assertR1C at hinterp
      rw [Free.interp_op] at hinterp
      by_cases hsatR : aR.eval rightVal.int * bR.eval rightVal.int =
          cR.eval rightVal.int
      · have hsatR' : rightVal.int aR * rightVal.int bR =
            rightVal.int cR := by
          rw [LC.Valuation.apply_eq_eval, LC.Valuation.apply_eq_eval,
            LC.Valuation.apply_eq_eval]
          exact hsatR
        simp [interpHandler, hsatR'] at hinterp
        have hsatL : aL * bL = cL := by
          have ha' := ha valueValuation rightVal hP
          have hb' := hb valueValuation rightVal hP
          have hc' := hc valueValuation rightVal hP
          unfold WF.LCEq at ha' hb' hc'
          simpa [valueValuation, Context.identityValuation,
            LC.Valuation.apply_eq_eval] using
            (show valueValuation.int aL * valueValuation.int bL =
              valueValuation.int cL by rw [ha', hb', hc']; exact hsatR')
        obtain ⟨value, ws', hrun⟩ := ih hP hinterp
        refine ⟨value, ws', ?_⟩
        unfold Semantics.Witgen.runAt
        rw [Free.interp_bind]
        unfold F2Z.assertR1C
        rw [Free.interp_op]
        simpa [Semantics.Witgen.handler, hsatL,
          Semantics.Witgen.runAt] using hrun
      · have hsatR' : ¬rightVal.int aR * rightVal.int bR =
            rightVal.int cR := by
          rw [LC.Valuation.apply_eq_eval, LC.Valuation.apply_eq_eval,
            LC.Valuation.apply_eq_eval]
          exact hsatR
        simp [interpHandler, hsatR'] at hinterp
  | @f2z P aL aR kL kR ha hcont ih =>
      change Bool at aL
      change LC Bool at aR
      let outL : ℤ := aL.toInt
      let outR : LC ℤ := LC.ofConst (rightVal.bool aR).toInt
      have hP' : P valueValuation rightVal ∧
          valueValuation.int outL = (valueValuation.bool aL).toInt ∧
          rightVal.int outR = (rightVal.bool aR).toInt := by
        refine ⟨hP, ?_, ?_⟩
        · rfl
        · exact LC.Valuation.ofConst_apply rightVal.int _
      unfold interp at hinterp
      rw [Free.interp_bind] at hinterp
      unfold F2Z.f2z at hinterp
      rw [Free.interp_op] at hinterp
      simp [interpHandler] at hinterp
      obtain ⟨value, ws', hrun⟩ := ih outL outR hP' hinterp
      refine ⟨value, ws', ?_⟩
      unfold Semantics.Witgen.runAt
      rw [Free.interp_bind]
      unfold F2Z.f2z
      rw [Free.interp_op]
      simpa [Semantics.Witgen.handler, outL,
        Semantics.Witgen.runAt] using hrun
  | @hint P n argTps argsL argsR bodyL bodyR kL kR hargs hbody hcont ih =>
      unfold interp at hinterp
      rw [Free.interp_bind] at hinterp
      unfold F2Z.hint at hinterp
      rw [Free.interp_op] at hinterp
      simp only [interpHandler] at hinterp
      generalize hrunR : Free.interp (interpHandler rightVal)
        (bodyR (WF.evalArgs lcContext rightVal argsR)) = bodyResult at hinterp
      cases bodyResult with
      | none => simp at hinterp
      | some values =>
        have hbodyRel := hbody valueValuation rightVal hP
        unfold WF.HintRel at hbodyRel
        rw [interpHint_eq rightVal, hrunR] at hbodyRel
        have hleftReturns := optionRel_eq_some_right hbodyRel
        have hleftReturnsRun : WF.HintReturns
            (bodyL (Semantics.Witgen.evalArgs ws argsL)) values := by
          unfold WF.HintReturns
          rw [← value_evalArgs ws]
          exact hleftReturns
        have hrunL := hintReturns_witgen hleftReturnsRun
        unfold Semantics.Witgen.runAt at hrunL
        let outL : Vector Bool n := values
        let outR : Vector (LC Bool) n := values.map LC.ofConst
        have hP' : P valueValuation rightVal ∧ ∃ actual,
            WF.HintReturns (bodyL (WF.evalArgs valueContext valueValuation argsL)) actual ∧
            WF.HintReturns (bodyR (WF.evalArgs lcContext rightVal argsR)) actual ∧
            WF.RealizesBools valueValuation.bool outL actual ∧
            WF.RealizesBools rightVal.bool outR actual := by
          refine ⟨hP, values, hleftReturns, ?_, ?_, ?_⟩
          · unfold WF.HintReturns
            rw [interpHint_eq rightVal]
            exact hrunR
          · intro i hi; rfl
          · intro i hi
            rw [LC.Valuation.apply_eq_eval]
            simp [outR]
        simp at hinterp
        obtain ⟨value, ws', hrun⟩ := ih outL outR hP' hinterp
        refine ⟨value, ws', ?_⟩
        unfold Semantics.Witgen.runAt
        rw [Free.interp_bind]
        unfold F2Z.hint
        rw [Free.interp_op]
        simp [Semantics.Witgen.handler, hrunL, appendHint]
        simpa [outL, Semantics.Witgen.runAt] using hrun

/-- Lockstep direct execution and symbolic construction preserve constraint
validity for every valuation represented by the generated witness. -/
private theorem runAt_adequate
    {P : WF.Assumption valueContext lcContext}
    {left : @Circuit valueContext αL} {right : @Circuit lcContext αR}
    {cs : Semantics.CSBuilder} {ws ws' : Semantics.Witgen.State}
    {value : αL}
    (hrel : WF.Rel (fun _ _ _ _ => True) P left right)
    (hnext : cs.nextWit = ws.bools.size)
    (hP : ∀ rightVal, RightRealizes cs ws rightVal →
      P valueValuation rightVal)
    (hvalid : ConstraintsValid cs ws)
    (hrun : StateT.run (Semantics.Witgen.runAt left) ws =
      some (value, ws')) :
    let result := StateT.run (Semantics.CSBuilder.runAt right) cs
    result.2.nextWit = ws'.bools.size ∧ ConstraintsValid result.2 ws' := by
  induction hrel generalizing cs ws ws' value with
  | pure hpost =>
      simp [Semantics.Witgen.runAt] at hrun
      rcases hrun with ⟨rfl, rfl⟩
      exact ⟨hnext, hvalid⟩
  | @assertR1C P aL bL cL aR bR cR kL kR ha hb hc hcont ih =>
      change ℤ at aL bL cL
      change LC ℤ at aR bR cR
      unfold Semantics.Witgen.runAt at hrun
      rw [Free.interp_bind] at hrun
      unfold F2Z.assertR1C at hrun
      rw [Free.interp_op] at hrun
      by_cases hsatL : aL * bL = cL
      · simp [Semantics.Witgen.handler, hsatL] at hrun
        let cs' := pushR1C cs aR bR cR
        have hP' : ∀ rv, RightRealizes cs' ws rv → P valueValuation rv :=
          fun rv hrv => hP rv hrv.of_pushR1C
        have hvalid' : ConstraintsValid cs' ws := by
          intro rv hrv r hr
          simp only [cs', pushR1C, Array.mem_push] at hr
          rcases hr with hr | rfl
          · exact hvalid rv hrv.of_pushR1C r hr
          · have hp := hP rv hrv.of_pushR1C
            have ha' := ha valueValuation rv hp
            have hb' := hb valueValuation rv hp
            have hc' := hc valueValuation rv hp
            unfold WF.LCEq at ha' hb' hc'
            calc
              rv.int aR * rv.int bR =
                  valueValuation.int aL * valueValuation.int bL := by
                    rw [ha'.symm, hb'.symm]
              _ = valueValuation.int cL := by
                    simpa [valueValuation, Context.identityValuation] using hsatL
              _ = rv.int cR := hc'
        unfold Semantics.CSBuilder.runAt
        rw [Free.interp_bind]
        unfold F2Z.assertR1C
        rw [Free.interp_op]
        simp [Semantics.CSBuilder.handler]
        exact ih hnext hP' hvalid' hrun
      · simp [Semantics.Witgen.handler, hsatL] at hrun
  | @f2z P aL aR kL kR ha hcont ih =>
      change Bool at aL
      change LC Bool at aR
      let outL : ℤ := aL.toInt
      let outR : LC ℤ := {cs.result.m.size}
      let cs' := pushF2Z cs aR
      have hP' : ∀ rv, RightRealizes cs' ws rv →
          (P valueValuation rv ∧
            valueValuation.int outL = (valueValuation.bool aL).toInt ∧
            rv.int outR = (rv.bool aR).toInt) := by
        intro rv hrv
        refine ⟨hP rv hrv.of_pushF2Z, rfl, ?_⟩
        have hnew := hrv.ints cs.result.m.size (by simp [cs', pushF2Z])
        simpa [outR, cs', pushF2Z] using hnew
      have hvalid' : ConstraintsValid cs' ws := by
        intro rv hrv r hr
        exact hvalid rv hrv.of_pushF2Z r (by simpa [cs', pushF2Z] using hr)
      unfold Semantics.Witgen.runAt at hrun
      rw [Free.interp_bind] at hrun
      unfold F2Z.f2z at hrun
      rw [Free.interp_op] at hrun
      simp [Semantics.Witgen.handler] at hrun
      unfold Semantics.CSBuilder.runAt
      rw [Free.interp_bind]
      unfold F2Z.f2z
      rw [Free.interp_op]
      simp [Semantics.CSBuilder.handler]
      exact ih outL outR hnext hP' hvalid' hrun
  | @hint P n argTps argsL argsR bodyL bodyR kL kR hargs hbody hcont ih =>
      unfold Semantics.Witgen.runAt at hrun
      rw [Free.interp_bind] at hrun
      unfold F2Z.hint at hrun
      rw [Free.interp_op] at hrun
      simp only [Semantics.Witgen.handler] at hrun
      generalize hbodyRun : Free.interp (fun {scope} => Semantics.Witgen.handler)
        (bodyL (Semantics.Witgen.evalArgs ws argsL)) = bodyResult at hrun
      cases bodyResult with
      | none => simp [hbodyRun] at hrun
      | some values =>
        let outL : Vector Bool n := values
        let outR := csHintOut cs n
        let cs' := pushHint cs n
        let wsNext := appendHint ws values
        have hP' : ∀ rv, RightRealizes cs' wsNext rv →
            (P valueValuation rv ∧ ∃ actual,
              WF.HintReturns (bodyL (WF.evalArgs valueContext valueValuation argsL)) actual ∧
              WF.HintReturns (bodyR (WF.evalArgs lcContext rv argsR)) actual ∧
              WF.RealizesBools valueValuation.bool outL actual ∧
              WF.RealizesBools rv.bool outR actual) := by
          intro rv hrv
          have hrvOld := hrv.of_pushHint
          have hp := hP rv hrvOld
          have hrelBody := hbody valueValuation rv hp
          rw [value_evalArgs ws] at hrelBody
          unfold WF.HintRel at hrelBody
          have hleftReturnsRun : WF.HintReturns
              (bodyL (Semantics.Witgen.evalArgs ws argsL)) values := by
            unfold WF.HintReturns
            rw [hintInterp_witgen]
            exact hbodyRun
          have hleftReturns : WF.HintReturns
              (bodyL (WF.evalArgs valueContext valueValuation argsL)) values := by
            unfold WF.HintReturns at hleftReturnsRun ⊢
            rw [value_evalArgs ws]
            exact hleftReturnsRun
          unfold WF.HintReturns at hleftReturnsRun
          rw [hleftReturnsRun] at hrelBody
          have hrightReturns := optionRel_eq_some hrelBody
          refine ⟨hp, values, ?_, ?_, ?_, ?_⟩
          · exact hleftReturns
          · exact hrightReturns
          · intro i hi; rfl
          · exact csHintOut_realizes hnext hrv.bools
        have hvalid' : ConstraintsValid cs' wsNext := by
          intro rv hrv r hr
          exact hvalid rv hrv.of_pushHint r (by simpa [cs', pushHint] using hr)
        have hnext' : cs'.nextWit = wsNext.bools.size := by
          simp [cs', pushHint, wsNext, appendHint, hnext]
        simp [hbodyRun] at hrun
        unfold Semantics.CSBuilder.runAt
        rw [Free.interp_bind]
        unfold F2Z.hint
        rw [Free.interp_op]
        simp [Semantics.CSBuilder.handler]
        exact ih outL outR hnext' hP' hvalid' hrun

private theorem ConstraintsValid.satisfies
    (h : ConstraintsValid cs ws) : cs.result.satisfies ws.boolWitness := by
  intro r hr
  have hs := h (csValuation cs ws) (RightRealizes.canonical cs ws) r hr
  change r.a.eval (cs.result.intWitness ws.boolWitness) *
      r.b.eval (cs.result.intWitness ws.boolWitness) =
    r.c.eval (cs.result.intWitness ws.boolWitness) at hs
  exact hs

private theorem triple_succeeds {x : Option α}
    (h : ⦃ ⌜True⌝ ⦄ x ⦃ ⇓ _ => ⌜True⌝ ⦄) :
    ∃ value, x = some value := by
  cases hx : x with
  | none =>
      rw [hx, Triple.iff] at h
      simp only [SPred.entails_nil] at h
      exact False.elim (h trivial)
  | some value => exact ⟨value, rfl⟩

/-- Completeness for a context-polymorphic circuit: successful symbolic
interpretation produces a direct witness satisfying the generated system. -/
theorem adequate
    {Output : Context → Type}
    {circ : ∀ ctx : Context,
      Vector ctx.WBool n → @Circuit ctx (Output ctx)}
    {inputs : Vector Bool n}
    {Q : ∀ {leftCtx rightCtx},
      @WF.Valuation leftCtx → @WF.Valuation rightCtx →
      Output leftCtx → Output rightCtx → Prop}
    (hwf : WF.GadgetSpec
      (fun {leftCtx rightCtx} leftVal rightVal
          (left : Vector leftCtx.WBool n) (right : Vector rightCtx.WBool n) =>
        WF.VectorRel
          (fun _ _ l r => WF.LCEq leftVal.bool rightVal.bool l r)
          leftVal rightVal left right)
      (fun {ctx} input => circ ctx input) Q)
    (hcomplete :
      ⦃ ⌜True⌝ ⦄
        interp (witnessValuation inputs.toArray)
          (circ lcContext (Vector.ofFn fun i => ({i.val} : LC Bool)))
      ⦃ ⇓ _ => ⌜True⌝ ⦄) :
    ∃ wit,
      Semantics.Witgen.runWithInputs (circ valueContext) inputs = some wit ∧
      (Semantics.CSBuilder.runWithInputs (circ lcContext)).2.satisfies
        (wit[·]!) := by
  let inputWires : Vector (LC Bool) n :=
    Vector.ofFn fun i => ({i.val} : LC Bool)
  let initialWs : Semantics.Witgen.State := { bools := inputs.toArray }
  let initialCs : Semantics.CSBuilder :=
    { result := { r1cs := #[], m := #[] }, nextWit := n }
  let inputVal := witnessValuation inputs.toArray
  have hrel : WF.Rel (fun _ _ _ _ => True)
      (fun (lv : @WF.Valuation valueContext)
          (rv : @WF.Valuation lcContext) => WF.VectorRel
        (fun _ _ (l : Bool) (r : LC Bool) =>
          WF.LCEq lv.bool rv.bool l r)
        lv rv inputs inputWires)
      (circ valueContext inputs) (circ lcContext inputWires) :=
    (hwf valueContext lcContext inputs inputWires).mono
      fun _ _ _ _ _ => True.intro
  have hP : WF.VectorRel
      (fun _ _ l r => WF.LCEq valueValuation.bool inputVal.bool l r)
      valueValuation inputVal inputs inputWires := by
    intro i
    unfold WF.LCEq
    rw [LC.Valuation.apply_eq_eval]
    simp [inputVal, inputWires, witnessValuation,
      valueValuation, Context.identityValuation]
  have hinterp : ∃ result,
      interp inputVal (circ lcContext inputWires) = some result :=
    triple_succeeds (by simpa [inputVal, inputWires] using hcomplete)
  obtain ⟨result, hinterp⟩ := hinterp
  obtain ⟨value, ws, hwitgen⟩ :=
    interp_runAt_adequate hrel inputVal hP hinterp (ws := initialWs)
  refine ⟨ws.bools, ?_, ?_⟩
  · simp only [Semantics.Witgen.runWithInputs, Semantics.Witgen.run,
      Semantics.Witgen.run']
    simp [initialWs, hwitgen]
  · have hvalid : ConstraintsValid initialCs initialWs := by
      intro valuation hrealizes r hr
      simp [initialCs] at hr
    have hinput : ∀ rv, RightRealizes initialCs initialWs rv →
        WF.VectorRel (fun _ _ l r => WF.LCEq valueValuation.bool rv.bool l r)
          valueValuation rv inputs inputWires := by
      intro rv hrv i
      unfold WF.LCEq
      simp [valueValuation, Context.identityValuation, inputWires]
      rw [hrv.bools i.val (by simp [initialWs])]
      unfold Semantics.Witgen.State.boolWitness
      rw [getElem!_pos inputs.toArray i.val (by simp)]
      rfl
    have hconstraints := runAt_adequate hrel
      (cs := initialCs) (ws := initialWs) (ws' := ws) (value := value)
      (by simp [initialCs, initialWs]) hinput hvalid hwitgen
    simp only [Semantics.CSBuilder.runWithInputs,
      Semantics.CSBuilder.run, Semantics.CSBuilder.run'] at ⊢
    generalize hcs :
      StateT.run (Semantics.CSBuilder.runAt (circ lcContext inputWires)) initialCs =
        csResult at hconstraints ⊢
    rcases csResult with ⟨csValue, cs⟩
    exact hconstraints.2.satisfies

end Freigen.F2Z.Complete
