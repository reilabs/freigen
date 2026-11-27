import Freigen.F2Z.Correctness.WF

namespace Freigen.F2Z.WF

/-- An assertion preserves the ambient valuation relation. -/
theorem Rel.assertR1C_rel {P : Assumption}
    {aL bL cL aR bR cR : LC ℤ}
    (ha : ∀ leftVal rightVal, P leftVal rightVal →
      LCEq leftVal.int rightVal.int aL aR)
    (hb : ∀ leftVal rightVal, P leftVal rightVal →
      LCEq leftVal.int rightVal.int bL bR)
    (hc : ∀ leftVal rightVal, P leftVal rightVal →
      LCEq leftVal.int rightVal.int cL cR) :
    Rel (fun leftVal rightVal _ _ => P leftVal rightVal) P
      (F2Z.assertR1C aL bL cL) (F2Z.assertR1C aR bR cR) :=
  Rel.assertR1C_pure ha hb hc fun _ _ h => h

/-- Apply a relational effect rule without throwing away the ambient relation.
This is the compositional form used when the result is subsequently bound. -/
theorem RelHom.relAmbient {R : Post α} {S : Post β}
    {fL fR : α → Circuit β} (h : RelHom R S fL fR)
    {P : Assumption} {left right : α}
    (hinput : ∀ leftVal rightVal, P leftVal rightVal →
      R leftVal rightVal left right) :
    Rel (fun leftVal rightVal outL outR =>
      P leftVal rightVal ∧ S leftVal rightVal outL outR)
      P (fL left) (fR right) :=
  h P left right hinput

/-- The primitive Boolean-to-integer conversion, preserving its ambient
valuation assumptions for subsequent binds. -/
theorem Rel.f2z_rel {P : Assumption} {left right : LC Bool}
    (hinput : ∀ leftVal rightVal, P leftVal rightVal →
      LCEq leftVal.bool rightVal.bool left right) :
    Rel (fun leftVal rightVal outL outR =>
      P leftVal rightVal ∧ LCEq leftVal.int rightVal.int outL outR)
      P (F2Z.f2z left) (F2Z.f2z right) :=
  RelHom.f2z.relAmbient hinput

/-- Converting a Boolean LC and adding a fixed natural multiple of it to an
integer-LC accumulator preserves the ambient assumptions and accumulator
equivalence. -/
theorem RelHom.f2z_add_nsmul {P : Assumption}
    {left right : LC Bool} (c : Nat)
    (hinput : ∀ leftVal rightVal, P leftVal rightVal →
      LCEq leftVal.bool rightVal.bool left right) :
    RelHom
      (fun leftVal rightVal left right =>
        P leftVal rightVal ∧ LCEq leftVal.int rightVal.int left right)
      (fun leftVal rightVal left right =>
        P leftVal rightVal ∧ LCEq leftVal.int rightVal.int left right)
      (fun acc => do
        let value ← F2Z.f2z left
        Pure.pure (acc + c • value))
      (fun acc => do
        let value ← F2Z.f2z right
        Pure.pure (acc + c • value)) := by
  intro A accL accR hacc
  have hf2z := Rel.f2z_rel fun leftVal rightVal hA =>
    hinput leftVal rightVal (hacc leftVal rightVal hA).1
  apply hf2z.bind
    (fun value => Pure.pure (accL + c • value))
    (fun value => Pure.pure (accR + c • value))
  intro B valueL valueR hvalue
  exact Rel.pure fun leftVal rightVal hB => by
    have hvalue := hvalue leftVal rightVal hB
    have hbase := hacc leftVal rightVal hvalue.1
    refine ⟨hvalue.1, hbase.1, ?_⟩
    unfold LCEq at *
    simp only [LC.eval_add, LC.eval_nsmul]
    rw [hbase.2, hvalue.2]

/-- Converting a Boolean LC and storing it at the same in-bounds position in
two vector accumulators preserves pointwise evaluated equality. -/
theorem RelHom.f2z_set! {P : Assumption} {left right : LC Bool}
    {i n : Nat} (_hi : i < n)
    (hinput : ∀ leftVal rightVal, P leftVal rightVal →
      LCEq leftVal.bool rightVal.bool left right) :
    RelHom
      (fun leftVal rightVal (left right : Vector (LC ℤ) n) =>
        P leftVal rightVal ∧
          VectorRel (fun leftVal rightVal left right =>
            LCEq leftVal.int rightVal.int left right)
            leftVal rightVal left right)
      (fun leftVal rightVal (left right : Vector (LC ℤ) n) =>
        P leftVal rightVal ∧
          VectorRel (fun leftVal rightVal left right =>
            LCEq leftVal.int rightVal.int left right)
            leftVal rightVal left right)
      (fun acc => do
        let value ← F2Z.f2z left
        Pure.pure (acc.set! i value))
      (fun acc => do
        let value ← F2Z.f2z right
        Pure.pure (acc.set! i value)) := by
  intro A accL accR hacc
  have hf2z := Rel.f2z_rel fun leftVal rightVal hA =>
    hinput leftVal rightVal (hacc leftVal rightVal hA).1
  apply hf2z.bind
    (fun value => Pure.pure (accL.set! i value))
    (fun value => Pure.pure (accR.set! i value))
  intro B valueL valueR hvalue
  exact Rel.pure fun leftVal rightVal hB => by
    have hvalue := hvalue leftVal rightVal hB
    have hbase := hacc leftVal rightVal hvalue.1
    refine ⟨hvalue.1, hbase.1, ?_⟩
    intro j
    simp only [Fin.getElem_fin, LCEq] at hbase ⊢
    rw [show accL.set! i valueL = accL.setIfInBounds i valueL by rfl,
      show accR.set! i valueR = accR.setIfInBounds i valueR by rfl]
    simp only [Vector.getElem_setIfInBounds j.isLt]
    split
    · exact hvalue.2
    · exact hbase.2 j

/-- Pointwise Boolean-to-integer conversion over vectors. -/
theorem Rel.mapM_f2z_rel {P : Assumption}
    {left right : Vector (LC Bool) n}
    (hinput : ∀ leftVal rightVal, P leftVal rightVal →
      VectorRel (fun leftVal rightVal left right =>
        LCEq leftVal.bool rightVal.bool left right)
        leftVal rightVal left right) :
    Rel (fun leftVal rightVal outL outR =>
      P leftVal rightVal ∧
      VectorRel (fun leftVal rightVal left right =>
        LCEq leftVal.int rightVal.int left right)
        leftVal rightVal outL outR)
      P (left.mapM F2Z.f2z) (right.mapM F2Z.f2z) :=
  RelHom.f2z.vectorMapM.relAmbient hinput

/-- A list loop whose body always yields preserves any relation preserved by
each aligned iteration. -/
theorem Rel.forIn'_list_yield
    {R : Post β} {P : Assumption} {xs : List α}
    {initL initR : β}
    {fL fR : (a : α) → a ∈ xs → β → Circuit β}
    (hinit : ∀ leftVal rightVal, P leftVal rightVal →
      R leftVal rightVal initL initR)
    (hstep : ∀ a h, RelHom R R (fL a h) (fR a h)) :
    Rel R P
      (forIn' xs initL fun a h b => do
        let b ← fL a h b
        Pure.pure (ForInStep.yield b))
      (forIn' xs initR fun a h b => do
        let b ← fR a h b
        Pure.pure (ForInStep.yield b)) := by
  induction xs generalizing initL initR P with
  | nil =>
      simp only [List.forIn'_nil]
      exact Rel.pure hinit
  | cons a xs ih =>
      simp only [List.forIn'_cons, bind_assoc, pure_bind]
      have hhead := hstep a (by simp)
      apply hhead P initL initR hinit |>.bind
        (fun b => forIn' xs b fun a h b => do
          let b ← fL a (by simp [h]) b
          Pure.pure (ForInStep.yield b))
        (fun b => forIn' xs b fun a h b => do
          let b ← fR a (by simp [h]) b
          Pure.pure (ForInStep.yield b))
      intro A left right hA
      apply ih
      · intro leftVal rightVal h
        exact (hA leftVal rightVal h).2
      · intro x hx
        exact hstep x (by simp [hx])

/-- The corresponding rule for the legacy range syntax generated by `for`. -/
theorem Rel.forIn'_range_yield
    {R : Post β} {P : Assumption} {xs : Std.Legacy.Range}
    {initL initR : β}
    {fL fR : (a : Nat) → a ∈ xs → β → Circuit β}
    (hinit : ∀ leftVal rightVal, P leftVal rightVal →
      R leftVal rightVal initL initR)
    (hstep : ∀ a h, RelHom R R (fL a h) (fR a h)) :
    Rel R P
      (forIn' xs initL fun a h b => do
        let b ← fL a h b
        Pure.pure (ForInStep.yield b))
      (forIn' xs initR fun a h b => do
        let b ← fR a h b
        Pure.pure (ForInStep.yield b)) := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range',
    Std.Legacy.Range.forIn'_eq_forIn'_range']
  apply Rel.forIn'_list_yield hinit
  intro a h
  exact hstep a (Std.Legacy.Range.mem_of_mem_range' h)

/-- A range loop followed by a continuation. This fused form lets proof search
infer the loop invariant from the continuation before descending into the body. -/
theorem Rel.forIn'_range_yield_bind
    {R : Post β} {Q : Post γ} {P : Assumption}
    {xs : Std.Legacy.Range} {initL initR : β}
    {fL fR : (a : Nat) → a ∈ xs → β → Circuit β}
    {kL kR : β → Circuit γ}
    (hinit : ∀ leftVal rightVal, P leftVal rightVal →
      R leftVal rightVal initL initR)
    (hstep : ∀ a h, RelHom R R (fL a h) (fR a h))
    (hcont : ∀ (A : Assumption) left right,
      (∀ leftVal rightVal, A leftVal rightVal →
        R leftVal rightVal left right) →
      Rel Q A (kL left) (kR right)) :
    Rel Q P
      ((forIn' xs initL fun a h b => do
        let b ← fL a h b
        Pure.pure (ForInStep.yield b)) >>= kL)
      ((forIn' xs initR fun a h b => do
        let b ← fR a h b
        Pure.pure (ForInStep.yield b)) >>= kR) :=
  (Rel.forIn'_range_yield hinit hstep).bind kL kR hcont

/-- A range loop iteration that obtains an intermediate effectful result and
then folds it into the accumulator. -/
theorem Rel.forIn'_range_map_yield
    {R : Post β} {P : Assumption} {xs : Std.Legacy.Range}
    {initL initR : β}
    {fL fR : (a : Nat) → a ∈ xs → β → Circuit δ}
    {nextL nextR : (a : Nat) → a ∈ xs → β → δ → β}
    (hinit : ∀ leftVal rightVal, P leftVal rightVal →
      R leftVal rightVal initL initR)
    (hstep : ∀ a h, RelHom R R
      (fun b => do
        let x ← fL a h b
        Pure.pure (nextL a h b x))
      (fun b => do
        let x ← fR a h b
        Pure.pure (nextR a h b x))) :
    Rel R P
      (forIn' xs initL fun a h b => do
        let x ← fL a h b
        Pure.pure (ForInStep.yield (nextL a h b x)))
      (forIn' xs initR fun a h b => do
        let x ← fR a h b
        Pure.pure (ForInStep.yield (nextR a h b x))) := by
  have h := Rel.forIn'_range_yield hinit hstep
  simpa only [bind_assoc, pure_bind] using h

/-- Fused continuation form of `Rel.forIn'_range_map_yield`. -/
theorem Rel.forIn'_range_map_yield_bind
    {R : Post β} {Q : Post γ} {P : Assumption}
    {xs : Std.Legacy.Range} {initL initR : β}
    {fL fR : (a : Nat) → a ∈ xs → β → Circuit δ}
    {nextL nextR : (a : Nat) → a ∈ xs → β → δ → β}
    {kL kR : β → Circuit γ}
    (hinit : ∀ leftVal rightVal, P leftVal rightVal →
      R leftVal rightVal initL initR)
    (hstep : ∀ a h, RelHom R R
      (fun b => do
        let x ← fL a h b
        Pure.pure (nextL a h b x))
      (fun b => do
        let x ← fR a h b
        Pure.pure (nextR a h b x)))
    (hcont : ∀ (A : Assumption) left right,
      (∀ leftVal rightVal, A leftVal rightVal →
        R leftVal rightVal left right) →
      Rel Q A (kL left) (kR right)) :
    Rel Q P
      ((forIn' xs initL fun a h b => do
        let x ← fL a h b
        Pure.pure (ForInStep.yield (nextL a h b x))) >>= kL)
      ((forIn' xs initR fun a h b => do
        let x ← fR a h b
        Pure.pure (ForInStep.yield (nextR a h b x))) >>= kR) :=
  (Rel.forIn'_range_map_yield hinit hstep).bind kL kR hcont

/-- The canonical F2Z loop invariant for integer linear-combination
accumulators: retain the ambient assumptions and preserve evaluated equality. -/
theorem Rel.forIn'_range_map_yield_intLC_bind
    {Q : Post γ} {P : Assumption} {xs : Std.Legacy.Range}
    {initL initR : LC ℤ}
    {fL fR : (a : Nat) → a ∈ xs → LC ℤ → Circuit δ}
    {nextL nextR : (a : Nat) → a ∈ xs → LC ℤ → δ → LC ℤ}
    {kL kR : LC ℤ → Circuit γ}
    (hinit : ∀ leftVal rightVal, P leftVal rightVal →
      LCEq leftVal.int rightVal.int initL initR)
    (hstep : ∀ a h,
      RelHom
        (fun leftVal rightVal left right =>
          P leftVal rightVal ∧ LCEq leftVal.int rightVal.int left right)
        (fun leftVal rightVal left right =>
          P leftVal rightVal ∧ LCEq leftVal.int rightVal.int left right)
        (fun b => do
          let x ← fL a h b
          Pure.pure (nextL a h b x))
        (fun b => do
          let x ← fR a h b
          Pure.pure (nextR a h b x)))
    (hcont : ∀ (A : Assumption) left right,
      (∀ leftVal rightVal, A leftVal rightVal →
        P leftVal rightVal ∧ LCEq leftVal.int rightVal.int left right) →
      Rel Q A (kL left) (kR right)) :
    Rel Q P
      ((forIn' xs initL fun a h b => do
        let x ← fL a h b
        Pure.pure (ForInStep.yield (nextL a h b x))) >>= kL)
      ((forIn' xs initR fun a h b => do
        let x ← fR a h b
        Pure.pure (ForInStep.yield (nextR a h b x))) >>= kR) := by
  apply Rel.forIn'_range_map_yield_bind
    (R := fun leftVal rightVal left right =>
      P leftVal rightVal ∧ LCEq leftVal.int rightVal.int left right)
  · intro leftVal rightVal hP
    exact ⟨hP, hinit leftVal rightVal hP⟩
  · exact hstep
  · exact hcont

/-- Canonical F2Z range loop: convert a Boolean LC, add a natural-scaled copy
to an integer-LC accumulator, then continue. -/
theorem Rel.forIn'_range_f2z_add_nsmul_bind
    {Q : Post γ} {P : Assumption} {xs : Std.Legacy.Range}
    {initL initR : LC ℤ}
    {inputL inputR : (a : Nat) → a ∈ xs → LC Bool}
    {coeff : (a : Nat) → a ∈ xs → Nat}
    {kL kR : LC ℤ → Circuit γ}
    (hinit : ∀ leftVal rightVal, P leftVal rightVal →
      LCEq leftVal.int rightVal.int initL initR)
    (hinput : ∀ a h leftVal rightVal, P leftVal rightVal →
      LCEq leftVal.bool rightVal.bool (inputL a h) (inputR a h))
    (hcont : ∀ (A : Assumption) left right,
      (∀ leftVal rightVal, A leftVal rightVal →
        P leftVal rightVal ∧ LCEq leftVal.int rightVal.int left right) →
      Rel Q A (kL left) (kR right)) :
    Rel Q P
      ((forIn' xs initL fun a h acc => do
        let value ← F2Z.f2z (inputL a h)
        Pure.pure (ForInStep.yield (acc + coeff a h • value))) >>= kL)
      ((forIn' xs initR fun a h acc => do
        let value ← F2Z.f2z (inputR a h)
        Pure.pure (ForInStep.yield (acc + coeff a h • value))) >>= kR) := by
  apply Rel.forIn'_range_map_yield_intLC_bind
  · exact hinit
  · intro a h
    exact RelHom.f2z_add_nsmul (coeff a h) (hinput a h)
  · exact hcont

/-- Canonical F2Z range loop with a vector accumulator: convert each Boolean
LC and store it at the loop index, then continue. -/
theorem Rel.forIn'_range_f2z_set!_bind
    {Q : Post γ} {P : Assumption} {xs : Std.Legacy.Range}
    {initL initR : Vector (LC ℤ) n}
    {inputL inputR : (a : Nat) → a ∈ xs → LC Bool}
    {kL kR : Vector (LC ℤ) n → Circuit γ}
    (hinit : ∀ leftVal rightVal, P leftVal rightVal →
      VectorRel (fun leftVal rightVal left right =>
        LCEq leftVal.int rightVal.int left right)
        leftVal rightVal initL initR)
    (hinput : ∀ a h leftVal rightVal, P leftVal rightVal →
      LCEq leftVal.bool rightVal.bool (inputL a h) (inputR a h))
    (hbound : ∀ a, a ∈ xs → a < n)
    (hcont : ∀ (A : Assumption) left right,
      (∀ leftVal rightVal, A leftVal rightVal →
        P leftVal rightVal ∧
          VectorRel (fun leftVal rightVal left right =>
            LCEq leftVal.int rightVal.int left right)
            leftVal rightVal left right) →
      Rel Q A (kL left) (kR right)) :
    Rel Q P
      ((forIn' xs initL fun a h acc => do
        let value ← F2Z.f2z (inputL a h)
        Pure.pure (ForInStep.yield (acc.set! a value))) >>= kL)
      ((forIn' xs initR fun a h acc => do
        let value ← F2Z.f2z (inputR a h)
        Pure.pure (ForInStep.yield (acc.set! a value))) >>= kR) := by
  apply Rel.forIn'_range_map_yield_bind
    (R := fun leftVal rightVal left right =>
      P leftVal rightVal ∧
        VectorRel (fun leftVal rightVal left right =>
          LCEq leftVal.int rightVal.int left right)
          leftVal rightVal left right)
  · intro leftVal rightVal hP
    exact ⟨hP, hinit leftVal rightVal hP⟩
  · intro a h
    exact RelHom.f2z_set! (hbound a h) (hinput a h)
  · exact hcont

/-- Applying the same pure function to pointwise-equal vectors preserves equality
after reversing them.  The functions are explicit so ordinary first-order
unification can infer them from an `LC.eval` goal. -/
theorem eval_reverse {f g : α → β} {left right : Vector α n}
    (h : ∀ i : Fin n, f left[i] = g right[i]) (i : Fin n) :
    f left.reverse[i] = g right.reverse[i] := by
  change f left.reverse[i.val] = g right.reverse[i.val]
  rw [Vector.getElem_reverse i.isLt, Vector.getElem_reverse i.isLt]
  exact h ⟨n - 1 - i, by omega⟩

/-- Evaluation congruence for the additive structure of `LC`. -/
theorem eval_add {F} [Semiring F] [DecidableEq F]
    {leftA rightA leftB rightB : LC F} {leftVal rightVal : Nat → F}
    (ha : LC.eval leftVal leftA = LC.eval rightVal rightA)
    (hb : LC.eval leftVal leftB = LC.eval rightVal rightB) :
    LC.eval leftVal (leftA + leftB) =
      LC.eval rightVal (rightA + rightB) := by
  simpa only [LC.eval_add] using congrArg₂ (· + ·) ha hb

/-- Evaluation congruence for subtraction of `LC`s. -/
theorem eval_sub {F} [Ring F] [DecidableEq F]
    {leftA rightA leftB rightB : LC F} {leftVal rightVal : Nat → F}
    (ha : LC.eval leftVal leftA = LC.eval rightVal rightA)
    (hb : LC.eval leftVal leftB = LC.eval rightVal rightB) :
    LC.eval leftVal (leftA - leftB) =
      LC.eval rightVal (rightA - rightB) := by
  simpa only [LC.eval_sub] using congrArg₂ (· - ·) ha hb

/-- Evaluation congruence for scalar multiplication of `LC`. -/
theorem eval_smul {F} [Semiring F] [DecidableEq F]
    (c : F) {left right : LC F} {leftVal rightVal : Nat → F}
    (h : LC.eval leftVal left = LC.eval rightVal right) :
    LC.eval leftVal (c • left) = LC.eval rightVal (c • right) := by
  simpa only [LC.eval_smul] using congrArg (c * ·) h

/-- Evaluation congruence for natural scalar multiplication of `LC`. -/
theorem eval_nsmul {F} [Semiring F] [DecidableEq F]
    (c : Nat) {left right : LC F} {leftVal rightVal : Nat → F}
    (h : LC.eval leftVal left = LC.eval rightVal right) :
    LC.eval leftVal (c • left) = LC.eval rightVal (c • right) := by
  simpa only [LC.eval_nsmul] using congrArg (c • ·) h

/-- Evaluation congruence for finite sums of `LC`s. -/
theorem eval_sum {F ι} [Semiring F] [DecidableEq F] [Fintype ι]
    {left right : ι → LC F} {leftVal rightVal : Nat → F}
    (h : ∀ i, LC.eval leftVal (left i) = LC.eval rightVal (right i)) :
    LC.eval leftVal (∑ i, left i) = LC.eval rightVal (∑ i, right i) := by
  simp only [LC.eval_sum]
  exact Finset.sum_congr rfl fun i _ => h i

/-- Specialize a pointwise vector relation at an index supplied by `[0:n)`. -/
theorem lceq_getElem_of_mem_range {F} [Semiring F] [DecidableEq F]
    {left right : Vector (LC F) n} {leftVal rightVal : Nat → F}
    {i : Nat} (hi : i ∈ ([:n] : Std.Legacy.Range))
    (h : ∀ j : Fin n,
      LCEq leftVal rightVal left[j] right[j]) :
    LCEq leftVal rightVal left[i] right[i] :=
  h ⟨i, hi.upper⟩

attribute [grind →] Membership.mem.upper

open Lean Elab Tactic

private structure RelView where
  left : Expr
  right : Expr

private def relView? (target : Expr) : Option RelView :=
  let target := target.consumeMData
  let fn := target.getAppFn
  let args := target.getAppArgs
  if fn.constName? == some ``Rel && args.size == 5 then
    some { left := args[3]!, right := args[4]! }
  else
    none

private def headConst? (e : Expr) : MetaM (Option Name) := do
  return (← instantiateMVars e).consumeMData.getAppFn.constName?

private def bindSource? (e : Expr) : MetaM (Option Expr) := do
  let e := (← instantiateMVars e).consumeMData
  if e.getAppFn.constName? == some ``Bind.bind then
    let args := e.getAppArgs
    if args.size >= 2 then return some args[args.size - 2]!
  return none

private partial def peelLambdasAux (e : Expr) (fuel : Nat) : MetaM Expr := do
  if fuel == 0 then return e
  let e ← instantiateMVars e
  match e.consumeMData with
  | .lam _ _ body _ => peelLambdasAux body (fuel - 1)
  | .letE _ _ value body _ => peelLambdasAux (body.instantiate1 value) (fuel - 1)
  | e => pure e

private def peelLambdas (e : Expr) : MetaM Expr :=
  peelLambdasAux e 16

/-- Recognize the canonical range-fold body handled by
`Rel.forIn'_range_f2z_add_nsmul_bind`.  This is deliberately only a
recognizer: it never unfolds an operation or tries unrelated rules. -/
private def isRangeF2ZFold (source : Expr) : MetaM Bool := do
  let source ← instantiateMVars source
  unless source.consumeMData.getAppFn.constName? == some ``ForIn'.forIn' do
    return false
  let args := source.consumeMData.getAppArgs
  unless args.size > 0 do return false
  let body ← peelLambdas args[args.size - 1]!
  let some first ← bindSource? body | return false
  return (← headConst? first) == some ``F2Z.f2z

private def rangeAccumulatorIsVector (source : Expr) : MetaM Bool := do
  let source ← instantiateMVars source
  let args := source.consumeMData.getAppArgs
  unless args.size ≥ 2 do return false
  let init := args[args.size - 2]!
  let type ← Lean.Meta.whnf (← Lean.Meta.inferType init)
  return type.getAppFn.constName? == some ``Vector

private def applyOn (goal : MVarId) (tactic : Syntax) : TacticM (List MVarId) := do
  setGoals [goal]
  evalTactic tactic
  getGoals

private def unfoldOn (goal : MVarId) (declName : Name) : TacticM MVarId :=
  Lean.Meta.unfoldTarget goal declName

private def isProtectedHead (name : Name) : Bool :=
  name == ``Bind.bind || name == ``Pure.pure || name == ``Vector.mapM ||
  name == ``F2Z.f2z || name == ``F2Z.hint || name == ``F2Z.assertR1C ||
  name == ``ForIn'.forIn'

private def isPrimitiveLCHead (name : Name) : Bool :=
  name == ``HAdd.hAdd || name == ``HSub.hSub || name == ``HSMul.hSMul ||
  name == ``Finset.sum || name == ``GetElem.getElem ||
  name == ``OfNat.ofNat || name == ``Zero.zero || name == ``Neg.neg ||
  name == ``LC.ofConst

mutual

private partial def dispatchWfGoal (goal : MVarId) (fuel : Nat) : TacticM Unit := goal.withContext do
  if fuel == 0 then
    throwError "wfgen exceeded its structural recursion limit"
  if ← goal.isAssigned then return
  let target ← instantiateMVars (← goal.getType)
  if let some rel := relView? target then
    -- `do` elaboration introduces administrative `let`/`have` bindings
    -- around the actual circuit constructor.  Strip them before dispatch;
    -- the structural rules still apply to the original goal by reduction.
    let left ← peelLambdas rel.left
    let leftHead := left.consumeMData.getAppFn.constName?
    match leftHead with
    | some ``Pure.pure =>
        let goals ← applyOn goal (← `(tactic| apply Rel.pure))
        for next in goals do dispatchWfGoal next (fuel - 1)
    | some ``Vector.mapM =>
        let goals ← applyOn goal (← `(tactic| apply Rel.mapM_f2z_rel))
        for next in goals do dispatchWfGoal next (fuel - 1)
    | some ``F2Z.f2z =>
        let goals ← applyOn goal (← `(tactic| apply Rel.f2z_rel))
        for next in goals do dispatchWfGoal next (fuel - 1)
    | some ``F2Z.hint =>
        let goals ← applyOn goal (← `(tactic| apply Rel.hint_pure))
        for next in goals do dispatchWfGoal next (fuel - 1)
    | some ``F2Z.assertR1C =>
        let goals ← applyOn goal (← `(tactic| apply Rel.assertR1C_rel))
        for next in goals do dispatchWfGoal next (fuel - 1)
    | some ``Bind.bind =>
        let some source ← bindSource? left |
          throwError "wfgen: malformed bind in relational goal"
        let sourceHead ← headConst? source
        if sourceHead == some ``F2Z.hint then
          -- The inductive rule already includes the continuation.  Going via
          -- `Rel.bind` would invent an unconstrained intermediate postcondition.
          let goals ← applyOn goal (← `(tactic| apply Rel.hint))
          for next in goals do dispatchWfGoal next (fuel - 1)
        else if sourceHead == some ``F2Z.f2z then
          let goals ← applyOn goal (← `(tactic| apply Rel.f2z))
          for next in goals do dispatchWfGoal next (fuel - 1)
        else if sourceHead == some ``F2Z.assertR1C then
          let goals ← applyOn goal (← `(tactic| apply Rel.assertR1C))
          for next in goals do dispatchWfGoal next (fuel - 1)
        else if ← isRangeF2ZFold source then
          let rule ← if ← rangeAccumulatorIsVector source then
            `(tactic| apply Rel.forIn'_range_f2z_set!_bind)
          else
            `(tactic| apply Rel.forIn'_range_f2z_add_nsmul_bind)
          let goals ← applyOn goal rule
          for next in goals do dispatchWfGoal next (fuel - 1)
        else if let some name := sourceHead then
          if !isProtectedHead name then
            -- Inline a user-defined circuit while it is still under its
            -- continuation.  Splitting first would require guessing an
            -- intermediate relation, which is precisely what the remainder
            -- of the program is meant to determine.
            let goals ← applyOn goal
              (← `(tactic| unfold $(mkIdent name); simp only [bind_assoc, pure_bind]))
            for next in goals do dispatchWfGoal next (fuel - 1)
          else
            let goals ← applyOn goal (← `(tactic| apply Rel.bind))
            for next in goals do dispatchWfGoal next (fuel - 1)
        else
          let goals ← applyOn goal (← `(tactic| apply Rel.bind))
          for next in goals do dispatchWfGoal next (fuel - 1)
    | some name =>
        if isProtectedHead name then
          throwError "wfgen has no structural rule for operation {name}"
        let next ← unfoldOn goal name
        dispatchWfGoal next (fuel - 1)
    | none =>
        throwError "wfgen cannot identify the circuit constructor in\n{left}"
  else
    dispatchPureGoal goal (fuel - 1)

private partial def dispatchPureGoal (goal : MVarId) (fuel : Nat) : TacticM Unit := goal.withContext do
  if fuel == 0 then
    throwError "wfgen exceeded its pure-goal recursion limit"
  if ← goal.isAssigned then return
  let targetBefore ← instantiateMVars (← goal.getType)
  if targetBefore.consumeMData.isForall then
    let introduced ← applyOn goal (← `(tactic| intro))
    for next in introduced do dispatchWfGoal next (fuel - 1)
    return
  let normalized ← applyOn goal
    (← `(tactic| try simp only [VectorRel, LCEq] at *))
  if normalized.isEmpty then return
  let goal := normalized.head!
  let target ← instantiateMVars (← goal.getType)
  if target.consumeMData.isForall then
    dispatchWfGoal goal (fuel - 1)
    return
  if target.consumeMData.getAppFn.constName? == some ``And then
    let goals ← applyOn goal (← `(tactic| constructor))
    for next in goals do dispatchWfGoal next (fuel - 1)
    return
  if target.consumeMData.getAppFn.constName? == some ``HintRel then
    let goals ← applyOn goal (← `(tactic| apply HintRel.of_eq))
    for next in goals do dispatchWfGoal next (fuel - 1)
    return
  if target.consumeMData.getAppFn.constName? == some ``Eq then
    let eqArgs := target.consumeMData.getAppArgs
    let lhs := eqArgs[eqArgs.size - 2]!
    if (← headConst? lhs) == some ``LC.eval then
      let evalArgs := (← instantiateMVars lhs).consumeMData.getAppArgs
      let lc := evalArgs[evalArgs.size - 1]!
      let lcHead ← headConst? lc
      if let some name := lcHead then
        if !isPrimitiveLCHead name then
          try
            let goals ← applyOn goal (← `(tactic| unfold $(mkIdent name)))
            for next in goals do dispatchWfGoal next (fuel - 1)
            return
          catch _ => pure ()
      let tactic? : Option Syntax ← match lcHead with
        | some ``HAdd.hAdd => some <$> `(tactic| apply eval_add)
        | some ``HSub.hSub => some <$> `(tactic| apply eval_sub)
        | some ``Finset.sum => some <$> `(tactic| apply eval_sum)
        | some ``HSMul.hSMul =>
            let smulArgs := (← instantiateMVars lc).consumeMData.getAppArgs
            let scalar := smulArgs[smulArgs.size - 2]!
            let scalarType ← Lean.Meta.whnf (← Lean.Meta.inferType scalar)
            if scalarType.isConstOf ``Nat then
              some <$> `(tactic| apply eval_nsmul)
            else
              some <$> `(tactic| apply eval_smul)
        | some ``GetElem.getElem =>
            let getArgs := (← instantiateMVars lc).consumeMData.getAppArgs
            let index := getArgs[getArgs.size - 2]!
            let indexType ← Lean.Meta.whnf (← Lean.Meta.inferType index)
            if indexType.isConstOf ``Nat then
              some <$> `(tactic| apply lceq_getElem_of_mem_range)
            else
              let collection := getArgs[getArgs.size - 3]!
              if (← headConst? collection) == some ``Vector.reverse then
                some <$> `(tactic| apply eval_reverse)
              else
                pure none
        | _ => pure none
      if let some tactic := tactic? then
        let goals ← applyOn goal tactic
        for next in goals do dispatchWfGoal next (fuel - 1)
        return
  setGoals [goal]
  evalTactic (← `(tactic| first | assumption | grind +splitImp))

end

private def evalWfgen (defs : Array Ident) : TacticM Unit := do
  evalTactic (← `(tactic| unfold GadgetSpec))
  evalTactic (← `(tactic| intros))
  for defName in defs do
    evalTactic (← `(tactic| unfold $defName))
  evalTactic (← `(tactic| simp only [bind_assoc, pure_bind]))
  let goals ← getGoals
  for goal in goals do dispatchWfGoal goal 256
  setGoals []

/-- Prove a `GadgetSpec` by following the syntax of the two circuit terms.
Definitions supplied in brackets are unfolded before structural dispatch, for
example `wfgen [myGadget]`. -/
elab "wfgen" : tactic => evalWfgen #[]

elab "wfgen" " [" defs:ident,* "]" : tactic => evalWfgen defs

end Freigen.F2Z.WF
