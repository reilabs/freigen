import Freigen.F2Z.Defs
import Freigen.F2Z.Semantics
import Freigen.F2Z.Nondet
import Freigen.F2Z.Correctness.WF
import Std.Tactic.Do

namespace Std.Do

universe u v

/-- Invariant for `Vector.ofFnM`: after `i` iterations, `xs` contains exactly
the prefix constructed so far. -/
@[spec_invariant_type]
def VectorOfFnM.Invariant (α : Type u) (n : Nat) (ps : PostShape.{u}) :=
  (i : Nat) → i ≤ n → Vector α i → Assertion ps

/-- Generic MVCGen rule for effectful vector construction. It exposes one
uniform indexed step obligation and keeps exceptional postconditions fixed
throughout the construction. -/
@[spec]
theorem Spec.vector_ofFnM
    {α : Type u} {m : Type u → Type v} {ps : PostShape.{u}}
    [Monad m] [WPMonad m ps]
    {n : Nat} {f : Fin n → m α} {E : ExceptConds ps}
    (inv : VectorOfFnM.Invariant α n ps)
    (step : ∀ i (hi : i < n) (xs : Vector α i),
      Triple (f ⟨i, hi⟩)
        (inv i (Nat.le_of_lt hi) xs)
        (fun x => inv (i + 1) (Nat.succ_le_of_lt hi) (xs.push x), E)) :
    Triple (Vector.ofFnM f)
      (inv 0 (Nat.zero_le n) #v[])
      (fun xs => inv n (Nat.le_refl n) xs, E) := by
  induction n with
  | zero =>
      rw [Vector.ofFnM_zero]
      exact Triple.pure _ (SPred.entails.refl _)
  | succ n ih =>
      rw [Vector.ofFnM_succ]
      apply Triple.bind (Q := fun xs => inv n (Nat.le_succ n) xs)
      case hx =>
        apply ih (inv := fun i hi xs => inv i (hi.trans (Nat.le_succ n)) xs)
        intro i hi xs
        exact step i (Nat.lt_trans hi (Nat.lt_succ_self n)) xs
      case hf =>
        intro xs
        apply Triple.bind
          (Q := fun x => inv (n + 1) (Nat.le_refl _) (xs.push x))
        case hx => exact step n (Nat.lt_succ_self n) xs
        case hf =>
          intro x
          exact Triple.pure _ (SPred.entails.refl _)

end Std.Do

namespace Freigen.F2Z.Sound

open Std.Do
open scoped Std.Do

local instance : Context := lcContext

abbrev Shape : PostShape :=
  .arg WF.Valuation .pure

abbrev RunnerM : Eff.Scope → Type → Type
| .constraint => Nondet
| .hint       => Semantics.CSBuilder.NoMonad

instance : (e: Eff.Scope) → Monad (RunnerM e)
| .constraint => inferInstance
| .hint       => inferInstance

instance : (e: Eff.Scope) → LawfulMonad (RunnerM e)
| .constraint => inferInstance
| .hint       => inferInstance

def handler (valuation : WF.Valuation) :
    Freigen.Eff.Handler (Eff lcContext) RunnerM :=
  fun {γ} e _ => match γ, e with
    | .constraint, .assertR1C a b c =>
        if a.eval valuation.int * b.eval valuation.int = c.eval valuation.int then
          pure ()
        else
          Nondet.abort
    | .constraint, .f2z a =>
        Nondet.chooseWhere fun x : LC ℤ =>
          (a.eval valuation.bool).toInt = x.eval valuation.int
    | .constraint, .hint _ _ n => Nondet.choose (Vector (LC Bool) n)
    | .hint, .fail _ _ => ()

def interp (valuation : WF.Valuation) {α : Type}
    (x : Circuit α) : Nondet α :=
  Free.interp (M := RunnerM) (handler valuation) x

variable {valuation : WF.Valuation}

@[simp, spec]
theorem interp_bind {x : Circuit α} {f : α → Circuit β} :
    interp valuation (do let a ← x; f a) =
      (do let a ← interp valuation x; interp valuation (f a)) := by
  simp [interp, Free.interp_bind]

@[simp, spec]
theorem interp_pure (a : α) :
    interp valuation (pure a : Circuit α) = pure a := by
  rfl

/-- MVCGen-facing form of `interp_bind`. Unlike an equational simp lemma,
this rule exposes the native `Nondet` bind before MVCGen inspects its head. -/
@[spec]
theorem interp_bind_spec {x : Circuit α} {f : α → Circuit β}
    {P : SPred []} {Q : PostCond β .pure}
    (h : Triple
      (do
        let a ← interp valuation x
        interp valuation (f a))
      P Q) :
    Triple (interp valuation (x >>= f)) P Q := by
  rwa [interp_bind]

/-- MVCGen-facing form of `interp_pure`. -/
@[spec]
theorem interp_pure_spec (a : α) (Q : PostCond α .pure) :
    Triple (interp valuation (pure a : Circuit α)) (Q.1 a) Q := by
  rw [interp_pure]
  exact Std.Do.Spec.pure

/-- Interpretation commutes with `forIn'` over lists. -/
theorem interp_forIn'_list (xs : List α) (init : β)
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

/-- Interpretation commutes with `forIn'` over legacy ranges, the collection
used by `for h : i in [start:stop]`. -/
theorem interp_forIn'_range (xs : Std.Legacy.Range) (init : β)
    (f : (a : Nat) → a ∈ xs → β → Circuit (ForInStep β)) :
    interp valuation (forIn' xs init f) =
      forIn' xs init fun a h b => interp valuation (f a h b) := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range',
    Std.Legacy.Range.forIn'_eq_forIn'_range']
  simpa using interp_forIn'_list xs.toList init
    (fun a h b => f a (Std.Legacy.Range.mem_of_mem_range' h) b)

/-- Expose an interpreted range loop as a native `Nondet` range loop so that
MVCGen can apply its standard loop rule and request an invariant. -/
@[spec]
theorem interp_forIn'_range_spec
    {xs : Std.Legacy.Range} {init : β}
    {f : (a : Nat) → a ∈ xs → β → Circuit (ForInStep β)}
    {P : SPred []} {Q : PostCond β .pure}
    (h : Triple
      (forIn' xs init fun a h b => interp valuation (f a h b)) P Q) :
    Triple (interp valuation (forIn' xs init f)) P Q := by
  rwa [interp_forIn'_range]

@[simp, spec]
theorem interp_map (g : α → β) (x : Circuit α) :
    interp valuation (g <$> x) = g <$> interp valuation x := by
  rw [← bind_pure_comp, interp_bind]
  simp only [interp_pure, bind_pure_comp]

private theorem interp_list_mapM (xs : List α) (f : α → Circuit β) :
    interp valuation (xs.mapM f) =
      xs.mapM (fun x => interp valuation (f x)) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, interp_bind]

private theorem interp_array_mapM (xs : Array α) (f : α → Circuit β) :
    interp valuation (xs.mapM f) =
      xs.mapM (fun x => interp valuation (f x)) := by
  simp only [Array.mapM_eq_mapM_toList, interp_map, interp_list_mapM]

@[simp, spec]
theorem interp_mapM (xs : Vector α n) (f : α → Circuit β) :
    interp valuation (xs.mapM f) =
      xs.mapM (fun x => interp valuation (f x)) := by
  apply Vector.map_toArray_inj.mp
  rw [← interp_map, Vector.toArray_mapM, interp_array_mapM, Vector.toArray_mapM]

/-- Interpretation commutes with constructing a vector effectfully by index. -/
@[simp, spec]
theorem interp_ofFnM (f : Fin n → Circuit α) :
    interp valuation (Vector.ofFnM f) =
      Vector.ofFnM (fun i => interp valuation (f i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Vector.ofFnM_succ, interp_bind, interp_pure, ih]

/- An assertion adds its equation as an assumption on the surviving path.
If the equation is false, the sound semantics aborts that path. -/
@[spec]
theorem assertR1C (a b c : LC ℤ) (Q : PostCond Unit .pure) :
    Triple (interp valuation (F2Z.assertR1C a b c))
      spred(⌜valuation.int a * valuation.int b =
        valuation.int c⌝ → Q.1 ()) Q := by
  rw [Triple.iff]
  simp only [SPred.entails_nil, wp, interp, F2Z.assertR1C]
  rw [Free.interp_op]
  simp only [PredTrans.apply, handler, SPred.imp_nil,
    SPred.down_pure_nil]
  split
  · rename_i hconstraint
    intro hpre
    have hconstraint' : valuation.int a * valuation.int b =
        valuation.int c := by
      simpa only [← LC.Valuation.apply_eq_eval] using hconstraint
    have hpost := hpre hconstraint'
    change (Q.1 ()).down
    exact hpost
  · intro _
    exact True.intro

@[spec]
theorem f2z {a}:
    ⦃⌜True⌝⦄ interp valuation (f2z a)
    ⦃⇓ r =>
      ⌜(valuation.bool a).toInt = valuation.int r⌝⦄ := by
  rw [Triple.iff]
  simp only [SPred.entails_nil]
  simp only [SPred.down_pure_nil, wp, interp, F2Z.f2z]
  rw [Free.interp_op]
  simp only [PredTrans.apply, handler, Nondet.chooseWhere, SPred.imp_nil, SPred.down_pure_nil,
    SPred.forall_nil]
  intro _ r h
  simpa only [← LC.Valuation.apply_eq_eval] using h

/-- Soundness treats a hint as universal nondeterminism: the postcondition
must hold for every vector the constraint-system semantics may return. -/
@[spec]
theorem hint {n : Nat} {argTps : List Eff.WitnessSide}
    (args : HList (Eff.WitnessSide.denoteW lcContext) argTps)
    (body : HList Eff.WitnessSide.denoteF argTps → Hint (Vector Bool n))
    (Q : PostCond (Vector (LC Bool) n) .pure) :
    Triple (interp valuation (F2Z.hint args body))
      spred(∀ result, Q.1 result) Q := by
  unfold interp F2Z.hint
  rw [Free.interp_op]
  simpa [handler, Nondet.choose] using
    Nondet.chooseWhere_spec
      (fun _ : Vector (LC Bool) n => True) Q

/-- The common valuation induced by a constraint system and a Boolean witness. -/
def csValuation (cs : Semantics.CS)
    (wit : Nat → Bool) : WF.Valuation where
  bool := LC.valuation wit
  int := LC.valuation (cs.intWitness wit)

private theorem satisfies_of_r1cs_prefix {cs : Semantics.CS} {wit : Nat → Bool}
    {pre : Array (Semantics.R1C ℤ)} {r1c : Semantics.R1C ℤ}
    (hprefix : (pre.push r1c).toList <+: cs.r1cs.toList)
    (hsat : cs.satisfies wit) :
    r1c.satisfies (cs.intWitness wit) := by
  have hmemList : r1c ∈ cs.r1cs.toList :=
    hprefix.mem (by simp)
  have hmem : r1c ∈ cs.r1cs := Array.mem_def.mpr hmemList
  change ∀ r ∈ cs.r1cs, r.satisfies (cs.intWitness wit) at hsat
  exact hsat r1c hmem

private theorem intWitness_eq_of_m_prefix {cs : Semantics.CS} {wit : Nat → Bool}
    {pre : Array (LC Bool)} {a : LC Bool}
    (hprefix : (pre.push a).toList <+: cs.m.toList) :
    cs.intWitness wit pre.size = (a.eval wit).toInt := by
  have hi : pre.size < (pre.push a).toList.length := by simp
  have hget := hprefix.getElem hi
  have hsize : pre.size < cs.m.size := by
    simpa using lt_of_lt_of_le hi hprefix.length_le
  have hget' : cs.m[pre.size]'hsize = a := by
    calc
      cs.m[pre.size] = cs.m.toList[pre.size] := rfl
      _ = (pre.push a).toList[pre.size] := hget.symm
      _ = a := by simp
  unfold Semantics.CS.intWitness
  rw [getElem!_pos _ _ (by simpa using hsize), Array.getElem_map, hget']
  rfl

private theorem interp_runAt {a : Circuit α} {s sf : Semantics.CSBuilder}
    {wit : Nat → Bool} {Q : PostCond α .pure}
    (hext : Semantics.CSBuilder.Extends
      (StateT.run (Semantics.CSBuilder.runAt a) s).2 sf)
    (hsat : sf.result.satisfies wit)
    (hwp : ((interp (csValuation sf.result wit) a).apply Q).down) :
    (Q.1 (StateT.run (Semantics.CSBuilder.runAt a) s).1).down := by
  let motive := fun (γ : Eff.Scope) (α : Type)
      (a : Free (Eff lcContext) γ α) =>
    match γ with
    | .constraint => ∀ (s sf : Semantics.CSBuilder) (wit : Nat → Bool)
        (Q : PostCond α .pure),
        Semantics.CSBuilder.Extends
          (StateT.run (Semantics.CSBuilder.runAt a) s).2 sf →
        sf.result.satisfies wit →
        ((interp (csValuation sf.result wit) a).apply Q).down →
        (Q.1 (StateT.run (Semantics.CSBuilder.runAt a) s).1).down
    | .hint => True
  refine (Free.recOn (motive := motive) a ?_ ?_) s sf wit Q hext hsat hwp
  · intro γ α value
    cases γ with
    | hint => trivial
    | constraint =>
      intro s sf wit Q hext hsat hwp
      change (Q.1 value).down
      change (Q.1 value).down at hwp
      exact hwp
  · intro γ α e blocks k _ ihk
    cases γ with
    | hint => trivial
    | constraint =>
      intro s sf wit Q hext hsat hwp
      cases e with
      | assertR1C a b c =>
          simp [Semantics.CSBuilder.runAt, Semantics.CSBuilder.handler,
            interp, handler] at hext hwp ⊢
          let s₁ : Semantics.CSBuilder := {
            s with result := {
              s.result with r1cs := s.result.r1cs.push { a := a, b := b, c := c }
            }
          }
          have hs₁sf : Semantics.CSBuilder.Extends s₁ sf :=
            (Semantics.CSBuilder.run'_extends (a := k ()) (s := s₁)).trans hext
          have hr1c := satisfies_of_r1cs_prefix hs₁sf.1 hsat
          change a.eval (sf.result.intWitness wit) * b.eval (sf.result.intWitness wit) =
            c.eval (sf.result.intWitness wit) at hr1c
          have hr1c' :
              (LC.valuation (sf.result.intWitness wit)) a *
                  (LC.valuation (sf.result.intWitness wit)) b =
                (LC.valuation (sf.result.intWitness wit)) c := by
            rw [LC.Valuation.apply_eq_eval, LC.Valuation.apply_eq_eval,
              LC.Valuation.apply_eq_eval]
            exact hr1c
          have hwp' : ((interp (csValuation sf.result wit) (k ())).apply Q).down := by
            simpa [interp, handler, csValuation, hr1c'] using hwp
          exact ihk () s₁ sf wit Q hext hsat hwp'
      | f2z a =>
          simp [Semantics.CSBuilder.runAt, Semantics.CSBuilder.handler,
            interp, handler] at hext hwp ⊢
          let out : LC ℤ := {s.result.m.size}
          let s₁ : Semantics.CSBuilder := {
            s with result := { s.result with m := s.result.m.push a }
          }
          have hs₁sf : Semantics.CSBuilder.Extends s₁ sf :=
            (Semantics.CSBuilder.run'_extends (a := k out) (s := s₁)).trans hext
          have hidx := intWitness_eq_of_m_prefix hs₁sf.2 (wit := wit)
          have hrel : (a.eval wit).toInt = out.eval (sf.result.intWitness wit) := by
            simp [out, hidx]
          change ∀ x : LC ℤ,
            (a.eval wit).toInt = x.eval (sf.result.intWitness wit) →
              ((interp (csValuation sf.result wit) (k x)).apply Q).down at hwp
          exact ihk out s₁ sf wit Q hext hsat (hwp out hrel)
      | hint argTps args n =>
          simp [Semantics.CSBuilder.runAt, Semantics.CSBuilder.handler,
            interp, handler] at hext hwp ⊢
          let out : Vector (LC Bool) n :=
            Vector.ofFn fun i => {s.nextWit + i.val}
          let s₁ : Semantics.CSBuilder := {
            s with nextWit := s.nextWit + n
          }
          change ∀ x : Vector (LC Bool) n, True →
            ((interp (csValuation sf.result wit) (k x)).apply Q).down at hwp
          exact ihk out s₁ sf wit Q hext hsat (hwp out True.intro)

/--
A soundness proof in the nondeterministic semantics transfers to constraint
generation for a concrete external-input selection and satisfying assignment.
-/
theorem adequate {circ : Vector (LC Bool) n → Circuit α}
    {inputs : Vector Bool n} {wit : Nat → Bool}
    {P : Vector Bool n → α → Prop} :
    ⦃ ⌜∀ i : Fin n, wit i.val = inputs[i]⌝ ⦄
      interp
        (csValuation (Semantics.CSBuilder.runWithInputs circ).2 wit)
        (circ (Vector.ofFn fun i => ({i.val} : LC Bool)))
    ⦃ ⇓ value => ⌜P inputs value⌝ ⦄ →
    (∀ i : Fin n, wit i.val = inputs[i]) →
    (Semantics.CSBuilder.runWithInputs circ).2.satisfies wit →
    P inputs (Semantics.CSBuilder.runWithInputs circ).1 := by
  intro htriple hinputs hsat
  let inputWires : Vector (LC Bool) n :=
    Vector.ofFn fun i => ({i.val} : LC Bool)
  let initial : Semantics.CSBuilder :=
    { result := { r1cs := #[], m := #[] }, nextWit := n }
  simp only [Semantics.CSBuilder.runWithInputs,
    Semantics.CSBuilder.run, Semantics.CSBuilder.run'] at htriple hsat ⊢
  generalize hrun :
      StateT.run (Semantics.CSBuilder.runAt (circ inputWires)) initial =
        result at htriple hsat ⊢
  rcases result with ⟨value, sf⟩
  simp only at htriple hsat ⊢
  rw [Triple.iff] at htriple
  simp only [SPred.entails_nil, SPred.down_pure_nil, wp] at htriple
  have hwp := htriple hinputs
  have h := interp_runAt
    (a := circ inputWires)
    (s := initial)
    (sf := sf)
    (wit := wit)
    (Q := (⇓ value => ⌜P inputs value⌝))
    (by simpa [hrun] using Semantics.CSBuilder.Extends.refl sf)
    hsat
    hwp
  simpa [hrun] using h

end Sound
