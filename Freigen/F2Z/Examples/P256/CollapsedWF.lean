import Freigen.F2Z.Examples.P256.WF

/-!
# Well-formedness for open-once P-256 addition

The optimized selectors witness one representative and constrain it with
gated integer R1Cs.  These proofs keep the valuation-parametric quotient
correctness boundary used by the public ECDSA theorem.
-/

namespace Freigen.F2Z.Examples.P256.AffineSlope

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open Std.Do
open scoped Std.Do
open Modular

theorem selectGated3Rep_wf_aux (width outBound : Nat)
    (description : String) :
    WF.GadgetSpec
      (fun lv rv
          (left right : LC ℤ × LC ℤ × LC ℤ × Rep × Rep × Rep) =>
        WF.LCEq lv.int rv.int left.1 right.1 ∧
        WF.LCEq lv.int rv.int left.2.1 right.2.1 ∧
        WF.LCEq lv.int rv.int left.2.2.1 right.2.2.1 ∧
        left.2.2.2.1.WFRel lv rv right.2.2.2.1 ∧
        left.2.2.2.2.1.WFRel lv rv right.2.2.2.2.1 ∧
        left.2.2.2.2.2.WFRel lv rv right.2.2.2.2.2)
      (fun input => selectGated3Rep width outBound description
        input.1 input.2.1 input.2.2.1 input.2.2.2.1
        input.2.2.2.2.1 input.2.2.2.2.2)
      Modular.Lazy.Rep.WFRel := by
  wfgen' using [U.fromWord_wf_rel]
    unfold [selectGated3Rep, Modular.Lazy.Rep.WFRel]
  case vc1 =>
    rename_i h
    change WF.LCEq leftVal.bool rightVal.bool outL[i] outR[i]
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt
  all_goals simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

theorem selectGated4Rep_wf_aux (width outBound : Nat)
    (description : String) :
    WF.GadgetSpec
      (fun lv rv
          (left right :
            LC ℤ × LC ℤ × LC ℤ × LC ℤ × Rep × Rep × Rep × Rep) =>
        WF.LCEq lv.int rv.int left.1 right.1 ∧
        WF.LCEq lv.int rv.int left.2.1 right.2.1 ∧
        WF.LCEq lv.int rv.int left.2.2.1 right.2.2.1 ∧
        WF.LCEq lv.int rv.int left.2.2.2.1 right.2.2.2.1 ∧
        left.2.2.2.2.1.WFRel lv rv right.2.2.2.2.1 ∧
        left.2.2.2.2.2.1.WFRel lv rv right.2.2.2.2.2.1 ∧
        left.2.2.2.2.2.2.1.WFRel lv rv right.2.2.2.2.2.2.1 ∧
        left.2.2.2.2.2.2.2.WFRel lv rv right.2.2.2.2.2.2.2)
      (fun input => selectGated4Rep width outBound description
        input.1 input.2.1 input.2.2.1 input.2.2.2.1
        input.2.2.2.2.1 input.2.2.2.2.2.1
        input.2.2.2.2.2.2.1 input.2.2.2.2.2.2.2)
      Modular.Lazy.Rep.WFRel := by
  wfgen' using [U.fromWord_wf_rel]
    unfold [selectGated4Rep, Modular.Lazy.Rep.WFRel]
  case vc1 =>
    rename_i h
    change WF.LCEq leftVal.bool rightVal.bool outL[i] outR[i]
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt
  all_goals simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

def selectCollapsedNumerator_wf_aux :=
  selectGated3Rep_wf_aux 262 66 "collapsed numerator"

def selectCollapsedDenominator_wf_aux :=
  selectGated3Rep_wf_aux 262 66 "collapsed denominator"

def selectCollapsedNumeratorTight_wf_aux :=
  selectGated3Rep_wf_aux 259 5 "collapsed numerator"

def selectCollapsedDenominatorTight_wf_aux :=
  selectGated3Rep_wf_aux 258 3 "collapsed denominator"

theorem selectCollapsedNumeratorCall_wf_aux :
    WF.GadgetSpec
      (fun lv rv
          (left right : Point × Point × AddControl × Rep) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.1.WFRel lv rv right.2.2.1 ∧
        left.2.2.2.WFRel lv rv right.2.2.2)
      (fun input => selectCollapsedNumerator
        input.1 input.2.1 input.2.2.1 input.2.2.2)
      Modular.Lazy.Rep.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold selectCollapsedNumerator
  apply WF.GadgetSpec.direct_rule
    (left := (left.2.2.1.doubleCase,
      left.2.2.1.active - left.2.2.1.doubleCase,
      LC.ofConst 1 - left.2.2.1.active,
      sub (scale 3 left.2.2.2) (ofElem three),
      sub left.2.1.Y left.1.Y, ofElem zero))
    (right := (right.2.2.1.doubleCase,
      right.2.2.1.active - right.2.2.1.doubleCase,
      LC.ofConst 1 - right.2.2.1.active,
      sub (scale 3 right.2.2.2) (ofElem three),
      sub right.2.1.Y right.1.Y, ofElem zero))
    selectCollapsedNumerator_wf_aux
  intro lv rv h
  simp_all [Point.WFRel, AddControl.WFRel, sub, scale, ofElem,
    Modular.Lazy.sub, Modular.Lazy.scale, Modular.Lazy.ofElem,
    Modular.Lazy.Rep.WFRel, WF.LCEq, LC.eval_add, LC.eval_sub,
    LC.eval_nsmul, LC.eval_ofConst, three, zero, fpConst,
    Modular.ofNat, U.intVal]

theorem selectCollapsedDenominatorCall_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point × AddControl) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => selectCollapsedDenominator
        input.1 input.2.1 input.2.2)
      Modular.Lazy.Rep.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold selectCollapsedDenominator
  apply WF.GadgetSpec.direct_rule
    (left := (left.2.2.doubleCase,
      left.2.2.active - left.2.2.doubleCase,
      LC.ofConst 1 - left.2.2.active,
      scale 2 left.1.Y, sub left.2.1.X left.1.X, ofElem one))
    (right := (right.2.2.doubleCase,
      right.2.2.active - right.2.2.doubleCase,
      LC.ofConst 1 - right.2.2.active,
      scale 2 right.1.Y, sub right.2.1.X right.1.X, ofElem one))
    selectCollapsedDenominator_wf_aux
  intro lv rv h
  simp_all [Point.WFRel, AddControl.WFRel, sub, scale, ofElem,
    Modular.Lazy.sub, Modular.Lazy.scale, Modular.Lazy.ofElem,
    Modular.Lazy.Rep.WFRel, WF.LCEq, LC.eval_add, LC.eval_sub,
    LC.eval_nsmul, LC.eval_ofConst, one, fpConst, Modular.ofNat,
    U.intVal]

theorem selectCollapsedNumeratorTightCall_wf_aux :
    WF.GadgetSpec
      (fun lv rv
          (left right : Point × Point × AddControl × Rep) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.1.WFRel lv rv right.2.2.1 ∧
        left.2.2.2.WFRel lv rv right.2.2.2)
      (fun input => selectCollapsedNumeratorTight
        input.1 input.2.1 input.2.2.1 input.2.2.2)
      Modular.Lazy.Rep.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold selectCollapsedNumeratorTight
  apply WF.GadgetSpec.direct_rule
    (left := (left.2.2.1.doubleCase,
      left.2.2.1.active - left.2.2.1.doubleCase,
      LC.ofConst 1 - left.2.2.1.active,
      sub (scale 3 left.2.2.2) (ofElem three),
      sub left.2.1.Y left.1.Y, ofElem zero))
    (right := (right.2.2.1.doubleCase,
      right.2.2.1.active - right.2.2.1.doubleCase,
      LC.ofConst 1 - right.2.2.1.active,
      sub (scale 3 right.2.2.2) (ofElem three),
      sub right.2.1.Y right.1.Y, ofElem zero))
    selectCollapsedNumeratorTight_wf_aux
  intro lv rv h
  simp_all [Point.WFRel, AddControl.WFRel, sub, scale, ofElem,
    Modular.Lazy.sub, Modular.Lazy.scale, Modular.Lazy.ofElem,
    Modular.Lazy.Rep.WFRel, WF.LCEq, LC.eval_add, LC.eval_sub,
    LC.eval_nsmul, LC.eval_ofConst, three, zero, fpConst,
    Modular.ofNat, U.intVal]

theorem selectCollapsedDenominatorTightCall_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point × AddControl) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => selectCollapsedDenominatorTight
        input.1 input.2.1 input.2.2)
      Modular.Lazy.Rep.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold selectCollapsedDenominatorTight
  apply WF.GadgetSpec.direct_rule
    (left := (left.2.2.doubleCase,
      left.2.2.active - left.2.2.doubleCase,
      LC.ofConst 1 - left.2.2.active,
      scale 2 left.1.Y, sub left.2.1.X left.1.X, ofElem one))
    (right := (right.2.2.doubleCase,
      right.2.2.active - right.2.2.doubleCase,
      LC.ofConst 1 - right.2.2.active,
      scale 2 right.1.Y, sub right.2.1.X right.1.X, ofElem one))
    selectCollapsedDenominatorTight_wf_aux
  intro lv rv h
  simp_all [Point.WFRel, AddControl.WFRel, sub, scale, ofElem,
    Modular.Lazy.sub, Modular.Lazy.scale, Modular.Lazy.ofElem,
    Modular.Lazy.Rep.WFRel, WF.LCEq, LC.eval_add, LC.eval_sub,
    LC.eval_nsmul, LC.eval_ofConst, one, fpConst, Modular.ofNat,
    U.intVal]

theorem finishSelectSlopeOperandsCollapsed_wf_aux :
    WF.GadgetSpec
      (fun lv rv
          (left right : Point × Point × AddControl × Rep) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.1.WFRel lv rv right.2.2.1 ∧
        left.2.2.2.WFRel lv rv right.2.2.2)
      (fun input => finishSelectSlopeOperandsCollapsed
        input.1 input.2.1 input.2.2.1 input.2.2.2)
      SlopeOperands.WFRel := by
  wfgen' using [selectCollapsedNumeratorCall_wf_aux,
    selectCollapsedDenominatorCall_wf_aux]
    unfold [finishSelectSlopeOperandsCollapsed, SlopeOperands.WFRel]

theorem finishSelectSlopeOperandsCollapsedTight_wf_aux :
    WF.GadgetSpec
      (fun lv rv
          (left right : Point × Point × AddControl × Rep) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.1.WFRel lv rv right.2.2.1 ∧
        left.2.2.2.WFRel lv rv right.2.2.2)
      (fun input => finishSelectSlopeOperandsCollapsedTight
        input.1 input.2.1 input.2.2.1 input.2.2.2)
      SlopeOperands.WFRel := by
  wfgen' using [selectCollapsedNumeratorTightCall_wf_aux,
    selectCollapsedDenominatorTightCall_wf_aux]
    unfold [finishSelectSlopeOperandsCollapsedTight, SlopeOperands.WFRel]

theorem selectSlopeOperandsCollapsed_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point × AddControl) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => selectSlopeOperandsCollapsed
        input.1 input.2.1 input.2.2)
      SlopeOperands.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold selectSlopeOperandsCollapsed
  apply WF.GadgetSpec.bind_rule
    (left := (left.1.X, left.1.X))
    (right := (right.1.X, right.1.X))
    (Modular.Lazy.mul_wf base)
  · intro lv rv h
    exact ⟨h.1.1, h.1.1⟩
  · intro B x2L x2R hx2
    apply WF.GadgetSpec.direct_rule
      (left := (left.1, left.2.1, left.2.2, x2L))
      (right := (right.1, right.2.1, right.2.2, x2R))
      finishSelectSlopeOperandsCollapsed_wf_aux
    intro lv rv hB
    have hh := hx2 lv rv hB
    exact ⟨hh.1.1, hh.1.2.1, hh.1.2.2, hh.2⟩

theorem selectSlopeOperandsCollapsedTight_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point × AddControl) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => selectSlopeOperandsCollapsedTight
        input.1 input.2.1 input.2.2)
      SlopeOperands.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold selectSlopeOperandsCollapsedTight
  apply WF.GadgetSpec.bind_rule
    (left := left.1) (right := right.1) doubleSquare_wf_aux
  · intro lv rv h
    exact h.1
  · intro B x2L x2R hx2
    apply WF.GadgetSpec.direct_rule
      (left := (left.1, left.2.1, left.2.2, x2L))
      (right := (right.1, right.2.1, right.2.2, x2R))
      finishSelectSlopeOperandsCollapsedTight_wf_aux
    intro lv rv hB
    have hh := hx2 lv rv hB
    exact ⟨hh.1.1, hh.1.2.1, hh.1.2.2, hh.2⟩

private def CollapsedBitsWFRel (n : Nat) (lv rv : WF.Valuation)
    (left right : Vector (LC Bool) n) : Prop :=
  ∀ i : Fin n, WF.LCEq lv.bool rv.bool left[i] right[i]

private theorem collapsedDecodeSlice_wf_aux
    (total start width : Nat) (hfit : start + width ≤ total) :
    WF.GadgetSpec (CollapsedBitsWFRel total)
      (fun bits => U.fromWord {
        bitsLE := Vector.ofFn (n := width) fun i =>
          bits[start + i.val]'(by omega) }) U.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  apply WF.GadgetSpec.direct_rule
    (left := ({ bitsLE := Vector.ofFn (n := width) fun i =>
      left[start + i.val]'(by omega) } : Word width))
    (right := ({ bitsLE := Vector.ofFn (n := width) fun i =>
      right[start + i.val]'(by omega) } : Word width))
    U.fromWord_wf_rel
  intro lv rv h i
  simpa only [instGetElemWordFinLCBoolTrue, Vector.getElem_ofFn,
    Fin.getElem_fin] using h ⟨start + i.val, by omega⟩

theorem collapsedSlopeHint_wf_aux :
    WF.GadgetSpec SlopeOperands.WFRel collapsedSlopeHint
      (CollapsedBitsWFRel 514) := by
  unfold WF.GadgetSpec
  intro left right
  unfold collapsedSlopeHint
  apply WF.Rel.hint_pure
  · intro lv rv h
    unfold WF.ArgsEq
    simp only [WF.evalArgs]
    congr 1
    · exact h.2.2
    · congr 1
      exact h.1.2
  · intro lv rv h
    have heq :
        WF.evalArgs lv h![left.denominator.intVal, left.numerator.intVal] =
        WF.evalArgs rv h![right.denominator.intVal,
          right.numerator.intVal] := by
      simp only [WF.evalArgs]
      congr 1
      · exact h.2.2
      · congr 1
        exact h.1.2
    rw [heq, h.1.1]
    exact WF.HintRel.refl _
  · intro bitsL bitsR lv rv h i
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt

theorem collapsedSlopeDecodeValue_wf_aux :
    WF.GadgetSpec (CollapsedBitsWFRel 514)
      collapsedSlopeDecodeValue U.WFRel := by
  unfold collapsedSlopeDecodeValue
  simpa using collapsedDecodeSlice_wf_aux 514 0 256 (by omega)

theorem collapsedSlopeDecodeQ_wf_aux :
    WF.GadgetSpec (CollapsedBitsWFRel 514)
      collapsedSlopeDecodeQ U.WFRel := by
  unfold collapsedSlopeDecodeQ
  simpa only [Nat.add_comm] using
    collapsedDecodeSlice_wf_aux 514 256 258 (by omega)

theorem collapsedSlopeCheck_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : SlopeOperands × U 256 × U 258) =>
        left.1.WFRel lv rv right.1 ∧
        U.WFRel lv rv left.2.1 right.2.1 ∧
        U.WFRel lv rv left.2.2 right.2.2)
      (fun input => collapsedSlopeCheck input.1 input.2.1 input.2.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold collapsedSlopeCheck
  apply WF.Rel.assertR1C_pure
  · intro lv rv h
    exact h.2.1.1
  · intro lv rv h
    exact h.1.2.2
  · intro lv rv h
    unfold WF.LCEq
    simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul, LC.eval_ofConst]
    rw [h.1.1.2, h.2.2.1, h.1.1.1]
  · intro _ _ _
    trivial

theorem collapsedSlope_wf_aux :
    WF.GadgetSpec SlopeOperands.WFRel collapsedSlope
      Modular.Lazy.Rep.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold collapsedSlope
  apply WF.GadgetSpec.bind_rule_direct
    (left := left) (right := right) collapsedSlopeHint_wf_aux
  · intro lv rv h
    exact h
  · intro bitsL bitsR
    apply WF.GadgetSpec.bind_rule_direct
      (left := bitsL) (right := bitsR) collapsedSlopeDecodeValue_wf_aux
    · intro lv rv h
      exact h.2
    · intro valueL valueR
      apply WF.GadgetSpec.bind_rule_direct
        (left := bitsL) (right := bitsR) collapsedSlopeDecodeQ_wf_aux
      · intro lv rv h
        exact h.1.2
      · intro qL qR
        apply WF.GadgetSpec.bind_rule_direct
          (left := (left, valueL, qL))
          (right := (right, valueR, qR)) collapsedSlopeCheck_wf_aux
        · intro lv rv h
          exact ⟨h.1.1.1, h.1.2, h.2⟩
        · intro _ _
          apply WF.Rel.pure
          intro lv rv h
          exact ⟨rfl, h.1.1.2.1⟩

private def CollapsedRepPairWFRel (lv rv : WF.Valuation)
    (left right : Rep × Rep) : Prop :=
  left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2

theorem collapsedCandidateXHint_wf_aux :
    WF.GadgetSpec CollapsedRepPairWFRel
      (fun input => collapsedCandidateXHint input.1 input.2)
      (CollapsedBitsWFRel 512) := by
  unfold WF.GadgetSpec
  intro left right
  unfold collapsedCandidateXHint
  apply WF.Rel.hint_pure
  · intro lv rv h
    unfold WF.ArgsEq
    simp only [WF.evalArgs]
    congr 1
    · exact h.1.2
    · congr 1
      exact h.2.2
  · intro lv rv h
    have heq : WF.evalArgs lv h![left.1.intVal, left.2.intVal] =
        WF.evalArgs rv h![right.1.intVal, right.2.intVal] := by
      simp only [WF.evalArgs]
      congr 1
      · exact h.1.2
      · congr 1
        exact h.2.2
    rw [heq, h.2.1]
    exact WF.HintRel.refl _
  · intro bitsL bitsR lv rv h i
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt

theorem collapsedCandidateXDecodeR_wf_aux :
    WF.GadgetSpec (CollapsedBitsWFRel 512)
      collapsedCandidateXDecodeR U.WFRel := by
  unfold collapsedCandidateXDecodeR
  simpa using collapsedDecodeSlice_wf_aux 512 0 256 (by omega)

theorem collapsedCandidateXDecodeQ_wf_aux :
    WF.GadgetSpec (CollapsedBitsWFRel 512)
      collapsedCandidateXDecodeQ U.WFRel := by
  unfold collapsedCandidateXDecodeQ
  simpa only [Nat.add_comm] using
    collapsedDecodeSlice_wf_aux 512 256 256 (by omega)

theorem collapsedCandidateXCheck_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Rep × Rep × U 256 × U 256) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        U.WFRel lv rv left.2.2.1 right.2.2.1 ∧
        U.WFRel lv rv left.2.2.2 right.2.2.2)
      (fun input => collapsedCandidateXCheck input.1 input.2.1
        input.2.2.1 input.2.2.2)
      (fun _ _ _ _ => True) := by
  simpa [collapsedCandidateXCheck, finishDoubleXCheck] using
    finishDoubleXCheck_wf_aux

theorem collapsedCandidateX_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point × Rep) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => collapsedCandidateX input.1 input.2.1 input.2.2)
      Modular.Elem.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold collapsedCandidateX
  apply WF.GadgetSpec.bind_rule_direct
    (left := (left.2.2, collapsedCandidateXTarget left.1 left.2.1))
    (right := (right.2.2, collapsedCandidateXTarget right.1 right.2.1))
    collapsedCandidateXHint_wf_aux
  · intro lv rv h
    constructor
    · exact h.2.2
    · unfold collapsedCandidateXTarget add Modular.Lazy.add
      exact ⟨by simp only; rw [h.1.1.1, h.2.1.1.1], by
        unfold WF.LCEq
        simp only [LC.eval_add]
        rw [h.1.1.2, h.2.1.1.2]⟩
  · intro bitsL bitsR
    apply WF.GadgetSpec.bind_rule_direct
      (left := bitsL) (right := bitsR) collapsedCandidateXDecodeR_wf_aux
    · intro lv rv h
      exact h.2
    · intro rL rR
      apply WF.GadgetSpec.bind_rule_direct
        (left := bitsL) (right := bitsR) collapsedCandidateXDecodeQ_wf_aux
      · intro lv rv h
        exact h.1.2
      · intro qL qR
        apply WF.GadgetSpec.bind_rule_direct
          (left := (left.2.2, collapsedCandidateXTarget left.1 left.2.1,
            rL, qL))
          (right := (right.2.2,
            collapsedCandidateXTarget right.1 right.2.1, rR, qR))
          collapsedCandidateXCheck_wf_aux
        · intro lv rv h
          have hinput := h.1.1.1
          constructor
          · exact hinput.2.2
          · constructor
            · unfold collapsedCandidateXTarget add Modular.Lazy.add
              exact ⟨by simp only; rw [hinput.1.1.1, hinput.2.1.1.1], by
                unfold WF.LCEq
                simp only [LC.eval_add]
                rw [hinput.1.1.2, hinput.2.1.1.2]⟩
            · exact ⟨h.1.2, h.2⟩
        · intro _ _
          apply WF.Rel.pure
          intro lv rv h
          exact h.1.1.2

private def CollapsedRepTripleWFRel (lv rv : WF.Valuation)
    (left right : Rep × Rep × Rep) : Prop :=
  left.1.WFRel lv rv right.1 ∧
  left.2.1.WFRel lv rv right.2.1 ∧
  left.2.2.WFRel lv rv right.2.2

theorem collapsedCandidateYHint_wf_aux :
    WF.GadgetSpec CollapsedRepTripleWFRel
      (fun input => collapsedCandidateYHint input.1 input.2.1 input.2.2)
      (CollapsedBitsWFRel 514) := by
  unfold WF.GadgetSpec
  intro left right
  unfold collapsedCandidateYHint
  apply WF.Rel.hint_pure
  · intro lv rv h
    unfold WF.ArgsEq
    simp only [WF.evalArgs]
    congr 1
    · exact h.1.2
    · congr 1
      · exact h.2.1.2
      · congr 1
        exact h.2.2.2
  · intro lv rv h
    have heq :
        WF.evalArgs lv h![left.1.intVal, left.2.1.intVal,
          left.2.2.intVal] =
        WF.evalArgs rv h![right.1.intVal, right.2.1.intVal,
          right.2.2.intVal] := by
      simp only [WF.evalArgs]
      congr 1
      · exact h.1.2
      · congr 1
        · exact h.2.1.2
        · congr 1
          exact h.2.2.2
    rw [heq, h.2.2.1]
    exact WF.HintRel.refl _
  · intro bitsL bitsR lv rv h i
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt

theorem collapsedCandidateYDecodeR_wf_aux :
    WF.GadgetSpec (CollapsedBitsWFRel 514)
      collapsedCandidateYDecodeR U.WFRel := by
  unfold collapsedCandidateYDecodeR
  simpa using collapsedDecodeSlice_wf_aux 514 0 256 (by omega)

theorem collapsedCandidateYDecodeQ_wf_aux :
    WF.GadgetSpec (CollapsedBitsWFRel 514)
      collapsedCandidateYDecodeQ U.WFRel := by
  unfold collapsedCandidateYDecodeQ
  simpa only [Nat.add_comm] using
    collapsedDecodeSlice_wf_aux 514 256 258 (by omega)

theorem collapsedCandidateYCheck_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Rep × Rep × Rep × U 256 × U 258) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.1.WFRel lv rv right.2.2.1 ∧
        U.WFRel lv rv left.2.2.2.1 right.2.2.2.1 ∧
        U.WFRel lv rv left.2.2.2.2 right.2.2.2.2)
      (fun input => collapsedCandidateYCheck input.1 input.2.1
        input.2.2.1 input.2.2.2.1 input.2.2.2.2)
      (fun _ _ _ _ => True) := by
  simpa [collapsedCandidateYCheck, finishDoubleYCheck] using
    finishDoubleYCheck_wf_aux

theorem collapsedCandidateY_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Rep × Fp) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        Modular.Elem.WFRel lv rv left.2.2 right.2.2)
      (fun input => collapsedCandidateY input.1 input.2.1 input.2.2)
      Modular.Elem.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold collapsedCandidateY
  apply WF.GadgetSpec.bind_rule_direct
    (left := (left.2.1, collapsedCandidateYFactor left.1 left.2.2,
      left.1.Y))
    (right := (right.2.1, collapsedCandidateYFactor right.1 right.2.2,
      right.1.Y))
    collapsedCandidateYHint_wf_aux
  · intro lv rv h
    constructor
    · exact h.2.1
    · constructor
      · unfold collapsedCandidateYFactor sub ofElem Modular.Lazy.sub
          Modular.Lazy.ofElem Modular.Lazy.Rep.WFRel
        constructor
        · simp only
          rw [h.1.1.1]
        · unfold WF.LCEq
          simp only [LC.eval_sub, LC.eval_add, LC.eval_ofConst]
          rw [h.1.1.2, h.2.2.1]
      · exact h.1.2.1
  · intro bitsL bitsR
    apply WF.GadgetSpec.bind_rule_direct
      (left := bitsL) (right := bitsR) collapsedCandidateYDecodeR_wf_aux
    · intro lv rv h
      exact h.2
    · intro rL rR
      apply WF.GadgetSpec.bind_rule_direct
        (left := bitsL) (right := bitsR) collapsedCandidateYDecodeQ_wf_aux
      · intro lv rv h
        exact h.1.2
      · intro qL qR
        apply WF.GadgetSpec.bind_rule_direct
          (left := (left.2.1, collapsedCandidateYFactor left.1 left.2.2,
            left.1.Y, rL, qL))
          (right := (right.2.1,
            collapsedCandidateYFactor right.1 right.2.2,
            right.1.Y, rR, qR))
          collapsedCandidateYCheck_wf_aux
        · intro lv rv h
          have hinput := h.1.1.1
          constructor
          · exact hinput.2.1
          · constructor
            · unfold collapsedCandidateYFactor sub ofElem Modular.Lazy.sub
                Modular.Lazy.ofElem Modular.Lazy.Rep.WFRel
              constructor
              · simp only
                rw [hinput.1.1.1]
              · unfold WF.LCEq
                simp only [LC.eval_sub, LC.eval_add, LC.eval_ofConst]
                rw [hinput.1.1.2, hinput.2.2.1]
            · exact ⟨hinput.1.2.1, h.1.2, h.2⟩
        · intro _ _
          apply WF.Rel.pure
          intro lv rv h
          exact h.1.1.2

theorem finishAddCandidateCollapsedX_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point × SlopeOperands) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => finishAddCandidateCollapsedX
        input.1 input.2.1 input.2.2)
      Modular.Lazy.Rep.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold finishAddCandidateCollapsedX
  apply WF.GadgetSpec.bind_rule_direct
    (left := left.2.2) (right := right.2.2) collapsedSlope_wf_aux
  · intro lv rv h
    exact h.2.2
  · intro slopeL slopeR
    apply WF.GadgetSpec.bind_rule_direct
      (left := (left.1, left.2.1, slopeL))
      (right := (right.1, right.2.1, slopeR))
      collapsedCandidateX_wf_aux
    · intro lv rv h
      exact ⟨h.1.1, h.1.2.1, h.2⟩
    · intro xL xR
      apply WF.Rel.pure
      intro lv rv h
      unfold ofElem Modular.Lazy.ofElem Modular.Lazy.Rep.WFRel
      exact ⟨rfl, h.2.1⟩

theorem finishAddCandidateCollapsed_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point × SlopeOperands) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => finishAddCandidateCollapsed
        input.1 input.2.1 input.2.2)
      (fun lv rv left right =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2) := by
  unfold WF.GadgetSpec
  intro left right
  unfold finishAddCandidateCollapsed
  apply WF.GadgetSpec.bind_rule_direct
    (left := left.2.2) (right := right.2.2) collapsedSlope_wf_aux
  · intro lv rv h
    exact h.2.2
  · intro slopeL slopeR
    apply WF.GadgetSpec.bind_rule_direct
      (left := (left.1, left.2.1, slopeL))
      (right := (right.1, right.2.1, slopeR))
      collapsedCandidateX_wf_aux
    · intro lv rv h
      exact ⟨h.1.1, h.1.2.1, h.2⟩
    · intro xL xR
      apply WF.GadgetSpec.bind_rule_direct
        (left := (left.1, slopeL, xL))
        (right := (right.1, slopeR, xR)) collapsedCandidateY_wf_aux
      · intro lv rv h
        exact ⟨h.1.1.1, h.1.2, h.2⟩
      · intro yL yR
        apply WF.Rel.pure
        intro lv rv h
        unfold ofElem Modular.Lazy.ofElem Modular.Lazy.Rep.WFRel
        exact ⟨⟨rfl, h.1.2.1⟩, ⟨rfl, h.2.1⟩⟩

theorem addCandidateCollapsed_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point × AddControl) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => addCandidateCollapsed input.1 input.2.1 input.2.2)
      (fun lv rv left right =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2) := by
  wfgen' using [selectSlopeOperandsCollapsedTight_wf_aux,
    finishAddCandidateCollapsed_wf_aux] unfold [addCandidateCollapsed]
  case vc1 =>
    rename_i hrel
    apply WF.GadgetSpec.direct_rule
      (left := (left.1, left.2.1, outL))
      (right := (right.1, right.2.1, outR))
      finishAddCandidateCollapsed_wf_aux
    intro lv rv hB
    have hh := hrel lv rv hB
    exact ⟨hh.1.1, hh.1.2.1, hh.2⟩

def selectCollapsedOutput_wf_aux :=
  selectGated4Rep_wf_aux 256 2 "collapsed output"

theorem selectAddCoordinateCollapsed_wf_aux :
    WF.GadgetSpec
      (fun lv rv
          (left right :
            Rep × Rep × Rep × Point × Point × AddControl × LC ℤ) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.1.WFRel lv rv right.2.2.1 ∧
        left.2.2.2.1.WFRel lv rv right.2.2.2.1 ∧
        left.2.2.2.2.1.WFRel lv rv right.2.2.2.2.1 ∧
        left.2.2.2.2.2.1.WFRel lv rv right.2.2.2.2.2.1 ∧
        WF.LCEq lv.int rv.int left.2.2.2.2.2.2 right.2.2.2.2.2.2)
      (fun input => selectAddCoordinateCollapsed input.1 input.2.1
        input.2.2.1 input.2.2.2.1 input.2.2.2.2.1
        input.2.2.2.2.2.1 input.2.2.2.2.2.2)
      Modular.Lazy.Rep.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold selectAddCoordinateCollapsed
  apply WF.GadgetSpec.direct_rule
    (left := (left.2.2.2.2.2.1.active,
      left.2.2.2.1.infinity,
      left.2.2.2.2.1.infinity - left.2.2.2.2.2.2,
      left.2.2.2.2.2.1.finite - left.2.2.2.2.2.1.active,
      left.2.2.1, left.2.1, left.1, ofElem zero))
    (right := (right.2.2.2.2.2.1.active,
      right.2.2.2.1.infinity,
      right.2.2.2.2.1.infinity - right.2.2.2.2.2.2,
      right.2.2.2.2.2.1.finite - right.2.2.2.2.2.1.active,
      right.2.2.1, right.2.1, right.1, ofElem zero))
    selectCollapsedOutput_wf_aux
  intro lv rv h
  simp_all [Point.WFRel, AddControl.WFRel, ofElem,
    Modular.Lazy.ofElem, Modular.Lazy.Rep.WFRel, WF.LCEq,
    LC.eval_sub, LC.eval_ofConst, zero, fpConst, Modular.ofNat, U.intVal]

theorem selectAddOutputCollapsed_wf_aux :
    WF.GadgetSpec
      (fun lv rv
          (left right : Point × Point × AddControl × (Rep × Rep)) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.1.WFRel lv rv right.2.2.1 ∧
        left.2.2.2.1.WFRel lv rv right.2.2.2.1 ∧
        left.2.2.2.2.WFRel lv rv right.2.2.2.2)
      (fun input => selectAddOutputCollapsed input.1 input.2.1
        input.2.2.1 input.2.2.2)
      Point.WFRel := by
  wfgen' using [andBit_wf_aux, selectAddCoordinateCollapsed_wf_aux,
    and3Bit_wf_aux]
    unfold [selectAddOutputCollapsed, Point.WFRel, AddControl.WFRel,
      Modular.Lazy.Rep.WFRel]
  all_goals simp_all [Modular.Lazy.Rep.WFRel, WF.LCEq, LC.eval_add]
  all_goals grind

theorem addCompleteCollapsed_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point) =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2)
      (fun input => addCompleteCollapsed input.1 input.2)
      Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold addCompleteCollapsed
  apply WF.GadgetSpec.bind_rule
    (left := left) (right := right) classifyAdd_wf_aux
  · intro lv rv h
    exact h
  · intro B controlL controlR hcontrol
    apply WF.GadgetSpec.bind_rule
      (left := (left.1, left.2, controlL))
      (right := (right.1, right.2, controlR))
      addCandidateCollapsed_wf_aux
    · intro lv rv hB
      have h := hcontrol lv rv hB
      exact ⟨h.1.1, h.1.2, h.2⟩
    · intro C candidateL candidateR hcandidate
      apply WF.GadgetSpec.direct_rule
        (left := (left.1, left.2, controlL, candidateL))
        (right := (right.1, right.2, controlR, candidateR))
        selectAddOutputCollapsed_wf_aux
      intro lv rv hC
      have hc := hcandidate lv rv hC
      have hk := hcontrol lv rv hc.1
      exact ⟨hk.1.1, hk.1.2, hk.2, hc.2.1, hc.2.2⟩

end Freigen.F2Z.Examples.P256.AffineSlope
