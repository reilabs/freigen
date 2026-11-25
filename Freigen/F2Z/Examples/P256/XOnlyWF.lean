import Freigen.F2Z.Examples.P256.XOnlyImpl
import Freigen.F2Z.Examples.P256.CollapsedWF

/-!
# Quotient well-formedness for terminal X-only affine addition

ECDSA consumes only the final X coordinate and infinity flag.  The quotient
relation below therefore deliberately omits a Y component while retaining the
full input-point relation required by classification and slope arithmetic.
-/

namespace Freigen.F2Z.Examples.P256.AffineSlope

open Std.Do
open scoped Std.Do
open Modular

set_option maxRecDepth 100000

def XPoint.WFRel (lv rv : WF.Valuation) (left right : XPoint) : Prop :=
  left.X.WFRel lv rv right.X ∧
    WF.LCEq lv.int rv.int left.infinity right.infinity

theorem finishAddCandidateX_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point × SlopeOperands) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => finishAddCandidateX input.1 input.2.1 input.2.2)
      Modular.Lazy.Rep.WFRel := by
  wfgen' using [Modular.Lazy.divide_wf,
    Modular.Lazy.mulSubToElem_wf]
    unfold [finishAddCandidateX, Point.WFRel, SlopeOperands.WFRel,
      add, ofElem, Modular.Lazy.add, Modular.Lazy.ofElem,
      Modular.Lazy.Rep.WFRel]
  all_goals simp_all [Modular.Lazy.Rep.WFRel, WF.LCEq, LC.eval_add]
  all_goals grind

theorem addCandidateCollapsedX_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point × AddControl) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => addCandidateCollapsedX input.1 input.2.1 input.2.2)
      Modular.Lazy.Rep.WFRel := by
  wfgen' using [selectSlopeOperandsCollapsedTight_wf_aux,
    finishAddCandidateCollapsedX_wf_aux] unfold [addCandidateCollapsedX]
  case vc1 =>
    rename_i hrel
    apply WF.GadgetSpec.direct_rule
      (left := (left.1, left.2.1, outL))
      (right := (right.1, right.2.1, outR))
      finishAddCandidateCollapsedX_wf_aux
    intro lv rv hB
    have hh := hrel lv rv hB
    exact ⟨hh.1.1, hh.1.2.1, hh.2⟩

theorem selectAddOutputCollapsedX_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point × AddControl × Rep) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.1.WFRel lv rv right.2.2.1 ∧
        left.2.2.2.WFRel lv rv right.2.2.2)
      (fun input => selectAddOutputCollapsedX input.1 input.2.1
        input.2.2.1 input.2.2.2)
      XPoint.WFRel := by
  wfgen' using [andBit_wf_aux, selectAddCoordinateCollapsed_wf_aux,
    and3Bit_wf_aux]
    unfold [selectAddOutputCollapsedX, XPoint.WFRel, Point.WFRel,
      AddControl.WFRel, Modular.Lazy.Rep.WFRel]
  all_goals simp_all [Modular.Lazy.Rep.WFRel, WF.LCEq, LC.eval_add]
  all_goals grind

theorem addCompleteCollapsedX_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point) =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2)
      (fun input => addCompleteCollapsedX input.1 input.2)
      XPoint.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold addCompleteCollapsedX
  apply WF.GadgetSpec.bind_rule
    (left := left) (right := right) classifyAdd_wf_aux
  · intro lv rv h
    exact h
  · intro B controlL controlR hcontrol
    apply WF.GadgetSpec.bind_rule
      (left := (left.1, left.2, controlL))
      (right := (right.1, right.2, controlR))
      addCandidateCollapsedX_wf_aux
    · intro lv rv hB
      have h := hcontrol lv rv hB
      exact ⟨h.1.1, h.1.2, h.2⟩
    · intro C candidateL candidateR hcandidate
      apply WF.GadgetSpec.direct_rule
        (left := (left.1, left.2, controlL, candidateL))
        (right := (right.1, right.2, controlR, candidateR))
        selectAddOutputCollapsedX_wf_aux
      intro lv rv hC
      have hx := hcandidate lv rv hC
      have hc := hcontrol lv rv hx.1
      exact ⟨hc.1.1, hc.1.2, hc.2, hx.2⟩

end Freigen.F2Z.Examples.P256.AffineSlope
