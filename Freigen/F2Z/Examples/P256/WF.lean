import Freigen.F2Z.Examples.Modular
import Freigen.F2Z.Examples.P256.Impl

/-!
# Auxiliary quotient well-formedness proofs for P-256 circuits

These compositional contracts keep the implementation's repeated point
operations opaque during top-level ECDSA well-formedness checking.
-/

namespace Freigen.F2Z.Examples.P256.Projective.Lazy

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

@[simp] private theorem curveB_intVal_eval_eq (lv rv : WF.Valuation) :
    LC.eval lv.int curveB.val.intVal = LC.eval rv.int curveB.val.intVal := by
  unfold curveB fpConst Modular.ofNat U.intVal
  simp

theorem assertOnCurve_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Fp × Fp) =>
        Modular.Elem.WFRel lv rv left.1 right.1 ∧
        Modular.Elem.WFRel lv rv left.2 right.2)
      (fun input => assertOnCurve input.1 input.2)
      (fun _ _ _ _ => True) := by
  wfgen' using [Modular.Lazy.mul_wf, Modular.Lazy.assertMulEq_wf]
    unfold [assertOnCurve, mul, Modular.Lazy.ofElem,
      Modular.Lazy.add, Modular.Lazy.sub, Modular.Lazy.scale,
      Modular.Elem.WFRel]
  case vc1 =>
    rename_i hmul1 hmul2
    apply WF.GadgetSpec.direct_rule
      (left := (
        { intVal := left.2.val.intVal, bound := 2 },
        { intVal := left.2.val.intVal, bound := 2 },
        { intVal := outL.intVal + curveB.val.intVal +
            LC.ofConst (6 * base.modulus : Int) - 3 • left.1.val.intVal,
          bound := outL.bound + 8 }))
      (right := (
        { intVal := right.2.val.intVal, bound := 2 },
        { intVal := right.2.val.intVal, bound := 2 },
        { intVal := outR.intVal + curveB.val.intVal +
            LC.ofConst (6 * base.modulus : Int) - 3 • right.1.val.intVal,
          bound := outR.bound + 8 }))
      (Modular.Lazy.assertMulEq_wf base)
    intro lv rv hB
    have h2 := hmul2 lv rv hB
    have h1 := hmul1 lv rv h2.1
    simp_all [Modular.Lazy.Rep.WFRel, U.WFRel, WF.LCEq,
      LC.eval_add, LC.eval_sub, LC.eval_nsmul, LC.eval_ofConst]
    exact curveB_intVal_eval_eq lv rv
  case vc2 =>
    rename_i hrel hB
    exact ⟨rfl, (hrel leftVal rightVal hB).1.1.1⟩
  all_goals simp_all [Modular.Lazy.Rep.WFRel, U.WFRel, WF.LCEq]

end Freigen.F2Z.Examples.P256.Projective.Lazy

namespace Freigen.F2Z.Examples.P256.AffineSlope

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

private theorem fpConst_wfRel (x : Nat) (h : x < baseModulus)
    (lv rv : WF.Valuation) :
    Modular.Elem.WFRel lv rv (fpConst x h) (fpConst x h) := by
  unfold Modular.Elem.WFRel fpConst Modular.ofNat
  exact U.wfRel_bitVec lv rv (BitVec.ofNat 256 x)

@[simp] private theorem fpConst_intVal_lceq (x : Nat)
    (h : x < baseModulus) (lv rv : WF.Valuation) :
    WF.LCEq lv.int rv.int (fpConst x h).val.intVal
      (fpConst x h).val.intVal :=
  (fpConst_wfRel x h lv rv).1

@[simp] private theorem zero_intVal_lceq (lv rv : WF.Valuation) :
    WF.LCEq lv.int rv.int zero.val.intVal zero.val.intVal :=
  fpConst_intVal_lceq 0 (by native_decide) lv rv

@[simp] private theorem one_intVal_lceq (lv rv : WF.Valuation) :
    WF.LCEq lv.int rv.int one.val.intVal one.val.intVal :=
  fpConst_intVal_lceq 1 (by native_decide) lv rv

@[simp] private theorem three_intVal_lceq (lv rv : WF.Valuation) :
    WF.LCEq lv.int rv.int three.val.intVal three.val.intVal :=
  fpConst_intVal_lceq 3 (by native_decide) lv rv

@[simp] private theorem zero_intVal_eval_eq (lv rv : WF.Valuation) :
    LC.eval lv.int zero.val.intVal = LC.eval rv.int zero.val.intVal :=
  zero_intVal_lceq lv rv

@[simp] private theorem one_intVal_eval_eq (lv rv : WF.Valuation) :
    LC.eval lv.int one.val.intVal = LC.eval rv.int one.val.intVal :=
  one_intVal_lceq lv rv

@[simp] private theorem three_intVal_eval_eq (lv rv : WF.Valuation) :
    LC.eval lv.int three.val.intVal = LC.eval rv.int three.val.intVal :=
  three_intVal_lceq lv rv

theorem ofElems_wfRel {lv rv : WF.Valuation} {xL xR yL yR : Fp}
    (hx : Modular.Elem.WFRel lv rv xL xR)
    (hy : Modular.Elem.WFRel lv rv yL yR) :
    Point.WFRel lv rv (ofElems xL yL) (ofElems xR yR) := by
  exact ⟨⟨rfl, hx.1⟩, ⟨rfl, hy.1⟩, by simp [WF.LCEq, ofElems]⟩

theorem infinity_wfRel (lv rv : WF.Valuation) :
    Point.WFRel lv rv infinity infinity := by
  unfold Point.WFRel infinity
  exact ⟨⟨rfl, zero_intVal_lceq lv rv⟩, ⟨rfl, zero_intVal_lceq lv rv⟩,
    by simp [WF.LCEq]⟩

theorem andBit_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : LC ℤ × LC ℤ) =>
        WF.LCEq lv.int rv.int left.1 right.1 ∧
        WF.LCEq lv.int rv.int left.2 right.2)
      (fun input => andBit input.1 input.2)
      (fun lv rv left right => WF.LCEq lv.int rv.int left right) := by
  wfgen' using [U.fromWord_wf_rel] unfold [andBit]
  case vc1 =>
    rename_i h
    change WF.LCEq leftVal.bool rightVal.bool outL[i] outR[i]
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt
  all_goals simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

theorem selectRep_wf_aux (width outBound : Nat) (description : String) :
    WF.GadgetSpec
      (fun lv rv (left right : LC ℤ × Rep × Rep) =>
        WF.LCEq lv.int rv.int left.1 right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => selectRep width outBound description
        input.1 input.2.1 input.2.2)
      Modular.Lazy.Rep.WFRel := by
  wfgen' using [U.fromWord_wf_rel]
    unfold [selectRep, Modular.Lazy.Rep.WFRel]
  case vc1 =>
    rename_i h
    change WF.LCEq leftVal.bool rightVal.bool outL[i] outR[i]
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt
  all_goals simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

theorem selectCanonical_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : LC ℤ × Rep × Rep) =>
        WF.LCEq lv.int rv.int left.1 right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => selectCanonical input.1 input.2.1 input.2.2)
      Modular.Lazy.Rep.WFRel := by
  simpa [selectCanonical] using selectRep_wf_aux 256 2 "canonical"

theorem doubleSlope_wf_aux :
    WF.GadgetSpec Point.WFRel doubleSlope
      Modular.Lazy.Rep.WFRel := by
  wfgen' using [Modular.Lazy.mul_wf, Modular.Lazy.divide_wf]
    unfold [doubleSlope, Point.WFRel, add, sub, scale, ofElem,
      Modular.Lazy.add, Modular.Lazy.sub, Modular.Lazy.scale,
      Modular.Lazy.ofElem, Modular.Lazy.Rep.WFRel]
  case vc1 =>
    rename_i hrel
    apply WF.GadgetSpec.direct_rule
      (left := (
        { intVal := 2 • left.Y.intVal + left.infinity,
          bound := 2 * left.Y.bound + 1 },
        { intVal := 3 • outL.intVal + LC.ofConst (2 * base.modulus : Int) -
            three.val.intVal + 3 • left.infinity,
          bound := 3 * outL.bound + 3 }))
      (right := (
        { intVal := 2 • right.Y.intVal + right.infinity,
          bound := 2 * right.Y.bound + 1 },
        { intVal := 3 • outR.intVal + LC.ofConst (2 * base.modulus : Int) -
            three.val.intVal + 3 • right.infinity,
          bound := 3 * outR.bound + 3 }))
      (Modular.Lazy.divide_wf base)
    intro lv rv hB
    have hh := hrel lv rv hB
    simp_all [Modular.Lazy.Rep.WFRel, WF.LCEq,
      LC.eval_add, LC.eval_sub, LC.eval_nsmul, LC.eval_ofConst]
    exact three_intVal_eval_eq lv rv

theorem finishDouble_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Rep) =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2)
      (fun input => finishDouble input.1 input.2) Point.WFRel := by
  wfgen' using [Modular.Lazy.mulSubToElem_wf]
    unfold [finishDouble, Point.WFRel, sub, scale, ofElem,
      Modular.Lazy.sub, Modular.Lazy.scale,
      Modular.Lazy.ofElem, Modular.Lazy.Rep.WFRel]
  all_goals simp_all [Modular.Lazy.Rep.WFRel, Modular.Elem.WFRel, U.WFRel,
    WF.LCEq, LC.eval_add, LC.eval_sub, LC.eval_nsmul, LC.eval_ofConst]
  all_goals grind

theorem doubleComplete_wf_aux :
    WF.GadgetSpec Point.WFRel doubleComplete Point.WFRel := by
  wfgen' using [doubleSlope_wf_aux, finishDouble_wf_aux]
    unfold [doubleComplete]
  case vc1 =>
    rename_i hrel
    apply WF.GadgetSpec.direct_rule
      (left := (left, outL)) (right := (right, outR))
      finishDouble_wf_aux
    intro lv rv hB
    have hh := hrel lv rv hB
    exact ⟨hh.1, hh.2⟩

theorem selectFormula_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : LC ℤ × Rep × Rep) =>
        WF.LCEq lv.int rv.int left.1 right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => selectFormula input.1 input.2.1 input.2.2)
      Modular.Lazy.Rep.WFRel := by
  simpa [selectFormula] using
    selectRep_wf_aux 262 66 "affine formula"

theorem and3Bit_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : LC ℤ × LC ℤ × LC ℤ) =>
        WF.LCEq lv.int rv.int left.1 right.1 ∧
        WF.LCEq lv.int rv.int left.2.1 right.2.1 ∧
        WF.LCEq lv.int rv.int left.2.2 right.2.2)
      (fun input => and3Bit input.1 input.2.1 input.2.2)
      (fun lv rv left right => WF.LCEq lv.int rv.int left right) := by
  wfgen' using [andBit_wf_aux] unfold [and3Bit]
  case vc1 =>
    rename_i hrel
    apply WF.GadgetSpec.direct_rule
      (left := (left.2.2, outL)) (right := (right.2.2, outR))
      andBit_wf_aux
    intro lv rv h
    have h' := hrel lv rv h
    exact ⟨h'.1.2.2, h'.2⟩

theorem classifyAdd_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point) =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2)
      (fun input => classifyAdd input.1 input.2)
      AddControl.WFRel := by
  wfgen' using [Modular.Lazy.zeroTest_wf, andBit_wf_aux]
    unfold [classifyAdd, Point.WFRel, AddControl.WFRel,
      sub, add, Modular.Lazy.sub, Modular.Lazy.add,
      Modular.Lazy.Rep.WFRel]
  all_goals simp_all [Modular.Lazy.Rep.WFRel, WF.LCEq,
    LC.eval_add, LC.eval_sub, LC.eval_ofConst]
  all_goals grind

theorem selectRawSlopeOperands_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point × AddControl) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => selectRawSlopeOperands input.1 input.2.1 input.2.2)
      SlopeOperands.WFRel := by
  wfgen' using [Modular.Lazy.mul_wf, selectFormula_wf_aux]
    unfold [selectRawSlopeOperands, Point.WFRel, AddControl.WFRel,
      SlopeOperands.WFRel, sub, scale, ofElem, Modular.Lazy.sub,
      Modular.Lazy.scale, Modular.Lazy.ofElem, Modular.Lazy.Rep.WFRel]
  all_goals simp_all [Modular.Lazy.Rep.WFRel, WF.LCEq,
    LC.eval_add, LC.eval_sub, LC.eval_nsmul, LC.eval_ofConst]
  case vc1 =>
    rename_i hinput hnext hB
    have hin := (hinput leftVal rightVal (hnext leftVal rightVal hB).1).1
    constructor
    · rw [hin.1.1.1, hin.2.1.1.1]
    · rw [hin.1.1.1, hin.1.1.2, hin.2.1.1.2]
  case vc2 =>
    rename_i hinput hnext hB
    exact (hinput leftVal rightVal (hnext leftVal rightVal hB).1).1.1.2.1
  case vc3 =>
    rename_i hinput hB
    have hin := (hinput leftVal rightVal hB).1
    constructor
    · rw [hin.2.1.2.1.1, hin.1.2.1.1]
    · rw [hin.2.1.2.1.2, hin.1.2.1.1, hin.1.2.1.2]
  case vc4 =>
    rename_i hrel hB
    have hh := hrel leftVal rightVal hB
    constructor
    · exact hh.2.1
    · rw [hh.2.2, three_intVal_eval_eq leftVal rightVal]

theorem activateSlopeOperands_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point × AddControl × SlopeOperands) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.1.WFRel lv rv right.2.2.1 ∧
        left.2.2.2.WFRel lv rv right.2.2.2)
      (fun input => activateSlopeOperands input.1 input.2.1
        input.2.2.1 input.2.2.2)
      SlopeOperands.WFRel := by
  wfgen' using [selectFormula_wf_aux]
    unfold [activateSlopeOperands, Point.WFRel, AddControl.WFRel,
      SlopeOperands.WFRel, ofElem, Modular.Lazy.ofElem,
      Modular.Lazy.Rep.WFRel]
  all_goals simp_all [Modular.Lazy.Rep.WFRel, WF.LCEq]
  all_goals try exact zero_intVal_eval_eq leftVal rightVal
  all_goals try exact one_intVal_eval_eq leftVal rightVal

theorem selectSlopeOperands_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point × AddControl) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => selectSlopeOperands input.1 input.2.1 input.2.2)
      SlopeOperands.WFRel := by
  wfgen' using [selectRawSlopeOperands_wf_aux,
    activateSlopeOperands_wf_aux] unfold [selectSlopeOperands]
  case vc1 =>
    rename_i hrel
    apply WF.GadgetSpec.direct_rule
      (left := (left.1, left.2.1, left.2.2, outL))
      (right := (right.1, right.2.1, right.2.2, outR))
      activateSlopeOperands_wf_aux
    intro lv rv hB
    have hh := hrel lv rv hB
    exact ⟨hh.1.1, hh.1.2.1, hh.1.2.2, hh.2⟩

theorem finishAddCandidate_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point × SlopeOperands) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => finishAddCandidate input.1 input.2.1 input.2.2)
      (fun lv rv left right =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2) := by
  wfgen' using [Modular.Lazy.divide_wf,
    Modular.Lazy.mulSubToElem_wf]
    unfold [finishAddCandidate, Point.WFRel, SlopeOperands.WFRel,
      add, sub, ofElem, Modular.Lazy.add, Modular.Lazy.sub,
      Modular.Lazy.ofElem, Modular.Lazy.Rep.WFRel]
  all_goals simp_all [Modular.Lazy.Rep.WFRel, Modular.Elem.WFRel, U.WFRel,
    WF.LCEq, LC.eval_add, LC.eval_sub, LC.eval_ofConst]
  all_goals grind

theorem addCandidate_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point × AddControl) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => addCandidate input.1 input.2.1 input.2.2)
      (fun lv rv left right =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2) := by
  wfgen' using [selectSlopeOperands_wf_aux,
    finishAddCandidate_wf_aux] unfold [addCandidate]
  case vc1 =>
    rename_i hrel
    apply WF.GadgetSpec.direct_rule
      (left := (left.1, left.2.1, outL))
      (right := (right.1, right.2.1, outR))
      finishAddCandidate_wf_aux
    intro lv rv hB
    have hh := hrel lv rv hB
    exact ⟨hh.1.1, hh.1.2.1, hh.2⟩

theorem selectAddOutput_wf_aux :
    WF.GadgetSpec
      (fun lv rv
          (left right : Point × Point × AddControl × (Rep × Rep)) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.1.WFRel lv rv right.2.2.1 ∧
        left.2.2.2.1.WFRel lv rv right.2.2.2.1 ∧
        left.2.2.2.2.WFRel lv rv right.2.2.2.2)
      (fun input => selectAddOutput input.1 input.2.1
        input.2.2.1 input.2.2.2)
      Point.WFRel := by
  wfgen' using [selectCanonical_wf_aux, andBit_wf_aux,
    and3Bit_wf_aux]
    unfold [selectAddOutput, Point.WFRel, AddControl.WFRel,
      ofElem, Modular.Lazy.ofElem, Modular.Lazy.Rep.WFRel]
  all_goals simp_all [Modular.Lazy.Rep.WFRel, WF.LCEq, LC.eval_add]
  all_goals try exact zero_intVal_eval_eq leftVal rightVal
  all_goals grind

theorem addComplete_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point) =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2)
      (fun input => addComplete input.1 input.2)
      Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold addComplete
  apply WF.GadgetSpec.bind_rule
    (left := left) (right := right) classifyAdd_wf_aux
  · intro lv rv h
    exact h
  · intro B controlL controlR hcontrol
    apply WF.GadgetSpec.bind_rule
      (left := (left.1, left.2, controlL))
      (right := (right.1, right.2, controlR))
      addCandidate_wf_aux
    · intro lv rv hB
      have h := hcontrol lv rv hB
      exact ⟨h.1.1, h.1.2, h.2⟩
    · intro C candidateL candidateR hcandidate
      apply WF.GadgetSpec.direct_rule
        (left := (left.1, left.2, controlL, candidateL))
        (right := (right.1, right.2, controlR, candidateR))
        selectAddOutput_wf_aux
      intro lv rv hC
      have hc := hcandidate lv rv hC
      have hk := hcontrol lv rv hc.1
      exact ⟨hk.1.1, hk.1.2, hk.2, hc.2.1, hc.2.2⟩

end Freigen.F2Z.Examples.P256.AffineSlope
