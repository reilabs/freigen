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

@[simp] private theorem curveB_intVal_eval_eq {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx) :
    lv.int (@U.intVal leftCtx 256
      (@Modular.Elem.val 256 leftCtx base (@curveB leftCtx))) =
      rv.int (@U.intVal rightCtx 256
        (@Modular.Elem.val 256 rightCtx base (@curveB rightCtx))) := by
  unfold curveB fpConst Modular.ofNat U.intVal
  simp

theorem assertOnCurve_wf_aux :
    WF.GadgetSpec
      (fun {leftCtx rightCtx} lv rv
          (left : @Fp leftCtx × @Fp leftCtx)
          (right : @Fp rightCtx × @Fp rightCtx) =>
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
    let elemIntL (x : @Fp leftCtx) : leftCtx.Wℤ :=
      @U.intVal leftCtx 256 (@Modular.Elem.val 256 leftCtx base x)
    let elemIntR (x : @Fp rightCtx) : rightCtx.Wℤ :=
      @U.intVal rightCtx 256 (@Modular.Elem.val 256 rightCtx base x)
    let repIntL (x : @Modular.Lazy.Rep 256 leftCtx base) : leftCtx.Wℤ :=
      @Modular.Lazy.Rep.intVal 256 leftCtx base x
    let repIntR (x : @Modular.Lazy.Rep 256 rightCtx base) : rightCtx.Wℤ :=
      @Modular.Lazy.Rep.intVal 256 rightCtx base x
    let leftY : @Modular.Lazy.Rep 256 leftCtx base :=
      @Modular.Lazy.Rep.mk 256 leftCtx base (elemIntL left.2) 2
    let rightY : @Modular.Lazy.Rep 256 rightCtx base :=
      @Modular.Lazy.Rep.mk 256 rightCtx base (elemIntR right.2) 2
    let leftRhs : @Modular.Lazy.Rep 256 leftCtx base :=
      @Modular.Lazy.Rep.mk 256 leftCtx base
        (repIntL outL + elemIntL (@curveB leftCtx) +
          (ofScalar (((3 * 2 : Nat) * base.modulus : Nat) : Int) :
            leftCtx.Wℤ) -
          3 • elemIntL left.1)
        (@Modular.Lazy.Rep.bound 256 leftCtx base outL + 2 + 3 * 2)
    let rightRhs : @Modular.Lazy.Rep 256 rightCtx base :=
      @Modular.Lazy.Rep.mk 256 rightCtx base
        (repIntR outR + elemIntR (@curveB rightCtx) +
          (ofScalar (((3 * 2 : Nat) * base.modulus : Nat) : Int) :
            rightCtx.Wℤ) -
          3 • elemIntR right.1)
        (@Modular.Lazy.Rep.bound 256 rightCtx base outR + 2 + 3 * 2)
    apply WF.GadgetSpec.direct_rule
      (left := (leftY, leftY, leftRhs))
      (right := (rightY, rightY, rightRhs))
      (Modular.Lazy.assertMulEq_wf base)
    intro lv rv hB
    have h2 := hmul2 lv rv hB
    have h1 := hmul1 lv rv h2.1
    simp_all [leftY, rightY, leftRhs, rightRhs, elemIntL, elemIntR,
      repIntL, repIntR, Modular.Lazy.Rep.WFRel, U.WFRel, WF.LCEq,
      Valuation.add_apply, Valuation.sub_apply, Valuation.ofScalar_apply,
      curveB_intVal_eval_eq]
    exact curveB_intVal_eval_eq lv rv
  case vc2 =>
    rename_i hrel hB
    exact ⟨rfl, (hrel leftVal rightVal hB).1.1.1⟩
  all_goals simp_all [Modular.Lazy.Rep.WFRel, U.WFRel, WF.LCEq]

end Freigen.F2Z.Examples.P256.Projective.Lazy

namespace Freigen.F2Z.Examples.P256.AffineSlope

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

private theorem fpConst_wfRel {leftCtx rightCtx : Context}
    (x : Nat) (h : x < baseModulus)
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx) :
    Modular.Elem.WFRel lv rv (@fpConst leftCtx x h)
      (@fpConst rightCtx x h) := by
  unfold Modular.Elem.WFRel fpConst Modular.ofNat
  exact U.wfRel_bitVec lv rv (BitVec.ofNat 256 x)

@[simp] private theorem fpConst_intVal_lceq (x : Nat)
    {leftCtx rightCtx : Context} (h : x < baseModulus)
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx) :
    WF.LCEq lv.int rv.int
      (@U.intVal leftCtx 256
        (@Modular.Elem.val 256 leftCtx base (@fpConst leftCtx x h)))
      (@U.intVal rightCtx 256
        (@Modular.Elem.val 256 rightCtx base (@fpConst rightCtx x h))) :=
  (fpConst_wfRel x h lv rv).1

@[simp] private theorem zero_intVal_lceq {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx) :
    WF.LCEq lv.int rv.int
      (@U.intVal leftCtx 256
        (@Modular.Elem.val 256 leftCtx base (@zero leftCtx)))
      (@U.intVal rightCtx 256
        (@Modular.Elem.val 256 rightCtx base (@zero rightCtx))) :=
  fpConst_intVal_lceq 0 (by native_decide) lv rv

@[simp] private theorem one_intVal_lceq {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx) :
    WF.LCEq lv.int rv.int
      (@U.intVal leftCtx 256
        (@Modular.Elem.val 256 leftCtx base (@one leftCtx)))
      (@U.intVal rightCtx 256
        (@Modular.Elem.val 256 rightCtx base (@one rightCtx))) :=
  fpConst_intVal_lceq 1 (by native_decide) lv rv

@[simp] private theorem three_intVal_lceq {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx) :
    WF.LCEq lv.int rv.int
      (@U.intVal leftCtx 256
        (@Modular.Elem.val 256 leftCtx base (@three leftCtx)))
      (@U.intVal rightCtx 256
        (@Modular.Elem.val 256 rightCtx base (@three rightCtx))) :=
  fpConst_intVal_lceq 3 (by native_decide) lv rv

@[simp] private theorem zero_intVal_eval_eq {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx) :
    lv.int (@U.intVal leftCtx 256
      (@Modular.Elem.val 256 leftCtx base (@zero leftCtx))) =
      rv.int (@U.intVal rightCtx 256
        (@Modular.Elem.val 256 rightCtx base (@zero rightCtx))) :=
  zero_intVal_lceq lv rv

@[simp] private theorem one_intVal_eval_eq {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx) :
    lv.int (@U.intVal leftCtx 256
      (@Modular.Elem.val 256 leftCtx base (@one leftCtx))) =
      rv.int (@U.intVal rightCtx 256
        (@Modular.Elem.val 256 rightCtx base (@one rightCtx))) :=
  one_intVal_lceq lv rv

@[simp] private theorem three_intVal_eval_eq {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx) :
    lv.int (@U.intVal leftCtx 256
      (@Modular.Elem.val 256 leftCtx base (@three leftCtx))) =
      rv.int (@U.intVal rightCtx 256
        (@Modular.Elem.val 256 rightCtx base (@three rightCtx))) :=
  three_intVal_lceq lv rv

theorem ofElems_wfRel {leftCtx rightCtx : Context}
    {lv : @WF.Valuation leftCtx} {rv : @WF.Valuation rightCtx}
    {xL yL : @Fp leftCtx} {xR yR : @Fp rightCtx}
    (hx : Modular.Elem.WFRel lv rv xL xR)
    (hy : Modular.Elem.WFRel lv rv yL yR) :
    Point.WFRel lv rv (@ofElems leftCtx xL yL)
      (@ofElems rightCtx xR yR) := by
  exact ⟨⟨rfl, hx.1⟩, ⟨rfl, hy.1⟩, by simp [WF.LCEq, ofElems]⟩

theorem infinity_wfRel {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx) :
    Point.WFRel lv rv (@infinity leftCtx) (@infinity rightCtx) := by
  let zeroL : leftCtx.Wℤ := @U.intVal leftCtx 256
    (@Modular.Elem.val 256 leftCtx base (@zero leftCtx))
  let zeroR : rightCtx.Wℤ := @U.intVal rightCtx 256
    (@Modular.Elem.val 256 rightCtx base (@zero rightCtx))
  change (2 = 2 ∧ WF.LCEq lv.int rv.int zeroL zeroR) ∧
    (2 = 2 ∧ WF.LCEq lv.int rv.int zeroL zeroR) ∧
    WF.LCEq lv.int rv.int (1 : leftCtx.Wℤ) (1 : rightCtx.Wℤ)
  exact ⟨⟨rfl, zero_intVal_lceq lv rv⟩,
    ⟨rfl, zero_intVal_lceq lv rv⟩, by simp [WF.LCEq]⟩

theorem andBit_wf_aux :
    WF.GadgetSpec
      (fun {leftCtx rightCtx} lv rv
          (left : leftCtx.Wℤ × leftCtx.Wℤ)
          (right : rightCtx.Wℤ × rightCtx.Wℤ) =>
        WF.LCEq lv.int rv.int left.1 right.1 ∧
        WF.LCEq lv.int rv.int left.2 right.2)
      (fun input => andBit input.1 input.2)
      (fun lv rv left right => WF.LCEq lv.int rv.int left right) := by
  wfgen' using [U.fromWord_wf_rel] unfold [andBit]
  case vc1 =>
    rename_i h
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt
  all_goals simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

theorem selectRep_wf_aux (width outBound : Nat) (description : String) :
    WF.GadgetSpec
      (fun {leftCtx rightCtx} lv rv
          (left : leftCtx.Wℤ × @Rep leftCtx × @Rep leftCtx)
          (right : rightCtx.Wℤ × @Rep rightCtx × @Rep rightCtx) =>
        WF.LCEq lv.int rv.int left.1 right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => selectRep width outBound description
        input.1 input.2.1 input.2.2)
      Modular.Lazy.Rep.WFRel := by
  wfgen' using [U.fromWord_wf_rel]
    unfold [selectRep, Modular.Lazy.Rep.WFRel]
  case vc1 =>
    rename_i hrel hB
    exact ⟨rfl, (hrel leftVal rightVal hB).2.1⟩
  case vc2 =>
    rename_i h
    change WF.LCEq leftVal.bool rightVal.bool outL[i] outR[i]
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt
  case vc3 =>
    simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]
    split <;> (split <;>
      simp only [WF.interpHint_pure, WF.interpHint_fail])
  all_goals simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

theorem selectCanonical_wf_aux :
    WF.GadgetSpec
      (fun {leftCtx rightCtx} lv rv
          (left : leftCtx.Wℤ × @Rep leftCtx × @Rep leftCtx)
          (right : rightCtx.Wℤ × @Rep rightCtx × @Rep rightCtx) =>
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
    let repIntL (x : @Modular.Lazy.Rep 256 leftCtx base) : leftCtx.Wℤ :=
      @Modular.Lazy.Rep.intVal 256 leftCtx base x
    let repIntR (x : @Modular.Lazy.Rep 256 rightCtx base) : rightCtx.Wℤ :=
      @Modular.Lazy.Rep.intVal 256 rightCtx base x
    let repBoundL (x : @Modular.Lazy.Rep 256 leftCtx base) : Nat :=
      @Modular.Lazy.Rep.bound 256 leftCtx base x
    let repBoundR (x : @Modular.Lazy.Rep 256 rightCtx base) : Nat :=
      @Modular.Lazy.Rep.bound 256 rightCtx base x
    let pointYL : @Modular.Lazy.Rep 256 leftCtx base := @Point.Y leftCtx left
    let pointYR : @Modular.Lazy.Rep 256 rightCtx base := @Point.Y rightCtx right
    let infL : leftCtx.Wℤ := @Point.infinity leftCtx left
    let infR : rightCtx.Wℤ := @Point.infinity rightCtx right
    let leftDen : @Modular.Lazy.Rep 256 leftCtx base :=
      @Modular.Lazy.Rep.mk 256 leftCtx base
        (2 • repIntL pointYL + infL) (2 * repBoundL pointYL + 1)
    let rightDen : @Modular.Lazy.Rep 256 rightCtx base :=
      @Modular.Lazy.Rep.mk 256 rightCtx base
        (2 • repIntR pointYR + infR) (2 * repBoundR pointYR + 1)
    let leftNum : @Modular.Lazy.Rep 256 leftCtx base :=
      @Modular.Lazy.Rep.mk 256 leftCtx base
        (3 • repIntL outL +
          (ofScalar (2 * base.modulus : Int) : leftCtx.Wℤ) -
          @U.intVal leftCtx 256
            (@Modular.Elem.val 256 leftCtx base (@three leftCtx)) + 3 • infL)
        (3 * repBoundL outL + 2 + 1)
    let rightNum : @Modular.Lazy.Rep 256 rightCtx base :=
      @Modular.Lazy.Rep.mk 256 rightCtx base
        (3 • repIntR outR +
          (ofScalar (2 * base.modulus : Int) : rightCtx.Wℤ) -
          @U.intVal rightCtx 256
            (@Modular.Elem.val 256 rightCtx base (@three rightCtx)) + 3 • infR)
        (3 * repBoundR outR + 2 + 1)
    apply WF.GadgetSpec.direct_rule
      (left := (leftDen, leftNum))
      (right := (rightDen, rightNum))
      (Modular.Lazy.divide_wf base)
    intro lv rv hB
    have hh := hrel lv rv hB
    simp_all [leftDen, rightDen, leftNum, rightNum, repIntL, repIntR,
      repBoundL, repBoundR, pointYL, pointYR, infL, infR,
      Modular.Lazy.Rep.WFRel, WF.LCEq, Valuation.add_apply,
      Valuation.sub_apply, Valuation.ofScalar_apply, three_intVal_eval_eq]
    exact three_intVal_eval_eq lv rv

theorem finishDouble_wf_aux :
    WF.GadgetSpec
      (fun {leftCtx rightCtx} lv rv
          (left : @Point leftCtx × @Rep leftCtx)
          (right : @Point rightCtx × @Rep rightCtx) =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2)
      (fun input => finishDouble input.1 input.2) Point.WFRel := by
  wfgen' using [Modular.Lazy.mulSubToElem_wf]
    unfold [finishDouble, Point.WFRel, sub, scale, ofElem,
      Modular.Lazy.sub, Modular.Lazy.scale,
      Modular.Lazy.ofElem, Modular.Lazy.Rep.WFRel]
  all_goals simp_all [Modular.Lazy.Rep.WFRel, Modular.Elem.WFRel, U.WFRel,
    WF.LCEq, Valuation.add_apply, Valuation.sub_apply,
    Valuation.ofScalar_apply]
  case vc1 =>
    rename_i hinput hnext hB
    have hn := hnext leftVal rightVal hB
    have hi := hinput leftVal rightVal hn.1
    exact ⟨hi.2.1, hn.2.1, hi.1.1.2.2⟩
  case vc2 =>
    rename_i hinput hB
    have hi := hinput leftVal rightVal hB
    exact ⟨hi.1.1.1.1, by rw [hi.1.1.1.2, hi.2.1]⟩

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
      (fun {leftCtx rightCtx} lv rv
          (left : leftCtx.Wℤ × @Rep leftCtx × @Rep leftCtx)
          (right : rightCtx.Wℤ × @Rep rightCtx × @Rep rightCtx) =>
        WF.LCEq lv.int rv.int left.1 right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => selectFormula input.1 input.2.1 input.2.2)
      Modular.Lazy.Rep.WFRel := by
  simpa [selectFormula] using
    selectRep_wf_aux 262 66 "affine formula"

theorem and3Bit_wf_aux :
    WF.GadgetSpec
      (fun {leftCtx rightCtx} lv rv
          (left : leftCtx.Wℤ × leftCtx.Wℤ × leftCtx.Wℤ)
          (right : rightCtx.Wℤ × rightCtx.Wℤ × rightCtx.Wℤ) =>
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
      (fun {leftCtx rightCtx} lv rv
          (left : @Point leftCtx × @Point leftCtx)
          (right : @Point rightCtx × @Point rightCtx) =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2)
      (fun input => classifyAdd input.1 input.2)
      AddControl.WFRel := by
  wfgen' using [Modular.Lazy.zeroTest_wf, andBit_wf_aux]
    unfold [classifyAdd, Point.WFRel, AddControl.WFRel,
      sub, add, Modular.Lazy.sub, Modular.Lazy.add,
      Modular.Lazy.Rep.WFRel]
  all_goals simp_all [Modular.Lazy.Rep.WFRel, WF.LCEq,
    Valuation.add_apply, Valuation.sub_apply, Valuation.ofScalar_apply]
  case vc1 =>
    rename_i hinput h5 h4 h3 h2 h1 hB
    have h1' := h1 leftVal rightVal hB
    have h2' := h2 leftVal rightVal h1'.1
    have h3' := h3 leftVal rightVal h2'.1
    have h4' := h4 leftVal rightVal h3'.1
    have h5' := h5 leftVal rightVal h4'.1
    have hin := hinput leftVal rightVal h5'.1
    exact ⟨hin.2, h5'.2, h4'.2, h2'.2, by rw [h2'.2, h1'.2]⟩
  case vc2 =>
    rename_i hinput h4 h3 h2 h1 hB
    have h1' := h1 leftVal rightVal hB
    have h2' := h2 leftVal rightVal h1'.1
    have h3' := h3 leftVal rightVal h2'.1
    have h4' := h4 leftVal rightVal h3'.1
    exact (hinput leftVal rightVal h4'.1).2
  case vc3 =>
    rename_i hinput h2 h1 hB
    have h1' := h1 leftVal rightVal hB
    have h2' := h2 leftVal rightVal h1'.1
    exact h2'.2
  case vc4 =>
    rename_i hinput h1 hB
    have h1' := h1 leftVal rightVal hB
    exact (hinput leftVal rightVal h1'.1).1.2.2.2
  case vc5 =>
    rename_i hinput h1 hB
    have h1' := h1 leftVal rightVal hB
    exact (hinput leftVal rightVal h1'.1).1.1.2.2
  case vc6 =>
    rename_i hinput hB
    have hin := hinput leftVal rightVal hB
    constructor
    · rw [hin.1.1.2.1.1, hin.1.2.2.1.1]
    · rw [hin.1.1.2.1.2, hin.1.2.2.1.2]

theorem selectRawSlopeOperands_wf_aux :
    WF.GadgetSpec
      (fun {leftCtx rightCtx} lv rv
          (left : @Point leftCtx × @Point leftCtx × @AddControl leftCtx)
          (right : @Point rightCtx × @Point rightCtx × @AddControl rightCtx) =>
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
    Valuation.add_apply, Valuation.sub_apply, Valuation.ofScalar_apply]
  case vc1 =>
    rename_i hinput hmiddle hnext hB
    have hn := hnext leftVal rightVal hB
    have hm := hmiddle leftVal rightVal hn.1
    exact ⟨hm.2, hn.2⟩
  case vc2 =>
    rename_i hinput hnext hB
    have hn := hnext leftVal rightVal hB
    have hin := (hinput leftVal rightVal hn.1).1
    constructor
    · rw [hin.1.1.1, hin.2.1.1.1]
    · rw [hin.1.1.1, hin.1.1.2, hin.2.1.1.2]
  case vc3 =>
    rename_i hinput hnext hB
    have hn := hnext leftVal rightVal hB
    exact (hinput leftVal rightVal hn.1).1.1.2.1
  case vc4 =>
    rename_i hinput hB
    have hin := (hinput leftVal rightVal hB).1
    constructor
    · rw [hin.2.1.2.1.1, hin.1.2.1.1]
    · rw [hin.2.1.2.1.2, hin.1.2.1.1, hin.1.2.1.2]
  case vc5 =>
    rename_i hinput hB
    have hi := hinput leftVal rightVal hB
    constructor
    · exact hi.2.1
    · rw [hi.2.2, three_intVal_eval_eq leftVal rightVal]

theorem activateSlopeOperands_wf_aux :
    WF.GadgetSpec
      (fun {leftCtx rightCtx} lv rv
          (left : @Point leftCtx × @Point leftCtx × @AddControl leftCtx ×
            @SlopeOperands leftCtx)
          (right : @Point rightCtx × @Point rightCtx × @AddControl rightCtx ×
            @SlopeOperands rightCtx) =>
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
  case vc1 =>
    rename_i hinput hnext hB
    have hn := hnext leftVal rightVal hB
    have hi := hinput leftVal rightVal hn.1
    exact ⟨hi.2, hn.2⟩
  case vc2 =>
    exact ⟨rfl, one_intVal_lceq leftVal rightVal⟩
  case vc3 =>
    exact ⟨rfl, zero_intVal_lceq leftVal rightVal⟩

theorem selectSlopeOperands_wf_aux :
    WF.GadgetSpec
      (fun {leftCtx rightCtx} lv rv
          (left : @Point leftCtx × @Point leftCtx × @AddControl leftCtx)
          (right : @Point rightCtx × @Point rightCtx × @AddControl rightCtx) =>
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
      (fun {leftCtx rightCtx} lv rv
          (left : @Point leftCtx × @Point leftCtx × @SlopeOperands leftCtx)
          (right : @Point rightCtx × @Point rightCtx × @SlopeOperands rightCtx) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => finishAddCandidate input.1 input.2.1 input.2.2)
      (fun {leftCtx rightCtx} lv rv
          (left : @Rep leftCtx × @Rep leftCtx)
          (right : @Rep rightCtx × @Rep rightCtx) =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2) := by
  wfgen' using [Modular.Lazy.divide_wf,
    Modular.Lazy.mulSubToElem_wf]
    unfold [finishAddCandidate, Point.WFRel, SlopeOperands.WFRel,
      add, sub, ofElem, Modular.Lazy.add, Modular.Lazy.sub,
      Modular.Lazy.ofElem, Modular.Lazy.Rep.WFRel]
  all_goals simp_all [Modular.Lazy.Rep.WFRel, Modular.Elem.WFRel, U.WFRel,
    WF.LCEq, Valuation.add_apply, Valuation.sub_apply,
    Valuation.ofScalar_apply]
  case vc1 =>
    rename_i hinput hmiddle hnext hB
    have hn := hnext leftVal rightVal hB
    have hm := hmiddle leftVal rightVal hn.1
    exact ⟨hm.2.1, hn.2.1⟩
  case vc2 =>
    rename_i hinput hnext hB
    have hn := hnext leftVal rightVal hB
    have hi := hinput leftVal rightVal hn.1
    exact ⟨hi.1.1.1.1, by rw [hi.1.1.1.2, hn.2.1]⟩
  case vc3 =>
    rename_i hinput hB
    have hi := hinput leftVal rightVal hB
    constructor
    · rw [hi.1.1.1.1, hi.1.2.1.1.1]
    · rw [hi.1.1.1.2, hi.1.2.1.1.2]

theorem addCandidate_wf_aux :
    WF.GadgetSpec
      (fun {leftCtx rightCtx} lv rv
          (left : @Point leftCtx × @Point leftCtx × @AddControl leftCtx)
          (right : @Point rightCtx × @Point rightCtx × @AddControl rightCtx) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.WFRel lv rv right.2.2)
      (fun input => addCandidate input.1 input.2.1 input.2.2)
      (fun {leftCtx rightCtx} lv rv
          (left : @Rep leftCtx × @Rep leftCtx)
          (right : @Rep rightCtx × @Rep rightCtx) =>
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
      (fun {leftCtx rightCtx} lv rv
          (left : @Point leftCtx × @Point leftCtx × @AddControl leftCtx ×
            (@Rep leftCtx × @Rep leftCtx))
          (right : @Point rightCtx × @Point rightCtx × @AddControl rightCtx ×
            (@Rep rightCtx × @Rep rightCtx)) =>
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
  all_goals simp_all [Modular.Lazy.Rep.WFRel, WF.LCEq,
    Valuation.add_apply]
  all_goals try exact zero_intVal_eval_eq leftVal rightVal
  all_goals grind

theorem addComplete_wf_aux :
    WF.GadgetSpec
      (fun {leftCtx rightCtx} lv rv
          (left : @Point leftCtx × @Point leftCtx)
          (right : @Point rightCtx × @Point rightCtx) =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2)
      (fun input => addComplete input.1 input.2)
      Point.WFRel := by
  unfold WF.GadgetSpec
  intro leftCtx rightCtx left right
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
