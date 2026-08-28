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

private def DoubleBitsWFRel (n : Nat) (lv rv : WF.Valuation)
    (left right : Vector (LC Bool) n) : Prop :=
  ∀ i : Fin n, WF.LCEq lv.bool rv.bool left[i] right[i]

private theorem doubleDecodeSlice_wf_aux
    (total start width : Nat) (hfit : start + width ≤ total) :
    WF.GadgetSpec (DoubleBitsWFRel total)
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

theorem doubleSquareHint_wf_aux :
    WF.GadgetSpec Point.WFRel doubleSquareHint (DoubleBitsWFRel 512) := by
  unfold WF.GadgetSpec
  intro left right
  unfold doubleSquareHint
  apply WF.Rel.hint_pure
  · intro lv rv h
    unfold WF.ArgsEq
    simp only [WF.evalArgs]
    exact congrArg (fun x => h![x]) h.1.2
  · intro lv rv h
    have heq : WF.evalArgs lv h![left.X.intVal] =
        WF.evalArgs rv h![right.X.intVal] := by
      simp only [WF.evalArgs]
      exact congrArg (fun x => h![x]) h.1.2
    rw [heq]
    exact WF.HintRel.refl _
  · intro bitsL bitsR lv rv h i
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt

theorem doubleSquareDecodeR_wf_aux :
    WF.GadgetSpec (DoubleBitsWFRel 512) doubleSquareDecodeR U.WFRel := by
  unfold doubleSquareDecodeR
  simpa using doubleDecodeSlice_wf_aux 512 0 256 (by omega)

theorem doubleSquareDecodeQ_wf_aux :
    WF.GadgetSpec (DoubleBitsWFRel 512) doubleSquareDecodeQ U.WFRel := by
  unfold doubleSquareDecodeQ
  simpa only [Nat.add_comm] using
    doubleDecodeSlice_wf_aux 512 256 256 (by omega)

theorem doubleSquareCheck_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × U 256 × U 256) =>
        left.1.WFRel lv rv right.1 ∧
        U.WFRel lv rv left.2.1 right.2.1 ∧
        U.WFRel lv rv left.2.2 right.2.2)
      (fun input => doubleSquareCheck input.1 input.2.1 input.2.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold doubleSquareCheck
  apply WF.Rel.assertR1C_pure
  · intro lv rv h
    exact h.1.1.2
  · intro lv rv h
    exact h.1.1.2
  · intro lv rv h
    unfold WF.LCEq
    simp only [LC.eval_add, LC.eval_nsmul]
    rw [h.2.1.1, h.2.2.1]
  · intro _ _ _
    trivial

theorem doubleSquare_wf_aux :
    WF.GadgetSpec Point.WFRel doubleSquare Modular.Lazy.Rep.WFRel := by
  wfgen' using [doubleSquareHint_wf_aux, doubleSquareDecodeR_wf_aux,
    doubleSquareDecodeQ_wf_aux, doubleSquareCheck_wf_aux]
    unfold [doubleSquare, Modular.Lazy.Rep.WFRel]

private def RepPairWFRel (lv rv : WF.Valuation)
    (left right : Rep × Rep) : Prop :=
  left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2

theorem doubleSlopeHint_wf_aux :
    WF.GadgetSpec RepPairWFRel
      (fun input => doubleSlopeHint input.1 input.2)
      (DoubleBitsWFRel 513) := by
  unfold WF.GadgetSpec
  intro left right
  unfold doubleSlopeHint
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

theorem doubleSlopeDecodeValue_wf_aux :
    WF.GadgetSpec (DoubleBitsWFRel 513) doubleSlopeDecodeValue U.WFRel := by
  unfold doubleSlopeDecodeValue
  simpa using doubleDecodeSlice_wf_aux 513 0 256 (by omega)

theorem doubleSlopeDecodeQ_wf_aux :
    WF.GadgetSpec (DoubleBitsWFRel 513) doubleSlopeDecodeQ U.WFRel := by
  unfold doubleSlopeDecodeQ
  simpa only [Nat.add_comm] using
    doubleDecodeSlice_wf_aux 513 256 257 (by omega)

theorem doubleSlopeCheck_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Rep × Rep × U 256 × U 257) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        U.WFRel lv rv left.2.2.1 right.2.2.1 ∧
        U.WFRel lv rv left.2.2.2 right.2.2.2)
      (fun input => doubleSlopeCheck input.1 input.2.1
        input.2.2.1 input.2.2.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold doubleSlopeCheck
  apply WF.Rel.assertR1C_pure
  · intro lv rv h
    exact h.2.2.1.1
  · intro lv rv h
    exact h.1.2
  · intro lv rv h
    unfold WF.LCEq
    simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul, LC.eval_ofConst]
    rw [h.2.1.2, h.2.2.2.1, h.2.1.1]
  · intro _ _ _
    trivial

theorem doubleSlopeFromSquare_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Rep) =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2)
      (fun input => doubleSlopeFromSquare input.1 input.2)
      Modular.Lazy.Rep.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold doubleSlopeFromSquare
  apply WF.GadgetSpec.bind_rule_direct
    (left := (doubleSlopeDenominator left.1,
      doubleSlopeNumerator left.1 left.2))
    (right := (doubleSlopeDenominator right.1,
      doubleSlopeNumerator right.1 right.2))
    doubleSlopeHint_wf_aux
  · intro lv rv h
    constructor
    · unfold doubleSlopeDenominator add scale Modular.Lazy.add
        Modular.Lazy.scale Modular.Lazy.Rep.WFRel
      constructor
      · simp only
        rw [h.1.2.1.1]
      · unfold WF.LCEq
        simp only [LC.eval_add, LC.eval_nsmul]
        rw [h.1.2.1.2, h.1.2.2]
    · unfold doubleSlopeNumerator add sub scale ofElem
        Modular.Lazy.add Modular.Lazy.sub Modular.Lazy.scale
        Modular.Lazy.ofElem Modular.Lazy.Rep.WFRel
      constructor
      · simp only
        rw [h.2.1]
      · unfold WF.LCEq
        simp only [LC.eval_add, LC.eval_sub, LC.eval_nsmul,
          LC.eval_ofConst]
        rw [h.2.2, h.1.2.2, three_intVal_eval_eq lv rv]
  · intro bitsL bitsR
    apply WF.GadgetSpec.bind_rule_direct
      (left := bitsL) (right := bitsR) doubleSlopeDecodeValue_wf_aux
    · intro lv rv h
      exact h.2
    · intro valueL valueR
      apply WF.GadgetSpec.bind_rule_direct
        (left := bitsL) (right := bitsR) doubleSlopeDecodeQ_wf_aux
      · intro lv rv h
        exact h.1.2
      · intro qL qR
        apply WF.GadgetSpec.bind_rule_direct
          (left := (doubleSlopeDenominator left.1,
            doubleSlopeNumerator left.1 left.2, valueL, qL))
          (right := (doubleSlopeDenominator right.1,
            doubleSlopeNumerator right.1 right.2, valueR, qR))
          doubleSlopeCheck_wf_aux
        · intro lv rv h
          have hinput := h.1.1.1
          constructor
          · unfold doubleSlopeDenominator add scale Modular.Lazy.add
              Modular.Lazy.scale Modular.Lazy.Rep.WFRel
            constructor
            · simp only
              rw [hinput.1.2.1.1]
            · unfold WF.LCEq
              simp only [LC.eval_add, LC.eval_nsmul]
              rw [hinput.1.2.1.2, hinput.1.2.2]
          · constructor
            · unfold doubleSlopeNumerator add sub scale ofElem
                Modular.Lazy.add Modular.Lazy.sub Modular.Lazy.scale
                Modular.Lazy.ofElem Modular.Lazy.Rep.WFRel
              constructor
              · simp only
                rw [hinput.2.1]
              · unfold WF.LCEq
                simp only [LC.eval_add, LC.eval_sub, LC.eval_nsmul,
                  LC.eval_ofConst]
                rw [hinput.2.2, hinput.1.2.2,
                  three_intVal_eval_eq lv rv]
            · exact ⟨h.1.2, h.2⟩
        · intro _ _
          apply WF.Rel.pure
          intro lv rv h
          exact ⟨rfl, h.1.1.2.1⟩

theorem doubleSlope_wf_aux :
    WF.GadgetSpec Point.WFRel doubleSlope
      Modular.Lazy.Rep.WFRel := by
  wfgen' using [doubleSquare_wf_aux, doubleSlopeFromSquare_wf_aux]
    unfold [doubleSlope]
  case vc1 =>
    rename_i hrel
    apply WF.GadgetSpec.direct_rule
      (left := (left, outL)) (right := (right, outR))
      doubleSlopeFromSquare_wf_aux
    intro lv rv hB
    have hh := hrel lv rv hB
    exact ⟨hh.1, hh.2⟩

theorem finishDoubleXHint_wf_aux :
    WF.GadgetSpec RepPairWFRel
      (fun input => finishDoubleXHint input.1 input.2)
      (DoubleBitsWFRel 512) := by
  unfold WF.GadgetSpec
  intro left right
  unfold finishDoubleXHint
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

theorem finishDoubleXDecodeR_wf_aux :
    WF.GadgetSpec (DoubleBitsWFRel 512) finishDoubleXDecodeR U.WFRel := by
  unfold finishDoubleXDecodeR
  simpa using doubleDecodeSlice_wf_aux 512 0 256 (by omega)

theorem finishDoubleXDecodeQ_wf_aux :
    WF.GadgetSpec (DoubleBitsWFRel 512) finishDoubleXDecodeQ U.WFRel := by
  unfold finishDoubleXDecodeQ
  simpa only [Nat.add_comm] using
    doubleDecodeSlice_wf_aux 512 256 256 (by omega)

theorem finishDoubleXCheck_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Rep × Rep × U 256 × U 256) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        U.WFRel lv rv left.2.2.1 right.2.2.1 ∧
        U.WFRel lv rv left.2.2.2 right.2.2.2)
      (fun input => finishDoubleXCheck input.1 input.2.1
        input.2.2.1 input.2.2.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold finishDoubleXCheck
  apply WF.Rel.assertR1C_pure
  · intro lv rv h
    exact h.1.2
  · intro lv rv h
    exact h.1.2
  · intro lv rv h
    unfold WF.LCEq
    simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul, LC.eval_ofConst]
    rw [h.2.2.1.1, h.2.1.2, h.2.2.2.1, h.2.1.1]
  · intro _ _ _
    trivial

theorem finishDoubleX_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Rep) =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2)
      (fun input => finishDoubleX input.1 input.2)
      Modular.Elem.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold finishDoubleX
  apply WF.GadgetSpec.bind_rule_direct
    (left := (left.2, finishDoubleXTarget left.1))
    (right := (right.2, finishDoubleXTarget right.1))
    finishDoubleXHint_wf_aux
  · intro lv rv h
    constructor
    · exact h.2
    · unfold finishDoubleXTarget scale Modular.Lazy.scale
      exact ⟨by simp only; rw [h.1.1.1], by
        unfold WF.LCEq
        simp only [LC.eval_nsmul]
        rw [h.1.1.2]⟩
  · intro bitsL bitsR
    apply WF.GadgetSpec.bind_rule_direct
      (left := bitsL) (right := bitsR) finishDoubleXDecodeR_wf_aux
    · intro lv rv h
      exact h.2
    · intro rL rR
      apply WF.GadgetSpec.bind_rule_direct
        (left := bitsL) (right := bitsR) finishDoubleXDecodeQ_wf_aux
      · intro lv rv h
        exact h.1.2
      · intro qL qR
        apply WF.GadgetSpec.bind_rule_direct
          (left := (left.2, finishDoubleXTarget left.1, rL, qL))
          (right := (right.2, finishDoubleXTarget right.1, rR, qR))
          finishDoubleXCheck_wf_aux
        · intro lv rv h
          have hinput := h.1.1.1
          constructor
          · exact hinput.2
          · constructor
            · unfold finishDoubleXTarget scale Modular.Lazy.scale
              exact ⟨by simp only; rw [hinput.1.1.1], by
                unfold WF.LCEq
                simp only [LC.eval_nsmul]
                rw [hinput.1.1.2]⟩
            · exact ⟨h.1.2, h.2⟩
        · intro _ _
          apply WF.Rel.pure
          intro lv rv h
          exact h.1.1.2

private def RepTripleWFRel (lv rv : WF.Valuation)
    (left right : Rep × Rep × Rep) : Prop :=
  left.1.WFRel lv rv right.1 ∧
  left.2.1.WFRel lv rv right.2.1 ∧
  left.2.2.WFRel lv rv right.2.2

theorem finishDoubleYHint_wf_aux :
    WF.GadgetSpec RepTripleWFRel
      (fun input => finishDoubleYHint input.1 input.2.1 input.2.2)
      (DoubleBitsWFRel 514) := by
  unfold WF.GadgetSpec
  intro left right
  unfold finishDoubleYHint
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

theorem finishDoubleYDecodeR_wf_aux :
    WF.GadgetSpec (DoubleBitsWFRel 514) finishDoubleYDecodeR U.WFRel := by
  unfold finishDoubleYDecodeR
  simpa using doubleDecodeSlice_wf_aux 514 0 256 (by omega)

theorem finishDoubleYDecodeQ_wf_aux :
    WF.GadgetSpec (DoubleBitsWFRel 514) finishDoubleYDecodeQ U.WFRel := by
  unfold finishDoubleYDecodeQ
  simpa only [Nat.add_comm] using
    doubleDecodeSlice_wf_aux 514 256 258 (by omega)

theorem finishDoubleYCheck_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Rep × Rep × Rep × U 256 × U 258) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.1.WFRel lv rv right.2.2.1 ∧
        U.WFRel lv rv left.2.2.2.1 right.2.2.2.1 ∧
        U.WFRel lv rv left.2.2.2.2 right.2.2.2.2)
      (fun input => finishDoubleYCheck input.1 input.2.1 input.2.2.1
        input.2.2.2.1 input.2.2.2.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold finishDoubleYCheck
  apply WF.Rel.assertR1C_pure
  · intro lv rv h
    exact h.1.2
  · intro lv rv h
    exact h.2.1.2
  · intro lv rv h
    unfold WF.LCEq
    simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul, LC.eval_ofConst]
    rw [h.2.2.2.1.1, h.2.2.1.2, h.2.2.2.2.1, h.2.2.1.1]
  · intro _ _ _
    trivial

theorem finishDoubleY_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Rep × Fp) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        Modular.Elem.WFRel lv rv left.2.2 right.2.2)
      (fun input => finishDoubleY input.1 input.2.1 input.2.2)
      Modular.Elem.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold finishDoubleY
  apply WF.GadgetSpec.bind_rule_direct
    (left := (left.2.1, finishDoubleYFactor left.1 left.2.2, left.1.Y))
    (right := (right.2.1, finishDoubleYFactor right.1 right.2.2,
      right.1.Y))
    finishDoubleYHint_wf_aux
  · intro lv rv h
    constructor
    · exact h.2.1
    · constructor
      · unfold finishDoubleYFactor sub ofElem Modular.Lazy.sub
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
      (left := bitsL) (right := bitsR) finishDoubleYDecodeR_wf_aux
    · intro lv rv h
      exact h.2
    · intro rL rR
      apply WF.GadgetSpec.bind_rule_direct
        (left := bitsL) (right := bitsR) finishDoubleYDecodeQ_wf_aux
      · intro lv rv h
        exact h.1.2
      · intro qL qR
        apply WF.GadgetSpec.bind_rule_direct
          (left := (left.2.1, finishDoubleYFactor left.1 left.2.2,
            left.1.Y, rL, qL))
          (right := (right.2.1, finishDoubleYFactor right.1 right.2.2,
            right.1.Y, rR, qR))
          finishDoubleYCheck_wf_aux
        · intro lv rv h
          have hinput := h.1.1.1
          constructor
          · exact hinput.2.1
          · constructor
            · unfold finishDoubleYFactor sub ofElem Modular.Lazy.sub
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

theorem finishDouble_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Rep) =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2)
      (fun input => finishDouble input.1 input.2) Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold finishDouble
  apply WF.GadgetSpec.bind_rule_direct
    (left := (left.1, left.2)) (right := (right.1, right.2))
    finishDoubleX_wf_aux
  · intro lv rv h
    exact h
  · intro xL xR
    apply WF.GadgetSpec.bind_rule_direct
      (left := (left.1, left.2, xL))
      (right := (right.1, right.2, xR)) finishDoubleY_wf_aux
    · intro lv rv h
      exact ⟨h.1.1, h.1.2, h.2⟩
    · intro yL yR
      apply WF.Rel.pure
      intro lv rv h
      unfold Point.WFRel ofElem Modular.Lazy.ofElem
        Modular.Lazy.Rep.WFRel
      exact ⟨⟨rfl, h.1.2.1⟩, ⟨rfl, h.2.1⟩, h.1.1.1.2.2⟩

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

private def ZeroTestBitsWFRel (lv rv : WF.Valuation)
    (left right : Vector (LC Bool) 257) : Prop :=
  ∀ i : Fin 257, WF.LCEq lv.bool rv.bool left[i] right[i]

theorem zeroTestBound4Hint_wf_aux :
    WF.GadgetSpec Modular.Lazy.Rep.WFRel zeroTestBound4Hint
      ZeroTestBitsWFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold zeroTestBound4Hint
  apply WF.Rel.hint_pure
  · intro lv rv h
    unfold WF.ArgsEq
    simp only [WF.evalArgs]
    exact congrArg (fun x => h![x]) h.2
  · intro lv rv h
    have heq : WF.evalArgs lv h![left.intVal] =
        WF.evalArgs rv h![right.intVal] := by
      simp only [WF.evalArgs]
      exact congrArg (fun x => h![x]) h.2
    rw [heq]
    exact WF.HintRel.refl _
  · intro bitsL bitsR lv rv h i
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt

private theorem zeroTestBound4DecodeSlice_wf_aux
    (start width : Nat) (hfit : start + width ≤ 257) :
    WF.GadgetSpec ZeroTestBitsWFRel
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
    Fin.getElem_fin] using
    h ⟨start + i.val, by omega⟩

theorem zeroTestBound4DecodeZero_wf_aux :
    WF.GadgetSpec ZeroTestBitsWFRel zeroTestBound4DecodeZero
      U.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold zeroTestBound4DecodeZero
  apply WF.GadgetSpec.direct_rule
    (left := ({ bitsLE := Vector.ofFn fun _ => left[0] } : Word 1))
    (right := ({ bitsLE := Vector.ofFn fun _ => right[0] } : Word 1))
    U.fromWord_wf_rel
  intro lv rv h i
  simpa [instGetElemWordFinLCBoolTrue, WF.LCEq] using h (0 : Fin 257)

theorem zeroTestBound4DecodeInverse_wf_aux :
    WF.GadgetSpec ZeroTestBitsWFRel zeroTestBound4DecodeInverse
      U.WFRel := by
  unfold zeroTestBound4DecodeInverse
  simpa only [Nat.add_comm] using
    zeroTestBound4DecodeSlice_wf_aux 1 256 (by omega)

theorem zeroTestBound4Prepare_wf_aux :
    WF.GadgetSpec Modular.Lazy.Rep.WFRel zeroTestBound4Prepare
      (fun lv rv (left right : LC ℤ × U 256) =>
        WF.LCEq lv.int rv.int left.1 right.1 ∧
        U.WFRel lv rv left.2 right.2) := by
  unfold WF.GadgetSpec
  intro left right
  unfold zeroTestBound4Prepare
  apply WF.GadgetSpec.bind_rule_direct
    (left := left) (right := right) zeroTestBound4Hint_wf_aux
  · intro lv rv h
    exact h
  · intro bitsL bitsR
    apply WF.GadgetSpec.bind_rule_direct
      (left := bitsL) (right := bitsR) zeroTestBound4DecodeZero_wf_aux
    · intro lv rv h
      exact h.2
    · intro zWordL zWordR
      apply WF.GadgetSpec.bind_rule_direct
        (left := bitsL) (right := bitsR)
        zeroTestBound4DecodeInverse_wf_aux
      · intro lv rv h
        exact h.1.2
      · intro inverseL inverseR
        apply WF.Rel.pure
        intro lv rv h
        constructor
        · simpa [U.intVal] using h.1.2.1
        · exact h.2

theorem zeroTestBound4InverseCheck_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Rep × LC ℤ × U 256) =>
        left.1.WFRel lv rv right.1 ∧
        WF.LCEq lv.int rv.int left.2.1 right.2.1 ∧
        U.WFRel lv rv left.2.2 right.2.2)
      (fun input => zeroTestBound4InverseCheck
        input.1 input.2.1 input.2.2)
      (fun _ _ _ _ => True) := by
  wfgen' using [U.fromWord_wf_rel]
    unfold [zeroTestBound4InverseCheck, Modular.Lazy.Rep.WFRel]
  case vc1 =>
    rename_i hrel
    apply WF.Rel.assertR1C_pure
    all_goals intro lv rv hB
    all_goals have h := hrel lv rv hB
    all_goals simp_all [WF.LCEq, U.WFRel, WF.evalArgs,
      LC.eval_add, LC.eval_sub, LC.eval_nsmul, LC.eval_ofConst]
  case vc2 =>
    rename_i h
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt
  case vc3 =>
    simp_all [WF.LCEq, WF.evalArgs, U.WFRel]
  case vc4 =>
    simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs, U.WFRel]

theorem zeroTestBound4ZeroCheck_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Rep × LC ℤ) =>
        left.1.WFRel lv rv right.1 ∧
        WF.LCEq lv.int rv.int left.2 right.2)
      (fun input => zeroTestBound4ZeroCheck input.1 input.2)
      (fun _ _ _ _ => True) := by
  wfgen' using [U.fromWord_wf_rel]
    unfold [zeroTestBound4ZeroCheck, Modular.Lazy.Rep.WFRel]
  case vc1 =>
    rename_i hrel
    apply WF.Rel.assertR1C_pure
    all_goals intro lv rv hB
    all_goals have h := hrel lv rv hB
    all_goals simp_all [WF.LCEq, U.WFRel, WF.evalArgs,
      LC.eval_nsmul]
  case vc2 =>
    rename_i h
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt
  case vc3 =>
    simp_all [WF.LCEq, WF.evalArgs]
  case vc4 =>
    simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

theorem zeroTestBound4_wf_aux :
    WF.GadgetSpec Modular.Lazy.Rep.WFRel zeroTestBound4
      (fun lv rv left right => WF.LCEq lv.int rv.int left right) := by
  unfold WF.GadgetSpec
  intro left right
  unfold zeroTestBound4
  apply WF.GadgetSpec.bind_rule
    (left := left) (right := right) zeroTestBound4Prepare_wf_aux
  · intro lv rv h
    exact h
  · intro B preparedL preparedR hprepared
    apply WF.GadgetSpec.bind_rule
      (left := (left, preparedL.1, preparedL.2))
      (right := (right, preparedR.1, preparedR.2))
      zeroTestBound4InverseCheck_wf_aux
    · intro lv rv hB
      have hp := hprepared lv rv hB
      exact ⟨hp.1, hp.2.1, hp.2.2⟩
    · intro C _ _ hcheck
      apply WF.GadgetSpec.bind_rule
        (left := (left, preparedL.1))
        (right := (right, preparedR.1))
        zeroTestBound4ZeroCheck_wf_aux
      · intro lv rv hC
        have hc := hcheck lv rv hC
        have hp := hprepared lv rv hc.1
        exact ⟨hp.1, hp.2.1⟩
      · intro D _ _ hzero
        apply WF.Rel.pure
        intro lv rv hD
        have hz := hzero lv rv hD
        have hc := hcheck lv rv hz.1
        have hp := hprepared lv rv hc.1
        exact hp.2.1

private def CanonicalSumInverseInputWFRel (lv rv : WF.Valuation)
    (left right : Rep × LC ℤ × U 256) : Prop :=
  left.1.WFRel lv rv right.1 ∧
  WF.LCEq lv.int rv.int left.2.1 right.2.1 ∧
  U.WFRel lv rv left.2.2 right.2.2

theorem zeroTestCanonicalSumInverseQHint_wf_aux :
    WF.GadgetSpec CanonicalSumInverseInputWFRel
      (fun input => zeroTestCanonicalSumInverseQHint
        input.1 input.2.1 input.2.2)
      (DoubleBitsWFRel 257) := by
  unfold WF.GadgetSpec
  intro left right
  unfold zeroTestCanonicalSumInverseQHint
  apply WF.Rel.hint_pure
  · intro lv rv h
    unfold WF.ArgsEq
    simp only [WF.evalArgs]
    congr 1
    · exact h.1.2
    · congr 1
      · exact h.2.2.1
      · congr 1
        exact h.2.1
  · intro lv rv h
    have heq :
        WF.evalArgs lv h![left.1.intVal, left.2.2.intVal, left.2.1] =
        WF.evalArgs rv h![right.1.intVal, right.2.2.intVal,
          right.2.1] := by
      simp only [WF.evalArgs]
      congr 1
      · exact h.1.2
      · congr 1
        · exact h.2.2.1
        · congr 1
          exact h.2.1
    rw [heq]
    exact WF.HintRel.refl _
  · intro bitsL bitsR lv rv h i
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt

theorem zeroTestCanonicalSumInverseQDecode_wf_aux :
    WF.GadgetSpec (DoubleBitsWFRel 257)
      zeroTestCanonicalSumInverseQDecode U.WFRel := by
  unfold zeroTestCanonicalSumInverseQDecode
  simpa using doubleDecodeSlice_wf_aux 257 0 257 (by omega)

theorem zeroTestCanonicalSumInverseCheck_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Rep × LC ℤ × U 256 × U 257) =>
        left.1.WFRel lv rv right.1 ∧
        WF.LCEq lv.int rv.int left.2.1 right.2.1 ∧
        U.WFRel lv rv left.2.2.1 right.2.2.1 ∧
        U.WFRel lv rv left.2.2.2 right.2.2.2)
      (fun input => zeroTestCanonicalSumInverseCheck input.1 input.2.1
        input.2.2.1 input.2.2.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold zeroTestCanonicalSumInverseCheck
  apply WF.Rel.assertR1C_pure
  · intro lv rv h
    exact h.1.2
  · intro lv rv h
    exact h.2.2.1.1
  · intro lv rv h
    unfold WF.LCEq
    simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul, LC.eval_ofConst]
    rw [h.2.1, h.2.2.2.1]
  · intro _ _ _
    trivial

theorem zeroTestCanonicalSumInverse_wf_aux :
    WF.GadgetSpec CanonicalSumInverseInputWFRel
      (fun input => zeroTestCanonicalSumInverse input.1
        input.2.1 input.2.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold zeroTestCanonicalSumInverse
  apply WF.GadgetSpec.bind_rule_direct
    (left := left) (right := right)
    zeroTestCanonicalSumInverseQHint_wf_aux
  · intro lv rv h
    exact h
  · intro bitsL bitsR
    apply WF.GadgetSpec.bind_rule_direct
      (left := bitsL) (right := bitsR)
      zeroTestCanonicalSumInverseQDecode_wf_aux
    · intro lv rv h
      exact h.2
    · intro qL qR
      apply WF.GadgetSpec.direct_rule
        (left := (left.1, left.2.1, left.2.2, qL))
        (right := (right.1, right.2.1, right.2.2, qR))
        zeroTestCanonicalSumInverseCheck_wf_aux
      intro lv rv h
      exact ⟨h.1.1.1, h.1.1.2.1, h.1.1.2.2, h.2⟩

private def CanonicalSumZeroInputWFRel (lv rv : WF.Valuation)
    (left right : Rep × LC ℤ) : Prop :=
  left.1.WFRel lv rv right.1 ∧
  WF.LCEq lv.int rv.int left.2 right.2

theorem zeroTestCanonicalSumZeroQHint_wf_aux :
    WF.GadgetSpec CanonicalSumZeroInputWFRel
      (fun input => zeroTestCanonicalSumZeroQHint input.1 input.2)
      (DoubleBitsWFRel 1) := by
  unfold WF.GadgetSpec
  intro left right
  unfold zeroTestCanonicalSumZeroQHint
  apply WF.Rel.hint_pure
  · intro lv rv h
    unfold WF.ArgsEq
    simp only [WF.evalArgs]
    congr 1
    · exact h.2
    · congr 1
      exact h.1.2
  · intro lv rv h
    have heq : WF.evalArgs lv h![left.2, left.1.intVal] =
        WF.evalArgs rv h![right.2, right.1.intVal] := by
      simp only [WF.evalArgs]
      congr 1
      · exact h.2
      · congr 1
        exact h.1.2
    rw [heq]
    exact WF.HintRel.refl _
  · intro bitsL bitsR lv rv h i
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt

theorem zeroTestCanonicalSumZeroQDecode_wf_aux :
    WF.GadgetSpec (DoubleBitsWFRel 1)
      zeroTestCanonicalSumZeroQDecode U.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold zeroTestCanonicalSumZeroQDecode
  apply WF.GadgetSpec.direct_rule
    (left := ({ bitsLE := left } : Word 1))
    (right := ({ bitsLE := right } : Word 1))
    U.fromWord_wf_rel
  intro lv rv h i
  exact h i

theorem zeroTestCanonicalSumZeroCheck_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Rep × LC ℤ × U 1) =>
        left.1.WFRel lv rv right.1 ∧
        WF.LCEq lv.int rv.int left.2.1 right.2.1 ∧
        U.WFRel lv rv left.2.2 right.2.2)
      (fun input => zeroTestCanonicalSumZeroCheck input.1
        input.2.1 input.2.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold zeroTestCanonicalSumZeroCheck
  apply WF.Rel.assertR1C_pure
  · intro lv rv h
    exact h.2.1
  · intro lv rv h
    exact h.1.2
  · intro lv rv h
    exact WF.eval_nsmul base.modulus h.2.2.1
  · intro _ _ _
    trivial

theorem zeroTestCanonicalSumZero_wf_aux :
    WF.GadgetSpec CanonicalSumZeroInputWFRel
      (fun input => zeroTestCanonicalSumZero input.1 input.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold zeroTestCanonicalSumZero
  apply WF.GadgetSpec.bind_rule_direct
    (left := left) (right := right) zeroTestCanonicalSumZeroQHint_wf_aux
  · intro lv rv h
    exact h
  · intro bitsL bitsR
    apply WF.GadgetSpec.bind_rule_direct
      (left := bitsL) (right := bitsR)
      zeroTestCanonicalSumZeroQDecode_wf_aux
    · intro lv rv h
      exact h.2
    · intro qL qR
      apply WF.GadgetSpec.direct_rule
        (left := (left.1, left.2, qL))
        (right := (right.1, right.2, qR))
        zeroTestCanonicalSumZeroCheck_wf_aux
      intro lv rv h
      exact ⟨h.1.1.1, h.1.1.2, h.2⟩

theorem zeroTestCanonicalSum_wf_aux :
    WF.GadgetSpec Modular.Lazy.Rep.WFRel zeroTestCanonicalSum
      (fun lv rv left right => WF.LCEq lv.int rv.int left right) := by
  unfold WF.GadgetSpec
  intro left right
  unfold zeroTestCanonicalSum
  apply WF.GadgetSpec.bind_rule_direct
    (left := left) (right := right) zeroTestBound4Prepare_wf_aux
  · intro lv rv h
    exact h
  · intro preparedL preparedR
    apply WF.GadgetSpec.bind_rule_direct
      (left := (left, preparedL.1, preparedL.2))
      (right := (right, preparedR.1, preparedR.2))
      zeroTestCanonicalSumInverse_wf_aux
    · intro lv rv h
      exact ⟨h.1, h.2.1, h.2.2⟩
    · intro _ _
      apply WF.GadgetSpec.bind_rule_direct
        (left := (left, preparedL.1))
        (right := (right, preparedR.1))
        zeroTestCanonicalSumZero_wf_aux
      · intro lv rv h
        exact ⟨h.1.1, h.1.2.1⟩
      · intro _ _
        apply WF.Rel.pure
        intro lv rv h
        exact h.1.1.2.1

theorem classifyAdd_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point) =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2)
      (fun input => classifyAdd input.1 input.2)
      AddControl.WFRel := by
  wfgen' using [zeroTestBound4_wf_aux, zeroTestCanonicalSum_wf_aux,
    andBit_wf_aux]
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
