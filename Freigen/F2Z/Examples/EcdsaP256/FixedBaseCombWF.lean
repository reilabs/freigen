import Freigen.F2Z.Examples.EcdsaP256.Radix32WF
import Freigen.F2Z.Examples.EcdsaP256.DirectTerminalWF
import Freigen.F2Z.Examples.EcdsaP256.DirectTerminalBlockWF
import Freigen.F2Z.Examples.P256.CanonicalXWF
import Freigen.F2Z.Examples.P256.XOnlyWF

/-! Quotient well-formedness for the fixed-base comb production verifier. -/

namespace Freigen.F2Z.Examples.EcdsaP256

open P256

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def IntLCVector.WFRel {n : Nat} : WF.Post (Vector (LC ℤ) n) :=
  WF.VectorRel fun lv rv left right => WF.LCEq lv.int rv.int left right

private theorem combBit_wfRel {lv rv : WF.Valuation} {left right : Fn}
    (h : Modular.Elem.ScalarWFRel lv rv left right)
    (i : Nat) (hi : i < 256) :
    WF.LCEq lv.int rv.int (combBit left i hi) (combBit right i hi) := by
  unfold combBit
  split
  · exact h.2 ⟨i + 1, by omega⟩
  · simp [WF.LCEq]

private theorem combWindowBits_wfRel {lv rv : WF.Valuation}
    {left right : Fn} (h : Modular.Elem.ScalarWFRel lv rv left right)
    (offset width : Nat) (hfit : offset + width ≤ 256) :
    IntLCVector.WFRel lv rv
      (combWindowBits left offset width hfit)
      (combWindowBits right offset width hfit) := by
  intro i
  simp only [combWindowBits, Vector.getElem_ofFn, Fin.getElem_fin]
  exact combBit_wfRel h (offset + i.val) (by omega)

private theorem combWindowValue_wfRel {lv rv : WF.Valuation}
    {width : Nat} {left right : Vector (LC ℤ) width}
    (h : IntLCVector.WFRel lv rv left right) :
    WF.LCEq lv.int rv.int
      (combWindowValue left) (combWindowValue right) := by
  unfold combWindowValue WF.LCEq
  simp only [LC.eval_sum, LC.eval_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [h i]

theorem xnorBit_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : LC ℤ × LC ℤ) =>
        WF.LCEq lv.int rv.int left.1 right.1 ∧
        WF.LCEq lv.int rv.int left.2 right.2)
      (fun input => xnorBit input.1 input.2)
      (fun lv rv left right => WF.LCEq lv.int rv.int left right) := by
  wfgen' using [AffineSlope.andBit_wf_aux] unfold [xnorBit]
  all_goals simp_all [WF.LCEq]
  case vc1 =>
    rename_i hpost hB
    have h := hpost leftVal rightVal hB
    rw [h.1.1, h.1.2, h.2]

theorem xnorMagnitudeBits_wf_aux (width : Nat) (hwidth : 1 ≤ width) :
    WF.GadgetSpec IntLCVector.WFRel
      (fun bits => xnorMagnitudeBits bits hwidth)
      IntLCVector.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold xnorMagnitudeBits
  apply WF.Rel.mono (WF.Rel.vectorOfFnM
    (S := fun _ lv rv left right => WF.LCEq lv.int rv.int left right) ?_)
  · exact fun _ _ _ _ h => h.2
  · intro i P _ _ hP
    simpa using xnorBit_wf_aux.relHom P
      (left[width - 1], left[i.val])
      (right[width - 1], right[i.val]) (by
        intro lv rv h
        have hbits := hP lv rv h
        exact ⟨hbits ⟨width - 1, by omega⟩,
          hbits ⟨i.val, by omega⟩⟩)

private theorem fixedInnerX_wfRel {lv rv : WF.Valuation}
    {left right : U 128} (h : U.FullWFRel lv rv left right)
    (table : Array Reference.Point) (width outerIndex : Nat) :
    WF.LCEq lv.int rv.int (fixedInnerX table width outerIndex left)
      (fixedInnerX table width outerIndex right) := by
  unfold fixedInnerX WF.LCEq
  simp only [LC.eval_sum, LC.eval_smul]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [LC.eval_nsmul] using
    congrArg (Reference.xNat
      table[128 * (outerIndex % 2 ^ (width - 8)) + i.val]! • ·) (h.2 i)

private theorem fixedInnerY_wfRel {lv rv : WF.Valuation}
    {left right : U 128} (h : U.FullWFRel lv rv left right)
    (table : Array Reference.Point) (width outerIndex : Nat) :
    WF.LCEq lv.int rv.int (fixedInnerY table width outerIndex left)
      (fixedInnerY table width outerIndex right) := by
  unfold fixedInnerY WF.LCEq
  simp only [LC.eval_sum, LC.eval_smul]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [LC.eval_nsmul] using
    congrArg ((if outerIndex / 2 ^ (width - 8) = 0 then
      base.modulus - Reference.yNat
        table[128 * (outerIndex % 2 ^ (width - 8)) + i.val]!
    else Reference.yNat
      table[128 * (outerIndex % 2 ^ (width - 8)) + i.val]!) • ·) (h.2 i)

theorem assertFactoredCoordinates_wf_aux (width : Nat)
    (table : Array Reference.Point) :
    WF.GadgetSpec
      (fun lv rv (left right : U 128 × U (2 ^ (width - 7)) × U 256 × U 256) =>
        U.FullWFRel lv rv left.1 right.1 ∧
        U.FullWFRel lv rv left.2.1 right.2.1 ∧
        U.WFRel lv rv left.2.2.1 right.2.2.1 ∧
        U.WFRel lv rv left.2.2.2 right.2.2.2)
      (fun input => assertFactoredCoordinates width table input.1
        input.2.1 input.2.2.1 input.2.2.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold assertFactoredCoordinates
  refine WF.Rel.mono (WF.Rel.foldRange_rule
    (I := fun lv rv (_ _ : Unit) =>
      U.FullWFRel lv rv left.1 right.1 ∧
      U.FullWFRel lv rv left.2.1 right.2.1 ∧
      U.WFRel lv rv left.2.2.1 right.2.2.1 ∧
      U.WFRel lv rv left.2.2.2 right.2.2.2) ?_ ?_) ?_
  · intro lv rv h
    exact h
  · intro i hi P _ _ hrel
    apply WF.Rel.assertR1C
    · intro lv rv hP
      exact (hrel lv rv hP).2.1.2 ⟨i, hi.2.1⟩
    · intro lv rv hP
      exact WF.eval_sub (hrel lv rv hP).2.2.1.1
        (fixedInnerX_wfRel (hrel lv rv hP).1 table width i)
    · intro _ _ _
      simp [WF.LCEq]
    apply WF.Rel.assertR1C_pure
    · intro lv rv hP
      exact (hrel lv rv hP).2.1.2 ⟨i, hi.2.1⟩
    · intro lv rv hP
      have h := hrel lv rv hP
      exact WF.eval_sub h.2.2.2.1
        (fixedInnerY_wfRel h.1 table width i)
    · intro _ _ _
      simp [WF.LCEq]
    · intro lv rv hP
      exact ⟨hP, hrel lv rv hP⟩
  · intro _ _ _ _ _
    trivial

theorem materializeFixedCoordinate_wf_aux (f : Nat → Nat) :
    WF.GadgetSpec
      (fun lv rv (left right : LC ℤ) =>
        WF.LCEq lv.int rv.int left right)
      (materializeFixedCoordinate f) U.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold materializeFixedCoordinate
  apply WF.Rel.hint
  · intro lv rv h
    unfold WF.ArgsEq
    simp only [WF.evalArgs]
    unfold WF.LCEq at h
    exact congrArg (fun value => h![value]) h
  · intro lv rv h
    apply WF.HintRel.of_argsEq
    unfold WF.ArgsEq
    simp only [WF.evalArgs]
    unfold WF.LCEq at h
    exact congrArg (fun value => h![value]) h
  · intro bitsL bitsR
    let S : WF.Assumption := fun lv rv =>
      WF.LCEq lv.int rv.int left right ∧ ∃ values,
        WF.HintReturns (coordinateHint f (WF.evalArgs lv h![left])) values ∧
        WF.HintReturns (coordinateHint f (WF.evalArgs rv h![right])) values ∧
        WF.RealizesBools lv.bool bitsL values ∧
        WF.RealizesBools rv.bool bitsR values
    have hbits : ∀ lv rv, S lv rv → ∀ i : Fin 256,
        WF.LCEq lv.bool rv.bool bitsL[i] bitsR[i] := by
      intro lv rv h i
      exact Modular.Aux.WF.lceq_of_common_realizes
        (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt
    have hword := U.fromWord_wf_rel.relHom S
      ({ bitsLE := bitsL } : Word 256) ({ bitsLE := bitsR } : Word 256)
      hbits
    exact WF.Rel.mono hword (by
      intro _ _ _ _ h
      exact h.2)

private theorem intLCEq_nsmul (k : Nat) {lv rv : WF.Valuation}
    {left right : LC ℤ} (h : WF.LCEq lv.int rv.int left right) :
    WF.LCEq lv.int rv.int (k • left) (k • right) := by
  unfold WF.LCEq at h ⊢
  simpa only [LC.eval_nsmul] using congrArg (k • ·) h

private theorem fixedInnerDigit_wfRel {lv rv : WF.Valuation}
    {width : Nat} {left right : Vector (LC ℤ) (width - 1)}
    (hwidth : 8 ≤ width) (h : IntLCVector.WFRel lv rv left right) :
    WF.LCEq lv.int rv.int
      (∑ i : Fin 7, (2 ^ i.val : Int) • left[i])
      (∑ i : Fin 7, (2 ^ i.val : Int) • right[i]) := by
  unfold WF.LCEq
  simp only [LC.eval_sum, LC.eval_smul]
  apply Finset.sum_congr rfl
  intro i _
  have hi := h ⟨i.val, by omega⟩
  unfold WF.LCEq at hi
  simpa using congrArg (fun value : Int => 2 ^ i.val * value) hi

private theorem fixedOuterDigit_wfRel {lv rv : WF.Valuation}
    {width : Nat} {leftBits rightBits : Vector (LC ℤ) width}
    {leftMagnitude rightMagnitude : Vector (LC ℤ) (width - 1)}
    (hwidth : 8 ≤ width)
    (hbits : IntLCVector.WFRel lv rv leftBits rightBits)
    (hmagnitude : IntLCVector.WFRel lv rv leftMagnitude rightMagnitude) :
    WF.LCEq lv.int rv.int
      ((∑ i : Fin (width - 8), (2 ^ i.val : Int) •
          leftMagnitude[i.val + 7]) +
        (2 ^ (width - 8) : Int) • leftBits[width - 1])
      ((∑ i : Fin (width - 8), (2 ^ i.val : Int) •
          rightMagnitude[i.val + 7]) +
        (2 ^ (width - 8) : Int) • rightBits[width - 1]) := by
  apply WF.eval_add
  · simp only [LC.eval_sum, LC.eval_smul]
    apply Finset.sum_congr rfl
    intro i _
    have hi := hmagnitude ⟨i.val + 7, by omega⟩
    unfold WF.LCEq at hi
    simpa using congrArg (fun value : Int => 2 ^ i.val * value) hi
  · exact intLCEq_nsmul (2 ^ (width - 8))
      (hbits ⟨width - 1, by omega⟩)

theorem lookupFixedFactored_wf_aux (offset width : Nat)
    (hwidth : 8 ≤ width) :
    WF.GadgetSpec IntLCVector.WFRel
      (fun bits => lookupFixedFactored offset width hwidth bits)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold lookupFixedFactored
  apply WF.GadgetSpec.bind_rule
    (left := left) (right := right)
    (xnorMagnitudeBits_wf_aux width (by omega))
  · intro lv rv h
    exact h
  · intro B magnitudeL magnitudeR hmagnitude
    apply WF.GadgetSpec.bind_rule
      (left := ∑ i : Fin 7, (2 ^ i.val : Int) • magnitudeL[i])
      (right := ∑ i : Fin 7, (2 ^ i.val : Int) • magnitudeR[i])
      (indicators_wf_aux 128)
    · intro lv rv hB
      exact fixedInnerDigit_wfRel hwidth (hmagnitude lv rv hB).2
    · intro C innerL innerR hinner
      let outerL :=
        (∑ i : Fin (width - 8), (2 ^ i.val : Int) •
          magnitudeL[i.val + 7]) +
        (2 ^ (width - 8) : Int) • left[width - 1]
      let outerR :=
        (∑ i : Fin (width - 8), (2 ^ i.val : Int) •
          magnitudeR[i.val + 7]) +
        (2 ^ (width - 8) : Int) • right[width - 1]
      apply WF.GadgetSpec.bind_rule
        (left := outerL) (right := outerR)
        (indicators_wf_aux (2 ^ (width - 7)))
      · intro lv rv hC
        have hi := hinner lv rv hC
        have hm := hmagnitude lv rv hi.1
        exact fixedOuterDigit_wfRel hwidth hm.1 hm.2
      · intro D outerSelL outerSelR houter
        let rawL := combWindowValue left
        let rawR := combWindowValue right
        let table := fixedMagnitudeTable offset (2 ^ (width - 1))
        apply WF.GadgetSpec.bind_rule
          (left := rawL) (right := rawR)
          (materializeFixedCoordinate_wf_aux (fun d => Reference.xNat
            table[(signedMagnitudeIndex width d)]!))
        · intro lv rv hD
          have ho := houter lv rv hD
          have hi := hinner lv rv ho.1
          have hm := hmagnitude lv rv hi.1
          exact combWindowValue_wfRel hm.1
        · intro E XL XR hX
          apply WF.GadgetSpec.bind_rule
            (left := rawL) (right := rawR)
            (materializeFixedCoordinate_wf_aux (fun d =>
              let y := Reference.yNat
                table[(signedMagnitudeIndex width d)]!
              if 2 ^ (width - 1) ≤ d then y else base.modulus - y))
          · intro lv rv hE
            have hx := hX lv rv hE
            have ho := houter lv rv hx.1
            have hi := hinner lv rv ho.1
            have hm := hmagnitude lv rv hi.1
            exact combWindowValue_wfRel hm.1
          · intro F YL YR hY
            apply WF.GadgetSpec.bind_rule_direct
              (left := (innerL, outerSelL, XL, YL))
              (right := (innerR, outerSelR, XR, YR))
              (assertFactoredCoordinates_wf_aux width table)
            · intro lv rv hF
              have hy := hY lv rv hF
              have hx := hX lv rv hy.1
              have ho := houter lv rv hx.1
              have hi := hinner lv rv ho.1
              exact ⟨hi.2, ho.2, hx.2, hy.2⟩
            · intro _ _
              apply WF.Rel.pure
              intro lv rv hF
              have hy := hY lv rv hF.1
              have hx := hX lv rv hy.1
              exact ⟨⟨rfl, hx.2.1⟩, ⟨rfl, hy.2.1⟩,
                by simp [WF.LCEq]⟩

theorem lookupFixed12_wf_aux (window : Nat) (hwindow : window < 8) :
    WF.GadgetSpec Modular.Elem.ScalarWFRel
      (fun k => lookupFixed12 k window hwindow)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold lookupFixed12
  apply WF.Rel.mono
    ((lookupFixedFactored_wf_aux (12 * window) 12 (by omega)).relHom
      (fun lv rv => Modular.Elem.ScalarWFRel lv rv left right)
      (combWindowBits left (12 * window) 12 (by omega))
      (combWindowBits right (12 * window) 12 (by omega)) (by
        intro lv rv h
        exact combWindowBits_wfRel h (12 * window) 12 (by omega)))
  intro _ _ _ _ h
  exact h.2

theorem lookupFixed13_wf_aux (window : Nat) (hwindow : window < 12) :
    WF.GadgetSpec Modular.Elem.ScalarWFRel
      (fun k => lookupFixed13 k window hwindow)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold lookupFixed13
  apply WF.Rel.mono
    ((lookupFixedFactored_wf_aux (96 + 13 * window) 13 (by omega)).relHom
      (fun lv rv => Modular.Elem.ScalarWFRel lv rv left right)
      (combWindowBits left (96 + 13 * window) 13 (by omega))
      (combWindowBits right (96 + 13 * window) 13 (by omega)) (by
        intro lv rv h
        exact combWindowBits_wfRel h (96 + 13 * window) 13 (by omega)))
  intro _ _ _ _ h
  exact h.2

theorem lookupFixedTop_wf_aux :
    WF.GadgetSpec Modular.Elem.ScalarWFRel lookupFixedTop
      AffineSlope.Point.WFRel := by
  wfgen' using [indicators_wf_aux]
    unfold [lookupFixedTop, AffineSlope.Point.WFRel,
      Modular.Lazy.Rep.WFRel]
  case vc1 =>
    rename_i hpost hB
    have hout := (hpost leftVal rightVal hB).2
    unfold WF.LCEq
    simp only [LC.eval_sum, LC.eval_smul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [LC.eval_nsmul]
    rw [hout.2 i]
  case vc2 =>
    rename_i hpost hB
    have hout := (hpost leftVal rightVal hB).2
    unfold WF.LCEq
    simp only [LC.eval_sum, LC.eval_smul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [LC.eval_nsmul]
    rw [hout.2 i]
  case vc3 =>
    rename_i hscalar
    apply WF.eval_add
    · exact combWindowValue_wfRel
        (combWindowBits_wfRel hscalar 252 4 (by omega))
    · exact intLCEq_nsmul 16 (hscalar.2 ⟨0, by omega⟩)
  all_goals simp_all [WF.LCEq, U.intVal]

def SignedRadix32VariableStepInput.WFRel :
    WF.Post (Fn × Radix32Table × AffineSlope.Point) :=
  fun lv rv left right =>
    Modular.Elem.ScalarWFRel lv rv left.1 right.1 ∧
    Radix32Table.WFRel lv rv left.2.1 right.2.1 ∧
    AffineSlope.Point.WFRel lv rv left.2.2 right.2.2

theorem signedRadix32VariableStep_wf_aux (i : Nat) (hi : i < 255) :
    WF.GadgetSpec SignedRadix32VariableStepInput.WFRel
      (fun input => signedRadix32VariableStep input.1 input.2.1
        i hi input.2.2)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold signedRadix32VariableStep
  apply WF.GadgetSpec.bind_rule
    (left := left.2.2) (right := right.2.2)
    AffineSlope.doubleComplete_wf_aux
  · intro lv rv h
    exact h.2.2
  · intro B accDL accDR hdouble
    by_cases hq : (254 - i) % 5 = 0
    · simp only [dif_pos hq]
      apply WF.GadgetSpec.bind_rule
        (left := boothDigit left.1 ((254 - i) / 5) (by omega))
        (right := boothDigit right.1 ((254 - i) / 5) (by omega))
        signedDigitIndicators_wf_aux
      · intro lv rv hB
        have hd := hdouble lv rv hB
        exact boothDigit_wfRel hd.1.1 ((254 - i) / 5) (by omega)
      · intro C digitL digitR hdigit
        apply WF.GadgetSpec.bind_rule
          (left := (digitL, left.2.1))
          (right := (digitR, right.2.1))
          selectSignedRadix32Point_wf_aux
        · intro lv rv hC
          have hdig := hdigit lv rv hC
          have hd := hdouble lv rv hdig.1
          exact ⟨hdig.2, hd.1.2.1⟩
        · intro D qL qR hqPoint
          apply WF.GadgetSpec.direct_rule
            (left := (accDL, qL)) (right := (accDR, qR))
            AffineSlope.addCompleteCollapsed_wf_aux
          intro lv rv hD
          have hq' := hqPoint lv rv hD
          have hdig := hdigit lv rv hq'.1
          have hd := hdouble lv rv hdig.1
          exact ⟨hd.2, hq'.2⟩
    · simp only [dif_neg hq]
      apply WF.Rel.pure
      intro lv rv hB
      exact (hdouble lv rv hB).2

def SignedRadix32VariableInput.WFRel : WF.Post (Fn × Projective) :=
  fun lv rv left right =>
    Modular.Elem.ScalarWFRel lv rv left.1 right.1 ∧
    Projective.WFRel lv rv left.2 right.2

theorem signedRadix32VariableMul_wf_aux :
    WF.GadgetSpec SignedRadix32VariableInput.WFRel
      (fun input => signedRadix32VariableMul input.1 input.2)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold signedRadix32VariableMul
  apply WF.GadgetSpec.bind_rule materializeRadix32Multiples_wf_aux
  · intro lv rv h
    exact h.2
  · intro B tableL tableR htable
    apply WF.GadgetSpec.bind_rule
      (left := boothDigit left.1 51 (by omega))
      (right := boothDigit right.1 51 (by omega))
      signedDigitIndicators_wf_aux
    · intro lv rv hB
      have ht := htable lv rv hB
      exact boothDigit_wfRel ht.1.1 51 (by omega)
    · intro C digitL digitR hdigit
      apply WF.GadgetSpec.bind_rule
        (left := (digitL, tableL)) (right := (digitR, tableR))
        selectSignedRadix32Point_wf_aux
      · intro lv rv hC
        have hd := hdigit lv rv hC
        have ht := htable lv rv hd.1
        exact ⟨hd.2, ht.2⟩
      · intro D initialL initialR hinitial
        refine WF.Rel.mono (WF.Rel.foldRange_rule
          (I := fun lv rv leftAcc rightAcc =>
            D lv rv ∧ AffineSlope.Point.WFRel lv rv leftAcc rightAcc)
          ?_ ?_) ?_
        · intro lv rv hD
          exact ⟨hD, (hinitial lv rv hD).2⟩
        · intro j hj P accL accR hacc
          have hinput : ∀ lv rv, P lv rv →
              SignedRadix32VariableStepInput.WFRel lv rv
                (left.1, tableL, accL) (right.1, tableR, accR) := by
            intro lv rv hP
            have ha := hacc lv rv hP
            have hi := hinitial lv rv ha.1
            have hd := hdigit lv rv hi.1
            have ht := htable lv rv hd.1
            exact ⟨ht.1.1, ht.2, ha.2⟩
          have hstep := (signedRadix32VariableStep_wf_aux j hj.2.1).relHom P
            (left.1, tableL, accL) (right.1, tableR, accR) hinput
          exact WF.Rel.mono hstep (by
            intro lv rv outL outR hpost
            exact ⟨hpost.1, (hacc lv rv hpost.1).1, hpost.2⟩)
        · intro _ _ _ _ hpost
          exact hpost.2

theorem fixedBaseComb12_wf_aux :
    WF.GadgetSpec Modular.Elem.ScalarWFRel fixedBaseComb12
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold fixedBaseComb12
  apply WF.GadgetSpec.bind_rule
    (left := left) (right := right) (lookupFixed12_wf_aux 0 (by omega))
  · intro lv rv h
    exact h
  · intro B initialL initialR hinitial
    refine WF.Rel.mono (WF.Rel.foldRange_rule
      (I := fun lv rv leftAcc rightAcc =>
        B lv rv ∧ AffineSlope.Point.WFRel lv rv leftAcc rightAcc)
      ?_ ?_) ?_
    · intro lv rv hB
      exact ⟨hB, (hinitial lv rv hB).2⟩
    · intro i hi P accL accR hacc
      have hscalar : ∀ lv rv, P lv rv →
          Modular.Elem.ScalarWFRel lv rv left right := by
        intro lv rv hP
        have ha := hacc lv rv hP
        exact (hinitial lv rv ha.1).1
      have hlookup := (lookupFixed12_wf_aux (i + 1) (by grind)).relHom P
        left right hscalar
      apply hlookup.bind
      intro C pointL pointR hpoint
      have hadd := AffineSlope.addIncompleteChecked_wf_aux.relHom C
        (accL, pointL) (accR, pointR) (by
          intro lv rv hC
          have hp := hpoint lv rv hC
          have ha := hacc lv rv hp.1
          exact ⟨ha.2, hp.2⟩)
      exact WF.Rel.mono hadd (by
        intro lv rv outL outR hpost
        have hp := hpoint lv rv hpost.1
        exact ⟨hp.1, (hacc lv rv hp.1).1, hpost.2⟩)
    · intro _ _ _ _ hpost
      exact hpost.2

def FixedBaseComb13Input.WFRel : WF.Post (Fn × AffineSlope.Point) :=
  fun lv rv left right =>
    Modular.Elem.ScalarWFRel lv rv left.1 right.1 ∧
    AffineSlope.Point.WFRel lv rv left.2 right.2

theorem fixedBaseComb13_wf_aux :
    WF.GadgetSpec FixedBaseComb13Input.WFRel
      (fun input => fixedBaseComb13 input.1 input.2)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold fixedBaseComb13
  refine WF.Rel.mono (WF.Rel.foldRange_rule
    (I := fun lv rv leftAcc rightAcc =>
      FixedBaseComb13Input.WFRel lv rv left right ∧
        AffineSlope.Point.WFRel lv rv leftAcc rightAcc)
    ?_ ?_) ?_
  · intro lv rv h
    exact ⟨h, h.2⟩
  · intro i hi P accL accR hacc
    have hscalar : ∀ lv rv, P lv rv →
        Modular.Elem.ScalarWFRel lv rv left.1 right.1 := by
      intro lv rv hP
      exact (hacc lv rv hP).1.1
    have hlookup := (lookupFixed13_wf_aux i (by
      simpa using hi.2.1)).relHom P
      left.1 right.1 hscalar
    apply hlookup.bind
    intro C pointL pointR hpoint
    have hadd := AffineSlope.addCompleteCollapsed_wf_aux.relHom C
      (accL, pointL) (accR, pointR) (by
        intro lv rv hC
        have hp := hpoint lv rv hC
        have ha := hacc lv rv hp.1
        exact ⟨ha.2, hp.2⟩)
    exact WF.Rel.mono hadd (by
      intro lv rv outL outR hpost
      have hp := hpoint lv rv hpost.1
      exact ⟨hp.1, (hacc lv rv hp.1).1, hpost.2⟩)
  · intro _ _ _ _ hpost
    exact hpost.2

theorem fixedBaseComb13Incomplete_wf_aux :
    WF.GadgetSpec FixedBaseComb13Input.WFRel
      (fun input => fixedBaseComb13Incomplete input.1 input.2)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold fixedBaseComb13Incomplete
  refine WF.Rel.mono (WF.Rel.foldRange_rule
    (I := fun lv rv leftAcc rightAcc =>
      FixedBaseComb13Input.WFRel lv rv left right ∧
        AffineSlope.Point.WFRel lv rv leftAcc rightAcc)
    ?_ ?_) ?_
  · intro lv rv h
    exact ⟨h, h.2⟩
  · intro i hi P accL accR hacc
    have hscalar : ∀ lv rv, P lv rv →
        Modular.Elem.ScalarWFRel lv rv left.1 right.1 := by
      intro lv rv hP
      exact (hacc lv rv hP).1.1
    have hlookup := (lookupFixed13_wf_aux i (by
      simpa using hi.2.1)).relHom P
      left.1 right.1 hscalar
    apply hlookup.bind
    intro C pointL pointR hpoint
    have hadd := AffineSlope.addIncompleteChecked_wf_aux.relHom C
      (accL, pointL) (accR, pointR) (by
        intro lv rv hC
        have hp := hpoint lv rv hC
        have ha := hacc lv rv hp.1
        exact ⟨ha.2, hp.2⟩)
    exact WF.Rel.mono hadd (by
      intro lv rv outL outR hpost
      have hp := hpoint lv rv hpost.1
      exact ⟨hp.1, (hacc lv rv hp.1).1, hpost.2⟩)
  · intro _ _ _ _ hpost
    exact hpost.2

theorem fixedBaseCombComplete_wf_aux :
    WF.GadgetSpec Modular.Elem.ScalarWFRel fixedBaseCombComplete
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold fixedBaseCombComplete
  apply WF.GadgetSpec.bind_rule
    (left := left) (right := right) fixedBaseComb12_wf_aux
  · intro lv rv h
    exact h
  · intro B acc12L acc12R hacc12
    apply WF.GadgetSpec.bind_rule
      (left := (left, acc12L)) (right := (right, acc12R))
      fixedBaseComb13Incomplete_wf_aux
    · intro lv rv hB
      have h12 := hacc12 lv rv hB
      exact ⟨h12.1, h12.2⟩
    · intro C accL accR hacc
      apply WF.GadgetSpec.bind_rule
        (left := left) (right := right) lookupFixedTop_wf_aux
      · intro lv rv hC
        have ha := hacc lv rv hC
        have h12 := hacc12 lv rv ha.1
        exact h12.1
      · intro D topL topR htop
        apply WF.GadgetSpec.direct_rule
          (left := (accL, topL)) (right := (accR, topR))
          AffineSlope.addCompleteCollapsed_wf_aux
        intro lv rv hD
        have ht := htop lv rv hD
        have ha := hacc lv rv ht.1
        exact ⟨ha.2, ht.2⟩

theorem fixedCombVerificationSum_wf_aux :
    WF.GadgetSpec PreparedVerification.WFRel fixedCombVerificationSum
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold fixedCombVerificationSum
  apply WF.GadgetSpec.bind_rule
    (left := (left.u2, left.q)) (right := (right.u2, right.q))
    signedRadix32VariableMul_wf_aux
  · intro lv rv h
    exact ⟨h.2.1, h.2.2.1⟩
  · intro B variableL variableR hvariable
    apply WF.GadgetSpec.bind_rule
      (left := left.u1) (right := right.u1) fixedBaseCombComplete_wf_aux
    · intro lv rv hB
      exact (hvariable lv rv hB).1.1
    · intro C fixedL fixedR hfixed
      apply WF.GadgetSpec.direct_rule
        (left := (variableL, fixedL)) (right := (variableR, fixedR))
        AffineSlope.addCompleteCollapsed_wf_aux
      intro lv rv hC
      have hf := hfixed lv rv hC
      have hv := hvariable lv rv hf.1
      exact ⟨hv.2, hf.2⟩

theorem fixedCombVerificationX_wf_aux :
    WF.GadgetSpec PreparedVerification.WFRel fixedCombVerificationX
      AffineSlope.XPoint.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold fixedCombVerificationX
  apply WF.GadgetSpec.bind_rule
    (left := (left.u2, left.q)) (right := (right.u2, right.q))
    signedRadix32VariableMul_wf_aux
  · intro lv rv h
    exact ⟨h.2.1, h.2.2.1⟩
  · intro B variableL variableR hvariable
    apply WF.GadgetSpec.bind_rule
      (left := left.u1) (right := right.u1) fixedBaseCombComplete_wf_aux
    · intro lv rv hB
      exact (hvariable lv rv hB).1.1
    · intro C fixedL fixedR hfixed
      apply WF.GadgetSpec.direct_rule
        (left := (variableL, fixedL)) (right := (variableR, fixedR))
        AffineSlope.addCompleteCollapsedX_wf_aux
      intro lv rv hC
      have hf := hfixed lv rv hC
      have hv := hvariable lv rv hf.1
      exact ⟨hv.2, hf.2⟩

theorem fixedCombVerificationCanonicalX_wf_aux :
    WF.GadgetSpec PreparedVerification.WFRel fixedCombVerificationCanonicalX
      AffineSlope.CanonicalXPoint.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold fixedCombVerificationCanonicalX
  apply WF.GadgetSpec.bind_rule
    (left := (left.u2, left.q)) (right := (right.u2, right.q))
    signedRadix32VariableMul_wf_aux
  · intro lv rv h
    exact ⟨h.2.1, h.2.2.1⟩
  · intro B variableL variableR hvariable
    apply WF.GadgetSpec.bind_rule
      (left := left.u1) (right := right.u1) fixedBaseCombComplete_wf_aux
    · intro lv rv hB
      exact (hvariable lv rv hB).1.1
    · intro C fixedL fixedR hfixed
      apply WF.GadgetSpec.direct_rule
        (left := (variableL, fixedL)) (right := (variableR, fixedR))
        AffineSlope.addCompleteCollapsedCanonicalX_wf_aux
      intro lv rv hC
      have hf := hfixed lv rv hC
      have hv := hvariable lv rv hf.1
      exact ⟨hv.2, hf.2⟩

theorem fixedCombVerificationDirectTerminal_wf_aux :
    WF.GadgetSpec PreparedVerification.WFRel
      fixedCombVerificationDirectTerminal (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold fixedCombVerificationDirectTerminal
  apply WF.GadgetSpec.bind_rule
    (left := (left.u2, left.q)) (right := (right.u2, right.q))
    signedRadix32VariableMul_wf_aux
  · intro lv rv h
    exact ⟨h.2.1, h.2.2.1⟩
  · intro B variableL variableR hvariable
    apply WF.GadgetSpec.bind_rule
      (left := left.u1) (right := right.u1) fixedBaseCombComplete_wf_aux
    · intro lv rv hB
      exact (hvariable lv rv hB).1.1
    · intro C fixedL fixedR hfixed
      apply WF.GadgetSpec.direct_rule
        (left := (left.r, variableL, fixedL))
        (right := (right.r, variableR, fixedR))
        addCompleteCollapsedDirectTerminal_wf_aux
      intro lv rv hC
      have hf := hfixed lv rv hC
      have hv := hvariable lv rv hf.1
      exact ⟨hv.1.2.2.2, hv.2, hf.2⟩

theorem fixedCombVerificationDeltaBlock_wf_aux :
    WF.GadgetSpec DeltaBlockWF.PreparedVerification.BlockWFRel
      fixedCombVerificationDeltaBlock (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold fixedCombVerificationDeltaBlock
  apply WF.GadgetSpec.bind_rule
    (left := (left.u2, left.q)) (right := (right.u2, right.q))
    signedRadix32VariableMul_wf_aux
  · intro lv rv h
    exact ⟨h.2.1, h.2.2.1⟩
  · intro B variableL variableR hvariable
    apply WF.GadgetSpec.bind_rule
      (left := left.u1) (right := right.u1) fixedBaseCombComplete_wf_aux
    · intro lv rv hB
      exact (hvariable lv rv hB).1.1
    · intro C fixedL fixedR hfixed
      apply WF.GadgetSpec.direct_rule
        (left := (left.r, variableL, fixedL))
        (right := (right.r, variableR, fixedR))
        DeltaBlockWF.addCompleteCollapsedDeltaBlock_wf_aux
      intro lv rv hC
      have hf := hfixed lv rv hC
      have hv := hvariable lv rv hf.1
      exact ⟨hv.1.2.2.2, hv.2, hf.2⟩

theorem computeVerificationSum_radix32_wf_aux :
    WF.GadgetSpec PreparedVerification.WFRel computeVerificationSum
      AffineSlope.Point.WFRel := by
  unfold computeVerificationSum
  exact fixedCombVerificationSum_wf_aux

theorem computeVerificationX_radix32_wf_aux :
    WF.GadgetSpec PreparedVerification.WFRel computeVerificationX
      AffineSlope.XPoint.WFRel := by
  unfold computeVerificationX
  exact fixedCombVerificationX_wf_aux

theorem computeVerificationCanonicalX_radix32_wf_aux :
    WF.GadgetSpec PreparedVerification.WFRel computeVerificationCanonicalX
      AffineSlope.CanonicalXPoint.WFRel := by
  unfold computeVerificationCanonicalX
  exact fixedCombVerificationCanonicalX_wf_aux

theorem computeVerificationDirectTerminal_radix32_wf_aux :
    WF.GadgetSpec PreparedVerification.WFRel
      computeVerificationDirectTerminal (fun _ _ _ _ => True) := by
  unfold computeVerificationDirectTerminal
  exact fixedCombVerificationDirectTerminal_wf_aux

theorem computeVerificationDeltaBlock_radix32_wf_aux :
    WF.GadgetSpec DeltaBlockWF.PreparedVerification.BlockWFRel
      computeVerificationDeltaBlock (fun _ _ _ _ => True) := by
  unfold computeVerificationDeltaBlock
  exact fixedCombVerificationDeltaBlock_wf_aux

theorem finishVerification_radix32_wf_aux :
    WF.GadgetSpec DeltaBlockWF.PreparedVerification.BlockWFRel
      finishVerification
      (fun _ _ _ _ => True) := by
  unfold finishVerification
  exact computeVerificationDeltaBlock_radix32_wf_aux

theorem verifyDigest_radix32_wf_aux :
    WF.GadgetSpec VerifyInput.WFRel
      (fun input => verifyDigest input.1 input.2.1 input.2.2.1 input.2.2.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold verifyDigest
  apply WF.GadgetSpec.bind_rule_direct
    (left := (left.2.1, left.2.2.1, left.2.2.2))
    (right := (right.2.1, right.2.2.1, right.2.2.2))
    canonicalizeInput_wf_aux
  · intro lv rv h
    exact h.2
  · intro inputL inputR
    apply WF.GadgetSpec.bind_rule_direct
      (left := (left.1, inputL)) (right := (right.1, inputR))
      DeltaBlockWF.prepareVerification_block_wf_aux
    · intro lv rv h
      exact ⟨h.1.1, h.2⟩
    · intro preparedL preparedR
      apply WF.GadgetSpec.direct_rule
        (left := preparedL) (right := preparedR)
        finishVerification_radix32_wf_aux
      intro lv rv h
      exact h.2

theorem verifyDigestFromBits_radix32_wf_aux :
    WF.GadgetSpec VerifyDigestBits.WFRel verifyDigestFromBits
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold verifyDigestFromBits
  apply WF.GadgetSpec.bind_rule_direct
    (left := verifyDigestInputWords left)
    (right := verifyDigestInputWords right) mapM_fromWord_wf_full
  · intro lv rv h
    exact verifyDigestInputWords_wf h
  · intro valuesL valuesR
    apply WF.GadgetSpec.direct_rule
      (left := (valuesL[0], ⟨valuesL[1], valuesL[2]⟩,
        ⟨valuesL[3], valuesL[4]⟩, ⟨valuesL[5], valuesL[6]⟩))
      (right := (valuesR[0], ⟨valuesR[1], valuesR[2]⟩,
        ⟨valuesR[3], valuesR[4]⟩, ⟨valuesR[5], valuesR[6]⟩))
      verifyDigest_radix32_wf_aux
    intro lv rv h
    exact ⟨h.2 0, h.2 1, h.2 2, h.2 3, h.2 4, h.2 5, h.2 6⟩

end Freigen.F2Z.Examples.EcdsaP256
