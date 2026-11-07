import Freigen.F2Z.Examples.EcdsaP256.Radix32Production
import Freigen.F2Z.Examples.EcdsaP256.WF
import Freigen.F2Z.Examples.P256.IncompleteWF

/-! Quotient well-formedness proofs for the signed radix-32 verifier. -/

namespace Freigen.F2Z.Examples.EcdsaP256

open P256

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def Radix32Table.WFRel (lv rv : WF.Valuation)
    (left right : Radix32Table) : Prop :=
  WF.VectorRel AffineSlope.Point.WFRel lv rv left.low right.low ∧
  AffineSlope.Point.WFRel lv rv left.p16 right.p16

def SignedDigit.WFRel (lv rv : WF.Valuation)
    (left right : SignedDigit) : Prop :=
  U.FullWFRel lv rv left.oneHot right.oneHot

private theorem signedDigit_value_wfRel {lv rv : WF.Valuation}
    {left right : SignedDigit} (h : SignedDigit.WFRel lv rv left right) :
    WF.LCEq lv.int rv.int left.value right.value := by
  unfold SignedDigit.value WF.LCEq
  simp only [LC.eval_sum, LC.eval_nsmul, LC.eval_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [h.2 i]

private theorem signedDigit_magnitude_wfRel {lv rv : WF.Valuation}
    {left right : SignedDigit} (h : SignedDigit.WFRel lv rv left right) :
    WF.LCEq lv.int rv.int left.magnitude right.magnitude := by
  unfold SignedDigit.magnitude WF.LCEq
  simp only [LC.eval_sum, LC.eval_nsmul, LC.eval_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [h.2 i]

private theorem signedDigit_negative_wfRel {lv rv : WF.Valuation}
    {left right : SignedDigit} (h : SignedDigit.WFRel lv rv left right) :
    WF.LCEq lv.int rv.int left.negative right.negative := by
  unfold SignedDigit.negative WF.LCEq
  simp only [LC.eval_sum, LC.eval_nsmul, LC.eval_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [h.2 i]

private theorem signedDigit_isSixteen_wfRel {lv rv : WF.Valuation}
    {left right : SignedDigit} (h : SignedDigit.WFRel lv rv left right) :
    WF.LCEq lv.int rv.int left.isSixteen right.isSixteen := by
  unfold SignedDigit.isSixteen WF.LCEq
  simp only [LC.eval_sum, LC.eval_nsmul, LC.eval_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [h.2 i]

private theorem lceq_nsmul (k : Nat) {lv rv : WF.Valuation}
    {left right : LC ℤ} (h : WF.LCEq lv.int rv.int left right) :
    WF.LCEq lv.int rv.int (k • left) (k • right) := by
  unfold WF.LCEq at h ⊢
  simpa only [LC.eval_nsmul] using congrArg (k • ·) h

theorem materializeRadix32Multiples_wf_aux :
    WF.GadgetSpec Projective.WFRel materializeRadix32Multiples
      Radix32Table.WFRel := by
  wfgen' using [AffineSlope.addIncompleteChecked_wf_aux,
    AffineSlope.doubleComplete_wf_aux]
    unfold [materializeRadix32Multiples, addRadix32Multiple, doubleMultiple]
  case vc1 =>
    rename_i B1 p2L p2R h1 B2 p3L p3R h2 B3 p4L p4R h3
      B4 p5L p5R h4 B5 p6L p6R h5 B6 p7L p7R h6
      B7 p8L p8R h7 B8 p9L p9R h8 B9 p10L p10R h9
      B10 p11L p11R h10 B11 p12L p12R h11
      B12 p13L p13R h12 B13 p14L p14R h13
      B14 p15L p15R h14 h15 hB
    have r16 := h15 leftVal rightVal hB
    have r15 := h14 leftVal rightVal r16.1
    have r14 := h13 leftVal rightVal r15.1
    have r13 := h12 leftVal rightVal r14.1
    have r12 := h11 leftVal rightVal r13.1
    have r11 := h10 leftVal rightVal r12.1
    have r10 := h9 leftVal rightVal r11.1
    have r9 := h8 leftVal rightVal r10.1
    have r8 := h7 leftVal rightVal r9.1
    have r7 := h6 leftVal rightVal r8.1
    have r6 := h5 leftVal rightVal r7.1
    have r5 := h4 leftVal rightVal r6.1
    have r4 := h3 leftVal rightVal r5.1
    have r3 := h2 leftVal rightVal r4.1
    have r2 := h1 leftVal rightVal r3.1
    have r1 := AffineSlope.ofElems_wfRel r2.1.1 r2.1.2.1
    constructor
    · intro i
      fin_cases i <;>
        simp only [Fin.getElem_fin, Vector.getElem_mk,
          ← Array.getElem_toList, List.getElem_cons_zero,
          List.getElem_cons_succ] <;>
        first
        | exact AffineSlope.infinity_wfRel leftVal rightVal
        | exact r1
        | exact r2.2
        | exact r3.2
        | exact r4.2
        | exact r5.2
        | exact r6.2
        | exact r7.2
        | exact r8.2
        | exact r9.2
        | exact r10.2
        | exact r11.2
        | exact r12.2
        | exact r13.2
        | exact r14.2
        | exact r15.2
    · exact r16.2
  all_goals
    have hprojective : Projective.WFRel leftVal rightVal left right := by
      grind (ematch := 100)
    exact AffineSlope.ofElems_wfRel hprojective.1 hprojective.2.1

theorem signedDigitIndicators_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : LC ℤ) => WF.LCEq lv.int rv.int left right)
      signedDigitIndicators SignedDigit.WFRel := by
  wfgen' using [indicators_wf_aux]
    unfold [signedDigitIndicators, SignedDigit.WFRel]
  all_goals simp_all [WF.LCEq]
  all_goals try rfl

theorem selectBit_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : LC ℤ × LC ℤ × LC ℤ) =>
        WF.LCEq lv.int rv.int left.1 right.1 ∧
        WF.LCEq lv.int rv.int left.2.1 right.2.1 ∧
        WF.LCEq lv.int rv.int left.2.2 right.2.2)
      (fun input => selectBit input.1 input.2.1 input.2.2)
      (fun lv rv left right => WF.LCEq lv.int rv.int left right) := by
  wfgen' using [U.fromWord_wf_rel] unfold [selectBit]
  case vc1 =>
    rename_i h
    change WF.LCEq leftVal.bool rightVal.bool outL[i] outR[i]
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt
  all_goals simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

theorem applyPointSign_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : LC ℤ × AffineSlope.Point) =>
        WF.LCEq lv.int rv.int left.1 right.1 ∧
        AffineSlope.Point.WFRel lv rv left.2 right.2)
      (fun input => applyPointSign input.1 input.2)
      AffineSlope.Point.WFRel := by
  wfgen' using [U.fromWord_wf_rel]
    unfold [applyPointSign, AffineSlope.Point.WFRel,
      Modular.Lazy.Rep.WFRel]
  case vc1 =>
    rename_i h
    change WF.LCEq leftVal.bool rightVal.bool outL[i] outR[i]
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt
  all_goals simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

private theorem signedNonzeroMagnitudeGate_wfRel {lv rv : WF.Valuation}
    {left right : SignedDigit} (h : SignedDigit.WFRel lv rv left right)
    (i : Nat) (hi : i < 16) :
    WF.LCEq lv.int rv.int
      (signedNonzeroMagnitudeGate left i hi)
      (signedNonzeroMagnitudeGate right i hi) := by
  unfold signedNonzeroMagnitudeGate
  exact WF.eval_add (h.2 ⟨15 - i, by omega⟩)
    (h.2 ⟨17 + i, by omega⟩)

private theorem radix32MagnitudeValues_wfRel {lv rv : WF.Valuation}
    {lowL lowR : Vector AffineSlope.Rep 16}
    {p16L p16R : AffineSlope.Rep}
    (hlow : WF.VectorRel Modular.Lazy.Rep.WFRel lv rv lowL lowR)
    (hp16 : Modular.Lazy.Rep.WFRel lv rv p16L p16R) :
    WF.VectorRel Modular.Lazy.Rep.WFRel lv rv
      (radix32MagnitudeValues lowL p16L)
      (radix32MagnitudeValues lowR p16R) := by
  intro i
  simp only [radix32MagnitudeValues, Vector.getElem_ofFn, Fin.getElem_fin]
  split
  · exact hlow ⟨i.val, by omega⟩
  · exact hp16

private theorem radix32MagnitudeFlags_wfRel {lv rv : WF.Valuation}
    {lowL lowR : Vector (LC ℤ) 16} {p16L p16R : LC ℤ}
    (hlow : WF.VectorRel (fun lv rv left right =>
      WF.LCEq lv.int rv.int left right) lv rv lowL lowR)
    (hp16 : WF.LCEq lv.int rv.int p16L p16R) :
    WF.VectorRel (fun lv rv left right =>
      WF.LCEq lv.int rv.int left right) lv rv
      (radix32MagnitudeValues lowL p16L)
      (radix32MagnitudeValues lowR p16R) := by
  intro i
  simp only [radix32MagnitudeValues, Vector.getElem_ofFn, Fin.getElem_fin]
  split
  · exact hlow ⟨i.val, by omega⟩
  · exact hp16

def SignedMagnitudeLookupInput.WFRel :
    WF.Post (SignedDigit × Vector AffineSlope.Rep 17) :=
  fun lv rv left right =>
    SignedDigit.WFRel lv rv left.1 right.1 ∧
    WF.VectorRel Modular.Lazy.Rep.WFRel lv rv left.2 right.2

theorem lookupSignedMagnitudeRep_wf_aux :
    WF.GadgetSpec SignedMagnitudeLookupInput.WFRel
      (fun input => lookupSignedMagnitudeRep input.1 input.2)
      Modular.Lazy.Rep.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold lookupSignedMagnitudeRep
  have hargs : ∀ lv rv,
      SignedMagnitudeLookupInput.WFRel lv rv left right →
      WF.ArgsEq lv rv
        (signedMagnitudeLookupArgs left.1.magnitude
          (left.2.map (·.intVal)))
        (signedMagnitudeLookupArgs right.1.magnitude
          (right.2.map (·.intVal))) := by
    intro lv rv h
    have hm := signedDigit_magnitude_wfRel h.1
    unfold WF.LCEq at hm
    have hv (i : Fin 17) := (h.2 i).2
    unfold WF.LCEq at hv
    unfold WF.ArgsEq signedMagnitudeLookupArgs
    simp only [WF.evalArgs, Vector.getElem_map]
    simp only [HList.cons.injEq, hm]
    exact ⟨trivial, hv 0, hv 1, hv 2, hv 3, hv 4, hv 5, hv 6,
      hv 7, hv 8, hv 9, hv 10, hv 11, hv 12, hv 13, hv 14,
      hv 15, hv 16, trivial⟩
  apply WF.Rel.hint
  · exact hargs
  · intro lv rv h
    exact WF.HintRel.of_argsEq signedMagnitudeLookupRepHint (hargs lv rv h)
  · intro bitsL bitsR
    let S : WF.Assumption := fun lv rv =>
      SignedMagnitudeLookupInput.WFRel lv rv left right ∧ ∃ values,
        WF.HintReturns (signedMagnitudeLookupRepHint
          (WF.evalArgs lv (signedMagnitudeLookupArgs left.1.magnitude
            (left.2.map (·.intVal))))) values ∧
        WF.HintReturns (signedMagnitudeLookupRepHint
          (WF.evalArgs rv (signedMagnitudeLookupArgs right.1.magnitude
            (right.2.map (·.intVal))))) values ∧
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
    apply hword.bind
    intro B wordL wordR hwordRel
    apply WF.Rel.assertR1C
    · intro lv rv hB
      exact (hwordRel lv rv hB).1.1.1.2 ⟨16, by omega⟩
    · intro lv rv hB
      have h := hwordRel lv rv hB
      exact WF.eval_sub h.2.1 (h.1.1.2 0).2
    · intro _ _ _
      simp [WF.LCEq]
    have hfold := WF.Rel.foldRange_rule
      (xs := [:16]) (initL := ()) (initR := ())
      (stepL := fun i hi _ =>
        assertR1C (signedNonzeroMagnitudeGate left.1 i hi.2.1)
          (wordL.intVal -
            (left.2[i + 1]'(Nat.succ_lt_succ hi.2.1)).intVal) 0)
      (stepR := fun i hi _ =>
        assertR1C (signedNonzeroMagnitudeGate right.1 i hi.2.1)
          (wordR.intVal -
            (right.2[i + 1]'(Nat.succ_lt_succ hi.2.1)).intVal) 0)
      (I := fun lv rv (_ _ : Unit) =>
        SignedMagnitudeLookupInput.WFRel lv rv left right ∧
        U.WFRel lv rv wordL wordR) (by
          intro lv rv hB
          have hw := hwordRel lv rv hB
          exact ⟨hw.1.1, hw.2⟩) (by
          intro i hi P _ _ hrel
          apply WF.Rel.assertR1C_pure
          · intro lv rv hP
            exact signedNonzeroMagnitudeGate_wfRel (hrel lv rv hP).1.1
              i hi.2.1
          · intro lv rv hP
            have h := hrel lv rv hP
            have hi' : i < 16 := hi.2.1
            exact WF.eval_sub h.2.1 (h.1.2 ⟨i + 1, by omega⟩).2
          · intro _ _ _
            simp [WF.LCEq]
          · intro lv rv hP
            exact ⟨hP, hrel lv rv hP⟩)
    apply hfold.bind
    intro C _ _ hunit
    apply WF.Rel.pure
    intro lv rv hC
    have h := hunit lv rv hC
    exact ⟨rfl, h.2.1⟩

def SignedMagnitudeFlagLookupInput.WFRel :
    WF.Post (SignedDigit × Vector (LC ℤ) 17) :=
  fun lv rv left right =>
    SignedDigit.WFRel lv rv left.1 right.1 ∧
    WF.VectorRel (fun lv rv l r => WF.LCEq lv.int rv.int l r)
      lv rv left.2 right.2

theorem lookupSignedMagnitudeFlag_wf_aux :
    WF.GadgetSpec SignedMagnitudeFlagLookupInput.WFRel
      (fun input => lookupSignedMagnitudeFlag input.1 input.2)
      (fun lv rv left right => WF.LCEq lv.int rv.int left right) := by
  unfold WF.GadgetSpec
  intro left right
  unfold lookupSignedMagnitudeFlag
  have hargs : ∀ lv rv,
      SignedMagnitudeFlagLookupInput.WFRel lv rv left right →
      WF.ArgsEq lv rv
        (signedMagnitudeLookupArgs left.1.magnitude left.2)
        (signedMagnitudeLookupArgs right.1.magnitude right.2) := by
    intro lv rv h
    have hm := signedDigit_magnitude_wfRel h.1
    unfold WF.LCEq at hm
    have hv (i : Fin 17) := h.2 i
    unfold WF.LCEq at hv
    unfold WF.ArgsEq signedMagnitudeLookupArgs
    simp only [WF.evalArgs]
    simp only [HList.cons.injEq, hm]
    exact ⟨trivial, hv 0, hv 1, hv 2, hv 3, hv 4, hv 5, hv 6,
      hv 7, hv 8, hv 9, hv 10, hv 11, hv 12, hv 13, hv 14,
      hv 15, hv 16, trivial⟩
  apply WF.Rel.hint
  · exact hargs
  · intro lv rv h
    exact WF.HintRel.of_argsEq signedMagnitudeLookupFlagHint
      (hargs lv rv h)
  · intro bitsL bitsR
    let S : WF.Assumption := fun lv rv =>
      SignedMagnitudeFlagLookupInput.WFRel lv rv left right ∧ ∃ values,
        WF.HintReturns (signedMagnitudeLookupFlagHint
          (WF.evalArgs lv
            (signedMagnitudeLookupArgs left.1.magnitude left.2))) values ∧
        WF.HintReturns (signedMagnitudeLookupFlagHint
          (WF.evalArgs rv
            (signedMagnitudeLookupArgs right.1.magnitude right.2))) values ∧
        WF.RealizesBools lv.bool bitsL values ∧
        WF.RealizesBools rv.bool bitsR values
    have hbit : ∀ lv rv, S lv rv →
        WF.LCEq lv.bool rv.bool bitsL[0] bitsR[0] := by
      intro lv rv h
      exact Modular.Aux.WF.lceq_of_common_realizes
        (Modular.Aux.WF.common_realizes_of_hint h) 0 (by omega)
    have hout := WF.Rel.f2z_rel hbit
    apply hout.bind
    intro B outL outR houtRel
    apply WF.Rel.assertR1C
    · intro lv rv hB
      exact (houtRel lv rv hB).1.1.1.2 ⟨16, by omega⟩
    · intro lv rv hB
      have h := houtRel lv rv hB
      exact WF.eval_sub h.2 (h.1.1.2 0)
    · intro _ _ _
      simp [WF.LCEq]
    have hfold := WF.Rel.foldRange_rule
      (xs := [:16]) (initL := ()) (initR := ())
      (stepL := fun i hi _ =>
        assertR1C (signedNonzeroMagnitudeGate left.1 i hi.2.1)
          (outL - left.2[i + 1]'(Nat.succ_lt_succ hi.2.1)) 0)
      (stepR := fun i hi _ =>
        assertR1C (signedNonzeroMagnitudeGate right.1 i hi.2.1)
          (outR - right.2[i + 1]'(Nat.succ_lt_succ hi.2.1)) 0)
      (I := fun lv rv (_ _ : Unit) =>
        SignedMagnitudeFlagLookupInput.WFRel lv rv left right ∧
        WF.LCEq lv.int rv.int outL outR) (by
          intro lv rv hB
          have ho := houtRel lv rv hB
          exact ⟨ho.1.1, ho.2⟩) (by
          intro i hi P _ _ hrel
          apply WF.Rel.assertR1C_pure
          · intro lv rv hP
            exact signedNonzeroMagnitudeGate_wfRel (hrel lv rv hP).1.1
              i hi.2.1
          · intro lv rv hP
            have h := hrel lv rv hP
            have hi' : i < 16 := hi.2.1
            exact WF.eval_sub h.2 (h.1.2 ⟨i + 1, by omega⟩)
          · intro _ _ _
            simp [WF.LCEq]
          · intro lv rv hP
            exact ⟨hP, hrel lv rv hP⟩)
    apply hfold.bind
    intro C _ _ hunit
    apply WF.Rel.pure
    intro lv rv hC
    exact (hunit lv rv hC).2

theorem selectRadix32Magnitude_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : SignedDigit × Radix32Table) =>
        SignedDigit.WFRel lv rv left.1 right.1 ∧
        Radix32Table.WFRel lv rv left.2 right.2)
      (fun input => selectRadix32Magnitude input.1 input.2)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold selectRadix32Magnitude
  apply WF.GadgetSpec.bind_rule
    (left := (left.1,
      radix32MagnitudeValues (left.2.low.map (·.X)) left.2.p16.X))
    (right := (right.1,
      radix32MagnitudeValues (right.2.low.map (·.X)) right.2.p16.X))
    lookupSignedMagnitudeRep_wf_aux
  · intro lv rv h
    exact ⟨h.1, radix32MagnitudeValues_wfRel
      (fun i => by
        simpa [Vector.getElem_map] using
          (h.2.1 i).1)
      h.2.2.1⟩
  · intro B XL XR hX
    apply WF.GadgetSpec.bind_rule
      (left := (left.1,
        radix32MagnitudeValues (left.2.low.map (·.Y)) left.2.p16.Y))
      (right := (right.1,
        radix32MagnitudeValues (right.2.low.map (·.Y)) right.2.p16.Y))
      lookupSignedMagnitudeRep_wf_aux
    · intro lv rv hB
      have hx := hX lv rv hB
      exact ⟨hx.1.1, radix32MagnitudeValues_wfRel
        (fun i => by
          simpa [Vector.getElem_map] using
            (hx.1.2.1 i).2.1)
        hx.1.2.2.2.1⟩
    · intro C YL YR hY
      apply WF.GadgetSpec.bind_rule
        (left := (left.1, radix32MagnitudeValues
          (left.2.low.map (·.infinity)) left.2.p16.infinity))
        (right := (right.1, radix32MagnitudeValues
          (right.2.low.map (·.infinity)) right.2.p16.infinity))
        lookupSignedMagnitudeFlag_wf_aux
      · intro lv rv hC
        have hy := hY lv rv hC
        have hx := hX lv rv hy.1
        exact ⟨hx.1.1, radix32MagnitudeFlags_wfRel
          (fun i => by
            simpa [Vector.getElem_map] using
              (hx.1.2.1 i).2.2)
          hx.1.2.2.2.2⟩
      · intro D infinityL infinityR hinfinity
        apply WF.Rel.pure
        intro lv rv hD
        have hi := hinfinity lv rv hD
        have hy := hY lv rv hi.1
        have hx := hX lv rv hy.1
        exact ⟨hx.2, hy.2, hi.2⟩

theorem selectSignedRadix32Point_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : SignedDigit × Radix32Table) =>
        SignedDigit.WFRel lv rv left.1 right.1 ∧
        Radix32Table.WFRel lv rv left.2 right.2)
      (fun input => selectSignedRadix32Point input.1 input.2)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold selectSignedRadix32Point
  apply WF.GadgetSpec.bind_rule
    (left := left) (right := right) selectRadix32Magnitude_wf_aux
  · intro lv rv h
    exact h
  · intro B pointL pointR hpoint
    apply WF.GadgetSpec.direct_rule
      (left := (left.1.negative, pointL))
      (right := (right.1.negative, pointR)) applyPointSign_wf_aux
    intro lv rv hB
    have hp := hpoint lv rv hB
    exact ⟨signedDigit_negative_wfRel hp.1.1, hp.2⟩

def SignedRadix32Input.WFRel : WF.Post (Fn × Fn × Projective) :=
  JointScalarInput.WFRel

private theorem windowValue_wfRel {lv rv : WF.Valuation}
    {left right : Fn} (h : Modular.Elem.ScalarWFRel lv rv left right)
    (start width : Nat) (hfit : start + width ≤ 256) :
    WF.LCEq lv.int rv.int
      (windowValue left start width hfit)
      (windowValue right start width hfit) := by
  unfold windowValue WF.LCEq
  simp only [LC.eval_sum, LC.eval_nsmul]
  apply Finset.sum_congr rfl
  intro j _
  have hb := h.2 ⟨start + j.val, by omega⟩
  unfold WF.LCEq at hb
  exact congrArg (2 ^ j.val • ·) hb

theorem boothDigit_wfRel {lv rv : WF.Valuation}
    {left right : Fn} (h : Modular.Elem.ScalarWFRel lv rv left right)
    (i : Nat) (hi : i < 52) :
    WF.LCEq lv.int rv.int
      (boothDigit left i hi) (boothDigit right i hi) := by
  unfold boothDigit
  split
  · apply WF.eval_sub
    · apply WF.eval_add
      · exact windowValue_wfRel h (5 * i) 4 (by omega)
      · split
        · simp [WF.LCEq]
        · exact windowValue_wfRel h (5 * i - 1) 1 (by omega)
    · exact lceq_nsmul 16 (windowValue_wfRel h (5 * i + 4) 1 (by omega))
  · exact WF.eval_add
      (windowValue_wfRel h 255 1 (by omega))
      (windowValue_wfRel h 254 1 (by omega))

def SignedRadix32StepInput.WFRel :
    WF.Post (Fn × Fn × Radix32Table × AffineSlope.Point) :=
  fun lv rv left right =>
    Modular.Elem.ScalarWFRel lv rv left.1 right.1 ∧
    Modular.Elem.ScalarWFRel lv rv left.2.1 right.2.1 ∧
    Radix32Table.WFRel lv rv left.2.2.1 right.2.2.1 ∧
    AffineSlope.Point.WFRel lv rv left.2.2.2 right.2.2.2

def GeneratorTailInput.WFRel : WF.Post (Fn × AffineSlope.Point) :=
  fun lv rv left right =>
    Modular.Elem.ScalarWFRel lv rv left.1 right.1 ∧
    AffineSlope.Point.WFRel lv rv left.2 right.2

theorem generatorTail_wf_aux (exponent : Nat)
    (hfit : exponent % 8 = 0 → exponent + 8 ≤ 256) :
    WF.GadgetSpec GeneratorTailInput.WFRel
      (fun input => if _h : exponent % 8 = 0 then do
        let g ← lookupGeneratorByte
          (windowValue input.1 exponent 8 (hfit _h))
        AffineSlope.addCompleteCollapsed input.2 g
      else pure input.2)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  by_cases h : exponent % 8 = 0
  · simp only [dif_pos h]
    apply WF.GadgetSpec.bind_rule
      (left := windowValue left.1 exponent 8 (hfit h))
      (right := windowValue right.1 exponent 8 (hfit h))
      lookupGeneratorByte_wf_aux
    · intro lv rv hB
      exact windowValue_wfRel hB.1 exponent 8 (hfit h)
    · intro B gL gR hg
      apply WF.GadgetSpec.direct_rule
        (left := (left.2, gL)) (right := (right.2, gR))
        AffineSlope.addCompleteCollapsed_wf_aux
      intro lv rv hB
      have h' := hg lv rv hB
      exact ⟨h'.1.2, h'.2⟩
  · simp only [dif_neg h]
    apply WF.Rel.pure
    intro _ _ hB
    exact hB.2

theorem signedRadix32Step_wf_aux (i : Nat) (hi : i < 255) :
    WF.GadgetSpec SignedRadix32StepInput.WFRel
      (fun input => signedRadix32Step input.1 input.2.1 input.2.2.1
        i hi input.2.2.2)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold signedRadix32Step
  apply WF.GadgetSpec.bind_rule
    (left := left.2.2.2) (right := right.2.2.2)
    AffineSlope.doubleComplete_wf_aux
  · intro lv rv h
    exact h.2.2.2
  · intro B accDL accDR hdouble
    by_cases hq : (254 - i) % 5 = 0
    · simp only [dif_pos hq]
      apply WF.GadgetSpec.bind_rule
        (left := boothDigit left.2.1 ((254 - i) / 5) (by omega))
        (right := boothDigit right.2.1 ((254 - i) / 5) (by omega))
        signedDigitIndicators_wf_aux
      · intro lv rv hB
        have hd := hdouble lv rv hB
        exact boothDigit_wfRel hd.1.2.1 ((254 - i) / 5) (by omega)
      · intro C digitL digitR hdigit
        apply WF.GadgetSpec.bind_rule
          (left := (digitL, left.2.2.1))
          (right := (digitR, right.2.2.1))
          selectSignedRadix32Point_wf_aux
        · intro lv rv hC
          have hdig := hdigit lv rv hC
          have hd := hdouble lv rv hdig.1
          exact ⟨hdig.2, hd.1.2.2.1⟩
        · intro D qL qR hqPoint
          apply WF.GadgetSpec.bind_rule
            (left := (accDL, qL)) (right := (accDR, qR))
            AffineSlope.addCompleteCollapsed_wf_aux
          · intro lv rv hD
            have hq' := hqPoint lv rv hD
            have hdig := hdigit lv rv hq'.1
            have hd := hdouble lv rv hdig.1
            exact ⟨hd.2, hq'.2⟩
          · intro E accQL accQR hadd
            apply WF.GadgetSpec.direct_rule
              (left := (left.1, accQL)) (right := (right.1, accQR))
              (generatorTail_wf_aux (254 - i) (by intro hg; omega))
            intro lv rv hE
            have ha := hadd lv rv hE
            have hq' := hqPoint lv rv ha.1
            have hdig := hdigit lv rv hq'.1
            have hd := hdouble lv rv hdig.1
            exact ⟨hd.1.1, ha.2⟩
    · simp only [dif_neg hq]
      apply WF.GadgetSpec.direct_rule
        (left := (left.1, accDL)) (right := (right.1, accDR))
        (generatorTail_wf_aux (254 - i) (by intro hg; omega))
      intro lv rv hB
      have hd := hdouble lv rv hB
      exact ⟨hd.1.1, hd.2⟩

theorem signedRadix32JointScalarMul_wf_aux :
    WF.GadgetSpec SignedRadix32Input.WFRel
      (fun input => signedRadix32JointScalarMul input.1 input.2.1 input.2.2)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold signedRadix32JointScalarMul
  apply WF.GadgetSpec.bind_rule materializeRadix32Multiples_wf_aux
  · intro lv rv h
    exact h.2.2
  · intro B tableL tableR htable
    apply WF.GadgetSpec.bind_rule
      (left := boothDigit left.2.1 51 (by omega))
      (right := boothDigit right.2.1 51 (by omega))
      signedDigitIndicators_wf_aux
    · intro lv rv hB
      have ht := htable lv rv hB
      exact boothDigit_wfRel ht.1.2.1 51 (by omega)
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
              SignedRadix32StepInput.WFRel lv rv
                (left.1, left.2.1, tableL, accL)
                (right.1, right.2.1, tableR, accR) := by
            intro lv rv hP
            have ha := hacc lv rv hP
            have hi := hinitial lv rv ha.1
            have hd := hdigit lv rv hi.1
            have ht := htable lv rv hd.1
            exact ⟨ht.1.1, ht.1.2.1, ht.2, ha.2⟩
          have hstep := (signedRadix32Step_wf_aux j hj.2.1).relHom P
            (left.1, left.2.1, tableL, accL)
            (right.1, right.2.1, tableR, accR) hinput
          exact WF.Rel.mono hstep (by
            intro lv rv outL outR hpost
            exact ⟨hpost.1, (hacc lv rv hpost.1).1, hpost.2⟩)
        · intro lv rv outL outR hpost
          exact hpost.2

end Freigen.F2Z.Examples.EcdsaP256
