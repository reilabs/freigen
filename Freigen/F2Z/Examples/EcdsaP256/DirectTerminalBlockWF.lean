import Freigen.F2Z.Examples.EcdsaP256.DirectTerminalBlockImpl
import Freigen.F2Z.Examples.EcdsaP256.WF

namespace Freigen.F2Z.Examples.EcdsaP256.DeltaBlockWF

open P256
open Modular

set_option maxRecDepth 100000

def delta : Nat := base.modulus - scalar.modulus

def scalarBitsFrom (r : Fn) (start : Nat) : LC ℤ :=
  ∑ i : Fin 256, if start ≤ i.val then
    2 ^ (i.val - start) • r.val.intBits[i] else 0

def selectedBlockBitsFrom (selected : U 8) (start : Nat) : LC ℤ :=
  ∑ i : Fin 8, if start ≤ i.val then
    2 ^ (i.val - start) • selected.intBits[i] else 0

def outerSelectedDeltaBlockFrom (outer : U 16) (start : Nat) : LC ℤ :=
  ∑ i : Fin 16,
    (delta / 2 ^ (8 * i.val + start) % 2 ^ (8 - start)) •
      outer.intBits[i]

structure Input where
  r : Fn
  qScalar : U 1
  outer : U 16
  inner : U 8
  selectedBlock : U 8

def Input.WFRel : WF.Post Input :=
  fun lv rv left right =>
    Modular.Elem.FullWFRel lv rv left.r right.r ∧
    U.ScalarWFRel lv rv left.qScalar right.qScalar ∧
    U.ScalarWFRel lv rv left.outer right.outer ∧
    U.ScalarWFRel lv rv left.inner right.inner ∧
    U.ScalarWFRel lv rv left.selectedBlock right.selectedBlock

def checkOuter (input : Input) (i : Fin 16) : Circuit Unit := do
  let start := 8 * i.val
  let expected := input.selectedBlock.intVal + LC.ofConst
    (2 ^ 8 * (delta / 2 ^ (start + 8) : Nat) : Int)
  assertR1C input.outer.intBits[i]
    (scalarBitsFrom input.r start - expected) 0

def checkInner (input : Input) (j : Fin 8) : Circuit Unit := do
  assertR1C input.inner.intBits[j]
    (selectedBlockBitsFrom input.selectedBlock j -
      (outerSelectedDeltaBlockFrom input.outer j - 1)) 0

def comparator (input : Input) : Circuit Unit := do
  assertR1C 1
    ((∑ i : Fin 16, input.outer.intBits[i]) - input.qScalar.intVal) 0
  assertR1C 1
    ((∑ i : Fin 8, input.inner.intBits[i]) - input.qScalar.intVal) 0
  for h:i in [0:16] do
    checkOuter input ⟨i, h.2.1⟩
  for h:j in [0:8] do
    checkInner input ⟨j, h.2.1⟩

private theorem eval_fin_sum {n : Nat} {lv rv : WF.Valuation}
    {left right : Fin n → LC ℤ}
    (h : ∀ i, WF.LCEq lv.int rv.int (left i) (right i)) :
    WF.LCEq lv.int rv.int (∑ i, left i) (∑ i, right i) := by
  simp only [WF.LCEq, LC.eval_sum]
  exact Finset.sum_congr rfl fun i _ => h i

private theorem scalarBitsFrom_wf {lv rv : WF.Valuation}
    {left right : Fn} (h : Modular.Elem.FullWFRel lv rv left right)
    (start : Nat) :
    WF.LCEq lv.int rv.int (scalarBitsFrom left start)
      (scalarBitsFrom right start) := by
  apply eval_fin_sum
  intro i
  split
  · exact WF.eval_nsmul _ (h.2 i)
  · rfl

private theorem selectedBlockBitsFrom_wf {lv rv : WF.Valuation}
    {left right : U 8} (h : U.ScalarWFRel lv rv left right)
    (start : Nat) :
    WF.LCEq lv.int rv.int (selectedBlockBitsFrom left start)
      (selectedBlockBitsFrom right start) := by
  apply eval_fin_sum
  intro i
  split
  · exact WF.eval_nsmul _ (h.2 i)
  · rfl

private theorem outerSelectedDeltaBlockFrom_wf {lv rv : WF.Valuation}
    {left right : U 16} (h : U.ScalarWFRel lv rv left right)
    (start : Nat) :
    WF.LCEq lv.int rv.int (outerSelectedDeltaBlockFrom left start)
      (outerSelectedDeltaBlockFrom right start) := by
  apply eval_fin_sum
  intro i
  exact WF.eval_nsmul _ (h.2 i)

theorem checkOuter_wf_aux (i : Fin 16) :
    WF.GadgetSpec Input.WFRel (fun input => checkOuter input i)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold checkOuter
  apply WF.Rel.assertR1C_pure
  · intro lv rv h
    exact h.2.2.1.2 i
  · intro lv rv h
    apply WF.eval_sub (scalarBitsFrom_wf h.1 (8 * i))
    exact WF.eval_add h.2.2.2.2.1 rfl
  · intro _ _ _
    rfl
  · intro _ _ _
    trivial

theorem checkInner_wf_aux (j : Fin 8) :
    WF.GadgetSpec Input.WFRel (fun input => checkInner input j)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold checkInner
  apply WF.Rel.assertR1C_pure
  · intro lv rv h
    exact h.2.2.2.1.2 j
  · intro lv rv h
    exact WF.eval_sub (selectedBlockBitsFrom_wf h.2.2.2.2 j)
      (WF.eval_sub (outerSelectedDeltaBlockFrom_wf h.2.2.1 j) rfl)
  · intro _ _ _
    rfl
  · intro _ _ _
    trivial

theorem comparator_wf_aux :
    WF.GadgetSpec Input.WFRel comparator (fun _ _ _ _ => True) := by
  wfgen' using [checkOuter_wf_aux, checkInner_wf_aux]
    unfold [comparator]
  case inv1 => exact fun _ _ _ _ => True
  case vc1 =>
    simp_all [Input.WFRel, U.ScalarWFRel, WF.LCEq]
  case vc2 =>
    intro a ha A unitL unitR hA
    let i : Fin 16 := ⟨a, ha.2.1⟩
    have hs := (checkOuter_wf_aux i).relHom A left right
      (fun lv rv h => (hA lv rv h).1)
    apply WF.Rel.mono hs
    intro lv rv _ _ h
    exact ⟨h.1, hA lv rv h.1⟩
  case vc3 =>
    intro A unitL unitR hA
    apply WF.Rel.forIn'_range_yield_bind
      (R := fun lv rv _ _ => Input.WFRel lv rv left right)
    · intro lv rv h
      exact (hA lv rv h).1
    · intro a ha A' unitL unitR hA'
      let j : Fin 8 := ⟨a, ha.2.1⟩
      have hs := (checkInner_wf_aux j).relHom A' left right
        (fun lv rv h => hA' lv rv h)
      apply WF.Rel.mono hs
      intro lv rv _ _ h
      exact ⟨h.1, hA' lv rv h.1⟩
    · intro B outL outR hout
      apply WF.Rel.pure
      intro _ _ _
      trivial

abbrev blockHint := deltaBlockTerminalHint

private theorem baseQWord_get (bits : Vector (LC Bool) 34) (i : Fin 1) :
    (deltaBlockBaseQWord bits)[i] = bits[0] := by
  change (Vector.ofFn fun _ : Fin 1 => bits[0])[i] = bits[0]
  simp

private theorem scalarQWord_get (bits : Vector (LC Bool) 34) (i : Fin 1) :
    (deltaBlockScalarQWord bits)[i] = bits[1] := by
  change (Vector.ofFn fun _ : Fin 1 => bits[1])[i] = bits[1]
  simp

private theorem outerWord_get (bits : Vector (LC Bool) 34) (i : Fin 16) :
    (deltaBlockOuterWord bits)[i] = bits[i.val + 2] := by
  change (Vector.ofFn fun j : Fin 16 => bits[j.val + 2])[i] = _
  simp

private theorem innerWord_get (bits : Vector (LC Bool) 34) (i : Fin 8) :
    (deltaBlockInnerWord bits)[i] = bits[i.val + 18] := by
  change (Vector.ofFn fun j : Fin 8 => bits[j.val + 18])[i] = _
  simp

private theorem selectedWord_get (bits : Vector (LC Bool) 34) (i : Fin 8) :
    (deltaBlockSelectedWord bits)[i] = bits[i.val + 26] := by
  change (Vector.ofFn fun j : Fin 8 => bits[j.val + 26])[i] = _
  simp

structure Witnesses where
  qBase : U 1
  qScalar : U 1
  outer : U 16
  inner : U 8
  selectedBlock : U 8

def Witnesses.WFRel : WF.Post Witnesses :=
  fun lv rv left right =>
    U.ScalarWFRel lv rv left.qBase right.qBase ∧
    U.ScalarWFRel lv rv left.qScalar right.qScalar ∧
    U.ScalarWFRel lv rv left.outer right.outer ∧
    U.ScalarWFRel lv rv left.inner right.inner ∧
    U.ScalarWFRel lv rv left.selectedBlock right.selectedBlock

def SelectInput.WFRel :
    WF.Post (Fn × AffineSlope.Point × AffineSlope.Point ×
      AffineSlope.AddControl × AffineSlope.Rep) :=
  fun lv rv left right =>
    Modular.Elem.FullWFRel lv rv left.1 right.1 ∧
    AffineSlope.Point.WFRel lv rv left.2.1 right.2.1 ∧
    AffineSlope.Point.WFRel lv rv left.2.2.1 right.2.2.1 ∧
    AffineSlope.AddControl.WFRel lv rv
      left.2.2.2.1 right.2.2.2.1 ∧
    Modular.Lazy.Rep.WFRel lv rv
      left.2.2.2.2 right.2.2.2.2

def materializeWitnesses
    (input : Fn × AffineSlope.Point × AffineSlope.Point ×
      AffineSlope.AddControl × AffineSlope.Rep) : Circuit Witnesses := do
  let bits ← hint
    h![input.2.2.2.1.active, input.2.1.infinity,
      input.2.2.1.infinity, input.2.2.2.2.intVal,
      input.2.1.X.intVal, input.2.2.1.X.intVal, input.1.val.intVal]
    blockHint
  let qBase ← U.fromWord (deltaBlockBaseQWord bits)
  let qScalar ← U.fromWord (deltaBlockScalarQWord bits)
  let outer ← U.fromWord (deltaBlockOuterWord bits)
  let inner ← U.fromWord (deltaBlockInnerWord bits)
  let selectedBlock ← U.fromWord (deltaBlockSelectedWord bits)
  pure ⟨qBase, qScalar, outer, inner, selectedBlock⟩

theorem materializeWitnesses_wf_aux :
    WF.GadgetSpec SelectInput.WFRel materializeWitnesses
      Witnesses.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold materializeWitnesses
  have hargs : ∀ lv rv, SelectInput.WFRel lv rv left right →
      WF.ArgsEq lv rv
        h![left.2.2.2.1.active, left.2.1.infinity,
          left.2.2.1.infinity, left.2.2.2.2.intVal,
          left.2.1.X.intVal, left.2.2.1.X.intVal, left.1.val.intVal]
        h![right.2.2.2.1.active, right.2.1.infinity,
          right.2.2.1.infinity, right.2.2.2.2.intVal,
          right.2.1.X.intVal, right.2.2.1.X.intVal,
          right.1.val.intVal] := by
    intro lv rv h
    simp_all [WF.ArgsEq, WF.evalArgs, SelectInput.WFRel,
      Modular.Elem.FullWFRel, U.FullWFRel, U.WFRel,
      AffineSlope.Point.WFRel, AffineSlope.AddControl.WFRel,
      Modular.Lazy.Rep.WFRel, WF.LCEq]
  apply WF.Rel.hint
  · exact hargs
  · intro lv rv h
    exact WF.HintRel.of_argsEq blockHint (hargs lv rv h)
  · intro bitsL bitsR
    let S : WF.Assumption := fun lv rv =>
      SelectInput.WFRel lv rv left right ∧ ∃ values,
        WF.HintReturns (blockHint (WF.evalArgs lv
          h![left.2.2.2.1.active, left.2.1.infinity,
            left.2.2.1.infinity, left.2.2.2.2.intVal,
            left.2.1.X.intVal, left.2.2.1.X.intVal,
            left.1.val.intVal])) values ∧
        WF.HintReturns (blockHint (WF.evalArgs rv
          h![right.2.2.2.1.active, right.2.1.infinity,
            right.2.2.1.infinity, right.2.2.2.2.intVal,
            right.2.1.X.intVal, right.2.2.1.X.intVal,
            right.1.val.intVal])) values ∧
        WF.RealizesBools lv.bool bitsL values ∧
        WF.RealizesBools rv.bool bitsR values
    have hbits : ∀ lv rv, S lv rv → ∀ i : Fin 34,
        WF.LCEq lv.bool rv.bool bitsL[i] bitsR[i] := by
      intro lv rv h i
      exact Modular.Aux.WF.lceq_of_common_realizes
        (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt
    have hqBase := U.fromWord_wf_scalar.relHom S
      (deltaBlockBaseQWord bitsL) (deltaBlockBaseQWord bitsR) (by
        intro lv rv h i
        rw [baseQWord_get, baseQWord_get]
        exact hbits lv rv h ⟨0, by omega⟩)
    apply hqBase.bind
    intro A qBaseL qBaseR hqBaseRel
    have hqScalar := U.fromWord_wf_scalar.relHom A
      (deltaBlockScalarQWord bitsL) (deltaBlockScalarQWord bitsR) (by
        intro lv rv h i
        rw [scalarQWord_get, scalarQWord_get]
        exact hbits lv rv (hqBaseRel lv rv h).1 ⟨1, by omega⟩)
    apply hqScalar.bind
    intro B qScalarL qScalarR hqScalarRel
    have houter := U.fromWord_wf_scalar.relHom B
      (deltaBlockOuterWord bitsL) (deltaBlockOuterWord bitsR) (by
        intro lv rv h i
        rw [outerWord_get, outerWord_get]
        exact hbits lv rv
          (hqBaseRel lv rv (hqScalarRel lv rv h).1).1
          ⟨i.val + 2, by omega⟩)
    apply houter.bind
    intro C outerL outerR houterRel
    have hinner := U.fromWord_wf_scalar.relHom C
      (deltaBlockInnerWord bitsL) (deltaBlockInnerWord bitsR) (by
        intro lv rv h i
        have ho := houterRel lv rv h
        have hq := hqScalarRel lv rv ho.1
        rw [innerWord_get, innerWord_get]
        exact hbits lv rv (hqBaseRel lv rv hq.1).1
          ⟨i.val + 18, by omega⟩)
    apply hinner.bind
    intro D innerL innerR hinnerRel
    have hselected := U.fromWord_wf_scalar.relHom D
      (deltaBlockSelectedWord bitsL) (deltaBlockSelectedWord bitsR) (by
        intro lv rv h i
        have hi := hinnerRel lv rv h
        have ho := houterRel lv rv hi.1
        have hq := hqScalarRel lv rv ho.1
        rw [selectedWord_get, selectedWord_get]
        exact hbits lv rv (hqBaseRel lv rv hq.1).1
          ⟨i.val + 26, by omega⟩)
    apply hselected.bind
    intro E selectedL selectedR hselectedRel
    apply WF.Rel.pure
    intro lv rv h
    have hs := hselectedRel lv rv h
    have hi := hinnerRel lv rv hs.1
    have ho := houterRel lv rv hi.1
    have hq := hqScalarRel lv rv ho.1
    have hb := hqBaseRel lv rv hq.1
    exact ⟨hb.2, hq.2, ho.2, hi.2, hs.2⟩

def selectOutput (r : Fn) (P Q : AffineSlope.Point)
    (control : AffineSlope.AddControl)
    (candidateX : AffineSlope.Rep) : Circuit Unit := do
  let bothInfinity ← AffineSlope.andBit P.infinity Q.infinity
  let w ← materializeWitnesses (r, P, Q, control, candidateX)
  let represented := r.val.intVal +
    scalar.modulus • w.qScalar.intVal + base.modulus • w.qBase.intVal
  assertR1C control.active (candidateX.intVal - represented) 0
  assertR1C P.infinity (Q.X.intVal - represented) 0
  assertR1C (Q.infinity - bothInfinity) (P.X.intVal - represented) 0
  comparator ⟨r, w.qScalar, w.outer, w.inner, w.selectedBlock⟩
  let finiteOpposite ← AffineSlope.and3Bit control.sameX
    control.oppositeY control.finite
  let infinity := bothInfinity + finiteOpposite
  assertR1C 0 0 infinity

theorem selectOutput_wf_aux :
    WF.GadgetSpec SelectInput.WFRel
      (fun input => selectOutput input.1 input.2.1 input.2.2.1
        input.2.2.2.1 input.2.2.2.2)
      (fun _ _ _ _ => True) := by
  wfgen' using [AffineSlope.andBit_wf_aux, materializeWitnesses_wf_aux,
    comparator_wf_aux, AffineSlope.and3Bit_wf_aux]
    unfold [selectOutput]
  case vc1 =>
    apply WF.Rel.assertR1C_pure
    all_goals simp_all [WF.LCEq, LC.eval_add]
    case hc => grind
  case vc2 =>
    simp_all [Input.WFRel, SelectInput.WFRel, Witnesses.WFRel,
      Modular.Elem.FullWFRel, U.FullWFRel]

def addComplete (r : Fn) (P Q : AffineSlope.Point) : Circuit Unit := do
  let control ← AffineSlope.classifyAdd P Q
  let candidateX ← AffineSlope.addCandidateCollapsedX P Q control
  selectOutput r P Q control candidateX

theorem addComplete_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Fn × AffineSlope.Point × AffineSlope.Point) =>
        Modular.Elem.FullWFRel lv rv left.1 right.1 ∧
        AffineSlope.Point.WFRel lv rv left.2.1 right.2.1 ∧
        AffineSlope.Point.WFRel lv rv left.2.2 right.2.2)
      (fun input => addComplete input.1 input.2.1 input.2.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold addComplete
  apply WF.GadgetSpec.bind_rule
    (left := (left.2.1, left.2.2))
    (right := (right.2.1, right.2.2))
    AffineSlope.classifyAdd_wf_aux
  · intro lv rv h
    exact ⟨h.2.1, h.2.2⟩
  · intro B controlL controlR hcontrol
    apply WF.GadgetSpec.bind_rule
      (left := (left.2.1, left.2.2, controlL))
      (right := (right.2.1, right.2.2, controlR))
      AffineSlope.addCandidateCollapsedX_wf_aux
    · intro lv rv hB
      have hc := hcontrol lv rv hB
      exact ⟨hc.1.2.1, hc.1.2.2, hc.2⟩
    · intro C candidateL candidateR hcandidate
      apply WF.GadgetSpec.direct_rule
        (left := (left.1, left.2.1, left.2.2, controlL, candidateL))
        (right := (right.1, right.2.1, right.2.2, controlR, candidateR))
        selectOutput_wf_aux
      intro lv rv hC
      have hx := hcandidate lv rv hC
      have hc := hcontrol lv rv hx.1
      exact ⟨hc.1.1, hc.1.2.1, hc.1.2.2, hc.2, hx.2⟩

def DeltaBlockComparatorInput.WFRel : WF.Post DeltaBlockComparatorInput :=
  fun lv rv left right =>
    Modular.Elem.FullWFRel lv rv left.r right.r ∧
    U.ScalarWFRel lv rv left.qScalar right.qScalar ∧
    U.ScalarWFRel lv rv left.outer right.outer ∧
    U.ScalarWFRel lv rv left.inner right.inner ∧
    U.ScalarWFRel lv rv left.selectedBlock right.selectedBlock

private def DeltaBlockComparatorInput.toWFInput
    (input : DeltaBlockComparatorInput) : Input :=
  ⟨input.r, input.qScalar, input.outer, input.inner, input.selectedBlock⟩

theorem deltaBlockComparator_wf_aux :
    WF.GadgetSpec DeltaBlockComparatorInput.WFRel deltaBlockComparator
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  change WF.Rel (fun _ _ _ _ => True)
    (fun lv rv => Input.WFRel lv rv
      (DeltaBlockComparatorInput.toWFInput left)
      (DeltaBlockComparatorInput.toWFInput right))
    (comparator (DeltaBlockComparatorInput.toWFInput left))
    (comparator (DeltaBlockComparatorInput.toWFInput right))
  exact comparator_wf_aux (DeltaBlockComparatorInput.toWFInput left)
    (DeltaBlockComparatorInput.toWFInput right)

theorem selectAddOutputDeltaBlock_wf_aux :
    WF.GadgetSpec SelectInput.WFRel
      (fun input => selectAddOutputDeltaBlock input.1 input.2.1
        input.2.2.1 input.2.2.2.1 input.2.2.2.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  change WF.Rel (fun _ _ _ _ => True)
    (fun lv rv => SelectInput.WFRel lv rv left right)
    (selectOutput left.1 left.2.1 left.2.2.1 left.2.2.2.1
      left.2.2.2.2)
    (selectOutput right.1 right.2.1 right.2.2.1 right.2.2.2.1
      right.2.2.2.2)
  exact selectOutput_wf_aux left right

theorem addCompleteCollapsedDeltaBlock_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Fn × AffineSlope.Point × AffineSlope.Point) =>
        Modular.Elem.FullWFRel lv rv left.1 right.1 ∧
        AffineSlope.Point.WFRel lv rv left.2.1 right.2.1 ∧
        AffineSlope.Point.WFRel lv rv left.2.2 right.2.2)
      (fun input => addCompleteCollapsedDeltaBlock input.1
        input.2.1 input.2.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  change WF.Rel (fun _ _ _ _ => True)
    (fun lv rv =>
      Modular.Elem.FullWFRel lv rv left.1 right.1 ∧
      AffineSlope.Point.WFRel lv rv left.2.1 right.2.1 ∧
      AffineSlope.Point.WFRel lv rv left.2.2 right.2.2)
    (addComplete left.1 left.2.1 left.2.2)
    (addComplete right.1 right.2.1 right.2.2)
  exact addComplete_wf_aux left right

def PreparedVerification.BlockWFRel (lv rv : WF.Valuation)
    (left right : PreparedVerification) : Prop :=
  Modular.Elem.ScalarWFRel lv rv left.u1 right.u1 ∧
  Modular.Elem.ScalarWFRel lv rv left.u2 right.u2 ∧
  Projective.WFRel lv rv left.q right.q ∧
  Modular.Elem.FullWFRel lv rv left.r right.r

private theorem one_wfRel (lv rv : WF.Valuation) :
    Modular.Elem.WFRel lv rv one one := by
  unfold one fpConst Modular.ofNat Modular.Elem.WFRel
  exact U.wfRel_bitVec lv rv (BitVec.ofNat 256 1)

theorem prepareVerification_block_wf_aux :
    WF.GadgetSpec PrepareInput.WFRel
      (fun input => prepareVerification input.1 input.2)
      PreparedVerification.BlockWFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold prepareVerification
  apply WF.GadgetSpec.bind_rule_direct
    (left := left.2) (right := right.2) validateCanonicalInput_wf_aux
  · intro lv rv h
    exact h.2
  · intro _ _
    apply WF.GadgetSpec.bind_rule
      (left := left) (right := right) deriveScalars_wf_aux
    · intro lv rv h
      exact h.1
    · intro B scalarsL scalarsR hscalars
      apply WF.Rel.pure
      intro lv rv hB
      have h := hscalars lv rv hB
      have hc := h.1.1.2
      exact ⟨h.2.1, h.2.2,
        ⟨hc.1.1, hc.2.1.1, one_wfRel lv rv⟩, hc.2.2.1⟩

end Freigen.F2Z.Examples.EcdsaP256.DeltaBlockWF
