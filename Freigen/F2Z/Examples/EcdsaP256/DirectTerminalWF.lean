import Freigen.F2Z.Examples.EcdsaP256.DirectTerminalImpl
import Freigen.F2Z.Examples.P256.XOnlyWF

/-!
# Quotient well-formedness for direct terminal ECDSA acceptance

Only the integer values of the two quotient bits and the 127-bit slack are
observed after decomposition.  The public signature `r` is likewise consumed
only through its canonical integer value, so no strengthened prepared-input
relation is needed.
-/

namespace Freigen.F2Z.Examples.EcdsaP256

open P256
open Modular

set_option maxRecDepth 100000

def DirectTerminalSelectInput.WFRel :
    WF.Post (Fn × AffineSlope.Point × AffineSlope.Point ×
      AffineSlope.AddControl × AffineSlope.Rep) :=
  fun lv rv left right =>
    Modular.Elem.WFRel lv rv left.1 right.1 ∧
    AffineSlope.Point.WFRel lv rv left.2.1 right.2.1 ∧
    AffineSlope.Point.WFRel lv rv left.2.2.1 right.2.2.1 ∧
    AffineSlope.AddControl.WFRel lv rv
      left.2.2.2.1 right.2.2.2.1 ∧
    Modular.Lazy.Rep.WFRel lv rv
      left.2.2.2.2 right.2.2.2.2

private def directTerminalScalarWord
    (bits : Vector (LC Bool) 129) : Word 1 :=
  { bitsLE := Vector.ofFn fun _ => bits[0] }

private def directTerminalBaseWord
    (bits : Vector (LC Bool) 129) : Word 1 :=
  { bitsLE := Vector.ofFn fun _ => bits[1] }

private def directTerminalSlackWord
    (bits : Vector (LC Bool) 129) : Word 127 :=
  { bitsLE := Vector.ofFn fun i => bits[i.val + 2]'(by omega) }

private theorem directTerminalScalarWord_get
    (bits : Vector (LC Bool) 129) (i : Fin 1) :
    (directTerminalScalarWord bits)[i] = bits[0] := by
  change (Vector.ofFn fun _ : Fin 1 => bits[0])[i] = bits[0]
  simp

private theorem directTerminalBaseWord_get
    (bits : Vector (LC Bool) 129) (i : Fin 1) :
    (directTerminalBaseWord bits)[i] = bits[1] := by
  change (Vector.ofFn fun _ : Fin 1 => bits[1])[i] = bits[1]
  simp

private theorem directTerminalSlackWord_get
    (bits : Vector (LC Bool) 129) (i : Fin 127) :
    (directTerminalSlackWord bits)[i] = bits[i.val + 2] := by
  change (Vector.ofFn fun j : Fin 127 => bits[j.val + 2])[i] =
    bits[i.val + 2]
  simp

theorem selectAddOutputDirectTerminal_wf_aux :
    WF.GadgetSpec DirectTerminalSelectInput.WFRel
      (fun input => selectAddOutputDirectTerminal input.1 input.2.1
        input.2.2.1 input.2.2.2.1 input.2.2.2.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold selectAddOutputDirectTerminal
  apply WF.GadgetSpec.bind_rule
    (left := (left.2.1.infinity, left.2.2.1.infinity))
    (right := (right.2.1.infinity, right.2.2.1.infinity))
    AffineSlope.andBit_wf_aux
  · intro lv rv h
    exact ⟨h.2.1.2.2, h.2.2.1.2.2⟩
  · intro B bothL bothR hboth
    have hargs : ∀ lv rv, B lv rv → WF.ArgsEq lv rv
        h![left.2.2.2.1.active, left.2.1.infinity,
          left.2.2.1.infinity, left.2.2.2.2.intVal,
          left.2.1.X.intVal, left.2.2.1.X.intVal,
          left.1.val.intVal]
        h![right.2.2.2.1.active, right.2.1.infinity,
          right.2.2.1.infinity, right.2.2.2.2.intVal,
          right.2.1.X.intVal, right.2.2.1.X.intVal,
          right.1.val.intVal] := by
      intro lv rv hB
      have h := (hboth lv rv hB).1
      simp_all [WF.ArgsEq, WF.evalArgs,
        DirectTerminalSelectInput.WFRel, AffineSlope.Point.WFRel,
        AffineSlope.AddControl.WFRel, Modular.Lazy.Rep.WFRel,
        Modular.Elem.WFRel, U.WFRel, WF.LCEq]
    apply WF.Rel.hint
    · exact hargs
    · intro lv rv hB
      exact WF.HintRel.of_argsEq directTerminalHint (hargs lv rv hB)
    · intro bitsL bitsR
      let S : WF.Assumption := fun lv rv =>
        B lv rv ∧ ∃ values,
          WF.HintReturns (directTerminalHint (WF.evalArgs lv
            h![left.2.2.2.1.active, left.2.1.infinity,
              left.2.2.1.infinity, left.2.2.2.2.intVal,
              left.2.1.X.intVal, left.2.2.1.X.intVal,
              left.1.val.intVal])) values ∧
          WF.HintReturns (directTerminalHint (WF.evalArgs rv
            h![right.2.2.2.1.active, right.2.1.infinity,
              right.2.2.1.infinity, right.2.2.2.2.intVal,
              right.2.1.X.intVal, right.2.2.1.X.intVal,
              right.1.val.intVal])) values ∧
          WF.RealizesBools lv.bool bitsL values ∧
          WF.RealizesBools rv.bool bitsR values
      have hbits : ∀ lv rv, S lv rv → ∀ i : Fin 129,
          WF.LCEq lv.bool rv.bool bitsL[i] bitsR[i] := by
        intro lv rv h i
        exact Modular.Aux.WF.lceq_of_common_realizes
          (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt
      have hscalarBits : ∀ lv rv, S lv rv → ∀ i : Fin 1,
          WF.LCEq lv.bool rv.bool
            (directTerminalScalarWord bitsL)[i]
            (directTerminalScalarWord bitsR)[i] := by
        intro lv rv h i
        rw [directTerminalScalarWord_get, directTerminalScalarWord_get]
        exact hbits lv rv h ⟨0, by omega⟩
      have hscalar := U.fromWord_wf_rel.relHom S
        (directTerminalScalarWord bitsL)
        (directTerminalScalarWord bitsR) hscalarBits
      apply hscalar.bind
      intro C qScalarL qScalarR hqScalar
      have hbaseBits : ∀ lv rv, C lv rv → ∀ i : Fin 1,
          WF.LCEq lv.bool rv.bool
            (directTerminalBaseWord bitsL)[i]
            (directTerminalBaseWord bitsR)[i] := by
        intro lv rv hC i
        have hS := (hqScalar lv rv hC).1
        rw [directTerminalBaseWord_get, directTerminalBaseWord_get]
        exact hbits lv rv hS ⟨1, by omega⟩
      have hbase := U.fromWord_wf_rel.relHom C
        (directTerminalBaseWord bitsL)
        (directTerminalBaseWord bitsR) hbaseBits
      apply hbase.bind
      intro D qBaseL qBaseR hqBase
      have hslackBits : ∀ lv rv, D lv rv → ∀ i : Fin 127,
          WF.LCEq lv.bool rv.bool
            (directTerminalSlackWord bitsL)[i]
            (directTerminalSlackWord bitsR)[i] := by
        intro lv rv hD i
        have hC := (hqBase lv rv hD).1
        have hS := (hqScalar lv rv hC).1
        rw [directTerminalSlackWord_get, directTerminalSlackWord_get]
        exact hbits lv rv hS ⟨i.val + 2, by omega⟩
      have hslack := U.fromWord_wf_rel.relHom D
        (directTerminalSlackWord bitsL)
        (directTerminalSlackWord bitsR) hslackBits
      apply hslack.bind
      intro E slackL slackR hslackRel
      have relations {lv rv} (hE : E lv rv) :
          DirectTerminalSelectInput.WFRel lv rv left right ∧
          U.WFRel lv rv qScalarL qScalarR ∧
          U.WFRel lv rv qBaseL qBaseR ∧
          U.WFRel lv rv slackL slackR := by
        have hs := hslackRel lv rv hE
        have hb := hqBase lv rv hs.1
        have hq := hqScalar lv rv hb.1
        have hS := hq.1
        have hi := (hboth lv rv hS.1).1
        exact ⟨hi, hq.2, hb.2, hs.2⟩
      have beforeHint {lv rv} (hE : E lv rv) : B lv rv := by
        have hs := hslackRel lv rv hE
        have hb := hqBase lv rv hs.1
        have hq := hqScalar lv rv hb.1
        exact hq.1.1
      have targetEq : ∀ lv rv, E lv rv → WF.LCEq lv.int rv.int
          (left.1.val.intVal + scalar.modulus • qScalarL.intVal +
            base.modulus • qBaseL.intVal)
          (right.1.val.intVal + scalar.modulus • qScalarR.intVal +
            base.modulus • qBaseR.intVal) := by
        intro lv rv hE
        have h := relations hE
        exact WF.eval_add
          (WF.eval_add h.1.1.1
            (WF.eval_nsmul scalar.modulus h.2.1.1))
          (WF.eval_nsmul base.modulus h.2.2.1.1)
      apply WF.Rel.assertR1C
      · intro lv rv hE
        exact (relations hE).1.2.2.2.1.2.2.2.2
      · intro lv rv hE
        exact WF.eval_sub (relations hE).1.2.2.2.2.2
          (targetEq lv rv hE)
      · intro _ _ _
        rfl
      apply WF.Rel.assertR1C
      · intro lv rv hE
        exact (relations hE).1.2.1.2.2
      · intro lv rv hE
        exact WF.eval_sub (relations hE).1.2.2.1.1.2
          (targetEq lv rv hE)
      · intro _ _ _
        rfl
      apply WF.Rel.assertR1C
      · intro lv rv hE
        have h := relations hE
        exact WF.eval_sub h.1.2.2.1.2.2
          (hboth lv rv (beforeHint hE)).2
      · intro lv rv hE
        exact WF.eval_sub (relations hE).1.2.1.1.2
          (targetEq lv rv hE)
      · intro _ _ _
        rfl
      apply WF.GadgetSpec.bind_rule
        (left := (left.2.2.2.1.sameX, left.2.2.2.1.oppositeY,
          left.2.2.2.1.finite))
        (right := (right.2.2.2.1.sameX, right.2.2.2.1.oppositeY,
          right.2.2.2.1.finite)) AffineSlope.and3Bit_wf_aux
      · intro lv rv hE
        have h := relations hE
        exact ⟨h.1.2.2.2.1.1, h.1.2.2.2.1.2.1,
          h.1.2.2.2.1.2.2.1⟩
      · intro F oppositeL oppositeR hopposite
        apply WF.Rel.assertR1C
        · intro _ _ _
          rfl
        · intro _ _ _
          rfl
        · intro lv rv hF
          have ho := hopposite lv rv hF
          have h := relations ho.1
          exact WF.eval_add (hboth lv rv (beforeHint ho.1)).2 ho.2
        apply WF.Rel.assertR1C_pure
        · intro lv rv hF
          have ho := hopposite lv rv hF
          exact (relations ho.1).2.1.1
        · intro lv rv hF
          have ho := hopposite lv rv hF
          have h := relations ho.1
          exact WF.eval_sub
            (WF.eval_add (WF.eval_add h.1.1.1 h.2.2.2.1) rfl) rfl
        · intro _ _ _
          rfl
        · intro _ _ _
          trivial

theorem addCompleteCollapsedDirectTerminal_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Fn × AffineSlope.Point × AffineSlope.Point) =>
        Modular.Elem.WFRel lv rv left.1 right.1 ∧
        AffineSlope.Point.WFRel lv rv left.2.1 right.2.1 ∧
        AffineSlope.Point.WFRel lv rv left.2.2 right.2.2)
      (fun input => addCompleteCollapsedDirectTerminal input.1
        input.2.1 input.2.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold addCompleteCollapsedDirectTerminal
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
        selectAddOutputDirectTerminal_wf_aux
      intro lv rv hC
      have hx := hcandidate lv rv hC
      have hc := hcontrol lv rv hx.1
      exact ⟨hc.1.1, hc.1.2.1, hc.1.2.2, hc.2, hx.2⟩

end Freigen.F2Z.Examples.EcdsaP256
