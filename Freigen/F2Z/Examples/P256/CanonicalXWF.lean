import Freigen.F2Z.Examples.P256.CanonicalXImpl
import Freigen.F2Z.Examples.P256.XOnlyWF

/-!
# Quotient well-formedness for canonical terminal X-only addition

The quotient relation retains the canonical base-field element and identity
flag. It deliberately imposes no semantic condition on `X` when the identity
flag is set; terminal ECDSA acceptance rejects that branch separately.
-/

namespace Freigen.F2Z.Examples.P256.AffineSlope

open Std.Do
open scoped Std.Do
open Modular

set_option maxRecDepth 100000

def CanonicalXPoint.WFRel (lv rv : WF.Valuation)
    (left right : CanonicalXPoint) : Prop :=
  left.X.WFRel lv rv right.X ∧
    WF.LCEq lv.int rv.int left.infinity right.infinity

private def canonicalXWord (bits : Vector (LC Bool) 257) : Word 256 :=
  { bitsLE := Vector.ofFn fun i => bits[i.val]'(by omega) }

private def canonicalXQuotientWord
    (bits : Vector (LC Bool) 257) : Word 1 :=
  { bitsLE := Vector.ofFn fun _ => bits[256] }

private theorem canonicalXWord_get (bits : Vector (LC Bool) 257)
    (i : Fin 256) : (canonicalXWord bits)[i] = bits[i.val] := by
  change (Vector.ofFn fun j : Fin 256 => bits[j.val])[i] = bits[i.val]
  simp

private theorem canonicalXQuotientWord_get (bits : Vector (LC Bool) 257)
    (i : Fin 1) : (canonicalXQuotientWord bits)[i] = bits[256] := by
  change (Vector.ofFn fun _ : Fin 1 => bits[256])[i] = bits[256]
  simp

theorem selectAddOutputCanonicalX_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point × AddControl × Rep) =>
        left.1.WFRel lv rv right.1 ∧
        left.2.1.WFRel lv rv right.2.1 ∧
        left.2.2.1.WFRel lv rv right.2.2.1 ∧
        left.2.2.2.WFRel lv rv right.2.2.2)
      (fun input => selectAddOutputCanonicalX input.1 input.2.1
        input.2.2.1 input.2.2.2)
      CanonicalXPoint.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold selectAddOutputCanonicalX
  apply WF.GadgetSpec.bind_rule
    (left := (left.1.infinity, left.2.1.infinity))
    (right := (right.1.infinity, right.2.1.infinity)) andBit_wf_aux
  · intro lv rv h
    exact ⟨h.1.2.2, h.2.1.2.2⟩
  · intro B bothL bothR hboth
    have hargs : ∀ lv rv, B lv rv → WF.ArgsEq lv rv
        h![left.2.2.1.active, left.1.infinity, left.2.1.infinity,
          left.2.2.2.intVal, left.1.X.intVal, left.2.1.X.intVal]
        h![right.2.2.1.active, right.1.infinity, right.2.1.infinity,
          right.2.2.2.intVal, right.1.X.intVal, right.2.1.X.intVal] := by
      intro lv rv hB
      have h := (hboth lv rv hB).1
      simp_all [WF.ArgsEq, WF.evalArgs, Point.WFRel, AddControl.WFRel,
        Modular.Lazy.Rep.WFRel, WF.LCEq]
    apply WF.Rel.hint
    · exact hargs
    · intro lv rv hB
      exact WF.HintRel.of_argsEq canonicalAddXHint (hargs lv rv hB)
    · intro bitsL bitsR
      let S : WF.Assumption := fun lv rv =>
        B lv rv ∧ ∃ values,
          WF.HintReturns (canonicalAddXHint (WF.evalArgs lv
            h![left.2.2.1.active, left.1.infinity, left.2.1.infinity,
              left.2.2.2.intVal, left.1.X.intVal, left.2.1.X.intVal])) values ∧
          WF.HintReturns (canonicalAddXHint (WF.evalArgs rv
            h![right.2.2.1.active, right.1.infinity, right.2.1.infinity,
              right.2.2.2.intVal, right.1.X.intVal, right.2.1.X.intVal])) values ∧
          WF.RealizesBools lv.bool bitsL values ∧
          WF.RealizesBools rv.bool bitsR values
      have hbits : ∀ lv rv, S lv rv → ∀ i : Fin 257,
          WF.LCEq lv.bool rv.bool bitsL[i] bitsR[i] := by
        intro lv rv h i
        exact Modular.Aux.WF.lceq_of_common_realizes
          (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt
      have hxBits : ∀ lv rv, S lv rv → ∀ i : Fin 256,
          WF.LCEq lv.bool rv.bool
            (canonicalXWord bitsL)[i] (canonicalXWord bitsR)[i] := by
        intro lv rv h i
        rw [canonicalXWord_get, canonicalXWord_get]
        exact
          hbits lv rv h ⟨i.val, by omega⟩
      have hxword := U.fromWord_wf_rel.relHom S
        (canonicalXWord bitsL) (canonicalXWord bitsR) hxBits
      apply hxword.bind
      intro C xWordL xWordR hxwordRel
      have hqBits : ∀ lv rv, C lv rv → ∀ i : Fin 1,
          WF.LCEq lv.bool rv.bool
            (canonicalXQuotientWord bitsL)[i]
            (canonicalXQuotientWord bitsR)[i] := by
        intro lv rv hC i
        have hS := (hxwordRel lv rv hC).1
        rw [canonicalXQuotientWord_get, canonicalXQuotientWord_get]
        exact hbits lv rv hS ⟨256, by omega⟩
      have hqword := U.fromWord_wf_rel.relHom C
        (canonicalXQuotientWord bitsL) (canonicalXQuotientWord bitsR) hqBits
      apply hqword.bind
      intro D quotientL quotientR hquotient
      apply WF.Rel.assertR1C
      · intro lv rv hD
        have hS := (hxwordRel lv rv (hquotient lv rv hD).1).1
        exact ((hboth lv rv hS.1).1).2.2.1.2.2.2.2
      · intro lv rv hD
        have hq := hquotient lv rv hD
        have hx := hxwordRel lv rv hq.1
        have hS := hx.1
        have hi := (hboth lv rv hS.1).1
        exact WF.eval_sub hi.2.2.2.2
          (WF.eval_add hx.2.1 (WF.eval_nsmul base.modulus hq.2.1))
      · intro _ _ _
        rfl
      apply WF.Rel.assertR1C
      · intro lv rv hD
        have hS := (hxwordRel lv rv (hquotient lv rv hD).1).1
        exact ((hboth lv rv hS.1).1).1.2.2
      · intro lv rv hD
        have hq := hquotient lv rv hD
        have hx := hxwordRel lv rv hq.1
        have hi := (hboth lv rv hx.1.1).1
        exact WF.eval_sub hi.2.1.1.2
          (WF.eval_add hx.2.1 (WF.eval_nsmul base.modulus hq.2.1))
      · intro _ _ _
        rfl
      apply WF.Rel.assertR1C
      · intro lv rv hD
        have hq := hquotient lv rv hD
        have hx := hxwordRel lv rv hq.1
        have hi := (hboth lv rv hx.1.1).1
        exact WF.eval_sub hi.2.1.2.2 (hboth lv rv hx.1.1).2
      · intro lv rv hD
        have hq := hquotient lv rv hD
        have hx := hxwordRel lv rv hq.1
        have hi := (hboth lv rv hx.1.1).1
        exact WF.eval_sub hi.1.1.2
          (WF.eval_add hx.2.1 (WF.eval_nsmul base.modulus hq.2.1))
      · intro _ _ _
        rfl
      apply WF.GadgetSpec.bind_rule
        (left := xWordL) (right := xWordR) (Modular.ofU_wf (p := base))
      · intro lv rv hD
        exact (hxwordRel lv rv (hquotient lv rv hD).1).2
      · intro E xL xR hx
        apply WF.GadgetSpec.bind_rule
          (left := (left.2.2.1.sameX, left.2.2.1.oppositeY,
            left.2.2.1.finite))
          (right := (right.2.2.1.sameX, right.2.2.1.oppositeY,
            right.2.2.1.finite)) and3Bit_wf_aux
        · intro lv rv hE
          have hq := hquotient lv rv (hx lv rv hE).1
          have hw := hxwordRel lv rv hq.1
          have hi := (hboth lv rv hw.1.1).1
          exact ⟨hi.2.2.1.1, hi.2.2.1.2.1, hi.2.2.1.2.2.1⟩
        · intro F oppositeL oppositeR hopposite
          apply WF.Rel.pure
          intro lv rv hF
          have hE := hopposite lv rv hF
          have hx' := hx lv rv hE.1
          have hq := hquotient lv rv hx'.1
          have hw := hxwordRel lv rv hq.1
          exact ⟨hx'.2, WF.eval_add (hboth lv rv hw.1.1).2 hE.2⟩

theorem addCompleteCollapsedCanonicalX_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point) =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2)
      (fun input => addCompleteCollapsedCanonicalX input.1 input.2)
      CanonicalXPoint.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold addCompleteCollapsedCanonicalX
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
        selectAddOutputCanonicalX_wf_aux
      intro lv rv hC
      have hx := hcandidate lv rv hC
      have hc := hcontrol lv rv hx.1
      exact ⟨hc.1.1, hc.1.2, hc.2, hx.2⟩

end Freigen.F2Z.Examples.P256.AffineSlope
