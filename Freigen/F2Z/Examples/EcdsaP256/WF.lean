import Freigen.F2Z.Examples.EcdsaP256.Impl
import Freigen.F2Z.Examples.P256.WF

/-!
# Auxiliary quotient well-formedness proofs for ECDSA-P256

The relations in this file identify circuit values exactly when all their
linear combinations agree under every pair of total valuations.  Keeping the
compositional proofs here prevents the fixed lookup tables and scalar loop
from being expanded into the public verifier statement.
-/

namespace Freigen.F2Z.Examples.EcdsaP256

open P256

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Equality of every linear combination stored in a word, under the two
total valuations.  `U.WFRel` deliberately omits the cached integer bits; the
ECDSA window code consumes those bits directly, so its quotient relation must
retain them as well. -/
def U.FullWFRel (lv rv : WF.Valuation) (left right : U n) : Prop :=
  U.WFRel lv rv left right ∧
    ∀ i : Fin n, WF.LCEq lv.int rv.int left.intBits[i] right.intBits[i]

def Modular.Elem.FullWFRel {p : Modular.Params n}
    (lv rv : WF.Valuation) (left right : Modular.Elem p) : Prop :=
  U.FullWFRel lv rv left.val right.val

/-- The scalar-multiplication quotient only observes the canonical integer and
its cached integer bits; Boolean source bits are not part of this boundary. -/
def U.ScalarWFRel (lv rv : WF.Valuation) (left right : U n) : Prop :=
  WF.LCEq lv.int rv.int left.intVal right.intVal ∧
    ∀ i : Fin n, WF.LCEq lv.int rv.int left.intBits[i] right.intBits[i]

def Modular.Elem.ScalarWFRel {p : Modular.Params n}
    (lv rv : WF.Valuation) (left right : Modular.Elem p) : Prop :=
  U.ScalarWFRel lv rv left.val right.val

theorem U.fromWord_wf_scalar :
    WF.GadgetSpec
      (fun lv rv (left right : Word n) => ∀ i : Fin n,
        WF.LCEq lv.bool rv.bool left[i] right[i])
      U.fromWord U.ScalarWFRel := by
  intro left right
  apply WF.Rel.mono (U.fromWord_wf_full left right)
  intro _ _ _ _ h
  exact ⟨h.2.2, h.2.1⟩

/-- Quotient-backend equality for verifier inputs.  It is intentionally
extensional: every circuit-visible LC has equal value under every related pair
of total valuations. -/
def VerifyInput.WFRel (lv rv : WF.Valuation)
    (left right : VerifyInput) : Prop :=
  U.FullWFRel lv rv left.1 right.1 ∧
    U.FullWFRel lv rv left.2.1.x right.2.1.x ∧
    U.FullWFRel lv rv left.2.1.y right.2.1.y ∧
    U.FullWFRel lv rv left.2.2.1.r right.2.2.1.r ∧
    U.FullWFRel lv rv left.2.2.1.s right.2.2.1.s ∧
    U.FullWFRel lv rv left.2.2.2.rInv right.2.2.2.rInv ∧
    U.FullWFRel lv rv left.2.2.2.sInv right.2.2.2.sInv

theorem materializeLow_wf_aux :
    WF.GadgetSpec AffineSlope.Point.WFRel materializeLow
      (WF.VectorRel AffineSlope.Point.WFRel) := by
  wfgen' using [AffineSlope.addComplete_wf_aux]
    unfold [materializeLow, addMultiple]
  all_goals fin_cases i <;>
    simp only [Fin.getElem_fin, Vector.getElem_mk, ← Array.getElem_toList,
      List.getElem_cons_zero, List.getElem_cons_succ] <;> grind

theorem materializeMid_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : AffineSlope.Point × AffineSlope.Point) =>
        AffineSlope.Point.WFRel lv rv left.1 right.1 ∧
        AffineSlope.Point.WFRel lv rv left.2 right.2)
      (fun input => materializeMid input.1 input.2)
      (WF.VectorRel AffineSlope.Point.WFRel) := by
  wfgen' using [AffineSlope.addComplete_wf_aux]
    unfold [materializeMid, addMultiple]
  all_goals fin_cases i <;>
    simp only [Fin.getElem_fin, Vector.getElem_mk, ← Array.getElem_toList,
      List.getElem_cons_zero, List.getElem_cons_succ] <;> grind

theorem materializeHigh_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : AffineSlope.Point × AffineSlope.Point) =>
        AffineSlope.Point.WFRel lv rv left.1 right.1 ∧
        AffineSlope.Point.WFRel lv rv left.2 right.2)
      (fun input => materializeHigh input.1 input.2)
      (WF.VectorRel AffineSlope.Point.WFRel) := by
  wfgen' using [AffineSlope.addComplete_wf_aux]
    unfold [materializeHigh, addMultiple]
  all_goals fin_cases i <;>
    simp only [Fin.getElem_fin, Vector.getElem_mk, ← Array.getElem_toList,
      List.getElem_cons_zero, List.getElem_cons_succ] <;> grind

theorem materializeTail_wf_aux :
    WF.GadgetSpec
      (fun lv rv
          (left right : AffineSlope.Point × Vector AffineSlope.Point 5) =>
        AffineSlope.Point.WFRel lv rv left.1 right.1 ∧
        WF.VectorRel AffineSlope.Point.WFRel lv rv left.2 right.2)
      (fun input => materializeTail input.1 input.2)
      (fun lv rv left right =>
        WF.VectorRel AffineSlope.Point.WFRel lv rv left.1 right.1 ∧
        WF.VectorRel AffineSlope.Point.WFRel lv rv left.2 right.2) := by
  wfgen' using [materializeMid_wf_aux, materializeHigh_wf_aux]
    unfold [materializeTail]
  case vc1 =>
    rename_i hrel hB
    exact (hrel leftVal rightVal hB).2 ⟨4, by omega⟩
  case vc2 =>
    rename_i h
    exact h.2 ⟨4, by omega⟩

theorem materializeMultiples_wf_aux :
    WF.GadgetSpec Projective.WFRel materializeMultiples
      (WF.VectorRel AffineSlope.Point.WFRel) := by
  wfgen' using [materializeLow_wf_aux, materializeTail_wf_aux]
    unfold [materializeMultiples]
  case vc1 =>
    rename_i hlow htail hB
    have ht := htail leftVal rightVal hB
    have hl := hlow leftVal rightVal ht.1
    fin_cases i
    · simpa only [Fin.getElem_fin, Vector.getElem_mk,
        ← Array.getElem_toList, List.getElem_cons_zero,
        List.getElem_cons_succ] using
        AffineSlope.infinity_wfRel leftVal rightVal
    · simpa only [Fin.getElem_fin, Vector.getElem_mk,
        ← Array.getElem_toList, List.getElem_cons_zero,
        List.getElem_cons_succ] using hl.2 ⟨0, by omega⟩
    · simpa only [Fin.getElem_fin, Vector.getElem_mk,
        ← Array.getElem_toList, List.getElem_cons_zero,
        List.getElem_cons_succ] using hl.2 ⟨1, by omega⟩
    · simpa only [Fin.getElem_fin, Vector.getElem_mk,
        ← Array.getElem_toList, List.getElem_cons_zero,
        List.getElem_cons_succ] using hl.2 ⟨2, by omega⟩
    · simpa only [Fin.getElem_fin, Vector.getElem_mk,
        ← Array.getElem_toList, List.getElem_cons_zero,
        List.getElem_cons_succ] using hl.2 ⟨3, by omega⟩
    · simpa only [Fin.getElem_fin, Vector.getElem_mk,
        ← Array.getElem_toList, List.getElem_cons_zero,
        List.getElem_cons_succ] using hl.2 ⟨4, by omega⟩
    · simpa only [Fin.getElem_fin, Vector.getElem_mk,
        ← Array.getElem_toList, List.getElem_cons_zero,
        List.getElem_cons_succ] using ht.2.1 ⟨0, by omega⟩
    · simpa only [Fin.getElem_fin, Vector.getElem_mk,
        ← Array.getElem_toList, List.getElem_cons_zero,
        List.getElem_cons_succ] using ht.2.1 ⟨1, by omega⟩
    · simpa only [Fin.getElem_fin, Vector.getElem_mk,
        ← Array.getElem_toList, List.getElem_cons_zero,
        List.getElem_cons_succ] using ht.2.1 ⟨2, by omega⟩
    · simpa only [Fin.getElem_fin, Vector.getElem_mk,
        ← Array.getElem_toList, List.getElem_cons_zero,
        List.getElem_cons_succ] using ht.2.1 ⟨3, by omega⟩
    · simpa only [Fin.getElem_fin, Vector.getElem_mk,
        ← Array.getElem_toList, List.getElem_cons_zero,
        List.getElem_cons_succ] using ht.2.1 ⟨4, by omega⟩
    · simpa only [Fin.getElem_fin, Vector.getElem_mk,
        ← Array.getElem_toList, List.getElem_cons_zero,
        List.getElem_cons_succ] using ht.2.2 ⟨0, by omega⟩
    · simpa only [Fin.getElem_fin, Vector.getElem_mk,
        ← Array.getElem_toList, List.getElem_cons_zero,
        List.getElem_cons_succ] using ht.2.2 ⟨1, by omega⟩
    · simpa only [Fin.getElem_fin, Vector.getElem_mk,
        ← Array.getElem_toList, List.getElem_cons_zero,
        List.getElem_cons_succ] using ht.2.2 ⟨2, by omega⟩
    · simpa only [Fin.getElem_fin, Vector.getElem_mk,
        ← Array.getElem_toList, List.getElem_cons_zero,
        List.getElem_cons_succ] using ht.2.2 ⟨3, by omega⟩
    · simpa only [Fin.getElem_fin, Vector.getElem_mk,
        ← Array.getElem_toList, List.getElem_cons_zero,
        List.getElem_cons_succ] using ht.2.2 ⟨4, by omega⟩
  case vc2 =>
    rename_i hrel hB
    have h := hrel leftVal rightVal hB
    exact AffineSlope.ofElems_wfRel h.1.1 h.1.2.1
  case vc3 =>
    rename_i h
    exact AffineSlope.ofElems_wfRel h.1 h.2.1

theorem indicators_wf_aux (n : Nat) :
    WF.GadgetSpec
      (fun lv rv (left right : LC ℤ) => WF.LCEq lv.int rv.int left right)
      (indicators n) U.FullWFRel := by
  wfgen' using [U.fromWord_wf_full] unfold [indicators, U.FullWFRel]
  case vc1 =>
    rename_i hpost hB
    have h := hpost leftVal rightVal hB
    exact ⟨h.2.2.2, h.2.1⟩
  case vc2 =>
    rename_i h
    rcases h with ⟨_, values, _, _, hleft, hright⟩
    exact (hleft i.val i.isLt).trans (hright i.val i.isLt).symm
  all_goals simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

def RepLookupRel : WF.Post (LC ℤ × U 16 × Vector AffineSlope.Rep 16) :=
  fun lv rv left right =>
    WF.LCEq lv.int rv.int left.1 right.1 ∧
    U.FullWFRel lv rv left.2.1 right.2.1 ∧
    WF.VectorRel Modular.Lazy.Rep.WFRel lv rv left.2.2 right.2.2

local macro "rw_fin16 " h:term : tactic =>
  `(tactic| rw [
    ($h 0 (by omega)), ($h 1 (by omega)), ($h 2 (by omega)),
    ($h 3 (by omega)), ($h 4 (by omega)), ($h 5 (by omega)),
    ($h 6 (by omega)), ($h 7 (by omega)), ($h 8 (by omega)),
    ($h 9 (by omega)), ($h 10 (by omega)), ($h 11 (by omega)),
    ($h 12 (by omega)), ($h 13 (by omega)), ($h 14 (by omega)),
    ($h 15 (by omega))])

private theorem lookupArgs_argsEq (lv rv : WF.Valuation)
    (digitL digitR : LC ℤ) (valuesL valuesR : Vector (LC ℤ) 16)
    (hd : WF.LCEq lv.int rv.int digitL digitR)
    (hv : ∀ i : Fin 16, WF.LCEq lv.int rv.int valuesL[i] valuesR[i]) :
    WF.ArgsEq lv rv (lookupArgs digitL valuesL) (lookupArgs digitR valuesR) := by
  unfold WF.LCEq at hd
  have hv' (i : Nat) (hi : i < 16) :
      LC.eval lv.int valuesL[i] = LC.eval rv.int valuesR[i] := by
    exact hv ⟨i, hi⟩
  simp only [WF.ArgsEq, lookupArgs, WF.evalArgs]
  rw [hd]
  rw_fin16 hv'

theorem assertLookupRep_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : U 16 × U 256 × Vector AffineSlope.Rep 16) =>
        U.FullWFRel lv rv left.1 right.1 ∧ U.WFRel lv rv left.2.1 right.2.1 ∧
        WF.VectorRel Modular.Lazy.Rep.WFRel lv rv left.2.2 right.2.2)
      (fun input => assertLookupRep input.1 input.2.1 input.2.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  simp only
  unfold assertLookupRep
  refine WF.Rel.mono (WF.Rel.foldRange_rule
    (I := fun lv rv (_ _ : Unit) =>
      U.FullWFRel lv rv left.1 right.1 ∧
      U.WFRel lv rv left.2.1 right.2.1 ∧
      WF.VectorRel Modular.Lazy.Rep.WFRel lv rv left.2.2 right.2.2) ?_ ?_) ?_
  · intro lv rv h
    exact h
  · intro i hi P _ _ hrel
    apply WF.Rel.assertR1C_pure
    · intro lv rv hP
      exact (hrel lv rv hP).1.2 ⟨i, hi.2.1⟩
    · intro lv rv hP
      have h := hrel lv rv hP
      exact WF.eval_sub h.2.1.1 (h.2.2 ⟨i, hi.2.1⟩).2
    · intro _ _ _
      rfl
    · intro lv rv hP
      exact ⟨hP, hrel lv rv hP⟩
  · intro _ _ _ _ _
    trivial

private theorem repLookup_argsEq (lv rv : WF.Valuation)
    (left right : LC ℤ × U 16 × Vector AffineSlope.Rep 16)
    (h : RepLookupRel lv rv left right) :
    WF.ArgsEq lv rv
      (lookupArgs left.1 (left.2.2.map (·.intVal)))
      (lookupArgs right.1 (right.2.2.map (·.intVal))) := by
  apply lookupArgs_argsEq lv rv
  · exact h.1
  · intro i
    simpa using (h.2.2 i).2

theorem lookupRepWord_wf_aux :
    WF.GadgetSpec RepLookupRel
      (fun input => lookupRepWord input.1 input.2.2)
      U.FullWFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold lookupRepWord
  apply WF.Rel.hint
  · intro lv rv h
    exact repLookup_argsEq lv rv left right h
  · intro lv rv h
    have heq := repLookup_argsEq lv rv left right h
    unfold WF.ArgsEq at heq
    rw [heq]
    exact WF.HintRel.refl _
  · intro bitsL bitsR
    let S : WF.Assumption := fun lv rv =>
      RepLookupRel lv rv left right ∧ ∃ values,
        WF.HintReturns
          (lookupRepHint (WF.evalArgs lv
            (lookupArgs left.1 (left.2.2.map (·.intVal))))) values ∧
        WF.HintReturns
          (lookupRepHint (WF.evalArgs rv
            (lookupArgs right.1 (right.2.2.map (·.intVal))))) values ∧
        WF.RealizesBools lv.bool bitsL values ∧
        WF.RealizesBools rv.bool bitsR values
    have hbits : ∀ lv rv, S lv rv → ∀ i : Fin 256,
        WF.LCEq lv.bool rv.bool bitsL[i] bitsR[i] := by
      intro lv rv h i
      exact Modular.Aux.WF.lceq_of_common_realizes
        (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt
    have hword := U.fromWord_wf_full.relHom S
      ({ bitsLE := bitsL } : Word 256) ({ bitsLE := bitsR } : Word 256)
      hbits
    exact WF.Rel.mono hword (by
      intro lv rv outL outR h
      exact ⟨⟨h.2.2.2, h.2.1⟩, h.2.2.1⟩)

theorem lookupRep_wf_aux :
    WF.GadgetSpec RepLookupRel
      (fun input => lookupRep input.1 input.2.1 input.2.2)
      Modular.Lazy.Rep.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold lookupRep
  apply WF.GadgetSpec.bind_rule_direct
    (left := left) (right := right) lookupRepWord_wf_aux
  · intro lv rv h
    exact h
  · intro outL outR
    apply WF.GadgetSpec.bind_rule_direct
      (left := (left.2.1, outL, left.2.2))
      (right := (right.2.1, outR, right.2.2)) assertLookupRep_wf_aux
    · intro lv rv h
      exact ⟨h.1.2.1, h.2.1, h.1.2.2⟩
    · intro _ _
      apply WF.Rel.pure
      intro lv rv h
      exact ⟨rfl, h.1.2.1.1⟩

def FlagLookupRel : WF.Post (LC ℤ × U 16 × Vector (LC ℤ) 16) :=
  fun lv rv left right =>
    WF.LCEq lv.int rv.int left.1 right.1 ∧
    U.FullWFRel lv rv left.2.1 right.2.1 ∧
    WF.VectorRel (fun lv rv l r => WF.LCEq lv.int rv.int l r)
      lv rv left.2.2 right.2.2

theorem assertLookupFlag_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : U 16 × LC ℤ × Vector (LC ℤ) 16) =>
        U.FullWFRel lv rv left.1 right.1 ∧
        WF.LCEq lv.int rv.int left.2.1 right.2.1 ∧
        WF.VectorRel (fun lv rv l r => WF.LCEq lv.int rv.int l r)
          lv rv left.2.2 right.2.2)
      (fun input => assertLookupFlag input.1 input.2.1 input.2.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  simp only
  unfold assertLookupFlag
  refine WF.Rel.mono (WF.Rel.foldRange_rule
    (I := fun lv rv (_ _ : Unit) =>
      U.FullWFRel lv rv left.1 right.1 ∧
      WF.LCEq lv.int rv.int left.2.1 right.2.1 ∧
      WF.VectorRel (fun lv rv l r => WF.LCEq lv.int rv.int l r)
        lv rv left.2.2 right.2.2) ?_ ?_) ?_
  · intro lv rv h
    exact h
  · intro i hi P _ _ hrel
    apply WF.Rel.assertR1C_pure
    · intro lv rv hP
      exact (hrel lv rv hP).1.2 ⟨i, hi.2.1⟩
    · intro lv rv hP
      have h := hrel lv rv hP
      exact WF.eval_sub h.2.1 (h.2.2 ⟨i, hi.2.1⟩)
    · intro _ _ _
      rfl
    · intro lv rv hP
      exact ⟨hP, hrel lv rv hP⟩
  · intro _ _ _ _ _
    trivial

private theorem flagLookup_argsEq (lv rv : WF.Valuation)
    (left right : LC ℤ × U 16 × Vector (LC ℤ) 16)
    (h : FlagLookupRel lv rv left right) :
    WF.ArgsEq lv rv
      (lookupArgs left.1 left.2.2) (lookupArgs right.1 right.2.2) := by
  exact lookupArgs_argsEq lv rv _ _ _ _ h.1 h.2.2

theorem lookupFlag_wf_aux :
    WF.GadgetSpec FlagLookupRel
      (fun input => lookupFlag input.1 input.2.1 input.2.2)
      (fun lv rv left right => WF.LCEq lv.int rv.int left right) := by
  wfgen' using [assertLookupFlag_wf_aux]
    unfold [lookupFlag, lookupFlagHint, FlagLookupRel]
  case vc1 =>
    rename_i hrel hB
    have h := hrel leftVal rightVal hB
    rcases h with ⟨⟨⟨_, values, _, _, hleft, hright⟩, hl, hr⟩, _⟩
    unfold WF.LCEq
    rw [hl, hr, (hleft 0 (by omega)).trans (hright 0 (by omega)).symm]
  case vc2 =>
    rename_i h
    rcases h with ⟨⟨_, values, _, _, hleft, hright⟩, hl, hr⟩
    unfold WF.LCEq
    rw [hl, hr, (hleft 0 (by omega)).trans (hright 0 (by omega)).symm]
  case vc3 =>
    rename_i h
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) j.val j.isLt
  case vc4 =>
    refine ⟨?_, ?_, ?_⟩ <;> native_decide
  case vc5 =>
    rename_i h
    rw [flagLookup_argsEq leftVal rightVal left right h]
  case vc6 =>
    rename_i h
    exact flagLookup_argsEq leftVal rightVal left right h

def PointLookupRel : WF.Post (LC ℤ × Vector AffineSlope.Point 16) :=
  fun lv rv left right =>
    WF.LCEq lv.int rv.int left.1 right.1 ∧
    WF.VectorRel AffineSlope.Point.WFRel lv rv left.2 right.2

theorem lookupPoint_wf_aux :
    WF.GadgetSpec PointLookupRel
      (fun input => lookupPoint input.1 input.2)
      AffineSlope.Point.WFRel := by
  wfgen' using [indicators_wf_aux, lookupRep_wf_aux,
    lookupFlag_wf_aux]
    unfold [lookupPoint, windowIndicators, PointLookupRel,
      AffineSlope.Point.WFRel]
  all_goals simp_all [RepLookupRel, FlagLookupRel, U.FullWFRel, WF.VectorRel]
  all_goals grind

theorem windowValue_wf_aux (start width : Nat) (hfit : start + width ≤ 256) :
    WF.GadgetSpec Modular.Elem.ScalarWFRel
      (fun k => pure (windowValue k start width hfit))
      (fun lv rv left right => WF.LCEq lv.int rv.int left right) := by
  unfold WF.GadgetSpec
  intro left right
  apply WF.Rel.pure
  intro lv rv h
  unfold WF.LCEq at h ⊢
  unfold windowValue
  simp only [LC.eval_sum, LC.eval_nsmul]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun x => 2 ^ j.val • x)
    (h.2 ⟨start + j.val, by omega⟩)

theorem windowDigit_wf_aux (i : Nat) (hi : i < 64) :
    WF.GadgetSpec Modular.Elem.ScalarWFRel
      (fun k => windowDigit k i hi)
      (fun lv rv left right => WF.LCEq lv.int rv.int left right) := by
  simpa [windowDigit] using
    windowValue_wf_aux (252 - 4 * i) 4 (by omega)

theorem windowByte_wf_aux (i : Nat) (hi : i < 32) :
    WF.GadgetSpec Modular.Elem.ScalarWFRel
      (fun k => windowByte k i hi)
      (fun lv rv left right => WF.LCEq lv.int rv.int left right) := by
  simpa [windowByte] using
    windowValue_wf_aux (248 - 8 * i) 8 (by omega)

theorem doublePair_wf_aux :
    WF.GadgetSpec AffineSlope.Point.WFRel doublePair
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold doublePair doubleStep
  apply WF.GadgetSpec.bind_rule
    (left := left) (right := right) AffineSlope.doubleComplete_wf_aux
  · intro lv rv h
    exact h
  · intro B midL midR hmid
    apply WF.GadgetSpec.direct_rule
      (left := midL) (right := midR) AffineSlope.doubleComplete_wf_aux
    intro lv rv hB
    exact (hmid lv rv hB).2

theorem doubleFour_wf_aux :
    WF.GadgetSpec AffineSlope.Point.WFRel doubleFour
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold doubleFour
  apply WF.GadgetSpec.bind_rule
    (left := left) (right := right) doublePair_wf_aux
  · intro lv rv h
    exact h
  · intro B midL midR hmid
    apply WF.GadgetSpec.direct_rule
      (left := midL) (right := midR) doublePair_wf_aux
    intro lv rv hB
    exact (hmid lv rv hB).2

theorem lookupGeneratorByte_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : LC ℤ) => WF.LCEq lv.int rv.int left right)
      lookupGeneratorByte AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold lookupGeneratorByte byteIndicators
  apply WF.GadgetSpec.bind_rule
    (left := left) (right := right) (indicators_wf_aux 256)
  · intro lv rv h
    exact h
  · intro B indicatorsL indicatorsR hindicators
    apply WF.Rel.pure
    intro lv rv hB
    have h := hindicators lv rv hB
    unfold AffineSlope.Point.WFRel Modular.Lazy.Rep.WFRel
    refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, h.2.2 ⟨0, by omega⟩⟩
    · unfold WF.LCEq
      simp only [LC.eval_sum, LC.eval_nsmul]
      apply Finset.sum_congr rfl
      intro j _
      rw [h.2.2 j]
    · unfold WF.LCEq
      simp only [LC.eval_sum, LC.eval_nsmul]
      apply Finset.sum_congr rfl
      intro j _
      rw [h.2.2 j]

def JointTerms.WFRel (lv rv : WF.Valuation)
    (left right : JointTerms) : Prop :=
  AffineSlope.Point.WFRel lv rv left.qhi right.qhi ∧
  AffineSlope.Point.WFRel lv rv left.qlo right.qlo ∧
  AffineSlope.Point.WFRel lv rv left.g right.g

theorem selectJointTerms_wf_aux (i : Nat) (hi : i < 32) :
    WF.GadgetSpec
      (fun lv rv
          (left right : Fn × Fn × Vector AffineSlope.Point 16) =>
        Modular.Elem.ScalarWFRel lv rv left.1 right.1 ∧
        Modular.Elem.ScalarWFRel lv rv left.2.1 right.2.1 ∧
        WF.VectorRel AffineSlope.Point.WFRel lv rv left.2.2 right.2.2)
      (fun input => selectJointTerms input.1 input.2.1 input.2.2 i hi)
      JointTerms.WFRel := by
  wfgen' using [windowByte_wf_aux, windowDigit_wf_aux,
    lookupPoint_wf_aux, lookupGeneratorByte_wf_aux]
    unfold [selectJointTerms, JointTerms.WFRel]
  all_goals simp_all [PointLookupRel]
  all_goals grind

theorem accumulateJoint_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : AffineSlope.Point × JointTerms) =>
        AffineSlope.Point.WFRel lv rv left.1 right.1 ∧
        JointTerms.WFRel lv rv left.2 right.2)
      (fun input => accumulateJoint input.1 input.2)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold accumulateJoint
  apply WF.GadgetSpec.bind_rule
    (left := left.1) (right := right.1) doubleFour_wf_aux
  · intro lv rv h
    exact h.1
  · intro B acc1L acc1R hacc1
    apply WF.GadgetSpec.bind_rule
      (left := (acc1L, left.2.qhi))
      (right := (acc1R, right.2.qhi)) AffineSlope.addComplete_wf_aux
    · intro lv rv hB
      have h := hacc1 lv rv hB
      exact ⟨h.2, h.1.2.1⟩
    · intro C acc2L acc2R hacc2
      apply WF.GadgetSpec.bind_rule
        (left := acc2L) (right := acc2R) doubleFour_wf_aux
      · intro lv rv hC
        exact (hacc2 lv rv hC).2
      · intro D acc3L acc3R hacc3
        apply WF.GadgetSpec.bind_rule
          (left := (acc3L, left.2.qlo))
          (right := (acc3R, right.2.qlo)) AffineSlope.addComplete_wf_aux
        · intro lv rv hD
          have h3 := hacc3 lv rv hD
          have h2 := hacc2 lv rv h3.1
          have h1 := hacc1 lv rv h2.1
          exact ⟨h3.2, h1.1.2.2.1⟩
        · intro E acc4L acc4R hacc4
          apply WF.GadgetSpec.direct_rule
            (left := (acc4L, left.2.g))
            (right := (acc4R, right.2.g)) AffineSlope.addComplete_wf_aux
          intro lv rv hE
          have h4 := hacc4 lv rv hE
          have h3 := hacc3 lv rv h4.1
          have h2 := hacc2 lv rv h3.1
          have h1 := hacc1 lv rv h2.1
          exact ⟨h4.2, h1.1.2.2.2⟩

theorem jointByteStep_wf_aux (i : Nat) (hi : i < 32) :
    WF.GadgetSpec
      (fun lv rv
          (left right : Fn × Fn × Vector AffineSlope.Point 16 ×
            AffineSlope.Point) =>
        Modular.Elem.ScalarWFRel lv rv left.1 right.1 ∧
        Modular.Elem.ScalarWFRel lv rv left.2.1 right.2.1 ∧
        WF.VectorRel AffineSlope.Point.WFRel lv rv left.2.2.1 right.2.2.1 ∧
        AffineSlope.Point.WFRel lv rv left.2.2.2 right.2.2.2)
      (fun input => jointByteStep input.1 input.2.1 input.2.2.1 i hi input.2.2.2)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold jointByteStep
  apply WF.GadgetSpec.bind_rule
    (left := (left.1, left.2.1, left.2.2.1))
    (right := (right.1, right.2.1, right.2.2.1))
    (selectJointTerms_wf_aux i hi)
  · intro lv rv h
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  · intro B termsL termsR hterms
    apply WF.GadgetSpec.direct_rule
      (left := (left.2.2.2, termsL))
      (right := (right.2.2.2, termsR)) accumulateJoint_wf_aux
    intro lv rv hB
    have h := hterms lv rv hB
    exact ⟨h.1.2.2.2, h.2⟩

def JointScalarInput.WFRel :
    WF.Post (Fn × Fn × Projective) :=
  fun lv rv left right =>
    Modular.Elem.ScalarWFRel lv rv left.1 right.1 ∧
    Modular.Elem.ScalarWFRel lv rv left.2.1 right.2.1 ∧
    Projective.WFRel lv rv left.2.2 right.2.2

theorem jointScalarMul_wf_aux :
    WF.GadgetSpec JointScalarInput.WFRel
      (fun input => jointScalarMul input.1 input.2.1 input.2.2)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold jointScalarMul
  apply WF.GadgetSpec.bind_rule materializeMultiples_wf_aux
  · intro lv rv h
    exact h.2.2
  · intro B tableL tableR htable
    refine WF.Rel.mono (WF.Rel.foldRange_rule
      (I := fun lv rv left right =>
        B lv rv ∧ AffineSlope.Point.WFRel lv rv left right) ?_ ?_) ?_
    · intro lv rv hB
      exact ⟨hB, AffineSlope.infinity_wfRel lv rv⟩
    · intro i hi P accL accR hacc
      have hinput : ∀ lv rv, P lv rv →
          Modular.Elem.ScalarWFRel lv rv left.1 right.1 ∧
          Modular.Elem.ScalarWFRel lv rv left.2.1 right.2.1 ∧
          WF.VectorRel AffineSlope.Point.WFRel lv rv tableL tableR ∧
          AffineSlope.Point.WFRel lv rv accL accR := by
        intro lv rv hP
        have hstate := hacc lv rv hP
        have ht := htable lv rv hstate.1
        exact ⟨ht.1.1, ht.1.2.1, ht.2, hstate.2⟩
      have hstep := (jointByteStep_wf_aux i hi.2.1).relHom P
        (left.1, left.2.1, tableL, accL)
        (right.1, right.2.1, tableR, accR) hinput
      exact WF.Rel.mono hstep (by
        intro lv rv outL outR hpost
        exact ⟨hpost.1, (hacc lv rv hpost.1).1, hpost.2⟩
      )
    · intro lv rv outL outR hpost
      exact hpost.2

private theorem fnOne_wfRel (lv rv : WF.Valuation) :
    Modular.Elem.WFRel lv rv fnOne fnOne := by
  unfold fnOne fnConst Modular.ofNat Modular.Elem.WFRel
  exact U.wfRel_bitVec lv rv (BitVec.ofNat 256 1)

theorem Modular.ofU_wf_full_aux {n : Nat} (p : Modular.Params n) :
    WF.GadgetSpec U.FullWFRel (Modular.ofU p)
      (Modular.Elem.FullWFRel (p := p)) := by
  unfold WF.GadgetSpec
  intro left right
  unfold Modular.ofU
  apply WF.GadgetSpec.bind_rule
    (left := left) (right := right) Modular.assertLt_wf
  · intro lv rv h
    exact h.1
  · intro B _ _ hassert
    apply WF.Rel.pure
    intro lv rv hB
    exact (hassert lv rv hB).1

theorem Modular.assertLt_wf_scalar_aux {n : Nat} (bound : Nat) :
    WF.GadgetSpec U.ScalarWFRel (Modular.assertLt (n := n) bound)
      (fun _ _ _ _ => True) := by
  wfgen' using [U.fromInt_wf_full]
    unfold [Modular.assertLt, U.ScalarWFRel]

theorem Modular.ofU_wf_scalar_aux {n : Nat} (p : Modular.Params n) :
    WF.GadgetSpec U.ScalarWFRel (Modular.ofU p)
      (Modular.Elem.ScalarWFRel (p := p)) := by
  unfold WF.GadgetSpec
  intro left right
  unfold Modular.ofU
  apply WF.GadgetSpec.bind_rule
    (left := left) (right := right)
    (Modular.assertLt_wf_scalar_aux p.modulus)
  · intro lv rv h
    exact h
  · intro B _ _ hassert
    apply WF.Rel.pure
    intro lv rv hB
    exact (hassert lv rv hB).1

theorem Modular.Lazy.reduce_wf_scalar_aux {n : Nat}
    (p : Modular.Params n) :
    WF.GadgetSpec Modular.Lazy.Rep.WFRel (Modular.Lazy.reduce p)
      (Modular.Elem.ScalarWFRel (p := p)) := by
  wfgen' using [U.fromWord_wf_scalar, Modular.ofU_wf_scalar_aux]
    unfold [Modular.Lazy.reduce, Modular.Lazy.Rep.WFRel,
      Modular.Elem.ScalarWFRel]
  case vc1 =>
    rename_i outBitsL outBitsR B0 rL rR hR
    apply WF.GadgetSpec.direct_rule (Modular.ofU_wf_scalar_aux p)
    intro lv rv hB
    exact (rR lv rv (hR lv rv hB).1).2
  case vc2 outBitsL outBitsR B =>
    rename_i qL qR
    have hp := outBitsR leftVal rightVal B
    apply Modular.Aux.WF.wordSlice_lceq_of_common_realizes
    · exact Modular.Aux.WF.common_realizes_of_hint hp.1
    · omega
  case vc3 =>
    rename_i h
    simpa only [zero_add] using
      Modular.Aux.WF.wordSlice_lceq_of_common_realizes
        (Modular.Aux.WF.common_realizes_of_hint h) 0 n (by omega) i
  all_goals simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

def CanonicalInput.WFRel (lv rv : WF.Valuation)
    (left right : CanonicalInput) : Prop :=
  Modular.Elem.FullWFRel lv rv left.qx right.qx ∧
  Modular.Elem.FullWFRel lv rv left.qy right.qy ∧
  Modular.Elem.FullWFRel lv rv left.r right.r ∧
  Modular.Elem.FullWFRel lv rv left.s right.s ∧
  Modular.Elem.FullWFRel lv rv left.rInv right.rInv ∧
  Modular.Elem.FullWFRel lv rv left.sInv right.sInv

def CanonicalizeInput.WFRel :
    WF.Post (PublicKey × Signature × Aux) :=
  fun lv rv left right =>
    U.FullWFRel lv rv left.1.x right.1.x ∧
    U.FullWFRel lv rv left.1.y right.1.y ∧
    U.FullWFRel lv rv left.2.1.r right.2.1.r ∧
    U.FullWFRel lv rv left.2.1.s right.2.1.s ∧
    U.FullWFRel lv rv left.2.2.rInv right.2.2.rInv ∧
    U.FullWFRel lv rv left.2.2.sInv right.2.2.sInv

def ElemPair.FullWFRel {p : Modular.Params n} :
    WF.Post (Modular.Elem p × Modular.Elem p) :=
  fun lv rv left right =>
    Modular.Elem.FullWFRel lv rv left.1 right.1 ∧
    Modular.Elem.FullWFRel lv rv left.2 right.2

theorem canonicalizeKey_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : PublicKey) =>
        U.FullWFRel lv rv left.x right.x ∧
        U.FullWFRel lv rv left.y right.y)
      canonicalizeKey (ElemPair.FullWFRel (p := base)) := by
  wfgen' using [Modular.ofU_wf_full_aux]
    unfold [canonicalizeKey, ElemPair.FullWFRel]

theorem canonicalizeSignature_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Signature) =>
        U.FullWFRel lv rv left.r right.r ∧
        U.FullWFRel lv rv left.s right.s)
      canonicalizeSignature (ElemPair.FullWFRel (p := scalar)) := by
  wfgen' using [Modular.ofU_wf_full_aux]
    unfold [canonicalizeSignature, ElemPair.FullWFRel]

theorem canonicalizeAux_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Aux) =>
        U.FullWFRel lv rv left.rInv right.rInv ∧
        U.FullWFRel lv rv left.sInv right.sInv)
      canonicalizeAux (ElemPair.FullWFRel (p := scalar)) := by
  wfgen' using [Modular.ofU_wf_full_aux]
    unfold [canonicalizeAux, ElemPair.FullWFRel]

theorem canonicalizeInput_wf_aux :
    WF.GadgetSpec CanonicalizeInput.WFRel
      (fun input => canonicalizeInput input.1 input.2.1 input.2.2)
      CanonicalInput.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold canonicalizeInput
  apply WF.GadgetSpec.bind_rule_direct
    (left := left.1) (right := right.1) canonicalizeKey_wf_aux
  · intro lv rv h
    exact ⟨h.1, h.2.1⟩
  · intro qL qR
    apply WF.GadgetSpec.bind_rule_direct
      (left := left.2.1) (right := right.2.1)
      canonicalizeSignature_wf_aux
    · intro lv rv h
      exact ⟨h.1.2.2.1, h.1.2.2.2.1⟩
    · intro rsL rsR
      apply WF.GadgetSpec.bind_rule_direct
        (left := left.2.2) (right := right.2.2) canonicalizeAux_wf_aux
      · intro lv rv h
        exact ⟨h.1.1.2.2.2.2.1, h.1.1.2.2.2.2.2⟩
      · intro invsL invsR
        apply WF.Rel.pure
        intro lv rv h
        exact ⟨h.1.1.2.1, h.1.1.2.2,
          h.1.2.1, h.1.2.2, h.2.1, h.2.2⟩

def PrepareInput.WFRel : WF.Post (U 256 × CanonicalInput) :=
  fun lv rv left right =>
    U.FullWFRel lv rv left.1 right.1 ∧
    CanonicalInput.WFRel lv rv left.2 right.2

def PreparedVerification.WFRel (lv rv : WF.Valuation)
    (left right : PreparedVerification) : Prop :=
  Modular.Elem.ScalarWFRel lv rv left.u1 right.u1 ∧
  Modular.Elem.ScalarWFRel lv rv left.u2 right.u2 ∧
  Projective.WFRel lv rv left.q right.q ∧
  Modular.Elem.WFRel lv rv left.r right.r

private theorem ofElem_rep_wfRel {p : Modular.Params n}
    {lv rv : WF.Valuation} {left right : Modular.Elem p}
    (h : Modular.Elem.FullWFRel lv rv left right) :
    Modular.Lazy.Rep.WFRel lv rv
      (Modular.Lazy.ofElem p left) (Modular.Lazy.ofElem p right) :=
  ⟨rfl, h.1.1⟩

private theorem fnOne_rep_wfRel (lv rv : WF.Valuation) :
    Modular.Lazy.Rep.WFRel lv rv
      (Modular.Lazy.ofElem scalar fnOne)
      (Modular.Lazy.ofElem scalar fnOne) :=
  ⟨rfl, (fnOne_wfRel lv rv).1⟩

private theorem one_wfRel (lv rv : WF.Valuation) :
    Modular.Elem.WFRel lv rv one one := by
  unfold one fpConst Modular.ofNat Modular.Elem.WFRel
  exact U.wfRel_bitVec lv rv (BitVec.ofNat 256 1)

theorem validateCanonicalInput_wf_aux :
    WF.GadgetSpec CanonicalInput.WFRel validateCanonicalInput
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold validateCanonicalInput
  apply WF.GadgetSpec.bind_rule_direct
    (left := (left.qx, left.qy)) (right := (right.qx, right.qy))
    Projective.Lazy.assertOnCurve_wf_aux
  · intro lv rv h
    exact ⟨h.1.1, h.2.1.1⟩
  · intro _ _
    apply WF.GadgetSpec.bind_rule_direct
      (left := (Modular.Lazy.ofElem scalar left.r,
        Modular.Lazy.ofElem scalar left.rInv,
        Modular.Lazy.ofElem scalar fnOne))
      (right := (Modular.Lazy.ofElem scalar right.r,
        Modular.Lazy.ofElem scalar right.rInv,
        Modular.Lazy.ofElem scalar fnOne))
      (Modular.Lazy.assertMulEq_wf scalar)
    · intro lv rv h
      exact ⟨ofElem_rep_wfRel h.1.2.2.1,
        ofElem_rep_wfRel h.1.2.2.2.2.1, fnOne_rep_wfRel lv rv⟩
    · intro _ _
      apply WF.GadgetSpec.direct_rule
        (left := (Modular.Lazy.ofElem scalar left.s,
          Modular.Lazy.ofElem scalar left.sInv,
          Modular.Lazy.ofElem scalar fnOne))
        (right := (Modular.Lazy.ofElem scalar right.s,
          Modular.Lazy.ofElem scalar right.sInv,
          Modular.Lazy.ofElem scalar fnOne))
        (Modular.Lazy.assertMulEq_wf scalar)
      intro lv rv h
      exact ⟨ofElem_rep_wfRel h.1.1.2.2.2.1,
        ofElem_rep_wfRel h.1.1.2.2.2.2.2,
        fnOne_rep_wfRel lv rv⟩

def ElemPair.WFRel {p : Modular.Params n} :
    WF.Post (Modular.Elem p × Modular.Elem p) :=
  fun lv rv left right =>
    Modular.Elem.WFRel lv rv left.1 right.1 ∧
    Modular.Elem.WFRel lv rv left.2 right.2

def ElemPair.ScalarWFRel {p : Modular.Params n} :
    WF.Post (Modular.Elem p × Modular.Elem p) :=
  fun lv rv left right =>
    Modular.Elem.ScalarWFRel lv rv left.1 right.1 ∧
    Modular.Elem.ScalarWFRel lv rv left.2 right.2

def MultiplyScalars.WFRel : WF.Post (Fn × CanonicalInput) :=
  fun lv rv left right =>
    Modular.Elem.WFRel lv rv left.1 right.1 ∧
    CanonicalInput.WFRel lv rv left.2 right.2

theorem multiplyScalars_wf_aux :
    WF.GadgetSpec MultiplyScalars.WFRel
      (fun input => multiplyScalars input.1 input.2)
      (ElemPair.WFRel (p := scalar)) := by
  unfold WF.GadgetSpec
  intro left right
  unfold multiplyScalars
  apply WF.GadgetSpec.bind_rule
    (left := (left.1, left.2.sInv))
    (right := (right.1, right.2.sInv))
    (Modular.Relaxed.mul_wf scalar)
  · intro lv rv h
    exact ⟨h.1, h.2.2.2.2.2.2.1⟩
  · intro B u1L u1R hu1
    apply WF.GadgetSpec.bind_rule
      (left := (left.2.r, left.2.sInv))
      (right := (right.2.r, right.2.sInv))
      (Modular.Relaxed.mul_wf scalar)
    · intro lv rv hB
      have h := hu1 lv rv hB
      exact ⟨h.1.2.2.2.1.1, h.1.2.2.2.2.2.2.1⟩
    · intro C u2L u2R hu2
      apply WF.Rel.pure
      intro lv rv hC
      have h2 := hu2 lv rv hC
      have h1 := hu1 lv rv h2.1
      exact ⟨h1.2, h2.2⟩

theorem deriveRelaxedScalars_wf_aux :
    WF.GadgetSpec PrepareInput.WFRel
      (fun input => deriveRelaxedScalars input.1 input.2)
      (ElemPair.WFRel (p := scalar)) := by
  unfold WF.GadgetSpec
  intro left right
  unfold deriveRelaxedScalars
  apply WF.GadgetSpec.bind_rule_direct
    (left := left.1.intVal) (right := right.1.intVal)
    (Modular.Relaxed.reduceSmall_wf scalar)
  · intro lv rv h
    exact h.1.1.1
  · intro zL zR
    apply WF.GadgetSpec.direct_rule
      (left := (zL, left.2)) (right := (zR, right.2))
      multiplyScalars_wf_aux
    intro lv rv h
    exact ⟨h.2, h.1.2⟩

theorem canonicalizeScalars_wf_aux :
    WF.GadgetSpec (ElemPair.WFRel (p := scalar)) canonicalizeScalars
      (ElemPair.ScalarWFRel (p := scalar)) := by
  unfold WF.GadgetSpec
  intro left right
  unfold canonicalizeScalars
  apply WF.GadgetSpec.bind_rule
    (left := Modular.Lazy.ofElem scalar left.1)
    (right := Modular.Lazy.ofElem scalar right.1)
    (Modular.Lazy.reduce_wf_scalar_aux scalar)
  · intro lv rv h
    exact ⟨rfl, h.1.1⟩
  · intro B u1L u1R hu1
    apply WF.GadgetSpec.bind_rule
      (left := Modular.Lazy.ofElem scalar left.2)
      (right := Modular.Lazy.ofElem scalar right.2)
      (Modular.Lazy.reduce_wf_scalar_aux scalar)
    · intro lv rv hB
      exact ⟨rfl, (hu1 lv rv hB).1.2.1⟩
    · intro C u2L u2R hu2
      apply WF.Rel.pure
      intro lv rv hC
      have h2 := hu2 lv rv hC
      have h1 := hu1 lv rv h2.1
      exact ⟨h1.2, h2.2⟩

theorem deriveScalars_wf_aux :
    WF.GadgetSpec PrepareInput.WFRel
      (fun input => deriveScalars input.1 input.2)
      (ElemPair.ScalarWFRel (p := scalar)) := by
  unfold WF.GadgetSpec
  intro left right
  unfold deriveScalars
  apply WF.GadgetSpec.bind_rule_direct
    (left := left) (right := right) deriveRelaxedScalars_wf_aux
  · intro lv rv h
    exact h
  · intro relaxedL relaxedR
    apply WF.GadgetSpec.direct_rule
      (left := relaxedL) (right := relaxedR) canonicalizeScalars_wf_aux
    intro lv rv h
    exact h.2

theorem prepareVerification_wf_aux :
    WF.GadgetSpec PrepareInput.WFRel
      (fun input => prepareVerification input.1 input.2)
      PreparedVerification.WFRel := by
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
        ⟨hc.1.1, hc.2.1.1, one_wfRel lv rv⟩, hc.2.2.1.1⟩

theorem computeVerificationSum_wf_aux :
    WF.GadgetSpec PreparedVerification.WFRel computeVerificationSum
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold computeVerificationSum
  apply WF.GadgetSpec.direct_rule
    (left := (left.u1, left.u2, left.q))
    (right := (right.u1, right.u2, right.q)) jointScalarMul_wf_aux
  intro lv rv h
  exact ⟨h.1, h.2.1, h.2.2.1⟩

def CheckVerificationX.WFRel :
    WF.Post (Fn × AffineSlope.Point) :=
  fun lv rv left right =>
    Modular.Elem.WFRel lv rv left.1 right.1 ∧
    AffineSlope.Point.WFRel lv rv left.2 right.2

theorem checkVerificationX_wf_aux :
    WF.GadgetSpec CheckVerificationX.WFRel
      (fun input => checkVerificationX input.1 input.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold checkVerificationX
  apply WF.Rel.assertR1C
  · intro _ _ _
    rfl
  · intro _ _ _
    rfl
  · intro lv rv h
    exact h.2.2.2
  · apply WF.GadgetSpec.bind_rule
      (left := left.2.X) (right := right.2.X)
      (Modular.Lazy.reduce_wf base)
    · intro lv rv h
      exact h.2.1
    · intro B xL xR hx
      apply WF.GadgetSpec.bind_rule
        (left := xL.val.intVal) (right := xR.val.intVal)
        (Modular.Relaxed.reduceSmall_wf scalar)
      · intro lv rv hB
        exact (hx lv rv hB).2.1
      · intro C xModL xModR hxMod
        apply WF.GadgetSpec.direct_rule
          (left := (xModL, left.1)) (right := (xModR, right.1))
          (Modular.assertEq_wf scalar)
        intro lv rv hC
        have hm := hxMod lv rv hC
        have hc := hx lv rv hm.1
        exact ⟨hm.2, hc.1.1⟩

theorem finishVerification_wf_aux :
    WF.GadgetSpec PreparedVerification.WFRel finishVerification
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold finishVerification
  apply WF.GadgetSpec.bind_rule_direct
    (left := left) (right := right) computeVerificationSum_wf_aux
  · intro lv rv h
    exact h
  · intro sumL sumR
    apply WF.GadgetSpec.direct_rule
      (left := (left.r, sumL)) (right := (right.r, sumR))
      checkVerificationX_wf_aux
    intro lv rv h
    exact ⟨h.1.2.2.2, h.2⟩

theorem verifyDigest_wf_aux :
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
      prepareVerification_wf_aux
    · intro lv rv h
      exact ⟨h.1.1, h.2⟩
    · intro preparedL preparedR
      apply WF.GadgetSpec.direct_rule
        (left := preparedL) (right := preparedR) finishVerification_wf_aux
      intro lv rv h
      exact h.2

end Freigen.F2Z.Examples.EcdsaP256
