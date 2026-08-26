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
      h![left.1, left.2.2[0].intVal, left.2.2[1].intVal,
        left.2.2[2].intVal, left.2.2[3].intVal, left.2.2[4].intVal,
        left.2.2[5].intVal, left.2.2[6].intVal, left.2.2[7].intVal,
        left.2.2[8].intVal, left.2.2[9].intVal, left.2.2[10].intVal,
        left.2.2[11].intVal, left.2.2[12].intVal, left.2.2[13].intVal,
        left.2.2[14].intVal, left.2.2[15].intVal]
      h![right.1, right.2.2[0].intVal, right.2.2[1].intVal,
        right.2.2[2].intVal, right.2.2[3].intVal, right.2.2[4].intVal,
        right.2.2[5].intVal, right.2.2[6].intVal, right.2.2[7].intVal,
        right.2.2[8].intVal, right.2.2[9].intVal, right.2.2[10].intVal,
        right.2.2[11].intVal, right.2.2[12].intVal, right.2.2[13].intVal,
        right.2.2[14].intVal, right.2.2[15].intVal] := by
  rcases h with ⟨hd, _, hx⟩
  unfold WF.LCEq at hd
  have h0 := (hx ⟨0, by omega⟩).2
  have h1 := (hx ⟨1, by omega⟩).2
  have h2 := (hx ⟨2, by omega⟩).2
  have h3 := (hx ⟨3, by omega⟩).2
  have h4 := (hx ⟨4, by omega⟩).2
  have h5 := (hx ⟨5, by omega⟩).2
  have h6 := (hx ⟨6, by omega⟩).2
  have h7 := (hx ⟨7, by omega⟩).2
  have h8 := (hx ⟨8, by omega⟩).2
  have h9 := (hx ⟨9, by omega⟩).2
  have h10 := (hx ⟨10, by omega⟩).2
  have h11 := (hx ⟨11, by omega⟩).2
  have h12 := (hx ⟨12, by omega⟩).2
  have h13 := (hx ⟨13, by omega⟩).2
  have h14 := (hx ⟨14, by omega⟩).2
  have h15 := (hx ⟨15, by omega⟩).2
  unfold WF.LCEq at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp only [Fin.getElem_fin] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp only [WF.ArgsEq, WF.evalArgs]
  rw [hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, h15]

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
          ((fun h![(d : Int), (x0 : Int), (x1 : Int), (x2 : Int),
              (x3 : Int), (x4 : Int), (x5 : Int), (x6 : Int), (x7 : Int),
              (x8 : Int), (x9 : Int), (x10 : Int), (x11 : Int),
              (x12 : Int), (x13 : Int), (x14 : Int), (x15 : Int)] =>
            let values := #[x0, x1, x2, x3, x4, x5, x6, x7,
              x8, x9, x10, x11, x12, x13, x14, x15]
            let chosen := values[d.toNat]!
            pure $ Vector.ofFn (n := 256) fun i =>
              chosen.toNat.testBit i)
            (WF.evalArgs lv h![left.1,
              left.2.2[0].intVal, left.2.2[1].intVal,
              left.2.2[2].intVal, left.2.2[3].intVal,
              left.2.2[4].intVal, left.2.2[5].intVal,
              left.2.2[6].intVal, left.2.2[7].intVal,
              left.2.2[8].intVal, left.2.2[9].intVal,
              left.2.2[10].intVal, left.2.2[11].intVal,
              left.2.2[12].intVal, left.2.2[13].intVal,
              left.2.2[14].intVal, left.2.2[15].intVal])) values ∧
        WF.HintReturns
          ((fun h![(d : Int), (x0 : Int), (x1 : Int), (x2 : Int),
              (x3 : Int), (x4 : Int), (x5 : Int), (x6 : Int), (x7 : Int),
              (x8 : Int), (x9 : Int), (x10 : Int), (x11 : Int),
              (x12 : Int), (x13 : Int), (x14 : Int), (x15 : Int)] =>
            let values := #[x0, x1, x2, x3, x4, x5, x6, x7,
              x8, x9, x10, x11, x12, x13, x14, x15]
            let chosen := values[d.toNat]!
            pure $ Vector.ofFn (n := 256) fun i =>
              chosen.toNat.testBit i)
            (WF.evalArgs rv h![right.1,
              right.2.2[0].intVal, right.2.2[1].intVal,
              right.2.2[2].intVal, right.2.2[3].intVal,
              right.2.2[4].intVal, right.2.2[5].intVal,
              right.2.2[6].intVal, right.2.2[7].intVal,
              right.2.2[8].intVal, right.2.2[9].intVal,
              right.2.2[10].intVal, right.2.2[11].intVal,
              right.2.2[12].intVal, right.2.2[13].intVal,
              right.2.2[14].intVal, right.2.2[15].intVal])) values ∧
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
      h![left.1, left.2.2[0], left.2.2[1], left.2.2[2], left.2.2[3],
        left.2.2[4], left.2.2[5], left.2.2[6], left.2.2[7],
        left.2.2[8], left.2.2[9], left.2.2[10], left.2.2[11],
        left.2.2[12], left.2.2[13], left.2.2[14], left.2.2[15]]
      h![right.1, right.2.2[0], right.2.2[1], right.2.2[2], right.2.2[3],
        right.2.2[4], right.2.2[5], right.2.2[6], right.2.2[7],
        right.2.2[8], right.2.2[9], right.2.2[10], right.2.2[11],
        right.2.2[12], right.2.2[13], right.2.2[14], right.2.2[15]] := by
  rcases h with ⟨hd, _, hf⟩
  unfold WF.LCEq at hd hf
  have h0 := hf ⟨0, by omega⟩
  have h1 := hf ⟨1, by omega⟩
  have h2 := hf ⟨2, by omega⟩
  have h3 := hf ⟨3, by omega⟩
  have h4 := hf ⟨4, by omega⟩
  have h5 := hf ⟨5, by omega⟩
  have h6 := hf ⟨6, by omega⟩
  have h7 := hf ⟨7, by omega⟩
  have h8 := hf ⟨8, by omega⟩
  have h9 := hf ⟨9, by omega⟩
  have h10 := hf ⟨10, by omega⟩
  have h11 := hf ⟨11, by omega⟩
  have h12 := hf ⟨12, by omega⟩
  have h13 := hf ⟨13, by omega⟩
  have h14 := hf ⟨14, by omega⟩
  have h15 := hf ⟨15, by omega⟩
  simp only [Fin.getElem_fin] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp only [WF.ArgsEq, WF.evalArgs]
  rw [hd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, h15]

theorem lookupFlag_wf_aux :
    WF.GadgetSpec FlagLookupRel
      (fun input => lookupFlag input.1 input.2.1 input.2.2)
      (fun lv rv left right => WF.LCEq lv.int rv.int left right) := by
  wfgen' using [assertLookupFlag_wf_aux]
    unfold [lookupFlag, FlagLookupRel]
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

theorem windowDigit_wf_aux (i : Nat) (hi : i < 64) :
    WF.GadgetSpec Modular.Elem.ScalarWFRel
      (fun k => windowDigit k i hi)
      (fun lv rv left right => WF.LCEq lv.int rv.int left right) := by
  unfold WF.GadgetSpec
  intro left right
  unfold windowDigit
  apply WF.Rel.pure
  intro lv rv h
  unfold WF.LCEq
  have h0 := h.2 ⟨252 - 4 * i, by omega⟩
  have h1 := h.2 ⟨252 - 4 * i + 1, by omega⟩
  have h2 := h.2 ⟨252 - 4 * i + 2, by omega⟩
  have h3 := h.2 ⟨252 - 4 * i + 3, by omega⟩
  simp only [WF.LCEq, Fin.getElem_fin] at h0 h1 h2 h3
  simp only [LC.eval_add, LC.eval_nsmul]
  rw [h0, h1, h2, h3]

theorem windowByte_wf_aux (i : Nat) (hi : i < 32) :
    WF.GadgetSpec Modular.Elem.ScalarWFRel
      (fun k => windowByte k i hi)
      (fun lv rv left right => WF.LCEq lv.int rv.int left right) := by
  unfold WF.GadgetSpec
  intro left right
  unfold windowByte
  apply WF.Rel.pure
  intro lv rv h
  unfold WF.LCEq
  have h0 := h.2 ⟨248 - 8 * i, by omega⟩
  have h1 := h.2 ⟨248 - 8 * i + 1, by omega⟩
  have h2 := h.2 ⟨248 - 8 * i + 2, by omega⟩
  have h3 := h.2 ⟨248 - 8 * i + 3, by omega⟩
  have h4 := h.2 ⟨248 - 8 * i + 4, by omega⟩
  have h5 := h.2 ⟨248 - 8 * i + 5, by omega⟩
  have h6 := h.2 ⟨248 - 8 * i + 6, by omega⟩
  have h7 := h.2 ⟨248 - 8 * i + 7, by omega⟩
  simp only [WF.LCEq, Fin.getElem_fin] at h0 h1 h2 h3 h4 h5 h6 h7
  simp only [LC.eval_add, LC.eval_nsmul]
  rw [h0, h1, h2, h3, h4, h5, h6, h7]

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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
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
