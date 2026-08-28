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
set_option maxHeartbeats 200000

private def IntWFRel {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx)
    (left : leftCtx.Wℤ) (right : rightCtx.Wℤ) : Prop :=
  WF.LCEq lv.int rv.int left right

private def BoolWFRel {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx)
    (left : leftCtx.WBool) (right : rightCtx.WBool) : Prop :=
  WF.LCEq lv.bool rv.bool left right

/-- Equality of every linear combination stored in a word, under the two
total valuations.  `U.WFRel` deliberately omits the cached integer bits; the
ECDSA window code consumes those bits directly, so its quotient relation must
retain them as well. -/
def U.FullWFRel {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx)
    (left : @U leftCtx n) (right : @U rightCtx n) : Prop :=
  U.WFRel lv rv left right ∧
    ∀ i : Fin n, WF.LCEq lv.int rv.int
      (@U.intBits leftCtx n left)[i] (@U.intBits rightCtx n right)[i]

def Modular.Elem.FullWFRel {p : Modular.Params n}
    {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx)
    (left : @Modular.Elem n leftCtx p)
    (right : @Modular.Elem n rightCtx p) : Prop :=
  U.FullWFRel lv rv (@Modular.Elem.val n leftCtx p left)
    (@Modular.Elem.val n rightCtx p right)

/-- The scalar-multiplication quotient only observes the canonical integer and
its cached integer bits; Boolean source bits are not part of this boundary. -/
def U.ScalarWFRel {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx)
    (left : @U leftCtx n) (right : @U rightCtx n) : Prop :=
  WF.LCEq lv.int rv.int (@U.intVal leftCtx n left)
      (@U.intVal rightCtx n right) ∧
    ∀ i : Fin n, WF.LCEq lv.int rv.int
      (@U.intBits leftCtx n left)[i] (@U.intBits rightCtx n right)[i]

def Modular.Elem.ScalarWFRel {p : Modular.Params n}
    {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx)
    (left : @Modular.Elem n leftCtx p)
    (right : @Modular.Elem n rightCtx p) : Prop :=
  U.ScalarWFRel lv rv (@Modular.Elem.val n leftCtx p left)
    (@Modular.Elem.val n rightCtx p right)

theorem U.fromWord_wf_scalar :
    WF.GadgetSpec
      (fun {leftCtx rightCtx} lv rv
          (left : @Word leftCtx n) (right : @Word rightCtx n) => ∀ i : Fin n,
        WF.LCEq lv.bool rv.bool left[i] right[i])
      U.fromWord U.ScalarWFRel := by
  intro leftCtx rightCtx left right
  apply WF.Rel.mono (U.fromWord_wf_full leftCtx rightCtx left right)
  intro _ _ _ _ h
  exact ⟨h.2.2, h.2.1⟩

/-- Quotient-backend equality for verifier inputs.  It is intentionally
extensional: every circuit-visible LC has equal value under every related pair
of total valuations. -/
def VerifyInput.WFRel {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx)
    (left : @VerifyInput leftCtx) (right : @VerifyInput rightCtx) : Prop :=
  U.FullWFRel lv rv left.1 right.1 ∧
    U.FullWFRel lv rv (@PublicKey.x leftCtx left.2.1)
      (@PublicKey.x rightCtx right.2.1) ∧
    U.FullWFRel lv rv (@PublicKey.y leftCtx left.2.1)
      (@PublicKey.y rightCtx right.2.1) ∧
    U.FullWFRel lv rv (@Signature.r leftCtx left.2.2.1)
      (@Signature.r rightCtx right.2.2.1) ∧
    U.FullWFRel lv rv (@Signature.s leftCtx left.2.2.1)
      (@Signature.s rightCtx right.2.2.1) ∧
    U.FullWFRel lv rv (@Aux.rInv leftCtx left.2.2.2)
      (@Aux.rInv rightCtx right.2.2.2) ∧
    U.FullWFRel lv rv (@Aux.sInv leftCtx left.2.2.2)
      (@Aux.sInv rightCtx right.2.2.2)

private theorem projective_ofElems_wfRel {leftCtx rightCtx : Context}
    {lv : @WF.Valuation leftCtx} {rv : @WF.Valuation rightCtx}
    {left : @Projective leftCtx} {right : @Projective rightCtx}
    (h : Projective.WFRel lv rv left right) :
    AffineSlope.Point.WFRel lv rv
      (@AffineSlope.ofElems leftCtx (@Projective.X leftCtx left)
        (@Projective.Y leftCtx left))
      (@AffineSlope.ofElems rightCtx (@Projective.X rightCtx right)
        (@Projective.Y rightCtx right)) :=
  AffineSlope.ofElems_wfRel h.1 h.2.1

set_option maxHeartbeats 2000000 in
theorem materializeMultiples_wf_aux :
    WF.GadgetSpec Projective.WFRel materializeMultiples
      (WF.VectorRel AffineSlope.Point.WFRel) := by
  wfgen' using [AffineSlope.addComplete_wf_aux]
    unfold [materializeMultiples]
  case vc1 =>
    rename_i _ _ _ h1 _ _ _ h2 _ _ _ h3 _ _ _ h4
      _ _ _ h5 _ _ _ h6 _ _ _ h7 _ _ _ h8 _ _ _ h9
      _ _ _ h10 _ _ _ h11 _ _ _ h12 _ _ _ h13 h14 hB
    have r15 := h14 leftVal rightVal hB
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
    have r1 := projective_ofElems_wfRel r2.1
    intro i
    fin_cases i <;>
      simp only [Fin.getElem_fin, Vector.getElem_mk,
        ← Array.getElem_toList, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · exact AffineSlope.infinity_wfRel leftVal rightVal
    · exact r1
    · exact r2.2
    · exact r3.2
    · exact r4.2
    · exact r5.2
    · exact r6.2
    · exact r7.2
    · exact r8.2
    · exact r9.2
    · exact r10.2
    · exact r11.2
    · exact r12.2
    · exact r13.2
    · exact r14.2
    · exact r15.2
  all_goals apply projective_ofElems_wfRel
  all_goals grind (ematch := 20)

theorem indicators_wf_aux (n : Nat) :
    WF.GadgetSpec
      (fun {leftCtx rightCtx} lv rv
          (left : leftCtx.Wℤ) (right : rightCtx.Wℤ) =>
        WF.LCEq lv.int rv.int left right)
      (indicators n) U.FullWFRel := by
  wfgen' using [U.fromWord_wf_full] unfold [indicators, U.FullWFRel]
  case vc1 =>
    rename_i hpost hB
    have h := hpost leftVal rightVal hB
    exact ⟨⟨h.2.2.2, h.2.1⟩, h.2.2.1⟩
  case vc7 =>
    rename_i h
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) i.val i.isLt
  all_goals simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

def RepLookupRel {leftCtx rightCtx : Context} :
    WF.Post leftCtx rightCtx
      (leftCtx.Wℤ × @U leftCtx 16 ×
        Vector (@AffineSlope.Rep leftCtx) 16)
      (rightCtx.Wℤ × @U rightCtx 16 ×
        Vector (@AffineSlope.Rep rightCtx) 16) :=
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

private theorem lookupArgs_argsEq {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx)
    (digitL : leftCtx.Wℤ) (digitR : rightCtx.Wℤ)
    (valuesL : Vector leftCtx.Wℤ 16)
    (valuesR : Vector rightCtx.Wℤ 16)
    (hd : WF.LCEq lv.int rv.int digitL digitR)
    (hv : ∀ i : Fin 16, WF.LCEq lv.int rv.int valuesL[i] valuesR[i]) :
    WF.ArgsEq lv rv (@lookupArgs leftCtx digitL valuesL)
      (@lookupArgs rightCtx digitR valuesR) := by
  unfold WF.LCEq at hd
  have hv' (i : Nat) (hi : i < 16) :
      lv.int valuesL[i] = rv.int valuesR[i] := by
    exact hv ⟨i, hi⟩
  simp only [WF.ArgsEq, lookupArgs, WF.evalArgs]
  rw [hd]
  rw_fin16 hv'

theorem assertLookupRep_wf_aux :
    WF.GadgetSpec
      (fun {leftCtx rightCtx} lv rv
          (left : @U leftCtx 16 × @U leftCtx 256 ×
            Vector (@AffineSlope.Rep leftCtx) 16)
          (right : @U rightCtx 16 × @U rightCtx 256 ×
            Vector (@AffineSlope.Rep rightCtx) 16) =>
        U.FullWFRel lv rv left.1 right.1 ∧ U.WFRel lv rv left.2.1 right.2.1 ∧
        WF.VectorRel Modular.Lazy.Rep.WFRel lv rv left.2.2 right.2.2)
      (fun input => assertLookupRep input.1 input.2.1 input.2.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro leftCtx rightCtx left right
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
      simp [WF.LCEq]
    · intro lv rv hP
      exact ⟨hP, hrel lv rv hP⟩
  · intro _ _ _ _ _
    trivial

private theorem repLookup_argsEq {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx)
    (left : leftCtx.Wℤ × @U leftCtx 16 ×
      Vector (@AffineSlope.Rep leftCtx) 16)
    (right : rightCtx.Wℤ × @U rightCtx 16 ×
      Vector (@AffineSlope.Rep rightCtx) 16)
    (h : RepLookupRel lv rv left right) :
    WF.ArgsEq lv rv
      (@lookupArgs leftCtx left.1
        (left.2.2.map (fun x => @Modular.Lazy.Rep.intVal 256 leftCtx base x)))
      (@lookupArgs rightCtx right.1
        (right.2.2.map (fun x => @Modular.Lazy.Rep.intVal 256 rightCtx base x))) := by
  apply lookupArgs_argsEq lv rv
  · exact h.1
  · intro i
    simpa using (h.2.2 i).2

theorem lookupRepWord_wf_aux :
    WF.GadgetSpec RepLookupRel
      (fun input => lookupRepWord input.1 input.2.2)
      U.FullWFRel := by
  unfold WF.GadgetSpec
  intro leftCtx rightCtx left right
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
    let S : WF.Assumption leftCtx rightCtx := fun lv rv =>
      RepLookupRel lv rv left right ∧ ∃ values,
        WF.HintReturns
          (lookupRepHint (WF.evalArgs leftCtx lv
            (@lookupArgs leftCtx left.1
              (left.2.2.map (fun x =>
                @Modular.Lazy.Rep.intVal 256 leftCtx base x))))) values ∧
        WF.HintReturns
          (lookupRepHint (WF.evalArgs rightCtx rv
            (@lookupArgs rightCtx right.1
              (right.2.2.map (fun x =>
                @Modular.Lazy.Rep.intVal 256 rightCtx base x))))) values ∧
        WF.RealizesBools lv.bool bitsL values ∧
        WF.RealizesBools rv.bool bitsR values
    have hbits : ∀ lv rv, S lv rv → ∀ i : Fin 256,
        WF.LCEq lv.bool rv.bool bitsL[i] bitsR[i] := by
      intro lv rv h i
      dsimp [S] at h
      rcases h.2 with ⟨values, _, _, hleft, hright⟩
      exact Modular.Aux.WF.lceq_of_common_realizes
        ⟨values, hleft, hright⟩ i.val i.isLt
    let wordL : @Word leftCtx 256 := @Word.mk leftCtx 256 bitsL
    let wordR : @Word rightCtx 256 := @Word.mk rightCtx 256 bitsR
    have hword := U.fromWord_wf_full.relHom leftCtx rightCtx S
      wordL wordR
      (fun lv rv h => by simpa [wordL, wordR] using hbits lv rv h)
    change WF.Rel U.FullWFRel S
      (@U.fromWord leftCtx 256 wordL) (@U.fromWord rightCtx 256 wordR)
    exact WF.Rel.mono hword (by
      intro lv rv outL outR h
      exact ⟨⟨h.2.2.2, h.2.1⟩, h.2.2.1⟩)

theorem lookupRep_wf_aux :
    WF.GadgetSpec RepLookupRel
      (fun input => lookupRep input.1 input.2.1 input.2.2)
      Modular.Lazy.Rep.WFRel := by
  unfold WF.GadgetSpec
  intro leftCtx rightCtx left right
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

def FlagLookupRel {leftCtx rightCtx : Context} :
    WF.Post leftCtx rightCtx
      (leftCtx.Wℤ × @U leftCtx 16 × Vector leftCtx.Wℤ 16)
      (rightCtx.Wℤ × @U rightCtx 16 × Vector rightCtx.Wℤ 16) :=
  fun lv rv left right =>
    WF.LCEq lv.int rv.int left.1 right.1 ∧
    U.FullWFRel lv rv left.2.1 right.2.1 ∧
    WF.VectorRel IntWFRel
      lv rv left.2.2 right.2.2

theorem assertLookupFlag_wf_aux :
    WF.GadgetSpec
      (fun {leftCtx rightCtx} lv rv
          (left : @U leftCtx 16 × leftCtx.Wℤ × Vector leftCtx.Wℤ 16)
          (right : @U rightCtx 16 × rightCtx.Wℤ × Vector rightCtx.Wℤ 16) =>
        U.FullWFRel lv rv left.1 right.1 ∧
        WF.LCEq lv.int rv.int left.2.1 right.2.1 ∧
        WF.VectorRel IntWFRel
          lv rv left.2.2 right.2.2)
      (fun input => assertLookupFlag input.1 input.2.1 input.2.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro leftCtx rightCtx left right
  simp only
  unfold assertLookupFlag
  refine WF.Rel.mono (WF.Rel.foldRange_rule
    (I := fun lv rv (_ _ : Unit) =>
      U.FullWFRel lv rv left.1 right.1 ∧
      WF.LCEq lv.int rv.int left.2.1 right.2.1 ∧
      WF.VectorRel IntWFRel
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
      simp [WF.LCEq]
    · intro lv rv hP
      exact ⟨hP, hrel lv rv hP⟩
  · intro _ _ _ _ _
    trivial

private theorem flagLookup_argsEq {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx)
    (left : leftCtx.Wℤ × @U leftCtx 16 × Vector leftCtx.Wℤ 16)
    (right : rightCtx.Wℤ × @U rightCtx 16 × Vector rightCtx.Wℤ 16)
    (h : FlagLookupRel lv rv left right) :
    WF.ArgsEq lv rv
      (@lookupArgs leftCtx left.1 left.2.2)
      (@lookupArgs rightCtx right.1 right.2.2) := by
  exact lookupArgs_argsEq lv rv _ _ _ _ h.1 h.2.2

theorem lookupFlag_wf_aux :
    WF.GadgetSpec FlagLookupRel
      (fun input => lookupFlag input.1 input.2.1 input.2.2)
      IntWFRel := by
  wfgen' using [assertLookupFlag_wf_aux]
    unfold [lookupFlag, lookupFlagHint, FlagLookupRel, IntWFRel]
  case vc1 =>
    rename_i hrel hB
    have h := hrel leftVal rightVal hB
    rcases h with ⟨⟨⟨_, values, _, _, hleft, hright⟩, hl, hr⟩, _⟩
    exact hl.trans ((congrArg Bool.toInt
      ((hleft 0 (by omega)).trans (hright 0 (by omega)).symm)).trans hr.symm)
  case vc2 =>
    rename_i h
    rcases h with ⟨⟨_, values, _, _, hleft, hright⟩, hl, hr⟩
    exact hl.trans ((congrArg Bool.toInt
      ((hleft 0 (by omega)).trans (hright 0 (by omega)).symm)).trans hr.symm)
  case vc3 =>
    rename_i h
    exact Modular.Aux.WF.lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_hint h) j.val j.isLt
  case vc4 =>
    refine ⟨?_, ?_, ?_⟩ <;> native_decide
  case vc5 =>
    rename_i h
    have heq := flagLookup_argsEq leftVal rightVal left right h
    unfold WF.ArgsEq at heq
    rw [heq]
    rfl
  case vc6 =>
    rename_i h
    exact flagLookup_argsEq leftVal rightVal left right h

def PointLookupRel {leftCtx rightCtx : Context} :
    WF.Post leftCtx rightCtx
      (leftCtx.Wℤ × Vector (@AffineSlope.Point leftCtx) 16)
      (rightCtx.Wℤ × Vector (@AffineSlope.Point rightCtx) 16) :=
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
  case vc1 =>
    rename_i hIndicators hX hY hFlag hB
    have hf := hFlag leftVal rightVal hB
    have hy := hY leftVal rightVal hf.1
    have hx := hX leftVal rightVal hy.1
    exact ⟨hx.2, hf.2⟩
  case vc2 =>
    rename_i hIndicators hX hY hB
    have hy := hY leftVal rightVal hB
    have hx := hX leftVal rightVal hy.1
    have hi := hIndicators leftVal rightVal hx.1
    exact ⟨hi.1.1, hi.2, fun i => (hi.1.2 i).2.2⟩

theorem windowValue_wf_aux (start width : Nat) (hfit : start + width ≤ 256) :
    WF.GadgetSpec Modular.Elem.ScalarWFRel
      (fun k => pure (windowValue k start width hfit))
      (fun lv rv left right => WF.LCEq lv.int rv.int left right) := by
  unfold WF.GadgetSpec
  intro leftCtx rightCtx left right
  apply WF.Rel.pure
  intro lv rv h
  unfold WF.LCEq at h ⊢
  unfold windowValue
  simp only [map_sum, map_nsmul]
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
  intro leftCtx rightCtx left right
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
  intro leftCtx rightCtx left right
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
      (fun {leftCtx rightCtx} lv rv
          (left : leftCtx.Wℤ) (right : rightCtx.Wℤ) =>
        WF.LCEq lv.int rv.int left right)
      lookupGeneratorByte AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro leftCtx rightCtx left right
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
      simp only [map_sum, map_nsmul]
      apply Finset.sum_congr rfl
      intro j _
      rw [h.2.2 j]
    · unfold WF.LCEq
      simp only [map_sum, map_nsmul]
      apply Finset.sum_congr rfl
      intro j _
      rw [h.2.2 j]

def JointTerms.WFRel {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx)
    (left : @JointTerms leftCtx) (right : @JointTerms rightCtx) : Prop :=
  AffineSlope.Point.WFRel lv rv
      (@JointTerms.qhi leftCtx left) (@JointTerms.qhi rightCtx right) ∧
  AffineSlope.Point.WFRel lv rv
      (@JointTerms.qlo leftCtx left) (@JointTerms.qlo rightCtx right) ∧
  AffineSlope.Point.WFRel lv rv
      (@JointTerms.g leftCtx left) (@JointTerms.g rightCtx right)

theorem selectJointTerms_wf_aux (i : Nat) (hi : i < 32) :
    WF.GadgetSpec
      (fun {leftCtx rightCtx} lv rv
          (left : @Fn leftCtx × @Fn leftCtx ×
            Vector (@AffineSlope.Point leftCtx) 16)
          (right : @Fn rightCtx × @Fn rightCtx ×
            Vector (@AffineSlope.Point rightCtx) 16) =>
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
      (fun {leftCtx rightCtx} lv rv
          (left : @AffineSlope.Point leftCtx × @JointTerms leftCtx)
          (right : @AffineSlope.Point rightCtx × @JointTerms rightCtx) =>
        AffineSlope.Point.WFRel lv rv left.1 right.1 ∧
        JointTerms.WFRel lv rv left.2 right.2)
      (fun input => accumulateJoint input.1 input.2)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro leftCtx rightCtx left right
  unfold accumulateJoint
  apply WF.GadgetSpec.bind_rule
    (left := left.1) (right := right.1) doubleFour_wf_aux
  · intro lv rv h
    exact h.1
  · intro B acc1L acc1R hacc1
    apply WF.GadgetSpec.bind_rule
      (left := (acc1L, @JointTerms.qhi leftCtx left.2))
      (right := (acc1R, @JointTerms.qhi rightCtx right.2))
      AffineSlope.addComplete_wf_aux
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
          (left := (acc3L, @JointTerms.qlo leftCtx left.2))
          (right := (acc3R, @JointTerms.qlo rightCtx right.2))
          AffineSlope.addComplete_wf_aux
        · intro lv rv hD
          have h3 := hacc3 lv rv hD
          have h2 := hacc2 lv rv h3.1
          have h1 := hacc1 lv rv h2.1
          exact ⟨h3.2, h1.1.2.2.1⟩
        · intro E acc4L acc4R hacc4
          apply WF.GadgetSpec.direct_rule
            (left := (acc4L, @JointTerms.g leftCtx left.2))
            (right := (acc4R, @JointTerms.g rightCtx right.2))
            AffineSlope.addComplete_wf_aux
          intro lv rv hE
          have h4 := hacc4 lv rv hE
          have h3 := hacc3 lv rv h4.1
          have h2 := hacc2 lv rv h3.1
          have h1 := hacc1 lv rv h2.1
          exact ⟨h4.2, h1.1.2.2.2⟩

theorem jointByteStep_wf_aux (i : Nat) (hi : i < 32) :
    WF.GadgetSpec
      (fun {leftCtx rightCtx} lv rv
          (left : @Fn leftCtx × @Fn leftCtx ×
            Vector (@AffineSlope.Point leftCtx) 16 × @AffineSlope.Point leftCtx)
          (right : @Fn rightCtx × @Fn rightCtx ×
            Vector (@AffineSlope.Point rightCtx) 16 × @AffineSlope.Point rightCtx) =>
        Modular.Elem.ScalarWFRel lv rv left.1 right.1 ∧
        Modular.Elem.ScalarWFRel lv rv left.2.1 right.2.1 ∧
        WF.VectorRel AffineSlope.Point.WFRel lv rv left.2.2.1 right.2.2.1 ∧
        AffineSlope.Point.WFRel lv rv left.2.2.2 right.2.2.2)
      (fun input => jointByteStep input.1 input.2.1 input.2.2.1 i hi input.2.2.2)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro leftCtx rightCtx left right
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

def JointScalarInput.WFRel {leftCtx rightCtx : Context} :
    WF.Post leftCtx rightCtx
      (@Fn leftCtx × @Fn leftCtx × @Projective leftCtx)
      (@Fn rightCtx × @Fn rightCtx × @Projective rightCtx) :=
  fun lv rv left right =>
    Modular.Elem.ScalarWFRel lv rv left.1 right.1 ∧
    Modular.Elem.ScalarWFRel lv rv left.2.1 right.2.1 ∧
    Projective.WFRel lv rv left.2.2 right.2.2

theorem jointScalarMul_wf_aux :
    WF.GadgetSpec JointScalarInput.WFRel
      (fun input => jointScalarMul input.1 input.2.1 input.2.2)
      AffineSlope.Point.WFRel := by
  unfold WF.GadgetSpec
  intro leftCtx rightCtx left right
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
      have hstep := (jointByteStep_wf_aux i hi.2.1).relHom
        leftCtx rightCtx P
        (left.1, left.2.1, tableL, accL)
        (right.1, right.2.1, tableR, accR) hinput
      exact WF.Rel.mono hstep (by
        intro lv rv outL outR hpost
        exact ⟨hpost.1, (hacc lv rv hpost.1).1, hpost.2⟩
      )
    · intro lv rv outL outR hpost
      exact hpost.2

private theorem fnOne_wfRel {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx) :
    Modular.Elem.WFRel lv rv (@fnOne leftCtx) (@fnOne rightCtx) := by
  unfold fnOne fnConst Modular.ofNat Modular.Elem.WFRel
  exact U.wfRel_bitVec lv rv (BitVec.ofNat 256 1)

theorem Modular.ofU_wf_full_aux {n : Nat} (p : Modular.Params n) :
    WF.GadgetSpec U.FullWFRel (Modular.ofU p)
      (Modular.Elem.FullWFRel (p := p)) := by
  unfold WF.GadgetSpec
  intro leftCtx rightCtx left right
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
  all_goals simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

theorem Modular.ofU_wf_scalar_aux {n : Nat} (p : Modular.Params n) :
    WF.GadgetSpec U.ScalarWFRel (Modular.ofU p)
      (Modular.Elem.ScalarWFRel (p := p)) := by
  unfold WF.GadgetSpec
  intro leftCtx rightCtx left right
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
  case vc4 =>
    rename_i hpost hB
    exact Modular.Aux.WF.wordSlice_lceq_of_common_realizes
      (Modular.Aux.WF.common_realizes_of_post
        (hpost leftVal rightVal hB))
      n (n + Modular.Lazy.quotientExtraBits) (by omega) i
  case vc5 =>
    rename_i h
    simpa only [zero_add, getElem] using
      Modular.Aux.WF.wordSlice_lceq_of_common_realizes
        (Modular.Aux.WF.common_realizes_of_hint h) 0 n (by omega) i
  case vc6 =>
    simp_all [WF.LCEq, Modular.Lazy.Rep.WFRel, WF.evalArgs]
    split <;> simp
  all_goals simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

def CanonicalInput.WFRel {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx)
    (left : @CanonicalInput leftCtx) (right : @CanonicalInput rightCtx) : Prop :=
  Modular.Elem.FullWFRel lv rv
      (@CanonicalInput.qx leftCtx left) (@CanonicalInput.qx rightCtx right) ∧
  Modular.Elem.FullWFRel lv rv
      (@CanonicalInput.qy leftCtx left) (@CanonicalInput.qy rightCtx right) ∧
  Modular.Elem.FullWFRel lv rv
      (@CanonicalInput.r leftCtx left) (@CanonicalInput.r rightCtx right) ∧
  Modular.Elem.FullWFRel lv rv
      (@CanonicalInput.s leftCtx left) (@CanonicalInput.s rightCtx right) ∧
  Modular.Elem.FullWFRel lv rv
      (@CanonicalInput.rInv leftCtx left) (@CanonicalInput.rInv rightCtx right) ∧
  Modular.Elem.FullWFRel lv rv
      (@CanonicalInput.sInv leftCtx left) (@CanonicalInput.sInv rightCtx right)

def CanonicalizeInput.WFRel {leftCtx rightCtx : Context} :
    WF.Post leftCtx rightCtx
      (@PublicKey leftCtx × @Signature leftCtx × @Aux leftCtx)
      (@PublicKey rightCtx × @Signature rightCtx × @Aux rightCtx) :=
  fun lv rv left right =>
    U.FullWFRel lv rv (@PublicKey.x leftCtx left.1)
      (@PublicKey.x rightCtx right.1) ∧
    U.FullWFRel lv rv (@PublicKey.y leftCtx left.1)
      (@PublicKey.y rightCtx right.1) ∧
    U.FullWFRel lv rv (@Signature.r leftCtx left.2.1)
      (@Signature.r rightCtx right.2.1) ∧
    U.FullWFRel lv rv (@Signature.s leftCtx left.2.1)
      (@Signature.s rightCtx right.2.1) ∧
    U.FullWFRel lv rv (@Aux.rInv leftCtx left.2.2)
      (@Aux.rInv rightCtx right.2.2) ∧
    U.FullWFRel lv rv (@Aux.sInv leftCtx left.2.2)
      (@Aux.sInv rightCtx right.2.2)

def ElemPair.FullWFRel {p : Modular.Params n} {leftCtx rightCtx : Context} :
    WF.Post leftCtx rightCtx
      (@Modular.Elem n leftCtx p × @Modular.Elem n leftCtx p)
      (@Modular.Elem n rightCtx p × @Modular.Elem n rightCtx p) :=
  fun lv rv left right =>
    Modular.Elem.FullWFRel lv rv left.1 right.1 ∧
    Modular.Elem.FullWFRel lv rv left.2 right.2

theorem canonicalizeKey_wf_aux :
    WF.GadgetSpec
      (fun {leftCtx rightCtx} lv rv
          (left : @PublicKey leftCtx) (right : @PublicKey rightCtx) =>
        U.FullWFRel lv rv (@PublicKey.x leftCtx left)
            (@PublicKey.x rightCtx right) ∧
        U.FullWFRel lv rv (@PublicKey.y leftCtx left)
          (@PublicKey.y rightCtx right))
      canonicalizeKey (ElemPair.FullWFRel (p := base)) := by
  wfgen' using [Modular.ofU_wf_full_aux]
    unfold [canonicalizeKey, ElemPair.FullWFRel]
  all_goals simp_all [Modular.Elem.FullWFRel, U.FullWFRel, U.WFRel]

theorem canonicalizeSignature_wf_aux :
    WF.GadgetSpec
      (fun {leftCtx rightCtx} lv rv
          (left : @Signature leftCtx) (right : @Signature rightCtx) =>
        U.FullWFRel lv rv (@Signature.r leftCtx left)
            (@Signature.r rightCtx right) ∧
        U.FullWFRel lv rv (@Signature.s leftCtx left)
          (@Signature.s rightCtx right))
      canonicalizeSignature (ElemPair.FullWFRel (p := scalar)) := by
  wfgen' using [Modular.ofU_wf_full_aux]
    unfold [canonicalizeSignature, ElemPair.FullWFRel]
  all_goals simp_all [Modular.Elem.FullWFRel, U.FullWFRel, U.WFRel]

theorem canonicalizeAux_wf_aux :
    WF.GadgetSpec
      (fun {leftCtx rightCtx} lv rv
          (left : @Aux leftCtx) (right : @Aux rightCtx) =>
        U.FullWFRel lv rv (@Aux.rInv leftCtx left)
            (@Aux.rInv rightCtx right) ∧
        U.FullWFRel lv rv (@Aux.sInv leftCtx left)
          (@Aux.sInv rightCtx right))
      canonicalizeAux (ElemPair.FullWFRel (p := scalar)) := by
  wfgen' using [Modular.ofU_wf_full_aux]
    unfold [canonicalizeAux, ElemPair.FullWFRel]
  all_goals simp_all [Modular.Elem.FullWFRel, U.FullWFRel, U.WFRel]

theorem canonicalizeInput_wf_aux :
    WF.GadgetSpec CanonicalizeInput.WFRel
      (fun input => canonicalizeInput input.1 input.2.1 input.2.2)
      CanonicalInput.WFRel := by
  unfold WF.GadgetSpec
  intro leftCtx rightCtx left right
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

def PrepareInput.WFRel {leftCtx rightCtx : Context} :
    WF.Post leftCtx rightCtx
      (@U leftCtx 256 × @CanonicalInput leftCtx)
      (@U rightCtx 256 × @CanonicalInput rightCtx) :=
  fun lv rv left right =>
    U.FullWFRel lv rv left.1 right.1 ∧
    CanonicalInput.WFRel lv rv left.2 right.2

def PreparedVerification.WFRel {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx)
    (left : @PreparedVerification leftCtx)
    (right : @PreparedVerification rightCtx) : Prop :=
  Modular.Elem.ScalarWFRel lv rv
      (@PreparedVerification.u1 leftCtx left)
      (@PreparedVerification.u1 rightCtx right) ∧
  Modular.Elem.ScalarWFRel lv rv
      (@PreparedVerification.u2 leftCtx left)
      (@PreparedVerification.u2 rightCtx right) ∧
  Projective.WFRel lv rv (@PreparedVerification.q leftCtx left)
      (@PreparedVerification.q rightCtx right) ∧
  Modular.Elem.WFRel lv rv (@PreparedVerification.r leftCtx left)
      (@PreparedVerification.r rightCtx right)

private theorem ofElem_rep_wfRel {p : Modular.Params n}
    {leftCtx rightCtx : Context}
    {lv : @WF.Valuation leftCtx} {rv : @WF.Valuation rightCtx}
    {left : @Modular.Elem n leftCtx p}
    {right : @Modular.Elem n rightCtx p}
    (h : Modular.Elem.FullWFRel lv rv left right) :
    Modular.Lazy.Rep.WFRel lv rv
      (@Modular.Lazy.ofElem n p leftCtx left)
      (@Modular.Lazy.ofElem n p rightCtx right) :=
  ⟨rfl, h.1.1⟩

private theorem fnOne_fullWFRel {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx) :
    Modular.Elem.FullWFRel lv rv (@fnOne leftCtx) (@fnOne rightCtx) := by
  unfold Modular.Elem.FullWFRel U.FullWFRel
  refine ⟨fnOne_wfRel lv rv, ?_⟩
  intro i
  unfold fnOne fnConst Modular.ofNat
  simp [WF.LCEq]

private theorem one_wfRel {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx) :
    Modular.Elem.WFRel lv rv (@one leftCtx) (@one rightCtx) := by
  unfold one fpConst Modular.ofNat Modular.Elem.WFRel
  exact U.wfRel_bitVec lv rv (BitVec.ofNat 256 1)

theorem validateCanonicalInput_wf_aux :
    WF.GadgetSpec CanonicalInput.WFRel validateCanonicalInput
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro leftCtx rightCtx left right
  unfold validateCanonicalInput
  apply WF.GadgetSpec.bind_rule_direct
    (left := (@CanonicalInput.qx leftCtx left,
      @CanonicalInput.qy leftCtx left))
    (right := (@CanonicalInput.qx rightCtx right,
      @CanonicalInput.qy rightCtx right))
    Projective.Lazy.assertOnCurve_wf_aux
  · intro lv rv h
    exact ⟨h.1.1, h.2.1.1⟩
  · intro _ _
    apply WF.GadgetSpec.bind_rule_direct
      (left := (@Modular.Lazy.ofElem 256 scalar leftCtx
          (@CanonicalInput.r leftCtx left),
        @Modular.Lazy.ofElem 256 scalar leftCtx
          (@CanonicalInput.rInv leftCtx left),
        @Modular.Lazy.ofElem 256 scalar leftCtx (@fnOne leftCtx)))
      (right := (@Modular.Lazy.ofElem 256 scalar rightCtx
          (@CanonicalInput.r rightCtx right),
        @Modular.Lazy.ofElem 256 scalar rightCtx
          (@CanonicalInput.rInv rightCtx right),
        @Modular.Lazy.ofElem 256 scalar rightCtx (@fnOne rightCtx)))
      (Modular.Lazy.assertMulEq_wf scalar)
    · intro lv rv h
      exact ⟨ofElem_rep_wfRel h.1.2.2.1,
        ofElem_rep_wfRel h.1.2.2.2.2.1,
        ofElem_rep_wfRel (fnOne_fullWFRel lv rv)⟩
    · intro _ _
      apply WF.GadgetSpec.direct_rule
        (left := (@Modular.Lazy.ofElem 256 scalar leftCtx
            (@CanonicalInput.s leftCtx left),
          @Modular.Lazy.ofElem 256 scalar leftCtx
            (@CanonicalInput.sInv leftCtx left),
          @Modular.Lazy.ofElem 256 scalar leftCtx (@fnOne leftCtx)))
        (right := (@Modular.Lazy.ofElem 256 scalar rightCtx
            (@CanonicalInput.s rightCtx right),
          @Modular.Lazy.ofElem 256 scalar rightCtx
            (@CanonicalInput.sInv rightCtx right),
          @Modular.Lazy.ofElem 256 scalar rightCtx (@fnOne rightCtx)))
        (Modular.Lazy.assertMulEq_wf scalar)
      intro lv rv h
      exact ⟨ofElem_rep_wfRel h.1.1.2.2.2.1,
        ofElem_rep_wfRel h.1.1.2.2.2.2.2,
        ofElem_rep_wfRel (fnOne_fullWFRel lv rv)⟩

def ElemPair.WFRel {p : Modular.Params n} {leftCtx rightCtx : Context} :
    WF.Post leftCtx rightCtx
      (@Modular.Elem n leftCtx p × @Modular.Elem n leftCtx p)
      (@Modular.Elem n rightCtx p × @Modular.Elem n rightCtx p) :=
  fun lv rv left right =>
    Modular.Elem.WFRel lv rv left.1 right.1 ∧
    Modular.Elem.WFRel lv rv left.2 right.2

def ElemPair.ScalarWFRel {p : Modular.Params n} {leftCtx rightCtx : Context} :
    WF.Post leftCtx rightCtx
      (@Modular.Elem n leftCtx p × @Modular.Elem n leftCtx p)
      (@Modular.Elem n rightCtx p × @Modular.Elem n rightCtx p) :=
  fun lv rv left right =>
    Modular.Elem.ScalarWFRel lv rv left.1 right.1 ∧
    Modular.Elem.ScalarWFRel lv rv left.2 right.2

def MultiplyScalars.WFRel {leftCtx rightCtx : Context} :
    WF.Post leftCtx rightCtx
      (@Fn leftCtx × @CanonicalInput leftCtx)
      (@Fn rightCtx × @CanonicalInput rightCtx) :=
  fun lv rv left right =>
    Modular.Elem.WFRel lv rv left.1 right.1 ∧
    CanonicalInput.WFRel lv rv left.2 right.2

theorem multiplyScalars_wf_aux :
    WF.GadgetSpec MultiplyScalars.WFRel
      (fun input => multiplyScalars input.1 input.2)
      (ElemPair.WFRel (p := scalar)) := by
  unfold WF.GadgetSpec
  intro leftCtx rightCtx left right
  unfold multiplyScalars
  apply WF.GadgetSpec.bind_rule
    (left := (left.1, @CanonicalInput.sInv leftCtx left.2))
    (right := (right.1, @CanonicalInput.sInv rightCtx right.2))
    (Modular.Relaxed.mul_wf scalar)
  · intro lv rv h
    exact ⟨h.1, h.2.2.2.2.2.2.1⟩
  · intro B u1L u1R hu1
    apply WF.GadgetSpec.bind_rule
      (left := (@CanonicalInput.r leftCtx left.2,
        @CanonicalInput.sInv leftCtx left.2))
      (right := (@CanonicalInput.r rightCtx right.2,
        @CanonicalInput.sInv rightCtx right.2))
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
  intro leftCtx rightCtx left right
  unfold deriveRelaxedScalars
  apply WF.GadgetSpec.bind_rule_direct
    (left := @U.intVal leftCtx 256 left.1)
    (right := @U.intVal rightCtx 256 right.1)
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
  intro leftCtx rightCtx left right
  unfold canonicalizeScalars
  apply WF.GadgetSpec.bind_rule
    (left := @Modular.Lazy.ofElem 256 scalar leftCtx left.1)
    (right := @Modular.Lazy.ofElem 256 scalar rightCtx right.1)
    (Modular.Lazy.reduce_wf_scalar_aux scalar)
  · intro lv rv h
    exact ⟨rfl, h.1.1⟩
  · intro B u1L u1R hu1
    apply WF.GadgetSpec.bind_rule
      (left := @Modular.Lazy.ofElem 256 scalar leftCtx left.2)
      (right := @Modular.Lazy.ofElem 256 scalar rightCtx right.2)
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
  intro leftCtx rightCtx left right
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
  intro leftCtx rightCtx left right
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
  intro leftCtx rightCtx left right
  unfold computeVerificationSum
  apply WF.GadgetSpec.direct_rule
    (left := (@PreparedVerification.u1 leftCtx left,
      @PreparedVerification.u2 leftCtx left,
      @PreparedVerification.q leftCtx left))
    (right := (@PreparedVerification.u1 rightCtx right,
      @PreparedVerification.u2 rightCtx right,
      @PreparedVerification.q rightCtx right)) jointScalarMul_wf_aux
  intro lv rv h
  exact ⟨h.1, h.2.1, h.2.2.1⟩

def CheckVerificationX.WFRel {leftCtx rightCtx : Context} :
    WF.Post leftCtx rightCtx
      (@Fn leftCtx × @AffineSlope.Point leftCtx)
      (@Fn rightCtx × @AffineSlope.Point rightCtx) :=
  fun lv rv left right =>
    Modular.Elem.WFRel lv rv left.1 right.1 ∧
    AffineSlope.Point.WFRel lv rv left.2 right.2

theorem checkVerificationX_wf_aux :
    WF.GadgetSpec CheckVerificationX.WFRel
      (fun input => checkVerificationX input.1 input.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro leftCtx rightCtx left right
  unfold checkVerificationX
  apply WF.Rel.assertR1C
  · intro _ _ _
    simp [WF.LCEq]
  · intro _ _ _
    simp [WF.LCEq]
  · intro lv rv h
    exact h.2.2.2
  · apply WF.GadgetSpec.bind_rule
      (left := @AffineSlope.Point.X leftCtx left.2)
      (right := @AffineSlope.Point.X rightCtx right.2)
      (Modular.Lazy.reduce_wf base)
    · intro lv rv h
      exact h.2.1
    · intro B xL xR hx
      apply WF.GadgetSpec.bind_rule
        (left := @U.intVal leftCtx 256
          (@Modular.Elem.val 256 leftCtx base xL))
        (right := @U.intVal rightCtx 256
          (@Modular.Elem.val 256 rightCtx base xR))
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
  intro leftCtx rightCtx left right
  unfold finishVerification
  apply WF.GadgetSpec.bind_rule_direct
    (left := left) (right := right) computeVerificationSum_wf_aux
  · intro lv rv h
    exact h
  · intro sumL sumR
    apply WF.GadgetSpec.direct_rule
      (left := (@PreparedVerification.r leftCtx left, sumL))
      (right := (@PreparedVerification.r rightCtx right, sumR))
      checkVerificationX_wf_aux
    intro lv rv h
    exact ⟨h.1.2.2.2, h.2⟩

theorem verifyDigest_wf_aux :
    WF.GadgetSpec VerifyInput.WFRel
      (fun input => verifyDigest input.1 input.2.1 input.2.2.1 input.2.2.2)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro leftCtx rightCtx left right
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

def VerifyDigestBits.WFRel {leftCtx rightCtx : Context}
    (lv : @WF.Valuation leftCtx) (rv : @WF.Valuation rightCtx)
    (left : Vector leftCtx.WBool verifyDigestInputBits)
    (right : Vector rightCtx.WBool verifyDigestInputBits) : Prop :=
  WF.VectorRel
    BoolWFRel
    lv rv left right

private theorem mapM_fromWord_wf_full :
    WF.GadgetSpec (WF.VectorRel Word.WFRel)
      (fun {ctx} (xs : Vector (@Word ctx n) m) => xs.mapM U.fromWord)
      (WF.VectorRel U.FullWFRel) := by
  intro leftCtx rightCtx left right
  apply WF.Rel.mono
    ((U.fromWord_wf_full.relHom leftCtx rightCtx).vectorMapM
      (fun lv rv => WF.VectorRel Word.WFRel lv rv left right)
      left right (fun _ _ h => h))
  intro lv rv outL outR h i
  have hi := h.2 i
  exact ⟨⟨hi.2.2, hi.1⟩, hi.2.1⟩

private theorem verifyDigestInputWords_wf
    {leftCtx rightCtx : Context}
    {lv : @WF.Valuation leftCtx} {rv : @WF.Valuation rightCtx}
    {left : Vector leftCtx.WBool verifyDigestInputBits}
    {right : Vector rightCtx.WBool verifyDigestInputBits}
    (h : VerifyDigestBits.WFRel lv rv left right) :
    WF.VectorRel Word.WFRel lv rv
      (@verifyDigestInputWords leftCtx left)
      (@verifyDigestInputWords rightCtx right) := by
  intro slot i
  simpa [verifyDigestInputWords, verifyDigestInputWord, BoolWFRel] using
    h ⟨slot.val * 256 + i.val, by
      simp [verifyDigestInputBits]
      omega⟩

theorem verifyDigestFromBits_wf_aux :
    WF.GadgetSpec VerifyDigestBits.WFRel verifyDigestFromBits
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro leftCtx rightCtx left right
  unfold verifyDigestFromBits
  apply WF.GadgetSpec.bind_rule_direct
    (left := @verifyDigestInputWords leftCtx left)
    (right := @verifyDigestInputWords rightCtx right) mapM_fromWord_wf_full
  · intro lv rv h
    exact verifyDigestInputWords_wf h
  · intro valuesL valuesR
    apply WF.GadgetSpec.direct_rule
      (left := (valuesL[0], @PublicKey.mk leftCtx valuesL[1] valuesL[2],
        @Signature.mk leftCtx valuesL[3] valuesL[4],
        @Aux.mk leftCtx valuesL[5] valuesL[6]))
      (right := (valuesR[0], @PublicKey.mk rightCtx valuesR[1] valuesR[2],
        @Signature.mk rightCtx valuesR[3] valuesR[4],
        @Aux.mk rightCtx valuesR[5] valuesR[6]))
      verifyDigest_wf_aux
    intro lv rv h
    exact ⟨h.2 0, h.2 1, h.2 2, h.2 3, h.2 4, h.2 5, h.2 6⟩

end Freigen.F2Z.Examples.EcdsaP256
