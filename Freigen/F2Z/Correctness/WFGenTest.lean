import Freigen.F2Z.Correctness.WFGen

namespace Freigen.F2Z.WF

/-! These restate the two existing `wfgen` specifications rather than using
their proofs.  Keeping them outside `WFGen.lean` also lets that module's local
environment cache be initialized before the tactic is exercised. -/

theorem fromWord_wfgen_test :
    GadgetSpec
      (Input := fun ctx => @Word ctx n)
      (Output := fun ctx => @U ctx n)
      (fun {leftCtx rightCtx} leftVal rightVal
          (left : @Word leftCtx n) (right : @Word rightCtx n) =>
        ∀ i : Fin n,
          LCEq leftVal.bool rightVal.bool
            (@Word.bitsLE leftCtx n left)[i]
            (@Word.bitsLE rightCtx n right)[i])
      (fun {ctx} word => @U.fromWord ctx n word)
      (fun {leftCtx rightCtx} leftVal rightVal
          (left : @U leftCtx n) (right : @U rightCtx n) =>
        (∀ i : Fin n, LCEq leftVal.bool rightVal.bool
          (@Word.bitsLE leftCtx n (@U.bits leftCtx n left))[i]
          (@Word.bitsLE rightCtx n (@U.bits rightCtx n right))[i]) ∧
        LCEq leftVal.int rightVal.int
          (@U.intVal leftCtx n left) (@U.intVal rightCtx n right)) := by
  wfgen' [U.fromWord]
  · exact fun leftVal rightVal left right =>
      (∀ i : Fin n, LCEq leftVal.int rightVal.int left[i] right[i])
  all_goals wfgen'
  all_goals grind

example :
    GadgetSpec
      (Input := fun ctx => ctx.Wℤ)
      (Output := fun ctx => @U ctx n)
      (fun {leftCtx rightCtx} leftVal rightVal
          (left : leftCtx.Wℤ) (right : rightCtx.Wℤ) =>
        LCEq leftVal.int rightVal.int left right)
      (fun {ctx} value => @U.fromInt ctx n value)
      (fun {leftCtx rightCtx} leftVal rightVal
          (left : @U leftCtx n) (right : @U rightCtx n) =>
        LCEq leftVal.int rightVal.int
          (@U.intVal leftCtx n left) (@U.intVal rightCtx n right) ∧
        (∀ i : Fin n, LCEq leftVal.bool rightVal.bool
          (@Word.bitsLE leftCtx n (@U.bits leftCtx n left))[i]
          (@Word.bitsLE rightCtx n (@U.bits rightCtx n right))[i])) := by
  intro leftCtx rightCtx left right
  apply Rel.mono (U.fromInt_wf leftCtx rightCtx left right)
  exact fun _ _ _ _ h => ⟨h.2.2, h.1⟩

end Freigen.F2Z.WF
