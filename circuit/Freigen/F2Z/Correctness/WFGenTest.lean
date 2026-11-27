import Freigen.F2Z.Correctness.WFGen

namespace Freigen.F2Z.WF

/-! These restate the two existing `wfgen` specifications rather than using
their proofs.  Keeping them outside `WFGen.lean` also lets that module's local
environment cache be initialized before the tactic is exercised. -/

theorem fromWord_wfgen_test :
    GadgetSpec
      (fun leftVal rightVal (left right : Word n) =>
        ∀ i : Fin n,
          LCEq leftVal.bool rightVal.bool left.bitsLE[i] right.bitsLE[i])
      U.fromWord
      (fun leftVal rightVal left right =>
        (∀ i : Fin n, LCEq leftVal.bool rightVal.bool
          left.bits.bitsLE[i] right.bits.bitsLE[i]) ∧
        LCEq leftVal.int rightVal.int left.intVal right.intVal) := by
  wfgen' [U.fromWord]
  · exact fun (leftVal rightVal : Valuation)
      (left right : Vector (LC ℤ) n) =>
      (∀ i : Fin n, LCEq leftVal.int rightVal.int left[i] right[i])
  all_goals wfgen'
  all_goals grind

example :
    GadgetSpec
      (fun leftVal rightVal (left right : LC ℤ) =>
        LCEq leftVal.int rightVal.int left right)
      (U.fromInt n)
      (fun leftVal rightVal left right =>
        LCEq leftVal.int rightVal.int left.intVal right.intVal ∧
        (∀ i : Fin n, LCEq leftVal.bool rightVal.bool
          left.bits.bitsLE[i] right.bits.bitsLE[i])) := by
  wfgen' using [fromWord_wfgen_test] unfold [U.fromInt]
  all_goals wfgen'
  all_goals grind

end Freigen.F2Z.WF
