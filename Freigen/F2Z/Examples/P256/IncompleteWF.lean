import Freigen.F2Z.Examples.P256.IncompleteImpl
import Freigen.F2Z.Examples.P256.WF

/-!
# Quotient well-formedness for checked incomplete affine addition

The discarded reciprocal and the ordinary chord formula depend only on
quotient-related affine representatives.  Exceptional-case assertions add no
outputs, so they do not change the output relation.
-/

namespace Freigen.F2Z.Examples.P256.AffineSlope

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem addIncompleteChecked_wf_aux :
    WF.GadgetSpec
      (fun lv rv (left right : Point × Point) =>
        left.1.WFRel lv rv right.1 ∧ left.2.WFRel lv rv right.2)
      (fun input => addIncompleteChecked input.1 input.2)
      Point.WFRel := by
  wfgen' using [Modular.Lazy.divide_wf, finishAddCandidate_wf_aux]
    unfold [addIncompleteChecked, Point.WFRel,
      sub, ofElem, Modular.Lazy.sub, Modular.Lazy.ofElem,
      Modular.Lazy.Rep.WFRel]
  case vc1 =>
    rename_i hrel hB
    have hh := hrel leftVal rightVal hB
    unfold SlopeOperands.WFRel
    simp_all [Modular.Lazy.Rep.WFRel, WF.LCEq, LC.eval_add,
      LC.eval_sub, LC.eval_ofConst]
  all_goals simp_all [Modular.Lazy.Rep.WFRel,
    WF.LCEq, LC.eval_add, LC.eval_sub, LC.eval_ofConst,
    one, fpConst, Modular.ofNat, U.intVal]

end Freigen.F2Z.Examples.P256.AffineSlope
