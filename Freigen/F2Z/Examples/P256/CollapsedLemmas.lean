import Freigen.F2Z.Examples.P256.Lemmas

/-!
# Completeness lemmas for open-once P-256 addition

This module isolates the heavier completeness proof for the collapsed
complete-add selectors. Keeping it out of the foundational P-256 lemma module
lets cost-optimization iterations reuse the cached base proofs.
-/

namespace Freigen.F2Z.Examples.P256.AffineSlope.Aux

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open Std.Do
open scoped Std.Do
open Modular

def CollapsedNumeratorSpec (ρ : WF.Valuation) (P Q : AffineSlope.Point)
    (control : AffineSlope.AddControl) (out : AffineSlope.Rep) : Prop :=
  (control.doubleCase.eval ρ.int = 1 →
    Modular.Lazy.evalZMod base out ρ =
      3 * (Modular.Lazy.evalZMod base P.X ρ *
        Modular.Lazy.evalZMod base P.X ρ) - 3) ∧
  ((control.active - control.doubleCase).eval ρ.int = 1 →
    Modular.Lazy.evalZMod base out ρ =
      Modular.Lazy.evalZMod base Q.Y ρ -
        Modular.Lazy.evalZMod base P.Y ρ) ∧
  ((LC.ofConst 1 - control.active).eval ρ.int = 1 →
    Modular.Lazy.evalZMod base out ρ = 0)

def CollapsedDenominatorSpec (ρ : WF.Valuation) (P Q : AffineSlope.Point)
    (control : AffineSlope.AddControl) (out : AffineSlope.Rep) : Prop :=
  (control.doubleCase.eval ρ.int = 1 →
    Modular.Lazy.evalZMod base out ρ =
      2 * Modular.Lazy.evalZMod base P.Y ρ) ∧
  ((control.active - control.doubleCase).eval ρ.int = 1 →
    Modular.Lazy.evalZMod base out ρ =
      Modular.Lazy.evalZMod base Q.X ρ -
        Modular.Lazy.evalZMod base P.X ρ) ∧
  ((LC.ofConst 1 - control.active).eval ρ.int = 1 →
    Modular.Lazy.evalZMod base out ρ = 1)

def CollapsedSlopeOperandsValid (ρ : WF.Valuation)
    (operands : AffineSlope.SlopeOperands) : Prop :=
  operands.numerator.Valid ρ ∧ operands.numerator.bound = 5 ∧
    operands.denominator.Valid ρ ∧ operands.denominator.bound = 3

@[spec 2000] theorem selectGated3Numerator_complete
    {description : String} {gate1 gate2 gate3 : LC ℤ}
    {value1 value2 value3 : AffineSlope.Rep}
    (hcases : Gated3Cases ρ gate1 gate2 gate3)
    (hvalue1 : value1.Valid ρ)
    (hvalue1Fit : value1.intVal.eval ρ.int < 5 * base.modulus)
    (hvalue2 : value2.Valid ρ)
    (hvalue2Fit : value2.intVal.eval ρ.int < 5 * base.modulus)
    (hvalue3 : value3.Valid ρ)
    (hvalue3Fit : value3.intVal.eval ρ.int < 5 * base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectGated3Rep 259 5 description
        gate1 gate2 gate3 value1 value2 value3)
    ⦃⇓ out => ⌜Gated3Spec ρ gate1 gate2 gate3 value1 value2 value3 out ∧
      out.Valid ρ ∧ out.intVal.eval ρ.int < 5 * base.modulus ∧
      out.bound = 5⌝⦄ := by
  exact selectGated3Rep_complete hcases hvalue1 hvalue1Fit hvalue2
    hvalue2Fit hvalue3 hvalue3Fit (by
      set_option exponentiation.threshold 300 in
        norm_num [base, baseModulus]) le_rfl

@[spec 2000] theorem selectGated3Denominator_complete
    {description : String} {gate1 gate2 gate3 : LC ℤ}
    {value1 value2 value3 : AffineSlope.Rep}
    (hcases : Gated3Cases ρ gate1 gate2 gate3)
    (hvalue1 : value1.Valid ρ)
    (hvalue1Fit : value1.intVal.eval ρ.int < 3 * base.modulus)
    (hvalue2 : value2.Valid ρ)
    (hvalue2Fit : value2.intVal.eval ρ.int < 3 * base.modulus)
    (hvalue3 : value3.Valid ρ)
    (hvalue3Fit : value3.intVal.eval ρ.int < 3 * base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectGated3Rep 258 3 description
        gate1 gate2 gate3 value1 value2 value3)
    ⦃⇓ out => ⌜Gated3Spec ρ gate1 gate2 gate3 value1 value2 value3 out ∧
      out.Valid ρ ∧ out.intVal.eval ρ.int < 3 * base.modulus ∧
      out.bound = 3⌝⦄ := by
  exact selectGated3Rep_complete hcases hvalue1 hvalue1Fit hvalue2
    hvalue2Fit hvalue3 hvalue3Fit (by
      set_option exponentiation.threshold 300 in
        norm_num [base, baseModulus]) le_rfl

@[spec 2000] theorem selectGated3Formula_complete
    {description : String} {gate1 gate2 gate3 : LC ℤ}
    {value1 value2 value3 : AffineSlope.Rep}
    (hcases : Gated3Cases ρ gate1 gate2 gate3)
    (hvalue1 : value1.Valid ρ)
    (hvalue1Fit : value1.intVal.eval ρ.int < (2 ^ 262 : Nat))
    (hvalue2 : value2.Valid ρ)
    (hvalue2Fit : value2.intVal.eval ρ.int < (2 ^ 262 : Nat))
    (hvalue3 : value3.Valid ρ)
    (hvalue3Fit : value3.intVal.eval ρ.int < (2 ^ 262 : Nat)) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectGated3Rep 262 66 description
        gate1 gate2 gate3 value1 value2 value3)
    ⦃⇓ out => ⌜Gated3Spec ρ gate1 gate2 gate3 value1 value2 value3 out ∧
      out.Valid ρ ∧ out.intVal.eval ρ.int < (2 ^ 262 : Nat) ∧
      out.bound = 66⌝⦄ := by
  exact selectGated3Rep_complete hcases hvalue1 hvalue1Fit hvalue2
    hvalue2Fit hvalue3 hvalue3Fit le_rfl (by
      set_option exponentiation.threshold 300 in
        norm_num [base, baseModulus])

@[spec] theorem selectSlopeOperandsCollapsedTight_complete
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {p : Reference.Point}
    (hPvalid : P.Valid ρ) (hQvalid : Q.Valid ρ)
    (hcontrol : AddControlSpec ρ P Q control)
    (hP : Reference.Represents ρ P p)
    (hnoTwoTorsion : p = 0 ∨ p + p ≠ 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectSlopeOperandsCollapsedTight P Q control)
    ⦃⇓ operands => ⌜CollapsedSlopeOperandsValid ρ operands ∧
      SlopeOperandsSpec ρ P Q control operands ∧
      Modular.Lazy.evalZMod base operands.denominator ρ ≠ 0⌝⦄ := by
  rcases hPvalid with
    ⟨hPXbound, hPX, hPXcanonical, hPYbound, hPY, hPYcanonical, hPinf⟩
  rcases hQvalid with
    ⟨hQXbound, hQX, hQXcanonical, hQYbound, hQY, hQYcanonical, hQinf⟩
  have hPvalid' : P.Valid ρ :=
    ⟨hPXbound, hPX, hPXcanonical, hPYbound, hPY, hPYcanonical, hPinf⟩
  have hthree : (AffineSlope.ofElem three).Valid ρ :=
    Modular.Lazy.ofElem_valid base
      (Modular.ofNat_valid base 3 (by decide) (by decide))
  have hzero : (AffineSlope.ofElem zero).Valid ρ :=
    Modular.Lazy.ofElem_valid base
      (Modular.ofNat_valid base 0 (by decide) (by decide))
  have hone : (AffineSlope.ofElem one).Valid ρ :=
    Modular.Lazy.ofElem_valid base
      (Modular.ofNat_valid base 1 (by decide) (by decide))
  have hthreeCanonical : three.Valid ρ :=
    Modular.ofNat_valid base 3 (by decide) (by decide)
  have hthreeNat : three.evalNat ρ = 3 :=
    Modular.ofNat_evalNat base 3 (by decide) (by decide)
  have hthreeEval : three.val.intVal.eval ρ.int = 3 := by
    unfold Modular.Elem.evalNat at hthreeNat
    have h0 := U.intVal_nonneg three.val hthreeCanonical.1
    omega
  have doubleNumeratorFit {x2 : AffineSlope.Rep}
      (hx2Canonical : x2.intVal.eval ρ.int < base.modulus) :
      (AffineSlope.sub (AffineSlope.scale 3 x2)
        (AffineSlope.ofElem three)).intVal.eval ρ.int < 5 * base.modulus := by
    simp only [AffineSlope.sub, AffineSlope.scale, AffineSlope.ofElem,
      Modular.Lazy.sub, Modular.Lazy.scale, Modular.Lazy.ofElem,
      LC.eval_sub, LC.eval_add, LC.eval_nsmul, LC.eval_ofConst,
      nsmul_eq_mul]
    rw [hthreeEval]
    omega
  have genericNumeratorFit :
      (AffineSlope.sub Q.Y P.Y).intVal.eval ρ.int < 5 * base.modulus := by
    have hPY0 := hPY.1
    unfold AffineSlope.sub Modular.Lazy.sub
    simp only [LC.eval_sub, LC.eval_add, LC.eval_ofConst]
    rw [hPYbound]
    omega
  have zeroFit : (AffineSlope.ofElem zero).intVal.eval ρ.int <
      5 * base.modulus := by
    have hz := hzero.2
    simp only [AffineSlope.ofElem, Modular.Lazy.ofElem] at hz ⊢
    omega
  have doubleDenominatorFit :
      (AffineSlope.scale 2 P.Y).intVal.eval ρ.int < 3 * base.modulus := by
    unfold AffineSlope.scale Modular.Lazy.scale
    simp only [LC.eval_nsmul, nsmul_eq_mul]
    omega
  have genericDenominatorFit :
      (AffineSlope.sub Q.X P.X).intVal.eval ρ.int < 3 * base.modulus := by
    have hPX0 := hPX.1
    unfold AffineSlope.sub Modular.Lazy.sub
    simp only [LC.eval_sub, LC.eval_add, LC.eval_ofConst]
    rw [hPXbound]
    omega
  have oneFit : (AffineSlope.ofElem one).intVal.eval ρ.int <
      3 * base.modulus := by
    have ho := hone.2
    simp only [AffineSlope.ofElem, Modular.Lazy.ofElem] at ho ⊢
    omega
  have hcases := hcontrol.slope_gated_cases
  unfold AffineSlope.selectSlopeOperandsCollapsedTight
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun x2 => ⌜
    Modular.Lazy.MulZModSpec base ρ P.X P.X x2 ∧
      x2.Valid ρ ∧ x2.bound = 2 ∧
      x2.intVal.eval ρ.int < base.modulus⌝)
  case hx =>
    simpa [and_assoc, and_left_comm, and_comm] using
      (doubleSquare_complete (ρ := ρ) hPvalid')
  case hf =>
    intro x2
    unfold AffineSlope.finishSelectSlopeOperandsCollapsedTight
      AffineSlope.selectCollapsedNumeratorTight
    rw [Complete.interp_bind]
    apply Triple.bind (Q := fun numerator => ⌜
      CollapsedNumeratorSpec ρ P Q control numerator ∧
        numerator.Valid ρ ∧
        numerator.intVal.eval ρ.int < 5 * base.modulus ∧
        numerator.bound = 5⌝)
    case hx =>
      mvcgen -trivial
      case vc1.success =>
        rename_i hmul numerator
        intros hsel hvalid hfit hbound
        refine ⟨?_, hvalid, hfit, hbound⟩
        unfold CollapsedNumeratorSpec
        exact ⟨fun hdouble => (hsel.1 hdouble).trans (by
            simp [Modular.Lazy.MulZModSpec] at hmul
            simp [hmul.1, AffineSlope.sub, AffineSlope.scale,
              AffineSlope.ofElem]),
          fun hgeneric => (hsel.2.1 hgeneric).trans (by
            simp [AffineSlope.sub]),
          fun hinactive => (hsel.2.2 hinactive).trans (by
            simp [AffineSlope.ofElem])⟩
      case vc2 => intros; exact hcases
      case vc3 =>
        intros _ hx2 _ _
        exact Modular.Lazy.sub_valid base
          (Modular.Lazy.scale_valid base hx2 (by omega)) hthree
      case vc4 =>
        intros _ _ _ hx2Canonical
        exact doubleNumeratorFit hx2Canonical
      case vc5 => intros; exact Modular.Lazy.sub_valid base hQY hPY
      case vc6 => intros; exact genericNumeratorFit
      case vc7 => intros; exact hzero
      case vc8 => intros; exact zeroFit
    case hf =>
      intro numerator
      unfold AffineSlope.selectCollapsedDenominatorTight
      rw [Complete.interp_bind]
      apply Triple.bind (Q := fun denominator => ⌜
        (CollapsedNumeratorSpec ρ P Q control numerator ∧
          numerator.Valid ρ ∧
          numerator.intVal.eval ρ.int < 5 * base.modulus ∧
          numerator.bound = 5) ∧
        (CollapsedDenominatorSpec ρ P Q control denominator ∧
          denominator.Valid ρ ∧
          denominator.intVal.eval ρ.int < 3 * base.modulus ∧
          denominator.bound = 3)⌝)
      case hx =>
        mvcgen -trivial
        case vc1.success =>
          rename_i hnum denominator
          intros hsel hvalid hfit hbound
          refine ⟨hnum, ?_, hvalid, hfit, hbound⟩
          unfold CollapsedDenominatorSpec
          exact ⟨fun hdouble => (hsel.1 hdouble).trans (by
              simp [AffineSlope.scale]),
            fun hgeneric => (hsel.2.1 hgeneric).trans (by
              simp [AffineSlope.sub]),
            fun hinactive => (hsel.2.2 hinactive).trans (by
              simp [AffineSlope.ofElem])⟩
        case vc2 => intros; exact hcases
        case vc3 =>
          intros
          exact Modular.Lazy.scale_valid base hPY (by omega)
        case vc4 => intros; exact doubleDenominatorFit
        case vc5 => intros; exact Modular.Lazy.sub_valid base hQX hPX
        case vc6 => intros; exact genericDenominatorFit
        case vc7 => intros; exact hone
        case vc8 => intros; exact oneFit
      case hf =>
        intro denominator
        rw [Complete.interp_pure]
        mvcgen -trivial
        have h :
            (CollapsedNumeratorSpec ρ P Q control numerator ∧
              numerator.Valid ρ ∧
              numerator.intVal.eval ρ.int < 5 * base.modulus ∧
              numerator.bound = 5) ∧
            (CollapsedDenominatorSpec ρ P Q control denominator ∧
              denominator.Valid ρ ∧
              denominator.intVal.eval ρ.int < 3 * base.modulus ∧
              denominator.bound = 3) := by assumption
        rcases h with ⟨hnum, hden⟩
        have hspec : SlopeOperandsSpec ρ P Q control
            ⟨numerator, denominator⟩ := by
          unfold SlopeOperandsSpec
          constructor
          · intro hactive
            constructor
            · intro hdouble
              exact ⟨hnum.1.1 hdouble, hden.1.1 hdouble⟩
            · intro hdouble
              have hg :
                  (control.active - control.doubleCase).eval ρ.int = 1 := by
                simp [hactive, hdouble]
              exact ⟨hnum.1.2.1 hg, hden.1.2.1 hg⟩
          · intro hactive
            have hi : (LC.ofConst 1 - control.active).eval ρ.int = 1 := by
              simp [hactive]
            exact ⟨hnum.1.2.2 hi, hden.1.2.2 hi⟩
        exact ⟨⟨hnum.2.1, hnum.2.2.2, hden.2.1, hden.2.2.2⟩,
          hspec, SlopeOperandsSpec.denominator_ne_zero hcontrol hspec hP
            hnoTwoTorsion⟩

@[spec] theorem selectSlopeOperandsCollapsed_complete
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {p : Reference.Point}
    (hPvalid : P.Valid ρ) (hQvalid : Q.Valid ρ)
    (hcontrol : AddControlSpec ρ P Q control)
    (hP : Reference.Represents ρ P p)
    (hnoTwoTorsion : p = 0 ∨ p + p ≠ 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectSlopeOperandsCollapsed P Q control)
    ⦃⇓ operands => ⌜operands.Valid ρ ∧
      SlopeOperandsSpec ρ P Q control operands ∧
      Modular.Lazy.evalZMod base operands.denominator ρ ≠ 0⌝⦄ := by
  rcases hPvalid with ⟨hPXbound, hPX, _, hPYbound, hPY, _, _⟩
  rcases hQvalid with ⟨hQXbound, hQX, _, hQYbound, hQY, _, _⟩
  have hthree : (AffineSlope.ofElem three).Valid ρ :=
    Modular.Lazy.ofElem_valid base
      (Modular.ofNat_valid base 3 (by decide) (by decide))
  have hzero : (AffineSlope.ofElem zero).Valid ρ :=
    Modular.Lazy.ofElem_valid base
      (Modular.ofNat_valid base 0 (by decide) (by decide))
  have hone : (AffineSlope.ofElem one).Valid ρ :=
    Modular.Lazy.ofElem_valid base
      (Modular.ofNat_valid base 1 (by decide) (by decide))
  have fit8 {x : AffineSlope.Rep} (hx : x.Valid ρ)
      (hbound : x.bound ≤ 8) :
      x.intVal.eval ρ.int < (2 ^ 262 : Nat) := by
    calc
      x.intVal.eval ρ.int < x.bound * base.modulus := hx.2
      _ ≤ 8 * base.modulus := by
        exact_mod_cast Nat.mul_le_mul_right base.modulus hbound
      _ < (2 ^ 262 : Nat) := by
        set_option exponentiation.threshold 300 in
          norm_num [base, baseModulus]
  have hx2Bound : P.X.bound * P.X.bound <
      2 ^ Modular.Lazy.quotientExtraBits := by
    simp [hPXbound, Modular.Lazy.quotientExtraBits]
  have hcases := hcontrol.slope_gated_cases
  unfold AffineSlope.selectSlopeOperandsCollapsed
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun x2 => ⌜
    Modular.Lazy.MulZModSpec base ρ P.X P.X x2 ∧
      x2.Valid ρ ∧ x2.bound = 2⌝)
  case hx => exact Modular.Lazy.mul_complete_zmod base hPX hPX hx2Bound
  case hf =>
    intro x2
    unfold AffineSlope.finishSelectSlopeOperandsCollapsed
      AffineSlope.selectCollapsedNumerator
    rw [Complete.interp_bind]
    apply Triple.bind (Q := fun numerator => ⌜
      CollapsedNumeratorSpec ρ P Q control numerator ∧
        numerator.Valid ρ ∧
        numerator.intVal.eval ρ.int < (2 ^ 262 : Nat) ∧
        numerator.bound = 66⌝)
    case hx =>
      mvcgen -trivial
      case vc1.success =>
        rename_i hmul numerator
        intros hsel hvalid hfit hbound
        refine ⟨?_, hvalid, hfit, hbound⟩
        unfold CollapsedNumeratorSpec
        exact ⟨fun hdouble => (hsel.1 hdouble).trans (by
            simp [Modular.Lazy.MulZModSpec] at hmul
            simp [hmul.1, AffineSlope.sub, AffineSlope.scale,
              AffineSlope.ofElem]),
          fun hgeneric => (hsel.2.1 hgeneric).trans (by
            simp [AffineSlope.sub]),
          fun hinactive => (hsel.2.2 hinactive).trans (by
            simp [AffineSlope.ofElem])⟩
      all_goals intros
      all_goals first
        | exact hcases
        | exact Modular.Lazy.sub_valid base hQY hPY
        | exact Modular.Lazy.scale_valid base hPY (by omega)
        | exact Modular.Lazy.sub_valid base
            (Modular.Lazy.scale_valid base (by assumption) (by omega)) hthree
        | exact hzero
        | exact fit8 (Modular.Lazy.sub_valid base
            (Modular.Lazy.scale_valid base (by assumption) (by omega)) hthree)
            (by
              change 3 * x2.bound + 2 ≤ 8
              omega)
        | exact fit8 (Modular.Lazy.sub_valid base hQY hPY)
            (by
              change Q.Y.bound + P.Y.bound ≤ 8
              omega)
        | exact fit8 hzero (by
            simp [AffineSlope.ofElem, Modular.Lazy.ofElem])
    case hf =>
      intro numerator
      unfold AffineSlope.selectCollapsedDenominator
      rw [Complete.interp_bind]
      apply Triple.bind (Q := fun denominator => ⌜
        (CollapsedNumeratorSpec ρ P Q control numerator ∧
          numerator.Valid ρ ∧
          numerator.intVal.eval ρ.int < (2 ^ 262 : Nat) ∧
          numerator.bound = 66) ∧
        (CollapsedDenominatorSpec ρ P Q control denominator ∧
          denominator.Valid ρ ∧
          denominator.intVal.eval ρ.int < (2 ^ 262 : Nat) ∧
          denominator.bound = 66)⌝)
      case hx =>
        mvcgen -trivial
        case vc1.success =>
          rename_i hnum denominator
          intros hsel hvalid hfit hbound
          refine ⟨hnum, ?_, hvalid, hfit, hbound⟩
          unfold CollapsedDenominatorSpec
          exact ⟨fun hdouble => (hsel.1 hdouble).trans (by
              simp [AffineSlope.scale]),
            fun hgeneric => (hsel.2.1 hgeneric).trans (by
              simp [AffineSlope.sub]),
            fun hinactive => (hsel.2.2 hinactive).trans (by
              simp [AffineSlope.ofElem])⟩
        all_goals intros
        all_goals first
          | exact hcases
          | exact Modular.Lazy.sub_valid base hQX hPX
          | exact Modular.Lazy.scale_valid base hPY (by omega)
          | exact hone
          | exact fit8 (Modular.Lazy.scale_valid base hPY (by omega)) (by
              change 2 * P.Y.bound ≤ 8
              omega)
          | exact fit8 (Modular.Lazy.sub_valid base hQX hPX) (by
              change Q.X.bound + P.X.bound ≤ 8
              omega)
          | exact fit8 hone (by
              simp [AffineSlope.ofElem, Modular.Lazy.ofElem])
      case hf =>
        intro denominator
        rw [Complete.interp_pure]
        mvcgen -trivial
        have h :
            (CollapsedNumeratorSpec ρ P Q control numerator ∧
              numerator.Valid ρ ∧
              numerator.intVal.eval ρ.int < (2 ^ 262 : Nat) ∧
              numerator.bound = 66) ∧
            (CollapsedDenominatorSpec ρ P Q control denominator ∧
              denominator.Valid ρ ∧
              denominator.intVal.eval ρ.int < (2 ^ 262 : Nat) ∧
              denominator.bound = 66) := by assumption
        rcases h with ⟨hnum, hden⟩
        have hspec : SlopeOperandsSpec ρ P Q control
            ⟨numerator, denominator⟩ := by
          unfold SlopeOperandsSpec
          constructor
          · intro hactive
            constructor
            · intro hdouble
              exact ⟨hnum.1.1 hdouble, hden.1.1 hdouble⟩
            · intro hdouble
              have hg :
                  (control.active - control.doubleCase).eval ρ.int = 1 := by
                simp [hactive, hdouble]
              exact ⟨hnum.1.2.1 hg, hden.1.2.1 hg⟩
          · intro hactive
            have hi : (LC.ofConst 1 - control.active).eval ρ.int = 1 := by
              simp [hactive]
            exact ⟨hnum.1.2.2 hi, hden.1.2.2 hi⟩
        exact ⟨⟨hnum.2.1, hnum.2.2.2, hden.2.1, hden.2.2.2⟩,
          hspec, SlopeOperandsSpec.denominator_ne_zero hcontrol hspec hP
            hnoTwoTorsion⟩

@[spec] theorem finishAddCandidateCollapsed_sound
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {operands : AffineSlope.SlopeOperands}
    (hoperands : SlopeOperandsSpec ρ P Q control operands)
    (hdoubleBit : control.doubleCase.eval ρ.int = 0 ∨
      control.doubleCase.eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (AffineSlope.finishAddCandidateCollapsed P Q operands)
    ⦃⇓ candidate => ⌜AddCandidateSpec ρ P Q control candidate⌝⦄ := by
  mvcgen [AffineSlope.finishAddCandidateCollapsed]
  rename_i slope hslope candidateX hcandidateX candidateY hcandidateY
  unfold AddCandidateSpec
  intro hactive
  rcases hoperands.1 hactive with ⟨hdouble, hgeneric⟩
  by_cases hd : control.doubleCase.eval ρ.int = 1
  · rcases hdouble hd with ⟨hnum, hden⟩
    refine ⟨slope, ?_⟩
    simp_all [Modular.Lazy.DivideZModSpec,
      Modular.Lazy.MulSubToElemZModSpec,
      AffineSlope.collapsedCandidateXTarget,
      AffineSlope.collapsedCandidateYFactor,
      AffineSlope.add, AffineSlope.sub, AffineSlope.ofElem]
  · have hd0 : control.doubleCase.eval ρ.int = 0 := by
      rcases hdoubleBit with h | h
      · exact h
      · contradiction
    rcases hgeneric hd0 with ⟨hnum, hden⟩
    refine ⟨slope, ?_⟩
    simp_all [Modular.Lazy.DivideZModSpec,
      Modular.Lazy.MulSubToElemZModSpec,
      AffineSlope.collapsedCandidateXTarget,
      AffineSlope.collapsedCandidateYFactor,
      AffineSlope.add, AffineSlope.sub, AffineSlope.ofElem]

@[spec] theorem finishAddCandidateCollapsed_complete
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {operands : AffineSlope.SlopeOperands}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ)
    (hoperands : CollapsedSlopeOperandsValid ρ operands)
    (hoperandsSpec : SlopeOperandsSpec ρ P Q control operands)
    (hden : Modular.Lazy.evalZMod base operands.denominator ρ ≠ 0)
    (hdoubleBit : control.doubleCase.eval ρ.int = 0 ∨
      control.doubleCase.eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.finishAddCandidateCollapsed P Q operands)
    ⦃⇓ candidate => ⌜candidate.1.Valid ρ ∧
      candidate.1.bound = 2 ∧
      candidate.1.intVal.eval ρ.int < base.modulus ∧
      candidate.2.Valid ρ ∧ candidate.2.bound = 2 ∧
      candidate.2.intVal.eval ρ.int < base.modulus ∧
      AddCandidateSpec ρ P Q control candidate⌝⦄ := by
  rcases hoperands with ⟨hnum, hnumBound, hdenValid, hdenBound⟩
  mvcgen [AffineSlope.finishAddCandidateCollapsed]
  all_goals first
    | exact hP
    | exact hQ
    | exact hnum
    | exact hnumBound
    | exact hdenValid
    | exact hdenBound
    | exact hden
    | assumption
    | skip
  case vc8.hslope =>
    rename_i slope hslope
    exact hslope.1
  case vc9.hslopeBound =>
    rename_i slope hslope
    exact hslope.2.1
  case vc10.hslopeCanonical =>
    rename_i slope hslope
    exact hslope.2.2.1
  case vc12.hslope =>
    rename_i slope hslope candidateX hcandidateX
    exact hslope.1
  case vc13.hslopeBound =>
    rename_i slope hslope candidateX hcandidateX
    exact hslope.2.1
  case vc14.hslopeCanonical =>
    rename_i slope hslope candidateX hcandidateX
    exact hslope.2.2.1
  case vc15.hx3 =>
    rename_i slope hslope candidateX hcandidateX
    exact hcandidateX.1
  case vc16.success.success.success =>
    rename_i slope hslope candidateX hcandidateX candidateY hcandidateY
    refine ⟨Modular.Lazy.ofElem_valid base hcandidateX.1, rfl,
      hcandidateX.1.2, Modular.Lazy.ofElem_valid base hcandidateY.1,
      rfl, hcandidateY.1.2, ?_⟩
    unfold AddCandidateSpec
    unfold Modular.Lazy.DivideZModSpec at hslope
    unfold Modular.Lazy.MulSubToElemZModSpec at hcandidateX hcandidateY
    intro hactive
    rcases hoperandsSpec.1 hactive with ⟨hdouble, hgeneric⟩
    have hcandidateXEq := hcandidateX.2
    have hcandidateYEq := hcandidateY.2
    simp only [AffineSlope.collapsedCandidateXTarget, AffineSlope.add,
      Modular.Lazy.evalZMod_add] at hcandidateXEq
    simp only [AffineSlope.collapsedCandidateYFactor, AffineSlope.sub,
      AffineSlope.ofElem, Modular.Lazy.evalZMod_sub,
      Modular.Lazy.evalZMod_ofElem] at hcandidateYEq
    rcases hdoubleBit with hd0 | hd1
    · rcases hgeneric hd0 with ⟨hnumEq, hdenEq⟩
      have hslopeEq := hslope.2.2.2
      rw [hdenEq, hnumEq] at hslopeEq
      exact ⟨slope, by simpa [hd0] using hslopeEq,
        hcandidateXEq, hcandidateYEq⟩
    · rcases hdouble hd1 with ⟨hnumEq, hdenEq⟩
      have hslopeEq := hslope.2.2.2
      rw [hdenEq, hnumEq] at hslopeEq
      exact ⟨slope, by simpa [hd1] using hslopeEq,
        hcandidateXEq, hcandidateYEq⟩

@[spec] theorem selectSlopeOperandsCollapsedTight_sound
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    (hcontrol : AddControlSpec ρ P Q control) :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (AffineSlope.selectSlopeOperandsCollapsedTight P Q control)
    ⦃⇓ operands => ⌜SlopeOperandsSpec ρ P Q control operands⌝⦄ := by
  mvcgen [AffineSlope.selectSlopeOperandsCollapsedTight,
    AffineSlope.finishSelectSlopeOperandsCollapsedTight,
    AffineSlope.selectCollapsedNumeratorTight,
    AffineSlope.selectCollapsedDenominatorTight]
  rename_i x2 hx2 numerator hnumerator denominator hdenominator
  unfold SlopeOperandsSpec
  constructor
  · intro hactive
    constructor
    · intro hdouble
      constructor
      · calc
          Modular.Lazy.evalZMod base numerator ρ =
              Modular.Lazy.evalZMod base
                (AffineSlope.sub (AffineSlope.scale 3 x2)
                  (AffineSlope.ofElem three)) ρ := hnumerator.1 hdouble
          _ = _ := by
            simp [Modular.Lazy.MulZModSpec] at hx2
            simp [hx2, AffineSlope.sub, AffineSlope.scale,
              AffineSlope.ofElem]
      · calc
          Modular.Lazy.evalZMod base denominator ρ =
              Modular.Lazy.evalZMod base (AffineSlope.scale 2 P.Y) ρ :=
            hdenominator.1 hdouble
          _ = _ := by simp [AffineSlope.scale]
    · intro hdouble
      have hgeneric :
          (control.active - control.doubleCase).eval ρ.int = 1 := by
        simp [hactive, hdouble]
      constructor
      · calc
          Modular.Lazy.evalZMod base numerator ρ =
              Modular.Lazy.evalZMod base (AffineSlope.sub Q.Y P.Y) ρ :=
            hnumerator.2.1 hgeneric
          _ = _ := by simp [AffineSlope.sub]
      · calc
          Modular.Lazy.evalZMod base denominator ρ =
              Modular.Lazy.evalZMod base (AffineSlope.sub Q.X P.X) ρ :=
            hdenominator.2.1 hgeneric
          _ = _ := by simp [AffineSlope.sub]
  · intro hactive
    have hinactive : (LC.ofConst 1 - control.active).eval ρ.int = 1 := by
      simp [hactive]
    exact ⟨by simpa [AffineSlope.ofElem] using hnumerator.2.2 hinactive,
      by simpa [AffineSlope.ofElem] using hdenominator.2.2 hinactive⟩

@[spec] theorem addCandidateCollapsed_sound
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    (hcontrol : AddControlSpec ρ P Q control) :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (AffineSlope.addCandidateCollapsed P Q control)
    ⦃⇓ candidate => ⌜AddCandidateSpec ρ P Q control candidate⌝⦄ := by
  have hdoubleBit : control.doubleCase.eval ρ.int = 0 ∨
      control.doubleCase.eval ρ.int = 1 := by
    rcases hcontrol with ⟨_, _, _, _, _, _, hdoubleCase, _, _⟩
    exact hdoubleCase.2
  mvcgen [AffineSlope.addCandidateCollapsed]
  all_goals intros <;> assumption

@[spec] theorem addCandidateCollapsed_complete
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {p : Reference.Point}
    (hPvalid : P.Valid ρ) (hQvalid : Q.Valid ρ)
    (hcontrol : AddControlSpec ρ P Q control)
    (hP : Reference.Represents ρ P p)
    (hnoTwoTorsion : p = 0 ∨ p + p ≠ 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.addCandidateCollapsed P Q control)
    ⦃⇓ candidate => ⌜candidate.1.Valid ρ ∧
      candidate.1.bound = 2 ∧
      candidate.1.intVal.eval ρ.int < base.modulus ∧
      candidate.2.Valid ρ ∧ candidate.2.bound = 2 ∧
      candidate.2.intVal.eval ρ.int < base.modulus ∧
      AddCandidateSpec ρ P Q control candidate⌝⦄ := by
  have hdoubleBit : control.doubleCase.eval ρ.int = 0 ∨
      control.doubleCase.eval ρ.int = 1 := by
    rcases hcontrol with ⟨_, _, _, _, _, _, hdoubleCase, _, _⟩
    exact hdoubleCase.2
  mvcgen [AffineSlope.addCandidateCollapsed]
  all_goals intros
  all_goals assumption

def CollapsedSelectAddOutputSpec (ρ : WF.Valuation)
    (P Q : AffineSlope.Point) (control : AffineSlope.AddControl)
    (candidate : AffineSlope.Rep × AffineSlope.Rep)
    (out : AffineSlope.Point) : Prop :=
  ∃ bothInfinity oppositePair finiteOpposite : LC ℤ,
    AffineSlope.AndBitSpec ρ P.infinity Q.infinity bothInfinity ∧
    AffineSlope.AndBitSpec ρ control.sameX control.oppositeY
      oppositePair ∧
    AffineSlope.AndBitSpec ρ control.finite oppositePair
      finiteOpposite ∧
    Gated4Spec ρ control.active P.infinity
      (Q.infinity - bothInfinity) (control.finite - control.active)
      candidate.1 Q.X P.X (AffineSlope.ofElem zero) out.X ∧
    Gated4Spec ρ control.active P.infinity
      (Q.infinity - bothInfinity) (control.finite - control.active)
      candidate.2 Q.Y P.Y (AffineSlope.ofElem zero) out.Y ∧
    out.infinity.eval ρ.int =
      bothInfinity.eval ρ.int + finiteOpposite.eval ρ.int

@[spec] theorem selectAddOutputCollapsed_sound
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {candidate : AffineSlope.Rep × AffineSlope.Rep} :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (AffineSlope.selectAddOutputCollapsed P Q control candidate)
    ⦃⇓ out => ⌜CollapsedSelectAddOutputSpec ρ P Q control candidate out⌝⦄ := by
  mvcgen [AffineSlope.selectAddOutputCollapsed,
    AffineSlope.selectAddCoordinateCollapsed,
    CollapsedSelectAddOutputSpec]
  rename_i bothInfinity hbothInfinity X hX Y hY
    finiteOpposite hfiniteOpposite
  rcases hfiniteOpposite with
    ⟨oppositePair, hoppositePair, hfiniteOpposite⟩
  exact ⟨bothInfinity, oppositePair, finiteOpposite,
    hbothInfinity, hoppositePair, hfiniteOpposite, hX, hY, by simp⟩

theorem CollapsedSelectAddOutputSpec.toSelectAddOutputSpec
    {P Q out : AffineSlope.Point} {control : AffineSlope.AddControl}
    {candidate : AffineSlope.Rep × AffineSlope.Rep}
    (hPinf : P.infinity.eval ρ.int = 0 ∨
      P.infinity.eval ρ.int = 1)
    (hQinf : Q.infinity.eval ρ.int = 0 ∨
      Q.infinity.eval ρ.int = 1)
    (hcontrol : AddControlSpec ρ P Q control)
    (hout : CollapsedSelectAddOutputSpec ρ P Q control candidate out) :
    SelectAddOutputSpec ρ P Q control candidate out := by
  have hactive := hcontrol.active_bit
  rcases hout with ⟨bothInfinity, oppositePair, finiteOpposite,
    hbothInfinity, hoppositePair, hfiniteOpposite, hX, hY, houtInfinity⟩
  let z := AffineSlope.ofElem zero
  let inactiveX0 := if Q.infinity.eval ρ.int = 1 then P.X else z
  let inactiveY0 := if Q.infinity.eval ρ.int = 1 then P.Y else z
  let inactiveX := if P.infinity.eval ρ.int = 1 then Q.X else inactiveX0
  let inactiveY := if P.infinity.eval ρ.int = 1 then Q.Y else inactiveY0
  refine ⟨inactiveX0, inactiveY0, inactiveX, inactiveY, ?_, ?_,
    ?_, ?_, ?_, ?_, bothInfinity, oppositePair, finiteOpposite,
    hbothInfinity, hoppositePair, hfiniteOpposite, houtInfinity⟩
  all_goals
    rcases hPinf with hp | hp <;>
    rcases hQinf with hq | hq <;>
    rcases hactive with ha | ha <;>
    simp_all [inactiveX0, inactiveY0, inactiveX, inactiveY, z,
      AffineSlope.SelectZModSpec, Gated4Spec, AffineSlope.AndBitSpec,
      AddControlSpec]

theorem active_zero_of_finite_zero {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl}
    (hcontrol : AddControlSpec ρ P Q control)
    (hfinite0 : control.finite.eval ρ.int = 0) :
    control.active.eval ρ.int = 0 := by
  rcases hcontrol with ⟨_, _, _, doubleKind, genericCase, _,
    hdoubleCase, hgenericCase, hactive⟩
  have hd : control.doubleCase.eval ρ.int = 0 := by
    rw [hdoubleCase.1, hfinite0]
    norm_num
  have hg : genericCase.eval ρ.int = 0 := by
    rw [hgenericCase.1, hfinite0]
    norm_num
  omega

theorem output_gated_cases {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl} {bothInfinity : LC ℤ}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ)
    (hcontrol : AddControlSpec ρ P Q control)
    (hbothInfinity :
      AffineSlope.AndBitSpec ρ P.infinity Q.infinity bothInfinity) :
    Gated4Cases ρ control.active P.infinity
      (Q.infinity - bothInfinity) (control.finite - control.active) := by
  rcases hP with ⟨_, _, _, _, _, _, hPinf⟩
  rcases hQ with ⟨_, _, _, _, _, _, hQinf⟩
  have hactive := hcontrol.active_bit
  have hfiniteActive := active_zero_of_finite_zero hcontrol
  rcases hPinf with hp | hp <;>
    rcases hQinf with hq | hq <;>
    rcases hactive with ha | ha <;>
    simp_all [Gated4Cases, AffineSlope.AndBitSpec, AddControlSpec]

@[spec 2000] theorem selectGated4Coordinate_complete
    {description : String} {gate1 gate2 gate3 gate4 : LC ℤ}
    {value1 value2 value3 value4 : AffineSlope.Rep}
    (hcases : Gated4Cases ρ gate1 gate2 gate3 gate4)
    (hvalue1 : value1.Valid ρ)
    (hvalue1Canonical : value1.intVal.eval ρ.int < base.modulus)
    (hvalue2 : value2.Valid ρ)
    (hvalue2Canonical : value2.intVal.eval ρ.int < base.modulus)
    (hvalue3 : value3.Valid ρ)
    (hvalue3Canonical : value3.intVal.eval ρ.int < base.modulus)
    (hvalue4 : value4.Valid ρ)
    (hvalue4Canonical : value4.intVal.eval ρ.int < base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectGated4Rep 256 2 description
        gate1 gate2 gate3 gate4 value1 value2 value3 value4)
    ⦃⇓ out => ⌜Gated4Spec ρ gate1 gate2 gate3 gate4
      value1 value2 value3 value4 out ∧ out.Valid ρ ∧
      out.intVal.eval ρ.int < base.modulus ∧ out.bound = 2⌝⦄ := by
  exact selectGated4Rep_complete hcases hvalue1 hvalue1Canonical
    hvalue2 hvalue2Canonical hvalue3 hvalue3Canonical
    hvalue4 hvalue4Canonical base.fits (by
      have := base.positive
      omega)

@[spec] theorem selectAddCoordinateCollapsed_complete
    {Pcoord Qcoord candidate : AffineSlope.Rep}
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {bothInfinity : LC ℤ}
    (hcases : Gated4Cases ρ control.active P.infinity
      (Q.infinity - bothInfinity) (control.finite - control.active))
    (hcandidate : candidate.Valid ρ)
    (hcandidateCanonical : candidate.intVal.eval ρ.int < base.modulus)
    (hQcoord : Qcoord.Valid ρ)
    (hQcoordCanonical : Qcoord.intVal.eval ρ.int < base.modulus)
    (hPcoord : Pcoord.Valid ρ)
    (hPcoordCanonical : Pcoord.intVal.eval ρ.int < base.modulus)
    (hzero : (AffineSlope.ofElem zero).Valid ρ)
    (hzeroCanonical :
      (AffineSlope.ofElem zero).intVal.eval ρ.int < base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectAddCoordinateCollapsed Pcoord Qcoord candidate
        P Q control bothInfinity)
    ⦃⇓ out => ⌜Gated4Spec ρ control.active P.infinity
      (Q.infinity - bothInfinity) (control.finite - control.active)
      candidate Qcoord Pcoord (AffineSlope.ofElem zero) out ∧
      out.Valid ρ ∧ out.intVal.eval ρ.int < base.modulus ∧
      out.bound = 2⌝⦄ := by
  unfold AffineSlope.selectAddCoordinateCollapsed
  exact selectGated4Coordinate_complete hcases hcandidate
    hcandidateCanonical hQcoord hQcoordCanonical hPcoord
    hPcoordCanonical hzero hzeroCanonical

@[spec] theorem selectAddOutputCollapsed_complete
    {P Q : AffineSlope.Point} {control : AffineSlope.AddControl}
    {candidate : AffineSlope.Rep × AffineSlope.Rep}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ)
    (hcontrol : AddControlSpec ρ P Q control)
    (hcandidateX : candidate.1.Valid ρ)
    (hcandidateXCanonical :
      candidate.1.intVal.eval ρ.int < base.modulus)
    (hcandidateY : candidate.2.Valid ρ)
    (hcandidateYCanonical :
      candidate.2.intVal.eval ρ.int < base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (AffineSlope.selectAddOutputCollapsed P Q control candidate)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      SelectAddOutputSpec ρ P Q control candidate out⌝⦄ := by
  have hP' := hP
  have hQ' := hQ
  have hcontrol' := hcontrol
  rcases hcontrol with ⟨hsame, hopposite, hfinite, _, _, _, _, _, _⟩
  rcases hP with ⟨hPXbound, hPX, hPXCanonical,
    hPYbound, hPY, hPYCanonical, hPinf⟩
  rcases hQ with ⟨hQXbound, hQX, hQXCanonical,
    hQYbound, hQY, hQYCanonical, hQinf⟩
  have hzeroElem : zero.Valid ρ :=
    Modular.ofNat_valid base 0 (by native_decide) (by native_decide)
  have hzero : (AffineSlope.ofElem zero).Valid ρ :=
    Modular.Lazy.ofElem_valid base hzeroElem
  have hzeroCanonical :
      (AffineSlope.ofElem zero).intVal.eval ρ.int < base.modulus :=
    hzeroElem.2
  mvcgen [AffineSlope.selectAddOutputCollapsed]
  all_goals first
    | exact hPinf
    | exact hQinf
    | exact hsame.1
    | exact hopposite.1
    | exact hfinite.2
    | exact hcandidateX
    | exact hcandidateY
    | exact hcandidateXCanonical
    | exact hcandidateYCanonical
    | exact hPX
    | exact hPY
    | exact hQX
    | exact hQY
    | exact hPXCanonical
    | exact hPYCanonical
    | exact hQXCanonical
    | exact hQYCanonical
    | exact hzero
    | exact hzeroCanonical
    | exact output_gated_cases hP' hQ' hcontrol' (by assumption)
    | skip
  case vc24.success.success.success.success =>
    rename_i bothInfinity hbothInfinity X hX Y hY
      finiteOpposite hfiniteOpposite
    rcases hfiniteOpposite with
      ⟨oppositePair, hoppositePair, hfiniteOpposite⟩
    have hcollapsed : CollapsedSelectAddOutputSpec ρ P Q control
        candidate ⟨X, Y, bothInfinity + finiteOpposite⟩ :=
      ⟨bothInfinity, oppositePair, finiteOpposite,
        hbothInfinity, hoppositePair, hfiniteOpposite,
        hX.1, hY.1, by simp⟩
    have hout := hcollapsed.toSelectAddOutputSpec hPinf hQinf hcontrol'
    exact ⟨⟨hX.2.2.2, hX.2.1, hX.2.2.1,
      hY.2.2.2, hY.2.1, hY.2.2.1,
      SelectAddOutputSpec.infinity_bit hP' hQ' hcontrol' hout⟩,
      hout⟩

end Freigen.F2Z.Examples.P256.AffineSlope.Aux
