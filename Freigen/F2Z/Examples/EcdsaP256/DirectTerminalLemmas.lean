import Freigen.F2Z.Examples.EcdsaP256.DirectTerminalImpl
import Freigen.F2Z.Examples.P256.CanonicalXLemmas

/-!
# Semantics of direct terminal ECDSA acceptance

The terminal complete addition is constrained directly to the signature
scalar `r`.  The 127-bit slack proves that the optional addition of the scalar
modulus still lies below the P-256 base modulus.
-/

namespace Freigen.F2Z.Examples.EcdsaP256

open Std.Do
open scoped Std.Do
open Modular
open P256
open AffineSlope AffineSlope.Aux

private theorem nat_eq_zero_or_one_of_lt_two {x : Nat} (h : x < 2) :
    x = 0 ∨ x = 1 := by omega

def TerminalPointAcceptanceSpec (rho : WF.Valuation) (r : Fn)
    (p : Reference.Point) : Prop :=
  match p with
  | 0 => False
  | .some x _ _ =>
      (x.val : ZMod P256.scalar.modulus) =
        (r.evalNat rho : ZMod P256.scalar.modulus)

def directTerminalTarget (r : Fn) (qScalar qBase : U 1) :
    AffineSlope.Rep :=
  { intVal := r.val.intVal + scalar.modulus • qScalar.intVal +
      base.modulus • qBase.intVal
    bound := 2 }

def DirectTerminalSelectSpec (rho : WF.Valuation) (r : Fn)
    (P Q : AffineSlope.Point) (control : AffineSlope.AddControl)
    (candidateX : AffineSlope.Rep) : Prop :=
  ∃ qScalar qBase : U 1, ∃ slack : U 127,
    qScalar.Valid rho ∧ qBase.Valid rho ∧ slack.Valid rho ∧
    ∃ bothInfinity oppositePair finiteOpposite : LC ℤ,
      Gated3Spec rho control.active P.infinity
        (Q.infinity - bothInfinity) candidateX Q.X P.X
        (directTerminalTarget r qScalar qBase) ∧
      AndBitSpec rho P.infinity Q.infinity bothInfinity ∧
      AndBitSpec rho control.sameX control.oppositeY oppositePair ∧
      AndBitSpec rho control.finite oppositePair finiteOpposite ∧
      bothInfinity.eval rho.int + finiteOpposite.eval rho.int = 0 ∧
      qScalar.intVal.eval rho.int *
        (r.val.intVal.eval rho.int + slack.intVal.eval rho.int + 1 -
          (base.modulus - scalar.modulus : Nat)) = 0

@[spec] theorem selectAddOutputDirectTerminal_sound
    {r : Fn} {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl} {candidateX : AffineSlope.Rep} :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (selectAddOutputDirectTerminal r P Q control candidateX)
    ⦃⇓ _ => ⌜DirectTerminalSelectSpec ρ r P Q control candidateX⌝⦄ := by
  mvcgen [selectAddOutputDirectTerminal]
  rename_i bothInfinity hbothInfinity
  intro bits
  mvcgen
  case vc1 =>
    rename_i qScalar hqScalar qBase hqBase slack hslack
      hactive hPInfinity hQInfinity finiteOpposite hfiniteOpposite hinfinity
    intro hcanonical
    rcases hfiniteOpposite with
      ⟨oppositePair, hoppositePair, hfiniteOpposite⟩
    refine ⟨qScalar, qBase, slack, hqScalar.1, hqBase.1, hslack.1,
      bothInfinity, oppositePair, finiteOpposite, ?_, hbothInfinity,
      hoppositePair, hfiniteOpposite, ?_, ?_⟩
    · unfold Gated3Spec directTerminalTarget
      constructor
      · intro hgate
        have heq := hactive.2
        simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul,
          LC.eval_zero, nsmul_eq_mul, hgate, one_mul] at heq
        have heqInt : candidateX.intVal.eval ρ.int =
            r.val.intVal.eval ρ.int +
              scalar.modulus * qScalar.intVal.eval ρ.int +
              base.modulus * qBase.intVal.eval ρ.int := by omega
        apply congrArg (Int.castRingHom (ZMod base.modulus)) at heqInt
        simpa [Modular.Lazy.evalZMod] using heqInt.symm
      constructor
      · intro hgate
        have heq := hPInfinity.2
        simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul,
          LC.eval_zero, nsmul_eq_mul, hgate, one_mul] at heq
        have heqInt : Q.X.intVal.eval ρ.int =
            r.val.intVal.eval ρ.int +
              scalar.modulus * qScalar.intVal.eval ρ.int +
              base.modulus * qBase.intVal.eval ρ.int := by omega
        apply congrArg (Int.castRingHom (ZMod base.modulus)) at heqInt
        simpa [Modular.Lazy.evalZMod] using heqInt.symm
      · intro hgate
        have heq := hQInfinity.2
        simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul,
          LC.eval_zero, nsmul_eq_mul, hgate, one_mul] at heq
        have heqInt : P.X.intVal.eval ρ.int =
            r.val.intVal.eval ρ.int +
              scalar.modulus * qScalar.intVal.eval ρ.int +
              base.modulus * qBase.intVal.eval ρ.int := by omega
        apply congrArg (Int.castRingHom (ZMod base.modulus)) at heqInt
        simpa [Modular.Lazy.evalZMod] using heqInt.symm
    · simpa [LC.eval_add] using hinfinity.2.symm
    · simpa [LC.eval_sub, LC.eval_add, LC.eval_nsmul,
        LC.eval_ofConst, nsmul_eq_mul] using hcanonical

theorem DirectTerminalSelectSpec.accepts_mathlib
    {r : Fn} {P Q : AffineSlope.Point}
    {p q : Reference.Point} {control : AffineSlope.AddControl}
    {candidateX : AffineSlope.Rep}
    (hr : r.Valid ρ)
    (hP : Reference.Represents ρ P p)
    (hQ : Reference.Represents ρ Q q)
    (hcontrol : AddControlSpec ρ P Q control)
    (hcandidate : AddCandidateXSpec ρ P Q control candidateX)
    (hselect : DirectTerminalSelectSpec ρ r P Q control candidateX) :
    TerminalPointAcceptanceSpec ρ r (p + q) := by
  rcases hselect with
    ⟨qScalar, qBase, slack, hqScalar, hqBase, hslack,
      bothInfinity, oppositePair, finiteOpposite, htarget,
      hbothInfinity, hoppositePair, hfiniteOpposite, hinfinity,
      hcanonical⟩
  let out : AffineSlope.XPoint :=
    ⟨directTerminalTarget r qScalar qBase,
      bothInfinity + finiteOpposite⟩
  have hcases := hcontrol.x_output_gated_cases hP.1 hQ.1 hbothInfinity
  have hnotDefault :
      (control.finite - control.active).eval ρ.int ≠ 1 := by
    intro hdefault
    have hactiveBit := hcontrol.active_bit
    rcases hcontrol with
      ⟨hsame, hopposite, hfinite, doubleKind, genericCase,
        hdoubleKind, hdoubleCase, hgenericCase, hactive⟩
    have hfinite1 : control.finite.eval ρ.int = 1 := by
      simp only [LC.eval_sub] at hdefault
      rcases hfinite.2 with hf0 | hf1 <;>
        rcases hactiveBit with ha0 | ha1 <;> omega
    have hactive0 : control.active.eval ρ.int = 0 := by
      simp only [LC.eval_sub, hfinite1] at hdefault
      omega
    have hgeneric0 : genericCase.eval ρ.int = 0 := by
      rw [hactive] at hactive0
      rcases hdoubleCase.2 with hd0 | hd1 <;>
        rcases hgenericCase.2 with hg0 | hg1 <;> omega
    have hsame1 : control.sameX.eval ρ.int = 1 := by
      rw [hgenericCase.1, hfinite1] at hgeneric0
      rcases hsame.1 with hs0 | hs1
      · simp [hs0] at hgeneric0
      · exact hs1
    have hdouble0 : control.doubleCase.eval ρ.int = 0 := by
      rw [hactive] at hactive0
      rcases hdoubleCase.2 with hd0 | hd1 <;>
        rcases hgenericCase.2 with hg0 | hg1 <;> omega
    have hdoubleKind0 : doubleKind.eval ρ.int = 0 := by
      rw [hdoubleCase.1, hfinite1] at hdouble0
      simpa using hdouble0
    have hopposite1 : control.oppositeY.eval ρ.int = 1 := by
      rw [hdoubleKind.1, hsame1] at hdoubleKind0
      rcases hopposite.1 with ho0 | ho1
      · simp [ho0] at hdoubleKind0
      · exact ho1
    have hboth0 : bothInfinity.eval ρ.int = 0 := by
      rw [hbothInfinity.1]
      rcases hcases with hc | hc | hc | hc <;> simp_all
    have hoppositePair1 : oppositePair.eval ρ.int = 1 := by
      rw [hoppositePair.1, hsame1, hopposite1]
      norm_num
    have hfiniteOpposite1 : finiteOpposite.eval ρ.int = 1 := by
      rw [hfiniteOpposite.1, hfinite1, hoppositePair1]
      norm_num
    omega
  have hout : SelectAddXOutputSpec ρ P Q control candidateX out := by
    refine ⟨bothInfinity, oppositePair, finiteOpposite,
      ⟨htarget.1, htarget.2.1, htarget.2.2, ?_⟩,
      hbothInfinity, hoppositePair, hfiniteOpposite, by simp [out]⟩
    intro hdefault
    exact (hnotDefault hdefault).elim
  have houtRep := add_specs_x_raw hP hQ hcontrol hcandidate hout
  have houtMath : Reference.XRepresents ρ out (p + q) :=
    ⟨houtRep.1, houtRep.2.trans (Reference.xCoordinate_slopeAdd p q)⟩
  rcases hqScalarCases : (qScalar.eval ρ).toNat with _ | qScalarNat
  · have hqScalarValue : qScalar.intVal.eval ρ.int = 0 := by
      rw [U.intVal_eval_eq_eval_toNat qScalar hqScalar, hqScalarCases]
      rfl
    have hcanonicalLt : r.evalNat ρ < base.modulus :=
      (Elem.evalNat_lt scalar hr).trans (by
        norm_num [base, baseModulus, scalar, scalarModulus])
    rcases hsum : p + q with _ | ⟨x, y, hcurve⟩
    · have := Reference.XRepresents.zero (hsum ▸ houtMath)
      change (bothInfinity + finiteOpposite).eval ρ.int = 1 at this
      simp only [LC.eval_add] at this
      omega
    · have hx := Reference.XRepresents.some (hsum ▸ houtMath)
      simp only [TerminalPointAcceptanceSpec]
      have hxField := hx.2
      unfold out directTerminalTarget Modular.Lazy.evalZMod at hxField
      simp only [LC.eval_add, LC.eval_nsmul, nsmul_eq_mul,
        hqScalarValue] at hxField
      have hxField' : (Int.castRingHom (ZMod base.modulus))
          (r.val.intVal.eval ρ.int) = x := by
        simpa using hxField
      change (((r.val.intVal.eval ρ.int : Int) : ZMod base.modulus)) = x
        at hxField'
      have hxVal := congrArg
        (fun z : ZMod base.modulus => (z.val : Int)) hxField'
      have hrBaseLt : r.val.intVal.eval ρ.int < base.modulus :=
        hr.2.trans (by
          norm_num [base, baseModulus, scalar, scalarModulus])
      rw [ZMod.val_intCast, Int.emod_eq_of_lt
        (U.intVal_nonneg r.val hr.1) hrBaseLt] at hxVal
      have hxNat : x.val = r.evalNat ρ := by
        unfold Elem.evalNat
        have hrCast := Int.toNat_of_nonneg (U.intVal_nonneg r.val hr.1)
        exact_mod_cast (hrCast.trans hxVal).symm
      rw [hxNat]
  · have hqScalarLt : qScalarNat < 1 := by
      have hlt := (qScalar.eval ρ).isLt
      rw [hqScalarCases] at hlt
      omega
    have hqScalarNatZero : qScalarNat = 0 := by omega
    subst qScalarNat
    have hqScalarValue : qScalar.intVal.eval ρ.int = 1 := by
      rw [U.intVal_eval_eq_eval_toNat qScalar hqScalar, hqScalarCases]
      rfl
    have hslack0 := U.intVal_nonneg slack hslack
    have hr0 := U.intVal_nonneg r.val hr.1
    have hrlt := hr.2
    have hpEq : (base.modulus : Int) =
        scalar.modulus + (base.modulus - scalar.modulus : Nat) := by
      norm_num [base, baseModulus, scalar, scalarModulus]
    have hcanonicalLtInt :
        r.val.intVal.eval ρ.int + scalar.modulus < base.modulus := by
      rw [hqScalarValue] at hcanonical
      omega
    have hcanonicalLt : r.evalNat ρ + scalar.modulus < base.modulus := by
      unfold Elem.evalNat
      rw [← Int.toNat_of_nonneg hr0] at hcanonicalLtInt
      exact_mod_cast hcanonicalLtInt
    rcases hsum : p + q with _ | ⟨x, y, hcurve⟩
    · have := Reference.XRepresents.zero (hsum ▸ houtMath)
      change (bothInfinity + finiteOpposite).eval ρ.int = 1 at this
      simp only [LC.eval_add] at this
      omega
    · have hx := Reference.XRepresents.some (hsum ▸ houtMath)
      simp only [TerminalPointAcceptanceSpec]
      have hxField := hx.2
      unfold out directTerminalTarget Modular.Lazy.evalZMod at hxField
      simp only [LC.eval_add, LC.eval_nsmul, nsmul_eq_mul,
        hqScalarValue] at hxField
      have hxField' : (Int.castRingHom (ZMod base.modulus))
          (r.val.intVal.eval ρ.int + scalar.modulus) = x := by
        simpa using hxField
      change ((((r.val.intVal.eval ρ.int + scalar.modulus : Int)) :
        ZMod base.modulus)) = x at hxField'
      have hxVal := congrArg
        (fun z : ZMod base.modulus => (z.val : Int)) hxField'
      rw [ZMod.val_intCast, Int.emod_eq_of_lt
        (by omega) hcanonicalLtInt] at hxVal
      have hxNat : x.val = r.evalNat ρ + scalar.modulus := by
        unfold Elem.evalNat
        have hrCast := Int.toNat_of_nonneg hr0
        have hcastInt : (((r.val.intVal.eval ρ.int).toNat +
            scalar.modulus : Nat) : Int) = x.val := by
          push_cast
          rw [hrCast]
          exact hxVal
        have hcast : ((r.val.intVal.eval ρ.int).toNat +
            scalar.modulus : Nat) = x.val := by exact_mod_cast hcastInt
        exact hcast.symm
      rw [hxNat]
      simp

@[spec] theorem addCompleteCollapsedDirectTerminal_sound_mathlib
    {r : Fn} {P Q : AffineSlope.Point} {p q : Reference.Point}
    (hr : r.Valid ρ)
    (hP : Reference.Represents ρ P p)
    (hQ : Reference.Represents ρ Q q) :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (addCompleteCollapsedDirectTerminal r P Q)
    ⦃⇓ _ => ⌜TerminalPointAcceptanceSpec ρ r (p + q)⌝⦄ := by
  mvcgen [addCompleteCollapsedDirectTerminal]
  case vc2.success.success.success =>
    intro hselect
    exact hselect.accepts_mathlib hr hP hQ (by assumption) (by assumption)

theorem directTerminal_complete_conditions
    {r : Fn} {P Q : AffineSlope.Point} {p q : Reference.Point}
    {control : AffineSlope.AddControl} {candidateX : AffineSlope.Rep}
    (hr : r.Valid ρ) (hPvalid : P.Valid ρ) (hQvalid : Q.Valid ρ)
    (hP : Reference.NormalizedRep ρ P p)
    (hQ : Reference.NormalizedRep ρ Q q)
    (hcontrol : AddControlSpec ρ P Q control)
    (hcandidate : AddCandidateXSpec ρ P Q control candidateX)
    (hcandidateValid : candidateX.Valid ρ)
    (hcandidateCanonical : candidateX.intVal.eval ρ.int < base.modulus)
    (haccept : TerminalPointAcceptanceSpec ρ r (p + q)) :
    P.infinity.eval ρ.int * Q.infinity.eval ρ.int +
        control.finite.eval ρ.int *
          (control.sameX.eval ρ.int * control.oppositeY.eval ρ.int) = 0 ∧
      (let source := if control.active.eval ρ.int = 1 then
          candidateX.intVal.eval ρ.int
        else if P.infinity.eval ρ.int = 1 then Q.X.intVal.eval ρ.int
        else if Q.infinity.eval ρ.int = 1 then P.X.intVal.eval ρ.int
        else 0
      source.toNat % scalar.modulus = r.evalNat ρ) := by
  let source : Int := if control.active.eval ρ.int = 1 then
      candidateX.intVal.eval ρ.int
    else if P.infinity.eval ρ.int = 1 then Q.X.intVal.eval ρ.int
    else if Q.infinity.eval ρ.int = 1 then P.X.intVal.eval ρ.int
    else 0
  let sourceRep : AffineSlope.Rep :=
    { intVal := LC.ofConst source, bound := 2 }
  let bothInfinity : LC ℤ := LC.ofConst
    (P.infinity.eval ρ.int * Q.infinity.eval ρ.int)
  let oppositePair : LC ℤ := LC.ofConst
    (control.sameX.eval ρ.int * control.oppositeY.eval ρ.int)
  let finiteOpposite : LC ℤ := LC.ofConst
    (control.finite.eval ρ.int *
      (control.sameX.eval ρ.int * control.oppositeY.eval ρ.int))
  have hbothInfinity : AndBitSpec ρ P.infinity Q.infinity bothInfinity := by
    constructor
    · simp [bothInfinity]
    · rcases hPvalid.2.2.2.2.2.2 with hp | hp <;>
        rcases hQvalid.2.2.2.2.2.2 with hq | hq <;>
        simp [bothInfinity, hp, hq]
  have hoppositePair : AndBitSpec ρ control.sameX control.oppositeY
      oppositePair := by
    constructor
    · simp [oppositePair]
    · rcases hcontrol.1.1 with hs | hs <;>
        rcases hcontrol.2.1.1 with ho | ho <;>
        simp [oppositePair, hs, ho]
  have hfiniteOpposite : AndBitSpec ρ control.finite oppositePair
      finiteOpposite := by
    constructor
    · simp [finiteOpposite, oppositePair]
    · rcases hcontrol.2.2.1.2 with hf | hf <;>
        rcases hoppositePair.2 with ho | ho <;>
        simp [finiteOpposite, oppositePair, hf, ho]
  have hcases := hcontrol.x_output_gated_cases
    hPvalid.2.2.2.2.2.2 hQvalid.2.2.2.2.2.2 hbothInfinity
  let out : AffineSlope.XPoint :=
    ⟨sourceRep, bothInfinity + finiteOpposite⟩
  have hout : SelectAddXOutputSpec ρ P Q control candidateX out := by
    refine ⟨bothInfinity, oppositePair, finiteOpposite, ?_,
      hbothInfinity, hoppositePair, hfiniteOpposite, by simp [out]⟩
    unfold Gated4Spec
    constructor
    · intro hgate
      rcases hcases with hc | hc | hc | hc <;>
        simp_all [out, source, sourceRep, Modular.Lazy.evalZMod]
    constructor
    · intro hgate
      rcases hcases with hc | hc | hc | hc <;>
        simp_all [out, source, sourceRep, Modular.Lazy.evalZMod]
    constructor
    · intro hgate
      rcases hQvalid.2.2.2.2.2.2 with hq | hq <;>
        rcases hcases with hc | hc | hc | hc <;>
        simp_all [out, source, sourceRep, Modular.Lazy.evalZMod,
          AndBitSpec, AddControlSpec, LC.eval_ofConst]
    · intro hgate
      rcases hQvalid.2.2.2.2.2.2 with hq | hq <;>
        rcases hcases with hc | hc | hc | hc <;>
        simp_all [out, source, sourceRep, Modular.Lazy.evalZMod,
          AffineSlope.ofElem, Modular.Lazy.ofElem, AndBitSpec,
          AddControlSpec, P256.zero, P256.fpConst, Modular.ofNat,
          U.intVal, LC.eval_ofConst]
  have houtRep := add_specs_x_normalized hP hQ hcontrol hcandidate hout
  rcases hsum : p + q with _ | ⟨x, y, hcurve⟩
  · rw [hsum] at haccept
    exact haccept.elim
  · have hx := Reference.XRepresents.some (hsum ▸ houtRep.1)
    have hinfinity :
        P.infinity.eval ρ.int * Q.infinity.eval ρ.int +
          control.finite.eval ρ.int *
            (control.sameX.eval ρ.int * control.oppositeY.eval ρ.int) = 0 := by
      simpa [out, bothInfinity, finiteOpposite] using hx.1
    have hsource0 : 0 ≤ source := by
      simp only [source]
      split_ifs <;> first
        | exact hcandidateValid.1
        | exact hQvalid.2.1.1
        | exact hPvalid.2.1.1
        | omega
    have hsourceLt : source < base.modulus := by
      simp only [source]
      split_ifs <;> first
        | exact hcandidateCanonical
        | exact hQvalid.2.2.1
        | exact hPvalid.2.2.1
        | norm_num [base, baseModulus]
    have hxField := hx.2
    change ((source : ZMod base.modulus)) = x at hxField
    have hxVal := congrArg
      (fun z : ZMod base.modulus => (z.val : Int)) hxField
    have hxVal' : source = (x.val : Int) := by
      simpa only [ZMod.val_intCast,
        Int.emod_eq_of_lt hsource0 hsourceLt] using hxVal
    have hsourceNat : source.toNat = x.val := by
      have hsourceCast := Int.toNat_of_nonneg hsource0
      exact_mod_cast hsourceCast.trans hxVal'
    rw [hsum] at haccept
    simp only [TerminalPointAcceptanceSpec] at haccept
    have hacceptVal := congrArg ZMod.val haccept
    rw [ZMod.val_natCast, ZMod.val_natCast,
      Nat.mod_eq_of_lt (Elem.evalNat_lt scalar hr)] at hacceptVal
    constructor
    · exact hinfinity
    · change source.toNat % scalar.modulus = r.evalNat ρ
      rw [hsourceNat]
      exact hacceptVal

@[spec] theorem selectAddOutputDirectTerminal_complete
    {r : Fn} {P Q : AffineSlope.Point}
    {control : AffineSlope.AddControl} {candidateX : AffineSlope.Rep}
    (hr : r.Valid ρ) (hP : P.Valid ρ) (hQ : Q.Valid ρ)
    (hcontrol : AddControlSpec ρ P Q control)
    (hcandidate : candidateX.Valid ρ)
    (hcandidateCanonical : candidateX.intVal.eval ρ.int < base.modulus)
    (hresultFinite :
      P.infinity.eval ρ.int * Q.infinity.eval ρ.int +
        control.finite.eval ρ.int *
          (control.sameX.eval ρ.int * control.oppositeY.eval ρ.int) = 0)
    (hsourceAccept :
      let source := if control.active.eval ρ.int = 1 then
          candidateX.intVal.eval ρ.int
        else if P.infinity.eval ρ.int = 1 then Q.X.intVal.eval ρ.int
        else if Q.infinity.eval ρ.int = 1 then P.X.intVal.eval ρ.int
        else 0
      source.toNat % scalar.modulus = r.evalNat ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (selectAddOutputDirectTerminal r P Q control candidateX)
    ⦃⇓ _ => ⌜DirectTerminalSelectSpec ρ r P Q control candidateX⌝⦄ := by
  mvcgen [selectAddOutputDirectTerminal]
  case vc1.hx => exact hP.2.2.2.2.2.2
  case vc2.hy => exact hQ.2.2.2.2.2.2
  case vc3.success =>
    rename_i bothInfinity hbothInfinity
    let source : Int := if control.active.eval ρ.int = 1 then
        candidateX.intVal.eval ρ.int
      else if P.infinity.eval ρ.int = 1 then Q.X.intVal.eval ρ.int
      else if Q.infinity.eval ρ.int = 1 then P.X.intVal.eval ρ.int
      else 0
    have hsource0 : 0 ≤ source := by
      simp only [source]
      split_ifs <;> first
        | exact hcandidate.1
        | exact hQ.2.1.1
        | exact hP.2.1.1
        | omega
    have hsourceLt : source < base.modulus := by
      simp only [source]
      split_ifs <;> first
        | exact hcandidateCanonical
        | exact hQ.2.2.1
        | exact hP.2.2.1
        | norm_num [base, baseModulus]
    have hsourceNatLt : source.toNat < base.modulus :=
      (Int.toNat_lt hsource0).2 hsourceLt
    have hrNatLt := Elem.evalNat_lt scalar hr
    have hmod : source.toNat % scalar.modulus = r.evalNat ρ := by
      simpa [source] using hsourceAccept
    let qScalarNat := source.toNat / scalar.modulus
    have hqScalarLt : qScalarNat < 2 := by
      rw [Nat.div_lt_iff_lt_mul scalar.positive]
      exact hsourceNatLt.trans (by
        norm_num [base, baseModulus, scalar, scalarModulus])
    have hqScalarCases : qScalarNat = 0 ∨ qScalarNat = 1 := by
      exact nat_eq_zero_or_one_of_lt_two hqScalarLt
    have hdecomp : source.toNat =
        r.evalNat ρ + scalar.modulus * qScalarNat := by
      calc
        source.toNat = source.toNat % scalar.modulus +
            scalar.modulus * (source.toNat / scalar.modulus) :=
          (Nat.mod_add_div source.toNat scalar.modulus).symm
        _ = r.evalNat ρ + scalar.modulus * qScalarNat := by
          rw [hmod]
    have hquotientCalc :
        (source.toNat - r.evalNat ρ) / scalar.modulus = qScalarNat := by
      rw [hdecomp, Nat.add_sub_cancel_left]
      exact Nat.mul_div_right qScalarNat scalar.positive
    have hquotientCalc' :
        (source.toNat - (r.val.intVal.eval ρ.int).toNat) /
          scalar.modulus = qScalarNat := by
      simpa [Elem.evalNat] using hquotientCalc
    let slackNat := if qScalarNat = 1 then
        base.modulus - scalar.modulus - 1 - r.evalNat ρ
      else 0
    have hslackLt : slackNat < 2 ^ 127 := by
      simp only [slackNat]
      split
      · exact (Nat.sub_le _ _).trans_lt ((Nat.sub_le _ _).trans_lt (by
          norm_num [base, baseModulus, scalar, scalarModulus]))
      · norm_num
    let bits : Vector Bool 129 := Vector.ofFn fun i =>
      if i.val = 0 then qScalarNat.testBit 0
      else if i.val = 1 then false
      else slackNat.testBit (i.val - 2)
    refine ⟨bits, ?_, ?_⟩
    · simp [WF.interpHint, WF.evalArgs, directTerminalHint,
        source, bits, hsource0, Nat.mod_eq_of_lt hsourceNatLt,
        Nat.div_eq_of_lt hsourceNatLt, Elem.evalNat,
        U.intVal_nonneg r.val hr.1, hquotientCalc', slackNat]
    · mvcgen
      rename_i qScalar hqScalar qBase hqBase slack hslack
      have hqScalarValue : qScalar.intVal.eval ρ.int = qScalarNat := by
        rw [U.Rel.intVal hqScalar]
        have hwordInt := congrArg Int.ofNat
          (Modular.Aux.constWord_eval_toNat (n := 1)
            qScalarNat hqScalarLt ρ)
        simpa [bits, Function.comp_def] using hwordInt
      have hqBaseValue : qBase.intVal.eval ρ.int = 0 := by
        rw [U.Rel.intVal hqBase]
        have hwordInt := congrArg Int.ofNat
          (Modular.Aux.constWord_eval_toNat (n := 1) 0 (by norm_num) ρ)
        simpa [bits, Function.comp_def] using hwordInt
      have hslackValue : slack.intVal.eval ρ.int = slackNat := by
        rw [U.Rel.intVal hslack]
        have hwordInt := congrArg Int.ofNat
          (Modular.Aux.constWord_eval_toNat slackNat hslackLt ρ)
        simpa [bits, Function.comp_def] using hwordInt
      have hr0 := U.intVal_nonneg r.val hr.1
      have hsourceInt : source = r.val.intVal.eval ρ.int +
          scalar.modulus * qScalarNat := by
        have hdecompInt := congrArg Int.ofNat hdecomp
        simpa [Elem.evalNat, Int.toNat_of_nonneg hsource0,
          Int.toNat_of_nonneg hr0] using hdecompInt
      have hcases := hcontrol.x_output_gated_cases
        hP.2.2.2.2.2.2 hQ.2.2.2.2.2.2 hbothInfinity
      constructor
      · simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul,
          LC.eval_zero, nsmul_eq_mul, hqScalarValue, hqBaseValue]
        rcases hcases with hc | hc | hc | hc <;>
          simp_all [source, AndBitSpec]
      · mvcgen
        case vc1.h =>
          constructor
          · have hPgate :
              P.infinity.eval ρ.int *
                (Q.X.intVal.eval ρ.int -
                  (r.val.intVal.eval ρ.int +
                    scalar.modulus * qScalar.intVal.eval ρ.int +
                    base.modulus * qBase.intVal.eval ρ.int)) = 0 := by
              rcases hcases with hc | hc | hc | hc <;>
                simp_all [source, AndBitSpec]
            simpa [LC.eval_sub, LC.eval_add, LC.eval_nsmul,
              LC.eval_zero, nsmul_eq_mul] using hPgate
          · mvcgen
            case vc1.h =>
              constructor
              · have hQgate :
                    (Q.infinity - bothInfinity).eval ρ.int *
                      (P.X.intVal.eval ρ.int -
                        (r.val.intVal.eval ρ.int +
                          scalar.modulus * qScalar.intVal.eval ρ.int +
                          base.modulus * qBase.intVal.eval ρ.int)) = 0 := by
                    rcases hcases with hc | hc | hc | hc <;>
                      simp_all [source, AndBitSpec]
                simpa [LC.eval_sub, LC.eval_add, LC.eval_nsmul,
                  LC.eval_zero, nsmul_eq_mul] using hQgate
              · mvcgen
                case vc1.hx => exact hcontrol.1.1
                case vc2.hy => exact hcontrol.2.1.1
                case vc3.hz => exact hcontrol.2.2.1.2
                case vc4 =>
                  rename_i finiteOpposite hfiniteOpposite
                  constructor
                  · rcases hfiniteOpposite with
                      ⟨oppositePair, hoppositePair, hfiniteOpposite⟩
                    have hinfinity : bothInfinity.eval ρ.int +
                        finiteOpposite.eval ρ.int = 0 := by
                      simp_all [AndBitSpec]
                    simpa [LC.eval_add] using hinfinity.symm
                  · mvcgen
                    case vc1.right =>
                      have hcanonicalGate :
                          qScalar.intVal.eval ρ.int *
                            (r.val.intVal.eval ρ.int +
                              slack.intVal.eval ρ.int + 1 -
                              (base.modulus - scalar.modulus : Nat)) = 0 := by
                        rcases hqScalarCases with hq0 | hq1
                        · simp [hqScalarValue, hq0]
                        · have hrDelta : r.evalNat ρ <
                              base.modulus - scalar.modulus := by
                            have hpEq : base.modulus = scalar.modulus +
                                (base.modulus - scalar.modulus) := by
                              norm_num [base, baseModulus, scalar,
                                scalarModulus]
                            rw [hq1] at hdecomp
                            omega
                          have hslackEq : r.evalNat ρ + slackNat + 1 =
                              base.modulus - scalar.modulus := by
                            simp only [slackNat, if_pos hq1]
                            omega
                          have hrCast := Int.toNat_of_nonneg hr0
                          have hslackEqInt :
                              r.val.intVal.eval ρ.int + slackNat + 1 =
                                (base.modulus - scalar.modulus : Nat) := by
                            calc
                              _ = (r.evalNat ρ : Int) + slackNat + 1 := by
                                unfold Elem.evalNat
                                rw [hrCast]
                              _ = ((r.evalNat ρ + slackNat + 1 : Nat) :
                                  Int) := by push_cast; ring
                              _ = (base.modulus - scalar.modulus : Nat) := by
                                exact_mod_cast hslackEq
                          rw [hqScalarValue, hq1, hslackValue]
                          omega
                      constructor
                      · simpa [LC.eval_sub, LC.eval_add, LC.eval_ofConst]
                          using hcanonicalGate
                      · rcases hfiniteOpposite with
                          ⟨oppositePair, hoppositePair,
                            hfiniteOpposite⟩
                        refine ⟨qScalar, qBase, slack, hqScalar.1,
                          hqBase.1, hslack.1, bothInfinity, oppositePair,
                          finiteOpposite, ?_, hbothInfinity, hoppositePair,
                          hfiniteOpposite, ?_, hcanonicalGate⟩
                        · unfold Gated3Spec
                          rcases hcases with hc | hc | hc | hc <;>
                            simp_all [source, directTerminalTarget,
                              Modular.Lazy.evalZMod, AndBitSpec]
                        · simp_all [AndBitSpec]

@[spec] theorem addCompleteCollapsedDirectTerminal_complete_mathlib
    {r : Fn} {P Q : AffineSlope.Point} {q p : Reference.Point}
    (hr : r.Valid ρ) (hPvalid : P.Valid ρ) (hQvalid : Q.Valid ρ)
    (hP : Reference.NormalizedRep ρ P p)
    (hQ : Reference.NormalizedRep ρ Q q)
    (hnoTwoTorsion : p = 0 ∨ p + p ≠ 0)
    (haccept : TerminalPointAcceptanceSpec ρ r (p + q)) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (addCompleteCollapsedDirectTerminal r P Q)
    ⦃⇓ _ => ⌜TerminalPointAcceptanceSpec ρ r (p + q)⌝⦄ := by
  mvcgen [addCompleteCollapsedDirectTerminal]
  all_goals first
    | exact hr
    | exact hPvalid
    | exact hQvalid
    | exact hP.1
    | exact hQ.1
    | exact hnoTwoTorsion
    | exact haccept
    | assumption
    | skip
  case vc16 =>
    rename_i control hcontrol candidateX
    intros hcandidateValid _ hcandidateCanonical hcandidate
    exact (directTerminal_complete_conditions hr hPvalid hQvalid hP hQ
      hcontrol hcandidate hcandidateValid hcandidateCanonical haccept).1
  case vc17 =>
    rename_i control hcontrol candidateX
    intros hcandidateValid _ hcandidateCanonical hcandidate
    exact (directTerminal_complete_conditions hr hPvalid hQvalid hP hQ
      hcontrol hcandidate hcandidateValid hcandidateCanonical haccept).2
  all_goals aesop

end Freigen.F2Z.Examples.EcdsaP256
