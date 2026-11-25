import Freigen.F2Z.Examples.EcdsaP256.FixedBaseCombLemmas
import Freigen.F2Z.Examples.EcdsaP256.Radix32Lemmas
import Freigen.F2Z.Examples.EcdsaP256.DirectTerminalLemmas
import Freigen.F2Z.Examples.EcdsaP256.DirectTerminalBlockLemmas
import Freigen.F2Z.Examples.P256.CanonicalXLemmas
import Freigen.F2Z.Examples.P256.XOnlyLemmas

/-! Correctness of the variable-only signed radix-32 branch. -/

namespace Freigen.F2Z.Examples.EcdsaP256

open Std.Do
open scoped Std.Do
open BigOperators
open Modular
open P256

set_option maxRecDepth 10000

def SignedRadix32VariableStepPoint (rho : WF.Valuation) (u2 : Fn)
    (q : Reference.Point) (i : Nat) (acc : Reference.Point) :
    Reference.Point :=
  let exponent := 254 - i
  let doubled := 2 • acc
  if _hq : exponent % 5 = 0 then
    doubled + (boothDigit u2 (exponent / 5) (by omega)).eval rho.int • q
  else doubled

theorem variableOrderZsmul {q : Reference.Point}
    (horder : scalarModulus • q = 0) (k : Int) :
    scalarModulus • (k • q) = 0 := by
  cases k with
  | ofNat n => simpa using Reference.Aux.order_nsmul horder n
  | negSucc n =>
      have h := Reference.Aux.order_nsmul horder (n + 1)
      rw [negSucc_zsmul, neg_nsmul, h, neg_zero]

theorem SignedRadix32VariableStepPoint.order
    {u2 : Fn} {q acc : Reference.Point} {i : Nat}
    (hacc : scalarModulus • acc = 0)
    (hq : scalarModulus • q = 0) :
    scalarModulus • SignedRadix32VariableStepPoint ρ u2 q i acc = 0 := by
  simp only [SignedRadix32VariableStepPoint]
  split
  · apply Reference.Aux.order_add
    · exact Reference.Aux.order_nsmul hacc 2
    · exact variableOrderZsmul hq _
  · exact Reference.Aux.order_nsmul hacc 2

@[spec] theorem signedRadix32VariableStep_sound
    {u2 : Fn} {q : Reference.Point}
    {i : Nat} {hi : i < 255} {acc : AffineSlope.Point}
    {accPoint : Reference.Point}
    (hu2 : u2.val.Valid ρ)
    (hacc : Reference.NormalizedRep ρ acc accPoint)
    (htable : Radix32TableSpec ρ qTable q) :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (signedRadix32VariableStep u2 qTable i hi acc)
    ⦃⇓ out => ⌜Reference.NormalizedRep ρ out
      (SignedRadix32VariableStepPoint ρ u2 q i accPoint)⌝⦄ := by
  mvcgen [signedRadix32VariableStep, SignedRadix32VariableStepPoint]
  case vc3.success =>
    intro hdouble
    split <;> mvcgen -trivial
    case vc1.value => exact boothDigit u2 ((254 - i) / 5) (by omega)
    case vc2.q => exact q
    case vc3.hdigit => assumption
    case vc4.htable => exact htable
    case vc6 => intro _; exact accPoint + accPoint
    case vc7 =>
      intro _
      exact (boothDigit u2 ((254 - i) / 5) (by omega)).eval ρ.int • q
    case vc8 => intro _; exact hdouble
    case vc9 =>
      intro hpoint
      exact SignedRadix32PointSpec.zsmul hpoint
    case vc5.success.success =>
      intro hout
      unfold SignedRadix32VariableStepPoint
      simp_all [two_nsmul]
    case vc1.isFalse =>
      unfold SignedRadix32VariableStepPoint
      simp_all [two_nsmul]

@[spec] theorem signedRadix32VariableStep_complete
    {u2 : Fn} {q : Reference.Point}
    {i : Nat} {hi : i < 255} {acc : AffineSlope.Point}
    {accPoint : Reference.Point}
    (hu2 : u2.val.Valid ρ) (haccValid : acc.Valid ρ)
    (hacc : Reference.NormalizedRep ρ acc accPoint)
    (haccOrder : scalarModulus • accPoint = 0)
    (htableValid : Radix32TableValid ρ qTable)
    (htable : Radix32TableSpec ρ qTable q)
    (hq : q ≠ 0) (horder : scalarModulus • q = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (signedRadix32VariableStep u2 qTable i hi acc)
    ⦃⇓ out => ⌜out.Valid ρ ∧ Reference.NormalizedRep ρ out
      (SignedRadix32VariableStepPoint ρ u2 q i accPoint)⌝⦄ := by
  mvcgen [signedRadix32VariableStep, SignedRadix32VariableStepPoint]
  case vc4.hdouble =>
    exact Reference.Aux.no_two_torsion_of_order haccOrder
  case vc5.success =>
    rename_i accD
    intro haccDValid hdouble
    split <;> mvcgen -trivial
    case vc1.hlow =>
      exact (boothDigit_bounds hu2 ((254 - i) / 5) (by omega)).1
    case vc2.hhigh =>
      exact (boothDigit_bounds hu2 ((254 - i) / 5) (by omega)).2
    case vc3.value => exact boothDigit u2 ((254 - i) / 5) (by omega)
    case vc4.q => exact q
    case vc5.hdigit => assumption
    case vc6.htableValid => exact htableValid
    case vc7.htable => exact htable
    case vc8.hq => exact hq
    case vc9.horder => exact horder
    case vc11 => intro _; exact accPoint + accPoint
    case vc12 =>
      intro _
      exact (boothDigit u2 ((254 - i) / 5) (by omega)).eval ρ.int • q
    case vc13 => intros; exact haccDValid
    case vc14 => intro hpoint _; exact hpoint
    case vc15 => intro _; exact hdouble
    case vc16 =>
      intro hpoint
      exact SignedRadix32PointSpec.zsmul hpoint.2
    case vc17 =>
      intro _
      apply Reference.Aux.no_two_torsion_of_order
      exact Reference.Aux.order_nsmul haccOrder 2
    case vc10.success.success =>
      intro houtValid hout
      refine ⟨houtValid, ?_⟩
      unfold SignedRadix32VariableStepPoint
      simp_all [two_nsmul]
    case vc1.isFalse =>
      exact ⟨haccDValid, by
        unfold SignedRadix32VariableStepPoint
        simp_all [two_nsmul]⟩

def SignedRadix32VariableFoldPoint (rho : WF.Valuation) (u2 : Fn)
    (q : Reference.Point) (indices : List Nat) : Reference.Point :=
  indices.foldl (fun acc i =>
    SignedRadix32VariableStepPoint rho u2 q i acc)
    ((boothDigit u2 51 (by omega)).eval rho.int • q)

@[spec] theorem signedRadix32VariableMul_sound
    {u2 : Fn} {Q : Projective} {q : Reference.Point}
    (hu2 : u2.val.Valid ρ)
    (hQ : Reference.Represents ρ (AffineSlope.ofElems Q.X Q.Y) q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (signedRadix32VariableMul u2 Q)
    ⦃⇓ out => ⌜Reference.NormalizedRep ρ out
      (SignedRadix32VariableFoldPoint ρ u2 q [:255].toList)⌝⦄ := by
  mvcgen -trivial [signedRadix32VariableMul, WF.foldRange] invariants
  · ⇓⟨cur, out⟩ => ⌜Reference.NormalizedRep ρ out
      (SignedRadix32VariableFoldPoint ρ u2 q cur.prefix)⌝
  case vc1.q => exact q
  case vc2.hP => exact hQ
  case vc3.value => exact boothDigit u2 51 (by omega)
  case vc4.q => exact q
  case vc5.hdigit => assumption
  case vc6.htable => assumption
  case vc7.q => exact q
  case vc8.accPoint pref cur suff hsplit b hprev =>
    exact SignedRadix32VariableFoldPoint ρ u2 q pref
  case vc9.hu2 => exact hu2
  case vc10.hacc => assumption
  case vc11.htable => assumption
  case vc12.success pref cur hstep =>
    unfold SignedRadix32VariableFoldPoint at hstep ⊢
    rw [List.foldl_append]
    simpa using hstep
  case vc13.pre =>
    unfold SignedRadix32VariableFoldPoint
    simpa using SignedRadix32PointSpec.zsmul
      ‹SignedRadix32PointSpec _ _ _ _›
  case vc14.post.success => intro h; exact h

@[spec] theorem signedRadix32VariableMul_complete
    {u2 : Fn} {Q : Projective} {q : Reference.Point}
    (hu2 : u2.val.Valid ρ) (hQvalid : Q.Valid ρ)
    (hQ : Reference.Represents ρ (AffineSlope.ofElems Q.X Q.Y) q)
    (hq : q ≠ 0) (horder : scalarModulus • q = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (signedRadix32VariableMul u2 Q)
    ⦃⇓ out => ⌜out.Valid ρ ∧ Reference.NormalizedRep ρ out
      (SignedRadix32VariableFoldPoint ρ u2 q [:255].toList)⌝⦄ := by
  mvcgen -trivial [signedRadix32VariableMul, WF.foldRange] invariants
  · ⇓⟨cur, out⟩ => ⌜out.Valid ρ ∧
      Reference.NormalizedRep ρ out
        (SignedRadix32VariableFoldPoint ρ u2 q cur.prefix) ∧
      scalarModulus •
        SignedRadix32VariableFoldPoint ρ u2 q cur.prefix = 0⌝
  case vc1.q => exact q
  case vc2.hPvalid => exact hQvalid
  case vc3.hP => exact hQ
  case vc4.horder => exact horder
  case vc5.hlow => exact (boothDigit_bounds hu2 51 (by omega)).1
  case vc6.hhigh => exact (boothDigit_bounds hu2 51 (by omega)).2
  case vc7.value => exact boothDigit u2 51 (by omega)
  case vc8.q => exact q
  case vc9.hdigit => assumption
  case vc10.htableValid => exact (by aesop)
  case vc11.htable => exact (by aesop)
  case vc12.hq => exact hq
  case vc13.horder => exact horder
  case vc14.q => exact q
  case vc15.accPoint pref cur suff hsplit b hprev =>
    exact SignedRadix32VariableFoldPoint ρ u2 q pref
  case vc16.hu2 => exact hu2
  case vc17.haccValid => exact (by aesop)
  case vc18.hacc => exact (by aesop)
  case vc19.haccOrder => exact (by aesop)
  case vc20.htableValid => exact (by aesop)
  case vc21.htable => exact (by aesop)
  case vc22.hq => exact hq
  case vc23.horder => exact horder
  case vc24.success pref cur hstep =>
    rename_i table htable suff hsplit acc hprev
    refine ⟨hstep.1, ?_, ?_⟩
    · unfold SignedRadix32VariableFoldPoint at hstep ⊢
      rw [List.foldl_append]
      simpa using hstep.2
    · unfold SignedRadix32VariableFoldPoint
      rw [List.foldl_append]
      exact SignedRadix32VariableStepPoint.order
        (i := suff) pref.2.2 horder
  case vc25.pre =>
    rename_i table htable digit hdigit initial hinitial
    refine ⟨hinitial.1, ?_, ?_⟩
    · unfold SignedRadix32VariableFoldPoint
      simpa using SignedRadix32PointSpec.zsmul hinitial.2
    · unfold SignedRadix32VariableFoldPoint
      exact variableOrderZsmul horder _
  case vc26.post.success =>
    intro hvalid hnormalized _
    exact ⟨hvalid, hnormalized⟩

theorem SignedRadix32VariableFoldPoint_range (u2 : Fn)
    (q : Reference.Point) {count : Nat} (hcount : count ≤ 255) :
    SignedRadix32VariableFoldPoint ρ u2 q (List.range count) =
      signedRadix32BoothCoeff ρ u2 count • q := by
  induction count with
  | zero =>
      simp [SignedRadix32VariableFoldPoint, signedRadix32BoothCoeff]
  | succ count ih =>
      rw [List.range_succ, SignedRadix32VariableFoldPoint,
        List.foldl_append]
      change SignedRadix32VariableStepPoint ρ u2 q count
        (SignedRadix32VariableFoldPoint ρ u2 q (List.range count)) = _
      rw [ih (by omega)]
      unfold SignedRadix32VariableStepPoint
      simp only [signedRadix32BoothCoeff]
      split <;> simp_all [add_zsmul, mul_zsmul]
      all_goals rfl

theorem SignedRadix32VariableFoldPoint_full {u2 : Fn}
    (q : Reference.Point) (hu2 : u2.val.Valid ρ) :
    SignedRadix32VariableFoldPoint ρ u2 q [:255].toList =
      (u2.val.eval ρ).toNat • q := by
  rw [show [:255].toList = List.range 255 by rfl,
    SignedRadix32VariableFoldPoint_range u2 q (by omega),
    signedRadix32BoothCoeff_full hu2]
  rfl

def FixedCombVerificationPoint (rho : WF.Valuation) (u1 u2 : Fn)
    (q : Reference.Point) : Reference.Point :=
  SignedRadix32VariableFoldPoint rho u2 q [:255].toList +
    FixedCombPoint rho u1

theorem FixedCombVerificationPoint.eq_radix32 {u1 u2 : Fn}
    (q : Reference.Point) (hu1 : u1.val.Valid ρ)
    (hu2 : u2.val.Valid ρ) :
    FixedCombVerificationPoint ρ u1 u2 q =
      SignedRadix32FoldPoint ρ u1 u2 q [:255].toList := by
  unfold FixedCombVerificationPoint
  rw [SignedRadix32FoldPoint_full u1 u2 q hu2,
    SignedRadix32VariableFoldPoint_full q hu2,
    FixedCombPoint.eq_scalar hu1]
  abel

theorem fixedCombVerificationPoint_eq_verificationPoint
    {digest : U 256} {sig : Signature}
    {r s sInv z u1Relaxed u2Relaxed u1 u2 : Fn}
    (hdigest : digest.Valid ρ)
    (hr : r.Valid ρ) (hsInv : sInv.Valid ρ)
    (hu1 : u1.Valid ρ) (hu2 : u2.Valid ρ)
    (hrNat : r.evalNat ρ = (sig.r.eval ρ).toNat)
    (hsNat : s.evalNat ρ = (sig.s.eval ρ).toNat)
    (hsMul : (s.evalNat ρ : ZMod scalar.modulus) *
      (sInv.evalNat ρ : ZMod scalar.modulus) = 1)
    (hz : Modular.Lazy.evalElemZMod scalar z ρ =
      Int.castRingHom (ZMod scalar.modulus) (digest.intVal.eval ρ.int))
    (hu1Relaxed : Modular.Lazy.evalElemZMod scalar u1Relaxed ρ =
      Modular.Lazy.evalElemZMod scalar z ρ *
        Modular.Lazy.evalElemZMod scalar sInv ρ)
    (hu2Relaxed : Modular.Lazy.evalElemZMod scalar u2Relaxed ρ =
      Modular.Lazy.evalElemZMod scalar r ρ *
        Modular.Lazy.evalElemZMod scalar sInv ρ)
    (hu1Canonical : Modular.Lazy.evalElemZMod scalar u1 ρ =
      Modular.Lazy.evalElemZMod scalar u1Relaxed ρ)
    (hu2Canonical : Modular.Lazy.evalElemZMod scalar u2 ρ =
      Modular.Lazy.evalElemZMod scalar u2Relaxed ρ)
    (publicKey : Reference.Point) :
    FixedCombVerificationPoint ρ u1 u2 publicKey =
      Reference.verificationPoint (digest.eval ρ).toNat
        (sig.r.eval ρ).toNat (sig.s.eval ρ).toNat publicKey := by
  rw [FixedCombVerificationPoint.eq_radix32 publicKey hu1.1 hu2.1]
  exact signedRadix32FoldPoint_eq_verificationPoint hdigest hr hsInv hu1 hu2
    hrNat hsNat hsMul hz hu1Relaxed hu2Relaxed hu1Canonical hu2Canonical
    publicKey

@[spec] theorem fixedCombVerificationSum_sound
    {input : PreparedVerification} {q : Reference.Point}
    (hu1 : input.u1.val.Valid ρ) (hu2 : input.u2.val.Valid ρ)
    (hQ : Reference.Represents ρ
      (AffineSlope.ofElems input.q.X input.q.Y) q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (fixedCombVerificationSum input)
    ⦃⇓ out => ⌜Reference.NormalizedRep ρ out
      (FixedCombVerificationPoint ρ input.u1 input.u2 q)⌝⦄ := by
  mvcgen [fixedCombVerificationSum, FixedCombVerificationPoint]
  case vc5 => intro _; assumption
  case vc6 => intro h; exact h

@[spec] theorem fixedCombVerificationSum_complete
    {input : PreparedVerification} {q : Reference.Point}
    (hu1 : input.u1.val.Valid ρ) (hu2 : input.u2.val.Valid ρ)
    (hQvalid : input.q.Valid ρ)
    (hQ : Reference.Represents ρ
      (AffineSlope.ofElems input.q.X input.q.Y) q)
    (hq : q ≠ 0) (horder : scalarModulus • q = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (fixedCombVerificationSum input)
    ⦃⇓ out => ⌜out.Valid ρ ∧ Reference.NormalizedRep ρ out
      (FixedCombVerificationPoint ρ input.u1 input.u2 q)⌝⦄ := by
  mvcgen [fixedCombVerificationSum, FixedCombVerificationPoint]
  case vc8 => intros; exact ‹_ ∧ Reference.NormalizedRep _ _ _› |>.1
  case vc9 => intro hvalid _; exact hvalid
  case vc10 => intros; exact ‹_ ∧ Reference.NormalizedRep _ _ _› |>.2
  case vc11 => intro _ hfixed; exact hfixed
  case vc12 =>
    intros
    apply Reference.Aux.no_two_torsion_of_order
    rw [SignedRadix32VariableFoldPoint_full q hu2]
    exact Reference.Aux.order_nsmul horder _

@[spec] theorem fixedCombVerificationX_sound
    {input : PreparedVerification} {q : Reference.Point}
    (hu1 : input.u1.val.Valid ρ) (hu2 : input.u2.val.Valid ρ)
    (hQ : Reference.Represents ρ
      (AffineSlope.ofElems input.q.X input.q.Y) q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (fixedCombVerificationX input)
    ⦃⇓ out => ⌜Reference.NormalizedXRep ρ out
      (FixedCombVerificationPoint ρ input.u1 input.u2 q)⌝⦄ := by
  mvcgen [fixedCombVerificationX, FixedCombVerificationPoint]
  case vc5 => intro _; assumption
  case vc6 => intro h; exact h

@[spec] theorem fixedCombVerificationX_complete
    {input : PreparedVerification} {q : Reference.Point}
    (hu1 : input.u1.val.Valid ρ) (hu2 : input.u2.val.Valid ρ)
    (hQvalid : input.q.Valid ρ)
    (hQ : Reference.Represents ρ
      (AffineSlope.ofElems input.q.X input.q.Y) q)
    (hq : q ≠ 0) (horder : scalarModulus • q = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (fixedCombVerificationX input)
    ⦃⇓ out => ⌜out.Valid ρ ∧ Reference.NormalizedXRep ρ out
      (FixedCombVerificationPoint ρ input.u1 input.u2 q)⌝⦄ := by
  mvcgen [fixedCombVerificationX, FixedCombVerificationPoint]
  case vc8 => intros; exact ‹_ ∧ Reference.NormalizedRep _ _ _› |>.1
  case vc9 => intro hvalid _; exact hvalid
  case vc10 => intros; exact ‹_ ∧ Reference.NormalizedRep _ _ _› |>.2
  case vc11 => intro _ hfixed; exact hfixed
  case vc12 =>
    intros
    apply Reference.Aux.no_two_torsion_of_order
    rw [SignedRadix32VariableFoldPoint_full q hu2]
    exact Reference.Aux.order_nsmul horder _

@[spec] theorem fixedCombVerificationCanonicalX_sound
    {input : PreparedVerification} {q : Reference.Point}
    (hu1 : input.u1.val.Valid ρ) (hu2 : input.u2.val.Valid ρ)
    (hQ : Reference.Represents ρ
      (AffineSlope.ofElems input.q.X input.q.Y) q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (fixedCombVerificationCanonicalX input)
    ⦃⇓ out => ⌜out.X.Valid ρ ∧ Reference.CanonicalXRepresents ρ out
      (FixedCombVerificationPoint ρ input.u1 input.u2 q)⌝⦄ := by
  mvcgen [fixedCombVerificationCanonicalX, FixedCombVerificationPoint]
  case vc5 =>
    intro _
    rename_i variablePart hvariable fixedPart hfixed
    exact hvariable.1
  case vc6 =>
    intro _
    rename_i variablePart hvariable fixedPart hfixed
    exact hfixed.1

@[spec] theorem fixedCombVerificationCanonicalX_complete
    {input : PreparedVerification} {q : Reference.Point}
    (hu1 : input.u1.val.Valid ρ) (hu2 : input.u2.val.Valid ρ)
    (hQvalid : input.q.Valid ρ)
    (hQ : Reference.Represents ρ
      (AffineSlope.ofElems input.q.X input.q.Y) q)
    (hq : q ≠ 0) (horder : scalarModulus • q = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (fixedCombVerificationCanonicalX input)
    ⦃⇓ out => ⌜out.Valid ρ ∧ Reference.CanonicalXRepresents ρ out
      (FixedCombVerificationPoint ρ input.u1 input.u2 q)⌝⦄ := by
  mvcgen [fixedCombVerificationCanonicalX, FixedCombVerificationPoint]
  case vc8 => intros; exact ‹_ ∧ Reference.NormalizedRep _ _ _› |>.1
  case vc9 => intro hvalid _; exact hvalid
  case vc10 => intros; exact ‹_ ∧ Reference.NormalizedRep _ _ _› |>.2
  case vc11 => intro _ hfixed; exact hfixed
  case vc12 =>
    intros
    apply Reference.Aux.no_two_torsion_of_order
    rw [SignedRadix32VariableFoldPoint_full q hu2]
    exact Reference.Aux.order_nsmul horder _

@[spec] theorem fixedCombVerificationDirectTerminal_sound
    {input : PreparedVerification} {q : Reference.Point}
    (hu1 : input.u1.val.Valid ρ) (hu2 : input.u2.val.Valid ρ)
    (hr : input.r.Valid ρ)
    (hQ : Reference.Represents ρ
      (AffineSlope.ofElems input.q.X input.q.Y) q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (fixedCombVerificationDirectTerminal input)
    ⦃⇓ _ => ⌜TerminalPointAcceptanceSpec ρ input.r
      (FixedCombVerificationPoint ρ input.u1 input.u2 q)⌝⦄ := by
  mvcgen [fixedCombVerificationDirectTerminal, FixedCombVerificationPoint]
  case vc5 => intro _; exact hr
  case vc6 => intro _; exact ‹Reference.NormalizedRep _ _ _› |>.1
  case vc7 => intro hfixed; exact hfixed.1

@[spec] theorem fixedCombVerificationDirectTerminal_complete
    {input : PreparedVerification} {q : Reference.Point}
    (hu1 : input.u1.val.Valid ρ) (hu2 : input.u2.val.Valid ρ)
    (hr : input.r.Valid ρ) (hQvalid : input.q.Valid ρ)
    (hQ : Reference.Represents ρ
      (AffineSlope.ofElems input.q.X input.q.Y) q)
    (hq : q ≠ 0) (horder : scalarModulus • q = 0)
    (haccept : TerminalPointAcceptanceSpec ρ input.r
      (FixedCombVerificationPoint ρ input.u1 input.u2 q)) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (fixedCombVerificationDirectTerminal input)
    ⦃⇓ _ => ⌜TerminalPointAcceptanceSpec ρ input.r
      (FixedCombVerificationPoint ρ input.u1 input.u2 q)⌝⦄ := by
  mvcgen -trivial
    [fixedCombVerificationDirectTerminal, FixedCombVerificationPoint]
  case vc1 => exact q
  case vc2.hu2 => exact hu2
  case vc3.hQvalid => exact hQvalid
  case vc4.hQ => exact hQ
  case vc5.hq => exact hq
  case vc6.horder => exact horder
  case vc7.hk => exact hu1
  case vc8 => intros; exact hr
  case vc9 => intros; exact ‹_ ∧ Reference.NormalizedRep _ _ _› |>.1
  case vc10 => intro hvalid _; exact hvalid
  case vc11 => intros; exact ‹_ ∧ Reference.NormalizedRep _ _ _› |>.2
  case vc12 => intro _ hfixed; exact hfixed
  case vc13 =>
    intros
    apply Reference.Aux.no_two_torsion_of_order
    rw [SignedRadix32VariableFoldPoint_full q hu2]
    exact Reference.Aux.order_nsmul horder _
  case vc14 => intros; exact haccept

@[spec] theorem fixedCombVerificationDeltaBlock_sound
    {input : PreparedVerification} {q : Reference.Point}
    (hu1 : input.u1.val.Valid ρ) (hu2 : input.u2.val.Valid ρ)
    (hr : input.r.Valid ρ)
    (hQ : Reference.Represents ρ
      (AffineSlope.ofElems input.q.X input.q.Y) q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (fixedCombVerificationDeltaBlock input)
    ⦃⇓ _ => ⌜TerminalPointAcceptanceSpec ρ input.r
      (FixedCombVerificationPoint ρ input.u1 input.u2 q)⌝⦄ := by
  mvcgen [fixedCombVerificationDeltaBlock, FixedCombVerificationPoint]
  case vc5 => intro _; exact hr
  case vc6 => intro _; exact ‹Reference.NormalizedRep _ _ _› |>.1
  case vc7 => intro hfixed; exact hfixed.1

@[spec] theorem fixedCombVerificationDeltaBlock_complete
    {input : PreparedVerification} {q : Reference.Point}
    (hu1 : input.u1.val.Valid ρ) (hu2 : input.u2.val.Valid ρ)
    (hr : input.r.Valid ρ) (hQvalid : input.q.Valid ρ)
    (hQ : Reference.Represents ρ
      (AffineSlope.ofElems input.q.X input.q.Y) q)
    (hq : q ≠ 0) (horder : scalarModulus • q = 0)
    (haccept : TerminalPointAcceptanceSpec ρ input.r
      (FixedCombVerificationPoint ρ input.u1 input.u2 q)) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (fixedCombVerificationDeltaBlock input)
    ⦃⇓ _ => ⌜TerminalPointAcceptanceSpec ρ input.r
      (FixedCombVerificationPoint ρ input.u1 input.u2 q)⌝⦄ := by
  mvcgen -trivial
    [fixedCombVerificationDeltaBlock, FixedCombVerificationPoint]
  case vc1 => exact q
  case vc2.hu2 => exact hu2
  case vc3.hQvalid => exact hQvalid
  case vc4.hQ => exact hQ
  case vc5.hq => exact hq
  case vc6.horder => exact horder
  case vc7.hk => exact hu1
  case vc8 => intros; exact hr
  case vc9 => intros; exact ‹_ ∧ Reference.NormalizedRep _ _ _› |>.1
  case vc10 => intro hvalid _; exact hvalid
  case vc11 => intros; exact ‹_ ∧ Reference.NormalizedRep _ _ _› |>.2
  case vc12 => intro _ hfixed; exact hfixed
  case vc13 =>
    intros
    apply Reference.Aux.no_two_torsion_of_order
    rw [SignedRadix32VariableFoldPoint_full q hu2]
    exact Reference.Aux.order_nsmul horder _
  case vc14 => intros; exact haccept

end Freigen.F2Z.Examples.EcdsaP256
