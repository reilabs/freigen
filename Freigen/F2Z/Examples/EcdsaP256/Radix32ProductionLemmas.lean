import Freigen.F2Z.Examples.EcdsaP256.FixedBaseCombVariableLemmas
import Freigen.F2Z.Examples.EcdsaP256.Radix32Production
import Freigen.F2Z.Examples.EcdsaP256.CanonicalXLemmas

namespace Freigen.F2Z.Examples.EcdsaP256

open Std.Do
open scoped Std.Do
open Modular
open P256

set_option maxRecDepth 10000

private theorem point_ne_zero_of_hasCoordinates {q : Reference.Point}
    {x y : Reference.Field} (h : Reference.HasCoordinates q x y) : q ≠ 0 := by
  rcases q with _ | ⟨qx, qy, hcurve⟩
  · simp [Reference.HasCoordinates, P256.Reference.coordinates] at h
  · simp

theorem terminalPointAcceptance_of_canonical
    {r : Fn} {sum : AffineSlope.CanonicalXPoint}
    {p : Reference.Point}
    (hsumValid : sum.X.Valid ρ)
    (hsum : Reference.CanonicalXRepresents ρ sum p)
    (haccept : CanonicalXAcceptanceSpec ρ r sum) :
    TerminalPointAcceptanceSpec ρ r p := by
  rcases p with _ | ⟨x, y, hcurve⟩
  · have hinfinity := P256.Reference.XRepresents.zero hsum
    change sum.infinity.eval ρ.int = 1 at hinfinity
    have hfinite := haccept.1
    omega
  · have hsome := P256.Reference.XRepresents.some hsum
    have hxPoint : (sum.X.evalNat ρ : P256.Reference.Field) = x := by
      have hxRaw := hsome.2
      change Int.castRingHom P256.Reference.Field
        (sum.X.val.intVal.eval ρ.int) = x at hxRaw
      rw [← Modular.Elem.evalNat_cast P256.base hsumValid] at hxRaw
      simpa using hxRaw
    have hxVal := congrArg ZMod.val hxPoint
    rw [ZMod.val_cast_of_lt
      (Modular.Elem.evalNat_lt P256.base hsumValid)] at hxVal
    simp only [TerminalPointAcceptanceSpec]
    rw [← hxVal]
    exact haccept.2

theorem canonical_acceptance_of_terminalPoint
    {r : Fn} {sum : AffineSlope.CanonicalXPoint}
    {p : Reference.Point}
    (hsumValid : sum.X.Valid ρ)
    (hsum : Reference.CanonicalXRepresents ρ sum p)
    (haccept : TerminalPointAcceptanceSpec ρ r p) :
    CanonicalXAcceptanceSpec ρ r sum := by
  rcases p with _ | ⟨x, y, hcurve⟩
  · exact haccept.elim
  · have hsome := P256.Reference.XRepresents.some hsum
    have hxPoint : (sum.X.evalNat ρ : P256.Reference.Field) = x := by
      have hxRaw := hsome.2
      change Int.castRingHom P256.Reference.Field
        (sum.X.val.intVal.eval ρ.int) = x at hxRaw
      rw [← Modular.Elem.evalNat_cast P256.base hsumValid] at hxRaw
      simpa using hxRaw
    have hxVal := congrArg ZMod.val hxPoint
    rw [ZMod.val_cast_of_lt
      (Modular.Elem.evalNat_lt P256.base hsumValid)] at hxVal
    constructor
    · change sum.toXPoint.infinity.eval ρ.int = 0
      exact hsome.1
    · simp only [TerminalPointAcceptanceSpec] at haccept
      rw [hxVal]
      exact haccept

theorem terminalPointAcceptance_of_verifies
    {digest rNat sNat : Nat} {r : Fn} {publicKey : Reference.Point}
    (hrNat : r.evalNat ρ = rNat)
    (hverifies : Reference.Verifies digest rNat sNat publicKey) :
    TerminalPointAcceptanceSpec ρ r
      (Reference.verificationPoint digest rNat sNat publicKey) := by
  rcases hverifies with ⟨_, _, _, _, _, hfinal⟩
  rcases hpoint : Reference.verificationPoint digest rNat sNat publicKey with
    _ | ⟨x, y, hcurve⟩
  · rw [hpoint] at hfinal
    exact hfinal.elim
  · simp only [TerminalPointAcceptanceSpec]
    rw [hpoint] at hfinal
    rw [hrNat]
    rw [← hfinal]
    exact (ZMod.natCast_mod x.val P256.scalar.modulus).symm

@[spec] theorem finishVerification_sound
    {input : PreparedVerification} {q : Reference.Point}
    (hu1 : input.u1.val.Valid ρ) (hu2 : input.u2.val.Valid ρ)
    (hr : input.r.Valid ρ)
    (hQ : Reference.Represents ρ
      (AffineSlope.ofElems input.q.X input.q.Y) q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (finishVerification input)
    ⦃⇓ _ => ⌜TerminalPointAcceptanceSpec ρ input.r
      (FixedCombVerificationPoint ρ input.u1 input.u2 q)⌝⦄ := by
  simpa only [finishVerification, computeVerificationDeltaBlock] using
    (fixedCombVerificationDeltaBlock_sound (input := input) (q := q)
      hu1 hu2 hr hQ)

@[spec] theorem finishVerification_complete
    {input : PreparedVerification} {q : Reference.Point}
    (hu1 : input.u1.val.Valid ρ) (hu2 : input.u2.val.Valid ρ)
    (hr : input.r.Valid ρ) (hQvalid : input.q.Valid ρ)
    (hQ : Reference.Represents ρ
      (AffineSlope.ofElems input.q.X input.q.Y) q)
    (hq : q ≠ 0) (horder : scalarModulus • q = 0)
    (haccept : TerminalPointAcceptanceSpec ρ input.r
      (FixedCombVerificationPoint ρ input.u1 input.u2 q)) :
    ⦃⌜True⌝⦄ Complete.interp ρ (finishVerification input)
    ⦃⇓ _ => ⌜TerminalPointAcceptanceSpec ρ input.r
      (FixedCombVerificationPoint ρ input.u1 input.u2 q)⌝⦄ := by
  simpa only [finishVerification, computeVerificationDeltaBlock] using
    (fixedCombVerificationDeltaBlock_complete (input := input) (q := q)
      hu1 hu2 hr hQvalid hQ hq horder haccept)

theorem verifyDigest_complete_radix32_aux {digest : U 256} {key : PublicKey}
    {sig : Signature} {aux : Aux} {publicKey : Reference.Point}
    (hdigest : digest.Valid ρ)
    (hkeyX : key.x.Valid ρ) (hkeyY : key.y.Valid ρ)
    (hr : sig.r.Valid ρ) (hs : sig.s.Valid ρ)
    (hrInv : aux.rInv.Valid ρ) (hsInv : aux.sInv.Valid ρ)
    (hkeyXlt : key.x.intVal.eval ρ.int < P256.base.modulus)
    (hkeyYlt : key.y.intVal.eval ρ.int < P256.base.modulus)
    (hrlt : sig.r.intVal.eval ρ.int < P256.scalar.modulus)
    (hslt : sig.s.intVal.eval ρ.int < P256.scalar.modulus)
    (hrInvlt : aux.rInv.intVal.eval ρ.int < P256.scalar.modulus)
    (hsInvlt : aux.sInv.intVal.eval ρ.int < P256.scalar.modulus)
    (hcoords : Reference.HasCoordinates publicKey
      (Int.castRingHom P256.Reference.Field (key.x.intVal.eval ρ.int))
      (Int.castRingHom P256.Reference.Field (key.y.intVal.eval ρ.int)))
    (horder : P256.scalarModulus • publicKey = 0)
    (hrInvMul : ((sig.r.eval ρ).toNat : Reference.Scalar) *
      ((aux.rInv.eval ρ).toNat : Reference.Scalar) = 1)
    (hsInvMul : ((sig.s.eval ρ).toNat : Reference.Scalar) *
      ((aux.sInv.eval ρ).toNat : Reference.Scalar) = 1)
    (hverifies : Reference.Verifies (digest.eval ρ).toNat
      (sig.r.eval ρ).toNat (sig.s.eval ρ).toNat publicKey) :
    ⦃⌜True⌝⦄ Complete.interp ρ (verifyDigest digest key sig aux)
    ⦃⇓ _ => ⌜Reference.Verifies (digest.eval ρ).toNat
      (sig.r.eval ρ).toNat (sig.s.eval ρ).toNat publicKey⌝⦄ := by
  mvcgen -trivial [verifyDigest, canonicalizeInput, canonicalizeKey,
    canonicalizeSignature, canonicalizeAux, prepareVerification,
    validateCanonicalInput, deriveScalars, deriveRelaxedScalars,
    multiplyScalars, canonicalizeScalars]
  case vc1.hx => exact hkeyX
  case vc2.hlt => exact hkeyXlt
  case vc3.hx => exact hkeyY
  case vc4.hlt => exact hkeyYlt
  case vc5.hx => exact hr
  case vc6.hlt => exact hrlt
  case vc7.hx => exact hs
  case vc8.hlt => exact hslt
  case vc9.hx => exact hrInv
  case vc10.hlt => exact hrInvlt
  case vc11.hx => exact hsInv
  case vc12.hlt => exact hsInvlt
  case vc15.hcurve =>
    rename_i qx hqx qy hqy r hr' s hs' rInv hrInv' sInv hsInv'
    apply onCurveZModSpec_of_hasCoordinates (publicKey := publicKey)
    have hxEval := congrArg (fun u : U 256 => u.intVal.eval ρ.int) hqx.2
    have hyEval := congrArg (fun u : U 256 => u.intVal.eval ρ.int) hqy.2
    rw [hxEval, hyEval]
    exact hcoords
  case vc13.hx => aesop
  case vc14.hy => aesop
  case vc16.hx => exact Modular.Lazy.ofElem_valid P256.scalar (by aesop)
  case vc17.hy => exact Modular.Lazy.ofElem_valid P256.scalar (by aesop)
  case vc18.htarget =>
    exact Modular.Lazy.ofElem_valid P256.scalar fnOne_valid
  case vc19.hspec =>
    exact assertMulEqSpec_of_u_mul (by aesop) (by aesop)
      (by aesop) (by aesop) hr hrInv hrInvMul
  case vc20.hbound =>
    norm_num [Modular.Lazy.ofElem, Modular.Lazy.quotientExtraBits]
  case vc21.hx0 => exact U.intVal_nonneg digest hdigest
  case vc22.hxBound =>
    exact (U.intVal_lt_two_pow digest hdigest).trans (by
      norm_num [P256.scalar, P256.scalarModulus])
  case vc23.hx => aesop
  case vc24.hy => aesop
  case vc25.hx => aesop
  case vc26.hy => aesop
  case vc27.hx => exact Modular.Lazy.ofElem_valid P256.scalar (by aesop)
  case vc28.hbound =>
    norm_num [Modular.Lazy.ofElem, Modular.Lazy.quotientExtraBits]
  case vc29.hx => exact Modular.Lazy.ofElem_valid P256.scalar (by aesop)
  case vc30.hbound =>
    norm_num [Modular.Lazy.ofElem, Modular.Lazy.quotientExtraBits]
  case vc31.q => exact publicKey
  case vc32.hu1 => simp_all [Modular.Elem.Valid]
  case vc33.hu2 => simp_all [Modular.Elem.Valid]
  case vc34.hr => simp_all [Modular.Elem.Valid]
  case vc35.hQvalid =>
    exact ⟨(by aesop), (by aesop), baseOne_valid⟩
  case vc36.hQ =>
    rename_i qx hqx qy hqy r hr' s hs' rInv hrInv' sInv hsInv'
      _ _ _ _ _ _ z hz u1Relaxed hu1Relaxed u2Relaxed hu2Relaxed
      u1 hu1 u2 hu2
    apply ofElems_represents_of_hasCoordinates (publicKey := publicKey)
    have hxEval := congrArg (fun u : U 256 => u.intVal.eval ρ.int) hqx.2
    have hyEval := congrArg (fun u : U 256 => u.intVal.eval ρ.int) hqy.2
    rw [hxEval, hyEval]
    exact hcoords
  case vc37.hq => exact point_ne_zero_of_hasCoordinates hcoords
  case vc38.horder => exact horder
  case vc39.haccept =>
    rename_i qx hqx qy hqy r hr' s hs' rInv hrInv' sInv hsInv'
      _ hcurve _ hrMul _ hsMul z hz u1Relaxed hu1Relaxed
      u2Relaxed hu2Relaxed u1 hu1 u2 hu2
    have hrNat : r.evalNat ρ = (sig.r.eval ρ).toNat :=
      elem_evalNat_eq_u_eval hr'.1 hr'.2 hr
    have hsNat : s.evalNat ρ = (sig.s.eval ρ).toNat :=
      elem_evalNat_eq_u_eval hs'.1 hs'.2 hs
    have hsInvNat : sInv.evalNat ρ = (aux.sInv.eval ρ).toNat :=
      elem_evalNat_eq_u_eval hsInv'.1 hsInv'.2 hsInv
    have hsMul' : (s.evalNat ρ : ZMod P256.scalar.modulus) *
        (sInv.evalNat ρ : ZMod P256.scalar.modulus) = 1 := by
      rw [hsNat, hsInvNat]
      change ((sig.s.eval ρ).toNat : ZMod P256.scalarModulus) *
        ((aux.sInv.eval ρ).toNat : ZMod P256.scalarModulus) = 1
      change ((sig.s.eval ρ).toNat : ZMod P256.scalarModulus) *
        ((aux.sInv.eval ρ).toNat : ZMod P256.scalarModulus) = 1 at hsInvMul
      exact hsInvMul
    have hsumPoint := fixedCombVerificationPoint_eq_verificationPoint hdigest hr'.1
      hsInv'.1 hu1.1 hu2.1 hrNat hsNat hsMul' hz.2 hu1Relaxed.2
      hu2Relaxed.2 hu1.2 hu2.2 publicKey
    rw [hsumPoint]
    exact terminalPointAcceptance_of_verifies hrNat hverifies
  case vc40.success.success.success.success => exact fun _ => hverifies
  case vc41 =>
    intro _
    exact Modular.Lazy.ofElem_valid P256.scalar (by aesop)
  case vc42 =>
    intro _
    exact Modular.Lazy.ofElem_valid P256.scalar (by aesop)
  case vc43 =>
    intro _
    exact Modular.Lazy.ofElem_valid P256.scalar fnOne_valid
  case vc44 =>
    intro _
    exact assertMulEqSpec_of_u_mul (by aesop) (by aesop)
      (by aesop) (by aesop) hs hsInv hsInvMul
  case vc45 =>
    intro _
    norm_num [Modular.Lazy.ofElem, Modular.Lazy.quotientExtraBits]

theorem verifyDigest_sound_radix32_aux {digest : U 256} {key : PublicKey}
    {sig : Signature} {aux : Aux}
    (hdigest : digest.Valid ρ)
    (hkeyX : key.x.Valid ρ) (hkeyY : key.y.Valid ρ)
    (hr : sig.r.Valid ρ) (hs : sig.s.Valid ρ)
    (hrInv : aux.rInv.Valid ρ) (hsInv : aux.sInv.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (verifyDigest digest key sig aux)
    ⦃⇓ _ => ⌜∃ publicKey : Reference.Point,
      Reference.HasCoordinates publicKey
        (Int.castRingHom P256.Reference.Field
          (key.x.intVal.eval ρ.int))
        (Int.castRingHom P256.Reference.Field
          (key.y.intVal.eval ρ.int)) ∧
      Reference.Verifies (digest.eval ρ).toNat
        (sig.r.eval ρ).toNat (sig.s.eval ρ).toNat publicKey⌝⦄ := by
  mvcgen [verifyDigest, canonicalizeInput, canonicalizeKey,
    canonicalizeSignature, canonicalizeAux, prepareVerification,
    validateCanonicalInput, deriveScalars, deriveRelaxedScalars,
    multiplyScalars, canonicalizeScalars]
  case vc7.q =>
    exact P256.Reference.pointOfCircuit ρ _ _ (by assumption)
  case vc8.hu1 => simp_all [Modular.Elem.Valid]
  case vc9.hu2 => simp_all [Modular.Elem.Valid]
  case vc10.hr =>
    rename_i qx hqx qy hqy r hr' s hs' rInv hrInv' sInv hsInv'
      _ _ _ _ _ _ z hz u1Relaxed hu1Relaxed u2Relaxed hu2Relaxed
      u1 hu1 u2 hu2
    exact hr'.1
  case vc11.hQ =>
    exact P256.Reference.Aux.ofElems_represents_pointOfCircuit (by assumption)
  case vc12.success.success.success.success =>
    rename_i qx hqx qy hqy r hr' s hs' rInv hrInv' sInv hsInv'
      _ hcurve _ hrMul _ hsMul z hz u1Relaxed hu1Relaxed
      u2Relaxed hu2Relaxed u1 hu1 u2 hu2 haccept
    let publicKey := P256.Reference.pointOfCircuit ρ qx qy hcurve
    have hrMul' : (r.evalNat ρ : ZMod P256.scalar.modulus) *
        (rInv.evalNat ρ : ZMod P256.scalar.modulus) = 1 := by
      unfold Modular.Lazy.AssertMulEqZModSpec at hrMul
      simp only [Modular.Lazy.evalZMod_ofElem] at hrMul
      rw [elem_evalZMod_eq_cast hr'.1, elem_evalZMod_eq_cast hrInv'.1,
        elem_evalZMod_eq_cast fnOne_valid, fnOne_evalNat] at hrMul
      simpa using hrMul
    have hsMul' : (s.evalNat ρ : ZMod P256.scalar.modulus) *
        (sInv.evalNat ρ : ZMod P256.scalar.modulus) = 1 := by
      unfold Modular.Lazy.AssertMulEqZModSpec at hsMul
      simp only [Modular.Lazy.evalZMod_ofElem] at hsMul
      rw [elem_evalZMod_eq_cast hs'.1, elem_evalZMod_eq_cast hsInv'.1,
        elem_evalZMod_eq_cast fnOne_valid, fnOne_evalNat] at hsMul
      simpa using hsMul
    have hrFieldNe : (r.evalNat ρ : ZMod P256.scalar.modulus) ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hrMul'
      exact zero_ne_one hrMul'
    have hsFieldNe : (s.evalNat ρ : ZMod P256.scalar.modulus) ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hsMul'
      exact zero_ne_one hsMul'
    have hrPos : 0 < r.evalNat ρ := Nat.pos_of_ne_zero fun hzero =>
      hrFieldNe (by simp [hzero])
    have hsPos : 0 < s.evalNat ρ := Nat.pos_of_ne_zero fun hzero =>
      hsFieldNe (by simp [hzero])
    have hrNat := elem_evalNat_eq_u_eval hr'.1 hr'.2 hr
    have hsNat := elem_evalNat_eq_u_eval hs'.1 hs'.2 hs
    have hsumPoint := fixedCombVerificationPoint_eq_verificationPoint hdigest hr'.1
      hsInv'.1 hu1.1 hu2.1 hrNat hsNat hsMul' hz.2 hu1Relaxed.2
      hu2Relaxed.2 hu1.2 hu2.2 publicKey
    intro haccept
    rw [hsumPoint] at haccept
    rcases hpoint : Reference.verificationPoint (digest.eval ρ).toNat
        (sig.r.eval ρ).toNat (sig.s.eval ρ).toNat publicKey with
      _ | ⟨pointX, pointY, hpointCurve⟩
    · rw [hpoint] at haccept
      exact haccept.elim
    · simp only [TerminalPointAcceptanceSpec] at haccept
      rw [hpoint] at haccept
      have hxModVal := congrArg ZMod.val haccept
      rw [ZMod.val_natCast, ZMod.val_natCast, hrNat] at hxModVal
      have hrInputLt : (sig.r.eval ρ).toNat < P256.scalar.modulus := by
        rw [← hrNat]
        exact Modular.Elem.evalNat_lt P256.scalar hr'.1
      rw [Nat.mod_eq_of_lt hrInputLt] at hxModVal
      refine ⟨publicKey, ?_, ?_⟩
      · unfold publicKey Reference.HasCoordinates
        simp only [P256.Reference.pointOfCircuit,
          WeierstrassCurve.Affine.Point.mk]
        simp [P256.Reference.coordinates, hqx.2, hqy.2]
      · unfold Reference.Verifies
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · unfold publicKey P256.Reference.pointOfCircuit
          exact WeierstrassCurve.Affine.Point.some_ne_zero _
        · simpa [hrNat] using hrPos
        · simpa [P256.scalar_modulus_eq, hrNat] using
            (Modular.Elem.evalNat_lt P256.scalar hr'.1)
        · simpa [hsNat] using hsPos
        · simpa [P256.scalar_modulus_eq, hsNat] using
            (Modular.Elem.evalNat_lt P256.scalar hs'.1)
        · rw [hpoint]
          simpa [P256.scalar_modulus_eq] using hxModVal

theorem verifyDigestFromBits_sound_radix32_aux
    (inputs : Vector Bool verifyDigestInputBits) :
    ⦃⌜∀ i : Fin verifyDigestInputBits, ρ.bool i.val = inputs[i]⌝⦄
      Sound.interp ρ
        (verifyDigestFromBits (Vector.ofFn fun i => ({i.val} : LC Bool)))
    ⦃⇓ _ => ⌜∃ publicKey : Reference.Point,
      Reference.HasCoordinates publicKey
        (verifyDigestInputValue inputs 1).toNat
        (verifyDigestInputValue inputs 2).toNat ∧
      Reference.Verifies (verifyDigestInputValue inputs 0).toNat
        (verifyDigestInputValue inputs 3).toNat
        (verifyDigestInputValue inputs 4).toNat publicKey⌝⦄ := by
  mvcgen -trivial [-Sound.interp_mapM, U.mapM_fromWord_sound,
    verifyDigestFromBits]
  case vc1 =>
    rename_i hbits values
    intro hvalues
    have hvalue (slot : Nat) (hslot : slot < 7) :
        (values[slot]'hslot).eval ρ =
          verifyDigestInputValue inputs ⟨slot, hslot⟩ := by
      have hall := hvalues.eval_eq.trans
        (verifyDigestInputWords_eval_inputs inputs hbits)
      have h := congrArg
        (fun xs : Vector (BitVec 256) 7 => xs[slot]'hslot) hall
      simpa only [Vector.getElem_map, Vector.getElem_ofFn] using h
    have hqxInt : values[1].intVal.eval ρ.int =
        ((verifyDigestInputValue inputs 1).toNat : Int) :=
      (U.intVal_eval_eq_eval_toNat values[1] (hvalues 1).1).trans
        (congrArg (fun x : BitVec 256 => (x.toNat : Int))
          (hvalue 1 (by omega)))
    have hqyInt : values[2].intVal.eval ρ.int =
        ((verifyDigestInputValue inputs 2).toNat : Int) :=
      (U.intVal_eval_eq_eval_toNat values[2] (hvalues 2).1).trans
        (congrArg (fun x : BitVec 256 => (x.toNat : Int))
          (hvalue 2 (by omega)))
    have hqxField :
        (Int.castRingHom P256.Reference.Field) (values[1].intVal.eval ρ.int) =
          ((verifyDigestInputValue inputs 1).toNat : P256.Reference.Field) := by
      rw [hqxInt]
      simp
    have hqyField :
        (Int.castRingHom P256.Reference.Field) (values[2].intVal.eval ρ.int) =
          ((verifyDigestInputValue inputs 2).toNat : P256.Reference.Field) := by
      rw [hqyInt]
      simp
    have ht := verifyDigest_sound_radix32_aux
      (digest := values[0]) (key := ⟨values[1], values[2]⟩)
      (sig := ⟨values[3], values[4]⟩)
      (aux := ⟨values[5], values[6]⟩)
      (hvalues 0).1 (hvalues 1).1 (hvalues 2).1
      (hvalues 3).1 (hvalues 4).1 (hvalues 5).1 (hvalues 6).1
    have htSpec :
        ⦃⌜True⌝⦄ Sound.interp ρ
          (verifyDigest values[0] ⟨values[1], values[2]⟩
            ⟨values[3], values[4]⟩ ⟨values[5], values[6]⟩)
        ⦃⇓ _ => ⌜∃ publicKey : Reference.Point,
          Reference.HasCoordinates publicKey
            (verifyDigestInputValue inputs 1).toNat
            (verifyDigestInputValue inputs 2).toNat ∧
          Reference.Verifies (verifyDigestInputValue inputs 0).toNat
            (verifyDigestInputValue inputs 3).toNat
            (verifyDigestInputValue inputs 4).toNat publicKey⌝⦄ := by
      apply Triple.iff_conseq.mp ht (by simp)
      simp only [PostCond.entails, SPred.entails_nil]
      refine ⟨?_, ExceptConds.entails.refl _⟩
      intro _ hex
      rcases hex with ⟨publicKey, hcoords, hverifies⟩
      refine ⟨publicKey, ?_, ?_⟩
      · rw [hqxField, hqyField] at hcoords
        exact hcoords
      · convert hverifies using 1
        · exact (congrArg BitVec.toNat (hvalue 0 (by omega))).symm
        · exact (congrArg BitVec.toNat (hvalue 3 (by omega))).symm
        · exact (congrArg BitVec.toNat (hvalue 4 (by omega))).symm
    rw [Triple.iff] at htSpec
    exact htSpec trivial

theorem verifyDigestFromBits_complete_radix32_aux
    (inputs : Vector Bool verifyDigestInputBits)
    (publicKey : Reference.Point)
    (hbits : ∀ i : Fin verifyDigestInputBits, ρ.bool i.val = inputs[i])
    (hkeyXlt : (verifyDigestInputValue inputs 1).toNat < P256.base.modulus)
    (hkeyYlt : (verifyDigestInputValue inputs 2).toNat < P256.base.modulus)
    (hrInvlt : (verifyDigestInputValue inputs 5).toNat < P256.scalar.modulus)
    (hsInvlt : (verifyDigestInputValue inputs 6).toNat < P256.scalar.modulus)
    (hcoords : Reference.HasCoordinates publicKey
      (verifyDigestInputValue inputs 1).toNat
      (verifyDigestInputValue inputs 2).toNat)
    (horder : P256.scalarModulus • publicKey = 0)
    (hrInvMul :
      ((verifyDigestInputValue inputs 3).toNat : Reference.Scalar) *
        ((verifyDigestInputValue inputs 5).toNat : Reference.Scalar) = 1)
    (hsInvMul :
      ((verifyDigestInputValue inputs 4).toNat : Reference.Scalar) *
        ((verifyDigestInputValue inputs 6).toNat : Reference.Scalar) = 1)
    (hverifies : Reference.Verifies
      (verifyDigestInputValue inputs 0).toNat
      (verifyDigestInputValue inputs 3).toNat
      (verifyDigestInputValue inputs 4).toNat publicKey) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (verifyDigestFromBits (Vector.ofFn fun i => ({i.val} : LC Bool)))
    ⦃⇓ _ => ⌜True⌝⦄ := by
  mvcgen -trivial [-Complete.interp_mapM, U.mapM_fromWord_complete,
    verifyDigestFromBits]
  case vc1 =>
    rename_i values
    intro hvalues
    have hvalue (slot : Nat) (hslot : slot < 7) :
        (values[slot]'hslot).eval ρ =
          verifyDigestInputValue inputs ⟨slot, hslot⟩ := by
      have hall := hvalues.eval_eq.trans
        (verifyDigestInputWords_eval_inputs inputs hbits)
      have h := congrArg
        (fun xs : Vector (BitVec 256) 7 => xs[slot]'hslot) hall
      simpa only [Vector.getElem_map, Vector.getElem_ofFn] using h
    have hqxInt : values[1].intVal.eval ρ.int =
        ((verifyDigestInputValue inputs 1).toNat : Int) := by
      exact (U.intVal_eval_eq_eval_toNat values[1] (hvalues 1).1).trans
        (congrArg (fun x : BitVec 256 => (x.toNat : Int))
          (hvalue 1 (by omega)))
    have hqyInt : values[2].intVal.eval ρ.int =
        ((verifyDigestInputValue inputs 2).toNat : Int) := by
      exact (U.intVal_eval_eq_eval_toNat values[2] (hvalues 2).1).trans
        (congrArg (fun x : BitVec 256 => (x.toNat : Int))
          (hvalue 2 (by omega)))
    have hrInt : values[3].intVal.eval ρ.int =
        ((verifyDigestInputValue inputs 3).toNat : Int) := by
      exact (U.intVal_eval_eq_eval_toNat values[3] (hvalues 3).1).trans
        (congrArg (fun x : BitVec 256 => (x.toNat : Int))
          (hvalue 3 (by omega)))
    have hsInt : values[4].intVal.eval ρ.int =
        ((verifyDigestInputValue inputs 4).toNat : Int) := by
      exact (U.intVal_eval_eq_eval_toNat values[4] (hvalues 4).1).trans
        (congrArg (fun x : BitVec 256 => (x.toNat : Int))
          (hvalue 4 (by omega)))
    have hrInvInt : values[5].intVal.eval ρ.int =
        ((verifyDigestInputValue inputs 5).toNat : Int) := by
      exact (U.intVal_eval_eq_eval_toNat values[5] (hvalues 5).1).trans
        (congrArg (fun x : BitVec 256 => (x.toNat : Int))
          (hvalue 5 (by omega)))
    have hsInvInt : values[6].intVal.eval ρ.int =
        ((verifyDigestInputValue inputs 6).toNat : Int) := by
      exact (U.intVal_eval_eq_eval_toNat values[6] (hvalues 6).1).trans
        (congrArg (fun x : BitVec 256 => (x.toNat : Int))
          (hvalue 6 (by omega)))
    have hdigestNat := congrArg BitVec.toNat (hvalue 0 (by omega))
    have hrNat := congrArg BitVec.toNat (hvalue 3 (by omega))
    have hsNat := congrArg BitVec.toNat (hvalue 4 (by omega))
    have hrInvNat := congrArg BitVec.toNat (hvalue 5 (by omega))
    have hsInvNat := congrArg BitVec.toNat (hvalue 6 (by omega))
    have ht := verifyDigest_complete_radix32_aux
      (digest := values[0]) (key := ⟨values[1], values[2]⟩)
      (sig := ⟨values[3], values[4]⟩)
      (aux := ⟨values[5], values[6]⟩) (publicKey := publicKey)
      (hvalues 0).1 (hvalues 1).1 (hvalues 2).1 (hvalues 3).1
      (hvalues 4).1 (hvalues 5).1 (hvalues 6).1
      (by rw [hqxInt]; exact_mod_cast hkeyXlt)
      (by rw [hqyInt]; exact_mod_cast hkeyYlt)
      (by rw [hrInt]; exact_mod_cast hverifies.2.2.1)
      (by rw [hsInt]; exact_mod_cast hverifies.2.2.2.2.1)
      (by rw [hrInvInt]; exact_mod_cast hrInvlt)
      (by rw [hsInvInt]; exact_mod_cast hsInvlt)
      (by rw [hqxInt, hqyInt]; simpa using hcoords)
      horder
      (by
        change ((values[3].eval ρ).toNat : Reference.Scalar) *
          ((values[5].eval ρ).toNat : Reference.Scalar) = 1
        calc
          _ = ((verifyDigestInputValue inputs 3).toNat : Reference.Scalar) *
              ((verifyDigestInputValue inputs 5).toNat : Reference.Scalar) :=
            congrArg₂ (fun x y : Reference.Scalar => x * y)
              (congrArg (fun n : Nat => (n : Reference.Scalar)) hrNat)
              (congrArg (fun n : Nat => (n : Reference.Scalar)) hrInvNat)
          _ = 1 := hrInvMul)
      (by
        change ((values[4].eval ρ).toNat : Reference.Scalar) *
          ((values[6].eval ρ).toNat : Reference.Scalar) = 1
        calc
          _ = ((verifyDigestInputValue inputs 4).toNat : Reference.Scalar) *
              ((verifyDigestInputValue inputs 6).toNat : Reference.Scalar) :=
            congrArg₂ (fun x y : Reference.Scalar => x * y)
              (congrArg (fun n : Nat => (n : Reference.Scalar)) hsNat)
              (congrArg (fun n : Nat => (n : Reference.Scalar)) hsInvNat)
          _ = 1 := hsInvMul)
      (by
        change Reference.Verifies (values[0].eval ρ).toNat
          (values[3].eval ρ).toNat (values[4].eval ρ).toNat publicKey
        convert hverifies using 1
        · exact hdigestNat
        · exact hrNat
        · exact hsNat)
    have htTrue :
        ⦃⌜True⌝⦄ Complete.interp ρ
          (verifyDigest values[0] ⟨values[1], values[2]⟩
            ⟨values[3], values[4]⟩ ⟨values[5], values[6]⟩)
        ⦃⇓ _ => ⌜True⌝⦄ := by
      apply Triple.iff_conseq.mp ht (by simp)
      simp only [PostCond.entails, SPred.entails_nil]
      exact ⟨fun _ _ => True.intro, ExceptConds.entails.refl _⟩
    rw [Triple.iff] at htTrue
    exact htTrue trivial

end Freigen.F2Z.Examples.EcdsaP256
