import Freigen.F2Z.Examples.EcdsaP256.Lemmas
import Freigen.F2Z.Examples.P256.CanonicalXLemmas

/-!
# Semantics of canonical terminal X acceptance

This module connects the base-field-canonical terminal X coordinate to the
ECDSA scalar comparison.  Since the P-256 base prime is less than twice the
group order, the scalar-reduction quotient is provably one bit.
-/

namespace Freigen.F2Z.Examples.EcdsaP256

open Std.Do
open scoped Std.Do
open Modular
open P256

theorem canonical_scalar_quotient_cases {x r : Nat}
    (hx : x < P256.base.modulus)
    (hr : r < P256.scalar.modulus)
    (hmod : (x : ZMod P256.scalar.modulus) =
      (r : ZMod P256.scalar.modulus)) :
    x = r ∨ x = r + P256.scalar.modulus := by
  have hbase : P256.base.modulus < 2 * P256.scalar.modulus := by
    norm_num [P256.base, P256.baseModulus, P256.scalar,
      P256.scalarModulus]
  have hx2 : x < 2 * P256.scalar.modulus := hx.trans hbase
  have hrem : x % P256.scalar.modulus = r := by
    have hv := congrArg ZMod.val hmod
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hr] using hv
  have hn : 0 < P256.scalar.modulus := by
    norm_num [P256.scalar, P256.scalarModulus]
  have hq : x / P256.scalar.modulus < 2 := by
    rw [Nat.div_lt_iff_lt_mul hn]
    simpa [Nat.mul_comm] using hx2
  have hdecomp := Nat.mod_add_div x P256.scalar.modulus
  interval_cases hquot : x / P256.scalar.modulus
  · left
    simp [hrem] at hdecomp
    omega
  · right
    simp [hrem] at hdecomp
    omega

def CanonicalXAcceptanceSpec (ρ : WF.Valuation) (r : Fn)
    (sum : AffineSlope.CanonicalXPoint) : Prop :=
  sum.infinity.eval ρ.int = 0 ∧
    (sum.X.evalNat ρ : ZMod P256.scalar.modulus) =
      (r.evalNat ρ : ZMod P256.scalar.modulus)

@[spec] theorem checkVerificationCanonicalX_sound
    {r : Fn} {sum : AffineSlope.CanonicalXPoint}
    (hr : r.Valid ρ) (hsum : sum.X.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (checkVerificationCanonicalX r sum)
    ⦃⇓ _ => ⌜CanonicalXAcceptanceSpec ρ r sum⌝⦄ := by
  mvcgen [checkVerificationCanonicalX]
  rename_i hinfinity
  intro bits
  mvcgen
  rename_i quotient hquotient
  intro hassert
  unfold CanonicalXAcceptanceSpec
  have hinfinity0 : sum.infinity.eval ρ.int = 0 := by
    simpa using hinfinity.symm
  constructor
  · exact hinfinity0
  · have heq : sum.X.val.intVal.eval ρ.int =
        r.val.intVal.eval ρ.int +
          scalar.modulus * quotient.intVal.eval ρ.int := by
      simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul,
        LC.eval_ofConst, LC.eval_zero, nsmul_eq_mul, hinfinity0,
        sub_zero, one_mul] at hassert
      omega
    have hcast := congrArg
      (Int.castRingHom (ZMod P256.scalar.modulus)) heq
    rw [← Modular.Elem.evalNat_cast (p := P256.base) hsum,
      ← Modular.Elem.evalNat_cast (p := P256.scalar) hr] at hcast
    simpa using hcast

@[spec] theorem checkVerificationCanonicalX_complete
    {r : Fn} {sum : AffineSlope.CanonicalXPoint}
    (hr : r.Valid ρ) (hsum : sum.Valid ρ)
    (haccept : CanonicalXAcceptanceSpec ρ r sum) :
    ⦃⌜True⌝⦄ Complete.interp ρ (checkVerificationCanonicalX r sum)
    ⦃⇓ _ => ⌜CanonicalXAcceptanceSpec ρ r sum⌝⦄ := by
  mvcgen [checkVerificationCanonicalX]
  constructor
  · simpa using haccept.1.symm
  · mvcgen
    have hxlt := Modular.Elem.evalNat_lt (p := P256.base) hsum.1
    have hrlt := Modular.Elem.evalNat_lt (p := P256.scalar) hr
    have hcases := canonical_scalar_quotient_cases hxlt hrlt haccept.2
    let q : Nat := if sum.X.evalNat ρ = r.evalNat ρ then 0 else 1
    have hqLt : q < 2 := by
      simp only [q]
      split_ifs <;> omega
    have hxEq : sum.X.evalNat ρ =
        r.evalNat ρ + q * P256.scalar.modulus := by
      rcases hcases with h | h
      · simp [q, h]
      · simp [q, h]
    have hquotCalc :
        (sum.X.evalNat ρ - r.evalNat ρ) / P256.scalar.modulus = q := by
      rw [hxEq]
      have hn : 0 < P256.scalar.modulus := by
        norm_num [P256.scalar, P256.scalarModulus]
      rw [Nat.add_sub_cancel_left]
      simpa [Nat.mul_comm] using Nat.mul_div_right q hn
    let bits : Vector Bool 1 := Vector.ofFn fun i => q.testBit i.val
    refine ⟨bits, ?_, ?_⟩
    · have hxRaw := Modular.Elem.evalNat_cast (p := P256.base) hsum.1
      have hrRaw := Modular.Elem.evalNat_cast (p := P256.scalar) hr
      simp [WF.interpHint, WF.evalArgs, terminalScalarQuotientHint,
        bits, ← hxRaw, ← hrRaw, hquotCalc]
    · mvcgen
      rename_i quotient hquotient
      have hquotientValue : quotient.intVal.eval ρ.int = q := by
        rw [U.Rel.intVal hquotient]
        have hqInt := congrArg Int.ofNat
          (Modular.Aux.constWord_eval_toNat (n := 1) q hqLt ρ)
        simpa [bits, Function.comp_def] using hqInt
      have hxRaw := Modular.Elem.evalNat_cast (p := P256.base) hsum.1
      have hrRaw := Modular.Elem.evalNat_cast (p := P256.scalar) hr
      have heqInt : sum.X.val.intVal.eval ρ.int =
          r.val.intVal.eval ρ.int +
            P256.scalar.modulus * q := by
        calc
          _ = (sum.X.evalNat ρ : Int) := hxRaw.symm
          _ = (r.evalNat ρ + q * P256.scalar.modulus : Nat) := by
            exact_mod_cast hxEq
          _ = r.val.intVal.eval ρ.int +
                P256.scalar.modulus * q := by
            push_cast
            rw [hrRaw]
            ring
      constructor
      · simp only [LC.eval_sub, LC.eval_add, LC.eval_nsmul,
          LC.eval_ofConst, LC.eval_zero, nsmul_eq_mul,
          haccept.1, sub_zero, one_mul, hquotientValue]
        omega
      · exact haccept

end Freigen.F2Z.Examples.EcdsaP256
