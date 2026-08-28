import Freigen.F2Z.Examples.EcdsaP256.Impl
import Freigen.F2Z.Examples.P256

/-!
# Auxiliary ECDSA-P256 reference lemmas

Small scalar-field facts used by the public soundness and completeness
statements live here, away from both implementation and theorem boundary.
-/

namespace Freigen.F2Z.Examples.EcdsaP256.Reference.Aux

open Freigen.F2Z.Examples.P256
open Freigen.F2Z.Examples.EcdsaP256.Reference

theorem inverse_eq_of_mul_eq_one {x inverse : Scalar}
    (hx : x ≠ 0) (h : x * inverse = 1) : inverse = x⁻¹ := by
  calc
    inverse = 1 * inverse := by simp
    _ = (x⁻¹ * x) * inverse := by rw [inv_mul_cancel₀ hx]
    _ = x⁻¹ * (x * inverse) := by rw [mul_assoc]
    _ = x⁻¹ := by rw [h]; simp

theorem generator_order :
    scalarModulus • P256.Reference.generator = 0 := by
  native_decide

theorem generator_nonzero : P256.Reference.generator ≠ 0 := by
  native_decide

theorem addOrderOf_generator :
    addOrderOf P256.Reference.generator = scalarModulus :=
  addOrderOf_eq_prime generator_order generator_nonzero

theorem generator_nsmul_ne_zero {k : Nat} (hk0 : k ≠ 0)
    (hk : k < scalarModulus) :
    k • P256.Reference.generator ≠ 0 := by
  intro hzero
  have hdvd : scalarModulus ∣ k := by
    rw [← addOrderOf_generator, addOrderOf_dvd_iff_nsmul_eq_zero]
    exact hzero
  exact (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk0) hk) hdvd

theorem addOrderOf_eq_scalarModulus {q : Point} (hq : q ≠ 0)
    (horder : scalarModulus • q = 0) :
    addOrderOf q = scalarModulus :=
  addOrderOf_eq_prime horder hq

theorem order_nsmul {q : Point}
    (horder : scalarModulus • q = 0) (k : Nat) :
    scalarModulus • (k • q) = 0 := by
  rw [smul_smul, Nat.mul_comm, ← smul_smul, horder]
  simp

theorem order_add {p q : Point}
    (hp : scalarModulus • p = 0)
    (hq : scalarModulus • q = 0) :
    scalarModulus • (p + q) = 0 := by
  rw [nsmul_add, hp, hq, add_zero]

theorem no_two_torsion_of_order {q : Point}
    (horder : scalarModulus • q = 0) : q = 0 ∨ q + q ≠ 0 := by
  by_cases hq : q = 0
  · exact Or.inl hq
  · right
    intro htwo
    have hdvd : addOrderOf q ∣ 2 := by
      rw [addOrderOf_dvd_iff_nsmul_eq_zero]
      simpa only [two_nsmul] using htwo
    rw [addOrderOf_eq_scalarModulus hq horder] at hdvd
    exact (by native_decide : ¬ scalarModulus ∣ 2) hdvd

end Freigen.F2Z.Examples.EcdsaP256.Reference.Aux

namespace Freigen.F2Z.Examples.EcdsaP256

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

-- These executable reference lemmas interpret the concrete LC circuit.
-- The circuit definitions and WF theorems themselves remain context-polymorphic.
local instance : Context := lcContext

open Std.Do BigOperators
open scoped Std.Do

namespace Aux

theorem natCast_ofBits_eq_sum {n : Nat} (f : Fin n → Bool) :
    (Nat.ofBits f : Int) =
      ∑ k : Fin n, 2 ^ k.val * (f k).toInt := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.ofBits_succ, Nat.cast_add, Nat.cast_mul, Fin.sum_univ_succ]
      simp only [Nat.cast_ofNat, Fin.val_zero, pow_zero, one_mul,
        Fin.val_succ, pow_succ]
      rw [ih, Finset.mul_sum]
      have hf : ((f 0).toNat : Int) = (f 0).toInt := by
        cases f 0 <;> rfl
      rw [hf, add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [Function.comp_apply]
      ring

theorem oneHot {n : Nat} {b : Fin n → Int}
    (hb : ∀ i, b i = 0 ∨ b i = 1)
    (hsum : ∑ i, b i = 1) : ∃! i, b i = 1 := by
  have hb0 : ∀ i, 0 ≤ b i := fun i => by
    rcases hb i with h | h <;> omega
  have hex : ∃ i, b i = 1 := by
    by_contra h
    push Not at h
    have hz : ∀ i, b i = 0 := fun i => (hb i).resolve_right (h i)
    simp [hz] at hsum
  rcases hex with ⟨i, hi⟩
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hij
  have hmem : j ∈ (Finset.univ.erase i) := by simp [hij]
  have hle : b j ≤ ∑ k ∈ Finset.univ.erase i, b k :=
    Finset.single_le_sum (fun k _ => hb0 k) hmem
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) b
    (Finset.mem_univ i)
  rw [hi, hsum] at hsplit
  omega

theorem sum_mul_oneHot {n : Nat} (f b : Fin n → Int) (i : Fin n)
    (hi : b i = 1) (hzero : ∀ j, j ≠ i → b j = 0) :
    ∑ j, f j * b j = f i := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have hzsum : ∑ j ∈ Finset.univ.erase i, f j * b j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hzero j (Finset.mem_erase.mp hj).1]
    simp
  rw [hzsum, hi]
  simp

@[simp] theorem generatorByteX_get (i : Fin 256) :
    generatorByteX[i] = Reference.xNat (i.val • P256.Reference.generator) := by
  simp [generatorByteX]

@[simp] theorem generatorByteY_get (i : Fin 256) :
    generatorByteY[i] = Reference.yNat (i.val • P256.Reference.generator) := by
  simp [generatorByteY]

end Aux

theorem windowValue_eval {k : P256.Fn} (hk : k.val.Valid ρ)
    (start width : Nat) (hfit : start + width ≤ 256) :
    ρ.int (windowValue k start width hfit) =
      ((BitVec.extractLsb' start width (k.val.eval ρ)).toNat : Int) := by
  let f : Fin width → Bool := fun j =>
    ρ.bool (k.val.bits.bitsLE[start + j.val]'(by omega))
  have heval := U.eval_eq_ofFnLE k.val hk
  have hextract : BitVec.extractLsb' start width (k.val.eval ρ) =
      BitVec.ofFnLE f := by
    apply BitVec.eq_of_getElem_eq
    intro j hj
    rw [BitVec.getElem_extractLsb' hj, heval,
      BitVec.getLsbD_eq_getElem (by omega)]
    simp [BitVec.getElem_ofFnLE, f]
  rw [hextract, BitVec.toNat_ofFnLE, Aux.natCast_ofBits_eq_sum]
  unfold windowValue
  rw [Freigen.F2Z.Valuation.finset_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_nsmul]
  simp only [nsmul_eq_mul]
  exact congrArg (fun x : Int => 2 ^ j.val * x)
    (by simpa [f] using hk ⟨start + j.val, by omega⟩)

def WindowByteSpec (ρ : WF.Valuation) (k : P256.Fn) (i : Nat)
    (out : LC ℤ) : Prop :=
  ρ.int (out) =
    ((BitVec.extractLsb' (248 - 8 * i) 8 (k.val.eval ρ)).toNat : Int)

theorem WindowByteSpec.nonneg {out : LC ℤ}
    (h : WindowByteSpec ρ k i out) : 0 ≤ ρ.int (out) := by
  rw [h]
  exact_mod_cast Nat.zero_le _

theorem WindowByteSpec.lt {out : LC ℤ}
    (h : WindowByteSpec ρ k i out) : ρ.int (out) < 256 := by
  rw [h]
  exact_mod_cast (BitVec.extractLsb' (248 - 8 * i) 8
    (k.val.eval ρ)).isLt

@[spec] theorem windowByte_sound {k : P256.Fn} {i : Nat} {hi : i < 32}
    (hk : k.val.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (windowByte k i hi)
    ⦃⇓ out => ⌜WindowByteSpec ρ k i out⌝⦄ := by
  mvcgen [windowByte, WindowByteSpec]
  exact windowValue_eval hk _ _ _

@[spec] theorem windowByte_complete {k : P256.Fn} {i : Nat} {hi : i < 32}
    (hk : k.val.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (windowByte k i hi)
    ⦃⇓ out => ⌜WindowByteSpec ρ k i out⌝⦄ := by
  mvcgen [windowByte, WindowByteSpec]
  exact windowValue_eval hk _ _ _

def WindowDigitSpec (ρ : WF.Valuation) (k : P256.Fn) (i : Nat)
    (out : LC ℤ) : Prop :=
  ρ.int (out) =
    ((BitVec.extractLsb' (252 - 4 * i) 4 (k.val.eval ρ)).toNat : Int)

theorem WindowDigitSpec.nonneg {out : LC ℤ}
    (h : WindowDigitSpec ρ k i out) : 0 ≤ ρ.int (out) := by
  rw [h]
  exact_mod_cast Nat.zero_le _

theorem WindowDigitSpec.lt {out : LC ℤ}
    (h : WindowDigitSpec ρ k i out) : ρ.int (out) < 16 := by
  rw [h]
  exact_mod_cast (BitVec.extractLsb' (252 - 4 * i) 4
    (k.val.eval ρ)).isLt

@[spec] theorem windowDigit_sound {k : P256.Fn} {i : Nat} {hi : i < 64}
    (hk : k.val.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (windowDigit k i hi)
    ⦃⇓ out => ⌜WindowDigitSpec ρ k i out⌝⦄ := by
  mvcgen [windowDigit, WindowDigitSpec]
  exact windowValue_eval hk _ _ _

@[spec] theorem windowDigit_complete {k : P256.Fn} {i : Nat} {hi : i < 64}
    (hk : k.val.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (windowDigit k i hi)
    ⦃⇓ out => ⌜WindowDigitSpec ρ k i out⌝⦄ := by
  mvcgen [windowDigit, WindowDigitSpec]
  exact windowValue_eval hk _ _ _

theorem addComplete_multiple_sound
    {P Q : P256.AffineSlope.Point} {q : P256.Reference.Point} {k : Nat}
    (hP : P256.Reference.NormalizedRep ρ P (k • q))
    (hQ : P256.Reference.NormalizedRep ρ Q q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (P256.AffineSlope.addComplete P Q)
    ⦃⇓ out => ⌜P256.Reference.NormalizedRep ρ out ((k + 1) • q)⌝⦄ := by
  apply Triple.iff_conseq.mp
    (P256.AffineSlope.addComplete_sound_normalized hP hQ) (by simp)
  simp only [PostCond.entails, SPred.entails_nil]
  exact ⟨fun _ h => by simpa only [add_nsmul, one_nsmul] using h,
    ExceptConds.entails.refl _⟩

theorem addComplete_multiple_complete
    {P Q : P256.AffineSlope.Point} {q : P256.Reference.Point} {k : Nat}
    (hPvalid : P.Valid ρ) (hQvalid : Q.Valid ρ)
    (hP : P256.Reference.NormalizedRep ρ P (k • q))
    (hQ : P256.Reference.NormalizedRep ρ Q q)
    (horder : P256.scalarModulus • q = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (P256.AffineSlope.addComplete P Q)
    ⦃⇓ out => ⌜out.Valid ρ ∧ P256.Reference.NormalizedRep ρ out
      ((k + 1) • q)⌝⦄ := by
  apply Triple.iff_conseq.mp
    (P256.AffineSlope.addComplete_complete_mathlib hPvalid hQvalid hP hQ
      (Reference.Aux.no_two_torsion_of_order
        (Reference.Aux.order_nsmul horder k))) (by simp)
  simp only [PostCond.entails, SPred.entails_nil]
  exact ⟨fun _ h => ⟨h.1, by
      simpa only [add_nsmul, one_nsmul] using h.2⟩,
    ExceptConds.entails.refl _⟩

theorem ofElems_valid {P : P256.Projective} (hP : P.Valid ρ) :
    (P256.AffineSlope.ofElems P.X P.Y).Valid ρ := by
  exact ⟨rfl, Modular.Lazy.ofElem_valid P256.base hP.1, hP.1.2,
    rfl, Modular.Lazy.ofElem_valid P256.base hP.2.1, hP.2.1.2,
    by simp [P256.AffineSlope.ofElems]⟩

@[spec] theorem materializeMultiples_sound {P : P256.Projective}
    {q : P256.Reference.Point}
    (hP : P256.Reference.Represents ρ
      (P256.AffineSlope.ofElems P.X P.Y) q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (materializeMultiples P)
    ⦃⇓ table => ⌜∀ i : Fin 16,
      P256.Reference.NormalizedRep ρ table[i] (i.val • q)⌝⦄ := by
  have hP' : P256.Reference.NormalizedRep ρ
      (P256.AffineSlope.ofElems P.X P.Y) q := by
    refine ⟨hP, ?_⟩
    intro hq
    have hinf := P256.Reference.Aux.represents_zero (hq ▸ hP)
    simp [P256.AffineSlope.ofElems] at hinf
  mvcgen [-P256.AffineSlope.addComplete_sound_normalized,
    addComplete_multiple_sound, materializeMultiples]
  all_goals first
    | exact 1
    | simpa using hP'
    | assumption
    | skip
  all_goals intro i
  all_goals fin_cases i <;> simp_all [P256.AffineSlope.infinity,
    P256.Reference.NormalizedRep, P256.Reference.Represents,
    P256.Reference.circuitCoordinates,
    P256.Reference.coordinates]

@[spec] theorem materializeMultiples_complete {P : P256.Projective}
    {q : P256.Reference.Point}
    (hPvalid : P.Valid ρ)
    (hP : P256.Reference.Represents ρ
      (P256.AffineSlope.ofElems P.X P.Y) q)
    (horder : P256.scalarModulus • q = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (materializeMultiples P)
    ⦃⇓ table => ⌜∀ i : Fin 16, table[i].Valid ρ ∧
      P256.Reference.NormalizedRep ρ table[i] (i.val • q)⌝⦄ := by
  have hP' : P256.Reference.NormalizedRep ρ
      (P256.AffineSlope.ofElems P.X P.Y) q := by
    refine ⟨hP, ?_⟩
    intro hq
    have hinf := P256.Reference.Aux.represents_zero (hq ▸ hP)
    simp [P256.AffineSlope.ofElems] at hinf
  have hPvalid' := ofElems_valid hPvalid
  have hInfinityValid : P256.AffineSlope.infinity.Valid ρ := by
    have hz : P256.zero.Valid ρ :=
      Modular.ofNat_valid P256.base 0 (by native_decide) (by native_decide)
    exact ⟨rfl, Modular.Lazy.ofElem_valid P256.base hz, hz.2,
      rfl, Modular.Lazy.ofElem_valid P256.base hz, hz.2,
      by simp [P256.AffineSlope.infinity]⟩
  mvcgen [-P256.AffineSlope.addComplete_complete_mathlib,
    addComplete_multiple_complete, materializeMultiples]
  case vc2.k => exact 1
  case vc9.k => exact 2
  case vc16.k => exact 3
  case vc23.k => exact 4
  case vc30.k => exact 5
  case vc37.k => exact 6
  case vc44.k => exact 7
  case vc51.k => exact 8
  case vc58.k => exact 9
  case vc65.k => exact 10
  case vc72.k => exact 11
  case vc79.k => exact 12
  case vc86.k => exact 13
  case vc93.k => exact 14
  all_goals first
    | exact q
    | exact horder
    | exact hPvalid'
    | exact hP'
    | exact hInfinityValid
    | simpa using hP'
    | simp_all
  all_goals intro i
  all_goals fin_cases i <;> simp_all [P256.AffineSlope.infinity,
    P256.Reference.NormalizedRep, P256.Reference.Represents,
    P256.Reference.circuitCoordinates, P256.Reference.coordinates]

def IndicatorsSpec {n : Nat} (ρ : WF.Valuation) (digit : LC ℤ)
    (out : U n) : Prop :=
  out.Valid ρ ∧ ∃ i : Fin n,
    ρ.int (out.intBits[i]) = 1 ∧ ρ.int (digit) = i.val ∧
      ∀ j : Fin n, ρ.int (out.intBits[j]) = 1 → j = i

@[spec] theorem indicators_sound {n : Nat} {digit : LC ℤ} :
    ⦃⌜True⌝⦄ Sound.interp ρ (indicators n digit)
    ⦃⇓ out => ⌜IndicatorsSpec ρ digit out⌝⦄ := by
  mvcgen [indicators, IndicatorsSpec]
  intro bits
  mvcgen
  rename_i out hout hsum hweighted
  refine ⟨hout.1, ?_⟩
  have hbit : ∀ i : Fin n,
      ρ.int (out.intBits[i]) = 0 ∨ ρ.int (out.intBits[i]) = 1 := by
    intro i
    have hi := hout.1 i
    cases hb : ρ.bool (out.bits.bitsLE[i]) <;>
      rw [hb] at hi <;> simp at hi
    · exact Or.inl hi
    · exact Or.inr hi
  have hsum' : ∑ i : Fin n, ρ.int (out.intBits[i]) = 1 := by
    simp only [Freigen.F2Z.Valuation.zero_apply, zero_mul, Freigen.F2Z.Valuation.sub_apply, Freigen.F2Z.Valuation.finset_sum,
      Freigen.F2Z.Valuation.one_apply] at hsum
    exact sub_eq_zero.mp hsum.symm
  rcases Aux.oneHot hbit hsum' with ⟨i, hi, hui⟩
  refine ⟨i, hi, ?_, hui⟩
  · simp only [Freigen.F2Z.Valuation.zero_apply, zero_mul, Freigen.F2Z.Valuation.sub_apply, Freigen.F2Z.Valuation.finset_sum,
      map_nsmul, nsmul_eq_mul] at hweighted
    have hzero : ∀ j : Fin n, j ≠ i →
        ρ.int (out.intBits[j]) = 0 := by
      intro j hji
      rcases hbit j with hj | hj
      · exact hj
      · exact (hji (hui j hj)).elim
    rw [show (∑ j : Fin n, (j.val : Int) *
        ρ.int (out.intBits[j])) = i.val by
      have hrest : ∑ j ∈ (Finset.univ.erase i), (j.val : Int) *
          ρ.int (out.intBits[j]) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [hzero j (Finset.mem_erase.mp hj).1]
        simp
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hrest, hi]
      simp] at hweighted
    omega

@[spec] theorem indicators_complete {n : Nat} {digit : LC ℤ}
    (hd0 : 0 ≤ ρ.int (digit)) (hdlt : ρ.int (digit) < (n : Int)) :
    ⦃⌜True⌝⦄ Complete.interp ρ (indicators n digit)
    ⦃⇓ out => ⌜IndicatorsSpec ρ digit out⌝⦄ := by
  mvcgen [indicators]
  let bits : Vector Bool n := Vector.ofFn fun i =>
    ρ.int (digit) = i.val
  refine ⟨bits, rfl, ?_⟩
  mvcgen
  rename_i out hout
  let chosen : Fin n := ⟨(ρ.int (digit)).toNat,
    (Int.toNat_lt hd0).2 hdlt⟩
  have houtBool (i : Fin n) :
      ρ.bool (out.bits.bitsLE[i]) = bits[i] := by
    have heval := U.eval_eq_ofFnLE out hout.1
    have hrel := hout.2
    rw [heval] at hrel
    have heq := congrArg (fun w : BitVec n => w[i.val]) hrel
    have heq' : ρ.bool (out.bits.bitsLE[i]) =
        ρ.bool (LC.ofConst bits[i]) := by
      simpa only [Word.eval, BitVec.getElem_ofFnLE,
        Vector.getElem_map, Fin.getElem_fin] using heq
    exact heq'.trans (LC.Valuation.ofConst_apply ρ.bool bits[i])
  have hbit (i : Fin n) :
      ρ.int (out.intBits[i]) = if i = chosen then 1 else 0 := by
    have hi := hout.1 i
    rw [houtBool i] at hi
    by_cases h : i = chosen
    · subst i
      simp [bits, chosen, Int.toNat_of_nonneg hd0] at hi ⊢
      exact hi
    · have hne : ρ.int (digit) ≠ (i.val : Int) := by
        intro heq
        apply h
        apply Fin.eq_of_val_eq
        dsimp [chosen]
        omega
      simp [bits, h, hne] at hi ⊢
      exact hi
  have hsum : ∑ i : Fin n, ρ.int (out.intBits[i]) = 1 := by
    simp_rw [hbit]
    simp
  have hweighted : ∑ i : Fin n, (i.val : Int) *
      ρ.int (out.intBits[i]) = ρ.int (digit) := by
    simp_rw [hbit]
    simp [chosen, Int.toNat_of_nonneg hd0]
  have hassertSum : ρ.int 0 * ρ.int 0 =
      ρ.int ((∑ i : Fin n, out.intBits[i]) - 1) := by
    simp only [Freigen.F2Z.Valuation.zero_apply, Freigen.F2Z.Valuation.sub_apply, Freigen.F2Z.Valuation.finset_sum, Freigen.F2Z.Valuation.one_apply]
    omega
  have hassertWeighted : ρ.int 0 * ρ.int 0 =
      ρ.int ((∑ i : Fin n, i.val • out.intBits[i]) - digit) := by
    simp only [Freigen.F2Z.Valuation.zero_apply, Freigen.F2Z.Valuation.sub_apply, Freigen.F2Z.Valuation.finset_sum, map_nsmul,
      nsmul_eq_mul]
    omega
  constructor
  · exact hassertSum
  · mvcgen
    constructor
    · exact hassertWeighted
    · mvcgen
      refine ⟨hout.1, chosen, ?_, ?_, ?_⟩
      · rw [hbit chosen]
        simp
      · simp [chosen, Int.toNat_of_nonneg hd0]
      · intro j hj
        rw [hbit] at hj
        split at hj
        · assumption
        · omega

@[spec] theorem windowIndicators_complete {digit : LC ℤ}
    (hd0 : 0 ≤ ρ.int (digit)) (hdlt : ρ.int (digit) < 16) :
    ⦃⌜True⌝⦄ Complete.interp ρ (windowIndicators digit)
    ⦃⇓ out => ⌜IndicatorsSpec ρ digit out⌝⦄ := by
  simpa [windowIndicators] using
    (indicators_complete (ρ := ρ) (n := 16) hd0 hdlt)

@[spec] theorem byteIndicators_complete {digit : LC ℤ}
    (hd0 : 0 ≤ ρ.int (digit)) (hdlt : ρ.int (digit) < 256) :
    ⦃⌜True⌝⦄ Complete.interp ρ (byteIndicators digit)
    ⦃⇓ out => ⌜IndicatorsSpec ρ digit out⌝⦄ := by
  simpa [byteIndicators] using
    (indicators_complete (ρ := ρ) (n := 256) hd0 hdlt)

@[spec] theorem windowIndicators_sound {digit : LC ℤ} :
    ⦃⌜True⌝⦄ Sound.interp ρ (windowIndicators digit)
    ⦃⇓ out => ⌜IndicatorsSpec ρ digit out⌝⦄ := by
  simpa [windowIndicators] using
    (indicators_sound (ρ := ρ) (n := 16) (digit := digit))

@[spec] theorem byteIndicators_sound {digit : LC ℤ} :
    ⦃⌜True⌝⦄ Sound.interp ρ (byteIndicators digit)
    ⦃⇓ out => ⌜IndicatorsSpec ρ digit out⌝⦄ := by
  simpa [byteIndicators] using
    (indicators_sound (ρ := ρ) (n := 256) (digit := digit))

def LookupRepSpec (ρ : WF.Valuation) (indicators : U 16)
    (xs : Vector P256.AffineSlope.Rep 16)
    (out : P256.AffineSlope.Rep) : Prop :=
  ∀ i : Fin 16, ρ.int (indicators.intBits[i]) = 1 →
    Modular.Lazy.evalZMod P256.base out ρ =
      Modular.Lazy.evalZMod P256.base xs[i] ρ

@[spec] theorem assertLookupRep_sound {indicators : U 16} {out : U 256}
    {xs : Vector P256.AffineSlope.Rep 16} :
    ⦃⌜True⌝⦄ Sound.interp ρ (assertLookupRep indicators out xs)
    ⦃⇓ _ => ⌜LookupRepSpec ρ indicators xs ⟨out.intVal, 2⟩⌝⦄ := by
  mvcgen [assertLookupRep, WF.foldRange] invariants
  · ⇓⟨cur, _⟩ => ⌜∀ i : Fin 16, i.val < cur.prefix.length →
      ρ.int (indicators.intBits[i]) = 1 →
      Modular.Lazy.evalZMod P256.base ⟨out.intVal, 2⟩ ρ =
        Modular.Lazy.evalZMod P256.base xs[i] ρ⌝
  case vc1 pref cur suff hsplit _ hprev hassert =>
    intro i hi hone
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i.val < pref.length
    · exact hprev i hlt hone
    · have hieq : i.val = cur := by
        have hcur : cur = pref.length := by grind
        omega
      subst cur
      rcases hassert with ⟨_, hassert⟩
      simp only [Freigen.F2Z.Valuation.sub_apply, Freigen.F2Z.Valuation.zero_apply] at hassert
      rw [show ρ.int (indicators.intBits[i.val]) = 1 by simpa using hone,
        one_mul] at hassert
      have houtEq : ρ.int (out.intVal) = ρ.int (xs[i].intVal) := by
        simpa only [Fin.getElem_fin] using sub_eq_zero.mp hassert
      unfold Modular.Lazy.evalZMod
      rw [houtEq]
  case vc2 => simp
  case vc3 h => simpa [LookupRepSpec] using h

@[spec] theorem assertLookupRep_complete
    {indicators : U 16} {out : U 256}
    {xs : Vector P256.AffineSlope.Rep 16}
    (hindicators : indicators.Valid ρ)
    (heq : ∀ i : Fin 16, ρ.int (indicators.intBits[i]) = 1 →
      ρ.int (out.intVal) = ρ.int (xs[i].intVal)) :
    ⦃⌜True⌝⦄ Complete.interp ρ (assertLookupRep indicators out xs)
    ⦃⇓ _ => ⌜LookupRepSpec ρ indicators xs ⟨out.intVal, 2⟩⌝⦄ := by
  have hbit (i : Fin 16) : ρ.int (indicators.intBits[i]) = 0 ∨
      ρ.int (indicators.intBits[i]) = 1 := by
    have hi := hindicators i
    cases hb : ρ.bool (indicators.bits.bitsLE[i]) <;>
      rw [hb] at hi <;> simp at hi
    · exact Or.inl hi
    · exact Or.inr hi
  mvcgen [assertLookupRep, WF.foldRange] invariants
  · ⇓⟨cur, _⟩ => ⌜∀ i : Fin 16, i.val < cur.prefix.length →
      ρ.int (indicators.intBits[i]) = 1 →
      Modular.Lazy.evalZMod P256.base ⟨out.intVal, 2⟩ ρ =
        Modular.Lazy.evalZMod P256.base xs[i] ρ⌝
  case vc1 pref cur suff hsplit _ hprev =>
    have hcur16 : cur < 16 := by grind
    let fi : Fin 16 := ⟨cur, hcur16⟩
    constructor
    · rcases hbit fi with hz | ho
      · have hz' : ρ.int (indicators.intBits[cur]) = 0 := by
          simpa [fi] using hz
        simp [hz']
      · have ho' : ρ.int (indicators.intBits[cur]) = 1 := by
          simpa [fi] using ho
        simp only [Freigen.F2Z.Valuation.sub_apply, Freigen.F2Z.Valuation.zero_apply, ho', one_mul]
        exact sub_eq_zero.mpr (heq fi (by simpa [fi] using ho'))
    · mvcgen
      intro i hi hone
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hlt : i.val < pref.length
      · exact hprev i hlt hone
      · have hieq : i.val = cur := by
          have hcur : cur = pref.length := by grind
          omega
        subst cur
        unfold Modular.Lazy.evalZMod
        rw [heq i hone]
  case vc2 => simp
  case vc3 h => simpa [LookupRepSpec] using h

@[spec] theorem lookupRep_sound {digit : LC ℤ} {indicators : U 16}
    {xs : Vector P256.AffineSlope.Rep 16} :
    ⦃⌜True⌝⦄ Sound.interp ρ (lookupRep digit indicators xs)
    ⦃⇓ out => ⌜LookupRepSpec ρ indicators xs out⌝⦄ := by
  mvcgen [lookupRep, lookupRepWord]
  intro bits
  mvcgen

@[spec] theorem lookupRep_complete {digit : LC ℤ}
    {indicators : U 16} {xs : Vector P256.AffineSlope.Rep 16}
    (hd0 : 0 ≤ ρ.int (digit)) (hdlt : ρ.int (digit) < 16)
    (hindicators : IndicatorsSpec ρ digit indicators)
    (hxs : ∀ i : Fin 16, xs[i].Valid ρ ∧
      ρ.int (xs[i].intVal) < P256.base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ (lookupRep digit indicators xs)
    ⦃⇓ out => ⌜LookupRepSpec ρ indicators xs out ∧ out.Valid ρ ∧
      ρ.int (out.intVal) < P256.base.modulus ∧ out.bound = 2⌝⦄ := by
  mvcgen [lookupRep, lookupRepWord]
  let chosen : Fin 16 := ⟨(ρ.int (digit)).toNat,
    (Int.toNat_lt hd0).2 hdlt⟩
  let values : Array Int := #[ρ.int (xs[0].intVal),
    ρ.int (xs[1].intVal), ρ.int (xs[2].intVal),
    ρ.int (xs[3].intVal), ρ.int (xs[4].intVal),
    ρ.int (xs[5].intVal), ρ.int (xs[6].intVal),
    ρ.int (xs[7].intVal), ρ.int (xs[8].intVal),
    ρ.int (xs[9].intVal), ρ.int (xs[10].intVal),
    ρ.int (xs[11].intVal), ρ.int (xs[12].intVal),
    ρ.int (xs[13].intVal), ρ.int (xs[14].intVal),
    ρ.int (xs[15].intVal)]
  let value := values[(ρ.int (digit)).toNat]!
  let bits : Vector Bool 256 := Vector.ofFn fun i => value.toNat.testBit i.val
  have hdNat : (ρ.int (digit)).toNat < 16 :=
    (Int.toNat_lt hd0).2 hdlt
  have hvalues (i : Fin 16) : values[i.val] = ρ.int (xs[i].intVal) := by
    fin_cases i <;> rfl
  have hvalue : value = ρ.int (xs[chosen].intVal) := by
    unfold value
    rw [getElem!_pos values _ (by simpa [values] using hdNat)]
    exact hvalues chosen
  refine ⟨bits, ?_, ?_⟩
  · simp [WF.interpHint, WF.evalArgs, lookupRepHint, lookupArgs,
      bits, value, values]
  · have houtFacts (out : U 256)
        (hout : U.Rel ρ out
          (Word.eval ρ.bool { bitsLE := Vector.map LC.ofConst bits })) :
        (∀ i : Fin 16, ρ.int (indicators.intBits[i]) = 1 →
          ρ.int (out.intVal) = ρ.int (xs[i].intVal)) ∧
        ((⟨out.intVal, 2⟩ : P256.AffineSlope.Rep).Valid ρ ∧
          ρ.int (out.intVal) < P256.base.modulus) := by
      have hvalue0 : 0 ≤ value := hvalue ▸ (hxs chosen).1.1
      have hvalueLt : value < P256.base.modulus := hvalue ▸ (hxs chosen).2
      have hfit : value.toNat < 2 ^ 256 := by
        apply (Int.toNat_lt hvalue0).2
        exact hvalueLt.trans (by
          norm_num [P256.base, P256.baseModulus])
      have hword :
          (Word.eval ρ.bool { bitsLE := Vector.map LC.ofConst bits }).toNat =
            value.toNat := by
        rw [show Vector.map LC.ofConst bits =
            Vector.ofFn (n := 256) fun i =>
              LC.ofConst (value.toNat.testBit i.val) by
          ext i
          simp [bits]]
        exact Modular.Aux.constWord_eval_toNat_lc value.toNat hfit ρ
      have houtVal : ρ.int (out.intVal) = value := by
        rw [U.Rel.intVal_apply hout, hword, Int.toNat_of_nonneg hvalue0]
      constructor
      · intro i hi
        rcases hindicators.2 with ⟨selected, _, hdigit, hunique⟩
        have hisel := hunique i hi
        have hchosen : selected = chosen := by
          apply Fin.eq_of_val_eq
          dsimp [chosen]
          omega
        rw [hisel, hchosen]
        exact houtVal.trans hvalue
      · exact ⟨⟨U.intVal_nonneg out hout.1, by
          rw [houtVal]
          have hp : (0 : Int) < P256.base.modulus := by
            exact_mod_cast P256.base.positive
          simpa using hvalueLt.trans (by nlinarith)⟩,
          by simpa [houtVal] using hvalueLt⟩
    mvcgen -trivial
    case vc1.hindicators => exact hindicators.1
    case vc2.heq out hout => exact (houtFacts out hout).1
    case vc3.vc1.refine_2.success.success =>
      rename_i out hout _ hlookup
      exact ⟨hlookup, (houtFacts out hout).2.1,
        (houtFacts out hout).2.2⟩

def LookupFlagSpec (ρ : WF.Valuation) (indicators : U 16)
    (flags : Vector (LC ℤ) 16) (out : LC ℤ) : Prop :=
  ∀ i : Fin 16, ρ.int (indicators.intBits[i]) = 1 →
    ρ.int (out) = ρ.int (flags[i])

@[spec] theorem assertLookupFlag_sound {indicators : U 16} {out : LC ℤ}
    {flags : Vector (LC ℤ) 16} :
    ⦃⌜True⌝⦄ Sound.interp ρ (assertLookupFlag indicators out flags)
    ⦃⇓ _ => ⌜LookupFlagSpec ρ indicators flags out⌝⦄ := by
  mvcgen [assertLookupFlag, WF.foldRange] invariants
  · ⇓⟨cur, _⟩ => ⌜∀ i : Fin 16, i.val < cur.prefix.length →
      ρ.int (indicators.intBits[i]) = 1 →
      ρ.int (out) = ρ.int (flags[i])⌝
  case vc1 pref cur suff hsplit _ hprev hassert =>
    intro i hi hone
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i.val < pref.length
    · exact hprev i hlt hone
    · have hieq : i.val = cur := by
        have hcur : cur = pref.length := by grind
        omega
      subst cur
      rcases hassert with ⟨_, hassert⟩
      simp only [Freigen.F2Z.Valuation.sub_apply, Freigen.F2Z.Valuation.zero_apply] at hassert
      rw [show ρ.int (indicators.intBits[i.val]) = 1 by simpa using hone,
        one_mul] at hassert
      simpa only [Fin.getElem_fin] using sub_eq_zero.mp hassert
  case vc2 => simp
  case vc3 h => simpa [LookupFlagSpec] using h

@[spec] theorem assertLookupFlag_complete {indicators : U 16} {out : LC ℤ}
    {flags : Vector (LC ℤ) 16}
    (hindicators : indicators.Valid ρ)
    (heq : ∀ i : Fin 16, ρ.int (indicators.intBits[i]) = 1 →
      ρ.int (out) = ρ.int (flags[i])) :
    ⦃⌜True⌝⦄ Complete.interp ρ (assertLookupFlag indicators out flags)
    ⦃⇓ _ => ⌜LookupFlagSpec ρ indicators flags out⌝⦄ := by
  have hbit (i : Fin 16) : ρ.int (indicators.intBits[i]) = 0 ∨
      ρ.int (indicators.intBits[i]) = 1 := by
    have hi := hindicators i
    cases hb : ρ.bool (indicators.bits.bitsLE[i]) <;>
      rw [hb] at hi <;> simp at hi
    · exact Or.inl hi
    · exact Or.inr hi
  mvcgen [assertLookupFlag, WF.foldRange] invariants
  · ⇓⟨cur, _⟩ => ⌜∀ i : Fin 16, i.val < cur.prefix.length →
      ρ.int (indicators.intBits[i]) = 1 →
      ρ.int (out) = ρ.int (flags[i])⌝
  case vc1 pref cur suff hsplit _ hprev =>
    have hcur16 : cur < 16 := by grind
    let fi : Fin 16 := ⟨cur, hcur16⟩
    constructor
    · rcases hbit fi with hz | ho
      · have hz' : ρ.int (indicators.intBits[cur]) = 0 := by
          simpa [fi] using hz
        simp [hz']
      · have ho' : ρ.int (indicators.intBits[cur]) = 1 := by
          simpa [fi] using ho
        simp only [Freigen.F2Z.Valuation.sub_apply, Freigen.F2Z.Valuation.zero_apply, ho', one_mul]
        exact sub_eq_zero.mpr (heq fi (by simpa [fi] using ho'))
    · mvcgen
      intro i hi hone
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hlt : i.val < pref.length
      · exact hprev i hlt hone
      · have hieq : i.val = cur := by
          have hcur : cur = pref.length := by grind
          omega
        subst cur
        rw [heq i hone]
  case vc2 => simp

@[spec] theorem lookupFlag_sound {digit : LC ℤ} {indicators : U 16}
    {flags : Vector (LC ℤ) 16} :
    ⦃⌜True⌝⦄ Sound.interp ρ (lookupFlag digit indicators flags)
    ⦃⇓ out => ⌜LookupFlagSpec ρ indicators flags out⌝⦄ := by
  mvcgen [lookupFlag]
  intro bits
  mvcgen

@[spec] theorem lookupFlag_complete {digit : LC ℤ}
    {indicators : U 16} {flags : Vector (LC ℤ) 16}
    (hd0 : 0 ≤ ρ.int (digit)) (hdlt : ρ.int (digit) < 16)
    (hindicators : IndicatorsSpec ρ digit indicators)
    (hflags : ∀ i : Fin 16, ρ.int (flags[i]) = 0 ∨
      ρ.int (flags[i]) = 1) :
    ⦃⌜True⌝⦄ Complete.interp ρ (lookupFlag digit indicators flags)
    ⦃⇓ out => ⌜LookupFlagSpec ρ indicators flags out ∧
      (ρ.int (out) = 0 ∨ ρ.int (out) = 1)⌝⦄ := by
  mvcgen [lookupFlag]
  let chosen : Fin 16 := ⟨(ρ.int (digit)).toNat,
    (Int.toNat_lt hd0).2 hdlt⟩
  let values : Array Int := #[ρ.int (flags[0]), ρ.int (flags[1]),
    ρ.int (flags[2]), ρ.int (flags[3]), ρ.int (flags[4]),
    ρ.int (flags[5]), ρ.int (flags[6]), ρ.int (flags[7]),
    ρ.int (flags[8]), ρ.int (flags[9]), ρ.int (flags[10]),
    ρ.int (flags[11]), ρ.int (flags[12]), ρ.int (flags[13]),
    ρ.int (flags[14]), ρ.int (flags[15])]
  let bitValue : Bool := ρ.int (flags[chosen]) = 1
  let bits : Vector Bool 1 := #v[bitValue]
  have hdNat : (ρ.int (digit)).toNat < 16 :=
    (Int.toNat_lt hd0).2 hdlt
  have hvalues (i : Fin 16) : values[i.val] = ρ.int (flags[i]) := by
    fin_cases i <;> rfl
  have hget : values[(ρ.int (digit)).toNat]! =
      ρ.int (flags[chosen]) := by
    rw [getElem!_pos values _ (by simpa [values] using hdNat)]
    exact hvalues chosen
  refine ⟨bits, ?_, ?_⟩
  · simp [WF.interpHint, WF.evalArgs, lookupFlagHint, lookupArgs,
      bits, bitValue, values, hget]
  · have houtFacts (out : LC ℤ)
        (hout : ρ.int (out) =
          (ρ.bool (Vector.map LC.ofConst #v[bitValue])[0]).toInt) :
        (∀ i : Fin 16, ρ.int (indicators.intBits[i]) = 1 →
          ρ.int (out) = ρ.int (flags[i])) ∧
        (ρ.int (out) = 0 ∨ ρ.int (out) = 1) := by
      have hout' : ρ.int (out) = bitValue.toInt := by
        have hconst : ρ.bool (Vector.map LC.ofConst #v[bitValue])[0] =
            bitValue := by
          calc
            ρ.bool (Vector.map LC.ofConst #v[bitValue])[0] =
                ρ.bool (LC.ofConst bitValue) := congrArg ρ.bool (by simp)
            _ = bitValue := LC.Valuation.ofConst_apply ρ.bool bitValue
        exact hout.trans (congrArg Bool.toInt hconst)
      have houtVal : ρ.int (out) = ρ.int (flags[chosen]) := by
        rw [hout']
        rcases hflags chosen with h0 | h1
        · have h0' : ρ.int (flags[chosen]) = 0 := h0
          simp only [bitValue, h0']
          rfl
        · have h1' : ρ.int (flags[chosen]) = 1 := h1
          simp only [bitValue, h1', decide_true]
          rfl
      constructor
      · intro i hi
        rcases hindicators.2 with ⟨selected, _, hdigit, hunique⟩
        have hisel := hunique i hi
        have hchosen : selected = chosen := by
          apply Fin.eq_of_val_eq
          dsimp [chosen]
          omega
        rw [hisel, hchosen]
        exact houtVal
      · exact houtVal ▸ hflags chosen
    mvcgen -trivial
    case vc1.hindicators => exact hindicators.1
    case vc2.heq out hout => exact (houtFacts out hout).1
    case vc3.vc1.refine_2.success.success =>
      rename_i out hout _ hlookup
      exact ⟨hlookup, (houtFacts out hout).2⟩

@[spec] theorem lookupPoint_sound {digit : LC ℤ}
    {table : Vector P256.AffineSlope.Point 16}
    {q : P256.Reference.Point}
    (htable : ∀ i : Fin 16,
      P256.Reference.NormalizedRep ρ table[i] (i.val • q)) :
    ⦃⌜True⌝⦄ Sound.interp ρ (lookupPoint digit table)
    ⦃⇓ out => ⌜∃ i : Fin 16, ρ.int (digit) = i.val ∧
      P256.Reference.NormalizedRep ρ out (i.val • q)⌝⦄ := by
  mvcgen [lookupPoint]
  rename_i indicators hi X hX Y hY infinity hinfinity
  rcases hi.2 with ⟨i, hone, hdigit, _⟩
  refine ⟨i, hdigit, ?_⟩
  have hxi : Modular.Lazy.evalZMod P256.base X ρ =
      Modular.Lazy.evalZMod P256.base table[i].X ρ := by
    simpa using hX i hone
  have hyi : Modular.Lazy.evalZMod P256.base Y ρ =
      Modular.Lazy.evalZMod P256.base table[i].Y ρ := by
    simpa using hY i hone
  have hfi : ρ.int (infinity) = ρ.int (table[i].infinity) := by
    simpa using hinfinity i hone
  rcases htable i with ⟨⟨hbit, hcoordinates⟩, hnormalized⟩
  constructor
  · unfold P256.Reference.Represents
    constructor
    · rw [hfi]
      exact hbit
    · unfold P256.Reference.circuitCoordinates at hcoordinates ⊢
      rw [hfi, hxi, hyi]
      exact hcoordinates
  · intro hzero
    have hzeroCoordinates := hnormalized hzero
    exact ⟨hxi.trans hzeroCoordinates.1, hyi.trans hzeroCoordinates.2⟩

@[spec] theorem lookupPoint_complete {digit : LC ℤ}
    {table : Vector P256.AffineSlope.Point 16}
    {q : P256.Reference.Point}
    (hd0 : 0 ≤ ρ.int (digit)) (hdlt : ρ.int (digit) < 16)
    (htableValid : ∀ i : Fin 16, table[i].Valid ρ)
    (htable : ∀ i : Fin 16,
      P256.Reference.NormalizedRep ρ table[i] (i.val • q)) :
    ⦃⌜True⌝⦄ Complete.interp ρ (lookupPoint digit table)
    ⦃⇓ out => ⌜out.Valid ρ ∧ ∃ i : Fin 16,
      ρ.int (digit) = i.val ∧
        P256.Reference.NormalizedRep ρ out (i.val • q)⌝⦄ := by
  mvcgen [lookupPoint]
  case vc6.hxs =>
    intro i
    simpa using ⟨(htableValid i).2.1, (htableValid i).2.2.1⟩
  case vc10.hxs =>
    intro i
    simpa using ⟨(htableValid i).2.2.2.2.1,
      (htableValid i).2.2.2.2.2.1⟩
  case vc14.hflags =>
    intro i
    simpa using (htableValid i).2.2.2.2.2.2
  case vc15.success.success.success.success =>
    rename_i indicators hi X hX Y hY infinity hinfinity
    rcases hi.2 with ⟨i, hone, hdigit, _⟩
    have hxi : Modular.Lazy.evalZMod P256.base X ρ =
        Modular.Lazy.evalZMod P256.base table[i].X ρ := by
      simpa using hX.1 i hone
    have hyi : Modular.Lazy.evalZMod P256.base Y ρ =
        Modular.Lazy.evalZMod P256.base table[i].Y ρ := by
      simpa using hY.1 i hone
    have hfi : ρ.int (infinity) = ρ.int (table[i].infinity) := by
      simpa using hinfinity.1 i hone
    rcases htable i with ⟨⟨hbit, hcoordinates⟩, hnormalized⟩
    refine ⟨?_, i, hdigit, ?_⟩
    · exact ⟨hX.2.2.2, hX.2.1, hX.2.2.1,
        hY.2.2.2, hY.2.1, hY.2.2.1, hinfinity.2⟩
    · constructor
      · unfold P256.Reference.Represents
        constructor
        · rw [hfi]
          exact hbit
        · unfold P256.Reference.circuitCoordinates at hcoordinates ⊢
          rw [hfi, hxi, hyi]
          exact hcoordinates
      · intro hzero
        have hzeroCoordinates := hnormalized hzero
        exact ⟨hxi.trans hzeroCoordinates.1,
          hyi.trans hzeroCoordinates.2⟩
@[spec] theorem lookupGeneratorByte_sound {digit : LC ℤ} :
    ⦃⌜True⌝⦄ Sound.interp ρ (lookupGeneratorByte digit)
    ⦃⇓ out => ⌜∃ i : Fin 256, ρ.int (digit) = i.val ∧
      P256.Reference.NormalizedRep ρ out
        (i.val • P256.Reference.generator)⌝⦄ := by
  mvcgen [lookupGeneratorByte]
  rename_i indicators hi
  rcases hi.2 with ⟨i, hone, hdigit, hunique⟩
  refine ⟨i, hdigit, ?_⟩
  constructor
  · unfold P256.Reference.Represents P256.Reference.circuitCoordinates
    constructor
    · have hbit := hi.1 (0 : Fin 256)
      cases hb : ρ.bool (indicators.bits.bitsLE[(0 : Fin 256)]) <;>
        rw [hb] at hbit <;> simp at hbit
      · exact Or.inl hbit
      · exact Or.inr hbit
    · by_cases hi0 : i.val = 0
      · have hieq : i = 0 := Fin.eq_of_val_eq hi0
        subst i
        simp only [P256.Reference.coordinates, if_pos (by simpa using hone)]
        rfl
      · have hzero : ρ.int (indicators.intBits[0]) = 0 := by
          have hbit := hi.1 (0 : Fin 256)
          have hcases : ρ.int (indicators.intBits[0]) = 0 ∨
              ρ.int (indicators.intBits[0]) = 1 := by
            cases hb : ρ.bool (indicators.bits.bitsLE[(0 : Fin 256)]) <;>
              rw [hb] at hbit <;> simp at hbit
            · exact Or.inl hbit
            · exact Or.inr hbit
          exact hcases.resolve_right fun h => by
            have := hunique 0 h
            omega
        rw [if_neg (show ρ.int (indicators.intBits[0]) ≠ 1 by omega)]
        have hnonzero := Reference.Aux.generator_nsmul_ne_zero hi0
          (i.isLt.trans (by native_decide : 256 < P256.scalarModulus))
        rcases hpoint : i.val • P256.Reference.generator with _ | ⟨x, y, hxy⟩
        · exact (hnonzero hpoint).elim
        · simp only [P256.Reference.coordinates]
          congr 1
          · unfold Modular.Lazy.evalZMod
            simp only [Freigen.F2Z.Valuation.finset_sum, map_nsmul, nsmul_eq_mul]
            rw [show (∑ j : Fin 256, (generatorByteX[j] : ℤ) *
                ρ.int (indicators.intBits[j])) = generatorByteX[i] by
              exact Aux.sum_mul_oneHot _ _ i hone fun j hji => by
                have hbit := hi.1 j
                cases hb : ρ.bool (indicators.bits.bitsLE[j]) <;>
                  rw [hb] at hbit <;> simp at hbit
                · exact hbit
                · exact (hji (hunique j hbit)).elim]
            rw [Aux.generatorByteX_get, hpoint]
            exact ZMod.natCast_zmod_val x
          · unfold Modular.Lazy.evalZMod
            simp only [Freigen.F2Z.Valuation.finset_sum, map_nsmul, nsmul_eq_mul]
            rw [show (∑ j : Fin 256, (generatorByteY[j] : ℤ) *
                ρ.int (indicators.intBits[j])) = generatorByteY[i] by
              exact Aux.sum_mul_oneHot _ _ i hone fun j hji => by
                have hbit := hi.1 j
                cases hb : ρ.bool (indicators.bits.bitsLE[j]) <;>
                  rw [hb] at hbit <;> simp at hbit
                · exact hbit
                · exact (hji (hunique j hbit)).elim]
            rw [Aux.generatorByteY_get, hpoint]
            exact ZMod.natCast_zmod_val y
  · intro hpointZero
    have hi0 : i.val = 0 := by
      by_contra hi0
      exact Reference.Aux.generator_nsmul_ne_zero hi0
        (i.isLt.trans (by native_decide : 256 < P256.scalarModulus))
        hpointZero
    have hieq : i = 0 := Fin.eq_of_val_eq hi0
    subst i
    have hzero : ∀ j : Fin 256, j ≠ 0 →
        ρ.int (indicators.intBits[j]) = 0 := by
      intro j hj
      have hbit := hi.1 j
      cases hb : ρ.bool (indicators.bits.bitsLE[j]) <;>
        rw [hb] at hbit <;> simp at hbit
      · exact hbit
      · exact (hj (hunique j hbit)).elim
    constructor
    · unfold Modular.Lazy.evalZMod
      simp only [Freigen.F2Z.Valuation.finset_sum, map_nsmul, nsmul_eq_mul]
      rw [Aux.sum_mul_oneHot _ _ 0 (by simpa using hone) hzero]
      rw [Aux.generatorByteX_get]
      norm_num [Reference.xNat]
    · unfold Modular.Lazy.evalZMod
      simp only [Freigen.F2Z.Valuation.finset_sum, map_nsmul, nsmul_eq_mul]
      rw [Aux.sum_mul_oneHot _ _ 0 (by simpa using hone) hzero]
      rw [Aux.generatorByteY_get]
      norm_num [Reference.yNat]

@[spec] theorem lookupGeneratorByte_complete {digit : LC ℤ}
    (hd0 : 0 ≤ ρ.int (digit)) (hdlt : ρ.int (digit) < 256) :
    ⦃⌜True⌝⦄ Complete.interp ρ (lookupGeneratorByte digit)
    ⦃⇓ out => ⌜out.Valid ρ ∧ ∃ i : Fin 256,
      ρ.int (digit) = i.val ∧
        P256.Reference.NormalizedRep ρ out
          (i.val • P256.Reference.generator)⌝⦄ := by
  mvcgen [lookupGeneratorByte]
  case vc3.success =>
    rename_i indicators hi
    rcases hi.2 with ⟨i, hone, hdigit, hunique⟩
    have hbit (j : Fin 256) :
        ρ.int (indicators.intBits[j]) = 0 ∨
          ρ.int (indicators.intBits[j]) = 1 := by
      have hj := hi.1 j
      cases hb : ρ.bool (indicators.bits.bitsLE[j]) <;>
        rw [hb] at hj <;> simp at hj
      · exact Or.inl hj
      · exact Or.inr hj
    have hzero (j : Fin 256) (hji : j ≠ i) :
        ρ.int (indicators.intBits[j]) = 0 :=
      (hbit j).resolve_right fun hj => hji (hunique j hj)
    have hxval :
        (∑ j : Fin 256, (generatorByteX[j] : ℤ) *
          ρ.int (indicators.intBits[j])) = generatorByteX[i] :=
      Aux.sum_mul_oneHot _ _ i hone hzero
    have hyval :
        (∑ j : Fin 256, (generatorByteY[j] : ℤ) *
          ρ.int (indicators.intBits[j])) = generatorByteY[i] :=
      Aux.sum_mul_oneHot _ _ i hone hzero
    have hxnonneg : 0 ≤ (generatorByteX[i] : ℤ) := by omega
    have hynonneg : 0 ≤ (generatorByteY[i] : ℤ) := by omega
    have hxlt : (generatorByteX[i] : ℤ) < P256.base.modulus := by
      rw [Aux.generatorByteX_get]
      rcases hpoint : i.val • P256.Reference.generator with _ | ⟨x, y, hxy⟩
      · simp [Reference.xNat]
        exact_mod_cast P256.base.positive
      · simp only [Reference.xNat]
        exact_mod_cast x.val_lt
    have hylt : (generatorByteY[i] : ℤ) < P256.base.modulus := by
      rw [Aux.generatorByteY_get]
      rcases hpoint : i.val • P256.Reference.generator with _ | ⟨x, y, hxy⟩
      · simp [Reference.yNat]
        exact_mod_cast P256.base.positive
      · simp only [Reference.yNat]
        exact_mod_cast y.val_lt
    let xLC : LC ℤ := ∑ j : Fin 256,
      generatorByteX[j] • indicators.intBits[j]
    let yLC : LC ℤ := ∑ j : Fin 256,
      generatorByteY[j] • indicators.intBits[j]
    have hXValid :
        ({ intVal := xLC, bound := 2 } : P256.AffineSlope.Rep).Valid ρ := by
      unfold Modular.Lazy.Rep.Valid
      simp only [xLC, Freigen.F2Z.Valuation.finset_sum, map_nsmul, nsmul_eq_mul]
      rw [hxval]
      refine ⟨hxnonneg, hxlt.trans ?_⟩
      have hp : (0 : ℤ) < P256.base.modulus := by
        exact_mod_cast P256.base.positive
      push_cast
      omega
    have hYValid :
        ({ intVal := yLC, bound := 2 } : P256.AffineSlope.Rep).Valid ρ := by
      unfold Modular.Lazy.Rep.Valid
      simp only [yLC, Freigen.F2Z.Valuation.finset_sum, map_nsmul, nsmul_eq_mul]
      rw [hyval]
      refine ⟨hynonneg, hylt.trans ?_⟩
      have hp : (0 : ℤ) < P256.base.modulus := by
        exact_mod_cast P256.base.positive
      push_cast
      omega
    have hxLClt : ρ.int (xLC) < P256.base.modulus := by
      simp only [xLC, Freigen.F2Z.Valuation.finset_sum, map_nsmul, nsmul_eq_mul]
      rw [hxval]
      exact hxlt
    have hyLClt : ρ.int (yLC) < P256.base.modulus := by
      simp only [yLC, Freigen.F2Z.Valuation.finset_sum, map_nsmul, nsmul_eq_mul]
      rw [hyval]
      exact hylt
    constructor
    · unfold P256.AffineSlope.Point.Valid
      dsimp only
      constructor
      · rfl
      constructor
      · exact hXValid
      constructor
      · exact hxLClt
      constructor
      · rfl
      constructor
      · exact hYValid
      constructor
      · exact hyLClt
      · exact hbit 0
    · refine ⟨i, hdigit, ?_⟩
      constructor
      · unfold P256.Reference.Represents
        constructor
        · exact hbit 0
        · unfold P256.Reference.circuitCoordinates
          by_cases hi0 : i.val = 0
          · have hieq : i = 0 := Fin.eq_of_val_eq hi0
            subst i
            simp only [P256.Reference.coordinates,
              if_pos (by simpa using hone)]
            constructor
          · have hzero0 : ρ.int (indicators.intBits[0]) = 0 :=
              hzero 0 (by
                intro h
                apply hi0
                exact (congrArg Fin.val h).symm)
            rw [if_neg (show ρ.int (indicators.intBits[0]) ≠ 1 by
              omega)]
            have hnonzero := Reference.Aux.generator_nsmul_ne_zero hi0
              (i.isLt.trans
                (by native_decide : 256 < P256.scalarModulus))
            rcases hpoint : i.val • P256.Reference.generator with
              _ | ⟨x, y, hxy⟩
            · exact (hnonzero hpoint).elim
            · simp only [P256.Reference.coordinates]
              congr 1
              · unfold Modular.Lazy.evalZMod
                simp only [Freigen.F2Z.Valuation.finset_sum, map_nsmul, nsmul_eq_mul]
                rw [hxval, Aux.generatorByteX_get, hpoint]
                exact ZMod.natCast_zmod_val x
              · unfold Modular.Lazy.evalZMod
                simp only [Freigen.F2Z.Valuation.finset_sum, map_nsmul, nsmul_eq_mul]
                rw [hyval, Aux.generatorByteY_get, hpoint]
                exact ZMod.natCast_zmod_val y
      · intro hpointZero
        have hi0 : i.val = 0 := by
          by_contra hi0
          exact Reference.Aux.generator_nsmul_ne_zero hi0
            (i.isLt.trans
              (by native_decide : 256 < P256.scalarModulus)) hpointZero
        have hieq : i = 0 := Fin.eq_of_val_eq hi0
        subst i
        constructor
        · unfold Modular.Lazy.evalZMod
          simp only [Freigen.F2Z.Valuation.finset_sum, map_nsmul, nsmul_eq_mul]
          rw [hxval, Aux.generatorByteX_get]
          norm_num [Reference.xNat]
        · unfold Modular.Lazy.evalZMod
          simp only [Freigen.F2Z.Valuation.finset_sum, map_nsmul, nsmul_eq_mul]
          rw [hyval, Aux.generatorByteY_get]
          norm_num [Reference.yNat]

@[spec] theorem doubleStep_sound {P : P256.AffineSlope.Point}
    {p : P256.Reference.Point} {k : Nat}
    (hP : P256.Reference.NormalizedRep ρ P (k • p)) :
    ⦃⌜True⌝⦄ Sound.interp ρ (doubleStep k P)
    ⦃⇓ out => ⌜P256.Reference.NormalizedRep ρ out ((k + k) • p)⌝⦄ := by
  unfold doubleStep
  apply Triple.iff_conseq.mp
    (P256.AffineSlope.doubleComplete_sound_mathlib hP) (by simp)
  simp only [PostCond.entails, SPred.entails_nil]
  exact ⟨fun _ h => by simpa only [add_nsmul] using h,
    ExceptConds.entails.refl _⟩

@[spec] theorem doubleStep_complete {P : P256.AffineSlope.Point}
    {p : P256.Reference.Point} {k : Nat}
    (hvalid : P.Valid ρ)
    (hP : P256.Reference.NormalizedRep ρ P p)
    (horder : P256.scalarModulus • p = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (doubleStep k P)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      P256.Reference.NormalizedRep ρ out (p + p)⌝⦄ := by
  unfold doubleStep
  exact P256.AffineSlope.doubleComplete_complete_mathlib hvalid hP
    (Reference.Aux.no_two_torsion_of_order horder)

private theorem complete_of_pure_pre {alpha : Type} {P : Prop}
    {c : Circuit alpha} {Q : PostCond alpha (.except PUnit .pure)}
    (h : P → ⦃⌜True⌝⦄ Complete.interp ρ c ⦃Q⦄) :
    ⦃⌜P⌝⦄ Complete.interp ρ c ⦃Q⦄ := by
  rw [Triple.iff]
  simp only [SPred.entails_nil, SPred.down_pure_nil]
  intro hP
  have ht := h hP
  rw [Triple.iff] at ht
  simp only [SPred.entails_nil, SPred.down_pure_nil] at ht
  exact ht True.intro

@[spec] theorem doublePair_sound {P : P256.AffineSlope.Point}
    {p : P256.Reference.Point}
    (hP : P256.Reference.NormalizedRep ρ P p) :
  ⦃⌜True⌝⦄ Sound.interp ρ (doublePair P)
    ⦃⇓ out => ⌜P256.Reference.NormalizedRep ρ out (4 • p)⌝⦄ := by
  mvcgen -trivial [doublePair]
  case vc1.p => exact p
  all_goals simpa [one_nsmul, add_nsmul] using hP

@[spec] theorem doublePair_complete {P : P256.AffineSlope.Point}
    {p : P256.Reference.Point}
    (hvalid : P.Valid ρ)
    (hP : P256.Reference.NormalizedRep ρ P p)
    (horder : P256.scalarModulus • p = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (doublePair P)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      P256.Reference.NormalizedRep ρ out (4 • p)⌝⦄ := by
  mvcgen -trivial [doublePair]
  all_goals first
    | exact p
    | exact hvalid
    | exact hP
    | exact horder
    | exact Reference.Aux.order_add horder horder
    | assumption
    | skip
  case vc7 =>
    intro _ _
    exact Reference.Aux.order_add horder horder
  all_goals try simp_all

@[spec] theorem doubleFour_sound {P : P256.AffineSlope.Point}
    {p : P256.Reference.Point}
    (hP : P256.Reference.NormalizedRep ρ P p) :
  ⦃⌜True⌝⦄ Sound.interp ρ (doubleFour P)
    ⦃⇓ out => ⌜P256.Reference.NormalizedRep ρ out (16 • p)⌝⦄ := by
  mvcgen -trivial [doubleFour]
  case vc3 =>
    intro h
    rw [show 4 = 2 + 2 by omega, add_nsmul, two_nsmul] at h
    exact h
  all_goals first
    | exact p
    | simpa [smul_smul] using hP

@[spec] theorem doubleFour_complete {P : P256.AffineSlope.Point}
    {p : P256.Reference.Point}
    (hvalid : P.Valid ρ)
    (hP : P256.Reference.NormalizedRep ρ P p)
    (horder : P256.scalarModulus • p = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (doubleFour P)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      P256.Reference.NormalizedRep ρ out (16 • p)⌝⦄ := by
  mvcgen -trivial [doubleFour]
  case vc6 =>
    intro _ h
    rw [show 4 = 2 + 2 by omega, add_nsmul, two_nsmul] at h
    exact h
  case vc7 =>
    intro _ _
    have hp2 := Reference.Aux.order_add horder horder
    exact Reference.Aux.order_add hp2 hp2
  all_goals first
    | exact p
    | exact hvalid
    | exact hP
    | exact horder
    | exact Reference.Aux.order_nsmul horder 4
    | assumption
    | skip
  all_goals try simp_all

def byteValue (ρ : WF.Valuation) (k : P256.Fn) (i : Nat) : Nat :=
  (BitVec.extractLsb' (248 - 8 * i) 8 (k.val.eval ρ)).toNat

def digitValue (ρ : WF.Valuation) (k : P256.Fn) (i : Nat) : Nat :=
  (BitVec.extractLsb' (252 - 4 * i) 4 (k.val.eval ρ)).toNat

def JointStepPoint (ρ : WF.Valuation) (u1 u2 : P256.Fn) (i : Nat)
    (acc q : P256.Reference.Point) : P256.Reference.Point :=
  256 • acc +
    (16 * digitValue ρ u2 (2 * i) + digitValue ρ u2 (2 * i + 1)) • q +
    byteValue ρ u1 i • P256.Reference.generator

def JointTermsSpec (rho : WF.Valuation) (u1 u2 : P256.Fn) (i : Nat)
    (q : P256.Reference.Point) (terms : JointTerms) : Prop :=
  P256.Reference.NormalizedRep rho terms.qhi
      (digitValue rho u2 (2 * i) • q) ∧
    P256.Reference.NormalizedRep rho terms.qlo
      (digitValue rho u2 (2 * i + 1) • q) ∧
    P256.Reference.NormalizedRep rho terms.g
      (byteValue rho u1 i • P256.Reference.generator)

@[spec] theorem selectJointTerms_sound {u1 u2 : P256.Fn}
    {qTable : Vector P256.AffineSlope.Point 16}
    {i : Nat} {hi : i < 32} {q : P256.Reference.Point}
    (hu1 : u1.val.Valid ρ) (hu2 : u2.val.Valid ρ)
    (htable : ∀ j : Fin 16,
      P256.Reference.NormalizedRep ρ qTable[j] (j.val • q)) :
    ⦃⌜True⌝⦄ Sound.interp ρ (selectJointTerms u1 u2 qTable i hi)
    ⦃⇓ terms => ⌜JointTermsSpec ρ u1 u2 i q terms⌝⦄ := by
  mvcgen [selectJointTerms]
  rename_i d1 hd1 d2hi hd2hi d2lo hd2lo qhi hqhi qlo hqlo g hg
  rcases hqhi with ⟨jhi, hjhi, hqhi⟩
  rcases hqlo with ⟨jlo, hjlo, hqlo⟩
  rcases hg with ⟨jg, hjg, hg⟩
  unfold JointTermsSpec
  have hjhi' : jhi.val = digitValue ρ u2 (2 * i) := by
    unfold digitValue
    unfold WindowDigitSpec at hd2hi
    omega
  have hjlo' : jlo.val = digitValue ρ u2 (2 * i + 1) := by
    unfold digitValue
    unfold WindowDigitSpec at hd2lo
    omega
  have hjg' : jg.val = byteValue ρ u1 i := by
    unfold byteValue
    unfold WindowByteSpec at hd1
    omega
  simpa only [hjhi', hjlo', hjg'] using And.intro hqhi (And.intro hqlo hg)

@[spec] theorem selectJointTerms_complete {u1 u2 : P256.Fn}
    {qTable : Vector P256.AffineSlope.Point 16}
    {i : Nat} {hi : i < 32} {q : P256.Reference.Point}
    (hu1 : u1.val.Valid ρ) (hu2 : u2.val.Valid ρ)
    (htableValid : ∀ j : Fin 16, qTable[j].Valid ρ)
    (htable : ∀ j : Fin 16,
      P256.Reference.NormalizedRep ρ qTable[j] (j.val • q)) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (selectJointTerms u1 u2 qTable i hi)
    ⦃⇓ terms => ⌜terms.qhi.Valid ρ ∧ terms.qlo.Valid ρ ∧
      terms.g.Valid ρ ∧ JointTermsSpec ρ u1 u2 i q terms⌝⦄ := by
  mvcgen [selectJointTerms]
  all_goals first
    | exact WindowByteSpec.nonneg (by assumption)
    | exact WindowByteSpec.lt (by assumption)
    | exact WindowDigitSpec.nonneg (by assumption)
    | exact WindowDigitSpec.lt (by assumption)
    | exact htableValid
    | exact htable
    | aesop
    | skip
  have hjhi' : w.val = digitValue ρ u2 (2 * i) := by
    unfold digitValue
    unfold WindowDigitSpec at h_1
    omega
  have hjlo' : w_1.val = digitValue ρ u2 (2 * i + 1) := by
    unfold digitValue
    unfold WindowDigitSpec at h_2
    omega
  have hjg' : w_2.val = byteValue ρ u1 i := by
    unfold byteValue
    unfold WindowByteSpec at h
    omega
  unfold JointTermsSpec
  simpa only [hjhi', hjlo', hjg'] using
    And.intro right (And.intro right_1 right_2)

private theorem sound_of_pure_pre {alpha : Type} {P : Prop}
    {c : Circuit alpha} {Q : PostCond alpha .pure}
    (h : P → ⦃⌜True⌝⦄ Sound.interp ρ c ⦃Q⦄) :
    ⦃⌜P⌝⦄ Sound.interp ρ c ⦃Q⦄ := by
  rw [Triple.iff]
  simp only [SPred.entails_nil, SPred.down_pure_nil]
  intro hP
  have ht := h hP
  rw [Triple.iff] at ht
  simp only [SPred.entails_nil, SPred.down_pure_nil] at ht
  exact ht True.intro

@[spec] theorem accumulateJoint_sound {acc : P256.AffineSlope.Point}
    {terms : JointTerms} {accPoint qhi qlo g : P256.Reference.Point}
    (hacc : P256.Reference.NormalizedRep ρ acc accPoint)
    (hqhi : P256.Reference.NormalizedRep ρ terms.qhi qhi)
    (hqlo : P256.Reference.NormalizedRep ρ terms.qlo qlo)
    (hg : P256.Reference.NormalizedRep ρ terms.g g) :
    ⦃⌜True⌝⦄ Sound.interp ρ (accumulateJoint acc terms)
    ⦃⇓ out => ⌜P256.Reference.NormalizedRep ρ out
      (256 • accPoint + 16 • qhi + qlo + g)⌝⦄ := by
  unfold accumulateJoint
  rw [Sound.interp_bind]
  apply Triple.bind (Q := fun acc16 =>
    ⌜P256.Reference.NormalizedRep ρ acc16 (16 • accPoint)⌝)
  case hx => exact doubleFour_sound hacc
  case hf =>
    intro acc16
    apply sound_of_pure_pre
    intro hacc16
    rw [Sound.interp_bind]
    apply Triple.bind (Q := fun accHi =>
      ⌜P256.Reference.NormalizedRep ρ accHi
        (16 • accPoint + qhi)⌝)
    case hx =>
      exact P256.AffineSlope.addComplete_sound_normalized hacc16 hqhi
    case hf =>
      intro accHi
      apply sound_of_pure_pre
      intro haccHi
      rw [Sound.interp_bind]
      apply Triple.bind (Q := fun acc256 =>
        ⌜P256.Reference.NormalizedRep ρ acc256
          (16 • (16 • accPoint + qhi))⌝)
      case hx => exact doubleFour_sound haccHi
      case hf =>
        intro acc256
        apply sound_of_pure_pre
        intro hacc256
        rw [Sound.interp_bind]
        apply Triple.bind (Q := fun accQ =>
          ⌜P256.Reference.NormalizedRep ρ accQ
            (16 • (16 • accPoint + qhi) + qlo)⌝)
        case hx =>
          exact P256.AffineSlope.addComplete_sound_normalized hacc256 hqlo
        case hf =>
          intro accQ
          apply sound_of_pure_pre
          intro haccQ
          apply Triple.iff_conseq.mp
            (P256.AffineSlope.addComplete_sound_normalized haccQ hg)
            (by simp)
          simp only [PostCond.entails, SPred.entails_nil]
          exact ⟨fun _ hout => by
            have hn : 16 • (16 • accPoint) = 256 • accPoint := by
              rw [← mul_nsmul]
            have heq : 16 • (16 • accPoint + qhi) + qlo + g =
                256 • accPoint + 16 • qhi + qlo + g := by
              rw [nsmul_add, hn]
            rw [heq] at hout
            exact hout,
            ExceptConds.entails.refl _⟩

@[spec] theorem accumulateJoint_complete {acc : P256.AffineSlope.Point}
    {terms : JointTerms} {accPoint qhi qlo g : P256.Reference.Point}
    (haccValid : acc.Valid ρ)
    (hqhiValid : terms.qhi.Valid ρ)
    (hqloValid : terms.qlo.Valid ρ)
    (hgValid : terms.g.Valid ρ)
    (hacc : P256.Reference.NormalizedRep ρ acc accPoint)
    (hqhi : P256.Reference.NormalizedRep ρ terms.qhi qhi)
    (hqlo : P256.Reference.NormalizedRep ρ terms.qlo qlo)
    (hg : P256.Reference.NormalizedRep ρ terms.g g)
    (haccOrder : P256.scalarModulus • accPoint = 0)
    (hqhiOrder : P256.scalarModulus • qhi = 0)
    (hqloOrder : P256.scalarModulus • qlo = 0)
    (_hgOrder : P256.scalarModulus • g = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (accumulateJoint acc terms)
    ⦃⇓ out => ⌜out.Valid ρ ∧ P256.Reference.NormalizedRep ρ out
      (256 • accPoint + 16 • qhi + qlo + g)⌝⦄ := by
  unfold accumulateJoint
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun acc16 => ⌜acc16.Valid ρ ∧
    P256.Reference.NormalizedRep ρ acc16 (16 • accPoint)⌝)
  case hx => exact doubleFour_complete haccValid hacc haccOrder
  case hf =>
    intro acc16
    apply complete_of_pure_pre
    rintro ⟨hacc16Valid, hacc16⟩
    rw [Complete.interp_bind]
    apply Triple.bind (Q := fun accHi => ⌜accHi.Valid ρ ∧
      P256.Reference.NormalizedRep ρ accHi (16 • accPoint + qhi)⌝)
    case hx =>
      exact P256.AffineSlope.addComplete_complete_mathlib
        hacc16Valid hqhiValid hacc16 hqhi
        (Reference.Aux.no_two_torsion_of_order
          (Reference.Aux.order_nsmul haccOrder 16))
    case hf =>
      intro accHi
      apply complete_of_pure_pre
      rintro ⟨haccHiValid, haccHi⟩
      rw [Complete.interp_bind]
      apply Triple.bind (Q := fun acc256 => ⌜acc256.Valid ρ ∧
        P256.Reference.NormalizedRep ρ acc256
          (16 • (16 • accPoint + qhi))⌝)
      case hx =>
        exact doubleFour_complete haccHiValid haccHi
          (Reference.Aux.order_add
            (Reference.Aux.order_nsmul haccOrder 16) hqhiOrder)
      case hf =>
        intro acc256
        apply complete_of_pure_pre
        rintro ⟨hacc256Valid, hacc256⟩
        rw [Complete.interp_bind]
        apply Triple.bind (Q := fun accQ => ⌜accQ.Valid ρ ∧
          P256.Reference.NormalizedRep ρ accQ
            (16 • (16 • accPoint + qhi) + qlo)⌝)
        case hx =>
          exact P256.AffineSlope.addComplete_complete_mathlib
            hacc256Valid hqloValid hacc256 hqlo
            (Reference.Aux.no_two_torsion_of_order
              (Reference.Aux.order_nsmul
                (Reference.Aux.order_add
                  (Reference.Aux.order_nsmul haccOrder 16) hqhiOrder) 16))
        case hf =>
          intro accQ
          apply complete_of_pure_pre
          rintro ⟨haccQValid, haccQ⟩
          apply Triple.iff_conseq.mp
            (P256.AffineSlope.addComplete_complete_mathlib
              haccQValid hgValid haccQ hg
              (Reference.Aux.no_two_torsion_of_order
                (Reference.Aux.order_add
                  (Reference.Aux.order_nsmul
                    (Reference.Aux.order_add
                      (Reference.Aux.order_nsmul haccOrder 16)
                      hqhiOrder) 16) hqloOrder))) (by simp)
          simp only [PostCond.entails, SPred.entails_nil]
          exact ⟨fun _ hout => ⟨hout.1, by
            have hn : 16 • (16 • accPoint) = 256 • accPoint := by
              rw [← mul_nsmul]
            have heq : 16 • (16 • accPoint + qhi) + qlo + g =
                256 • accPoint + 16 • qhi + qlo + g := by
              rw [nsmul_add, hn]
            rw [heq] at hout
            exact hout.2⟩,
            ExceptConds.entails.refl _⟩

@[spec] theorem jointByteStep_sound {u1 u2 : P256.Fn}
    {qTable : Vector P256.AffineSlope.Point 16}
    {i : Nat} {hi : i < 32} {acc : P256.AffineSlope.Point}
    {accPoint q : P256.Reference.Point}
    (hu1 : u1.val.Valid ρ) (hu2 : u2.val.Valid ρ)
    (hacc : P256.Reference.NormalizedRep ρ acc accPoint)
    (htable : ∀ j : Fin 16,
      P256.Reference.NormalizedRep ρ qTable[j] (j.val • q)) :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (jointByteStep u1 u2 qTable i hi acc)
    ⦃⇓ out => ⌜P256.Reference.NormalizedRep ρ out
      (JointStepPoint ρ u1 u2 i accPoint q)⌝⦄ := by
  unfold jointByteStep
  rw [Sound.interp_bind]
  apply Triple.bind (Q := fun terms =>
    ⌜JointTermsSpec ρ u1 u2 i q terms⌝)
  case hx => exact selectJointTerms_sound hu1 hu2 htable
  case hf =>
    intro terms
    apply sound_of_pure_pre
    intro hterms
    rcases hterms with ⟨hqhi, hqlo, hg⟩
    apply Triple.iff_conseq.mp
      (accumulateJoint_sound hacc hqhi hqlo hg) (by simp)
    simp only [PostCond.entails, SPred.entails_nil]
    exact ⟨fun _ hout => by
      have hmul : 16 • (digitValue ρ u2 (2 * i) • q) =
          (16 * digitValue ρ u2 (2 * i)) • q := by
        rw [show 16 * digitValue ρ u2 (2 * i) =
            digitValue ρ u2 (2 * i) * 16 by omega,
          mul_nsmul]
      rw [hmul] at hout
      unfold JointStepPoint
      simpa only [add_nsmul, add_assoc] using hout,
      ExceptConds.entails.refl _⟩

@[spec] theorem jointByteStep_complete {u1 u2 : P256.Fn}
    {qTable : Vector P256.AffineSlope.Point 16}
    {i : Nat} {hi : i < 32} {acc : P256.AffineSlope.Point}
    {accPoint q : P256.Reference.Point}
    (hu1 : u1.val.Valid ρ) (hu2 : u2.val.Valid ρ)
    (haccValid : acc.Valid ρ)
    (hacc : P256.Reference.NormalizedRep ρ acc accPoint)
    (haccOrder : P256.scalarModulus • accPoint = 0)
    (htableValid : ∀ j : Fin 16, qTable[j].Valid ρ)
    (htable : ∀ j : Fin 16,
      P256.Reference.NormalizedRep ρ qTable[j] (j.val • q))
    (hqOrder : P256.scalarModulus • q = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (jointByteStep u1 u2 qTable i hi acc)
    ⦃⇓ out => ⌜out.Valid ρ ∧ P256.Reference.NormalizedRep ρ out
      (JointStepPoint ρ u1 u2 i accPoint q)⌝⦄ := by
  unfold jointByteStep
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun terms => ⌜terms.qhi.Valid ρ ∧
    terms.qlo.Valid ρ ∧ terms.g.Valid ρ ∧
      JointTermsSpec ρ u1 u2 i q terms⌝)
  case hx => exact selectJointTerms_complete hu1 hu2 htableValid htable
  case hf =>
    intro terms
    apply complete_of_pure_pre
    rintro ⟨hqhiValid, hqloValid, hgValid, hqhi, hqlo, hg⟩
    apply Triple.iff_conseq.mp
      (accumulateJoint_complete haccValid hqhiValid hqloValid hgValid
        hacc hqhi hqlo hg haccOrder
        (Reference.Aux.order_nsmul hqOrder (digitValue ρ u2 (2 * i)))
        (Reference.Aux.order_nsmul hqOrder
          (digitValue ρ u2 (2 * i + 1)))
        (Reference.Aux.order_nsmul Reference.Aux.generator_order
          (byteValue ρ u1 i))) (by simp)
    simp only [PostCond.entails, SPred.entails_nil]
    exact ⟨fun _ hout => ⟨hout.1, by
      have hmul : 16 • (digitValue ρ u2 (2 * i) • q) =
          (16 * digitValue ρ u2 (2 * i)) • q := by
        rw [show 16 * digitValue ρ u2 (2 * i) =
            digitValue ρ u2 (2 * i) * 16 by omega,
          mul_nsmul]
      rw [hmul] at hout
      unfold JointStepPoint
      simpa only [add_nsmul, add_assoc] using hout.2⟩,
      ExceptConds.entails.refl _⟩

def JointFoldPoint (rho : WF.Valuation) (u1 u2 : P256.Fn)
    (q : P256.Reference.Point) (indices : List Nat) : P256.Reference.Point :=
  indices.foldl (fun acc i => JointStepPoint rho u1 u2 i acc q) 0

theorem JointStepPoint.order {u1 u2 : P256.Fn} {i : Nat}
    {acc q : P256.Reference.Point}
    (hacc : P256.scalarModulus • acc = 0)
    (hq : P256.scalarModulus • q = 0) :
    P256.scalarModulus • JointStepPoint ρ u1 u2 i acc q = 0 := by
  exact Reference.Aux.order_add
    (Reference.Aux.order_add
      (Reference.Aux.order_nsmul hacc 256)
      (Reference.Aux.order_nsmul hq
        (16 * digitValue ρ u2 (2 * i) +
          digitValue ρ u2 (2 * i + 1))))
    (Reference.Aux.order_nsmul Reference.Aux.generator_order
      (byteValue ρ u1 i))

theorem affineInfinity_valid : P256.AffineSlope.infinity.Valid ρ := by
  have hz : P256.zero.Valid ρ :=
    Modular.ofNat_valid P256.base 0 (by native_decide) (by native_decide)
  exact ⟨rfl, Modular.Lazy.ofElem_valid P256.base hz, hz.2,
    rfl, Modular.Lazy.ofElem_valid P256.base hz, hz.2,
    by simp [P256.AffineSlope.infinity]⟩

@[spec] theorem jointScalarMul_sound {u1 u2 : P256.Fn}
    {Q : P256.Projective} {q : P256.Reference.Point}
    (hu1 : u1.val.Valid ρ) (hu2 : u2.val.Valid ρ)
    (hQ : P256.Reference.Represents ρ
      (P256.AffineSlope.ofElems Q.X Q.Y) q) :
    ⦃⌜True⌝⦄ Sound.interp ρ (jointScalarMul u1 u2 Q)
    ⦃⇓ out => ⌜P256.Reference.NormalizedRep ρ out
      (JointFoldPoint ρ u1 u2 q [:32].toList)⌝⦄ := by
  mvcgen -trivial [jointScalarMul, WF.foldRange] invariants
  · ⇓⟨cur, out⟩ => ⌜P256.Reference.NormalizedRep ρ out
      (JointFoldPoint ρ u1 u2 q cur.prefix)⌝
  case vc1.q => exact q
  case vc2.hP => exact hQ
  case vc3.accPoint pref cur suff hsplit b hprev =>
    exact JointFoldPoint ρ u1 u2 q pref
  case vc4.q => exact q
  case vc5.hu1 => exact hu1
  case vc6.hu2 => exact hu2
  case vc7.hacc => assumption
  case vc8.htable => assumption
  case vc9.success pref cur hstep =>
    unfold JointFoldPoint at hstep ⊢
    rw [List.foldl_append]
    simpa using hstep
  case vc10.pre =>
    simp [JointFoldPoint, P256.Reference.NormalizedRep,
      P256.Reference.Represents, P256.Reference.circuitCoordinates,
      P256.Reference.coordinates, P256.AffineSlope.infinity]
  case vc11.post.success => exact fun h => h

@[spec] theorem jointScalarMul_complete {u1 u2 : P256.Fn}
    {Q : P256.Projective} {q : P256.Reference.Point}
    (hu1 : u1.val.Valid ρ) (hu2 : u2.val.Valid ρ)
    (hQvalid : Q.Valid ρ)
    (hQ : P256.Reference.Represents ρ
      (P256.AffineSlope.ofElems Q.X Q.Y) q)
    (hqOrder : P256.scalarModulus • q = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (jointScalarMul u1 u2 Q)
    ⦃⇓ out => ⌜out.Valid ρ ∧ P256.Reference.NormalizedRep ρ out
      (JointFoldPoint ρ u1 u2 q [:32].toList)⌝⦄ := by
  mvcgen -trivial [jointScalarMul, WF.foldRange] invariants
  · ⇓⟨cur, out⟩ => ⌜out.Valid ρ ∧
      P256.Reference.NormalizedRep ρ out
        (JointFoldPoint ρ u1 u2 q cur.prefix) ∧
      P256.scalarModulus •
        JointFoldPoint ρ u1 u2 q cur.prefix = 0⌝
  case vc1.q => exact q
  case vc2.hPvalid => exact hQvalid
  case vc3.hP => exact hQ
  case vc4.horder => exact hqOrder
  case vc5.accPoint pref cur suff hsplit b hprev =>
    exact JointFoldPoint ρ u1 u2 q pref
  case vc6.q => exact q
  case vc7.hu1 => exact hu1
  case vc8.hu2 => exact hu2
  case vc9.haccValid => exact (by aesop)
  case vc10.hacc => exact (by aesop)
  case vc11.haccOrder => exact (by aesop)
  case vc12.htableValid j => exact (by aesop)
  case vc13.htable => exact (by aesop)
  case vc14.hqOrder => exact hqOrder
  case vc15.success pref cur hstep =>
    rename_i table htable suff hsplit acc hprev
    refine ⟨hstep.1, ?_, ?_⟩
    · unfold JointFoldPoint at hstep ⊢
      rw [List.foldl_append]
      simpa using hstep.2
    · unfold JointFoldPoint
      rw [List.foldl_append]
      exact JointStepPoint.order (ρ := ρ) (i := suff) pref.2.2 hqOrder
  case vc16.pre =>
    refine ⟨affineInfinity_valid, ?_, ?_⟩
    · simp [JointFoldPoint, P256.Reference.NormalizedRep,
        P256.Reference.Represents, P256.Reference.circuitCoordinates,
        P256.Reference.coordinates, P256.AffineSlope.infinity]
    · simp [JointFoldPoint]
  case vc17.post.success =>
    intro hvalid hnormalized _
    exact ⟨hvalid, hnormalized⟩

def scalarPrefix (rho : WF.Valuation) (k : P256.Fn) (count : Nat) : Nat :=
  (k.val.eval rho).toNat / 2 ^ (256 - 8 * count)

theorem digitPair_eq_byteValue {k : P256.Fn} {i : Nat} (hi : i < 32) :
    16 * digitValue ρ k (2 * i) + digitValue ρ k (2 * i + 1) =
      byteValue ρ k i := by
  unfold digitValue byteValue
  simp only [BitVec.extractLsb'_toNat, Nat.reducePow]
  rw [show 252 - 4 * (2 * i) = (248 - 8 * i) + 4 by omega,
    show 252 - 4 * (2 * i + 1) = 248 - 8 * i by omega,
    Nat.shiftRight_add]
  omega

theorem scalarPrefix_zero (k : P256.Fn) : scalarPrefix ρ k 0 = 0 := by
  unfold scalarPrefix
  norm_num
  exact (k.val.eval ρ).isLt

theorem scalarPrefix_succ {k : P256.Fn} {i : Nat} (hi : i < 32) :
    scalarPrefix ρ k (i + 1) =
      256 * scalarPrefix ρ k i + byteValue ρ k i := by
  unfold scalarPrefix byteValue
  simp only [BitVec.extractLsb'_toNat, Nat.reducePow]
  rw [show 256 - 8 * i = (248 - 8 * i) + 8 by omega,
    show 256 - 8 * (i + 1) = 248 - 8 * i by omega,
    Nat.shiftRight_eq_div_pow, pow_add]
  norm_num
  rw [← Nat.div_div_eq_div_mul]
  exact (Nat.div_add_mod _ 256).symm

theorem scalarPrefix_full (k : P256.Fn) :
    scalarPrefix ρ k 32 = (k.val.eval ρ).toNat := by
  simp [scalarPrefix]

private theorem nsmul_commute (m n : Nat) (P : P256.Reference.Point) :
    m • (n • P) = n • (m • P) := by
  rw [← mul_nsmul, ← mul_nsmul, Nat.mul_comm]

theorem JointFoldPoint_range (u1 u2 : P256.Fn)
    (q : P256.Reference.Point) {count : Nat} (hcount : count ≤ 32) :
    JointFoldPoint ρ u1 u2 q (List.range count) =
      scalarPrefix ρ u1 count • P256.Reference.generator +
        scalarPrefix ρ u2 count • q := by
  induction count with
  | zero =>
      simp [JointFoldPoint, scalarPrefix_zero]
  | succ count ih =>
      have hcount32 : count < 32 := by omega
      rw [List.range_succ, JointFoldPoint, List.foldl_append]
      change JointStepPoint ρ u1 u2 count
        (JointFoldPoint ρ u1 u2 q (List.range count)) q = _
      rw [ih (by omega)]
      unfold JointStepPoint
      rw [digitPair_eq_byteValue hcount32,
        scalarPrefix_succ hcount32, scalarPrefix_succ hcount32]
      simp only [nsmul_add, add_nsmul, mul_nsmul]
      rw [nsmul_commute 256 (scalarPrefix ρ u1 count),
        nsmul_commute 256 (scalarPrefix ρ u2 count)]
      abel

theorem JointFoldPoint_full (u1 u2 : P256.Fn)
    (q : P256.Reference.Point) :
    JointFoldPoint ρ u1 u2 q [:32].toList =
      (u1.val.eval ρ).toNat • P256.Reference.generator +
        (u2.val.eval ρ).toNat • q := by
  rw [show [:32].toList = List.range 32 by rfl,
    JointFoldPoint_range u1 u2 q (by omega),
    scalarPrefix_full, scalarPrefix_full]

theorem onCurveZModSpec_of_hasCoordinates {publicKey : Reference.Point}
    {qx qy : P256.Fp}
    (hcoords : Reference.HasCoordinates publicKey
      (Int.castRingHom P256.Reference.Field (ρ.int (qx.val.intVal)))
      (Int.castRingHom P256.Reference.Field (ρ.int (qy.val.intVal)))) :
    P256.Projective.Lazy.OnCurveZModSpec ρ qx qy := by
  rcases publicKey with _ | ⟨x, y, hxy⟩
  · simp [Reference.HasCoordinates, P256.Reference.coordinates] at hcoords
  · simp only [Reference.HasCoordinates, P256.Reference.coordinates] at hcoords
    rcases hcoords with ⟨rfl, rfl⟩
    unfold P256.Projective.Lazy.OnCurveZModSpec
    dsimp
    exact (P256.Reference.equation_iff_short _ _).1 hxy.1

theorem fnOne_valid : P256.fnOne.Valid ρ := by
  simpa [P256.fnOne, P256.fnConst] using
    (Modular.ofNat_valid (ρ := ρ) P256.scalar 1
      (by native_decide) (by native_decide))

theorem fnOne_evalNat : P256.fnOne.evalNat ρ = 1 := by
  simpa [P256.fnOne, P256.fnConst] using
    (Modular.ofNat_evalNat (ρ := ρ) P256.scalar 1
      (by native_decide) (by native_decide))

theorem baseOne_valid : P256.one.Valid ρ := by
  simpa [P256.one, P256.fpConst] using
    (Modular.ofNat_valid (ρ := ρ) P256.base 1
      (by native_decide) (by native_decide))

theorem ofElems_represents_of_hasCoordinates {qx qy : P256.Fp}
    {publicKey : Reference.Point}
    (hcoords : Reference.HasCoordinates publicKey
      (Int.castRingHom P256.Reference.Field (ρ.int (qx.val.intVal)))
      (Int.castRingHom P256.Reference.Field (ρ.int (qy.val.intVal)))) :
    P256.Reference.Represents ρ (P256.AffineSlope.ofElems qx qy)
      publicKey := by
  unfold P256.Reference.Represents
  constructor
  · simp [P256.AffineSlope.ofElems]
  · unfold P256.Reference.circuitCoordinates
    simpa [P256.AffineSlope.ofElems, Modular.Lazy.ofElem,
      Modular.Lazy.evalZMod] using hcoords.symm

theorem elem_evalNat_eq_u_eval {a : P256.Fn} {u : U 256}
    (_ha : a.Valid ρ) (hau : a.val = u) (hu : u.Valid ρ) :
    a.evalNat ρ = (u.eval ρ).toNat := by
  unfold Modular.Elem.evalNat
  rw [hau, U.intVal_eval_eq_eval_toNat u hu]
  simp

theorem elem_evalZMod_eq_cast {a : P256.Fn} (ha : a.Valid ρ) :
    Modular.Lazy.evalElemZMod P256.scalar a ρ =
      (a.evalNat ρ : ZMod P256.scalar.modulus) := by
  unfold Modular.Lazy.evalElemZMod
  rw [← Modular.Elem.evalNat_cast P256.scalar ha]
  rfl

theorem assertMulEqSpec_of_u_mul {a b : P256.Fn} {u v : U 256}
    (ha : a.Valid ρ) (hb : b.Valid ρ)
    (hau : a.val = u) (hbv : b.val = v)
    (hu : u.Valid ρ) (hv : v.Valid ρ)
    (hmul : ((u.eval ρ).toNat : Reference.Scalar) *
      ((v.eval ρ).toNat : Reference.Scalar) = 1) :
    Modular.Lazy.AssertMulEqZModSpec P256.scalar ρ
      (Modular.Lazy.ofElem P256.scalar a)
      (Modular.Lazy.ofElem P256.scalar b)
      (Modular.Lazy.ofElem P256.scalar P256.fnOne) := by
  unfold Modular.Lazy.AssertMulEqZModSpec
  simp only [Modular.Lazy.evalZMod_ofElem]
  rw [elem_evalZMod_eq_cast ha, elem_evalZMod_eq_cast hb,
    elem_evalZMod_eq_cast fnOne_valid, fnOne_evalNat,
    elem_evalNat_eq_u_eval ha hau hu,
    elem_evalNat_eq_u_eval hb hbv hv]
  exact hmul

theorem jointFoldPoint_eq_verificationPoint
    {digest : U 256} {sig : Signature}
    {r s sInv z u1Relaxed u2Relaxed u1 u2 : P256.Fn}
    (hdigest : digest.Valid ρ)
    (hr : r.Valid ρ) (hsInv : sInv.Valid ρ)
    (hu1 : u1.Valid ρ) (hu2 : u2.Valid ρ)
    (hrNat : r.evalNat ρ = (sig.r.eval ρ).toNat)
    (hsNat : s.evalNat ρ = (sig.s.eval ρ).toNat)
    (hsMul : (s.evalNat ρ : ZMod P256.scalar.modulus) *
      (sInv.evalNat ρ : ZMod P256.scalar.modulus) = 1)
    (hz : Modular.Lazy.evalElemZMod P256.scalar z ρ =
      Int.castRingHom (ZMod P256.scalar.modulus) (ρ.int (digest.intVal)))
    (hu1Relaxed : Modular.Lazy.evalElemZMod P256.scalar u1Relaxed ρ =
      Modular.Lazy.evalElemZMod P256.scalar z ρ *
        Modular.Lazy.evalElemZMod P256.scalar sInv ρ)
    (hu2Relaxed : Modular.Lazy.evalElemZMod P256.scalar u2Relaxed ρ =
      Modular.Lazy.evalElemZMod P256.scalar r ρ *
        Modular.Lazy.evalElemZMod P256.scalar sInv ρ)
    (hu1Canonical : Modular.Lazy.evalElemZMod P256.scalar u1 ρ =
      Modular.Lazy.evalElemZMod P256.scalar u1Relaxed ρ)
    (hu2Canonical : Modular.Lazy.evalElemZMod P256.scalar u2 ρ =
      Modular.Lazy.evalElemZMod P256.scalar u2Relaxed ρ)
    (publicKey : Reference.Point) :
    JointFoldPoint ρ u1 u2 publicKey [:32].toList =
      Reference.verificationPoint (digest.eval ρ).toNat
        (sig.r.eval ρ).toNat (sig.s.eval ρ).toNat publicKey := by
  have hsFieldNe : (s.evalNat ρ : ZMod P256.scalar.modulus) ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hsMul
    exact zero_ne_one hsMul
  have hsInvEq : (sInv.evalNat ρ : ZMod P256.scalar.modulus) =
      (s.evalNat ρ : ZMod P256.scalar.modulus)⁻¹ :=
    Reference.Aux.inverse_eq_of_mul_eq_one hsFieldNe hsMul
  have hdigestCast : Int.castRingHom (ZMod P256.scalar.modulus)
      (ρ.int (digest.intVal)) =
      ((digest.eval ρ).toNat : ZMod P256.scalar.modulus) := by
    rw [U.intVal_eval_eq_eval_toNat digest hdigest]
    simp
  have hu1Field : (u1.evalNat ρ : ZMod P256.scalar.modulus) =
      ((digest.eval ρ).toNat : ZMod P256.scalar.modulus) *
        (s.evalNat ρ : ZMod P256.scalar.modulus)⁻¹ := by
    rw [← elem_evalZMod_eq_cast hu1, hu1Canonical, hu1Relaxed, hz,
      hdigestCast, elem_evalZMod_eq_cast hsInv, hsInvEq]
  have hu2Field : (u2.evalNat ρ : ZMod P256.scalar.modulus) =
      (r.evalNat ρ : ZMod P256.scalar.modulus) *
        (s.evalNat ρ : ZMod P256.scalar.modulus)⁻¹ := by
    rw [← elem_evalZMod_eq_cast hu2, hu2Canonical, hu2Relaxed,
      elem_evalZMod_eq_cast hr, elem_evalZMod_eq_cast hsInv, hsInvEq]
  have hu1Val : (((digest.eval ρ).toNat : ZMod P256.scalar.modulus) *
        (s.evalNat ρ : ZMod P256.scalar.modulus)⁻¹).val =
      (u1.val.eval ρ).toNat := by
    have hval := congrArg ZMod.val hu1Field
    rw [ZMod.val_cast_of_lt
      (Modular.Elem.evalNat_lt P256.scalar hu1)] at hval
    exact hval.symm.trans (elem_evalNat_eq_u_eval hu1 rfl hu1.1)
  have hu2Val : (((r.evalNat ρ : ZMod P256.scalar.modulus) *
        (s.evalNat ρ : ZMod P256.scalar.modulus)⁻¹)).val =
      (u2.val.eval ρ).toNat := by
    have hval := congrArg ZMod.val hu2Field
    rw [ZMod.val_cast_of_lt
      (Modular.Elem.evalNat_lt P256.scalar hu2)] at hval
    exact hval.symm.trans (elem_evalNat_eq_u_eval hu2 rfl hu2.1)
  rw [JointFoldPoint_full]
  simp only [Reference.verificationPoint, ← hrNat, ← hsNat]
  rw [← hu1Val, ← hu2Val]
  rfl

theorem verifyDigest_complete_aux {digest : U 256} {key : PublicKey}
    {sig : Signature} {aux : Aux} {publicKey : Reference.Point}
    (hdigest : digest.Valid ρ)
    (hkeyX : key.x.Valid ρ) (hkeyY : key.y.Valid ρ)
    (hr : sig.r.Valid ρ) (hs : sig.s.Valid ρ)
    (hrInv : aux.rInv.Valid ρ) (hsInv : aux.sInv.Valid ρ)
    (hkeyXlt : ρ.int (key.x.intVal) < P256.base.modulus)
    (hkeyYlt : ρ.int (key.y.intVal) < P256.base.modulus)
    (hrlt : ρ.int (sig.r.intVal) < P256.scalar.modulus)
    (hslt : ρ.int (sig.s.intVal) < P256.scalar.modulus)
    (hrInvlt : ρ.int (aux.rInv.intVal) < P256.scalar.modulus)
    (hsInvlt : ρ.int (aux.sInv.intVal) < P256.scalar.modulus)
    (hcoords : Reference.HasCoordinates publicKey
      (Int.castRingHom P256.Reference.Field (ρ.int (key.x.intVal)))
      (Int.castRingHom P256.Reference.Field (ρ.int (key.y.intVal))))
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
    multiplyScalars, canonicalizeScalars, finishVerification,
    computeVerificationSum, checkVerificationX]
  case vc15.hcurve =>
    rename_i qx hqx qy hqy r hr' s hs' rInv hrInv' sInv hsInv'
    apply onCurveZModSpec_of_hasCoordinates (publicKey := publicKey)
    have hxEval := congrArg (fun u : U 256 => ρ.int (u.intVal)) hqx.2
    have hyEval := congrArg (fun u : U 256 => ρ.int (u.intVal)) hqy.2
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
  case vc32.hu1 => simp_all [Modular.Elem.Valid]
  case vc33.hu2 => simp_all [Modular.Elem.Valid]
  case vc34.hQvalid =>
    exact ⟨(by aesop), (by aesop), baseOne_valid⟩
  case vc31.q => exact publicKey
  case vc35.hQ =>
    rename_i qx hqx qy hqy r hr' s hs' rInv hrInv' sInv hsInv'
      _ _ _ _ _ _ z hz u1Relaxed hu1Relaxed u2Relaxed hu2Relaxed
      u1 hu1 u2 hu2
    apply ofElems_represents_of_hasCoordinates (publicKey := publicKey)
    have hxEval := congrArg (fun u : U 256 => ρ.int (u.intVal)) hqx.2
    have hyEval := congrArg (fun u : U 256 => ρ.int (u.intVal)) hqy.2
    rw [hxEval, hyEval]
    exact hcoords
  case vc37.success.success.success.success =>
    rename_i qx hqx qy hqy r hr' s hs' rInv hrInv' sInv hsInv'
      _ hcurve _ hrMul _ hsMul z hz u1Relaxed hu1Relaxed
      u2Relaxed hu2Relaxed u1 hu1 u2 hu2 sum hsum
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
    have hsumPoint := jointFoldPoint_eq_verificationPoint hdigest hr'.1
      hsInv'.1 hu1.1 hu2.1 hrNat hsNat hsMul' hz.2 hu1Relaxed.2
      hu2Relaxed.2 hu1.2 hu2.2 publicKey
    rw [hsumPoint] at hsum
    have hverificationNonzero : Reference.verificationPoint
        (digest.eval ρ).toNat (sig.r.eval ρ).toNat
          (sig.s.eval ρ).toNat publicKey ≠ 0 := by
      rcases hverifies with ⟨_, _, _, _, _, hfinal⟩
      intro hzero
      rw [hzero] at hfinal
      exact hfinal
    have hsumInfinity : ρ.int (sum.infinity) = 0 := by
      rcases hpoint : Reference.verificationPoint (digest.eval ρ).toNat
          (sig.r.eval ρ).toNat (sig.s.eval ρ).toNat publicKey with
        _ | ⟨pointX, pointY, hpointCurve⟩
      · exact (hverificationNonzero hpoint).elim
      · exact (P256.Reference.Aux.represents_some
          (hpoint ▸ hsum.2.1)).1
    constructor
    · simp [hsumInfinity]
    · mvcgen -trivial
      case vc1.hx => exact hsum.1.2.1
      case vc2.hbound =>
        rw [hsum.1.1]
        norm_num [Modular.Lazy.quotientExtraBits]
      case vc3.hx0 =>
        rename_i xCanonical hxCanonical
        exact U.intVal_nonneg xCanonical.val hxCanonical.1.1
      case vc4.hxBound =>
        rename_i xCanonical hxCanonical
        exact hxCanonical.1.2.trans (by
          norm_num [P256.base, P256.baseModulus, P256.scalar,
            P256.scalarModulus])
      case vc5.right.success.success.success => exact fun _ => hverifies
      case vc6 =>
        rename_i xCanonical hxCanonical xModN
        intro hxModValid hxModSem
        rcases hverifies with ⟨_, _, _, _, _, hfinal⟩
        rcases hpoint : Reference.verificationPoint (digest.eval ρ).toNat
            (sig.r.eval ρ).toNat (sig.s.eval ρ).toNat publicKey with
          _ | ⟨pointX, pointY, hpointCurve⟩
        · exact (hverificationNonzero hpoint).elim
        · have hsumSome := P256.Reference.Aux.represents_some
            (hpoint ▸ hsum.2.1)
          have hxPoint : Modular.Lazy.evalElemZMod P256.base
              xCanonical ρ = pointX :=
            hxCanonical.2.trans hsumSome.2.1
          have hxCanonicalNat : xCanonical.evalNat ρ = pointX.val := by
            have hxPoint' : (xCanonical.evalNat ρ : P256.Reference.Field) =
                pointX := by
              unfold Modular.Lazy.evalElemZMod at hxPoint
              rw [← Modular.Elem.evalNat_cast P256.base
                hxCanonical.1] at hxPoint
              exact hxPoint
            have hval := congrArg ZMod.val hxPoint'
            rw [ZMod.val_cast_of_lt
              (Modular.Elem.evalNat_lt P256.base hxCanonical.1)] at hval
            exact hval
          have hxModNatCast : Modular.Lazy.evalElemZMod P256.scalar
              xModN ρ = (xModN.evalNat ρ : ZMod P256.scalar.modulus) := by
            unfold Modular.Lazy.evalElemZMod Modular.Elem.evalNat
            have hnonneg := U.intVal_nonneg xModN.val hxModValid.1
            rw [← Int.cast_natCast]
            exact congrArg (Int.castRingHom (ZMod P256.scalar.modulus))
              (Int.toNat_of_nonneg hnonneg).symm
          have hxCanonicalScalarCast :
              (Int.castRingHom (ZMod P256.scalar.modulus)
                (ρ.int (xCanonical.val.intVal))) =
                (xCanonical.evalNat ρ : ZMod P256.scalar.modulus) := by
            rw [← Modular.Elem.evalNat_cast P256.base hxCanonical.1]
            rfl
          have hxModField :
              (xModN.evalNat ρ : ZMod P256.scalar.modulus) =
                (xCanonical.evalNat ρ : ZMod P256.scalar.modulus) := by
            rw [← hxModNatCast, hxModSem, hxCanonicalScalarCast]
          have hxModVal := congrArg ZMod.val hxModField
          rw [ZMod.val_cast_of_lt
              (Modular.Elem.evalNat_lt P256.scalar hxModValid),
            ZMod.val_natCast, hxCanonicalNat] at hxModVal
          rw [hpoint] at hfinal
          rw [hrNat]
          exact hxModVal.trans (by
            simpa [P256.scalar_modulus_eq] using hfinal)
      case vc7 => exact fun hvalid _ => hvalid
      case vc8 => exact fun _ _ => hr'.1
  case vc38 =>
    intro _
    exact Modular.Lazy.ofElem_valid P256.scalar (by aesop)
  case vc39 =>
    intro _
    exact Modular.Lazy.ofElem_valid P256.scalar (by aesop)
  case vc40 =>
    intro _
    exact Modular.Lazy.ofElem_valid P256.scalar fnOne_valid
  case vc41 =>
    intro _
    exact assertMulEqSpec_of_u_mul (by aesop) (by aesop)
      (by aesop) (by aesop) hs hsInv hsInvMul
  case vc42 =>
    intro _
    norm_num [Modular.Lazy.ofElem, Modular.Lazy.quotientExtraBits]
  all_goals try assumption

theorem verifyDigest_sound_aux {digest : U 256} {key : PublicKey}
    {sig : Signature} {aux : Aux}
    (hdigest : digest.Valid ρ)
    (hkeyX : key.x.Valid ρ) (hkeyY : key.y.Valid ρ)
    (hr : sig.r.Valid ρ) (hs : sig.s.Valid ρ)
    (hrInv : aux.rInv.Valid ρ) (hsInv : aux.sInv.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (verifyDigest digest key sig aux)
    ⦃⇓ _ => ⌜∃ publicKey : Reference.Point,
      Reference.HasCoordinates publicKey
        (Int.castRingHom P256.Reference.Field
          (ρ.int (key.x.intVal)))
        (Int.castRingHom P256.Reference.Field
          (ρ.int (key.y.intVal))) ∧
      Reference.Verifies (digest.eval ρ).toNat
        (sig.r.eval ρ).toNat (sig.s.eval ρ).toNat publicKey⌝⦄ := by
  mvcgen [verifyDigest, canonicalizeInput, canonicalizeKey,
    canonicalizeSignature, canonicalizeAux, prepareVerification,
    validateCanonicalInput, deriveScalars, deriveRelaxedScalars,
    multiplyScalars, canonicalizeScalars, finishVerification,
    computeVerificationSum, checkVerificationX]
  case vc7.q =>
    exact P256.Reference.pointOfCircuit ρ _ _ (by assumption)
  case vc8.hu1 =>
    simp_all [Modular.Elem.Valid]
  case vc9.hu2 =>
    simp_all [Modular.Elem.Valid]
  case vc10.hQ =>
    exact P256.Reference.Aux.ofElems_represents_pointOfCircuit (by assumption)
  case vc11.success.success =>
    rename_i qx hqx qy hqy r hr' s hs' rInv hrInv' sInv hsInv'
      _ hcurve _ hrMul _ hsMul z hz u1Relaxed hu1Relaxed
      u2Relaxed hu2Relaxed u1 hu1 u2 hu2 sum hsum hfinite
      xCanonical hxCanonical xModN hxModN _
    intro hfinalEq
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
    have hsumPoint := jointFoldPoint_eq_verificationPoint hdigest hr'.1
      hsInv'.1 hu1.1 hu2.1 hrNat hsNat hsMul' hz.2 hu1Relaxed.2
      hu2Relaxed.2 hu1.2 hu2.2 publicKey
    rw [hsumPoint] at hsum
    have hsumInfinity : ρ.int (sum.infinity) = 0 := by
      simpa using hfinite.symm
    have hverificationNonzero : Reference.verificationPoint
        (digest.eval ρ).toNat (sig.r.eval ρ).toNat
          (sig.s.eval ρ).toNat publicKey ≠ 0 := by
      intro hzero
      have hinfinity := P256.Reference.Aux.represents_zero (hzero ▸ hsum.1)
      omega
    rcases hpoint : Reference.verificationPoint (digest.eval ρ).toNat
        (sig.r.eval ρ).toNat (sig.s.eval ρ).toNat publicKey with
      _ | ⟨pointX, pointY, hpointCurve⟩
    · exact (hverificationNonzero hpoint).elim
    · have hsumSome := P256.Reference.Aux.represents_some (hpoint ▸ hsum.1)
      have hxPoint : Modular.Lazy.evalElemZMod P256.base xCanonical ρ =
          pointX := hxCanonical.2.trans hsumSome.2.1
      have hxCanonicalNat : xCanonical.evalNat ρ = pointX.val := by
        have hxPoint' : (xCanonical.evalNat ρ : P256.Reference.Field) =
            pointX := by
          unfold Modular.Lazy.evalElemZMod at hxPoint
          rw [← Modular.Elem.evalNat_cast P256.base hxCanonical.1] at hxPoint
          exact hxPoint
        have hval := congrArg ZMod.val hxPoint'
        rw [ZMod.val_cast_of_lt
          (Modular.Elem.evalNat_lt P256.base hxCanonical.1)] at hval
        exact hval
      have hxModNatCast : Modular.Lazy.evalElemZMod P256.scalar xModN ρ =
          (xModN.evalNat ρ : ZMod P256.scalar.modulus) := by
        unfold Modular.Lazy.evalElemZMod Modular.Elem.evalNat
        have hnonneg := U.intVal_nonneg xModN.val hxModN.1
        rw [← Int.cast_natCast]
        exact congrArg (Int.castRingHom (ZMod P256.scalar.modulus))
          (Int.toNat_of_nonneg hnonneg).symm
      have hxCanonicalScalarCast :
          (Int.castRingHom (ZMod P256.scalar.modulus)
            (ρ.int (xCanonical.val.intVal))) =
            (xCanonical.evalNat ρ : ZMod P256.scalar.modulus) := by
        rw [← Modular.Elem.evalNat_cast P256.base hxCanonical.1]
        rfl
      have hxModField : (xModN.evalNat ρ : ZMod P256.scalar.modulus) =
          (xCanonical.evalNat ρ : ZMod P256.scalar.modulus) := by
        rw [← hxModNatCast, hxModN.2, hxCanonicalScalarCast]
      rw [hfinalEq] at hxModField
      have hxModVal := congrArg ZMod.val hxModField
      rw [ZMod.val_cast_of_lt (Modular.Elem.evalNat_lt P256.scalar hr'.1),
        ZMod.val_natCast, hrNat, hxCanonicalNat] at hxModVal
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
          simpa [P256.scalar_modulus_eq, hrNat] using hxModVal.symm

theorem verifyDigestInputWord_eval_inputs
    {ρ : WF.Valuation} (inputs : Vector Bool verifyDigestInputBits)
    (hbits : ∀ i : Fin verifyDigestInputBits,
      ρ.bool ({i.val} : LC Bool) = inputs[i])
    (slot : Fin 7) :
    Word.eval ρ.bool
      (verifyDigestInputWord (Vector.ofFn fun i => ({i.val} : LC Bool)) slot) =
      verifyDigestInputValue inputs slot := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [Word.eval, BitVec.getElem_ofFnLE, Fin.getElem_fin,
    verifyDigestInputWord, Vector.getElem_ofFn, verifyDigestInputValue]
  exact hbits ⟨slot.val * 256 + i, by
    simp [verifyDigestInputBits]
    omega⟩

theorem verifyDigestInputWords_eval_inputs
    {ρ : WF.Valuation} (inputs : Vector Bool verifyDigestInputBits)
    (hbits : ∀ i : Fin verifyDigestInputBits,
      ρ.bool ({i.val} : LC Bool) = inputs[i]) :
    (verifyDigestInputWords (Vector.ofFn fun i => ({i.val} : LC Bool))).map
        (Word.eval ρ.bool) =
      Vector.ofFn (verifyDigestInputValue inputs) := by
  apply Vector.ext
  intro i hi
  simpa [verifyDigestInputWords] using
    verifyDigestInputWord_eval_inputs inputs hbits ⟨i, hi⟩

theorem verifyDigestFromBits_sound_aux
    (inputs : Vector Bool verifyDigestInputBits) :
    ⦃⌜∀ i : Fin verifyDigestInputBits,
      ρ.bool ({i.val} : LC Bool) = inputs[i]⌝⦄
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
    have hqxInt : ρ.int (values[1].intVal) =
        ((verifyDigestInputValue inputs 1).toNat : Int) :=
      (U.intVal_eval_eq_eval_toNat values[1] (hvalues 1).1).trans
        (congrArg (fun x : BitVec 256 => (x.toNat : Int))
          (hvalue 1 (by omega)))
    have hqyInt : ρ.int (values[2].intVal) =
        ((verifyDigestInputValue inputs 2).toNat : Int) :=
      (U.intVal_eval_eq_eval_toNat values[2] (hvalues 2).1).trans
        (congrArg (fun x : BitVec 256 => (x.toNat : Int))
          (hvalue 2 (by omega)))
    have hqxField :
        (Int.castRingHom P256.Reference.Field) (ρ.int (values[1].intVal)) =
          ((verifyDigestInputValue inputs 1).toNat : P256.Reference.Field) := by
      rw [hqxInt]
      simp
    have hqyField :
        (Int.castRingHom P256.Reference.Field) (ρ.int (values[2].intVal)) =
          ((verifyDigestInputValue inputs 2).toNat : P256.Reference.Field) := by
      rw [hqyInt]
      simp
    have ht := verifyDigest_sound_aux
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

theorem verifyDigestFromBits_complete_aux
    (inputs : Vector Bool verifyDigestInputBits)
    (publicKey : Reference.Point)
    (hbits : ∀ i : Fin verifyDigestInputBits,
      ρ.bool ({i.val} : LC Bool) = inputs[i])
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
    have hqxInt : ρ.int (values[1].intVal) =
        ((verifyDigestInputValue inputs 1).toNat : Int) := by
      exact (U.intVal_eval_eq_eval_toNat values[1] (hvalues 1).1).trans
        (congrArg (fun x : BitVec 256 => (x.toNat : Int))
          (hvalue 1 (by omega)))
    have hqyInt : ρ.int (values[2].intVal) =
        ((verifyDigestInputValue inputs 2).toNat : Int) := by
      exact (U.intVal_eval_eq_eval_toNat values[2] (hvalues 2).1).trans
        (congrArg (fun x : BitVec 256 => (x.toNat : Int))
          (hvalue 2 (by omega)))
    have hrInt : ρ.int (values[3].intVal) =
        ((verifyDigestInputValue inputs 3).toNat : Int) := by
      exact (U.intVal_eval_eq_eval_toNat values[3] (hvalues 3).1).trans
        (congrArg (fun x : BitVec 256 => (x.toNat : Int))
          (hvalue 3 (by omega)))
    have hsInt : ρ.int (values[4].intVal) =
        ((verifyDigestInputValue inputs 4).toNat : Int) := by
      exact (U.intVal_eval_eq_eval_toNat values[4] (hvalues 4).1).trans
        (congrArg (fun x : BitVec 256 => (x.toNat : Int))
          (hvalue 4 (by omega)))
    have hrInvInt : ρ.int (values[5].intVal) =
        ((verifyDigestInputValue inputs 5).toNat : Int) := by
      exact (U.intVal_eval_eq_eval_toNat values[5] (hvalues 5).1).trans
        (congrArg (fun x : BitVec 256 => (x.toNat : Int))
          (hvalue 5 (by omega)))
    have hsInvInt : ρ.int (values[6].intVal) =
        ((verifyDigestInputValue inputs 6).toNat : Int) := by
      exact (U.intVal_eval_eq_eval_toNat values[6] (hvalues 6).1).trans
        (congrArg (fun x : BitVec 256 => (x.toNat : Int))
          (hvalue 6 (by omega)))
    have hdigestNat := congrArg BitVec.toNat (hvalue 0 (by omega))
    have hrNat := congrArg BitVec.toNat (hvalue 3 (by omega))
    have hsNat := congrArg BitVec.toNat (hvalue 4 (by omega))
    have hrInvNat := congrArg BitVec.toNat (hvalue 5 (by omega))
    have hsInvNat := congrArg BitVec.toNat (hvalue 6 (by omega))
    have ht := verifyDigest_complete_aux
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
