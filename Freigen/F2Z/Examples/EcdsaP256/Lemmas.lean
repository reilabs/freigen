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

theorem cast_ne_zero_of_pos_of_lt {x : Nat}
    (hx : 0 < x) (hlt : x < scalarModulus) : (x : Scalar) ≠ 0 := by
  intro hzero
  have hval := congrArg ZMod.val hzero
  rw [ZMod.val_cast_of_lt hlt] at hval
  simp at hval
  omega

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

end Freigen.F2Z.Examples.EcdsaP256.Reference.Aux

namespace Freigen.F2Z.Examples.EcdsaP256

open Std.Do BigOperators
open scoped Std.Do

namespace Aux

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

def IndicatorsSpec {n : Nat} (ρ : WF.Valuation) (digit : LC ℤ)
    (out : U n) : Prop :=
  out.Valid ρ ∧ ∃ i : Fin n,
    out.intBits[i].eval ρ.int = 1 ∧ digit.eval ρ.int = i.val ∧
      ∀ j : Fin n, out.intBits[j].eval ρ.int = 1 → j = i

@[spec] theorem indicators_sound {n : Nat} {digit : LC ℤ} :
    ⦃⌜True⌝⦄ Sound.interp ρ (indicators n digit)
    ⦃⇓ out => ⌜IndicatorsSpec ρ digit out⌝⦄ := by
  mvcgen [indicators, IndicatorsSpec]
  intro bits
  mvcgen
  rename_i out hout hsum hweighted
  refine ⟨hout.1, ?_⟩
  have hbit : ∀ i : Fin n,
      out.intBits[i].eval ρ.int = 0 ∨ out.intBits[i].eval ρ.int = 1 := by
    intro i
    have hi := hout.1 i
    cases hb : out.bits.bitsLE[i].eval ρ.bool <;>
      rw [hb] at hi <;> simp at hi
    · exact Or.inl hi
    · exact Or.inr hi
  have hsum' : ∑ i : Fin n, out.intBits[i].eval ρ.int = 1 := by
    simp only [LC.eval_zero, zero_mul, LC.eval_sub, LC.eval_sum,
      LC.eval_one] at hsum
    exact sub_eq_zero.mp hsum.symm
  rcases Aux.oneHot hbit hsum' with ⟨i, hi, hui⟩
  refine ⟨i, hi, ?_, hui⟩
  · simp only [LC.eval_zero, zero_mul, LC.eval_sub, LC.eval_sum,
      LC.eval_nsmul, nsmul_eq_mul] at hweighted
    have hzero : ∀ j : Fin n, j ≠ i →
        out.intBits[j].eval ρ.int = 0 := by
      intro j hji
      rcases hbit j with hj | hj
      · exact hj
      · exact (hji (hui j hj)).elim
    rw [show (∑ j : Fin n, (j.val : Int) *
        out.intBits[j].eval ρ.int) = i.val by
      have hrest : ∑ j ∈ (Finset.univ.erase i), (j.val : Int) *
          out.intBits[j].eval ρ.int = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [hzero j (Finset.mem_erase.mp hj).1]
        simp
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hrest, hi]
      simp] at hweighted
    omega

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
  ∀ i : Fin 16, indicators.intBits[i].eval ρ.int = 1 →
    Modular.Lazy.evalZMod P256.base out ρ =
      Modular.Lazy.evalZMod P256.base xs[i] ρ

@[spec] theorem assertLookupRep_sound {indicators : U 16} {out : U 256}
    {xs : Vector P256.AffineSlope.Rep 16} :
    ⦃⌜True⌝⦄ Sound.interp ρ (assertLookupRep indicators out xs)
    ⦃⇓ _ => ⌜LookupRepSpec ρ indicators xs ⟨out.intVal, 2⟩⌝⦄ := by
  mvcgen [assertLookupRep] invariants
  · ⇓⟨cur, _⟩ => ⌜∀ i : Fin 16, i.val < cur.prefix.length →
      indicators.intBits[i].eval ρ.int = 1 →
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
      simp only [LC.eval_sub, LC.eval_zero] at hassert
      rw [show indicators.intBits[i.val].eval ρ.int = 1 by simpa using hone,
        one_mul] at hassert
      have houtEq : out.intVal.eval ρ.int = xs[i].intVal.eval ρ.int := by
        simpa only [Fin.getElem_fin] using sub_eq_zero.mp hassert
      unfold Modular.Lazy.evalZMod
      rw [houtEq]
  case vc2 => simp
  case vc3 h => simpa [LookupRepSpec] using h

@[spec] theorem lookupRep_sound {digit : LC ℤ} {indicators : U 16}
    {xs : Vector P256.AffineSlope.Rep 16} :
    ⦃⌜True⌝⦄ Sound.interp ρ (lookupRep digit indicators xs)
    ⦃⇓ out => ⌜LookupRepSpec ρ indicators xs out⌝⦄ := by
  mvcgen [lookupRep]
  intro bits
  mvcgen

@[spec] theorem lookupPoint_sound {digit : LC ℤ}
    {table : Vector P256.AffineSlope.Point 16}
    {q : P256.Reference.Point}
    (htable : ∀ i : Fin 16,
      P256.Reference.Represents ρ table[i] (i.val • q))
    (hnonzero : ∀ i : Fin 16, i.val ≠ 0 → i.val • q ≠ 0) :
    ⦃⌜True⌝⦄ Sound.interp ρ (lookupPoint digit table)
    ⦃⇓ out => ⌜∃ i : Fin 16, digit.eval ρ.int = i.val ∧
      P256.Reference.Represents ρ out (i.val • q)⌝⦄ := by
  mvcgen [lookupPoint]
  rename_i indicators hi X hX Y hY
  rcases hi.2 with ⟨i, hone, hdigit, hunique⟩
  refine ⟨i, hdigit, ?_⟩
  have hxi := hX i hone
  have hyi := hY i hone
  have htablei := htable i
  unfold P256.Reference.Represents at htablei ⊢
  constructor
  · by_cases hi0 : i.val = 0
    · right
      have hieq : i = 0 := Fin.eq_of_val_eq hi0
      subst i
      simpa using hone
    · left
      have hzero : indicators.intBits[0].eval ρ.int = 0 := by
        have hbit := hi.1 (0 : Fin 16)
        have hbit0 : indicators.intBits[0].eval ρ.int = 0 ∨
            indicators.intBits[0].eval ρ.int = 1 := by
          cases hb : indicators.bits.bitsLE[(0 : Fin 16)].eval ρ.bool <;>
            rw [hb] at hbit <;> simp at hbit
          · exact Or.inl hbit
          · exact Or.inr hbit
        rcases hbit0 with h0 | h1
        · exact h0
        · have hz := hunique 0 h1
          omega
      exact hzero
  · unfold P256.Reference.circuitCoordinates at htablei ⊢
    by_cases hi0 : i.val = 0
    · have hieq : i = 0 := Fin.eq_of_val_eq hi0
      subst i
      simp only [P256.Reference.coordinates] at htablei ⊢
      have houtInf : indicators.intBits[0].eval ρ.int = 1 := by
        simpa using hone
      rw [if_pos houtInf]
      simp
    · have hmul0 := hnonzero i hi0
      rcases hpoint : i.val • q with _ | ⟨px, py, hp⟩
      · exact (hmul0 hpoint).elim
      · simp only [hpoint, P256.Reference.coordinates] at htablei ⊢
        have htableFinite := htablei.2
        split at htableFinite
        · contradiction
        · rename_i htableFlag
          have houtFlag : indicators.intBits[0].eval ρ.int = 0 := by
            have hbit := hi.1 (0 : Fin 16)
            have hbit0 : indicators.intBits[0].eval ρ.int = 0 ∨
                indicators.intBits[0].eval ρ.int = 1 := by
              cases hb : indicators.bits.bitsLE[(0 : Fin 16)].eval ρ.bool <;>
                rw [hb] at hbit <;> simp at hbit
              · exact Or.inl hbit
              · exact Or.inr hbit
            rcases hbit0 with h0 | h1
            · exact h0
            · have hz := hunique 0 h1
              omega
          rw [if_neg (by omega)]
          have hcoords := P256.Reference.Coordinates.finite.inj htableFinite
          have hxi' : Modular.Lazy.evalZMod P256.base X ρ =
              Modular.Lazy.evalZMod P256.base table[i].X ρ := by simpa using hxi
          have hyi' : Modular.Lazy.evalZMod P256.base Y ρ =
              Modular.Lazy.evalZMod P256.base table[i].Y ρ := by simpa using hyi
          congr 1
          · change ((X.intVal.eval ρ.int : Int) : ZMod P256.baseModulus) = px
            exact hxi'.trans hcoords.1
          · change ((Y.intVal.eval ρ.int : Int) : ZMod P256.baseModulus) = py
            exact hyi'.trans hcoords.2

@[spec] theorem lookupGeneratorByte_sound {digit : LC ℤ} :
    ⦃⌜True⌝⦄ Sound.interp ρ (lookupGeneratorByte digit)
    ⦃⇓ out => ⌜∃ i : Fin 256, digit.eval ρ.int = i.val ∧
      P256.Reference.Represents ρ out
        (i.val • P256.Reference.generator)⌝⦄ := by
  mvcgen [lookupGeneratorByte]
  rename_i indicators hi
  rcases hi.2 with ⟨i, hone, hdigit, hunique⟩
  refine ⟨i, hdigit, ?_⟩
  unfold P256.Reference.Represents P256.Reference.circuitCoordinates
  constructor
  · have hbit := hi.1 (0 : Fin 256)
    cases hb : indicators.bits.bitsLE[(0 : Fin 256)].eval ρ.bool <;>
      rw [hb] at hbit <;> simp at hbit
    · exact Or.inl hbit
    · exact Or.inr hbit
  · by_cases hi0 : i.val = 0
    · have hieq : i = 0 := Fin.eq_of_val_eq hi0
      subst i
      simp only [P256.Reference.coordinates, if_pos (by simpa using hone)]
      rfl
    · have hzero : indicators.intBits[0].eval ρ.int = 0 := by
        have hbit := hi.1 (0 : Fin 256)
        have hcases : indicators.intBits[0].eval ρ.int = 0 ∨
            indicators.intBits[0].eval ρ.int = 1 := by
          cases hb : indicators.bits.bitsLE[(0 : Fin 256)].eval ρ.bool <;>
            rw [hb] at hbit <;> simp at hbit
          · exact Or.inl hbit
          · exact Or.inr hbit
        exact hcases.resolve_right fun h => by
          have := hunique 0 h
          omega
      rw [if_neg (show indicators.intBits[0].eval ρ.int ≠ 1 by omega)]
      have hnonzero := Reference.Aux.generator_nsmul_ne_zero hi0
        (i.isLt.trans (by native_decide : 256 < P256.scalarModulus))
      rcases hpoint : i.val • P256.Reference.generator with _ | ⟨x, y, hxy⟩
      · exact (hnonzero hpoint).elim
      · simp only [hpoint, P256.Reference.coordinates]
        congr 1
        · unfold Modular.Lazy.evalZMod
          simp only [LC.eval_sum, LC.eval_nsmul, nsmul_eq_mul]
          rw [show (∑ j : Fin 256, (generatorByteX[j] : ℤ) *
              indicators.intBits[j].eval ρ.int) = generatorByteX[i] by
            exact Aux.sum_mul_oneHot _ _ i hone fun j hji => by
              have hbit := hi.1 j
              cases hb : indicators.bits.bitsLE[j].eval ρ.bool <;>
                rw [hb] at hbit <;> simp at hbit
              · exact hbit
              · exact (hji (hunique j hbit)).elim]
          rw [Aux.generatorByteX_get, hpoint]
          exact ZMod.natCast_zmod_val x
        · unfold Modular.Lazy.evalZMod
          simp only [LC.eval_sum, LC.eval_nsmul, nsmul_eq_mul]
          rw [show (∑ j : Fin 256, (generatorByteY[j] : ℤ) *
              indicators.intBits[j].eval ρ.int) = generatorByteY[i] by
            exact Aux.sum_mul_oneHot _ _ i hone fun j hji => by
              have hbit := hi.1 j
              cases hb : indicators.bits.bitsLE[j].eval ρ.bool <;>
                rw [hb] at hbit <;> simp at hbit
              · exact hbit
              · exact (hji (hunique j hbit)).elim]
          rw [Aux.generatorByteY_get, hpoint]
          exact ZMod.natCast_zmod_val y

end Freigen.F2Z.Examples.EcdsaP256
