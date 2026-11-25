import Freigen.F2Z.Examples.EcdsaP256.Lemmas
import Freigen.F2Z.Examples.EcdsaP256.FixedBaseCombImpl

/-!
Proofs local to the mixed-comb recoding and selector.  Keeping this module
separate avoids re-elaborating the public ECDSA proof while iterating on the
wide fixed-table lookup.
-/

namespace Freigen.F2Z.Examples.EcdsaP256

open Std.Do
open scoped Std.Do
open BigOperators
open Modular
open P256

set_option maxRecDepth 10000

def XnorBitSpec (rho : WF.Valuation) (sign bit out : LC ℤ) : Prop :=
  out.eval rho.int = 2 * sign.eval rho.int * bit.eval rho.int -
    sign.eval rho.int - bit.eval rho.int + 1

@[spec] theorem xnorBit_sound {sign bit : LC ℤ} :
    ⦃⌜True⌝⦄ Sound.interp ρ (xnorBit sign bit)
    ⦃⇓ out => ⌜XnorBitSpec ρ sign bit out⌝⦄ := by
  mvcgen [xnorBit]
  rename_i out hout
  unfold XnorBitSpec
  simp only [LC.eval_add, LC.eval_sub, LC.eval_nsmul, LC.eval_one,
    nsmul_eq_mul, hout.1]
  ring

@[spec] theorem xnorBit_complete {sign bit : LC ℤ}
    (hsign : sign.eval ρ.int = 0 ∨ sign.eval ρ.int = 1)
    (hbit : bit.eval ρ.int = 0 ∨ bit.eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Complete.interp ρ (xnorBit sign bit)
    ⦃⇓ out => ⌜XnorBitSpec ρ sign bit out⌝⦄ := by
  mvcgen [xnorBit]
  case vc3.success =>
    rename_i out hout
    unfold XnorBitSpec
    simp only [LC.eval_add, LC.eval_sub, LC.eval_nsmul, LC.eval_one,
      nsmul_eq_mul, hout.1]
    ring

theorem XnorBitSpec.bool (h : XnorBitSpec ρ sign bit out)
    (hsign : sign.eval ρ.int = 0 ∨ sign.eval ρ.int = 1)
    (hbit : bit.eval ρ.int = 0 ∨ bit.eval ρ.int = 1) :
    out.eval ρ.int = 0 ∨ out.eval ρ.int = 1 := by
  unfold XnorBitSpec at h
  rcases hsign with hsign | hsign <;> rcases hbit with hbit | hbit <;>
    simp_all

def XnorMagnitudeBitsSpec (rho : WF.Valuation) {width : Nat}
    (bits : Vector (LC ℤ) width) (hwidth : 1 ≤ width)
    (out : Vector (LC ℤ) (width - 1)) : Prop :=
  ∀ i : Fin (width - 1),
    XnorBitSpec rho (bits[width - 1]'(by omega))
      (bits[i.val]'(by omega)) out[i]

@[spec] theorem xnorMagnitudeBits_sound {width : Nat}
    {bits : Vector (LC ℤ) width} {hwidth : 1 ≤ width} :
    ⦃⌜True⌝⦄ Sound.interp ρ (xnorMagnitudeBits bits hwidth)
    ⦃⇓ out => ⌜XnorMagnitudeBitsSpec ρ bits hwidth out⌝⦄ := by
  rw [xnorMagnitudeBits]
  apply Sound.vectorOfFnM (R := fun i out =>
    XnorBitSpec ρ (bits[width - 1]'(by omega))
      (bits[i.val]'(by omega)) out)
  intro i
  simpa using (xnorBit_sound (ρ := ρ)
    (sign := bits[width - 1]'(by omega)) (bit := bits[i.val]'(by omega)))

@[spec] theorem xnorMagnitudeBits_complete {width : Nat}
    {bits : Vector (LC ℤ) width} {hwidth : 1 ≤ width}
    (hbits : ∀ i : Fin width,
      bits[i].eval ρ.int = 0 ∨ bits[i].eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Complete.interp ρ (xnorMagnitudeBits bits hwidth)
    ⦃⇓ out => ⌜XnorMagnitudeBitsSpec ρ bits hwidth out⌝⦄ := by
  rw [xnorMagnitudeBits]
  apply Complete.vectorOfFnM (R := fun i out =>
    XnorBitSpec ρ (bits[width - 1]'(by omega))
      (bits[i.val]'(by omega)) out)
  intro i
  apply xnorBit_complete
  · exact hbits ⟨width - 1, by omega⟩
  · exact hbits ⟨i.val, by omega⟩

theorem combBit_eval {k : Fn} (hk : k.val.Valid ρ)
    (i : Nat) (hi : i < 256) :
    (combBit k i hi).eval ρ.int =
      if h : i < 255 then
        (if (k.val.eval ρ)[i + 1] then 1 else 0)
      else 1 := by
  unfold combBit
  split
  · rename_i h
    have heval := U.eval_eq_ofFnLE k.val hk
    rw [heval, BitVec.getElem_ofFnLE]
    have hbit := hk ⟨i + 1, by omega⟩
    cases hb : (k.val.bits.bitsLE[i + 1]'(by omega)).eval ρ.bool <;>
      simpa [hb] using hbit
  · simp only [LC.eval_one]

theorem combBit_bool {k : Fn} (hk : k.val.Valid ρ)
    (i : Nat) (hi : i < 256) :
    (combBit k i hi).eval ρ.int = 0 ∨
      (combBit k i hi).eval ρ.int = 1 := by
  rw [combBit_eval hk]
  split
  · split <;> simp
  · simp

theorem combWindowValue_eval {k : Fn} (hk : k.val.Valid ρ)
    (offset width : Nat) (hfit : offset + width ≤ 256) :
    (combWindowValue (combWindowBits k offset width hfit)).eval ρ.int =
      ∑ i : Fin width, (2 ^ i.val : Int) *
        (if h : offset + i.val < 255 then
          (if (k.val.eval ρ)[offset + i.val + 1] then 1 else 0)
         else 1) := by
  unfold combWindowValue combWindowBits
  rw [LC.eval_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [LC.eval_smul]
  have hget :
      (Vector.ofFn fun j : Fin width =>
        combBit k (offset + j.val) (by omega))[i] =
        combBit k (offset + i.val) (by omega) := by
    exact Vector.get_ofFn _ i
  rw [hget]
  rw [combBit_eval hk]

def FactoredCoordinatesSpec (rho : WF.Valuation) (width : Nat)
    (table : Array Reference.Point) (inner : U 128)
    (outer : U (2 ^ (width - 7))) (X Y : U 256) : Prop :=
  ∀ o : Fin (2 ^ (width - 7)), outer.intBits[o].eval rho.int = 1 →
    X.intVal.eval rho.int = (fixedInnerX table width o.val inner).eval rho.int ∧
    Y.intVal.eval rho.int = (fixedInnerY table width o.val inner).eval rho.int

@[spec] theorem assertFactoredCoordinates_sound {width : Nat}
    {table : Array Reference.Point} {inner : U 128}
    {outer : U (2 ^ (width - 7))} {X Y : U 256} :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (assertFactoredCoordinates width table inner outer X Y)
    ⦃⇓ _ => ⌜FactoredCoordinatesSpec ρ width table inner outer X Y⌝⦄ := by
  mvcgen [assertFactoredCoordinates, WF.foldRange] invariants
  · ⇓⟨cur, _⟩ => ⌜∀ o : Fin (2 ^ (width - 7)),
      o.val < cur.prefix.length → outer.intBits[o].eval ρ.int = 1 →
      X.intVal.eval ρ.int = (fixedInnerX table width o.val inner).eval ρ.int ∧
      Y.intVal.eval ρ.int = (fixedInnerY table width o.val inner).eval ρ.int⌝
  case vc1 pref cur suff hsplit _ hprev hx hy =>
    intro o ho hone
    simp only [List.length_append, List.length_singleton] at ho
    by_cases hlt : o.val < pref.length
    · exact hprev o hlt hone
    · have hocur : o.val = cur := by
        have hcur : cur = pref.length := by grind
        omega
      subst cur
      simp only [LC.eval_sub, LC.eval_zero] at hx hy
      rw [show outer.intBits[o.val].eval ρ.int = 1 by simpa using hone,
        one_mul] at hx hy
      exact ⟨sub_eq_zero.mp hx.2, sub_eq_zero.mp hy⟩
  case vc2 => simp
  case vc3 h => simpa [FactoredCoordinatesSpec] using h

@[spec] theorem assertFactoredCoordinates_complete {width : Nat}
    {table : Array Reference.Point} {inner : U 128}
    {outer : U (2 ^ (width - 7))} {X Y : U 256}
    (houter : outer.Valid ρ)
    (heq : ∀ o : Fin (2 ^ (width - 7)),
      outer.intBits[o].eval ρ.int = 1 →
      X.intVal.eval ρ.int = (fixedInnerX table width o.val inner).eval ρ.int ∧
      Y.intVal.eval ρ.int = (fixedInnerY table width o.val inner).eval ρ.int) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (assertFactoredCoordinates width table inner outer X Y)
    ⦃⇓ _ => ⌜FactoredCoordinatesSpec ρ width table inner outer X Y⌝⦄ := by
  have hbit (o : Fin (2 ^ (width - 7))) :
      outer.intBits[o].eval ρ.int = 0 ∨ outer.intBits[o].eval ρ.int = 1 := by
    have ho := houter o
    cases hb : outer.bits.bitsLE[o].eval ρ.bool <;>
      rw [hb] at ho <;> simp at ho
    · exact Or.inl ho
    · exact Or.inr ho
  mvcgen [assertFactoredCoordinates, WF.foldRange] invariants
  · ⇓⟨cur, _⟩ => ⌜∀ o : Fin (2 ^ (width - 7)),
      o.val < cur.prefix.length → outer.intBits[o].eval ρ.int = 1 →
      X.intVal.eval ρ.int = (fixedInnerX table width o.val inner).eval ρ.int ∧
      Y.intVal.eval ρ.int = (fixedInnerY table width o.val inner).eval ρ.int⌝
  case vc1 pref cur suff hsplit _ hprev =>
    have hcur : cur < 2 ^ (width - 7) := by grind
    let o : Fin (2 ^ (width - 7)) := ⟨cur, hcur⟩
    constructor
    · rcases hbit o with hz | hone
      · have hz' : outer.intBits[cur].eval ρ.int = 0 := by simpa [o] using hz
        simp [hz']
      · have hone' : outer.intBits[cur].eval ρ.int = 1 := by simpa [o] using hone
        simp only [LC.eval_sub, LC.eval_zero, hone', one_mul]
        exact sub_eq_zero.mpr (heq o hone).1
    · mvcgen
      let o : Fin (2 ^ (width - 7)) := ⟨cur, hcur⟩
      constructor
      · rcases hbit o with hz | hone
        · have hz' : outer.intBits[cur].eval ρ.int = 0 := by simpa [o] using hz
          simp [hz']
        · have hone' : outer.intBits[cur].eval ρ.int = 1 := by simpa [o] using hone
          simp only [LC.eval_sub, LC.eval_zero, hone', one_mul]
          exact sub_eq_zero.mpr (heq o hone).2
      · mvcgen
        intro j hj hjone
        simp only [List.length_append, List.length_singleton] at hj
        by_cases hlt : j.val < pref.length
        · exact hprev j hlt hjone
        · have hjcur : j.val = cur := by
            have hcurEq : cur = pref.length := by grind
            omega
          subst cur
          exact heq j hjone
  case vc2 => simp

def FixedLookupCoordinatesSpec (rho : WF.Valuation) (offset width : Nat)
    (bits : Vector (LC ℤ) width) (out : AffineSlope.Point) : Prop :=
  let raw := (combWindowValue bits).eval rho.int
  out.infinity.eval rho.int = 0 ∧
    out.X.intVal.eval rho.int =
      (fixedMagnitudeX offset (signedMagnitudeIndex width raw.toNat) : Int) ∧
    out.Y.intVal.eval rho.int = (selectedFixedY offset width raw.toNat : Int)

def FixedLookupSelectedSpec (rho : WF.Valuation) (offset width : Nat)
    (hwidth : 8 ≤ width) (bits : Vector (LC ℤ) width)
    (out : AffineSlope.Point) : Prop :=
  let table := fixedMagnitudeTable offset (2 ^ (width - 1))
  ∃ magnitudeBits : Vector (LC ℤ) (width - 1),
    XnorMagnitudeBitsSpec rho bits (by omega) magnitudeBits ∧
  ∃ innerIndex : Fin 128, ∃ outerIndex : Fin (2 ^ (width - 7)),
    (∑ i : Fin 7, (2 ^ i.val : Int) • magnitudeBits[i]).eval rho.int =
      innerIndex.val ∧
    ((∑ i : Fin (width - 8),
        (2 ^ i.val : Int) • magnitudeBits[i.val + 7]'(by omega)) +
      (2 ^ (width - 8) : Int) • bits[width - 1]'(by omega)).eval rho.int =
      outerIndex.val ∧
    out.infinity.eval rho.int = 0 ∧
    out.X.intVal.eval rho.int =
      (Reference.xNat table[128 * (outerIndex.val % 2 ^ (width - 8)) +
        innerIndex.val]! : Int) ∧
    out.Y.intVal.eval rho.int =
      (((if outerIndex.val / 2 ^ (width - 8) = 0 then
          base.modulus - Reference.yNat
            table[128 * (outerIndex.val % 2 ^ (width - 8)) + innerIndex.val]!
        else Reference.yNat
            table[128 * (outerIndex.val % 2 ^ (width - 8)) + innerIndex.val]!) : Nat) : Int)

theorem lookupFixedFactored_sound_aux {offset width : Nat}
    {hwidth : 8 ≤ width} {bits : Vector (LC ℤ) width}
    (hbits : ∀ i : Fin width,
      bits[i].eval ρ.int = 0 ∨ bits[i].eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (lookupFixedFactored offset width hwidth bits)
    ⦃⇓ out => ⌜FixedLookupSelectedSpec ρ offset width hwidth bits out⌝⦄ := by
  mvcgen -trivial [-Sound.interp_mapM, lookupFixedFactored,
    materializeFixedCoordinate]
  case vc1 =>
    intro xBits
    mvcgen
    intro yBits
    mvcgen
    rename_i magnitudeBits hmagnitude inner hinner outer houter X hX Y hY unit hcoords
    rcases hinner.2 with ⟨innerIndex, hinnerOne, hinnerValue, hinnerUnique⟩
    rcases houter.2 with ⟨outerIndex, houterOne, houterValue, _⟩
    have hinnerZero (j : Fin 128) (hne : j ≠ innerIndex) :
        inner.intBits[j].eval ρ.int = 0 := by
      have hj := hinner.1 j
      cases hb : inner.bits.bitsLE[j].eval ρ.bool <;>
        rw [hb] at hj <;> simp at hj
      · exact hj
      · exact (hne (hinnerUnique j hj)).elim
    have hselected := hcoords outerIndex houterOne
    unfold fixedInnerX fixedInnerY at hselected
    simp only [LC.eval_sum, LC.eval_nsmul, nsmul_eq_mul] at hselected
    rw [Aux.sum_mul_oneHot _ _ innerIndex hinnerOne hinnerZero,
      Aux.sum_mul_oneHot _ _ innerIndex hinnerOne hinnerZero] at hselected
    refine ⟨magnitudeBits, hmagnitude, innerIndex, outerIndex,
      hinnerValue, houterValue, ?_, hselected.1, hselected.2⟩
    simp

set_option maxHeartbeats 1000000 in
theorem factoredIndexArithmetic12
    (b : Fin 12 → Int) (x : Fin 11 → Int) (inner outer : Int)
    (hb : ∀ i, b i = 0 ∨ b i = 1)
    (hx : ∀ i, x i = 2 * b 11 * b ⟨i.val, by omega⟩ -
      b 11 - b ⟨i.val, by omega⟩ + 1)
    (hinner : inner = ∑ i : Fin 7, 2 ^ i.val * x ⟨i.val, by omega⟩)
    (houter : outer = (∑ i : Fin 4, 2 ^ i.val * x ⟨i.val + 7, by omega⟩) +
      16 * b 11) :
    let raw := ∑ i : Fin 12, 2 ^ i.val * b i
    0 ≤ raw ∧ raw < 4096 ∧
      (if 2048 ≤ raw then raw - 2048 else 2047 - raw) =
        inner + 128 * (outer % 16) ∧
      outer / 16 = b 11 ∧ (2048 ≤ raw ↔ b 11 = 1) := by
  dsimp
  have hb0 := hb 0; have hb1 := hb 1; have hb2 := hb 2
  have hb3 := hb 3; have hb4 := hb 4; have hb5 := hb 5
  have hb6 := hb 6; have hb7 := hb 7; have hb8 := hb 8
  have hb9 := hb 9; have hb10 := hb 10; have hb11 := hb 11
  have hx0 := hx 0; have hx1 := hx 1; have hx2 := hx 2
  have hx3 := hx 3; have hx4 := hx 4; have hx5 := hx 5
  have hx6 := hx 6; have hx7 := hx 7; have hx8 := hx 8
  have hx9 := hx 9; have hx10 := hx 10
  have hbnd (i : Fin 12) : 0 ≤ b i ∧ b i ≤ 1 := by
    rcases hb i with h | h <;> omega
  rcases hbnd 0 with ⟨hbnd0l, hbnd0u⟩
  rcases hbnd 1 with ⟨hbnd1l, hbnd1u⟩
  rcases hbnd 2 with ⟨hbnd2l, hbnd2u⟩
  rcases hbnd 3 with ⟨hbnd3l, hbnd3u⟩
  rcases hbnd 4 with ⟨hbnd4l, hbnd4u⟩
  rcases hbnd 5 with ⟨hbnd5l, hbnd5u⟩
  rcases hbnd 6 with ⟨hbnd6l, hbnd6u⟩
  rcases hbnd 7 with ⟨hbnd7l, hbnd7u⟩
  rcases hbnd 8 with ⟨hbnd8l, hbnd8u⟩
  rcases hbnd 9 with ⟨hbnd9l, hbnd9u⟩
  rcases hbnd 10 with ⟨hbnd10l, hbnd10u⟩
  norm_num [Fin.sum_univ_succ] at hinner houter ⊢
  have hlow : 0 ≤ b 0 + 2 * b 1 + 4 * b 2 + 8 * b 3 + 16 * b 4 +
      32 * b 5 + 64 * b 6 + 128 * b 7 + 256 * b 8 + 512 * b 9 +
      1024 * b 10 := by omega
  have hhigh : b 0 + 2 * b 1 + 4 * b 2 + 8 * b 3 + 16 * b 4 +
      32 * b 5 + 64 * b 6 + 128 * b 7 + 256 * b 8 + 512 * b 9 +
      1024 * b 10 ≤ 2047 := by omega
  have hxbool (i : Fin 11) : 0 ≤ x i ∧ x i ≤ 1 := by
    have hxi := hx i
    rcases hb 11 with hs | hs <;> rcases hb ⟨i.val, by omega⟩ with hi | hi <;>
      simp_all
  rcases hxbool 7 with ⟨hx7l, hx7u⟩
  rcases hxbool 8 with ⟨hx8l, hx8u⟩
  rcases hxbool 9 with ⟨hx9l, hx9u⟩
  rcases hxbool 10 with ⟨hx10l, hx10u⟩
  have hxOuterLow : 0 ≤ x 7 + 2 * x 8 + 4 * x 9 + 8 * x 10 := by omega
  have hxOuterHigh : x 7 + 2 * x 8 + 4 * x 9 + 8 * x 10 ≤ 15 := by omega
  rcases hb11 with hb11 | hb11 <;> simp_all <;> omega

set_option maxHeartbeats 1000000 in
theorem factoredIndexArithmetic13
    (b : Fin 13 → Int) (x : Fin 12 → Int) (inner outer : Int)
    (hb : ∀ i, b i = 0 ∨ b i = 1)
    (hx : ∀ i, x i = 2 * b 12 * b ⟨i.val, by omega⟩ -
      b 12 - b ⟨i.val, by omega⟩ + 1)
    (hinner : inner = ∑ i : Fin 7, 2 ^ i.val * x ⟨i.val, by omega⟩)
    (houter : outer = (∑ i : Fin 5, 2 ^ i.val * x ⟨i.val + 7, by omega⟩) +
      32 * b 12) :
    let raw := ∑ i : Fin 13, 2 ^ i.val * b i
    0 ≤ raw ∧ raw < 8192 ∧
      (if 4096 ≤ raw then raw - 4096 else 4095 - raw) =
        inner + 128 * (outer % 32) ∧
      outer / 32 = b 12 ∧ (4096 ≤ raw ↔ b 12 = 1) := by
  dsimp
  have hb0 := hb 0; have hb1 := hb 1; have hb2 := hb 2
  have hb3 := hb 3; have hb4 := hb 4; have hb5 := hb 5
  have hb6 := hb 6; have hb7 := hb 7; have hb8 := hb 8
  have hb9 := hb 9; have hb10 := hb 10; have hb11 := hb 11
  have hb12 := hb 12
  have hx0 := hx 0; have hx1 := hx 1; have hx2 := hx 2
  have hx3 := hx 3; have hx4 := hx 4; have hx5 := hx 5
  have hx6 := hx 6; have hx7 := hx 7; have hx8 := hx 8
  have hx9 := hx 9; have hx10 := hx 10; have hx11 := hx 11
  have hbnd (i : Fin 13) : 0 ≤ b i ∧ b i ≤ 1 := by
    rcases hb i with h | h <;> omega
  rcases hbnd 0 with ⟨hbnd0l, hbnd0u⟩
  rcases hbnd 1 with ⟨hbnd1l, hbnd1u⟩
  rcases hbnd 2 with ⟨hbnd2l, hbnd2u⟩
  rcases hbnd 3 with ⟨hbnd3l, hbnd3u⟩
  rcases hbnd 4 with ⟨hbnd4l, hbnd4u⟩
  rcases hbnd 5 with ⟨hbnd5l, hbnd5u⟩
  rcases hbnd 6 with ⟨hbnd6l, hbnd6u⟩
  rcases hbnd 7 with ⟨hbnd7l, hbnd7u⟩
  rcases hbnd 8 with ⟨hbnd8l, hbnd8u⟩
  rcases hbnd 9 with ⟨hbnd9l, hbnd9u⟩
  rcases hbnd 10 with ⟨hbnd10l, hbnd10u⟩
  rcases hbnd 11 with ⟨hbnd11l, hbnd11u⟩
  norm_num [Fin.sum_univ_succ] at hinner houter ⊢
  have hlow : 0 ≤ b 0 + 2 * b 1 + 4 * b 2 + 8 * b 3 + 16 * b 4 +
      32 * b 5 + 64 * b 6 + 128 * b 7 + 256 * b 8 + 512 * b 9 +
      1024 * b 10 + 2048 * b 11 := by omega
  have hhigh : b 0 + 2 * b 1 + 4 * b 2 + 8 * b 3 + 16 * b 4 +
      32 * b 5 + 64 * b 6 + 128 * b 7 + 256 * b 8 + 512 * b 9 +
      1024 * b 10 + 2048 * b 11 ≤ 4095 := by omega
  have hxbool (i : Fin 12) : 0 ≤ x i ∧ x i ≤ 1 := by
    have hxi := hx i
    rcases hb 12 with hs | hs <;> rcases hb ⟨i.val, by omega⟩ with hi | hi <;>
      simp_all
  rcases hxbool 7 with ⟨hx7l, hx7u⟩
  rcases hxbool 8 with ⟨hx8l, hx8u⟩
  rcases hxbool 9 with ⟨hx9l, hx9u⟩
  rcases hxbool 10 with ⟨hx10l, hx10u⟩
  rcases hxbool 11 with ⟨hx11l, hx11u⟩
  have hxOuterLow : 0 ≤ x 7 + 2 * x 8 + 4 * x 9 + 8 * x 10 + 16 * x 11 := by omega
  have hxOuterHigh : x 7 + 2 * x 8 + 4 * x 9 + 8 * x 10 + 16 * x 11 ≤ 31 := by omega
  rcases hb12 with hb12 | hb12 <;> simp_all <;> omega

@[simp] theorem fixedMagnitudePoints_length (step start : Reference.Point)
    (count : Nat) :
    (fixedMagnitudePoints step count start).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp [fixedMagnitudePoints, ih]

theorem fixedMagnitudePoints_getElem (step start : Reference.Point)
    {count i : Nat} (hi : i < count) :
    (fixedMagnitudePoints step count start)[i]'(by simpa using hi) =
      start + i • step := by
  induction count generalizing start i with
  | zero => omega
  | succ count ih =>
      cases i with
      | zero => simp [fixedMagnitudePoints]
      | succ i =>
          simp only [fixedMagnitudePoints, List.getElem_cons_succ]
          have hi' : i < count := by omega
          have hlist : i < (fixedMagnitudePoints step count (start + step)).length := by
            simpa using hi'
          calc
            (fixedMagnitudePoints step count (start + step))[i]'hlist =
                (start + step) + i • step :=
              ih (start + step) (i := i) hi'
            _ = start + (i + 1) • step := by
              rw [succ_nsmul']
              abel

theorem fixedMagnitudeTable_getElem (offset count : Nat)
    {i : Nat} (hi : i < count) :
    (fixedMagnitudeTable offset count)[i]'(by
      simp [fixedMagnitudeTable]
      exact hi) = fixedMagnitudePoint offset i := by
  unfold fixedMagnitudeTable
  change (fixedMagnitudePoints ((2 ^ (offset + 1)) • Reference.generator)
    count ((2 ^ offset) • Reference.generator))[i]'(by simpa using hi) = _
  rw [fixedMagnitudePoints_getElem _ _ hi]
  unfold fixedMagnitudePoint
  rw [show 2 ^ (offset + 1) = 2 * 2 ^ offset by
    simpa [pow_succ, Nat.mul_comm]]
  rw [← mul_nsmul]
  rw [← add_nsmul]
  congr 1
  ring

theorem fixedLookupSelected12_coordinates {offset : Nat}
    {bits : Vector (LC ℤ) 12} {out : AffineSlope.Point}
    (hbits : ∀ i : Fin 12,
      bits[i].eval ρ.int = 0 ∨ bits[i].eval ρ.int = 1)
    (hspec : FixedLookupSelectedSpec ρ offset 12 (by omega) bits out) :
    FixedLookupCoordinatesSpec ρ offset 12 bits out := by
  have htable (i : Fin 2048) :
      (fixedMagnitudeTable offset 2048)[i.val]! =
        fixedMagnitudePoint offset i.val := by
    rw [getElem!_pos _ _ (by simp [fixedMagnitudeTable])]
    exact fixedMagnitudeTable_getElem offset 2048 i.isLt
  rcases hspec with ⟨magnitudeBits, hmagnitude, innerIndex, outerIndex,
    hinner, houter, hinfinity, houtX, houtY⟩
  have hinner' : (innerIndex.val : Int) =
      ∑ i : Fin 7, 2 ^ i.val * magnitudeBits[i].eval ρ.int := by
    simpa only [LC.eval_sum, LC.eval_smul] using hinner.symm
  have houter' : (outerIndex.val : Int) =
      (∑ i : Fin 4, 2 ^ i.val *
        (magnitudeBits[i.val + 7]'(by omega)).eval ρ.int) +
        (16 : Int) * bits[11].eval ρ.int := by
    simpa only [LC.eval_add, LC.eval_sum, LC.eval_smul,
      show 2 ^ (12 - 8) = (16 : Int) by norm_num,
      show 12 - 1 = 11 by norm_num] using houter.symm
  have hx (i : Fin 11) : magnitudeBits[i].eval ρ.int =
      2 * bits[11].eval ρ.int * bits[i.val].eval ρ.int -
        bits[11].eval ρ.int - bits[i.val].eval ρ.int + 1 := by
    exact hmagnitude i
  have harith := factoredIndexArithmetic12
    (b := fun i => bits[i].eval ρ.int)
    (x := fun i => magnitudeBits[i].eval ρ.int)
    (inner := innerIndex.val) (outer := outerIndex.val)
    hbits hx hinner' houter'
  let raw : Int := ∑ i : Fin 12, 2 ^ i.val * bits[i].eval ρ.int
  have hrawEval : (combWindowValue bits).eval ρ.int = raw := by
    unfold combWindowValue raw
    simp only [LC.eval_sum, LC.eval_smul]
  have hraw0 : 0 ≤ raw := harith.1
  have hrawLt : raw < 4096 := harith.2.1
  let magnitude : Int := if 2048 ≤ raw then raw - 2048 else 2047 - raw
  have hmagnitudeEq : magnitude =
      innerIndex.val + 128 * (outerIndex.val % 16) := harith.2.2.1
  have hmagnitude0 : 0 ≤ magnitude := by
    unfold magnitude
    split <;> omega
  have hmagnitudeLt : magnitude < 2048 := by
    unfold magnitude
    split <;> omega
  let tableIndex : Nat := 128 * (outerIndex.val % 16) + innerIndex.val
  have htableIndex : tableIndex < 2048 := by
    dsimp [tableIndex]
    omega
  have hrawNat : (raw.toNat : Int) = raw := by
    exact Int.toNat_of_nonneg hraw0
  have hmagNat : signedMagnitudeIndex 12 raw.toNat = tableIndex := by
    unfold signedMagnitudeIndex tableIndex magnitude at *
    norm_num
    split <;> omega
  have htableAt := htable ⟨tableIndex, htableIndex⟩
  unfold FixedLookupCoordinatesSpec
  rw [hrawEval]
  refine ⟨hinfinity, ?_, ?_⟩
  · rw [hmagNat]
    unfold fixedMagnitudeX
    rw [← htableAt]
    simpa [tableIndex] using houtX
  · unfold selectedFixedY
    rw [hmagNat]
    unfold fixedMagnitudeY
    rw [← htableAt]
    rcases hbits 11 with hsign | hsign
    · have hrawSmallInt : ¬(2048 : Int) ≤ raw := by
        intro hlarge
        have := harith.2.2.2.2.mp hlarge
        omega
      have hrawSmall : raw.toNat < 2048 := by omega
      have houterSignInt : (outerIndex.val : Int) / 16 = 0 :=
        harith.2.2.2.1.trans hsign
      have houterSign : outerIndex.val / 16 = 0 := by
        exact_mod_cast houterSignInt
      have houterLow : outerIndex.val < 16 := by omega
      norm_num at houtY ⊢
      simp only [if_neg (not_le.mpr hrawSmall)]
      simp [houterLow, tableIndex] at houtY ⊢
      exact houtY
    · have hrawLarge : 2048 ≤ raw.toNat := by
        have hlargeInt : (2048 : Int) ≤ raw :=
          harith.2.2.2.2.mpr hsign
        omega
      have houterSignInt : (outerIndex.val : Int) / 16 = 1 :=
        harith.2.2.2.1.trans hsign
      have houterSign : outerIndex.val / 16 = 1 := by
        exact_mod_cast houterSignInt
      have houterHigh : 16 ≤ outerIndex.val := by omega
      norm_num at houtY ⊢
      simp only [if_pos hrawLarge]
      simp [show ¬outerIndex.val < 16 by omega, tableIndex] at houtY ⊢
      exact houtY

theorem fixedLookupSelected13_coordinates {offset : Nat}
    {bits : Vector (LC ℤ) 13} {out : AffineSlope.Point}
    (hbits : ∀ i : Fin 13,
      bits[i].eval ρ.int = 0 ∨ bits[i].eval ρ.int = 1)
    (hspec : FixedLookupSelectedSpec ρ offset 13 (by omega) bits out) :
    FixedLookupCoordinatesSpec ρ offset 13 bits out := by
  have htable (i : Fin 4096) :
      (fixedMagnitudeTable offset 4096)[i.val]! =
        fixedMagnitudePoint offset i.val := by
    rw [getElem!_pos _ _ (by simp [fixedMagnitudeTable])]
    exact fixedMagnitudeTable_getElem offset 4096 i.isLt
  rcases hspec with ⟨magnitudeBits, hmagnitude, innerIndex, outerIndex,
    hinner, houter, hinfinity, houtX, houtY⟩
  have hinner' : (innerIndex.val : Int) =
      ∑ i : Fin 7, 2 ^ i.val * magnitudeBits[i].eval ρ.int := by
    simpa only [LC.eval_sum, LC.eval_smul] using hinner.symm
  have houter' : (outerIndex.val : Int) =
      (∑ i : Fin 5, 2 ^ i.val *
        (magnitudeBits[i.val + 7]'(by omega)).eval ρ.int) +
        (32 : Int) * bits[12].eval ρ.int := by
    simpa only [LC.eval_add, LC.eval_sum, LC.eval_smul,
      show 2 ^ (13 - 8) = (32 : Int) by norm_num,
      show 13 - 1 = 12 by norm_num] using houter.symm
  have hx (i : Fin 12) : magnitudeBits[i].eval ρ.int =
      2 * bits[12].eval ρ.int * bits[i.val].eval ρ.int -
        bits[12].eval ρ.int - bits[i.val].eval ρ.int + 1 := by
    exact hmagnitude i
  have harith := factoredIndexArithmetic13
    (b := fun i => bits[i].eval ρ.int)
    (x := fun i => magnitudeBits[i].eval ρ.int)
    (inner := innerIndex.val) (outer := outerIndex.val)
    hbits hx hinner' houter'
  let raw : Int := ∑ i : Fin 13, 2 ^ i.val * bits[i].eval ρ.int
  have hrawEval : (combWindowValue bits).eval ρ.int = raw := by
    unfold combWindowValue raw
    simp only [LC.eval_sum, LC.eval_smul]
  have hraw0 : 0 ≤ raw := harith.1
  have hrawLt : raw < 8192 := harith.2.1
  let magnitude : Int := if 4096 ≤ raw then raw - 4096 else 4095 - raw
  have hmagnitudeEq : magnitude =
      innerIndex.val + 128 * (outerIndex.val % 32) := harith.2.2.1
  have hmagnitude0 : 0 ≤ magnitude := by
    unfold magnitude
    split <;> omega
  have hmagnitudeLt : magnitude < 4096 := by
    unfold magnitude
    split <;> omega
  let tableIndex : Nat := 128 * (outerIndex.val % 32) + innerIndex.val
  have htableIndex : tableIndex < 4096 := by
    dsimp [tableIndex]
    omega
  have hrawNat : (raw.toNat : Int) = raw := by
    exact Int.toNat_of_nonneg hraw0
  have hmagNat : signedMagnitudeIndex 13 raw.toNat = tableIndex := by
    unfold signedMagnitudeIndex tableIndex magnitude at *
    norm_num
    split <;> omega
  have htableAt := htable ⟨tableIndex, htableIndex⟩
  unfold FixedLookupCoordinatesSpec
  rw [hrawEval]
  refine ⟨hinfinity, ?_, ?_⟩
  · rw [hmagNat]
    unfold fixedMagnitudeX
    rw [← htableAt]
    simpa [tableIndex] using houtX
  · unfold selectedFixedY
    rw [hmagNat]
    unfold fixedMagnitudeY
    rw [← htableAt]
    rcases hbits 12 with hsign | hsign
    · have hrawSmallInt : ¬(4096 : Int) ≤ raw := by
        intro hlarge
        have := harith.2.2.2.2.mp hlarge
        omega
      have hrawSmall : raw.toNat < 4096 := by omega
      have houterSignInt : (outerIndex.val : Int) / 32 = 0 :=
        harith.2.2.2.1.trans hsign
      have houterSign : outerIndex.val / 32 = 0 := by
        exact_mod_cast houterSignInt
      have houterLow : outerIndex.val < 32 := by omega
      norm_num at houtY ⊢
      simp only [if_neg (not_le.mpr hrawSmall)]
      simp [houterLow, tableIndex] at houtY ⊢
      exact houtY
    · have hrawLarge : 4096 ≤ raw.toNat := by
        have hlargeInt : (4096 : Int) ≤ raw :=
          harith.2.2.2.2.mpr hsign
        omega
      have houterSignInt : (outerIndex.val : Int) / 32 = 1 :=
        harith.2.2.2.1.trans hsign
      have houterSign : outerIndex.val / 32 = 1 := by
        exact_mod_cast houterSignInt
      have houterHigh : 32 ≤ outerIndex.val := by omega
      norm_num at houtY ⊢
      simp only [if_pos hrawLarge]
      simp [show ¬outerIndex.val < 32 by omega, tableIndex] at houtY ⊢
      exact houtY

@[spec] theorem lookupFixedFactored12_sound {offset : Nat}
    {bits : Vector (LC ℤ) 12}
    (hbits : ∀ i : Fin 12,
      bits[i].eval ρ.int = 0 ∨ bits[i].eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (lookupFixedFactored offset 12 (by omega) bits)
    ⦃⇓ out => ⌜FixedLookupCoordinatesSpec ρ offset 12 bits out⌝⦄ := by
  apply Triple.iff_conseq.mp
    (lookupFixedFactored_sound_aux (ρ := ρ) (offset := offset)
      (width := 12) (hwidth := by omega) hbits) (by simp)
  simp only [PostCond.entails, SPred.entails_nil]
  exact ⟨fun _ h => fixedLookupSelected12_coordinates hbits h,
    ExceptConds.entails.refl _⟩

@[spec] theorem lookupFixedFactored13_sound {offset : Nat}
    {bits : Vector (LC ℤ) 13}
    (hbits : ∀ i : Fin 13,
      bits[i].eval ρ.int = 0 ∨ bits[i].eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Sound.interp ρ
      (lookupFixedFactored offset 13 (by omega) bits)
    ⦃⇓ out => ⌜FixedLookupCoordinatesSpec ρ offset 13 bits out⌝⦄ := by
  apply Triple.iff_conseq.mp
    (lookupFixedFactored_sound_aux (ρ := ρ) (offset := offset)
      (width := 13) (hwidth := by omega) hbits) (by simp)
  simp only [PostCond.entails, SPred.entails_nil]
  exact ⟨fun _ h => fixedLookupSelected13_coordinates hbits h,
    ExceptConds.entails.refl _⟩

private theorem complete_of_pure_pre_comb {α : Type} {P : Prop}
    {c : Circuit α} {Q : PostCond α (.except PUnit .pure)}
    (h : P → ⦃⌜True⌝⦄ Complete.interp ρ c ⦃Q⦄) :
    ⦃⌜P⌝⦄ Complete.interp ρ c ⦃Q⦄ := by
  rw [Triple.iff]
  simp only [SPred.entails_nil, SPred.down_pure_nil]
  intro hP
  have ht := h hP
  rw [Triple.iff] at ht
  simp only [SPred.entails_nil, SPred.down_pure_nil] at ht
  exact ht True.intro

theorem Reference.xNat_lt_base (p : Reference.Point) :
    Reference.xNat p < base.modulus := by
  rcases p with _ | ⟨x, y, hxy⟩
  · simp [Reference.xNat]
    exact base.positive
  · simpa [Reference.xNat] using x.val_lt

theorem Reference.yNat_lt_base (p : Reference.Point) :
    Reference.yNat p < base.modulus := by
  rcases p with _ | ⟨x, y, hxy⟩
  · simp [Reference.yNat]
    exact base.positive
  · simpa [Reference.yNat] using y.val_lt

theorem Reference.yNat_pos_of_nonzero_order {p : Reference.Point}
    (hp : p ≠ 0) (horder : scalarModulus • p = 0) :
    0 < Reference.yNat p := by
  have htwo : p + p ≠ 0 :=
    (Reference.Aux.no_two_torsion_of_order horder).resolve_left hp
  rcases p with _ | ⟨px, py, hcurve⟩
  · exact (hp rfl).elim
  · simp only [Reference.yNat]
    apply Nat.pos_of_ne_zero
    intro hyval
    have hpy : py = 0 := by
      exact (ZMod.val_eq_zero py).mp hyval
    apply htwo
    apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    rw [Reference.negY_eq, hpy]
    simp

theorem signedMagnitudeIndex_lt {width raw : Nat} (hwidth : 1 ≤ width)
    (hraw : raw < 2 ^ width) :
    signedMagnitudeIndex width raw < 2 ^ (width - 1) := by
  have hpow : 2 ^ width = 2 * 2 ^ (width - 1) := by
    obtain ⟨w, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : width ≠ 0)
    simp [pow_succ, Nat.mul_comm]
  unfold signedMagnitudeIndex
  split <;> omega

theorem fixedMagnitudePoint_nonzero {offset width raw : Nat}
    (hwidth : 1 ≤ width) (hfit : offset + width ≤ 252)
    (hraw : raw < 2 ^ width) :
    fixedMagnitudePoint offset (signedMagnitudeIndex width raw) ≠ 0 := by
  apply Reference.Aux.generator_nsmul_ne_zero
  · simp [fixedMagnitudePoint]
  · have hmag := signedMagnitudeIndex_lt hwidth hraw
    have hpow : 2 ^ width = 2 * 2 ^ (width - 1) := by
      obtain ⟨w, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : width ≠ 0)
      simp [pow_succ, Nat.mul_comm]
    have hodd : 2 * signedMagnitudeIndex width raw + 1 < 2 ^ width := by
      rw [hpow]
      omega
    have hcoeff : (2 * signedMagnitudeIndex width raw + 1) * 2 ^ offset <
        2 ^ (offset + width) := by
      rw [pow_add]
      have hmul := Nat.mul_lt_mul_of_pos_right hodd
        (show 0 < 2 ^ offset by positivity)
      simpa [Nat.mul_comm] using hmul
    exact hcoeff.trans (by
      calc
        2 ^ (offset + width) ≤ 2 ^ 252 :=
          Nat.pow_le_pow_right (n := 2) (by omega) hfit
        _ < scalarModulus := by norm_num [scalarModulus])

theorem selectedFixedY_lt_base {offset width raw : Nat}
    (hwidth : 1 ≤ width) (hfit : offset + width ≤ 252)
    (hraw : raw < 2 ^ width) :
    selectedFixedY offset width raw < base.modulus := by
  have hpNonzero := fixedMagnitudePoint_nonzero hwidth hfit hraw
  have hpOrder := Reference.Aux.order_nsmul
    Reference.Aux.generator_order
    ((2 * signedMagnitudeIndex width raw + 1) * 2 ^ offset)
  have hyPos : 0 < fixedMagnitudeY offset
      (signedMagnitudeIndex width raw) := by
    exact Reference.yNat_pos_of_nonzero_order hpNonzero hpOrder
  have hyLt : fixedMagnitudeY offset
      (signedMagnitudeIndex width raw) < base.modulus :=
    Reference.yNat_lt_base _
  unfold selectedFixedY
  split
  · exact hyLt
  · exact Nat.sub_lt base.positive hyPos

theorem combWindowValue_bounds {ρ : WF.Valuation}
    {width : Nat} {bits : Vector (LC ℤ) width}
    (hbits : ∀ i : Fin width,
      bits[i].eval ρ.int = 0 ∨ bits[i].eval ρ.int = 1) :
    0 ≤ (combWindowValue bits).eval ρ.int ∧
      (combWindowValue bits).eval ρ.int < 2 ^ width := by
  let f : Fin width → Bool := fun i => (bits.get i).eval ρ.int = 1
  have hbits' (i : Fin width) :
      (bits.get i).eval ρ.int = 0 ∨ (bits.get i).eval ρ.int = 1 := by
    rw [Vector.get_eq_getElem]
    exact hbits ⟨i.val, i.isLt⟩
  have hbit (i : Fin width) :
      (bits.get i).eval ρ.int = (f i).toInt := by
    change (bits.get i).eval ρ.int =
      (decide ((bits.get i).eval ρ.int = 1)).toInt
    by_cases hone : (bits.get i).eval ρ.int = 1
    · simp [hone]
    · have hzero := (hbits' i).resolve_right hone
      simp [hone, hzero]
  have heval : (combWindowValue bits).eval ρ.int = (Nat.ofBits f : Int) := by
    unfold combWindowValue
    rw [LC.eval_sum]
    calc
      ∑ i : Fin width, LC.eval ρ.int ((2 ^ i.val : Int) • bits[i]) =
          ∑ i : Fin width, 2 ^ i.val * (f i).toInt := by
        apply Finset.sum_congr rfl
        intro i _
        rw [LC.eval_smul]
        congr 1
        exact hbit i
      _ = (Nat.ofBits f : Int) := (Aux.natCast_ofBits_eq_sum f).symm
  rw [heval]
  constructor
  · exact_mod_cast Nat.zero_le (Nat.ofBits f)
  · exact_mod_cast Nat.ofBits_lt_two_pow f

theorem FixedLookupCoordinatesSpec.normalizedRep
    {offset width : Nat} {bits : Vector (LC ℤ) width}
    {out : AffineSlope.Point}
    (hspec : FixedLookupCoordinatesSpec ρ offset width bits out)
    (hwidth : 1 ≤ width) (hfit : offset + width ≤ 252)
    (hraw : 0 ≤ (combWindowValue bits).eval ρ.int ∧
      (combWindowValue bits).eval ρ.int < 2 ^ width) :
    Reference.NormalizedRep ρ out
      (fixedSignedPoint offset width
        ((combWindowValue bits).eval ρ.int).toNat) := by
  let raw := (combWindowValue bits).eval ρ.int
  let rawNat := raw.toNat
  let magnitude := signedMagnitudeIndex width rawNat
  let point := fixedMagnitudePoint offset magnitude
  have hrawNat : (rawNat : Int) = raw := Int.toNat_of_nonneg hraw.1
  have hrawNatLt : rawNat < 2 ^ width :=
    (Int.toNat_lt hraw.1).2 hraw.2
  have hpoint : point ≠ 0 := by
    exact fixedMagnitudePoint_nonzero hwidth hfit hrawNatLt
  have hpointOrder : scalarModulus • point = 0 := by
    exact Reference.Aux.order_nsmul Reference.Aux.generator_order
      ((2 * magnitude + 1) * 2 ^ offset)
  have hyPos : 0 < fixedMagnitudeY offset magnitude := by
    exact Reference.yNat_pos_of_nonzero_order hpoint hpointOrder
  have hspec' := hspec
  unfold FixedLookupCoordinatesSpec at hspec'
  change out.infinity.eval ρ.int = 0 ∧
      out.X.intVal.eval ρ.int = (fixedMagnitudeX offset magnitude : Int) ∧
      out.Y.intVal.eval ρ.int = (selectedFixedY offset width rawNat : Int)
    at hspec'
  rcases hspec' with ⟨hinfinity, hX, hY⟩
  constructor
  · constructor
    · exact Or.inl hinfinity
    · unfold Reference.circuitCoordinates
      rw [if_neg (by omega)]
      by_cases hpositive : 2 ^ (width - 1) ≤ rawNat
      · have hsigned : fixedSignedPoint offset width rawNat = point := by
          simp [fixedSignedPoint, hpositive, point, magnitude,
            signedMagnitudeIndex]
        rw [hsigned]
        rcases hp : point with _ | ⟨px, py, hcurve⟩
        · exact (hpoint hp).elim
        · simp only [Reference.coordinates]
          have hp' : fixedMagnitudePoint offset magnitude =
              .some px py hcurve := by simpa [point] using hp
          apply congrArg₂ Reference.Coordinates.finite
          · unfold Modular.Lazy.evalZMod
            rw [hX]
            unfold fixedMagnitudeX
            rw [hp']
            simp only [Reference.xNat]
            exact ZMod.natCast_zmod_val px
          · unfold Modular.Lazy.evalZMod
            rw [hY]
            unfold selectedFixedY
            rw [if_pos hpositive]
            change (Int.castRingHom (ZMod base.modulus))
              (fixedMagnitudeY offset magnitude : Int) = py
            unfold fixedMagnitudeY
            rw [hp']
            simp only [Reference.yNat]
            exact ZMod.natCast_zmod_val py
      · have hsigned : fixedSignedPoint offset width rawNat = -point := by
          simp [fixedSignedPoint, hpositive, point, magnitude,
            signedMagnitudeIndex]
        rw [hsigned]
        rcases hp : point with _ | ⟨px, py, hcurve⟩
        · exact (hpoint hp).elim
        · simp only [WeierstrassCurve.Affine.Point.neg_some,
            Reference.coordinates]
          have hp' : fixedMagnitudePoint offset magnitude =
              .some px py hcurve := by simpa [point] using hp
          apply congrArg₂ Reference.Coordinates.finite
          · unfold Modular.Lazy.evalZMod
            rw [hX]
            unfold fixedMagnitudeX
            rw [hp']
            simp only [Reference.xNat]
            exact ZMod.natCast_zmod_val px
          · unfold Modular.Lazy.evalZMod
            rw [hY]
            unfold selectedFixedY
            rw [if_neg hpositive]
            change (Int.castRingHom (ZMod base.modulus))
              (base.modulus - fixedMagnitudeY offset magnitude : Nat) = _
            unfold fixedMagnitudeY at hyPos ⊢
            rw [hp'] at hyPos ⊢
            simp only [Reference.yNat] at hyPos ⊢
            rw [Nat.cast_sub (Nat.le_of_lt py.val_lt)]
            simp [Reference.negY_eq]
  · intro hzero
    by_cases hpositive : 2 ^ (width - 1) ≤ rawNat
    · have hsigned : fixedSignedPoint offset width rawNat = point := by
        simp [fixedSignedPoint, hpositive, point, magnitude,
          signedMagnitudeIndex]
      exact (hpoint (hsigned ▸ hzero)).elim
    · have hsigned : fixedSignedPoint offset width rawNat = -point := by
        simp [fixedSignedPoint, hpositive, point, magnitude,
          signedMagnitudeIndex]
      exact (hpoint (neg_eq_zero.mp (hsigned ▸ hzero))).elim

theorem Reference.normalizedRep_of_natCoordinates {p : Reference.Point}
    {out : AffineSlope.Point} (hp : p ≠ 0)
    (hinfinity : out.infinity.eval ρ.int = 0)
    (hX : out.X.intVal.eval ρ.int = (Reference.xNat p : Int))
    (hY : out.Y.intVal.eval ρ.int = (Reference.yNat p : Int)) :
    Reference.NormalizedRep ρ out p := by
  rcases hpoint : p with _ | ⟨px, py, hcurve⟩
  · exact (hp hpoint).elim
  · constructor
    · constructor
      · exact Or.inl hinfinity
      · unfold Reference.circuitCoordinates
        rw [if_neg (by omega)]
        simp only [Reference.coordinates]
        apply congrArg₂ Reference.Coordinates.finite
        · unfold Modular.Lazy.evalZMod
          rw [hX, hpoint]
          simp only [Reference.xNat]
          exact ZMod.natCast_zmod_val px
        · unfold Modular.Lazy.evalZMod
          rw [hY, hpoint]
          simp only [Reference.yNat]
          exact ZMod.natCast_zmod_val py
    · intro hzero
      simp at hzero

theorem topCombRaw_bounds {k : Fn} (hk : k.val.Valid ρ) :
    8 ≤ (combWindowValue (combWindowBits k 252 4 (by omega))).eval ρ.int ∧
      (combWindowValue (combWindowBits k 252 4 (by omega))).eval ρ.int < 16 := by
  let bits := combWindowBits k 252 4 (by omega)
  have hbits : ∀ i : Fin 4,
      bits[i].eval ρ.int = 0 ∨ bits[i].eval ρ.int = 1 := by
    intro i
    simpa [bits, combWindowBits] using
      combBit_bool hk (252 + i.val) (by omega)
  have h3 : bits[3].eval ρ.int = 1 := by
    simp [bits, combWindowBits, combBit]
  have h0 := hbits 0; have h1 := hbits 1; have h2 := hbits 2
  change 8 ≤ (combWindowValue bits).eval ρ.int ∧
    (combWindowValue bits).eval ρ.int < 16
  unfold combWindowValue
  simp only [LC.eval_sum, LC.eval_smul]
  norm_num [Fin.sum_univ_succ] at h0 h1 h2 h3 ⊢
  omega

theorem topCombPoint_nonzero {raw parity : Nat}
    (hrawLow : 8 ≤ raw) (hrawHigh : raw < 16)
    (hparity : parity ≤ 1) :
    topCombPoint raw parity ≠ 0 := by
  unfold topCombPoint
  simp only [dif_pos hrawLow]
  apply Reference.Aux.generator_nsmul_ne_zero
  · have hp : 0 < 2 ^ 252 := by positivity
    omega
  · have hp : 0 < 2 ^ 252 := by positivity
    calc
      (2 * raw + 1 - 16) * 2 ^ 252 - (1 - parity) ≤
          15 * 2 ^ 252 := by omega
      _ < scalarModulus := by norm_num [scalarModulus]

theorem fixedFactoredCoordinates12_hint {offset : Nat}
    {bits : Vector (LC ℤ) 12} {magnitudeBits : Vector (LC ℤ) 11}
    {inner : U 128} {outer : U (2 ^ (12 - 7))} {X Y : U 256}
    (hbits : ∀ i : Fin 12,
      bits[i].eval ρ.int = 0 ∨ bits[i].eval ρ.int = 1)
    (hmagnitude : XnorMagnitudeBitsSpec ρ bits (by omega) magnitudeBits)
    (hinner : IndicatorsSpec ρ
      (∑ i : Fin 7, (2 ^ i.val : Int) • magnitudeBits[i]) inner)
    (houter : IndicatorsSpec ρ
      ((∑ i : Fin 4, (2 ^ i.val : Int) •
        magnitudeBits[i.val + 7]'(by omega)) +
        (2 ^ (12 - 8) : Int) • bits[12 - 1]) outer)
    (hX : X.intVal.eval ρ.int =
      (Reference.xNat ((fixedMagnitudeTable offset 2048)[signedMagnitudeIndex 12
          ((combWindowValue bits).eval ρ.int).toNat]!) : Int))
    (hY : Y.intVal.eval ρ.int =
      ((if 2048 ≤ ((combWindowValue bits).eval ρ.int).toNat then
          Reference.yNat ((fixedMagnitudeTable offset 2048)[signedMagnitudeIndex 12
              ((combWindowValue bits).eval ρ.int).toNat]!)
        else base.modulus -
          Reference.yNat ((fixedMagnitudeTable offset 2048)[signedMagnitudeIndex 12
              ((combWindowValue bits).eval ρ.int).toNat]!)) : Nat)) :
    ∀ o : Fin (2 ^ (12 - 7)), outer.intBits[o].eval ρ.int = 1 →
      X.intVal.eval ρ.int =
        (fixedInnerX (fixedMagnitudeTable offset 2048) 12 o.val inner).eval ρ.int ∧
      Y.intVal.eval ρ.int =
        (fixedInnerY (fixedMagnitudeTable offset 2048) 12 o.val inner).eval ρ.int := by
  rcases hinner.2 with ⟨innerIndex, hinnerOne, hinnerValue, hinnerUnique⟩
  rcases houter.2 with ⟨outerIndex, houterOne, houterValue, houterUnique⟩
  have hinnerZero (j : Fin 128) (hne : j ≠ innerIndex) :
      inner.intBits[j].eval ρ.int = 0 := by
    have hj := hinner.1 j
    cases hb : inner.bits.bitsLE[j].eval ρ.bool <;>
      rw [hb] at hj <;> simp at hj
    · exact hj
    · exact (hne (hinnerUnique j hj)).elim
  have hinner' : (innerIndex.val : Int) =
      ∑ i : Fin 7, 2 ^ i.val * magnitudeBits[i].eval ρ.int := by
    simpa only [LC.eval_sum, LC.eval_smul] using hinnerValue.symm
  have houter' : (outerIndex.val : Int) =
      (∑ i : Fin 4, 2 ^ i.val *
        (magnitudeBits[i.val + 7]'(by omega)).eval ρ.int) +
        16 * bits[11].eval ρ.int := by
    simp only [LC.eval_add, LC.eval_sum, LC.eval_smul,
      show 2 ^ (12 - 8) = (16 : Int) by norm_num,
      show 12 - 1 = 11 by norm_num] at houterValue
    convert houterValue.symm using 1 <;> norm_num
  have hxnor (i : Fin 11) : magnitudeBits[i].eval ρ.int =
      2 * bits[11].eval ρ.int * bits[i.val].eval ρ.int -
        bits[11].eval ρ.int - bits[i.val].eval ρ.int + 1 := hmagnitude i
  have harith := factoredIndexArithmetic12
    (b := fun i => bits[i].eval ρ.int)
    (x := fun i => magnitudeBits[i].eval ρ.int)
    (inner := innerIndex.val) (outer := outerIndex.val)
    hbits hxnor hinner' houter'
  let raw : Int := ∑ i : Fin 12, 2 ^ i.val * bits[i].eval ρ.int
  have hrawEval : (combWindowValue bits).eval ρ.int = raw := by
    unfold combWindowValue raw
    simp only [LC.eval_sum, LC.eval_smul]
  have hraw0 : 0 ≤ raw := harith.1
  have hrawLt : raw < 4096 := harith.2.1
  let tableIndex : Nat := 128 * (outerIndex.val % 16) + innerIndex.val
  have hindex : signedMagnitudeIndex 12 raw.toNat = tableIndex := by
    unfold signedMagnitudeIndex tableIndex
    norm_num
    have hrawNat : (raw.toNat : Int) = raw := Int.toNat_of_nonneg hraw0
    split <;> omega
  intro o hone
  have ho : o = outerIndex := houterUnique o hone
  subst o
  unfold fixedInnerX fixedInnerY
  simp only [LC.eval_sum, LC.eval_nsmul, nsmul_eq_mul]
  rw [Aux.sum_mul_oneHot _ _ innerIndex hinnerOne hinnerZero,
    Aux.sum_mul_oneHot _ _ innerIndex hinnerOne hinnerZero]
  rw [hrawEval] at hX hY
  refine ⟨?_, ?_⟩
  · rw [hX, hindex]
    rfl
  · rw [hY, hindex]
    rcases hbits 11 with hsign | hsign
    · have hrawSmallInt : ¬(2048 : Int) ≤ raw := by
        intro hlarge
        exact (by omega : False)
      have hrawSmall : raw.toNat < 2048 := by omega
      have houterSignInt : (outerIndex.val : Int) / 16 = 0 :=
        harith.2.2.2.1.trans hsign
      have houterSign : outerIndex.val / 16 = 0 := by
        exact_mod_cast houterSignInt
      simp [tableIndex, hrawSmall, houterSign]
    · have hrawLargeInt : (2048 : Int) ≤ raw :=
        harith.2.2.2.2.mpr hsign
      have hrawLarge : 2048 ≤ raw.toNat := by omega
      have houterSignInt : (outerIndex.val : Int) / 16 = 1 :=
        harith.2.2.2.1.trans hsign
      have houterSign : outerIndex.val / 16 = 1 := by
        exact_mod_cast houterSignInt
      simp [tableIndex, hrawLarge, houterSign]

theorem fixedFactoredCoordinates13_hint {offset : Nat}
    {bits : Vector (LC ℤ) 13} {magnitudeBits : Vector (LC ℤ) 12}
    {inner : U 128} {outer : U (2 ^ (13 - 7))} {X Y : U 256}
    (hbits : ∀ i : Fin 13,
      bits[i].eval ρ.int = 0 ∨ bits[i].eval ρ.int = 1)
    (hmagnitude : XnorMagnitudeBitsSpec ρ bits (by omega) magnitudeBits)
    (hinner : IndicatorsSpec ρ
      (∑ i : Fin 7, (2 ^ i.val : Int) • magnitudeBits[i]) inner)
    (houter : IndicatorsSpec ρ
      ((∑ i : Fin 5, (2 ^ i.val : Int) •
        magnitudeBits[i.val + 7]'(by omega)) +
        (2 ^ (13 - 8) : Int) • bits[13 - 1]) outer)
    (hX : X.intVal.eval ρ.int =
      (Reference.xNat ((fixedMagnitudeTable offset 4096)[signedMagnitudeIndex 13
          ((combWindowValue bits).eval ρ.int).toNat]!) : Int))
    (hY : Y.intVal.eval ρ.int =
      ((if 4096 ≤ ((combWindowValue bits).eval ρ.int).toNat then
          Reference.yNat ((fixedMagnitudeTable offset 4096)[signedMagnitudeIndex 13
              ((combWindowValue bits).eval ρ.int).toNat]!)
        else base.modulus -
          Reference.yNat ((fixedMagnitudeTable offset 4096)[signedMagnitudeIndex 13
              ((combWindowValue bits).eval ρ.int).toNat]!)) : Nat)) :
    ∀ o : Fin (2 ^ (13 - 7)), outer.intBits[o].eval ρ.int = 1 →
      X.intVal.eval ρ.int =
        (fixedInnerX (fixedMagnitudeTable offset 4096) 13 o.val inner).eval ρ.int ∧
      Y.intVal.eval ρ.int =
        (fixedInnerY (fixedMagnitudeTable offset 4096) 13 o.val inner).eval ρ.int := by
  rcases hinner.2 with ⟨innerIndex, hinnerOne, hinnerValue, hinnerUnique⟩
  rcases houter.2 with ⟨outerIndex, houterOne, houterValue, houterUnique⟩
  have hinnerZero (j : Fin 128) (hne : j ≠ innerIndex) :
      inner.intBits[j].eval ρ.int = 0 := by
    have hj := hinner.1 j
    cases hb : inner.bits.bitsLE[j].eval ρ.bool <;>
      rw [hb] at hj <;> simp at hj
    · exact hj
    · exact (hne (hinnerUnique j hj)).elim
  have hinner' : (innerIndex.val : Int) =
      ∑ i : Fin 7, 2 ^ i.val * magnitudeBits[i].eval ρ.int := by
    simpa only [LC.eval_sum, LC.eval_smul] using hinnerValue.symm
  have houter' : (outerIndex.val : Int) =
      (∑ i : Fin 5, 2 ^ i.val *
        (magnitudeBits[i.val + 7]'(by omega)).eval ρ.int) +
        32 * bits[12].eval ρ.int := by
    simp only [LC.eval_add, LC.eval_sum, LC.eval_smul,
      show 2 ^ (13 - 8) = (32 : Int) by norm_num,
      show 13 - 1 = 12 by norm_num] at houterValue
    convert houterValue.symm using 1 <;> norm_num
  have hxnor (i : Fin 12) : magnitudeBits[i].eval ρ.int =
      2 * bits[12].eval ρ.int * bits[i.val].eval ρ.int -
        bits[12].eval ρ.int - bits[i.val].eval ρ.int + 1 := hmagnitude i
  have harith := factoredIndexArithmetic13
    (b := fun i => bits[i].eval ρ.int)
    (x := fun i => magnitudeBits[i].eval ρ.int)
    (inner := innerIndex.val) (outer := outerIndex.val)
    hbits hxnor hinner' houter'
  let raw : Int := ∑ i : Fin 13, 2 ^ i.val * bits[i].eval ρ.int
  have hrawEval : (combWindowValue bits).eval ρ.int = raw := by
    unfold combWindowValue raw
    simp only [LC.eval_sum, LC.eval_smul]
  have hraw0 : 0 ≤ raw := harith.1
  have hrawLt : raw < 8192 := harith.2.1
  let tableIndex : Nat := 128 * (outerIndex.val % 32) + innerIndex.val
  have hindex : signedMagnitudeIndex 13 raw.toNat = tableIndex := by
    unfold signedMagnitudeIndex tableIndex
    norm_num
    have hrawNat : (raw.toNat : Int) = raw := Int.toNat_of_nonneg hraw0
    split <;> omega
  intro o hone
  have ho : o = outerIndex := houterUnique o hone
  subst o
  unfold fixedInnerX fixedInnerY
  simp only [LC.eval_sum, LC.eval_nsmul, nsmul_eq_mul]
  rw [Aux.sum_mul_oneHot _ _ innerIndex hinnerOne hinnerZero,
    Aux.sum_mul_oneHot _ _ innerIndex hinnerOne hinnerZero]
  rw [hrawEval] at hX hY
  refine ⟨?_, ?_⟩
  · rw [hX, hindex]
    rfl
  · rw [hY, hindex]
    rcases hbits 12 with hsign | hsign
    · have hrawSmallInt : ¬(4096 : Int) ≤ raw := by
        intro hlarge
        exact (by omega : False)
      have hrawSmall : raw.toNat < 4096 := by omega
      have houterSignInt : (outerIndex.val : Int) / 32 = 0 :=
        harith.2.2.2.1.trans hsign
      have houterSign : outerIndex.val / 32 = 0 := by
        exact_mod_cast houterSignInt
      simp [tableIndex, hrawSmall, houterSign]
    · have hrawLargeInt : (4096 : Int) ≤ raw :=
        harith.2.2.2.2.mpr hsign
      have hrawLarge : 4096 ≤ raw.toNat := by omega
      have houterSignInt : (outerIndex.val : Int) / 32 = 1 :=
        harith.2.2.2.1.trans hsign
      have houterSign : outerIndex.val / 32 = 1 := by
        exact_mod_cast houterSignInt
      simp [tableIndex, hrawLarge, houterSign]

@[spec] theorem lookupFixedFactored12_complete {offset : Nat}
    {bits : Vector (LC ℤ) 12}
    (hbits : ∀ i : Fin 12,
      bits[i].eval ρ.int = 0 ∨ bits[i].eval ρ.int = 1)
    (hselectedY : selectedFixedY offset 12
      ((combWindowValue bits).eval ρ.int).toNat < base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (lookupFixedFactored offset 12 (by omega) bits)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      FixedLookupCoordinatesSpec ρ offset 12 bits out⌝⦄ := by
  rw [lookupFixedFactored]
  simp only [materializeFixedCoordinate]
  rw [Complete.interp_bind]
  apply Triple.bind
  · exact xnorMagnitudeBits_complete hbits
  · intro magnitudeBits
    apply complete_of_pure_pre_comb
    intro hmagnitude
    have hmagBits (i : Fin 11) :
        magnitudeBits[i].eval ρ.int = 0 ∨
          magnitudeBits[i].eval ρ.int = 1 :=
      XnorBitSpec.bool (hmagnitude i) (hbits 11)
        (hbits ⟨i.val, by omega⟩)
    have hmagBounds (i : Fin 11) :
        0 ≤ magnitudeBits[i].eval ρ.int ∧
          magnitudeBits[i].eval ρ.int ≤ 1 := by
      rcases hmagBits i with h | h <;> omega
    have hbitBounds (i : Fin 12) :
        0 ≤ bits[i].eval ρ.int ∧ bits[i].eval ρ.int ≤ 1 := by
      rcases hbits i with h | h <;> omega
    have hinnerLow : 0 ≤
        (∑ i : Fin 7, (2 ^ i.val : Int) • magnitudeBits[i]).eval ρ.int := by
      simp only [LC.eval_sum, LC.eval_smul]
      have h0 := hmagBounds 0; have h1 := hmagBounds 1
      have h2 := hmagBounds 2; have h3 := hmagBounds 3
      have h4 := hmagBounds 4; have h5 := hmagBounds 5
      have h6 := hmagBounds 6
      norm_num [Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6 ⊢
      omega
    have hinnerHigh :
        (∑ i : Fin 7, (2 ^ i.val : Int) • magnitudeBits[i]).eval ρ.int < 128 := by
      simp only [LC.eval_sum, LC.eval_smul]
      have h0 := hmagBounds 0; have h1 := hmagBounds 1
      have h2 := hmagBounds 2; have h3 := hmagBounds 3
      have h4 := hmagBounds 4; have h5 := hmagBounds 5
      have h6 := hmagBounds 6
      norm_num [Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6 ⊢
      omega
    have houterLow : 0 ≤
        ((∑ i : Fin 4, (2 ^ i.val : Int) •
          magnitudeBits[i.val + 7]'(by omega)) +
          (16 : Int) • bits[11]).eval ρ.int := by
      simp only [LC.eval_add, LC.eval_sum, LC.eval_smul]
      have h7 := hmagBounds 7; have h8 := hmagBounds 8
      have h9 := hmagBounds 9; have h10 := hmagBounds 10
      have hs := hbitBounds 11
      norm_num [Fin.sum_univ_succ] at h7 h8 h9 h10 hs ⊢
      omega
    have houterHigh :
        ((∑ i : Fin 4, (2 ^ i.val : Int) •
          magnitudeBits[i.val + 7]'(by omega)) +
          (16 : Int) • bits[11]).eval ρ.int < 32 := by
      simp only [LC.eval_add, LC.eval_sum, LC.eval_smul]
      have h7 := hmagBounds 7; have h8 := hmagBounds 8
      have h9 := hmagBounds 9; have h10 := hmagBounds 10
      have hs := hbitBounds 11
      norm_num [Fin.sum_univ_succ] at h7 h8 h9 h10 hs ⊢
      omega
    mvcgen
    case vc5 =>
      let raw := (combWindowValue bits).eval ρ.int
      let table := fixedMagnitudeTable offset 2048
      let xValue := Reference.xNat table[signedMagnitudeIndex 12 raw.toNat]!
      refine ⟨Vector.ofFn fun i : Fin 256 => xValue.testBit i.val, ?_, ?_⟩
      · rfl
      · mvcgen
        case vc1 =>
          let yValue := if 2048 ≤ raw.toNat then
              Reference.yNat table[signedMagnitudeIndex 12 raw.toNat]!
            else base.modulus -
              Reference.yNat table[signedMagnitudeIndex 12 raw.toNat]!
          refine ⟨Vector.ofFn fun i : Fin 256 => yValue.testBit i.val, ?_, ?_⟩
          · rfl
          · mvcgen
            case vc1.houter =>
              rename_i inner hinner outer houter X hX Y hY
              exact houter.1
            case vc2.heq =>
              rename_i inner hinner outer houter X hX Y hY
              have hxFit : xValue < 2 ^ 256 :=
                (Reference.xNat_lt_base _).trans (by
                  norm_num [base, baseModulus])
              let xBits : Vector Bool 256 :=
                Vector.ofFn fun i => xValue.testBit i.val
              have hxWord :
                  (Word.eval ρ.bool { bitsLE := xBits.map LC.ofConst }).toNat =
                    xValue := by
                rw [show xBits.map LC.ofConst =
                    Vector.ofFn fun i : Fin 256 =>
                      LC.ofConst (xValue.testBit i.val) by
                  ext i
                  simp [xBits]]
                exact Modular.Aux.constWord_eval_toNat xValue hxFit ρ
              have hxEval : X.intVal.eval ρ.int = xValue := by
                rw [U.Rel.intVal hX, hxWord]
              have hyLe : yValue ≤ base.modulus := by
                dsimp [yValue]
                split
                · exact Nat.le_of_lt (Reference.yNat_lt_base _)
                · exact Nat.sub_le _ _
              have hyFit : yValue < 2 ^ 256 :=
                lt_of_le_of_lt hyLe (by
                  norm_num [base, baseModulus])
              let yBits : Vector Bool 256 :=
                Vector.ofFn fun i => yValue.testBit i.val
              have hyWord :
                  (Word.eval ρ.bool { bitsLE := yBits.map LC.ofConst }).toNat =
                    yValue := by
                rw [show yBits.map LC.ofConst =
                    Vector.ofFn fun i : Fin 256 =>
                      LC.ofConst (yValue.testBit i.val) by
                  ext i
                  simp [yBits]]
                exact Modular.Aux.constWord_eval_toNat yValue hyFit ρ
              have hyEval : Y.intVal.eval ρ.int = yValue := by
                rw [U.Rel.intVal hY, hyWord]
              simpa [raw, table, xValue, yValue] using
                (fixedFactoredCoordinates12_hint (ρ := ρ) (offset := offset)
                  hbits hmagnitude hinner houter hxEval hyEval)
            case vc3.success =>
              rename_i inner hinner outer houter X hX Y hY unit hcoords
              rcases hinner.2 with
                ⟨innerIndex, hinnerOne, hinnerValue, hinnerUnique⟩
              rcases houter.2 with
                ⟨outerIndex, houterOne, houterValue, _⟩
              have hinnerZero (j : Fin 128) (hne : j ≠ innerIndex) :
                  inner.intBits[j].eval ρ.int = 0 := by
                have hj := hinner.1 j
                cases hb : inner.bits.bitsLE[j].eval ρ.bool <;>
                  rw [hb] at hj <;> simp at hj
                · exact hj
                · exact (hne (hinnerUnique j hj)).elim
              have hselected := hcoords outerIndex houterOne
              unfold fixedInnerX fixedInnerY at hselected
              simp only [LC.eval_sum, LC.eval_nsmul, nsmul_eq_mul] at hselected
              rw [Aux.sum_mul_oneHot _ _ innerIndex hinnerOne hinnerZero,
                Aux.sum_mul_oneHot _ _ innerIndex hinnerOne hinnerZero] at hselected
              let out : AffineSlope.Point :=
                ⟨⟨X.intVal, 2⟩, ⟨Y.intVal, 2⟩, 0⟩
              have hspec : FixedLookupSelectedSpec ρ offset 12 (by omega)
                  bits out := by
                refine ⟨magnitudeBits, hmagnitude, innerIndex, outerIndex,
                  hinnerValue, houterValue, ?_, hselected.1, hselected.2⟩
                simp [out]
              have hcoord := fixedLookupSelected12_coordinates hbits hspec
              have hxLt : X.intVal.eval ρ.int < base.modulus := by
                rw [hcoord.2.1]
                exact_mod_cast Reference.xNat_lt_base _
              have hyLt : Y.intVal.eval ρ.int < base.modulus := by
                rw [hcoord.2.2]
                exact_mod_cast hselectedY
              change out.Valid ρ ∧ FixedLookupCoordinatesSpec ρ offset 12 bits out
              refine ⟨?_, hcoord⟩
              unfold AffineSlope.Point.Valid Modular.Lazy.Rep.Valid
              simp only [out]
              refine ⟨trivial, ⟨U.intVal_nonneg X hX.1, ?_⟩, hxLt,
                trivial, ⟨U.intVal_nonneg Y hY.1, ?_⟩, hyLt, by simp⟩
              · have hp : (0 : Int) < base.modulus := by
                  exact_mod_cast base.positive
                omega
              · have hp : (0 : Int) < base.modulus := by
                  exact_mod_cast base.positive
                omega

@[spec] theorem lookupFixedFactored13_complete {offset : Nat}
    {bits : Vector (LC ℤ) 13}
    (hbits : ∀ i : Fin 13,
      bits[i].eval ρ.int = 0 ∨ bits[i].eval ρ.int = 1)
    (hselectedY : selectedFixedY offset 13
      ((combWindowValue bits).eval ρ.int).toNat < base.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ
      (lookupFixedFactored offset 13 (by omega) bits)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      FixedLookupCoordinatesSpec ρ offset 13 bits out⌝⦄ := by
  rw [lookupFixedFactored]
  simp only [materializeFixedCoordinate]
  rw [Complete.interp_bind]
  apply Triple.bind
  · exact xnorMagnitudeBits_complete hbits
  · intro magnitudeBits
    apply complete_of_pure_pre_comb
    intro hmagnitude
    have hmagBits (i : Fin 12) :
        magnitudeBits[i].eval ρ.int = 0 ∨
          magnitudeBits[i].eval ρ.int = 1 :=
      XnorBitSpec.bool (hmagnitude i) (hbits 12)
        (hbits ⟨i.val, by omega⟩)
    have hmagBounds (i : Fin 12) :
        0 ≤ magnitudeBits[i].eval ρ.int ∧
          magnitudeBits[i].eval ρ.int ≤ 1 := by
      rcases hmagBits i with h | h <;> omega
    have hbitBounds (i : Fin 13) :
        0 ≤ bits[i].eval ρ.int ∧ bits[i].eval ρ.int ≤ 1 := by
      rcases hbits i with h | h <;> omega
    have hinnerLow : 0 ≤
        (∑ i : Fin 7, (2 ^ i.val : Int) • magnitudeBits[i]).eval ρ.int := by
      simp only [LC.eval_sum, LC.eval_smul]
      have h0 := hmagBounds 0; have h1 := hmagBounds 1
      have h2 := hmagBounds 2; have h3 := hmagBounds 3
      have h4 := hmagBounds 4; have h5 := hmagBounds 5
      have h6 := hmagBounds 6
      norm_num [Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6 ⊢
      omega
    have hinnerHigh :
        (∑ i : Fin 7, (2 ^ i.val : Int) • magnitudeBits[i]).eval ρ.int < 128 := by
      simp only [LC.eval_sum, LC.eval_smul]
      have h0 := hmagBounds 0; have h1 := hmagBounds 1
      have h2 := hmagBounds 2; have h3 := hmagBounds 3
      have h4 := hmagBounds 4; have h5 := hmagBounds 5
      have h6 := hmagBounds 6
      norm_num [Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6 ⊢
      omega
    have houterLow : 0 ≤
        ((∑ i : Fin 5, (2 ^ i.val : Int) •
          magnitudeBits[i.val + 7]'(by omega)) +
          (32 : Int) • bits[12]).eval ρ.int := by
      simp only [LC.eval_add, LC.eval_sum, LC.eval_smul]
      have h7 := hmagBounds 7; have h8 := hmagBounds 8
      have h9 := hmagBounds 9; have h10 := hmagBounds 10
      have h11 := hmagBounds 11; have hs := hbitBounds 12
      norm_num [Fin.sum_univ_succ] at h7 h8 h9 h10 h11 hs ⊢
      omega
    have houterHigh :
        ((∑ i : Fin 5, (2 ^ i.val : Int) •
          magnitudeBits[i.val + 7]'(by omega)) +
          (32 : Int) • bits[12]).eval ρ.int < 64 := by
      simp only [LC.eval_add, LC.eval_sum, LC.eval_smul]
      have h7 := hmagBounds 7; have h8 := hmagBounds 8
      have h9 := hmagBounds 9; have h10 := hmagBounds 10
      have h11 := hmagBounds 11
      have hs := hbitBounds 12
      norm_num [Fin.sum_univ_succ] at h7 h8 h9 h10 h11 hs ⊢
      omega
    mvcgen
    case vc5 =>
      let raw := (combWindowValue bits).eval ρ.int
      let table := fixedMagnitudeTable offset 4096
      let xValue := Reference.xNat table[signedMagnitudeIndex 13 raw.toNat]!
      refine ⟨Vector.ofFn fun i : Fin 256 => xValue.testBit i.val, ?_, ?_⟩
      · rfl
      · mvcgen
        case vc1 =>
          let yValue := if 4096 ≤ raw.toNat then
              Reference.yNat table[signedMagnitudeIndex 13 raw.toNat]!
            else base.modulus -
              Reference.yNat table[signedMagnitudeIndex 13 raw.toNat]!
          refine ⟨Vector.ofFn fun i : Fin 256 => yValue.testBit i.val, ?_, ?_⟩
          · rfl
          · mvcgen
            case vc1.houter =>
              rename_i inner hinner outer houter X hX Y hY
              exact houter.1
            case vc2.heq =>
              rename_i inner hinner outer houter X hX Y hY
              have hxFit : xValue < 2 ^ 256 :=
                (Reference.xNat_lt_base _).trans (by
                  norm_num [base, baseModulus])
              let xBits : Vector Bool 256 :=
                Vector.ofFn fun i => xValue.testBit i.val
              have hxWord :
                  (Word.eval ρ.bool { bitsLE := xBits.map LC.ofConst }).toNat =
                    xValue := by
                rw [show xBits.map LC.ofConst =
                    Vector.ofFn fun i : Fin 256 =>
                      LC.ofConst (xValue.testBit i.val) by
                  ext i
                  simp [xBits]]
                exact Modular.Aux.constWord_eval_toNat xValue hxFit ρ
              have hxEval : X.intVal.eval ρ.int = xValue := by
                rw [U.Rel.intVal hX, hxWord]
              have hyLe : yValue ≤ base.modulus := by
                dsimp [yValue]
                split
                · exact Nat.le_of_lt (Reference.yNat_lt_base _)
                · exact Nat.sub_le _ _
              have hyFit : yValue < 2 ^ 256 :=
                lt_of_le_of_lt hyLe (by
                  norm_num [base, baseModulus])
              let yBits : Vector Bool 256 :=
                Vector.ofFn fun i => yValue.testBit i.val
              have hyWord :
                  (Word.eval ρ.bool { bitsLE := yBits.map LC.ofConst }).toNat =
                    yValue := by
                rw [show yBits.map LC.ofConst =
                    Vector.ofFn fun i : Fin 256 =>
                      LC.ofConst (yValue.testBit i.val) by
                  ext i
                  simp [yBits]]
                exact Modular.Aux.constWord_eval_toNat yValue hyFit ρ
              have hyEval : Y.intVal.eval ρ.int = yValue := by
                rw [U.Rel.intVal hY, hyWord]
              simpa [raw, table, xValue, yValue] using
                (fixedFactoredCoordinates13_hint (ρ := ρ) (offset := offset)
                  hbits hmagnitude hinner houter hxEval hyEval)
            case vc3.success =>
              rename_i inner hinner outer houter X hX Y hY unit hcoords
              rcases hinner.2 with
                ⟨innerIndex, hinnerOne, hinnerValue, hinnerUnique⟩
              rcases houter.2 with
                ⟨outerIndex, houterOne, houterValue, _⟩
              have hinnerZero (j : Fin 128) (hne : j ≠ innerIndex) :
                  inner.intBits[j].eval ρ.int = 0 := by
                have hj := hinner.1 j
                cases hb : inner.bits.bitsLE[j].eval ρ.bool <;>
                  rw [hb] at hj <;> simp at hj
                · exact hj
                · exact (hne (hinnerUnique j hj)).elim
              have hselected := hcoords outerIndex houterOne
              unfold fixedInnerX fixedInnerY at hselected
              simp only [LC.eval_sum, LC.eval_nsmul, nsmul_eq_mul] at hselected
              rw [Aux.sum_mul_oneHot _ _ innerIndex hinnerOne hinnerZero,
                Aux.sum_mul_oneHot _ _ innerIndex hinnerOne hinnerZero] at hselected
              let out : AffineSlope.Point :=
                ⟨⟨X.intVal, 2⟩, ⟨Y.intVal, 2⟩, 0⟩
              have hspec : FixedLookupSelectedSpec ρ offset 13 (by omega)
                  bits out := by
                refine ⟨magnitudeBits, hmagnitude, innerIndex, outerIndex,
                  hinnerValue, houterValue, ?_, hselected.1, hselected.2⟩
                simp [out]
              have hcoord := fixedLookupSelected13_coordinates hbits hspec
              have hxLt : X.intVal.eval ρ.int < base.modulus := by
                rw [hcoord.2.1]
                exact_mod_cast Reference.xNat_lt_base _
              have hyLt : Y.intVal.eval ρ.int < base.modulus := by
                rw [hcoord.2.2]
                exact_mod_cast hselectedY
              change out.Valid ρ ∧ FixedLookupCoordinatesSpec ρ offset 13 bits out
              refine ⟨?_, hcoord⟩
              unfold AffineSlope.Point.Valid Modular.Lazy.Rep.Valid
              simp only [out]
              refine ⟨trivial, ⟨U.intVal_nonneg X hX.1, ?_⟩, hxLt,
                trivial, ⟨U.intVal_nonneg Y hY.1, ?_⟩, hyLt, by simp⟩
              · have hp : (0 : Int) < base.modulus := by
                  exact_mod_cast base.positive
                omega
              · have hp : (0 : Int) < base.modulus := by
                  exact_mod_cast base.positive
                omega



@[spec] theorem lookupFixed12_sound {k : Fn} {window : Nat}
    {hwindow : window < 8} (hk : k.val.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (lookupFixed12 k window hwindow)
    ⦃⇓ out => ⌜FixedLookupCoordinatesSpec ρ (12 * window) 12
      (combWindowBits k (12 * window) 12 (by omega)) out⌝⦄ := by
  unfold lookupFixed12
  apply lookupFixedFactored12_sound
  intro i
  simpa [combWindowBits] using
    combBit_bool hk (12 * window + i.val) (by omega)

@[spec] theorem lookupFixed12_complete {k : Fn} {window : Nat}
    {hwindow : window < 8} (hk : k.val.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (lookupFixed12 k window hwindow)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      FixedLookupCoordinatesSpec ρ (12 * window) 12
        (combWindowBits k (12 * window) 12 (by omega)) out⌝⦄ := by
  unfold lookupFixed12
  let bits := combWindowBits k (12 * window) 12 (by omega)
  have hbits : ∀ i : Fin 12,
      bits[i].eval ρ.int = 0 ∨ bits[i].eval ρ.int = 1 := by
    intro i
    simpa [bits, combWindowBits] using
      combBit_bool hk (12 * window + i.val) (by omega)
  apply lookupFixedFactored12_complete hbits
  apply selectedFixedY_lt_base (hwidth := by omega) (hfit := by omega)
  exact (Int.toNat_lt (combWindowValue_bounds hbits).1).2
    (combWindowValue_bounds hbits).2

@[spec] theorem lookupFixed13_sound {k : Fn} {window : Nat}
    {hwindow : window < 12} (hk : k.val.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (lookupFixed13 k window hwindow)
    ⦃⇓ out => ⌜FixedLookupCoordinatesSpec ρ (96 + 13 * window) 13
      (combWindowBits k (96 + 13 * window) 13 (by omega)) out⌝⦄ := by
  unfold lookupFixed13
  apply lookupFixedFactored13_sound
  intro i
  simpa [combWindowBits] using
    combBit_bool hk (96 + 13 * window + i.val) (by omega)

@[spec] theorem lookupFixed13_complete {k : Fn} {window : Nat}
    {hwindow : window < 12} (hk : k.val.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (lookupFixed13 k window hwindow)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      FixedLookupCoordinatesSpec ρ (96 + 13 * window) 13
        (combWindowBits k (96 + 13 * window) 13 (by omega)) out⌝⦄ := by
  unfold lookupFixed13
  let bits := combWindowBits k (96 + 13 * window) 13 (by omega)
  have hbits : ∀ i : Fin 13,
      bits[i].eval ρ.int = 0 ∨ bits[i].eval ρ.int = 1 := by
    intro i
    simpa [bits, combWindowBits] using
      combBit_bool hk (96 + 13 * window + i.val) (by omega)
  apply lookupFixedFactored13_complete hbits
  apply selectedFixedY_lt_base (hwidth := by omega) (hfit := by omega)
  exact (Int.toNat_lt (combWindowValue_bounds hbits).1).2
    (combWindowValue_bounds hbits).2

@[spec] theorem lookupFixed12_sound_normalized {k : Fn} {window : Nat}
    {hwindow : window < 8} (hk : k.val.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (lookupFixed12 k window hwindow)
    ⦃⇓ out => ⌜Reference.NormalizedRep ρ out
      (fixedSignedPoint (12 * window) 12
        ((combWindowValue (combWindowBits k (12 * window) 12
          (by omega))).eval ρ.int).toNat)⌝⦄ := by
  apply Triple.iff_conseq.mp (lookupFixed12_sound hk) (by simp)
  simp only [PostCond.entails, SPred.entails_nil]
  refine ⟨fun _ h => h.normalizedRep (by omega) (by omega) ?_,
    ExceptConds.entails.refl _⟩
  apply combWindowValue_bounds
  intro i
  simpa [combWindowBits] using
    combBit_bool hk (12 * window + i.val) (by omega)

@[spec] theorem lookupFixed12_complete_normalized {k : Fn} {window : Nat}
    {hwindow : window < 8} (hk : k.val.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (lookupFixed12 k window hwindow)
    ⦃⇓ out => ⌜out.Valid ρ ∧ Reference.NormalizedRep ρ out
      (fixedSignedPoint (12 * window) 12
        ((combWindowValue (combWindowBits k (12 * window) 12
          (by omega))).eval ρ.int).toNat)⌝⦄ := by
  apply Triple.iff_conseq.mp (lookupFixed12_complete hk) (by simp)
  simp only [PostCond.entails, SPred.entails_nil]
  refine ⟨fun _ h => ⟨h.1, h.2.normalizedRep (by omega) (by omega) ?_⟩,
    ExceptConds.entails.refl _⟩
  apply combWindowValue_bounds
  intro i
  simpa [combWindowBits] using
    combBit_bool hk (12 * window + i.val) (by omega)

@[spec] theorem lookupFixed13_sound_normalized {k : Fn} {window : Nat}
    {hwindow : window < 12} (hk : k.val.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (lookupFixed13 k window hwindow)
    ⦃⇓ out => ⌜Reference.NormalizedRep ρ out
      (fixedSignedPoint (96 + 13 * window) 13
        ((combWindowValue (combWindowBits k (96 + 13 * window) 13
          (by omega))).eval ρ.int).toNat)⌝⦄ := by
  apply Triple.iff_conseq.mp (lookupFixed13_sound hk) (by simp)
  simp only [PostCond.entails, SPred.entails_nil]
  refine ⟨fun _ h => h.normalizedRep (by omega) (by omega) ?_,
    ExceptConds.entails.refl _⟩
  apply combWindowValue_bounds
  intro i
  simpa [combWindowBits] using
    combBit_bool hk (96 + 13 * window + i.val) (by omega)

@[spec] theorem lookupFixed13_complete_normalized {k : Fn} {window : Nat}
    {hwindow : window < 12} (hk : k.val.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (lookupFixed13 k window hwindow)
    ⦃⇓ out => ⌜out.Valid ρ ∧ Reference.NormalizedRep ρ out
      (fixedSignedPoint (96 + 13 * window) 13
        ((combWindowValue (combWindowBits k (96 + 13 * window) 13
          (by omega))).eval ρ.int).toNat)⌝⦄ := by
  apply Triple.iff_conseq.mp (lookupFixed13_complete hk) (by simp)
  simp only [PostCond.entails, SPred.entails_nil]
  refine ⟨fun _ h => ⟨h.1, h.2.normalizedRep (by omega) (by omega) ?_⟩,
    ExceptConds.entails.refl _⟩
  apply combWindowValue_bounds
  intro i
  simpa [combWindowBits] using
    combBit_bool hk (96 + 13 * window + i.val) (by omega)

def TopLookupCoordinatesSpec (rho : WF.Valuation) (k : Fn)
    (out : AffineSlope.Point) : Prop :=
  let raw := (combWindowValue
    (combWindowBits k 252 4 (by omega))).eval rho.int
  let parity := k.val.intBits[0].eval rho.int
  out.infinity.eval rho.int = 0 ∧
    out.X.intVal.eval rho.int =
      (topCombX (raw.toNat + 16 * parity.toNat) : Int) ∧
    out.Y.intVal.eval rho.int =
      (topCombY (raw.toNat + 16 * parity.toNat) : Int)

theorem TopLookupCoordinatesSpec.normalizedRep {k : Fn}
    {out : AffineSlope.Point} (hk : k.val.Valid ρ)
    (h : TopLookupCoordinatesSpec ρ k out) :
    Reference.NormalizedRep ρ out
      (topCombPoint
        ((combWindowValue (combWindowBits k 252 4 (by omega))).eval
          ρ.int).toNat
        ((k.val.intBits[0].eval ρ.int).toNat)) := by
  let raw := (combWindowValue
    (combWindowBits k 252 4 (by omega))).eval ρ.int
  let parity := k.val.intBits[0].eval ρ.int
  have hraw := topCombRaw_bounds hk
  have hparity : parity = 0 ∨ parity = 1 := by
    have hbit := hk (0 : Fin 256)
    cases hb : k.val.bits.bitsLE[(0 : Fin 256)].eval ρ.bool <;>
      rw [hb] at hbit <;> simp at hbit
    · exact Or.inl hbit
    · exact Or.inr hbit
  have hrawNatLow : 8 ≤ raw.toNat := by
    have hrawNat : (raw.toNat : Int) = raw := Int.toNat_of_nonneg (by
      simpa [raw] using le_trans (by omega : (0 : Int) ≤ 8) hraw.1)
    omega
  have hrawNatHigh : raw.toNat < 16 := by
    have hrawNat : (raw.toNat : Int) = raw := Int.toNat_of_nonneg (by
      simpa [raw] using le_trans (by omega : (0 : Int) ≤ 8) hraw.1)
    omega
  have hparityNat : parity.toNat ≤ 1 := by rcases hparity with h | h <;> simp [h]
  have hp := topCombPoint_nonzero hrawNatLow hrawNatHigh hparityNat
  apply Reference.normalizedRep_of_natCoordinates hp h.1
  · rw [h.2.1]
    unfold topCombX
    have hmod : (raw.toNat + 16 * parity.toNat) % 16 = raw.toNat := by
      omega
    have hdiv : (raw.toNat + 16 * parity.toNat) / 16 = parity.toNat := by
      omega
    rw [hmod, hdiv]
  · rw [h.2.2]
    unfold topCombY
    have hmod : (raw.toNat + 16 * parity.toNat) % 16 = raw.toNat := by
      omega
    have hdiv : (raw.toNat + 16 * parity.toNat) / 16 = parity.toNat := by
      omega
    rw [hmod, hdiv]

theorem topLookupCoordinates_of_indicators {k : Fn} (hk : k.val.Valid ρ)
    {oneHot : U 32}
    (hone : IndicatorsSpec ρ
      (combWindowValue (combWindowBits k 252 4 (by omega)) +
        16 • k.val.intBits[0]) oneHot) :
    TopLookupCoordinatesSpec ρ k
      ⟨⟨∑ i : Fin 32, topCombX i.val • oneHot.intBits[i], 2⟩,
        ⟨∑ i : Fin 32, topCombY i.val • oneHot.intBits[i], 2⟩, 0⟩ := by
  unfold TopLookupCoordinatesSpec
  rcases hone.2 with ⟨i, hi, hindex, hunique⟩
  have hbit (j : Fin 32) :
      oneHot.intBits[j].eval ρ.int = 0 ∨
        oneHot.intBits[j].eval ρ.int = 1 := by
    have hj := hone.1 j
    cases hb : oneHot.bits.bitsLE[j].eval ρ.bool <;>
      rw [hb] at hj <;> simp at hj
    · exact Or.inl hj
    · exact Or.inr hj
  have hzero (j : Fin 32) (hji : j ≠ i) :
      oneHot.intBits[j].eval ρ.int = 0 :=
    (hbit j).resolve_right fun hj => hji (hunique j hj)
  have hraw := topCombRaw_bounds hk
  have hparity : k.val.intBits[0].eval ρ.int = 0 ∨
      k.val.intBits[0].eval ρ.int = 1 := by
    have h0 := hk (0 : Fin 256)
    cases hb : k.val.bits.bitsLE[(0 : Fin 256)].eval ρ.bool <;>
      rw [hb] at h0 <;> simp at h0
    · exact Or.inl h0
    · exact Or.inr h0
  have hindexNat : i.val =
      ((combWindowValue (combWindowBits k 252 4 (by omega))).eval ρ.int).toNat +
        16 * (k.val.intBits[0].eval ρ.int).toNat := by
    simp only [LC.eval_add, LC.eval_nsmul, nsmul_eq_mul] at hindex
    have hrawNonneg : 0 ≤
        (combWindowValue (combWindowBits k 252 4 (by omega))).eval ρ.int := by
      omega
    rcases hparity with hp | hp <;>
      simp [hp, Int.toNat_of_nonneg hrawNonneg] <;> omega
  constructor
  · simp
  constructor
  · simp only [LC.eval_sum, LC.eval_nsmul, nsmul_eq_mul]
    rw [Aux.sum_mul_oneHot _ _ i hi hzero, hindexNat]
  · simp only [LC.eval_sum, LC.eval_nsmul, nsmul_eq_mul]
    rw [Aux.sum_mul_oneHot _ _ i hi hzero, hindexNat]

private theorem sound_of_pure_pre_comb {alpha : Type} {P : Prop}
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

@[spec] theorem lookupFixedTop_sound {k : Fn} (hk : k.val.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (lookupFixedTop k)
    ⦃⇓ out => ⌜TopLookupCoordinatesSpec ρ k out⌝⦄ := by
  unfold lookupFixedTop
  rw [Sound.interp_bind]
  apply Triple.bind (Q := fun oneHot => ⌜IndicatorsSpec ρ
    (combWindowValue (combWindowBits k 252 4 (by omega)) +
      16 • k.val.intBits[0]) oneHot⌝)
  · exact indicators_sound
  · intro oneHot
    apply sound_of_pure_pre_comb
    intro hone
    rw [Sound.interp_pure]
    apply Triple.pure
    simp only [SPred.entails_nil]
    intro _
    exact topLookupCoordinates_of_indicators hk hone

@[spec] theorem lookupFixedTop_complete {k : Fn} (hk : k.val.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (lookupFixedTop k)
    ⦃⇓ out => ⌜out.Valid ρ ∧ TopLookupCoordinatesSpec ρ k out⌝⦄ := by
  have hraw := topCombRaw_bounds hk
  have hparity : k.val.intBits[0].eval ρ.int = 0 ∨
      k.val.intBits[0].eval ρ.int = 1 := by
    have h0 := hk (0 : Fin 256)
    cases hb : k.val.bits.bitsLE[(0 : Fin 256)].eval ρ.bool <;>
      rw [hb] at h0 <;> simp at h0
    · exact Or.inl h0
    · exact Or.inr h0
  have hindexNonneg : 0 ≤
      (combWindowValue (combWindowBits k 252 4 (by omega)) +
        16 • k.val.intBits[0]).eval ρ.int := by
    simp only [LC.eval_add, LC.eval_nsmul, nsmul_eq_mul]
    rcases hparity with h | h <;> omega
  have hindexLt :
      (combWindowValue (combWindowBits k 252 4 (by omega)) +
        16 • k.val.intBits[0]).eval ρ.int < 32 := by
    simp only [LC.eval_add, LC.eval_nsmul, nsmul_eq_mul]
    rcases hparity with h | h <;> omega
  unfold lookupFixedTop
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun oneHot => ⌜IndicatorsSpec ρ
    (combWindowValue (combWindowBits k 252 4 (by omega)) +
      16 • k.val.intBits[0]) oneHot⌝)
  · exact indicators_complete hindexNonneg hindexLt
  · intro oneHot
    apply complete_of_pure_pre_comb
    intro hone
    mvcgen
    let out : AffineSlope.Point :=
      ⟨⟨∑ i : Fin 32, topCombX i.val • oneHot.intBits[i], 2⟩,
        ⟨∑ i : Fin 32, topCombY i.val • oneHot.intBits[i], 2⟩, 0⟩
    have hcoord : TopLookupCoordinatesSpec ρ k out :=
      topLookupCoordinates_of_indicators hk hone
    refine ⟨?_, hcoord⟩
    have hxNonneg : 0 ≤ out.X.intVal.eval ρ.int := by
      rw [hcoord.2.1]
      exact_mod_cast Nat.zero_le _
    have hxLt : out.X.intVal.eval ρ.int < base.modulus := by
      rw [hcoord.2.1]
      unfold topCombX
      exact_mod_cast Reference.xNat_lt_base _
    have hyNonneg : 0 ≤ out.Y.intVal.eval ρ.int := by
      rw [hcoord.2.2]
      exact_mod_cast Nat.zero_le _
    have hyLt : out.Y.intVal.eval ρ.int < base.modulus := by
      rw [hcoord.2.2]
      unfold topCombY
      exact_mod_cast Reference.yNat_lt_base _
    change out.Valid ρ
    unfold AffineSlope.Point.Valid Modular.Lazy.Rep.Valid
    simp only [out]
    refine ⟨trivial, ⟨hxNonneg, ?_⟩, hxLt,
      trivial, ⟨hyNonneg, ?_⟩, hyLt, by simp⟩
    · have hp : (0 : Int) < base.modulus := by
        exact_mod_cast base.positive
      have hxLt' :
          (∑ i : Fin 32, topCombX i.val • oneHot.intBits[i]).eval ρ.int <
            base.modulus := by simpa [out] using hxLt
      omega
    · have hp : (0 : Int) < base.modulus := by
        exact_mod_cast base.positive
      have hyLt' :
          (∑ i : Fin 32, topCombY i.val • oneHot.intBits[i]).eval ρ.int <
            base.modulus := by simpa [out] using hyLt
      omega

@[spec] theorem lookupFixedTop_sound_normalized {k : Fn}
    (hk : k.val.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (lookupFixedTop k)
    ⦃⇓ out => ⌜Reference.NormalizedRep ρ out
      (topCombPoint
        ((combWindowValue (combWindowBits k 252 4 (by omega))).eval
          ρ.int).toNat
        ((k.val.intBits[0].eval ρ.int).toNat))⌝⦄ := by
  apply Triple.iff_conseq.mp (lookupFixedTop_sound hk) (by simp)
  simp only [PostCond.entails, SPred.entails_nil]
  exact ⟨fun _ h => h.normalizedRep hk, ExceptConds.entails.refl _⟩

@[spec] theorem lookupFixedTop_complete_normalized {k : Fn}
    (hk : k.val.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (lookupFixedTop k)
    ⦃⇓ out => ⌜out.Valid ρ ∧ Reference.NormalizedRep ρ out
      (topCombPoint
        ((combWindowValue (combWindowBits k 252 4 (by omega))).eval
          ρ.int).toNat
        ((k.val.intBits[0].eval ρ.int).toNat))⌝⦄ := by
  apply Triple.iff_conseq.mp (lookupFixedTop_complete hk) (by simp)
  simp only [PostCond.entails, SPred.entails_nil]
  exact ⟨fun _ h => ⟨h.1, h.2.normalizedRep hk⟩,
    ExceptConds.entails.refl _⟩

end Freigen.F2Z.Examples.EcdsaP256
