import Freigen.F2Z.Defs
import Freigen.F2Z.Correctness.Basic
import Mathlib.Data.List.DropRight
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Indexes
import Mathlib.Data.Nat.Digits.Lemmas
import Batteries.Data.Vector.Lemmas
import Batteries.Data.BitVec.Lemmas

namespace Freigen.F2Z

private theorem natCast_ofBits_eq_sum (f : Fin n → Bool) :
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

structure Word (n : Nat) where
  bitsLE : Vector (LC Bool) n

def Word.evalZ (ρ : WF.Valuation) (w : Word n) : ℤ :=
  Nat.ofBits fun i => (w.bitsLE[i].eval ρ.bool)

def Word.take (m : Nat) (w : Word n) : Word (min m n) :=
  { bitsLE := w.bitsLE.take m }

def Word.takeLE (m : Nat) (h : m ≤ n) (w : Word n) : Word m :=
  (Nat.min_eq_left h) ▸ { bitsLE := w.bitsLE.take m }

def Word.rotateRight (k : Nat) (w : Word n) : Word n :=
  { bitsLE := show (n - k + min k n = n) by omega ▸ (w.bitsLE.drop k ++ w.bitsLE.take k) }

instance : HShiftRight (Word n) Nat (Word n) where
  hShiftRight w a := show (n - a + min a n = n) by omega ▸
    { bitsLE := w.bitsLE.drop a ++ Vector.replicate (min a n) (0 : LC Bool)}

instance : HXor (Word n) (Word n) (Word n) where
  hXor w₁ w₂ := { bitsLE := Vector.zipWith (· + ·) w₁.bitsLE w₂.bitsLE }

def Word.eval (valuation : Nat → Bool) (w : Word n) : BitVec n :=
  BitVec.ofFnLE fun i => w.bitsLE[i].eval valuation

private theorem Vector.getElem_eq_mpr {m n : Nat} (h : m = n)
    (v : Vector α m) (i : Nat) (hi : i < n) : (h ▸ v)[i] = v[i] := by
  subst n
  rfl

private theorem Word.getElem_eq_mpr {m n : Nat} (h : m = n)
    (v : Vector (LC Bool) m) (i : Nat) (hi : i < n) :
    (h ▸ ({ bitsLE := v } : Word m)).bitsLE[i] = v[i] := by
  subst n
  rfl

theorem Word.rotateRight_getElem (u : Word n) (k i : Nat) (hi : i < n) :
    (u.rotateRight k).bitsLE[i] =
      if h : i < n - k then u.bitsLE[k + i]
      else u.bitsLE[i - (n - k)] := by
  simp only [Word.rotateRight, Vector.getElem_eq_mpr,
    Vector.getElem_append, Vector.getElem_drop, Vector.getElem_take]

theorem Word.shiftRight_getElem (u : Word n) (k i : Nat) (hi : i < n) :
    (u >>> k).bitsLE[i] =
      if h : i < n - k then u.bitsLE[k + i] else 0 := by
  simp only [HShiftRight.hShiftRight, Word.getElem_eq_mpr,
    Vector.getElem_append, Vector.getElem_drop, Vector.getElem_replicate]

@[simp]
theorem Word.eval_xor (valuation : Nat → Bool) (u v : Word n) :
    (u ^^^ v).eval valuation = u.eval valuation ^^^ v.eval valuation := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [Word.eval, BitVec.getElem_ofFnLE, BitVec.getElem_xor]
  change LC.eval valuation
      (Vector.zipWith (· + ·) u.bitsLE v.bitsLE)[i] = _
  rw [Vector.getElem_zipWith hi, LC.eval_add]
  generalize LC.eval valuation u.bitsLE[i] = ub
  generalize LC.eval valuation v.bitsLE[i] = vb
  cases ub <;> cases vb <;> rfl

theorem Word.eval_xor3 (valuation : Nat → Bool) (u v w : Word n) :
    (u ^^^ v ^^^ w).eval valuation =
      u.eval valuation ^^^ v.eval valuation ^^^ w.eval valuation := by
  rw [Word.eval_xor, Word.eval_xor]

@[simp]
theorem Word.eval_rotateRight (valuation : Nat → Bool)
    (u : Word n) (k : Nat) (hk : k < n) :
    (u.rotateRight k).eval valuation = (u.eval valuation).rotateRight k := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_rotateRight hi]
  simp only [Nat.mod_eq_of_lt hk, Word.eval, BitVec.getElem_ofFnLE,
    Fin.getElem_fin]
  rw [Word.rotateRight_getElem]
  split <;> rfl

@[simp]
theorem Word.eval_shiftRight (valuation : Nat → Bool)
    (u : Word n) (k : Nat) :
    (u >>> k).eval valuation = (u.eval valuation >>> k) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_ushiftRight _ _ _ hi]
  simp only [Word.eval, BitVec.getElem_ofFnLE]
  have hget : (u >>> k).bitsLE[i] =
      if h : i < n - k then u.bitsLE[k + i] else 0 :=
    Word.shiftRight_getElem u k i hi
  calc
    LC.eval valuation (getElem (u >>> k).bitsLE i hi) =
        LC.eval valuation (if h : i < n - k then u.bitsLE[k + i] else 0) :=
      congrArg (LC.eval valuation) hget
    _ = (BitVec.ofFnLE fun i => LC.eval valuation u.bitsLE[i]).getLsbD (k + i) := by
      split
      · simp only [BitVec.getLsbD, BitVec.toNat_ofFnLE]
        rw [Nat.testBit_ofBits_lt _ _ (by omega)]
        simp only [Fin.getElem_fin]
      · rw [LC.eval_zero]
        simp only [BitVec.getLsbD, BitVec.toNat_ofFnLE]
        rw [Nat.testBit_ofBits_ge _ _ (by omega)]
        rfl

instance : GetElem (Word n) (Fin n) (LC Bool) (fun _ _ => True) where
  getElem w i _ := w.bitsLE[i]

structure U (n : Nat) where
  bits : Word n
  intBits : Vector (LC ℤ) n

instance : Coe (BitVec n) (U n) where
  coe w := {
    bits := { bitsLE := Vector.ofFn fun i => w[i] }
    intBits := Vector.ofFn fun i => w[i].toInt
  }

instance : Inhabited (LC Bool) where
  default := 0

instance : Inhabited (LC ℤ) where
  default := 0

instance : Inhabited (U n) where
  default := {
    bits := {
      bitsLE := Vector.replicate n 0
    }
    intBits := Vector.replicate n 0
  }

def U.Valid (u : U n) (ρ : WF.Valuation) : Prop :=
  ∀ i : Fin n, u.intBits[i].eval ρ.int = (u.bits.bitsLE[i].eval ρ.bool).toInt

def U.fromWord (w : Word n) : Circuit (U n) := do
  let mut res := Vector.replicate n 0
  for h:i in [0:n] do
    let b ← f2z w.bitsLE[i]
    res := res.set! i b
  pure { bits := w, intBits := res }

def U.intVal (u : U n) : LC ℤ :=
  ∑ i : Fin n, 2 ^ i.val • u.intBits[i]

def U.eval : U n → WF.Valuation → BitVec n := fun u ρ =>
  BitVec.ofNat n $ (u.intVal.eval ρ.int).toNat

def U.takeLE (m : Nat) (h : m ≤ n) (u : U n) : U m :=
  { bits := { bitsLE := Vector.ofFn fun i => u.bits.bitsLE[i.castLE h] }
    intBits := Vector.ofFn fun i => u.intBits[i.castLE h] }

theorem U.eval_intVal_eq_evalZ (u : U n) (h : u.Valid ρ) :
    u.intVal.eval ρ.int = u.bits.evalZ ρ := by
  unfold U.intVal Word.evalZ
  rw [natCast_ofBits_eq_sum]
  simp only [LC.eval_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [LC.eval_nsmul, h i]
  simp

theorem U.eval_eq_ofFnLE (u : U n) (h : u.Valid ρ) :
    u.eval ρ = BitVec.ofFnLE (fun i => u.bits.bitsLE[i].eval ρ.bool) := by
  apply BitVec.toNat_inj.mp
  simp [U.eval, U.eval_intVal_eq_evalZ u h, Word.evalZ,
    Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow _)]

theorem U.intVal_eval_eq_eval_toNat (u : U n) (h : u.Valid ρ) :
    u.intVal.eval ρ.int = (u.eval ρ).toNat := by
  rw [U.eval_eq_ofFnLE u h, U.eval_intVal_eq_evalZ u h]
  simp [Word.evalZ]

theorem U.eval_eq_word_eval (u : U n) (w : Word n)
    (hvalid : u.Valid ρ) (hbits : u.bits = w) :
    u.eval ρ = w.eval ρ.bool := by
  rw [U.eval_eq_ofFnLE u hvalid, hbits]
  rfl

theorem U.takeLE_valid (u : U n) (hvalid : u.Valid ρ) (h : m ≤ n) :
    (u.takeLE m h).Valid ρ := by
  intro i
  simpa [U.takeLE, Fin.getElem_fin] using hvalid (i.castLE h)

theorem U.takeLE_eval (u : U n) (hvalid : u.Valid ρ) (h : m ≤ n) :
    (u.takeLE m h).eval ρ = BitVec.ofNat m (u.intVal.eval ρ.int).toNat := by
  rw [U.eval_eq_ofFnLE _ (U.takeLE_valid u hvalid h)]
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hin : i < n := hi.trans_le h
  have hu := congrArg (fun x : BitVec n => x[i]'hin)
    (U.eval_eq_ofFnLE u hvalid)
  simpa [U.eval, U.takeLE, Fin.getElem_fin, hi, hin,
    BitVec.getElem_ofFnLE, BitVec.getElem_eq_testBit_toNat] using hu.symm

theorem U.takeLE_eq_truncate (u : U n) (h : m ≤ n) :
    u.takeLE m h =
      { bits := (Nat.min_eq_left h) ▸ u.bits.take m
        intBits := (Nat.min_eq_left h) ▸ u.intBits.take m } := by
  cases u with
  | mk bits intBits =>
    apply congrArg₂ U.mk
    · apply congrArg Word.mk
      apply Vector.ext
      intro i hi
      simp only [U.takeLE, Word.take, Vector.getElem_ofFn,
        Word.getElem_eq_mpr, Vector.getElem_take, Fin.getElem_fin]
      rfl
    · apply Vector.ext
      intro i hi
      simp only [U.takeLE, Vector.getElem_ofFn, Vector.getElem_eq_mpr,
        Vector.getElem_take, Fin.getElem_fin]
      rfl

def U.fromInt (n : Nat) (x : LC ℤ) : Circuit (U n) := do
  let bits ← hint h![x] fun h![(x: Int)] => match x with
    | .ofNat n => pure $ Vector.ofFn fun i => n.testBit i
    | _ => fail s!"negative integer {x} in U.fromInt"
  let r ← U.fromWord { bitsLE := bits }
  assertR1C 0 0 (x - r.intVal)
  pure r

def U.sum (us : Array (U n)) : Circuit (U n) := do
  let newZ := us.map (·.intVal) |>.sum
  let newBits ← U.fromInt (n + Nat.clog 2 us.size) newZ
  have : min n (n + Nat.clog 2 us.size) = n := by grind
  pure { bits := this ▸ newBits.bits.take n, intBits := this ▸ newBits.intBits.take n }

open Std.Do
open scoped Std.Do

private theorem Vector.set!_eq_setIfInBounds (xs : Vector α n) (i : Nat) (x : α) :
    xs.set! i x = xs.setIfInBounds i x := by
  rfl

@[simp]
theorem U.valid_default {n : Nat} : (default : U n).Valid ρ := by
  intro i
  change LC.eval ρ.int (Vector.replicate n (0 : LC ℤ))[i.val] =
    (LC.eval ρ.bool (Vector.replicate n (0 : LC Bool))[i.val]).toInt
  simp
  rfl

@[spec]
theorem U.fromWord_sound {ρ} {w : Word n}:
    ⦃ ⌜True⌝ ⦄
      (Sound.interp ρ $ U.fromWord w)
    ⦃ ⇓ u => ⌜u.bits = w⌝ ∧ ⌜u.Valid ρ⌝ ⦄ := by
  mvcgen [U.fromWord] invariants
  · ⇓⟨cur, res⟩ => ⌜∀ i : Fin n, i.val < cur.prefix.length →
      res[i].eval ρ.int = (w.bitsLE[i].eval ρ.bool).toInt⌝
  case vc1 pref cur _ _ _ h₁ _ h₂ =>
    rename_i suff out hloop hsplit
    have : cur = pref.length := by grind
    subst cur
    have hk : pref.length < n := by grind
    intro i hseen
    simp only [List.length_append, List.length_singleton] at hseen
    rw [Vector.set!_eq_setIfInBounds]
    simp only [Fin.getElem_fin] at h₁ ⊢
    by_cases hi : i.val < pref.length
    · rw [Vector.getElem_setIfInBounds_ne i.isLt (by omega)]
      exact h₁ i hi
    · have hieq : i.val = pref.length := by omega
      simpa [Vector.getElem_setIfInBounds, hieq] using h₂.symm
  case vc2 => simp
  case vc3 h =>
    constructor
    · trivial
    · intro i
      exact h i (by grind)

@[spec]
theorem U.fromWord_complete {ρ} {w : Word n} :
    ⦃ ⌜True⌝ ⦄ (Complete.interp ρ $ U.fromWord w)
    ⦃ ⇓ u => ⌜u.bits = w ∧ u.Valid ρ⌝ ⦄ := by
  mvcgen [U.fromWord] invariants
  · ⇓⟨cur, res⟩ => ⌜∀ i : Fin n, i.val < cur.prefix.length →
      res[i].eval ρ.int = (w.bitsLE[i].eval ρ.bool).toInt⌝
  case vc1 pref cur _ _ _ h₁ _ h₂ =>
    rename_i suff out hloop hsplit
    have : cur = pref.length := by grind
    subst cur
    have hk : pref.length < n := by grind
    intro i hseen
    simp only [List.length_append, List.length_singleton] at hseen
    rw [Vector.set!_eq_setIfInBounds]
    simp only [Fin.getElem_fin] at h₁ ⊢
    by_cases hi : i.val < pref.length
    · rw [Vector.getElem_setIfInBounds_ne i.isLt (by omega)]
      exact h₁ i hi
    · have hieq : i.val = pref.length := by omega
      simpa [Vector.getElem_setIfInBounds, hieq] using h₂
  case vc2 => simp
  case vc3 h =>
    constructor
    · trivial
    · intro i
      exact h i (by grind)

theorem U.fromWord_wf :
    WF.GadgetSpec
      (fun leftVal rightVal (left right : Word n) =>
        ∀ i : Fin n,
          WF.LCEq leftVal.bool rightVal.bool left.bitsLE[i] right.bitsLE[i])
      U.fromWord
      (fun leftVal rightVal left right =>
        (∀ i : Fin n, WF.LCEq leftVal.bool rightVal.bool
          left.bits.bitsLE[i] right.bits.bitsLE[i]) ∧
        WF.LCEq leftVal.int rightVal.int left.intVal right.intVal) := by
  wfgen [U.fromWord]

theorem U.fromInt_sound {ρ} {n : Nat} {x : LC ℤ} :
    ⦃ ⌜True⌝ ⦄ (Sound.interp ρ $ U.fromInt n x)
    ⦃ ⇓ u => ⌜u.Valid ρ⌝ ∧ ⌜u.intVal.eval ρ.int = x.eval ρ.int⌝ ⦄ := by
  mvcgen [fromInt]
  intro b
  mvcgen
  simp only [Valid, LC.eval_zero, mul_zero, LC.eval_sub] at *
  grind

theorem U.fromInt_complete {ρ} {n : Nat} {x : LC ℤ} (h0 : x.eval ρ.int ≥ 0)
    (h2 : x.eval ρ.int < 2 ^ n) :
    ⦃ ⌜True⌝ ⦄ (Complete.interp ρ $ U.fromInt n x)
    ⦃ ⇓ u => ⌜u.Valid ρ⌝ ∧ ⌜u.intVal.eval ρ.int = x.eval ρ.int⌝ ⦄ := by
  mvcgen [fromInt]
  have : ∃n, LC.eval ρ.int x = Int.ofNat n := by
    exists (x.eval ρ.int).toNat
    simp_all
  rcases this with ⟨x', hx'⟩
  simp only [WF.interpHint, WF.evalArgs, hx', Int.ofNat_eq_natCast, Free.interp_pure,
    Option.pure_def, Option.some.injEq, exists_eq_left', Vector.map_ofFn]
  mvcgen
  rename_i r h
  rcases h with ⟨h, h'⟩
  have hxlt : x' < 2 ^ n := by
    rw [hx'] at h2
    exact Int.ofNat_lt.mp (by simpa using h2)
  have hbits : r.bits.evalZ ρ = x' := by
    simp [Word.evalZ, h, Nat.ofBits_testBit, Nat.mod_eq_of_lt hxlt]
  have hintVal : r.intVal.eval ρ.int = (x' : Int) :=
    (U.eval_intVal_eq_evalZ r h').trans (by simpa using hbits)
  constructor
  · simp [LC.eval_zero, LC.eval_sub, hx', hintVal]
  · mvcgen

theorem U.fromInt_wf :
    WF.GadgetSpec
      (fun leftVal rightVal (left right : LC ℤ) =>
        WF.LCEq leftVal.int rightVal.int left right)
      (U.fromInt n)
      (fun leftVal rightVal left right =>
        WF.LCEq leftVal.int rightVal.int left.intVal right.intVal ∧
        (∀ i : Fin n, WF.LCEq leftVal.bool rightVal.bool
          left.bits.bitsLE[i] right.bits.bitsLE[i])) := by
  wfgen [U.fromInt]

def U.sumValue (u : Array (U n)) (ρ : WF.Valuation) : BitVec n :=
  BitVec.ofNat n
    ((u.map (fun value : U n => value.intVal)).sum.eval ρ.int).toNat

theorem U.intVal_nonneg (u : U n) (h : u.Valid ρ) :
    0 ≤ u.intVal.eval ρ.int := by
  rw [U.eval_intVal_eq_evalZ u h]
  exact Int.natCast_nonneg _

theorem U.intVal_lt_two_pow (u : U n) (h : u.Valid ρ) :
    u.intVal.eval ρ.int < (2 ^ n : Nat) := by
  rw [U.eval_intVal_eq_evalZ u h]
  unfold Word.evalZ
  exact_mod_cast Nat.ofBits_lt_two_pow _

private theorem List.sum_lt_length_mul {xs : List ℤ} {bound : ℤ}
    (hne : xs ≠ []) (h : ∀ x ∈ xs, x < bound) :
    xs.sum < (xs.length : ℤ) * bound := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
      have hx := h x (by simp)
      have htail : xs.sum ≤ (xs.length : ℤ) * bound :=
        List.sum_le_card_nsmul xs bound fun y hy =>
          (h y (by simp [hy])).le
      simp only [List.sum_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one]
      linarith

theorem U.sum_nonneg (us : Array (U n))
    (hvalid : ∀ u ∈ us, u.Valid ρ) :
    0 ≤ (us.map (fun value : U n => value.intVal)).sum.eval ρ.int := by
  rw [LC.eval_array_sum, ← Array.sum_toList]
  simp only [Array.map_map]
  apply List.sum_nonneg
  intro value hvalue
  simp only [Array.toList_map, List.mem_map] at hvalue
  obtain ⟨u, hu, rfl⟩ := hvalue
  exact U.intVal_nonneg u (hvalid u (by simpa using hu))

theorem U.sum_lt_capacity (us : Array (U n))
    (hvalid : ∀ u ∈ us, u.Valid ρ) :
    (us.map (fun value : U n => value.intVal)).sum.eval ρ.int <
      2 ^ (n + Nat.clog 2 us.size) := by
  rw [LC.eval_array_sum, ← Array.sum_toList]
  simp only [Array.map_map]
  by_cases hempty : us = #[]
  · subst us
    simp
  · have hne : (us.map fun u => u.intVal.eval ρ.int).toList ≠ [] := by
      simp [hempty]
    have hsum := List.sum_lt_length_mul hne (fun value hvalue => by
      simp only [Array.toList_map, List.mem_map] at hvalue
      obtain ⟨u, hu, rfl⟩ := hvalue
      exact U.intVal_lt_two_pow u (hvalid u (by simpa using hu)))
    have hsum' :
        (us.map fun u => u.intVal.eval ρ.int).toList.sum <
          (us.size : ℤ) * (2 ^ n : Nat) := by
      simpa using hsum
    have hsize : us.size ≤ 2 ^ Nat.clog 2 us.size :=
      Nat.le_pow_clog (by omega) _
    have hpow : (us.size : ℤ) * (2 ^ n : Nat) ≤
        (2 ^ (n + Nat.clog 2 us.size) : Nat) := by
      exact_mod_cast (Nat.mul_le_mul_right (2 ^ n) hsize |>.trans_eq (by
        rw [Nat.pow_add]
        ac_rfl))
    exact hsum'.trans_le hpow

private theorem U.sumValue_eq_sum_list (us : List (U n))
    (hvalid : ∀ u ∈ us, u.Valid ρ) :
    BitVec.ofNat n
        (us.map (fun u : U n => u.intVal.eval ρ.int)).sum.toNat =
      (us.map fun u : U n => u.eval ρ).sum := by
  induction us with
  | nil => simp
  | cons u us ih =>
      have hu := hvalid u (by simp)
      have hus : ∀ v ∈ us, v.Valid ρ := by
        intro v hv
        exact hvalid v (by simp [hv])
      have htail : 0 ≤
          (us.map fun u : U n => u.intVal.eval ρ.int).sum :=
        List.sum_nonneg fun value hvalue => by
          simp only [List.mem_map] at hvalue
          obtain ⟨v, hv, rfl⟩ := hvalue
          exact U.intVal_nonneg v (hus v hv)
      simp only [List.map_cons, List.sum_cons]
      rw [Int.toNat_add (U.intVal_nonneg u hu) htail,
        BitVec.ofNat_add, ih hus]
      rfl

theorem U.sumValue_eq_sum (us : Array (U n))
    (hvalid : ∀ u ∈ us, u.Valid ρ) :
    U.sumValue us ρ = (us.map fun u : U n => u.eval ρ).sum := by
  unfold U.sumValue
  rw [LC.eval_array_sum]
  rw [← Array.sum_toList, ← Array.sum_toList]
  simp only [Array.toList_map, List.map_map]
  change BitVec.ofNat n
      (us.toList.map (fun u : U n => u.intVal.eval ρ.int)).sum.toNat =
    (us.toList.map fun u : U n => u.eval ρ).sum
  exact U.sumValue_eq_sum_list us.toList (by
    intro u hu
    exact hvalid u (by simpa using hu))

@[spec]
theorem U.sum_sound {us : Array (U n)}
    (hvalid : ∀ u ∈ us, u.Valid ρ) :
    ⦃ ⌜True⌝ ⦄ Sound.interp ρ (U.sum us)
    ⦃ ⇓ out => ⌜out.Valid ρ ∧
      out.eval ρ = (us.map fun u : U n => u.eval ρ).sum⌝ ⦄ := by
  unfold U.sum
  rw [Sound.interp_bind]
  apply Triple.bind
    (Q := fun wide => ⌜wide.Valid ρ ∧
      wide.intVal.eval ρ.int =
        (us.map (fun value : U n => value.intVal)).sum.eval ρ.int⌝)
  case hx => exact U.fromInt_sound
  case hf =>
    intro wide
    mvcgen
    case vc1 hwide =>
      let hle : n ≤ n + Nat.clog 2 us.size := Nat.le_add_right n _
      rw [← U.takeLE_eq_truncate wide hle]
      exact ⟨U.takeLE_valid wide hwide.1 hle, by
        rw [U.takeLE_eval wide hwide.1 hle, hwide.2]
        exact U.sumValue_eq_sum us hvalid⟩

@[spec]
theorem U.sum_complete {us : Array (U n)}
    (hvalid : ∀ u ∈ us, u.Valid ρ) :
    ⦃ ⌜True⌝ ⦄ Complete.interp ρ (U.sum us)
    ⦃ ⇓ out => ⌜out.Valid ρ ∧
      out.eval ρ = (us.map fun u : U n => u.eval ρ).sum⌝ ⦄ := by
  unfold U.sum
  rw [Complete.interp_bind]
  apply Triple.bind
    (Q := fun wide => ⌜wide.Valid ρ ∧
      wide.intVal.eval ρ.int =
        (us.map (fun value : U n => value.intVal)).sum.eval ρ.int⌝)
  case hx =>
    exact U.fromInt_complete (U.sum_nonneg us hvalid)
      (U.sum_lt_capacity us hvalid)
  case hf =>
    intro wide
    mvcgen
    case vc1 hwide =>
      let hle : n ≤ n + Nat.clog 2 us.size := Nat.le_add_right n _
      rw [← U.takeLE_eq_truncate wide hle]
      exact ⟨U.takeLE_valid wide hwide.1 hle, by
        rw [U.takeLE_eval wide hwide.1 hle, hwide.2]
        exact U.sumValue_eq_sum us hvalid⟩

end Freigen.F2Z
