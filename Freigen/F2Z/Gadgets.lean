import Freigen.F2Z.Defs
import Freigen.F2Z.Correctness.Basic
import Mathlib.Data.List.DropRight
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Indexes
import Mathlib.Data.Nat.Digits.Lemmas
import Batteries.Data.Vector.Lemmas
import Batteries.Data.BitVec.Lemmas

namespace Freigen.F2Z

open Context

section Generic

variable [ctx : Context]

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
  bitsLE : Vector ctx.WBool n

def Word.evalZ (ρ : WF.Valuation) (w : Word n) : ℤ :=
  Nat.ofBits fun i => ρ.bool w.bitsLE[i]

def Word.take (m : Nat) (w : Word n) : Word (min m n) :=
  { bitsLE := w.bitsLE.take m }

def Word.takeLE (m : Nat) (h : m ≤ n) (w : Word n) : Word m :=
  (Nat.min_eq_left h) ▸ { bitsLE := w.bitsLE.take m }

def Word.rotateRight (k : Nat) (w : Word n) : Word n :=
  { bitsLE := show (n - k + min k n = n) by omega ▸ (w.bitsLE.drop k ++ w.bitsLE.take k) }

def Word.shiftRight (w : Word n) (a : Nat) : Word n :=
  show (n - a + min a n = n) by omega ▸
    { bitsLE := w.bitsLE.drop a ++ Vector.replicate (min a n) (0 : ctx.WBool) }

instance : HShiftRight (Word n) Nat (Word n) where
  hShiftRight := Word.shiftRight

def Word.xor (w₁ w₂ : Word n) : Word n :=
  { bitsLE := Vector.zipWith (· + ·) w₁.bitsLE w₂.bitsLE }

instance : HXor (Word n) (Word n) (Word n) where
  hXor := Word.xor

def Word.eval (valuation : Freigen.F2Z.Valuation Bool ctx.WBool)
    (w : Word n) : BitVec n :=
  BitVec.ofFnLE fun i => valuation w.bitsLE[i]

private theorem Vector.getElem_eq_mpr {m n : Nat} (h : m = n)
    (v : Vector α m) (i : Nat) (hi : i < n) : (h ▸ v)[i] = v[i] := by
  subst n
  rfl

private theorem Word.getElem_eq_mpr {m n : Nat} (h : m = n)
    (v : Vector ctx.WBool m) (i : Nat) (hi : i < n) :
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
    (Word.shiftRight u k).bitsLE[i] =
      if h : i < n - k then u.bitsLE[k + i] else 0 := by
  simp only [Word.shiftRight, Word.getElem_eq_mpr,
    Vector.getElem_append, Vector.getElem_drop, Vector.getElem_replicate]

@[simp]
theorem Word.eval_xor (valuation : Freigen.F2Z.Valuation Bool ctx.WBool)
    (u v : Word n) :
    (u ^^^ v).eval valuation = u.eval valuation ^^^ v.eval valuation := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [Word.eval, BitVec.getElem_ofFnLE, BitVec.getElem_xor]
  change valuation
      (Vector.zipWith (· + ·) u.bitsLE v.bitsLE)[i] = _
  rw [Vector.getElem_zipWith hi, Valuation.add_apply]
  generalize valuation u.bitsLE[i] = ub
  generalize valuation v.bitsLE[i] = vb
  cases ub <;> cases vb <;> rfl

theorem Word.eval_xor3 (valuation : Freigen.F2Z.Valuation Bool ctx.WBool)
    (u v w : Word n) :
    (u ^^^ v ^^^ w).eval valuation =
      u.eval valuation ^^^ v.eval valuation ^^^ w.eval valuation := by
  rw [Word.eval_xor, Word.eval_xor]

@[simp]
theorem Word.eval_rotateRight
    (valuation : Freigen.F2Z.Valuation Bool ctx.WBool)
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
theorem Word.eval_shiftRight
    (valuation : Freigen.F2Z.Valuation Bool ctx.WBool)
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
    valuation (getElem (u >>> k).bitsLE i hi) =
        valuation (if h : i < n - k then u.bitsLE[k + i] else 0) :=
      congrArg valuation hget
    _ = (BitVec.ofFnLE fun i => valuation u.bitsLE[i]).getLsbD (k + i) := by
      split
      · simp only [BitVec.getLsbD, BitVec.toNat_ofFnLE]
        rw [Nat.testBit_ofBits_lt _ _ (by omega)]
        simp only [Fin.getElem_fin]
      · rw [Valuation.zero_apply]
        simp only [BitVec.getLsbD, BitVec.toNat_ofFnLE]
        rw [Nat.testBit_ofBits_ge _ _ (by omega)]
        rfl

instance : GetElem (Word n) (Fin n) ctx.WBool (fun _ _ => True) where
  getElem w i _ := w.bitsLE[i]

structure U (n : Nat) where
  bits : Word n
  intBits : Vector ctx.Wℤ n

instance : Coe (BitVec n) (U n) where
  coe w := {
    bits := { bitsLE := Vector.ofFn fun i => ofScalar w[i] }
    intBits := Vector.ofFn fun i => ofScalar w[i].toInt
  }

instance : Inhabited ctx.WBool where
  default := 0

instance : Inhabited ctx.Wℤ where
  default := 0

instance : Inhabited (U n) where
  default := {
    bits := {
      bitsLE := Vector.replicate n 0
    }
    intBits := Vector.replicate n 0
  }

def U.Valid (u : U n) (ρ : WF.Valuation) : Prop :=
  ∀ i : Fin n, ρ.int u.intBits[i] = (ρ.bool u.bits.bitsLE[i]).toInt

def U.fromWord (w : Word n) : Circuit (U n) := do
  let mut res := Vector.replicate n 0
  for h:i in [0:n] do
    let b ← f2z w.bitsLE[i]
    res := res.set! i b
  pure { bits := w, intBits := res }

def U.intVal (u : U n) : ctx.Wℤ :=
  ∑ i : Fin n, 2 ^ i.val • u.intBits[i]

def U.eval : U n → WF.Valuation → BitVec n := fun u ρ =>
  BitVec.ofNat n $ (ρ.int u.intVal).toNat

def U.takeLE (m : Nat) (h : m ≤ n) (u : U n) : U m :=
  { bits := { bitsLE := Vector.ofFn fun i => u.bits.bitsLE[i.castLE h] }
    intBits := Vector.ofFn fun i => u.intBits[i.castLE h] }

theorem U.eval_intVal_eq_evalZ (u : U n) (h : u.Valid ρ) :
    ρ.int u.intVal = u.bits.evalZ ρ := by
  unfold U.intVal Word.evalZ
  rw [natCast_ofBits_eq_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_nsmul, h i]
  simp

theorem U.eval_eq_ofFnLE (u : U n) (h : u.Valid ρ) :
    u.eval ρ = BitVec.ofFnLE (fun i => ρ.bool u.bits.bitsLE[i]) := by
  apply BitVec.toNat_inj.mp
  simp [U.eval, U.eval_intVal_eq_evalZ u h, Word.evalZ,
    Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow _)]

theorem U.intVal_eval_eq_eval_toNat (u : U n) (h : u.Valid ρ) :
    ρ.int u.intVal = (u.eval ρ).toNat := by
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
    (u.takeLE m h).eval ρ = BitVec.ofNat m (ρ.int u.intVal).toNat := by
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

def U.fromInt (n : Nat) (x : ctx.Wℤ) : Circuit (U n) := do
  let bits ← hint (argTps := [.z]) h![x] fun h![(x: Int)] => match x with
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

end Generic

local instance : Context := lcContext

open Std.Do
open scoped Std.Do

private theorem Vector.set!_eq_setIfInBounds (xs : Vector α n) (i : Nat) (x : α) :
    xs.set! i x = xs.setIfInBounds i x := by
  rfl

@[simp]
theorem U.valid_default {n : Nat} : (default : U n).Valid ρ := by
  intro i
  change ρ.int (Vector.replicate n (0 : LC ℤ))[i.val] =
    (ρ.bool (Vector.replicate n (0 : LC Bool))[i.val]).toInt
  simp
  rfl

@[spec]
theorem U.fromWord_sound {ρ} {w : Word n}:
    ⦃ ⌜True⌝ ⦄
      (Sound.interp ρ $ U.fromWord w)
    ⦃ ⇓ u => ⌜u.bits = w⌝ ∧ ⌜u.Valid ρ⌝ ⦄ := by
  mvcgen [U.fromWord] invariants
  · ⇓⟨cur, res⟩ => ⌜∀ i : Fin n, i.val < cur.prefix.length →
      ρ.int res[i] = (ρ.bool w.bitsLE[i]).toInt⌝
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
      simpa only [Vector.getElem_setIfInBounds, hieq,
        ← LC.Valuation.apply_eq_eval, if_pos] using h₂.symm
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
      ρ.int res[i] = (ρ.bool w.bitsLE[i]).toInt⌝
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
      simpa only [Vector.getElem_setIfInBounds, hieq,
        ← LC.Valuation.apply_eq_eval, if_pos] using h₂
  case vc2 => simp
  case vc3 h =>
    constructor
    · trivial
    · intro i
      exact h i (by grind)

private theorem U.fromWord_wf_pointwise :
    WF.GadgetSpec
      (Input := fun ctx => @Word ctx n)
      (Output := fun ctx => @U ctx n)
      (fun {leftCtx rightCtx}
          (leftVal : @WF.Valuation leftCtx)
          (rightVal : @WF.Valuation rightCtx)
          (left : @Word leftCtx n) (right : @Word rightCtx n) =>
        ∀ i : Fin n,
          WF.LCEq leftVal.bool rightVal.bool
            (@Word.bitsLE leftCtx n left)[i]
            (@Word.bitsLE rightCtx n right)[i])
      (fun {ctx} (w : @Word ctx n) => @U.fromWord ctx n w)
      (fun {leftCtx rightCtx}
          (leftVal : @WF.Valuation leftCtx)
          (rightVal : @WF.Valuation rightCtx)
          (left : @U leftCtx n) (right : @U rightCtx n) =>
        (∀ i : Fin n, WF.LCEq leftVal.bool rightVal.bool
          (@Word.bitsLE leftCtx n (@U.bits leftCtx n left))[i]
          (@Word.bitsLE rightCtx n (@U.bits rightCtx n right))[i]) ∧
        (∀ i : Fin n, WF.LCEq leftVal.int rightVal.int
          (@U.intBits leftCtx n left)[i]
          (@U.intBits rightCtx n right)[i])) := by
  intro leftCtx rightCtx left right
  unfold U.fromWord
  simp only [pure_bind]
  apply WF.Rel.forIn'_range_f2z_set!_bind
  · intro leftVal rightVal _ i
    simp [WF.IntEq, WF.LCEq]
  · intro a ha leftVal rightVal hinput
    exact hinput ⟨a, ha.upper⟩
  · intro a ha
    exact ha.upper
  · intro A leftInts rightInts hA
    exact WF.Rel.pure fun leftVal rightVal h => by
      have related := hA leftVal rightVal h
      exact ⟨related.1, related.2⟩

theorem U.fromWord_wf :
    WF.GadgetSpec
      (Input := fun ctx => @Word ctx n)
      (Output := fun ctx => @U ctx n)
      (fun {leftCtx rightCtx}
          (leftVal : @WF.Valuation leftCtx)
          (rightVal : @WF.Valuation rightCtx)
          (left : @Word leftCtx n) (right : @Word rightCtx n) =>
        ∀ i : Fin n, WF.LCEq leftVal.bool rightVal.bool
          (@Word.bitsLE leftCtx n left)[i]
          (@Word.bitsLE rightCtx n right)[i])
      (fun {ctx} (w : @Word ctx n) => @U.fromWord ctx n w)
      (fun {leftCtx rightCtx}
          (leftVal : @WF.Valuation leftCtx)
          (rightVal : @WF.Valuation rightCtx)
          (left : @U leftCtx n) (right : @U rightCtx n) =>
        (∀ i : Fin n, WF.LCEq leftVal.bool rightVal.bool
          (@Word.bitsLE leftCtx n (@U.bits leftCtx n left))[i]
          (@Word.bitsLE rightCtx n (@U.bits rightCtx n right))[i]) ∧
        (∀ i : Fin n, WF.LCEq leftVal.int rightVal.int
          (@U.intBits leftCtx n left)[i]
          (@U.intBits rightCtx n right)[i]) ∧
        WF.LCEq leftVal.int rightVal.int
          (@U.intVal leftCtx n left) (@U.intVal rightCtx n right)) := by
  intro leftCtx rightCtx left right
  exact (U.fromWord_wf_pointwise leftCtx rightCtx left right).mono
    (fun leftVal rightVal left right h => ⟨h.1, h.2, by
      unfold U.intVal
      exact WF.eval_sum fun i => WF.eval_nsmul _ (h.2 i)⟩)

theorem U.fromInt_sound {ρ} {n : Nat} {x : LC ℤ} :
    ⦃ ⌜True⌝ ⦄ (Sound.interp ρ $ U.fromInt n x)
    ⦃ ⇓ u => ⌜u.Valid ρ⌝ ∧ ⌜ρ.int u.intVal = ρ.int x⌝ ⦄ := by
  mvcgen [fromInt]
  intro b
  mvcgen
  simp only [Valid, Valuation.sub_apply, Valuation.zero_apply, zero_mul] at *
  constructor
  · aesop
  · omega

theorem U.fromInt_complete {ρ} {n : Nat} {x : LC ℤ} (h0 : ρ.int x ≥ 0)
    (h2 : ρ.int x < 2 ^ n) :
    ⦃ ⌜True⌝ ⦄ (Complete.interp ρ $ U.fromInt n x)
    ⦃ ⇓ u => ⌜u.Valid ρ⌝ ∧ ⌜ρ.int u.intVal = ρ.int x⌝ ⦄ := by
  mvcgen [fromInt]
  have : ∃n, ρ.int x = Int.ofNat n := by
    exists (ρ.int x).toNat
    exact (Int.toNat_of_nonneg h0).symm
  rcases this with ⟨x', hx'⟩
  have hxv : ρ.int x = Int.ofNat x' := hx'
  simp only [WF.interpHint, WF.evalArgs, hxv,
    Int.ofNat_eq_natCast, Free.interp_pure, Option.pure_def,
    Option.some.injEq, exists_eq_left', Vector.map_ofFn]
  mvcgen
  rename_i r h
  rcases h with ⟨h, h'⟩
  have hxlt : x' < 2 ^ n := by
    rw [hx'] at h2
    exact Int.ofNat_lt.mp (by simpa using h2)
  have hbits : r.bits.evalZ ρ = x' := by
    simp only [Word.evalZ, h, Vector.getElem_ofFn, Function.comp_apply,
      Fin.getElem_fin]
    have heval : ∀ i : Fin n,
        ρ.bool (LC.ofConst (x'.testBit i)) = x'.testBit i :=
      fun i => LC.Valuation.ofConst_apply ρ.bool (x'.testBit i)
    simp_rw [heval]
    rw [Nat.ofBits_testBit, Nat.mod_eq_of_lt hxlt]
  have hintVal' : ρ.int r.intVal = (x' : Int) :=
    (U.eval_intVal_eq_evalZ r h').trans (by simpa using hbits)
  have hintVal : ρ.int r.intVal = (x' : Int) := hintVal'
  constructor
  · simp [Valuation.sub_apply, hxv, hintVal']
  · mvcgen

private theorem U.fromInt_hintRel {leftCtx rightCtx : Context}
    (leftVal : @WF.Valuation leftCtx) (rightVal : @WF.Valuation rightCtx)
    (left : leftCtx.Wℤ) (right : rightCtx.Wℤ)
    (h : WF.LCEq leftVal.int rightVal.int left right) :
    WF.HintRel Eq
      (show @Hint leftCtx (Vector Bool n) from
        match leftVal.int left with
        | .ofNat value => pure (Vector.ofFn fun i => value.testBit i)
        | _ => F2Z.fail (ctx := leftCtx)
            s!"negative integer {leftVal.int left} in U.fromInt")
      (show @Hint rightCtx (Vector Bool n) from
        match rightVal.int right with
        | .ofNat value => pure (Vector.ofFn fun i => value.testBit i)
        | _ => F2Z.fail (ctx := rightCtx)
            s!"negative integer {rightVal.int right} in U.fromInt") := by
  unfold WF.LCEq at h
  unfold WF.HintRel
  rw [h]
  cases rightVal.int right <;> simp

theorem U.fromInt_wf :
    WF.GadgetSpec
      (Input := fun ctx => ctx.Wℤ)
      (Output := fun ctx => @U ctx n)
      (fun {leftCtx rightCtx}
          (leftVal : @WF.Valuation leftCtx)
          (rightVal : @WF.Valuation rightCtx)
          (left : leftCtx.Wℤ) (right : rightCtx.Wℤ) =>
        WF.LCEq leftVal.int rightVal.int left right)
      (fun {ctx} (x : ctx.Wℤ) => @U.fromInt ctx n x)
      (fun {leftCtx rightCtx}
          (leftVal : @WF.Valuation leftCtx)
          (rightVal : @WF.Valuation rightCtx)
        (left : @U leftCtx n) (right : @U rightCtx n) =>
        (∀ i : Fin n, WF.LCEq leftVal.bool rightVal.bool
          (@Word.bitsLE leftCtx n (@U.bits leftCtx n left))[i]
          (@Word.bitsLE rightCtx n (@U.bits rightCtx n right))[i]) ∧
        (∀ i : Fin n, WF.LCEq leftVal.int rightVal.int
          (@U.intBits leftCtx n left)[i]
          (@U.intBits rightCtx n right)[i]) ∧
        WF.LCEq leftVal.int rightVal.int
          (@U.intVal leftCtx n left) (@U.intVal rightCtx n right)) := by
  intro leftCtx rightCtx left right
  unfold U.fromInt
  apply WF.Rel.hint
  · intro leftVal rightVal h
    simpa [WF.ArgsEq, WF.evalArgs, WF.LCEq,
      Eff.WitnessSide.denoteF] using h
  · intro leftVal rightVal h
    simpa [WF.evalArgs, Eff.WitnessSide.denoteF] using
      U.fromInt_hintRel leftVal rightVal left right h
  · intro outL outR
    apply ((U.fromWord_wf leftCtx rightCtx
        (@Word.mk leftCtx n outL)
        (@Word.mk rightCtx n outR)).frame
        (fun leftVal rightVal h i => by
          unfold WF.LCEq
          rcases h.2 with ⟨values, _, _, hleft, hright⟩
          change leftVal.bool outL[i] = rightVal.bool outR[i]
          exact (hleft i.val i.isLt).trans (hright i.val i.isLt).symm)).bind
      (fun value => F2Z.assertR1C (ctx := leftCtx) 0 0
        (left - @U.intVal leftCtx n value) >>= fun _ => pure value)
      (fun value => F2Z.assertR1C (ctx := rightCtx) 0 0
        (right - @U.intVal rightCtx n value) >>= fun _ => pure value)
    intro A leftOut rightOut hA
    apply WF.Rel.assertR1C
    · intro leftVal rightVal _
      simp [WF.LCEq]
    · intro leftVal rightVal _
      simp [WF.LCEq]
    · intro leftVal rightVal h
      have related := hA leftVal rightVal h
      exact WF.eval_sub related.1.1 related.2.2.2
    · exact WF.Rel.pure fun leftVal rightVal h => by
        have related := hA leftVal rightVal h
        exact ⟨related.2.1, related.2.2.1, related.2.2.2⟩

def U.sumValue (u : Array (U n)) (ρ : WF.Valuation) : BitVec n :=
  BitVec.ofNat n
    (ρ.int (u.map (fun value : U n => value.intVal)).sum).toNat

theorem U.intVal_nonneg (u : U n) (h : u.Valid ρ) :
    0 ≤ ρ.int u.intVal := by
  rw [U.eval_intVal_eq_evalZ u h]
  exact Int.natCast_nonneg _

theorem U.intVal_lt_two_pow (u : U n) (h : u.Valid ρ) :
    ρ.int u.intVal < (2 ^ n : Nat) := by
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
    0 ≤ ρ.int (us.map (fun value : U n => value.intVal)).sum := by
  rw [Valuation.array_sum, ← Array.sum_toList]
  simp only [Array.map_map]
  apply List.sum_nonneg
  intro value hvalue
  simp only [Array.toList_map, List.mem_map] at hvalue
  obtain ⟨u, hu, rfl⟩ := hvalue
  exact U.intVal_nonneg u (hvalid u (by simpa using hu))

theorem U.sum_lt_capacity (us : Array (U n))
    (hvalid : ∀ u ∈ us, u.Valid ρ) :
    ρ.int (us.map (fun value : U n => value.intVal)).sum <
      2 ^ (n + Nat.clog 2 us.size) := by
  rw [Valuation.array_sum, ← Array.sum_toList]
  simp only [Array.map_map]
  by_cases hempty : us = #[]
  · subst us
    simp
  · have hne : (us.map fun u => ρ.int u.intVal).toList ≠ [] := by
      simp [hempty]
    have hsum := List.sum_lt_length_mul hne (fun value hvalue => by
      simp only [Array.toList_map, List.mem_map] at hvalue
      obtain ⟨u, hu, rfl⟩ := hvalue
      exact U.intVal_lt_two_pow u (hvalid u (by simpa using hu)))
    have hsum' :
        (us.map fun u => ρ.int u.intVal).toList.sum <
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
        (us.map (fun u : U n => ρ.int u.intVal)).sum.toNat =
      (us.map fun u : U n => u.eval ρ).sum := by
  induction us with
  | nil => simp
  | cons u us ih =>
      have hu := hvalid u (by simp)
      have hus : ∀ v ∈ us, v.Valid ρ := by
        intro v hv
        exact hvalid v (by simp [hv])
      have htail : 0 ≤
          (us.map fun u : U n => ρ.int u.intVal).sum :=
        List.sum_nonneg fun value hvalue => by
          simp only [List.mem_map] at hvalue
          obtain ⟨v, hv, rfl⟩ := hvalue
          exact U.intVal_nonneg v (hus v hv)
      simp only [List.map_cons, List.sum_cons]
      rw [Int.toNat_add (U.intVal_nonneg u hu) htail,
        BitVec.ofNat_add, ih hus]
      rw [U.intVal_eval_eq_eval_toNat u hu]
      simp

theorem U.sumValue_eq_sum (us : Array (U n))
    (hvalid : ∀ u ∈ us, u.Valid ρ) :
    U.sumValue us ρ = (us.map fun u : U n => u.eval ρ).sum := by
  unfold U.sumValue
  rw [Valuation.array_sum]
  rw [← Array.sum_toList, ← Array.sum_toList]
  simp only [Array.toList_map, List.map_map]
  change BitVec.ofNat n
      (us.toList.map (fun u : U n => ρ.int u.intVal)).sum.toNat =
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
      ρ.int wide.intVal =
        ρ.int (us.map (fun value : U n => value.intVal)).sum⌝)
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
      ρ.int wide.intVal =
        ρ.int (us.map (fun value : U n => value.intVal)).sum⌝)
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
