import Freigen.F2Z.Examples.EcdsaP256.FixedBaseCombLookupLemmas
import Freigen.F2Z.Examples.P256.IncompleteLemmas

/-!
# Correctness of the mixed-width fixed-base comb

This module lifts the individually verified fixed-table lookups through the
nineteen checked incomplete positional additions and the complete top-window
addition.  It is separate from the lookup arithmetic so an edit to a fold
invariant does not re-elaborate the large selector proofs.
-/

namespace Freigen.F2Z.Examples.EcdsaP256

open Std.Do
open scoped Std.Do
open BigOperators
open Modular
open P256

set_option maxRecDepth 10000

def fixed12SelectedPoint (rho : WF.Valuation) (k : Fn) (window : Nat) :
    Reference.Point :=
  if hwindow : window < 8 then
    fixedSignedPoint (12 * window) 12
      ((combWindowValue (combWindowBits k (12 * window) 12
        (by omega))).eval rho.int).toNat
  else 0

def fixed13SelectedPoint (rho : WF.Valuation) (k : Fn) (window : Nat) :
    Reference.Point :=
  if hwindow : window < 12 then
    fixedSignedPoint (96 + 13 * window) 13
      ((combWindowValue (combWindowBits k (96 + 13 * window) 13
        (by omega))).eval rho.int).toNat
  else 0

def fixedTopSelectedPoint (rho : WF.Valuation) (k : Fn) : Reference.Point :=
  topCombPoint
    ((combWindowValue (combWindowBits k 252 4 (by omega))).eval
      rho.int).toNat
    ((k.val.intBits[0].eval rho.int).toNat)

def fixedDigitCoefficient (offset width : Nat) (raw : Int) : Int :=
  (2 * raw + 1 - 2 ^ width) * 2 ^ offset

def fixed12SelectedCoefficient (rho : WF.Valuation) (k : Fn)
    (window : Nat) : Int :=
  if hwindow : window < 8 then
    fixedDigitCoefficient (12 * window) 12
      ((combWindowValue (combWindowBits k (12 * window) 12
        (by omega))).eval rho.int)
  else 0

def fixed13SelectedCoefficient (rho : WF.Valuation) (k : Fn)
    (window : Nat) : Int :=
  if hwindow : window < 12 then
    fixedDigitCoefficient (96 + 13 * window) 13
      ((combWindowValue (combWindowBits k (96 + 13 * window) 13
        (by omega))).eval rho.int)
  else 0

def fixedTopSelectedCoefficient (rho : WF.Valuation) (k : Fn) : Int :=
  fixedDigitCoefficient 252 4
      ((combWindowValue (combWindowBits k 252 4 (by omega))).eval rho.int) -
    (1 - k.val.intBits[0].eval rho.int)

def Fixed12FoldPoint (rho : WF.Valuation) (k : Fn)
    (indices : List Nat) : Reference.Point :=
  indices.foldl (fun acc i => acc + fixed12SelectedPoint rho k (i + 1))
    (fixed12SelectedPoint rho k 0)

def Fixed13FoldPoint (rho : WF.Valuation) (k : Fn)
    (initial : Reference.Point) (indices : List Nat) : Reference.Point :=
  indices.foldl (fun acc i => acc + fixed13SelectedPoint rho k i) initial

def FixedCombPoint (rho : WF.Valuation) (k : Fn) : Reference.Point :=
  Fixed13FoldPoint rho k (Fixed12FoldPoint rho k [:7].toList)
      [:12].toList + fixedTopSelectedPoint rho k

def Fixed12FoldCoefficient (rho : WF.Valuation) (k : Fn)
    (indices : List Nat) : Int :=
  indices.foldl (fun acc i => acc + fixed12SelectedCoefficient rho k (i + 1))
    (fixed12SelectedCoefficient rho k 0)

def Fixed13FoldCoefficient (rho : WF.Valuation) (k : Fn)
    (initial : Int) (indices : List Nat) : Int :=
  indices.foldl (fun acc i => acc + fixed13SelectedCoefficient rho k i) initial

def FixedCombCoefficient (rho : WF.Valuation) (k : Fn) : Int :=
  Fixed13FoldCoefficient rho k (Fixed12FoldCoefficient rho k [:7].toList)
      [:12].toList + fixedTopSelectedCoefficient rho k

theorem fixedSignedPoint_eq_zsmul (offset width raw : Nat)
    (hwidth : 1 ≤ width) (hraw : raw < 2 ^ width) :
    fixedSignedPoint offset width raw =
      fixedDigitCoefficient offset width raw • Reference.generator := by
  unfold fixedSignedPoint fixedDigitCoefficient fixedMagnitudePoint
  split
  · rename_i hpositive
    have hcoeff :
        ((2 * (raw : Int) + 1 - 2 ^ width) * 2 ^ offset) =
          (((2 * (raw - 2 ^ (width - 1)) + 1) * 2 ^ offset : Nat) : Int) := by
      have hp : 0 < 2 ^ (width - 1) := by positivity
      have hpow : (2 : Nat) ^ width = 2 * 2 ^ (width - 1) := by
        cases width with
        | zero => omega
        | succ width => simp [pow_succ, Nat.mul_comm]
      have hpowInt : (2 : Int) ^ width =
          2 * (2 : Int) ^ (width - 1) := by exact_mod_cast hpow
      push_cast
      rw [hpowInt]
      rw [Nat.cast_sub hpositive]
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      ring
    rw [hcoeff]
    norm_cast
  · rename_i hnegative
    have hcoeff :
        ((2 * (raw : Int) + 1 - 2 ^ width) * 2 ^ offset) =
          -((((2 * (2 ^ (width - 1) - 1 - raw) + 1) * 2 ^ offset : Nat) : Int)) := by
      have hp : 0 < 2 ^ (width - 1) := by positivity
      have hpow : (2 : Nat) ^ width = 2 * 2 ^ (width - 1) := by
        cases width with
        | zero => omega
        | succ width => simp [pow_succ, Nat.mul_comm]
      have hpowInt : (2 : Int) ^ width =
          2 * (2 : Int) ^ (width - 1) := by exact_mod_cast hpow
      push_cast
      rw [hpowInt]
      rw [Nat.cast_sub (by omega : raw ≤ 2 ^ (width - 1) - 1),
        Nat.cast_sub (by omega : 1 ≤ 2 ^ (width - 1))]
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      ring
    rw [hcoeff]
    rw [neg_zsmul]
    congr 1

theorem fixed12SelectedPoint_eq_zsmul {k : Fn} (hk : k.val.Valid ρ)
    (window : Nat) :
    fixed12SelectedPoint ρ k window =
      fixed12SelectedCoefficient ρ k window • Reference.generator := by
  unfold fixed12SelectedPoint fixed12SelectedCoefficient
  split
  · rename_i hwindow
    let raw := (combWindowValue (combWindowBits k (12 * window) 12
      (by omega))).eval ρ.int
    have hbits : ∀ i : Fin 12,
        (combWindowBits k (12 * window) 12 (by omega))[i].eval ρ.int = 0 ∨
          (combWindowBits k (12 * window) 12 (by omega))[i].eval ρ.int = 1 := by
      intro i
      simpa [combWindowBits] using
        combBit_bool hk (12 * window + i.val) (by omega)
    have hbounds := combWindowValue_bounds hbits
    have hrawNat : (raw.toNat : Int) = raw := Int.toNat_of_nonneg hbounds.1
    have hrawLt : raw.toNat < 2 ^ 12 := by
      rw [show 2 ^ 12 = 4096 by norm_num]
      omega
    rw [fixedSignedPoint_eq_zsmul _ _ _ (by omega) hrawLt]
    simp only [fixedDigitCoefficient]
    rw [hrawNat]
  · simp

theorem fixed13SelectedPoint_eq_zsmul {k : Fn} (hk : k.val.Valid ρ)
    (window : Nat) :
    fixed13SelectedPoint ρ k window =
      fixed13SelectedCoefficient ρ k window • Reference.generator := by
  unfold fixed13SelectedPoint fixed13SelectedCoefficient
  split
  · rename_i hwindow
    let raw := (combWindowValue (combWindowBits k (96 + 13 * window) 13
      (by omega))).eval ρ.int
    have hbits : ∀ i : Fin 13,
        (combWindowBits k (96 + 13 * window) 13 (by omega))[i].eval ρ.int = 0 ∨
          (combWindowBits k (96 + 13 * window) 13 (by omega))[i].eval ρ.int = 1 := by
      intro i
      simpa [combWindowBits] using
        combBit_bool hk (96 + 13 * window + i.val) (by omega)
    have hbounds := combWindowValue_bounds hbits
    have hrawNat : (raw.toNat : Int) = raw := Int.toNat_of_nonneg hbounds.1
    have hrawLt : raw.toNat < 2 ^ 13 := by
      rw [show 2 ^ 13 = 8192 by norm_num]
      omega
    rw [fixedSignedPoint_eq_zsmul _ _ _ (by omega) hrawLt]
    simp only [fixedDigitCoefficient]
    rw [hrawNat]
  · simp

theorem foldl_points_eq_zsmul (points : Nat → Reference.Point)
    (coefficients : Nat → Int) (indices : List Nat)
    (initialPoint : Reference.Point) (initialCoefficient : Int)
    (hinitial : initialPoint = initialCoefficient • Reference.generator)
    (hpoints : ∀ i, points i = coefficients i • Reference.generator) :
    indices.foldl (fun acc i => acc + points i) initialPoint =
      indices.foldl (fun acc i => acc + coefficients i) initialCoefficient •
        Reference.generator := by
  induction indices generalizing initialPoint initialCoefficient with
  | nil => simpa using hinitial
  | cons i indices ih =>
      simp only [List.foldl_cons]
      apply ih
      · rw [hinitial, hpoints, add_zsmul]

theorem Fixed12FoldPoint.eq_zsmul {k : Fn} (hk : k.val.Valid ρ)
    (indices : List Nat) :
    Fixed12FoldPoint ρ k indices =
      Fixed12FoldCoefficient ρ k indices • Reference.generator := by
  apply foldl_points_eq_zsmul
  · exact fixed12SelectedPoint_eq_zsmul hk 0
  · intro i
    exact fixed12SelectedPoint_eq_zsmul hk (i + 1)

theorem Fixed13FoldPoint.eq_zsmul {k : Fn} (hk : k.val.Valid ρ)
    (initial : Reference.Point) (initialCoefficient : Int)
    (indices : List Nat)
    (hinitial : initial = initialCoefficient • Reference.generator) :
    Fixed13FoldPoint ρ k initial indices =
      Fixed13FoldCoefficient ρ k initialCoefficient indices •
        Reference.generator := by
  apply foldl_points_eq_zsmul
  · exact hinitial
  · intro i
    exact fixed13SelectedPoint_eq_zsmul hk i

theorem fixedTopSelectedPoint_eq_zsmul {k : Fn} (hk : k.val.Valid ρ) :
    fixedTopSelectedPoint ρ k =
      fixedTopSelectedCoefficient ρ k • Reference.generator := by
  let raw := (combWindowValue
    (combWindowBits k 252 4 (by omega))).eval ρ.int
  let parity := k.val.intBits[0].eval ρ.int
  have hraw := topCombRaw_bounds hk
  have hrawNonneg : 0 ≤ raw := by simpa [raw] using (by omega :
    0 ≤ (combWindowValue (combWindowBits k 252 4 (by omega))).eval ρ.int)
  have hrawNat : (raw.toNat : Int) = raw := Int.toNat_of_nonneg hrawNonneg
  have hrawNatLow : 8 ≤ raw.toNat := by omega
  have hrawNatHigh : raw.toNat < 16 := by omega
  have hparity : parity = 0 ∨ parity = 1 := by
    have h0 := hk (0 : Fin 256)
    cases hb : k.val.bits.bitsLE[(0 : Fin 256)].eval ρ.bool <;>
      rw [hb] at h0 <;> simp at h0
    · exact Or.inl h0
    · exact Or.inr h0
  have hparityNonneg : 0 ≤ parity := by rcases hparity with h | h <;> omega
  have hparityNat : (parity.toNat : Int) = parity :=
    Int.toNat_of_nonneg hparityNonneg
  have hparityNatLe : parity.toNat ≤ 1 := by omega
  unfold fixedTopSelectedPoint fixedTopSelectedCoefficient
  rw [topCombPoint, dif_pos hrawNatLow]
  dsimp only
  have hbase : 16 ≤ 2 * raw.toNat + 1 := by omega
  have hsmall : 1 - parity.toNat ≤
      (2 * raw.toNat + 1 - 16) * 2 ^ 252 := by
    have hp : 0 < 2 ^ 252 := by positivity
    omega
  have hcoeff :
      (((2 * raw.toNat + 1 - 16) * 2 ^ 252 -
        (1 - parity.toNat) : Nat) : Int) =
        fixedDigitCoefficient 252 4 raw - (1 - parity) := by
    unfold fixedDigitCoefficient
    rw [Nat.cast_sub hsmall, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_sub hbase, Nat.cast_sub hparityNatLe]
    push_cast
    rw [hrawNat, hparityNat]
  change ((2 * raw.toNat + 1 - 16) * 2 ^ 252 -
      (1 - parity.toNat)) • Reference.generator =
    (fixedDigitCoefficient 252 4 raw - (1 - parity)) • Reference.generator
  rw [← hcoeff]
  norm_cast

theorem FixedCombPoint.eq_zsmul {k : Fn} (hk : k.val.Valid ρ) :
    FixedCombPoint ρ k =
      FixedCombCoefficient ρ k • Reference.generator := by
  unfold FixedCombPoint FixedCombCoefficient
  rw [Fixed13FoldPoint.eq_zsmul hk
      (Fixed12FoldPoint ρ k [:7].toList)
      (Fixed12FoldCoefficient ρ k [:7].toList) [:12].toList
      (Fixed12FoldPoint.eq_zsmul hk [:7].toList),
    fixedTopSelectedPoint_eq_zsmul hk, add_zsmul]

theorem windowValue_eval_split {ρ : WF.Valuation} (k : Fn)
    (start left right : Nat)
    (hfit : start + (left + right) ≤ 256) :
    (windowValue k start (left + right) hfit).eval ρ.int =
      (windowValue k start left (by omega)).eval ρ.int +
        2 ^ left *
          (windowValue k (start + left) right (by omega)).eval ρ.int := by
  unfold windowValue
  simp only [LC.eval_sum, LC.eval_nsmul, nsmul_eq_mul]
  rw [Fin.sum_univ_add]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rcases i with ⟨i, hi⟩
  simp [Fin.natAdd, pow_add]
  ring

theorem combWindowValue_eval_shift {ρ : WF.Valuation} (k : Fn)
    (offset width : Nat)
    (hfit : offset + width ≤ 255) :
    (combWindowValue (combWindowBits k offset width (by omega))).eval ρ.int =
      (windowValue k (offset + 1) width (by omega)).eval ρ.int := by
  unfold combWindowValue combWindowBits windowValue
  simp only [LC.eval_sum, LC.eval_smul, LC.eval_nsmul, nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hget :
      (Vector.ofFn fun j : Fin width =>
        combBit k (offset + j.val) (by omega))[i] =
        combBit k (offset + i.val) (by omega) := by
    exact Vector.get_ofFn _ i
  rw [hget]
  unfold combBit
  rw [dif_pos (by omega)]
  congr 3 <;> omega

theorem combTopWindowValue_eval {ρ : WF.Valuation} (k : Fn) :
    (combWindowValue (combWindowBits k 252 4 (by omega))).eval ρ.int =
      (windowValue k 253 3 (by omega)).eval ρ.int + 8 := by
  unfold combWindowValue combWindowBits windowValue combBit
  norm_num [Fin.sum_univ_succ]
  ring

theorem FixedCombCoefficient.eq_windowValue (k : Fn) :
    FixedCombCoefficient ρ k =
      (windowValue k 0 256 (by omega)).eval ρ.int := by
  norm_num [FixedCombCoefficient, Fixed13FoldCoefficient,
    Fixed12FoldCoefficient, fixed12SelectedCoefficient,
    fixed13SelectedCoefficient, fixedTopSelectedCoefficient,
    fixedDigitCoefficient, Std.Legacy.Range.toList, List.range', List.foldl]
  rw [combWindowValue_eval_shift k 0 12 (by omega),
    combWindowValue_eval_shift k 12 12 (by omega),
    combWindowValue_eval_shift k 24 12 (by omega),
    combWindowValue_eval_shift k 36 12 (by omega),
    combWindowValue_eval_shift k 48 12 (by omega),
    combWindowValue_eval_shift k 60 12 (by omega),
    combWindowValue_eval_shift k 72 12 (by omega),
    combWindowValue_eval_shift k 84 12 (by omega),
    combWindowValue_eval_shift k 96 13 (by omega),
    combWindowValue_eval_shift k 109 13 (by omega),
    combWindowValue_eval_shift k 122 13 (by omega),
    combWindowValue_eval_shift k 135 13 (by omega),
    combWindowValue_eval_shift k 148 13 (by omega),
    combWindowValue_eval_shift k 161 13 (by omega),
    combWindowValue_eval_shift k 174 13 (by omega),
    combWindowValue_eval_shift k 187 13 (by omega),
    combWindowValue_eval_shift k 200 13 (by omega),
    combWindowValue_eval_shift k 213 13 (by omega),
    combWindowValue_eval_shift k 226 13 (by omega),
    combWindowValue_eval_shift k 239 13 (by omega),
    combTopWindowValue_eval k]
  rw [windowValue_eval_split k 0 1 255 (by omega),
    windowValue_eval_split k 1 12 243 (by omega),
    windowValue_eval_split k 13 12 231 (by omega),
    windowValue_eval_split k 25 12 219 (by omega),
    windowValue_eval_split k 37 12 207 (by omega),
    windowValue_eval_split k 49 12 195 (by omega),
    windowValue_eval_split k 61 12 183 (by omega),
    windowValue_eval_split k 73 12 171 (by omega),
    windowValue_eval_split k 85 12 159 (by omega),
    windowValue_eval_split k 97 13 146 (by omega),
    windowValue_eval_split k 110 13 133 (by omega),
    windowValue_eval_split k 123 13 120 (by omega),
    windowValue_eval_split k 136 13 107 (by omega),
    windowValue_eval_split k 149 13 94 (by omega),
    windowValue_eval_split k 162 13 81 (by omega),
    windowValue_eval_split k 175 13 68 (by omega),
    windowValue_eval_split k 188 13 55 (by omega),
    windowValue_eval_split k 201 13 42 (by omega),
    windowValue_eval_split k 214 13 29 (by omega),
    windowValue_eval_split k 227 13 16 (by omega),
    windowValue_eval_split k 240 13 3 (by omega)]
  have hbit0 : (windowValue k 0 1 (by omega)).eval ρ.int =
      k.val.intBits[0].eval ρ.int := by
    unfold windowValue
    norm_num [Fin.sum_univ_succ]
  rw [hbit0]
  ring

theorem FixedCombCoefficient.eq_scalar {k : Fn} (hk : k.val.Valid ρ) :
    FixedCombCoefficient ρ k = ((k.val.eval ρ).toNat : Int) := by
  rw [FixedCombCoefficient.eq_windowValue]
  rw [windowValue_eval hk 0 256 (by omega)]
  simp

private theorem range_split_prefix {n cur : Nat} {pref suff : List Nat}
    (h : List.range n = pref ++ cur :: suff) : pref = List.range cur := by
  have hpref : pref = (List.range n).take pref.length := by
    rw [h, List.take_left]
  have hlen : pref.length < n := by
    have hlength := congrArg List.length h
    simp only [List.length_range, List.length_append, List.length_cons] at hlength
    omega
  have hcur : cur = pref.length := by
    have hx := congrArg (fun xs => xs[pref.length]?) h
    rw [List.getElem?_range hlen] at hx
    simpa using hx.symm
  calc
    pref = (List.range n).take pref.length := hpref
    _ = List.range (min pref.length n) := List.take_range
    _ = List.range pref.length := by rw [Nat.min_eq_left hlen.le]
    _ = List.range cur := by rw [hcur]

private theorem Fixed12FoldCoefficient.range_eq_windowValue (k : Fn)
    (n : Nat) (hn : n ≤ 7) :
    Fixed12FoldCoefficient ρ k (List.range n) =
      2 * (windowValue k 1 (12 * (n + 1)) (by omega)).eval ρ.int -
        (2 ^ (12 * (n + 1)) - 1) := by
  induction n with
  | zero =>
      simp only [List.range_zero, Fixed12FoldCoefficient, List.foldl_nil]
      rw [fixed12SelectedCoefficient, dif_pos (by omega)]
      rw [combWindowValue_eval_shift k 0 12 (by omega)]
      simp [fixedDigitCoefficient]
      ring
  | succ n ih =>
      have hn' : n ≤ 7 := by omega
      rw [List.range_succ, Fixed12FoldCoefficient, List.foldl_append]
      simp only [List.foldl]
      change Fixed12FoldCoefficient ρ k (List.range n) +
          fixed12SelectedCoefficient ρ k (n + 1) = _
      rw [ih hn']
      rw [fixed12SelectedCoefficient, dif_pos (by omega)]
      rw [combWindowValue_eval_shift k (12 * (n + 1)) 12 (by omega)]
      have hsplitEval :
          (windowValue k 1 (12 * (n + 1 + 1)) (by omega)).eval ρ.int =
            (windowValue k 1 (12 * (n + 1)) (by omega)).eval ρ.int +
              2 ^ (12 * (n + 1)) *
                (windowValue k (1 + 12 * (n + 1)) 12 (by omega)).eval ρ.int := by
        simpa only [show 12 * (n + 1 + 1) = 12 * (n + 1) + 12 by omega] using
          windowValue_eval_split (ρ := ρ) k 1 (12 * (n + 1)) 12 (by omega)
      rw [hsplitEval]
      simp only [fixedDigitCoefficient]
      ring

private theorem Fixed13FoldCoefficient.range_eq_windowValue (k : Fn)
    (n : Nat) (hn : n ≤ 12) :
    Fixed13FoldCoefficient ρ k
        (Fixed12FoldCoefficient ρ k [:7].toList) (List.range n) =
      2 * (windowValue k 1 (96 + 13 * n) (by omega)).eval ρ.int -
        (2 ^ (96 + 13 * n) - 1) := by
  induction n with
  | zero =>
      simp only [List.range_zero, Fixed13FoldCoefficient, List.foldl_nil]
      rw [show [:7].toList = List.range 7 by decide]
      simpa using Fixed12FoldCoefficient.range_eq_windowValue
        (ρ := ρ) k 7 (by omega)
  | succ n ih =>
      have hn' : n ≤ 12 := by omega
      rw [List.range_succ, Fixed13FoldCoefficient, List.foldl_append]
      simp only [List.foldl]
      change Fixed13FoldCoefficient ρ k
          (Fixed12FoldCoefficient ρ k [:7].toList) (List.range n) +
          fixed13SelectedCoefficient ρ k n = _
      rw [ih hn']
      rw [fixed13SelectedCoefficient, dif_pos (by omega)]
      rw [combWindowValue_eval_shift k (96 + 13 * n) 13 (by omega)]
      have hsplitEval :
          (windowValue k 1 (96 + 13 * (n + 1)) (by omega)).eval ρ.int =
            (windowValue k 1 (96 + 13 * n) (by omega)).eval ρ.int +
              2 ^ (96 + 13 * n) *
                (windowValue k (1 + (96 + 13 * n)) 13 (by omega)).eval ρ.int := by
        simpa only [show 96 + 13 * (n + 1) = (96 + 13 * n) + 13 by omega] using
          windowValue_eval_split (ρ := ρ) k 1 (96 + 13 * n) 13 (by omega)
      rw [hsplitEval]
      simp only [fixedDigitCoefficient]
      ring

private theorem generator_zsmul_ne_zero_of_natAbs_lt {c : Int}
    (hc : c ≠ 0) (hsmall : c.natAbs < scalarModulus) :
    c • Reference.generator ≠ 0 := by
  cases c with
  | ofNat n =>
      have hn : n ≠ 0 := by simpa using hc
      change n < scalarModulus at hsmall
      exact Reference.Aux.generator_nsmul_ne_zero hn hsmall
  | negSucc n =>
      simp only [Int.natAbs_negSucc] at hsmall
      rw [negSucc_zsmul]
      exact neg_ne_zero.mpr
        (Reference.Aux.generator_nsmul_ne_zero (by omega) hsmall)

private theorem odd_int_ne_zero {x : Int} (hx : Odd x) : x ≠ 0 := by
  rcases hx with ⟨k, hk⟩
  omega

private theorem generator_odd_even_chord_safe {a b : Int}
    (haOdd : Odd a) (hbEven : Even b) (hb : b ≠ 0)
    (haSmall : a.natAbs < 2 ^ 252) (hbSmall : b.natAbs < 2 ^ 252) :
    a • Reference.generator ≠ 0 ∧
      b • Reference.generator ≠ 0 ∧
      a • Reference.generator ≠ b • Reference.generator ∧
      a • Reference.generator ≠ -(b • Reference.generator) := by
  have hpowOrder : 2 ^ 253 < scalarModulus := by
    norm_num [scalarModulus]
  have hpow252Order : 2 ^ 252 < scalarModulus := by omega
  have ha : a ≠ 0 := odd_int_ne_zero haOdd
  have hdiffOdd : Odd (a - b) := haOdd.sub_even hbEven
  have hsumOdd : Odd (a + b) := haOdd.add_even hbEven
  have hdiffSmall : (a - b).natAbs < scalarModulus :=
    (Int.natAbs_sub_le a b).trans_lt (by omega)
  have hsumSmall : (a + b).natAbs < scalarModulus :=
    (Int.natAbs_add_le a b).trans_lt (by omega)
  refine ⟨generator_zsmul_ne_zero_of_natAbs_lt ha (haSmall.trans hpow252Order),
    generator_zsmul_ne_zero_of_natAbs_lt hb (hbSmall.trans hpow252Order), ?_, ?_⟩
  · intro heq
    apply generator_zsmul_ne_zero_of_natAbs_lt
      (odd_int_ne_zero hdiffOdd) hdiffSmall
    rw [sub_zsmul, heq]
    exact sub_self _
  · intro heq
    apply generator_zsmul_ne_zero_of_natAbs_lt
      (odd_int_ne_zero hsumOdd) hsumSmall
    rw [add_zsmul, heq]
    exact neg_add_cancel _

private theorem int_natAbs_le_of_bounds {x : Int} {n : Nat}
    (hlower : -(n : Int) ≤ x) (hupper : x ≤ (n : Int)) : x.natAbs ≤ n := by
  by_cases hnonneg : 0 ≤ x
  · have hcastAbs : ((x.natAbs : Nat) : Int) = x :=
      Int.natAbs_of_nonneg hnonneg
    exact_mod_cast (hcastAbs.trans_le hupper)
  · have hnonpos : x ≤ 0 := by omega
    have hnegNonneg : 0 ≤ -x := by omega
    have hcastAbs : ((x.natAbs : Nat) : Int) = -x := by
      rw [← Int.natAbs_neg x]
      exact Int.natAbs_of_nonneg hnegNonneg
    have : -x ≤ (n : Int) := by omega
    exact_mod_cast (hcastAbs.trans_le this)

private theorem centeredCoefficient_odd_bound {bits value : Nat}
    (hbits : 1 ≤ bits) (hvalue : value < 2 ^ bits) :
    Odd (2 * (value : Int) - (2 ^ bits - 1)) ∧
      (2 * (value : Int) - (2 ^ bits - 1)).natAbs ≤ 2 ^ bits - 1 := by
  have hpowCast : ((2 : Int) ^ bits) = ((2 ^ bits : Nat) : Int) := by norm_num
  have hpowEven : Even ((2 : Int) ^ bits) := by
    rw [show bits = (bits - 1) + 1 by omega, pow_succ]
    exact ⟨(2 : Int) ^ (bits - 1), by ring⟩
  have haEq : 2 * (value : Int) - (2 ^ bits - 1) =
      2 * (value : Int) + 1 - ((2 ^ bits : Nat) : Int) := by
    rw [← hpowCast]
    ring
  have hodd : Odd (2 * (value : Int) - (2 ^ bits - 1)) := by
    rw [haEq, ← hpowCast]
    exact (odd_two_mul_add_one (value : Int)).sub_even hpowEven
  have hvalue' : (value : Int) < ((2 ^ bits : Nat) : Int) := by exact_mod_cast hvalue
  have hlower : -((2 ^ bits - 1 : Nat) : Int) ≤
      2 * (value : Int) - (2 ^ bits - 1) := by
    rw [haEq]
    push_cast
    omega
  have hupper : 2 * (value : Int) - (2 ^ bits - 1) ≤
      ((2 ^ bits - 1 : Nat) : Int) := by
    rw [haEq]
    push_cast
    omega
  have habs : (2 * (value : Int) - (2 ^ bits - 1)).natAbs ≤
      2 ^ bits - 1 := by
    exact int_natAbs_le_of_bounds hlower hupper
  exact ⟨hodd, habs⟩

private theorem centeredCoefficient_odd_small {bits value : Nat}
    (hbits : 1 ≤ bits) (hbitsMax : bits ≤ 252) (hvalue : value < 2 ^ bits) :
    Odd (2 * (value : Int) - (2 ^ bits - 1)) ∧
      (2 * (value : Int) - (2 ^ bits - 1)).natAbs < 2 ^ 252 := by
  have h := centeredCoefficient_odd_bound hbits hvalue
  have hpowLe : 2 ^ bits ≤ 2 ^ 252 :=
    Nat.pow_le_pow_right (by omega) hbitsMax
  exact ⟨h.1, by omega⟩

private theorem fixedDigitCoefficient_later_properties {offset width raw : Nat}
    (hoffset : 1 ≤ offset) (hwidth : 1 ≤ width)
    (hfit : offset + width ≤ 252) (hraw : raw < 2 ^ width) :
    let c := fixedDigitCoefficient offset width raw
    Even c ∧ c ≠ 0 ∧ c.natAbs < 2 ^ 252 := by
  have hdigit := centeredCoefficient_odd_bound hwidth hraw
  have hdigitNe : 2 * (raw : Int) - (2 ^ width - 1) ≠ 0 :=
    odd_int_ne_zero hdigit.1
  have hcoeff : fixedDigitCoefficient offset width raw =
      (2 * (raw : Int) - (2 ^ width - 1)) * 2 ^ offset := by
    unfold fixedDigitCoefficient
    ring
  have hpowNe : (2 : Int) ^ offset ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpowEven : Even ((2 : Int) ^ offset) := by
    rw [show offset = (offset - 1) + 1 by omega, pow_succ]
    exact ⟨(2 : Int) ^ (offset - 1), by ring⟩
  have hbound : (fixedDigitCoefficient offset width raw).natAbs < 2 ^ 252 := by
    rw [hcoeff, Int.natAbs_mul, Int.natAbs_pow]
    calc
      _ ≤ (2 ^ width - 1) * 2 ^ offset :=
        Nat.mul_le_mul_right _ hdigit.2
      _ < 2 ^ width * 2 ^ offset := by
        have : 0 < 2 ^ offset := pow_pos (by omega) _
        exact Nat.mul_lt_mul_of_pos_right (by omega) this
      _ = 2 ^ (width + offset) := by rw [← pow_add]
      _ ≤ 2 ^ 252 := by
        apply Nat.pow_le_pow_right (by omega)
        omega
  exact ⟨by rw [hcoeff]; exact hpowEven.mul_left _,
    by rw [hcoeff]; exact mul_ne_zero hdigitNe hpowNe, hbound⟩

private theorem Fixed12FoldCoefficient.internal_properties {k : Fn}
    (hk : k.val.Valid ρ) {cur : Nat} (hcur : cur < 7) :
    Odd (Fixed12FoldCoefficient ρ k (List.range cur)) ∧
      (Fixed12FoldCoefficient ρ k (List.range cur)).natAbs < 2 ^ 252 := by
  rw [Fixed12FoldCoefficient.range_eq_windowValue k cur (by omega)]
  rw [windowValue_eval hk 1 (12 * (cur + 1)) (by omega)]
  apply centeredCoefficient_odd_small (by omega) (by omega)
  exact BitVec.isLt _

private theorem Fixed13FoldCoefficient.internal_properties {k : Fn}
    (hk : k.val.Valid ρ) {cur : Nat} (hcur : cur < 12) :
    Odd (Fixed13FoldCoefficient ρ k
      (Fixed12FoldCoefficient ρ k [:7].toList) (List.range cur)) ∧
      (Fixed13FoldCoefficient ρ k
        (Fixed12FoldCoefficient ρ k [:7].toList)
        (List.range cur)).natAbs < 2 ^ 252 := by
  rw [Fixed13FoldCoefficient.range_eq_windowValue k cur (by omega)]
  rw [windowValue_eval hk 1 (96 + 13 * cur) (by omega)]
  apply centeredCoefficient_odd_small (by omega) (by omega)
  exact BitVec.isLt _

private theorem fixed12SelectedCoefficient.later_properties {k : Fn}
    (hk : k.val.Valid ρ) {window : Nat} (hwindowLower : 1 ≤ window)
    (hwindowUpper : window < 8) :
    let c := fixed12SelectedCoefficient ρ k window
    Even c ∧ c ≠ 0 ∧ c.natAbs < 2 ^ 252 := by
  rw [fixed12SelectedCoefficient, dif_pos hwindowUpper]
  rw [combWindowValue_eval_shift k (12 * window) 12 (by omega)]
  rw [windowValue_eval hk (12 * window + 1) 12 (by omega)]
  apply fixedDigitCoefficient_later_properties (by omega) (by omega) (by omega)
  exact BitVec.isLt _

private theorem fixed13SelectedCoefficient.later_properties {k : Fn}
    (hk : k.val.Valid ρ) {window : Nat} (hwindow : window < 12) :
    let c := fixed13SelectedCoefficient ρ k window
    Even c ∧ c ≠ 0 ∧ c.natAbs < 2 ^ 252 := by
  rw [fixed13SelectedCoefficient, dif_pos hwindow]
  rw [combWindowValue_eval_shift k (96 + 13 * window) 13 (by omega)]
  rw [windowValue_eval hk (96 + 13 * window + 1) 13 (by omega)]
  apply fixedDigitCoefficient_later_properties (by omega) (by omega) (by omega)
  exact BitVec.isLt _

private theorem fixed12_internal_chord_safe {k : Fn} (hk : k.val.Valid ρ)
    {pref suff : List Nat} {cur : Nat}
    (hsplit : [:7].toList = pref ++ cur :: suff) :
    let acc := Fixed12FoldPoint ρ k pref
    let point := fixed12SelectedPoint ρ k (cur + 1)
    acc ≠ 0 ∧ point ≠ 0 ∧ acc ≠ point ∧ acc ≠ -point := by
  have hrange : [:7].toList = List.range 7 := by decide
  have hsplit' : List.range 7 = pref ++ cur :: suff := by simpa [hrange] using hsplit
  have hpref : pref = List.range cur := range_split_prefix hsplit'
  have hcur : cur < 7 := by
    have := List.mem_range.mp (by
      rw [hsplit']
      exact List.mem_append_right pref (List.mem_cons_self))
    exact this
  let a := Fixed12FoldCoefficient ρ k (List.range cur)
  let b := fixed12SelectedCoefficient ρ k (cur + 1)
  have ha := Fixed12FoldCoefficient.internal_properties hk hcur
  have hb := fixed12SelectedCoefficient.later_properties
    (ρ := ρ) (window := cur + 1) hk (by omega) (by omega)
  have hsafe := generator_odd_even_chord_safe ha.1 hb.1 hb.2.1 ha.2 hb.2.2
  rw [hpref, Fixed12FoldPoint.eq_zsmul hk, fixed12SelectedPoint_eq_zsmul hk]
  exact hsafe

private theorem fixed13_internal_chord_safe {k : Fn} (hk : k.val.Valid ρ)
    {pref suff : List Nat} {cur : Nat}
    (hsplit : [:12].toList = pref ++ cur :: suff) :
    let acc := Fixed13FoldPoint ρ k (Fixed12FoldPoint ρ k [:7].toList) pref
    let point := fixed13SelectedPoint ρ k cur
    acc ≠ 0 ∧ point ≠ 0 ∧ acc ≠ point ∧ acc ≠ -point := by
  have hrange : [:12].toList = List.range 12 := by decide
  have hsplit' : List.range 12 = pref ++ cur :: suff := by simpa [hrange] using hsplit
  have hpref : pref = List.range cur := range_split_prefix hsplit'
  have hcur : cur < 12 := by
    have := List.mem_range.mp (by
      rw [hsplit']
      exact List.mem_append_right pref (List.mem_cons_self))
    exact this
  have ha := Fixed13FoldCoefficient.internal_properties hk hcur
  have hb := fixed13SelectedCoefficient.later_properties hk hcur
  have hsafe := generator_odd_even_chord_safe ha.1 hb.1 hb.2.1 ha.2 hb.2.2
  rw [Fixed13FoldPoint.eq_zsmul hk _ _ _
      (Fixed12FoldPoint.eq_zsmul hk [:7].toList),
    fixed13SelectedPoint_eq_zsmul hk, hpref]
  exact hsafe

theorem FixedCombPoint.eq_scalar {k : Fn} (hk : k.val.Valid ρ) :
    FixedCombPoint ρ k = (k.val.eval ρ).toNat • Reference.generator := by
  rw [FixedCombPoint.eq_zsmul hk, FixedCombCoefficient.eq_scalar hk]
  norm_cast

theorem fixedSignedPoint_order (offset width raw : Nat) :
    scalarModulus • fixedSignedPoint offset width raw = 0 := by
  unfold fixedSignedPoint fixedMagnitudePoint
  split
  · exact Reference.Aux.order_nsmul Reference.Aux.generator_order _
  · rw [neg_nsmul]
    simp only [Reference.Aux.order_nsmul Reference.Aux.generator_order _, neg_zero]

theorem topCombPoint_order (raw parity : Nat) :
    scalarModulus • topCombPoint raw parity = 0 := by
  unfold topCombPoint
  split
  · exact Reference.Aux.order_nsmul Reference.Aux.generator_order _
  · exact Reference.Aux.generator_order

theorem foldl_add_order (points : Nat → Reference.Point)
    (indices : List Nat) (initial : Reference.Point)
    (hinitial : scalarModulus • initial = 0)
    (hpoints : ∀ i, scalarModulus • points i = 0) :
    scalarModulus • indices.foldl (fun acc i => acc + points i) initial = 0 := by
  induction indices generalizing initial with
  | nil => simpa using hinitial
  | cons i indices ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact Reference.Aux.order_add hinitial (hpoints i)

theorem Fixed12FoldPoint.order (rho : WF.Valuation) (k : Fn)
    (indices : List Nat) :
    scalarModulus • Fixed12FoldPoint rho k indices = 0 := by
  apply foldl_add_order
    (points := fun i => fixed12SelectedPoint rho k (i + 1))
    (initial := fixed12SelectedPoint rho k 0)
  · simp only [fixed12SelectedPoint, if_pos (by decide : 0 < 8)]
    exact fixedSignedPoint_order _ _ _
  · intro i
    unfold fixed12SelectedPoint
    split
    · exact fixedSignedPoint_order _ _ _
    · simp

theorem Fixed13FoldPoint.order (rho : WF.Valuation) (k : Fn)
    (initial : Reference.Point) (indices : List Nat)
    (hinitial : scalarModulus • initial = 0) :
    scalarModulus • Fixed13FoldPoint rho k initial indices = 0 := by
  apply foldl_add_order
  · exact hinitial
  · intro i
    unfold fixed13SelectedPoint
    split
    · exact fixedSignedPoint_order _ _ _
    · simp

theorem FixedCombPoint.order (rho : WF.Valuation) (k : Fn) :
    scalarModulus • FixedCombPoint rho k = 0 := by
  unfold FixedCombPoint
  apply Reference.Aux.order_add
  · exact Fixed13FoldPoint.order _ _ _ _ (Fixed12FoldPoint.order _ _ _)
  · exact topCombPoint_order _ _

theorem fixedLookup12Coordinates_normalized {k : Fn} {window : Nat}
    (hk : k.val.Valid ρ) (hwindow : window < 8)
    {out : AffineSlope.Point}
    (hcoord : FixedLookupCoordinatesSpec ρ (12 * window) 12
      (combWindowBits k (12 * window) 12 (by omega)) out) :
    Reference.NormalizedRep ρ out (fixed12SelectedPoint ρ k window) := by
  have hbounds := combWindowValue_bounds (width := 12)
    (bits := combWindowBits k (12 * window) 12 (by omega)) (by
      intro i
      simpa [combWindowBits] using
        combBit_bool hk (12 * window + i.val) (by omega))
  simpa [fixed12SelectedPoint, hwindow] using
    hcoord.normalizedRep (by omega) (by omega) hbounds

theorem fixedLookup13Coordinates_normalized {k : Fn} {window : Nat}
    (hk : k.val.Valid ρ) (hwindow : window < 12)
    {out : AffineSlope.Point}
    (hcoord : FixedLookupCoordinatesSpec ρ (96 + 13 * window) 13
      (combWindowBits k (96 + 13 * window) 13 (by omega)) out) :
    Reference.NormalizedRep ρ out (fixed13SelectedPoint ρ k window) := by
  have hbounds := combWindowValue_bounds (width := 13)
    (bits := combWindowBits k (96 + 13 * window) 13 (by omega)) (by
      intro i
      simpa [combWindowBits] using
        combBit_bool hk (96 + 13 * window + i.val) (by omega))
  simpa [fixed13SelectedPoint, hwindow] using
    hcoord.normalizedRep (by omega) (by omega) hbounds

theorem topLookupCoordinates_normalized {k : Fn} (hk : k.val.Valid ρ)
    {out : AffineSlope.Point} (hcoord : TopLookupCoordinatesSpec ρ k out) :
    Reference.NormalizedRep ρ out (fixedTopSelectedPoint ρ k) := by
  simpa [fixedTopSelectedPoint] using hcoord.normalizedRep hk

@[spec] theorem fixedBaseComb12_sound {k : Fn} (hk : k.val.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (fixedBaseComb12 k)
    ⦃⇓ out => ⌜Reference.NormalizedRep ρ out
      (Fixed12FoldPoint ρ k [:7].toList)⌝⦄ := by
  mvcgen -trivial [fixedBaseComb12, WF.foldRange] invariants
  · ⇓⟨cur, out⟩ => ⌜Reference.NormalizedRep ρ out
      (Fixed12FoldPoint ρ k cur.prefix)⌝
  case vc3.h.success pref cur suff hsplit acc hacc point hpoint out hadd =>
    unfold Fixed12FoldPoint at hadd ⊢
    rw [List.foldl_append]
    simpa [fixed12SelectedPoint] using hadd
  case vc1.hk => exact hk
  case vc2.hk => exact hk
  case vc6 =>
    intros
    exact And.left (by assumption)
  case vc7 =>
    intros
    exact (fixedLookup12Coordinates_normalized hk (by grind) (by assumption)).1
  case vc8.pre hcoord =>
    simpa [Fixed12FoldPoint] using
      fixedLookup12Coordinates_normalized hk (by omega) hcoord
  case vc9.post.success => intro h; exact h

@[spec] theorem fixedBaseComb13_sound {k : Fn}
    {initial : AffineSlope.Point} {initialPoint : Reference.Point}
    (hk : k.val.Valid ρ)
    (hinitial : Reference.NormalizedRep ρ initial initialPoint) :
    ⦃⌜True⌝⦄ Sound.interp ρ (fixedBaseComb13 k initial)
    ⦃⇓ out => ⌜Reference.NormalizedRep ρ out
      (Fixed13FoldPoint ρ k initialPoint [:12].toList)⌝⦄ := by
  mvcgen -trivial [fixedBaseComb13, WF.foldRange] invariants
  · ⇓⟨cur, out⟩ => ⌜Reference.NormalizedRep ρ out
      (Fixed13FoldPoint ρ k initialPoint cur.prefix)⌝
  case vc2.h.success.success pref cur suff hsplit acc hacc point hpoint out hadd =>
    unfold Fixed13FoldPoint at hadd ⊢
    rw [List.foldl_append]
    simpa [fixed13SelectedPoint] using hadd
  case vc1.hk => exact hk
  case vc5 =>
    intro _
    assumption
  case vc6 =>
    intro hcoord
    exact fixedLookup13Coordinates_normalized hk (by grind) hcoord
  case vc7.h.pre => simpa [Fixed13FoldPoint] using hinitial
  case vc8.h.post.success => intro h; exact h

@[spec] theorem fixedBaseComb13Incomplete_sound {k : Fn}
    {initial : AffineSlope.Point} {initialPoint : Reference.Point}
    (hk : k.val.Valid ρ)
    (hinitial : Reference.NormalizedRep ρ initial initialPoint) :
    ⦃⌜True⌝⦄ Sound.interp ρ (fixedBaseComb13Incomplete k initial)
    ⦃⇓ out => ⌜Reference.NormalizedRep ρ out
      (Fixed13FoldPoint ρ k initialPoint [:12].toList)⌝⦄ := by
  mvcgen -trivial [fixedBaseComb13Incomplete, WF.foldRange] invariants
  · ⇓⟨cur, out⟩ => ⌜Reference.NormalizedRep ρ out
      (Fixed13FoldPoint ρ k initialPoint cur.prefix)⌝
  case vc2.h.success pref cur suff hsplit acc hacc point hpoint out hadd =>
    unfold Fixed13FoldPoint at hadd ⊢
    rw [List.foldl_append]
    simpa [fixed13SelectedPoint] using hadd
  case vc1.hk => exact hk
  case vc5 =>
    intro _
    exact And.left (by assumption)
  case vc6 =>
    intro hcoord
    exact (fixedLookup13Coordinates_normalized hk (by grind) hcoord).1
  case vc7.h.pre => simpa [Fixed13FoldPoint] using hinitial
  case vc8.h.post.success => intro h; exact h

@[spec] theorem fixedBaseCombComplete_sound {k : Fn}
    (hk : k.val.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (fixedBaseCombComplete k)
    ⦃⇓ out => ⌜Reference.NormalizedRep ρ out (FixedCombPoint ρ k)⌝⦄ := by
  mvcgen [fixedBaseCombComplete, FixedCombPoint]
  all_goals try assumption
  case vc6 => intro _; assumption
  case vc7 =>
    intro hcoord
    exact topLookupCoordinates_normalized hk hcoord

@[spec] theorem fixedBaseComb12_complete {k : Fn} (hk : k.val.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (fixedBaseComb12 k)
    ⦃⇓ out => ⌜out.Valid ρ ∧ Reference.NormalizedRep ρ out
      (Fixed12FoldPoint ρ k [:7].toList)⌝⦄ := by
  mvcgen -trivial [fixedBaseComb12, WF.foldRange] invariants
  · ⇓⟨cur, out⟩ => ⌜out.Valid ρ ∧
      Reference.NormalizedRep ρ out (Fixed12FoldPoint ρ k cur.prefix) ∧
      scalarModulus • Fixed12FoldPoint ρ k cur.prefix = 0⌝
  case vc3.h.success.success pref cur suff hsplit acc hacc point hpoint out hadd =>
    refine ⟨hadd.1, ?_, ?_⟩
    · unfold Fixed12FoldPoint at hadd ⊢
      rw [List.foldl_append]
      simpa [fixed12SelectedPoint] using hadd.2
    · unfold Fixed12FoldPoint
      rw [List.foldl_append]
      apply Reference.Aux.order_add hacc.2.2
      unfold fixed12SelectedPoint
      rw [dif_pos (by grind)]
      exact fixedSignedPoint_order _ _ _
  case vc1.hk => exact hk
  case vc2.hk => exact hk
  case vc6 => intros; exact (by aesop)
  case vc7 => intros; assumption
  case vc8 => intro _; exact (by aesop)
  case vc9 =>
    intro hpoint
    exact fixedLookup12Coordinates_normalized hk (by grind) hpoint.2
  case vc10 =>
    intros
    exact (fixed12_internal_chord_safe hk (by assumption)).1
  case vc11 =>
    intros
    exact (fixed12_internal_chord_safe hk (by assumption)).2.1
  case vc12 =>
    intros
    exact (fixed12_internal_chord_safe hk (by assumption)).2.2.1
  case vc13 =>
    intros
    exact (fixed12_internal_chord_safe hk (by assumption)).2.2.2
  case vc14.pre hpoint =>
    refine ⟨hpoint.1, ?_, Fixed12FoldPoint.order _ _ _⟩
    simpa [Fixed12FoldPoint] using
      fixedLookup12Coordinates_normalized hk (by omega) hpoint.2
  case vc15.post.success => intros; aesop

@[spec] theorem fixedBaseComb13_complete {k : Fn}
    {initial : AffineSlope.Point} {initialPoint : Reference.Point}
    (hk : k.val.Valid ρ) (hinitialValid : initial.Valid ρ)
    (hinitial : Reference.NormalizedRep ρ initial initialPoint)
    (hinitialOrder : scalarModulus • initialPoint = 0) :
    ⦃⌜True⌝⦄ Complete.interp ρ (fixedBaseComb13 k initial)
    ⦃⇓ out => ⌜out.Valid ρ ∧ Reference.NormalizedRep ρ out
      (Fixed13FoldPoint ρ k initialPoint [:12].toList)⌝⦄ := by
  mvcgen -trivial [fixedBaseComb13, WF.foldRange] invariants
  · ⇓⟨cur, out⟩ => ⌜out.Valid ρ ∧
      Reference.NormalizedRep ρ out
        (Fixed13FoldPoint ρ k initialPoint cur.prefix) ∧
      scalarModulus • Fixed13FoldPoint ρ k initialPoint cur.prefix = 0⌝
  case vc2.h.success.success pref cur suff hsplit acc hacc point hpoint out hadd =>
    refine ⟨hadd.1, ?_, ?_⟩
    · unfold Fixed13FoldPoint at hadd ⊢
      rw [List.foldl_append]
      simpa [fixed13SelectedPoint] using hadd.2
    · unfold Fixed13FoldPoint
      rw [List.foldl_append]
      apply Reference.Aux.order_add hacc.2.2
      unfold fixed13SelectedPoint
      rw [dif_pos (by grind)]
      exact fixedSignedPoint_order _ _ _
  case vc1.hk => exact hk
  case vc5 => intros; exact (by aesop)
  case vc6 => intros; assumption
  case vc7 => intro _; exact (by aesop)
  case vc8 =>
    intro hpoint
    exact fixedLookup13Coordinates_normalized hk (by grind) hpoint.2
  case vc9 =>
    rename_i pref cur suff hsplit acc hacc point
    intro _
    apply Reference.Aux.no_two_torsion_of_order
    exact hacc.2.2
  case vc10.h.pre =>
    simpa [Fixed13FoldPoint] using
      And.intro hinitialValid (And.intro hinitial hinitialOrder)
  case vc11.h.post.success => intros; aesop

@[spec] theorem fixedBaseComb13Incomplete_complete {k : Fn}
    {initial : AffineSlope.Point}
    (hk : k.val.Valid ρ) (hinitialValid : initial.Valid ρ)
    (hinitial : Reference.NormalizedRep ρ initial
      (Fixed12FoldPoint ρ k [:7].toList)) :
    ⦃⌜True⌝⦄ Complete.interp ρ (fixedBaseComb13Incomplete k initial)
    ⦃⇓ out => ⌜out.Valid ρ ∧ Reference.NormalizedRep ρ out
      (Fixed13FoldPoint ρ k (Fixed12FoldPoint ρ k [:7].toList)
        [:12].toList)⌝⦄ := by
  mvcgen -trivial [fixedBaseComb13Incomplete, WF.foldRange] invariants
  · ⇓⟨cur, out⟩ => ⌜out.Valid ρ ∧
      Reference.NormalizedRep ρ out
        (Fixed13FoldPoint ρ k (Fixed12FoldPoint ρ k [:7].toList)
          cur.prefix) ∧
      scalarModulus •
        Fixed13FoldPoint ρ k (Fixed12FoldPoint ρ k [:7].toList)
          cur.prefix = 0⌝
  case vc2.h.success.success pref cur suff hsplit acc hacc point hpoint out hadd =>
    refine ⟨hadd.1, ?_, ?_⟩
    · unfold Fixed13FoldPoint at hadd ⊢
      rw [List.foldl_append]
      simpa [fixed13SelectedPoint] using hadd.2
    · unfold Fixed13FoldPoint
      rw [List.foldl_append]
      apply Reference.Aux.order_add hacc.2.2
      unfold fixed13SelectedPoint
      rw [dif_pos (by grind)]
      exact fixedSignedPoint_order _ _ _
  case vc1.hk => exact hk
  case vc5 => intros; aesop
  case vc6 => intros; assumption
  case vc7 => intros; aesop
  case vc8 =>
    intro hpoint
    exact fixedLookup13Coordinates_normalized hk (by grind) hpoint.2
  case vc9 pref cur suff hsplit acc hacc point =>
    intro _
    exact (fixed13_internal_chord_safe hk hsplit).1
  case vc10 pref cur suff hsplit acc hacc point =>
    intro _
    exact (fixed13_internal_chord_safe hk hsplit).2.1
  case vc11 pref cur suff hsplit acc hacc point =>
    intro _
    exact (fixed13_internal_chord_safe hk hsplit).2.2.1
  case vc12 pref cur suff hsplit acc hacc point =>
    intro _
    exact (fixed13_internal_chord_safe hk hsplit).2.2.2
  case vc13.h.pre =>
    simpa [Fixed13FoldPoint] using
      And.intro hinitialValid (And.intro hinitial
        (Fixed12FoldPoint.order ρ k [:7].toList))
  case vc14.h.post.success => intros; aesop

@[spec] theorem fixedBaseCombComplete_complete {k : Fn}
    (hk : k.val.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (fixedBaseCombComplete k)
    ⦃⇓ out => ⌜out.Valid ρ ∧ Reference.NormalizedRep ρ out
      (FixedCombPoint ρ k)⌝⦄ := by
  mvcgen [fixedBaseCombComplete, FixedCombPoint]
  case vc3.hinitialValid => exact (by aesop)
  case vc4.hinitial => exact (by aesop)
  case vc6 => intros; exact (by aesop)
  case vc7 => intros; assumption
  case vc8 => intros; exact (by aesop)
  case vc9 =>
    intros
    exact topLookupCoordinates_normalized hk (by assumption)
  case vc10 =>
    intros
    apply Reference.Aux.no_two_torsion_of_order
    exact Fixed13FoldPoint.order _ _ _ _ (Fixed12FoldPoint.order _ _ _)

@[spec] theorem fixedBaseCombComplete_sound_scalar {k : Fn}
    (hk : k.val.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (fixedBaseCombComplete k)
    ⦃⇓ out => ⌜Reference.NormalizedRep ρ out
      ((k.val.eval ρ).toNat • Reference.generator)⌝⦄ := by
  apply Triple.iff_conseq.mp (fixedBaseCombComplete_sound hk) (by simp)
  simp only [PostCond.entails, SPred.entails_nil]
  exact ⟨fun _ h => by simpa [FixedCombPoint.eq_scalar hk] using h,
    ExceptConds.entails.refl _⟩

@[spec] theorem fixedBaseCombComplete_complete_scalar {k : Fn}
    (hk : k.val.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (fixedBaseCombComplete k)
    ⦃⇓ out => ⌜out.Valid ρ ∧ Reference.NormalizedRep ρ out
      ((k.val.eval ρ).toNat • Reference.generator)⌝⦄ := by
  apply Triple.iff_conseq.mp (fixedBaseCombComplete_complete hk) (by simp)
  simp only [PostCond.entails, SPred.entails_nil]
  exact ⟨fun _ h => ⟨h.1, by simpa [FixedCombPoint.eq_scalar hk] using h.2⟩,
    ExceptConds.entails.refl _⟩

end Freigen.F2Z.Examples.EcdsaP256
