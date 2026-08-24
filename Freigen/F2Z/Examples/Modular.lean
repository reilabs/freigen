import Freigen.F2Z.Correctness.U

/-!
# Bounded modular arithmetic gadgets

This module deliberately comes before the P-256 implementation.  It contains
the representation and the three proof interfaces used by the curve code:

* `Complete.interp`: the supplied witness generator succeeds;
* `Sound.interp`: every satisfying execution has the advertised value;
* `WF.GadgetSpec`: the gadget is independent of concrete witness names.

## Representation

An `Elem p` is a `U p.bits`, hence it has a Boolean little-endian
decomposition and an integer linear combination for the same value.  The
additional invariant says that the value is strictly below `p.modulus`.

The useful F2Z-specific encoding is in `mul`: over the integer constraint
semantics, the entire modular multiplication is the single R1C equation

`x * y = r + p.modulus * q`.

Both `r` and `q` are range checked by bit decomposition, and `r < modulus` is
proved with a bounded slack.  Thus the equation is exact over `Int`; there are
no limb carries to constrain.  This is not an encoding one may copy to an
R1CS interpreted over a small finite field without an additional no-wrap
argument.
-/

namespace Freigen.F2Z.Examples.Modular

open Std.Do
open scoped Std.Do

/-- Strengthen the initial relational assumption of a well-formedness proof.
This small structural rule makes proved gadgets compositional when an outer
type carries more invariants than a callee consumes. -/
theorem WF.Rel.strengthen {Q : WF.Post α} {R S : WF.Assumption}
    {left right : Circuit α} (h : WF.Rel Q R left right)
    (hSR : ∀ lv rv, S lv rv → R lv rv) :
    WF.Rel Q S left right := by
  induction h generalizing S with
  | pure hpost =>
      exact .pure fun lv rv hS => hpost lv rv (hSR lv rv hS)
  | assertR1C ha hb hc _ ih =>
      exact .assertR1C
        (fun lv rv hS => ha lv rv (hSR lv rv hS))
        (fun lv rv hS => hb lv rv (hSR lv rv hS))
        (fun lv rv hS => hc lv rv (hSR lv rv hS))
        (ih hSR)
  | f2z ha _ ih =>
      apply WF.Rel.f2z (fun lv rv hS => ha lv rv (hSR lv rv hS))
      intro outL outR
      apply ih
      intro lv rv hS
      exact ⟨hSR lv rv hS.1, hS.2.1, hS.2.2⟩
  | hint hargs hbody _ ih =>
      apply WF.Rel.hint
        (fun lv rv hS => hargs lv rv (hSR lv rv hS))
        (fun lv rv hS => hbody lv rv (hSR lv rv hS))
      intro outL outR
      apply ih
      intro lv rv hS
      exact ⟨hSR lv rv hS.1, hS.2⟩

/-- Parameters needed by the generic `n`-bit reduction gadget.  The
lower-half condition makes the quotient of two canonical inputs fit in `n`
bits. -/
structure Params (n : Nat) where
  modulus : Nat
  bitsPositive : 0 < n
  positive : 0 < modulus
  fits : modulus ≤ 2 ^ n
  lowerHalf : 2 ^ (n - 1) ≤ modulus

variable {n : Nat} (p : Params n)

structure Elem (p : Params n) where
  val : U n

namespace Elem

def Valid {p : Params n} (x : Elem p) (ρ : WF.Valuation) : Prop :=
  x.val.Valid ρ ∧ x.val.intVal.eval ρ.int < p.modulus

def evalNat {p : Params n} (x : Elem p) (ρ : WF.Valuation) : Nat :=
  (x.val.intVal.eval ρ.int).toNat

def WFRel {p : Params n} (lv rv : WF.Valuation) (l r : Elem p) : Prop :=
  U.WFRel lv rv l.val r.val

theorem nonneg {x : Elem p} (h : x.Valid ρ) :
    0 ≤ x.val.intVal.eval ρ.int :=
  U.intVal_nonneg x.val h.1

theorem evalNat_cast {x : Elem p} (h : x.Valid ρ) :
    (x.evalNat ρ : Int) = x.val.intVal.eval ρ.int := by
  simp [evalNat, Int.toNat_of_nonneg (Elem.nonneg (p := p) h)]

theorem evalNat_lt {x : Elem p} (h : x.Valid ρ) :
    x.evalNat ρ < p.modulus := by
  unfold evalNat
  exact (Int.toNat_lt (Elem.nonneg (p := p) h)).2 h.2

end Elem

/-- Prove `x < bound` by decomposing the nonnegative slack
`bound - 1 - x`. -/
def assertLt (bound : Nat) (x : U n) : Circuit Unit := do
  let _ ← U.fromInt n (LC.ofConst ((bound : Int) - 1) - x.intVal)
  pure ()

@[spec] theorem assertLt_sound {bound : Nat} {x : U n}
    (hvalid : x.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (assertLt (n := n) bound x)
    ⦃⇓ _ => ⌜x.intVal.eval ρ.int < bound⌝⦄ := by
  unfold assertLt
  rw [Sound.interp_bind]
  apply Triple.bind
    (Q := fun slack => ⌜slack.Valid ρ ∧
      slack.intVal.eval ρ.int =
        (LC.ofConst ((bound : Int) - 1) - x.intVal).eval ρ.int⌝)
  case hx => exact U.fromInt_sound
  case hf =>
    intro slack
    mvcgen
    rename_i hslack
    have hnonneg := U.intVal_nonneg slack hslack.1
    simp only [LC.eval_sub, LC.eval_ofConst] at hslack
    omega

@[spec] theorem assertLt_complete {bound : Nat} {x : U n}
    (hvalid : x.Valid ρ) (hbound : bound ≤ 2 ^ n)
    (hlt : x.intVal.eval ρ.int < bound) :
    ⦃⌜True⌝⦄ Complete.interp ρ (assertLt (n := n) bound x)
    ⦃⇓ _ => ⌜x.intVal.eval ρ.int < bound⌝⦄ := by
  unfold assertLt
  rw [Complete.interp_bind]
  apply Triple.bind
    (Q := fun slack => ⌜slack.Valid ρ ∧
      slack.intVal.eval ρ.int =
        (LC.ofConst ((bound : Int) - 1) - x.intVal).eval ρ.int⌝)
  case hx =>
    apply U.fromInt_complete
    · simp only [LC.eval_sub, LC.eval_ofConst]
      have hx0 := U.intVal_nonneg x hvalid
      omega
    · simp only [LC.eval_sub, LC.eval_ofConst]
      have hx0 := U.intVal_nonneg x hvalid
      have hb : (bound : Int) ≤ (2 ^ n : Nat) := by exact_mod_cast hbound
      rw [show (2 : Int) ^ n = ((2 ^ n : Nat) : Int) by norm_num]
      omega
  case hf =>
    intro slack
    mvcgen

theorem assertLt_wf :
    WF.GadgetSpec
      (fun lv rv (l r : U n) => U.WFRel lv rv l r)
      (assertLt (n := n) bound)
      (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec assertLt
  intro left right
  wfgen' using [U.fromInt_wf_full]

/-- Turn an already bit-decomposed integer into a canonical modular element. -/
def ofU (x : U n) : Circuit (Elem p) := do
  assertLt p.modulus x
  pure ⟨x⟩

@[spec] theorem ofU_sound {x : U n} (hx : x.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (ofU p x)
    ⦃⇓ out => ⌜out.Valid ρ ∧ out.val = x⌝⦄ := by
  mvcgen [ofU, Elem.Valid]

@[spec] theorem ofU_complete {x : U n} (hx : x.Valid ρ)
    (hlt : x.intVal.eval ρ.int < p.modulus) :
    ⦃⌜True⌝⦄ Complete.interp ρ (ofU p x)
    ⦃⇓ out => ⌜out.Valid ρ ∧ out.val = x⌝⦄ := by
  mvcgen [ofU, Elem.Valid]
  case hbound => exact p.fits

theorem ofU_wf :
    WF.GadgetSpec U.WFRel (ofU p) (Elem.WFRel (p := p)) := by
  wfgen' using [assertLt_wf] unfold [ofU, Elem.WFRel]

/-- Constant canonical element. -/
def ofNat (x : Nat) (hfit : x < 2 ^ n) (hlt : x < p.modulus) : Elem p :=
  ⟨BitVec.ofNat n x⟩

theorem ofNat_valid (x : Nat) (hfit : x < 2 ^ n) (hlt : x < p.modulus) :
    (ofNat p x hfit hlt).Valid ρ := by
  constructor
  · exact U.valid_bitVec _
  · change ((BitVec.ofNat n x : U n).intVal.eval ρ.int) < p.modulus
    rw [U.intVal_eval_eq_eval_toNat _ (U.valid_bitVec _), U.eval_bitVec]
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]

theorem ofNat_evalNat (x : Nat) (hfit : x < 2 ^ n) (hlt : x < p.modulus) :
    (ofNat p x hfit hlt).evalNat ρ = x := by
  unfold Elem.evalNat
  change ((BitVec.ofNat n x : U n).intVal.eval ρ.int).toNat = x
  rw [U.intVal_eval_eq_eval_toNat _ (U.valid_bitVec _), U.eval_bitVec]
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]

private theorem constWord_eval_toNat {n : Nat} (v : Nat)
    (hv : v < 2 ^ n) (ρ : WF.Valuation) :
    (Word.eval ρ.bool {
      bitsLE := Vector.ofFn (n := n) fun i => LC.ofConst (v.testBit i)
    }).toNat = v := by
  simp [Word.eval, BitVec.toNat_ofFnLE, Nat.ofBits_testBit,
    Nat.mod_eq_of_lt hv]

private theorem WF.lceq_of_common_realizes
    {left right : Vector (LC Bool) m} {lv rv : WF.Valuation}
    (h : ∃ values : Vector Bool m,
      WF.RealizesBools lv.bool left values ∧
      WF.RealizesBools rv.bool right values)
    (i : Nat) (hi : i < m) :
    WF.LCEq lv.bool rv.bool left[i] right[i] := by
  rcases h with ⟨values, hleft, hright⟩
  exact (hleft i hi).trans (hright i hi).symm

private theorem WF.common_realizes_of_post
    {left right : Vector (LC Bool) m} {lv rv : WF.Valuation}
    {P Q : Prop} {A B : Vector Bool m → Prop}
    (h : (P ∧ ∃ values, A values ∧ B values ∧
      WF.RealizesBools lv.bool left values ∧
      WF.RealizesBools rv.bool right values) ∧ Q) :
    ∃ values, WF.RealizesBools lv.bool left values ∧
      WF.RealizesBools rv.bool right values := by
  rcases h.1.2 with ⟨values, _, _, hleft, hright⟩
  exact ⟨values, hleft, hright⟩

private theorem WF.common_realizes_of_hint
    {left right : Vector (LC Bool) m} {lv rv : WF.Valuation}
    {R : Prop} {bodyL bodyR : Hint (Vector Bool m)}
    (h : R ∧ ∃ values, WF.HintReturns bodyL values ∧
      WF.HintReturns bodyR values ∧
      WF.RealizesBools lv.bool left values ∧
      WF.RealizesBools rv.bool right values) :
    ∃ values, WF.RealizesBools lv.bool left values ∧
      WF.RealizesBools rv.bool right values := by
  rcases h.2 with ⟨values, _, _, hleft, hright⟩
  exact ⟨values, hleft, hright⟩

private theorem WF.lowWord_lceq_of_common_realizes
    {left right : Vector (LC Bool) (2 * n)} {lv rv : WF.Valuation}
    (h : ∃ values : Vector Bool (2 * n),
      WF.RealizesBools lv.bool left values ∧
      WF.RealizesBools rv.bool right values)
    (i : Fin n) :
    WF.LCEq lv.bool rv.bool
      ({ bitsLE := Vector.ofFn fun j => left[j.val]'(by omega) } : Word n)[i]
      ({ bitsLE := Vector.ofFn fun j => right[j.val]'(by omega) } : Word n)[i] := by
  unfold WF.LCEq
  change LC.eval lv.bool (Vector.ofFn fun j : Fin n => left[j.val]'(by omega))[i] =
    LC.eval rv.bool (Vector.ofFn fun j : Fin n => right[j.val]'(by omega))[i]
  have hleft :
      (Vector.ofFn fun j : Fin n => left[j.val]'(by omega))[i] = left[i.val] := by
    change (Vector.ofFn fun j : Fin n => left[j.val]'(by omega)).get i = _
    simp
  have hright :
      (Vector.ofFn fun j : Fin n => right[j.val]'(by omega))[i] = right[i.val] := by
    change (Vector.ofFn fun j : Fin n => right[j.val]'(by omega)).get i = _
    simp
  rw [hleft, hright]
  exact WF.lceq_of_common_realizes h i.val (by omega)

private theorem WF.highWord_lceq_of_common_realizes
    {left right : Vector (LC Bool) (2 * n)} {lv rv : WF.Valuation}
    (h : ∃ values : Vector Bool (2 * n),
      WF.RealizesBools lv.bool left values ∧
      WF.RealizesBools rv.bool right values)
    (i : Fin n) :
    WF.LCEq lv.bool rv.bool
      ({ bitsLE := Vector.ofFn fun j => left[n + j.val]'(by omega) } : Word n)[i]
      ({ bitsLE := Vector.ofFn fun j => right[n + j.val]'(by omega) } : Word n)[i] := by
  unfold WF.LCEq
  change LC.eval lv.bool
      (Vector.ofFn fun j : Fin n => left[n + j.val]'(by omega))[i] =
    LC.eval rv.bool
      (Vector.ofFn fun j : Fin n => right[n + j.val]'(by omega))[i]
  have hleft :
      (Vector.ofFn fun j : Fin n => left[n + j.val]'(by omega))[i] =
        left[n + i.val] := by
    change (Vector.ofFn fun j : Fin n => left[n + j.val]'(by omega)).get i = _
    simp
  have hright :
      (Vector.ofFn fun j : Fin n => right[n + j.val]'(by omega))[i] =
        right[n + i.val] := by
    change (Vector.ofFn fun j : Fin n => right[n + j.val]'(by omega)).get i = _
    simp
  rw [hleft, hright]
  exact WF.lceq_of_common_realizes h (n + i.val) (by omega)

/-- Witness `(r,q)` for Euclidean reduction of a nonnegative integer.  This
is the only place where division occurs; constraints consume only the
resulting bits. -/
def divRemHint (x y : LC ℤ) : Circuit (U n × U n) := do
  let bits ← hint h![x, y] fun h![(a : Int), (b : Int)] =>
    if ha : 0 ≤ a then
      if hb : 0 ≤ b then
      let z := a.toNat * b.toNat
      let r := z % p.modulus
      let q := z / p.modulus
      pure $ Vector.ofFn (n := 2 * n) fun i =>
        if hi : i.val < n then r.testBit i.val
        else q.testBit (i.val - n)
      else
        fail s!"negative factor {b} in modular reduction"
    else
      fail s!"negative factor {a} in modular reduction"
  let r ← U.fromWord {
    bitsLE := Vector.ofFn fun i => bits[i.val]'(by omega) }
  let q ← U.fromWord {
    bitsLE := Vector.ofFn fun i => bits[n + i.val]'(by omega) }
  assertR1C x y (r.intVal + p.modulus • q.intVal)
  assertLt p.modulus r
  pure (r, q)

def DivRemSpec (ρ : WF.Valuation) (x y : LC ℤ) (out : U n × U n) : Prop :=
  out.1.Valid ρ ∧ out.2.Valid ρ ∧
    out.1.intVal.eval ρ.int < p.modulus ∧
    x.eval ρ.int * y.eval ρ.int =
      out.1.intVal.eval ρ.int + p.modulus * out.2.intVal.eval ρ.int

private theorem divRemSpec_of_rel {x y : LC ℤ} {r q : U n}
    (hr : U.Rel ρ r rv) (hq : U.Rel ρ q qv)
    (hlt : r.intVal.eval ρ.int < p.modulus)
    (heq : x.eval ρ.int * y.eval ρ.int =
      (r.intVal + p.modulus • q.intVal).eval ρ.int) :
    DivRemSpec p ρ x y (r, q) := by
  exact ⟨hr.1, hq.1, hlt, by
    simpa only [LC.eval_add, LC.eval_nsmul, nsmul_eq_mul] using heq⟩

@[spec] theorem divRemHint_sound {x y : LC ℤ} :
    ⦃⌜True⌝⦄ Sound.interp ρ (divRemHint p x y)
    ⦃⇓ out => ⌜DivRemSpec p ρ x y out⌝⦄ := by
  mvcgen [divRemHint]
  intro bits
  mvcgen [DivRemSpec]
  all_goals first
    | assumption
    | grind [U.Rel]
    | (apply divRemSpec_of_rel p <;> assumption)

@[spec] theorem divRemHint_complete {x y : LC ℤ}
    (hx0 : 0 ≤ x.eval ρ.int) (hy0 : 0 ≤ y.eval ρ.int)
    (hqBound : (x.eval ρ.int).toNat * (y.eval ρ.int).toNat /
      p.modulus < 2 ^ n) :
    ⦃⌜True⌝⦄ Complete.interp ρ (divRemHint p x y)
    ⦃⇓ out => ⌜DivRemSpec p ρ x y out⌝⦄ := by
  mvcgen [divRemHint]
  let a := (x.eval ρ.int).toNat
  let b := (y.eval ρ.int).toNat
  let bits : Vector Bool (2 * n) := Vector.ofFn fun i =>
    if hi : i.val < n then (a * b % p.modulus).testBit i.val
    else (a * b / p.modulus).testBit (i.val - n)
  refine ⟨bits, ?_, ?_⟩
  · simp [WF.evalArgs, WF.interpHint, hx0, hy0, bits, a, b]
  · mvcgen [DivRemSpec]
    rename_i r hr q hq
    have hrFit : a * b % p.modulus < 2 ^ n :=
      (Nat.mod_lt _ p.positive).trans_le p.fits
    have hqFit : a * b / p.modulus < 2 ^ n := hqBound
    have rWord :
        (Word.eval ρ.bool {
          bitsLE := Vector.ofFn (n := n) fun i =>
            (Vector.map LC.ofConst bits)[i.val]'(by omega)
        }).toNat = a * b % p.modulus := by
      simp [Word.eval, BitVec.toNat_ofFnLE, bits, Nat.ofBits_testBit,
        Nat.mod_eq_of_lt hrFit]
    have qWord :
        (Word.eval ρ.bool {
          bitsLE := Vector.ofFn (n := n) fun i =>
            (Vector.map LC.ofConst bits)[n + i.val]'(by omega)
        }).toNat = a * b / p.modulus := by
      simp [Word.eval, BitVec.toNat_ofFnLE, bits,
        show ∀ i : Fin n, ¬n + i.val < n by omega,
        Nat.ofBits_testBit, Nat.mod_eq_of_lt hqFit]
    have hrVal : r.intVal.eval ρ.int = (a * b % p.modulus : Nat) := by
      rw [U.Rel.intVal hr, rWord]
    have hqVal : q.intVal.eval ρ.int = (a * b / p.modulus : Nat) := by
      rw [U.Rel.intVal hq, qWord]
    have hxVal : x.eval ρ.int = (a : Nat) := by
      exact (Int.toNat_of_nonneg hx0).symm
    have hyVal : y.eval ρ.int = (b : Nat) := by
      exact (Int.toNat_of_nonneg hy0).symm
    constructor
    · simp only [LC.eval_add, LC.eval_nsmul, nsmul_eq_mul,
        hxVal, hyVal, hrVal, hqVal]
      exact_mod_cast (Nat.mod_add_div (a * b) p.modulus).symm
    · mvcgen
      · exact hr.1
      · exact p.fits
      · rw [hrVal]
        exact_mod_cast Nat.mod_lt (a * b) p.positive
      · exact ⟨hr.1, hq.1, by
          rw [hrVal]
          exact_mod_cast Nat.mod_lt (a * b) p.positive, by
          simp only [hxVal, hyVal, hrVal, hqVal]
          exact_mod_cast (Nat.mod_add_div (a * b) p.modulus).symm⟩

theorem divRemHint_wf :
    WF.GadgetSpec
      (fun lv rv (l r : LC ℤ × LC ℤ) =>
        WF.LCEq lv.int rv.int l.1 r.1 ∧
        WF.LCEq lv.int rv.int l.2 r.2)
      (fun x => divRemHint p x.1 x.2)
      (fun lv rv l r =>
        U.WFRel lv rv l.1 r.1 ∧ U.WFRel lv rv l.2 r.2) := by
  wfgen' using [U.fromWord_wf_rel, assertLt_wf] unfold [divRemHint]
  case vc1 =>
    simp_all [WF.LCEq, U.WFRel, Word.WFRel, WF.ArgsEq,
      WF.RealizesBools, WF.evalArgs, LC.eval_add, LC.eval_nsmul]
    grind
  case vc2 outBitsL outBitsR B =>
    rename_i qL qR
    apply WF.highWord_lceq_of_common_realizes
    have hp := outBitsR leftVal rightVal B
    exact WF.common_realizes_of_hint hp.1
  case vc3 =>
    rename_i h
    apply WF.lowWord_lceq_of_common_realizes
    exact WF.common_realizes_of_hint h
  case vc4 =>
    simp_all [WF.LCEq, WF.evalArgs]
  case vc5 =>
    simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

/-- Exact modular multiplication. -/
def mul (x y : Elem p) : Circuit (Elem p) := do
  let rq ← divRemHint p x.val.intVal y.val.intVal
  pure ⟨rq.1⟩

def MulSpec (ρ : WF.Valuation) (x y out : Elem p) : Prop :=
  out.Valid ρ ∧
    (out.evalNat ρ = (x.evalNat ρ * y.evalNat ρ) % p.modulus)

private theorem mulSpec_of_divRem {x y : Elem p} {r q : U n}
    (hx : x.Valid ρ) (hy : y.Valid ρ)
    (hdiv : DivRemSpec p ρ x.val.intVal y.val.intVal (r, q))
    (hrlt : r.intVal.eval ρ.int < p.modulus) :
    MulSpec p ρ x y ⟨r⟩ := by
  have hrValid : (⟨r⟩ : Elem p).Valid ρ := ⟨hdiv.1, hrlt⟩
  refine ⟨hrValid, ?_⟩
  have hq0 := U.intVal_nonneg q hdiv.2.1
  have hr0 := U.intVal_nonneg r hdiv.1
  have hnat : x.evalNat ρ * y.evalNat ρ =
      (r.intVal.eval ρ.int).toNat +
        p.modulus * (q.intVal.eval ρ.int).toNat := by
    have heq := hdiv.2.2.2
    rw [← Elem.evalNat_cast (p := p) hx,
      ← Elem.evalNat_cast (p := p) hy] at heq
    have heq' : (x.evalNat ρ * y.evalNat ρ : Int) =
        ((r.intVal.eval ρ.int).toNat +
          p.modulus * (q.intVal.eval ρ.int).toNat : Nat) := by
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      rw [Int.toNat_of_nonneg hr0, Int.toNat_of_nonneg hq0]
      exact heq
    exact_mod_cast heq'
  have hmod : x.evalNat ρ * y.evalNat ρ ≡
      (r.intVal.eval ρ.int).toNat [MOD p.modulus] := by
    rw [Nat.ModEq]
    simp [hnat, Nat.add_mod]
  have hrNatLt : (r.intVal.eval ρ.int).toNat < p.modulus :=
    (Int.toNat_lt hr0).2 hrlt
  unfold Elem.evalNat
  exact (Nat.mod_eq_of_modEq hmod hrNatLt).symm

@[spec] theorem mul_sound {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (mul p x y)
    ⦃⇓ out => ⌜MulSpec p ρ x y out⌝⦄ := by
  unfold mul
  mvcgen
  rename_i rq hdiv
  exact mulSpec_of_divRem p hx hy hdiv hdiv.2.2.1

@[spec] theorem mul_complete {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (mul p x y)
    ⦃⇓ out => ⌜MulSpec p ρ x y out⌝⦄ := by
  unfold mul
  mvcgen
  · exact Elem.nonneg (p := p) hx
  · exact Elem.nonneg (p := p) hy
  · have hxn := Elem.evalNat_lt (p := p) hx
    have hyn := Elem.evalNat_lt (p := p) hy
    have hab : x.evalNat ρ * y.evalNat ρ < p.modulus * p.modulus := by
      nlinarith
    exact (Nat.div_lt_of_lt_mul (by
      simpa [Elem.evalNat, Nat.mul_comm] using hab)).trans_le
      p.fits
  · rename_i rq hdiv
    exact mulSpec_of_divRem p hx hy hdiv hdiv.2.2.1

theorem mul_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Elem p × Elem p) =>
        Elem.WFRel lv rv l.1 r.1 ∧ Elem.WFRel lv rv l.2 r.2)
      (fun x => mul p x.1 x.2)
      (Elem.WFRel (p := p)) := by
  wfgen' using [U.fromWord_wf_rel, assertLt_wf]
    unfold [mul, divRemHint, Elem.WFRel]
  case vc1 =>
    simp_all [WF.LCEq, U.WFRel, Word.WFRel, WF.ArgsEq,
      WF.RealizesBools, WF.evalArgs, LC.eval_add, LC.eval_nsmul]
    grind
  case vc2 outBitsL outBitsR B =>
    rename_i qL qR
    apply WF.highWord_lceq_of_common_realizes
    have hp := outBitsR leftVal rightVal B
    exact WF.common_realizes_of_hint hp.1
  case vc3 =>
    rename_i h
    apply WF.lowWord_lceq_of_common_realizes
    exact WF.common_realizes_of_hint h
  case vc4 =>
    simp_all [U.WFRel, WF.LCEq, WF.evalArgs]
  case vc5 =>
    simp_all [U.WFRel, WF.LCEq, WF.ArgsEq, WF.evalArgs]

/-! ## Linear reduction, addition, and subtraction -/

def reduce (x : LC ℤ) : Circuit (Elem p) := do
  let rq ← divRemHint p x (LC.ofConst 1)
  pure ⟨rq.1⟩

def ReduceSpec (ρ : WF.Valuation) (x : LC ℤ) (out : Elem p) : Prop :=
  out.Valid ρ ∧ out.evalNat ρ = (x.eval ρ.int).toNat % p.modulus

private theorem reduceSpec_of_divRem {x : LC ℤ} {r q : U n}
    (hx0 : 0 ≤ x.eval ρ.int)
    (hdiv : DivRemSpec p ρ x (LC.ofConst 1) (r, q)) :
    ReduceSpec p ρ x ⟨r⟩ := by
  have hr0 := U.intVal_nonneg r hdiv.1
  have hq0 := U.intVal_nonneg q hdiv.2.1
  have hnat : (x.eval ρ.int).toNat =
      (r.intVal.eval ρ.int).toNat +
        p.modulus * (q.intVal.eval ρ.int).toNat := by
    have heq := hdiv.2.2.2
    simp only [LC.eval_ofConst, mul_one] at heq
    have heq' : ((x.eval ρ.int).toNat : Int) =
        ((r.intVal.eval ρ.int).toNat +
          p.modulus * (q.intVal.eval ρ.int).toNat : Nat) := by
      simp only [Nat.cast_add, Nat.cast_mul]
      rw [Int.toNat_of_nonneg hx0, Int.toNat_of_nonneg hr0,
        Int.toNat_of_nonneg hq0]
      exact heq
    exact_mod_cast heq'
  have hmod : (x.eval ρ.int).toNat ≡
      (r.intVal.eval ρ.int).toNat [MOD p.modulus] := by
    rw [Nat.ModEq]
    simp [hnat, Nat.add_mod]
  have hrlt : (r.intVal.eval ρ.int).toNat < p.modulus :=
    (Int.toNat_lt hr0).2 hdiv.2.2.1
  exact ⟨⟨hdiv.1, hdiv.2.2.1⟩,
    (Nat.mod_eq_of_modEq hmod hrlt).symm⟩

@[spec] theorem reduce_sound {x : LC ℤ} (hx0 : 0 ≤ x.eval ρ.int) :
    ⦃⌜True⌝⦄ Sound.interp ρ (reduce p x)
    ⦃⇓ out => ⌜ReduceSpec p ρ x out⌝⦄ := by
  mvcgen [reduce]
  exact reduceSpec_of_divRem p hx0 (by assumption)

@[spec] theorem reduce_complete {x : LC ℤ} (hx0 : 0 ≤ x.eval ρ.int)
    (hq : (x.eval ρ.int).toNat / p.modulus < 2 ^ n) :
    ⦃⌜True⌝⦄ Complete.interp ρ (reduce p x)
    ⦃⇓ out => ⌜ReduceSpec p ρ x out⌝⦄ := by
  mvcgen [reduce]
  · simp
  · simpa using hq
  · exact reduceSpec_of_divRem p hx0 (by assumption)

theorem reduce_wf :
    WF.GadgetSpec
      (fun lv rv (l r : LC ℤ) => WF.LCEq lv.int rv.int l r)
      (reduce p) (Elem.WFRel (p := p)) := by
  wfgen' using [U.fromWord_wf_rel, assertLt_wf]
    unfold [reduce, divRemHint, Elem.WFRel]
  case vc1 =>
    simp_all [WF.LCEq, U.WFRel, WF.RealizesBools, WF.evalArgs,
      LC.eval_add, LC.eval_nsmul]
    grind
  case vc2 outBitsL outBitsR B =>
    rename_i qL qR
    apply WF.highWord_lceq_of_common_realizes
    have hp := outBitsR leftVal rightVal B
    exact WF.common_realizes_of_hint hp.1
  case vc3 =>
    rename_i h
    apply WF.lowWord_lceq_of_common_realizes
    exact WF.common_realizes_of_hint h
  case vc4 =>
    simp_all [WF.LCEq, WF.evalArgs]
  case vc5 =>
    simp_all [WF.LCEq, WF.ArgsEq, WF.evalArgs]

def add (x y : Elem p) : Circuit (Elem p) :=
  reduce p (x.val.intVal + y.val.intVal)

def AddSpec (ρ : WF.Valuation) (x y out : Elem p) : Prop :=
  out.Valid ρ ∧
    out.evalNat ρ = (x.evalNat ρ + y.evalNat ρ) % p.modulus

private theorem addQuotientFits {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ((x.val.intVal + y.val.intVal).eval ρ.int).toNat /
      p.modulus < 2 ^ n := by
  have hx0 := Elem.nonneg (p := p) hx
  have hy0 := Elem.nonneg (p := p) hy
  have hxlt := hx.2
  have hylt := hy.2
  simp only [LC.eval_add, Int.toNat_add hx0 hy0]
  by_cases hm : p.modulus = 1
  · have hxz : x.val.intVal.eval ρ.int = 0 := by omega
    have hyz : y.val.intVal.eval ρ.int = 0 := by omega
    simp [hxz, hyz]
  · have hm2 : 2 ≤ p.modulus := by omega
    have hprod :
        (x.val.intVal.eval ρ.int).toNat +
          (y.val.intVal.eval ρ.int).toNat < p.modulus * p.modulus := by
      have hxn := (Int.toNat_lt hx0).2 hxlt
      have hyn := (Int.toNat_lt hy0).2 hylt
      nlinarith
    exact (Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hprod)).trans_le
      p.fits

@[spec] theorem add_sound {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (add p x y)
    ⦃⇓ out => ⌜AddSpec p ρ x y out⌝⦄ := by
  unfold add
  mvcgen
  · simpa only [LC.eval_add] using
      add_nonneg (Elem.nonneg (p := p) hx) (Elem.nonneg (p := p) hy)
  · intro hred
    refine ⟨hred.1, ?_⟩
    rw [hred.2]
    simp only [LC.eval_add, Int.toNat_add
      (Elem.nonneg (p := p) hx) (Elem.nonneg (p := p) hy), Elem.evalNat]

@[spec] theorem add_complete {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (add p x y)
    ⦃⇓ out => ⌜AddSpec p ρ x y out⌝⦄ := by
  unfold add
  mvcgen
  · simpa only [LC.eval_add] using
      add_nonneg (Elem.nonneg (p := p) hx) (Elem.nonneg (p := p) hy)
  · exact addQuotientFits p hx hy
  · intro hred
    refine ⟨hred.1, ?_⟩
    rw [hred.2]
    simp only [LC.eval_add, Int.toNat_add
      (Elem.nonneg (p := p) hx) (Elem.nonneg (p := p) hy), Elem.evalNat]

theorem add_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Elem p × Elem p) =>
        Elem.WFRel lv rv l.1 r.1 ∧ Elem.WFRel lv rv l.2 r.2)
      (fun x => add p x.1 x.2) (Elem.WFRel (p := p)) := by
  unfold WF.GadgetSpec add
  intro left right
  apply WF.Rel.strengthen
    (reduce_wf p (left.1.val.intVal + left.2.val.intVal)
      (right.1.val.intVal + right.2.val.intVal))
  intro lv rv h
  unfold Elem.WFRel U.WFRel WF.LCEq at h
  unfold WF.LCEq
  simp only [LC.eval_add]
  rw [h.1.1, h.2.1]

def sub (x y : Elem p) : Circuit (Elem p) :=
  reduce p (x.val.intVal + LC.ofConst (p.modulus : Int) - y.val.intVal)

def SubSpec (ρ : WF.Valuation) (x y out : Elem p) : Prop :=
  out.Valid ρ ∧
    out.evalNat ρ =
      (x.evalNat ρ + p.modulus - y.evalNat ρ) % p.modulus

private theorem subDividend_nonneg {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    0 ≤ (x.val.intVal + LC.ofConst (p.modulus : Int) - y.val.intVal).eval ρ.int := by
  simp only [LC.eval_sub, LC.eval_add, LC.eval_ofConst]
  have hx0 := Elem.nonneg (p := p) hx
  have hylt := hy.2
  omega

private theorem subDividend_toNat {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ((x.val.intVal + LC.ofConst (p.modulus : Int) - y.val.intVal).eval ρ.int).toNat =
      x.evalNat ρ + p.modulus - y.evalNat ρ := by
  have hnonneg := subDividend_nonneg p hx hy
  apply Int.ofNat_inj.mp
  rw [Int.toNat_of_nonneg hnonneg]
  simp only [LC.eval_sub, LC.eval_add, LC.eval_ofConst]
  rw [Nat.cast_sub]
  · simp only [Nat.cast_add]
    rw [Elem.evalNat_cast (p := p) hx, Elem.evalNat_cast (p := p) hy]
  · exact (Elem.evalNat_lt (p := p) hy).le.trans
      (Nat.le_add_left p.modulus (x.evalNat ρ))

private theorem subQuotientFits {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ((x.val.intVal + LC.ofConst (p.modulus : Int) - y.val.intVal).eval ρ.int).toNat /
      p.modulus < 2 ^ n := by
  rw [subDividend_toNat p hx hy]
  by_cases hm : p.modulus = 1
  · have hxz : x.evalNat ρ = 0 := by
      have := Elem.evalNat_lt (p := p) hx
      omega
    have hyz : y.evalNat ρ = 0 := by
      have := Elem.evalNat_lt (p := p) hy
      omega
    have hn : n ≠ 0 := Nat.ne_of_gt p.bitsPositive
    simp [hm, hxz, hyz, hn]
  · have hp := p.positive
    have hm2 : 2 ≤ p.modulus := by omega
    have hnum : x.evalNat ρ + p.modulus - y.evalNat ρ <
        p.modulus * p.modulus := by
      have hxlt := Elem.evalNat_lt (p := p) hx
      nlinarith [Nat.sub_le (x.evalNat ρ + p.modulus) (y.evalNat ρ)]
    exact (Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hnum)).trans_le
      p.fits

@[spec] theorem sub_sound {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (sub p x y)
    ⦃⇓ out => ⌜SubSpec p ρ x y out⌝⦄ := by
  unfold sub
  mvcgen
  · exact subDividend_nonneg p hx hy
  · intro hred
    exact ⟨hred.1, by rw [hred.2, subDividend_toNat p hx hy]⟩

@[spec] theorem sub_complete {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (sub p x y)
    ⦃⇓ out => ⌜SubSpec p ρ x y out⌝⦄ := by
  unfold sub
  mvcgen
  · exact subDividend_nonneg p hx hy
  · exact subQuotientFits p hx hy
  · intro hred
    exact ⟨hred.1, by rw [hred.2, subDividend_toNat p hx hy]⟩

theorem sub_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Elem p × Elem p) =>
        Elem.WFRel lv rv l.1 r.1 ∧ Elem.WFRel lv rv l.2 r.2)
      (fun x => sub p x.1 x.2) (Elem.WFRel (p := p)) := by
  unfold WF.GadgetSpec sub
  intro left right
  apply WF.Rel.strengthen
    (reduce_wf p
      (left.1.val.intVal + LC.ofConst (p.modulus : Int) - left.2.val.intVal)
      (right.1.val.intVal + LC.ofConst (p.modulus : Int) - right.2.val.intVal))
  intro lv rv h
  unfold Elem.WFRel U.WFRel WF.LCEq at h
  unfold WF.LCEq
  simp only [LC.eval_sub, LC.eval_add, LC.eval_ofConst]
  rw [h.1.1, h.2.1]

/-! ## Whole-element conditional selection

Selecting 256 individual coordinate bits with 256 multiplication constraints
is unnecessary.  `select` witnesses the selected canonical word and proves the
choice with one integer R1C equation

`b * (y - x) = out - x`.

The caller supplies the usual Boolean fact `b = 0 ∨ b = 1`.  Exact integer
semantics make this a sound whole-element mux; the output bit decomposition and
`assertLt` retain the canonical representation.
-/

def select (b : LC ℤ) (x y : Elem p) : Circuit (Elem p) := do
  let bits ← hint h![b, x.val.intVal, y.val.intVal]
    fun h![(bit : Int), (xv : Int), (yv : Int)] =>
      if bit = 0 then
        pure $ Vector.ofFn (n := n) fun i => xv.toNat.testBit i
      else if bit = 1 then
        pure $ Vector.ofFn (n := n) fun i => yv.toNat.testBit i
      else
        fail s!"modular select expected a bit, got {bit}"
  let out ← U.fromWord { bitsLE := bits }
  assertR1C b (y.val.intVal - x.val.intVal)
    (out.intVal - x.val.intVal)
  assertLt p.modulus out
  pure ⟨out⟩

def SelectSpec (ρ : WF.Valuation) (b : LC ℤ)
    (x y out : Elem p) : Prop :=
  out.Valid ρ ∧
    out.val.intVal.eval ρ.int =
      x.val.intVal.eval ρ.int +
        b.eval ρ.int *
          (y.val.intVal.eval ρ.int - x.val.intVal.eval ρ.int)

@[spec] theorem select_sound {b : LC ℤ} {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (select p b x y)
    ⦃⇓ out => ⌜SelectSpec p ρ b x y out⌝⦄ := by
  mvcgen [select, SelectSpec]
  intro bits
  mvcgen
  all_goals simp_all [SelectSpec, Elem.Valid, LC.eval_sub, U.Rel]
  all_goals nlinarith

@[spec] theorem select_complete {b : LC ℤ} {x y : Elem p}
    (hx : x.Valid ρ) (hy : y.Valid ρ)
    (hb : b.eval ρ.int = 0 ∨ b.eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Complete.interp ρ (select p b x y)
    ⦃⇓ out => ⌜SelectSpec p ρ b x y out⌝⦄ := by
  mvcgen [select, SelectSpec]
  let chosen := if b.eval ρ.int = 0 then x.evalNat ρ else y.evalNat ρ
  let bits : Vector Bool n := Vector.ofFn fun i => chosen.testBit i
  refine ⟨bits, ?_, ?_⟩
  · rcases hb with hb | hb
    · simp [WF.interpHint, WF.evalArgs, hb, bits, chosen,
        Elem.evalNat, Int.toNat_of_nonneg (Elem.nonneg (p := p) hx)]
    · simp [WF.interpHint, WF.evalArgs, hb, bits, chosen,
        Elem.evalNat, Int.toNat_of_nonneg (Elem.nonneg (p := p) hy)]
  · mvcgen
    rename_i out hout
    have hchosenFit : chosen < 2 ^ n := by
      unfold chosen
      split
      · exact (Elem.evalNat_lt (p := p) hx).trans_le p.fits
      · exact (Elem.evalNat_lt (p := p) hy).trans_le p.fits
    have hword :
        (Word.eval ρ.bool { bitsLE := Vector.map LC.ofConst bits }).toNat =
          chosen := by
      simp [Word.eval, BitVec.toNat_ofFnLE, bits, Nat.ofBits_testBit,
        Nat.mod_eq_of_lt hchosenFit]
    have houtVal : out.intVal.eval ρ.int = (chosen : Nat) := by
      rw [U.Rel.intVal hout, hword]
    constructor
    · rcases hb with hb | hb
      · simp only [LC.eval_sub, hb, zero_mul, houtVal, chosen, if_pos hb]
        rw [← Elem.evalNat_cast (p := p) hx]
        ring
      · simp only [LC.eval_sub, hb, one_mul, houtVal, chosen,
          if_neg (by omega : ¬b.eval ρ.int = 0)]
        rw [← Elem.evalNat_cast (p := p) hx,
          ← Elem.evalNat_cast (p := p) hy]
    · mvcgen
      · exact hout.1
      · exact p.fits
      · rw [houtVal]
        unfold chosen
        split
        · exact_mod_cast Elem.evalNat_lt (p := p) hx
        · exact_mod_cast Elem.evalNat_lt (p := p) hy
      · constructor
        · exact ⟨hout.1, by
            rw [houtVal]
            unfold chosen
            split
            · exact_mod_cast Elem.evalNat_lt (p := p) hx
            · exact_mod_cast Elem.evalNat_lt (p := p) hy⟩
        · rcases hb with hb | hb
          · simp [houtVal, chosen, hb, Elem.evalNat_cast (p := p) hx]
          · simp [houtVal, chosen, hb]
            exact Elem.evalNat_cast (p := p) hy

theorem select_wf :
    WF.GadgetSpec
      (fun lv rv (l r : LC ℤ × Elem p × Elem p) =>
        WF.LCEq lv.int rv.int l.1 r.1 ∧
        Elem.WFRel lv rv l.2.1 r.2.1 ∧
        Elem.WFRel lv rv l.2.2 r.2.2)
      (fun z => select p z.1 z.2.1 z.2.2)
      (Elem.WFRel (p := p)) := by
  wfgen' using [U.fromWord_wf_rel, assertLt_wf]
    unfold [select, Elem.WFRel]
  case vc1 =>
    apply WF.lceq_of_common_realizes
    exact WF.common_realizes_of_hint (by assumption)
  case vc2 =>
    simp_all [WF.LCEq, U.WFRel, WF.ArgsEq, WF.evalArgs, LC.eval_sub]
  case vc3 =>
    simp_all [WF.LCEq, U.WFRel, WF.ArgsEq, WF.evalArgs]

/-! ## Equality and checked inverses

An inverse is most economical as an auxiliary witness: the circuit does not
need to reproduce Euclid's algorithm, because one modular multiplication and
one equality constraint certify it.  This is a proof-carrying witness, not a
trusted hint; a wrong inverse cannot satisfy the circuit.
-/

def assertEq (x y : Elem p) : Circuit Unit := do
  assertR1C 0 0 (x.val.intVal - y.val.intVal)

@[spec] theorem assertEq_sound {x y : Elem p} :
    ⦃⌜True⌝⦄ Sound.interp ρ (assertEq p x y)
    ⦃⇓ _ => ⌜x.evalNat ρ = y.evalNat ρ⌝⦄ := by
  mvcgen [assertEq]
  intro h
  simp only [LC.eval_zero, zero_mul, LC.eval_sub] at h
  unfold Elem.evalNat
  have he : x.val.intVal.eval ρ.int = y.val.intVal.eval ρ.int := by omega
  rw [he]

@[spec] theorem assertEq_complete {x y : Elem p}
    (heq : x.evalNat ρ = y.evalNat ρ)
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (assertEq p x y)
    ⦃⇓ _ => ⌜x.evalNat ρ = y.evalNat ρ⌝⦄ := by
  have hz : x.val.intVal.eval ρ.int - y.val.intVal.eval ρ.int = 0 := by
    rw [← Elem.evalNat_cast (p := p) hx,
      ← Elem.evalNat_cast (p := p) hy, heq]
    simp
  mvcgen [assertEq]
  constructor
  · simpa only [LC.eval_zero, zero_mul, LC.eval_sub] using hz.symm
  · exact heq

theorem assertEq_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Elem p × Elem p) =>
        Elem.WFRel lv rv l.1 r.1 ∧ Elem.WFRel lv rv l.2 r.2)
      (fun z => assertEq p z.1 z.2) (fun _ _ _ _ => True) := by
  unfold WF.GadgetSpec
  intro left right
  unfold assertEq
  apply WF.Rel.assertR1C_pure
  · simp [WF.LCEq]
  · simp [WF.LCEq]
  · intro lv rv h
    unfold Elem.WFRel U.WFRel at h
    unfold WF.LCEq at h ⊢
    simp only [LC.eval_sub]
    rw [h.1.1, h.2.1]
  · intro _ _ _
    trivial

def checkedInv (one x candidate : Elem p) : Circuit (Elem p) := do
  let product ← mul p x candidate
  assertEq p product one
  pure candidate

def InvSpec (ρ : WF.Valuation) (one x out : Elem p) : Prop :=
  out.Valid ρ ∧ (x.evalNat ρ * out.evalNat ρ) % p.modulus = one.evalNat ρ

@[spec] theorem checkedInv_sound {one x candidate : Elem p}
    (hone : one.Valid ρ) (hx : x.Valid ρ) (hc : candidate.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (checkedInv p one x candidate)
    ⦃⇓ out => ⌜InvSpec p ρ one x out⌝⦄ := by
  mvcgen [checkedInv, InvSpec]
  all_goals simp_all [MulSpec, InvSpec]

@[spec] theorem checkedInv_complete {one x candidate : Elem p}
    (hone : one.Valid ρ) (hx : x.Valid ρ) (hc : candidate.Valid ρ)
    (hinv : (x.evalNat ρ * candidate.evalNat ρ) % p.modulus =
      one.evalNat ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (checkedInv p one x candidate)
    ⦃⇓ out => ⌜InvSpec p ρ one x out⌝⦄ := by
  mvcgen [checkedInv, InvSpec]
  all_goals simp_all [MulSpec, InvSpec]

theorem checkedInv_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Elem p × Elem p × Elem p) =>
        Elem.WFRel lv rv l.1 r.1 ∧
        Elem.WFRel lv rv l.2.1 r.2.1 ∧ Elem.WFRel lv rv l.2.2 r.2.2)
      (fun z => checkedInv p z.1 z.2.1 z.2.2)
      (Elem.WFRel (p := p)) := by
  unfold WF.GadgetSpec
  intro left right
  unfold checkedInv
  apply WF.GadgetSpec.bind_rule (mul_wf p)
  · intro lv rv h
    exact ⟨h.2.1, h.2.2⟩
  · intro A productL productR hproduct
    unfold assertEq
    apply WF.Rel.assertR1C
    · intro _ _ _
      rfl
    · intro _ _ _
      rfl
    · intro lv rv hA
      have h := hproduct lv rv hA
      exact WF.eval_sub h.2.1 h.1.1.1
    · apply WF.Rel.pure
      intro lv rv hA
      exact (hproduct lv rv hA).1.2.2

end Freigen.F2Z.Examples.Modular
