import Freigen.F2Z.Examples.Modular

/-!
# P-256 field and projective-curve gadgets

This module is intentionally layered on the proved generic modular library.
Coordinates are canonical 256-bit integers modulo the P-256 base prime.  The
curve uses homogeneous projective coordinates `(X : Y : Z)`, representing
`(X/Z, Y/Z)` when `Z != 0` and infinity as `(0 : 1 : 0)`.

The addition law below is the complete Renes--Costello--Batina formula.  Using
one formula for ordinary addition, doubling, opposite points, and infinity is
slightly more expensive than an incomplete Jacobian formula, but it removes
all exceptional-case selectors from the scalar ladder.  In a verification
circuit that simplicity is both a soundness win and a good engineering trade.
-/

namespace Freigen.F2Z.Examples.P256

set_option maxRecDepth 10000

open Std.Do
open scoped Std.Do
open Modular

def baseModulus : Nat :=
  0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

def scalarModulus : Nat :=
  0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

def base : Params 256 where
  modulus := baseModulus
  bitsPositive := by omega
  positive := by native_decide
  fits := by native_decide
  lowerHalf := by native_decide

def scalar : Params 256 where
  modulus := scalarModulus
  bitsPositive := by omega
  positive := by native_decide
  fits := by native_decide
  lowerHalf := by native_decide

abbrev Fp := Elem base
abbrev Fn := Elem scalar

def fpConst (x : Nat) (h : x < baseModulus) : Fp :=
  Modular.ofNat base x (h.trans_le base.fits) h

def fnConst (x : Nat) (h : x < scalarModulus) : Fn :=
  Modular.ofNat scalar x (h.trans_le scalar.fits) h

def fnOne : Fn := fnConst 1 (by native_decide)

def zero : Fp := fpConst 0 (by native_decide)
def one : Fp := fpConst 1 (by native_decide)
def two : Fp := fpConst 2 (by native_decide)
def three : Fp := fpConst 3 (by native_decide)
def four : Fp := fpConst 4 (by native_decide)
def eight : Fp := fpConst 8 (by native_decide)

def curveA : Fp := fpConst (baseModulus - 3) (by native_decide)
def curveB : Fp := fpConst
  0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
  (by native_decide)

def curveB3 : Fp := fpConst
  ((3 * 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b) %
    baseModulus) (by native_decide)

def generatorX : Fp := fpConst
  0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
  (by native_decide)

def generatorY : Fp := fpConst
  0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
  (by native_decide)

structure Projective where
  X : Fp
  Y : Fp
  Z : Fp

namespace Projective

def Valid (P : Projective) (ρ : WF.Valuation) : Prop :=
  P.X.Valid ρ ∧ P.Y.Valid ρ ∧ P.Z.Valid ρ

def WFRel (lv rv : WF.Valuation) (P Q : Projective) : Prop :=
  Elem.WFRel lv rv P.X Q.X ∧ Elem.WFRel lv rv P.Y Q.Y ∧
    Elem.WFRel lv rv P.Z Q.Z

def infinity : Projective := ⟨zero, one, zero⟩
def generator : Projective := ⟨generatorX, generatorY, one⟩

theorem zero_valid : zero.Valid ρ :=
  Modular.ofNat_valid base 0 (by native_decide) (by native_decide)
theorem one_valid : one.Valid ρ :=
  Modular.ofNat_valid base 1 (by native_decide) (by native_decide)
theorem two_valid : two.Valid ρ :=
  Modular.ofNat_valid base 2 (by native_decide) (by native_decide)
theorem three_valid : three.Valid ρ :=
  Modular.ofNat_valid base 3 (by native_decide) (by native_decide)
theorem four_valid : four.Valid ρ :=
  Modular.ofNat_valid base 4 (by native_decide) (by native_decide)
theorem eight_valid : eight.Valid ρ :=
  Modular.ofNat_valid base 8 (by native_decide) (by native_decide)

theorem infinity_valid : infinity.Valid ρ :=
  ⟨zero_valid, one_valid, zero_valid⟩

theorem generator_valid : generator.Valid ρ :=
  ⟨Modular.ofNat_valid base _ (by native_decide) (by native_decide),
    Modular.ofNat_valid base _ (by native_decide) (by native_decide), one_valid⟩

/-- Complete homogeneous-projective addition for short Weierstrass curves.
`curveB3` is `3*b`; `curveA` is `-3`.  No exceptional input cases are
excluded. -/
def addComplete (P Q : Projective) : Circuit Projective := do
  let t0 ← mul base P.X Q.X
  let t1 ← mul base P.Y Q.Y
  let t2 ← mul base P.Z Q.Z
  let x1y1 ← add base P.X P.Y
  let x2y2 ← add base Q.X Q.Y
  let t3p ← mul base x1y1 x2y2
  let t0t1 ← add base t0 t1
  let t3 ← sub base t3p t0t1
  let x1z1 ← add base P.X P.Z
  let x2z2 ← add base Q.X Q.Z
  let t4p ← mul base x1z1 x2z2
  let t0t2 ← add base t0 t2
  let t4 ← sub base t4p t0t2
  let y1z1 ← add base P.Y P.Z
  let y2z2 ← add base Q.Y Q.Z
  let t5p ← mul base y1z1 y2z2
  let t1t2 ← add base t1 t2
  let t5 ← sub base t5p t1t2
  let z0 ← mul base curveA t4
  let x0 ← mul base curveB3 t2
  let z1 ← add base x0 z0
  let x1 ← sub base t1 z1
  let z2 ← add base t1 z1
  let y0 ← mul base x1 z2
  let t1d ← add base t0 t0
  let t1t ← add base t1d t0
  let t2a ← mul base curveA t2
  let t4b ← mul base curveB3 t4
  let t1a ← add base t1t t2a
  let t2s ← sub base t0 t2a
  let t2aa ← mul base curveA t2s
  let t4a ← add base t4b t2aa
  let t0m ← mul base t1a t4a
  let Y3 ← add base y0 t0m
  let t0x ← mul base t5 t4a
  let x2m ← mul base t3 x1
  let X3 ← sub base x2m t0x
  let t0z ← mul base t3 t1a
  let z3m ← mul base t5 z2
  let Z3 ← add base z3m t0z
  pure ⟨X3, Y3, Z3⟩

structure Value where
  X : Nat
  Y : Nat
  Z : Nat
  deriving DecidableEq

def eval (P : Projective) (ρ : WF.Valuation) : Value :=
  ⟨P.X.evalNat ρ, P.Y.evalNat ρ, P.Z.evalNat ρ⟩

private def fadd (x y : Nat) : Nat := (x + y) % baseModulus
private def fmul (x y : Nat) : Nat := (x * y) % baseModulus
private def fsub (x y : Nat) : Nat := (x + baseModulus - y) % baseModulus
private def aval : Nat := baseModulus - 3
private def b3val : Nat :=
  (3 * 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b) %
    baseModulus

/-- Pure coordinate model of `addComplete`.  Its deliberately line-for-line
shape makes the soundness theorem useful as an audit artifact. -/
def addModel (P Q : Value) : Value :=
  let t0 := fmul P.X Q.X
  let t1 := fmul P.Y Q.Y
  let t2 := fmul P.Z Q.Z
  let t3p := fmul (fadd P.X P.Y) (fadd Q.X Q.Y)
  let t3 := fsub t3p (fadd t0 t1)
  let t4p := fmul (fadd P.X P.Z) (fadd Q.X Q.Z)
  let t4 := fsub t4p (fadd t0 t2)
  let t5p := fmul (fadd P.Y P.Z) (fadd Q.Y Q.Z)
  let t5 := fsub t5p (fadd t1 t2)
  let z0 := fmul aval t4
  let x0 := fmul b3val t2
  let z1 := fadd x0 z0
  let x1 := fsub t1 z1
  let z2 := fadd t1 z1
  let y0 := fmul x1 z2
  let t1t := fadd (fadd t0 t0) t0
  let t2a := fmul aval t2
  let t4b := fmul b3val t4
  let t1a := fadd t1t t2a
  let t2aa := fmul (curveA.evalNat default) (fsub t0 t2a)
  let t4a := fadd t4b t2aa
  ⟨fsub (fmul t3 x1) (fmul t5 t4a),
    fadd y0 (fmul t1a t4a),
    fadd (fmul t5 z2) (fmul t3 t1a)⟩

def AddValueSpec (ρ : WF.Valuation) (P Q out : Projective) : Prop :=
  out.Valid ρ ∧ out.eval ρ = addModel (P.eval ρ) (Q.eval ρ)

def double (P : Projective) : Circuit Projective := addComplete P P

@[spec] theorem double_sound {P : Projective} (hP : P.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (double P)
    ⦃⇓ out => ⌜out.Valid ρ⌝⦄ := by
  unfold Valid at hP
  have hthree : three.Valid ρ := three_valid
  have hfour : four.Valid ρ := four_valid
  have height : eight.Valid ρ := eight_valid
  have ha : curveA.Valid ρ := Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  have hb3 : curveB3.Valid ρ := Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  mvcgen -trivial [double, addComplete, Valid]
  all_goals first
    | assumption
    | aesop (add simp [MulSpec, AddSpec, SubSpec])
    | (unfold Valid; aesop (add simp [MulSpec, AddSpec, SubSpec]))

@[spec] theorem double_complete {P : Projective} (hP : P.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (double P)
    ⦃⇓ out => ⌜out.Valid ρ⌝⦄ := by
  unfold Valid at hP
  have hthree : three.Valid ρ := three_valid
  have hfour : four.Valid ρ := four_valid
  have height : eight.Valid ρ := eight_valid
  have ha : curveA.Valid ρ := Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  have hb3 : curveB3.Valid ρ := Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  mvcgen -trivial [double, addComplete, Valid]
  all_goals first
    | assumption
    | aesop (add simp [MulSpec, AddSpec, SubSpec])
    | (unfold Valid; aesop (add simp [MulSpec, AddSpec, SubSpec]))

@[spec] theorem addComplete_sound {P Q : Projective}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (addComplete P Q)
    ⦃⇓ out => ⌜out.Valid ρ⌝⦄ := by
  unfold Valid at hP hQ
  have htwo : two.Valid ρ := two_valid
  have ha : curveA.Valid ρ := Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  have hb3 : curveB3.Valid ρ := Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  mvcgen -trivial [addComplete, Valid]
  all_goals first
    | assumption
    | aesop (add simp [MulSpec, AddSpec, SubSpec])
    | (unfold Valid; aesop (add simp [MulSpec, AddSpec, SubSpec]))

@[spec] theorem addComplete_complete {P Q : Projective}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (addComplete P Q)
    ⦃⇓ out => ⌜out.Valid ρ⌝⦄ := by
  unfold Valid at hP hQ
  have htwo : two.Valid ρ := two_valid
  have ha : curveA.Valid ρ := Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  have hb3 : curveB3.Valid ρ := Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  mvcgen -trivial [addComplete, Valid]
  all_goals first
    | assumption
    | aesop (add simp [MulSpec, AddSpec, SubSpec])
    | (unfold Valid; aesop (add simp [MulSpec, AddSpec, SubSpec]))

private theorem curveA_evalNat : curveA.evalNat ρ = aval := by
  simp [curveA, fpConst, Modular.ofNat, Elem.evalNat, U.intVal, aval]

private theorem curveB3_evalNat : curveB3.evalNat ρ = b3val := by
  simp [curveB3, fpConst, Modular.ofNat, Elem.evalNat, U.intVal, b3val]

theorem addComplete_sound_value {P Q : Projective}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (addComplete P Q)
    ⦃⇓ out => ⌜AddValueSpec ρ P Q out⌝⦄ := by
  unfold Valid at hP hQ
  have ha : curveA.Valid ρ :=
    Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  have hb3 : curveB3.Valid ρ :=
    Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  mvcgen -trivial [addComplete, AddValueSpec]
  all_goals simp_all [MulSpec, AddSpec, SubSpec, eval, addModel,
    fmul, fadd, fsub, curveA_evalNat, curveB3_evalNat]

theorem addComplete_complete_value {P Q : Projective}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (addComplete P Q)
    ⦃⇓ out => ⌜AddValueSpec ρ P Q out⌝⦄ := by
  unfold Valid at hP hQ
  have ha : curveA.Valid ρ :=
    Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  have hb3 : curveB3.Valid ρ :=
    Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  mvcgen -trivial [addComplete, AddValueSpec]
  all_goals simp_all [MulSpec, AddSpec, SubSpec, eval, addModel,
    fmul, fadd, fsub, curveA_evalNat, curveB3_evalNat]

theorem addComplete_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Projective × Projective) =>
        WFRel lv rv l.1 r.1 ∧ WFRel lv rv l.2 r.2)
      (fun z => addComplete z.1 z.2) WFRel := by
  wfgen' using [Modular.mul_wf, Modular.add_wf, Modular.sub_wf]
    unfold [addComplete, WFRel]

theorem double_wf : WF.GadgetSpec WFRel double WFRel := by
  unfold WF.GadgetSpec double
  intro left right
  apply Modular.WF.Rel.strengthen
    (addComplete_wf (left, left) (right, right))
  intro lv rv h
  exact ⟨h, h⟩

/-- Coordinate-wise whole-field selection.  Each coordinate uses the generic
one-R1C integer mux from `Modular.select`; no per-bit multiplication array is
allocated. -/
def select (b : LC ℤ) (P Q : Projective) : Circuit Projective := do
  let X ← Modular.select base b P.X Q.X
  let Y ← Modular.select base b P.Y Q.Y
  let Z ← Modular.select base b P.Z Q.Z
  pure ⟨X, Y, Z⟩

@[spec] theorem select_sound {b : LC ℤ} {P Q : Projective}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (select b P Q)
    ⦃⇓ out => ⌜out.Valid ρ⌝⦄ := by
  unfold Valid at hP hQ
  mvcgen -trivial [select, Valid]
  all_goals aesop (add simp [Modular.SelectSpec])

@[spec] theorem select_complete {b : LC ℤ} {P Q : Projective}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ)
    (hb : b.eval ρ.int = 0 ∨ b.eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Complete.interp ρ (select b P Q)
    ⦃⇓ out => ⌜out.Valid ρ⌝⦄ := by
  unfold Valid at hP hQ
  mvcgen -trivial [select, Valid]
  all_goals first
    | exact hb
    | aesop (add simp [Modular.SelectSpec])

theorem select_wf :
    WF.GadgetSpec
      (fun lv rv (l r : LC ℤ × Projective × Projective) =>
        WF.LCEq lv.int rv.int l.1 r.1 ∧
        WFRel lv rv l.2.1 r.2.1 ∧ WFRel lv rv l.2.2 r.2.2)
      (fun z => select z.1 z.2.1 z.2.2) WFRel := by
  wfgen' using [Modular.select_wf] unfold [select, WFRel]

structure LadderState where
  acc : Projective
  power : Projective

namespace LadderState

def Valid (s : LadderState) (ρ : WF.Valuation) : Prop :=
  s.acc.Valid ρ ∧ s.power.Valid ρ

def WFRel (lv rv : WF.Valuation) (l r : LadderState) : Prop :=
  Projective.WFRel lv rv l.acc r.acc ∧
    Projective.WFRel lv rv l.power r.power

end LadderState

/-- Little-endian double-and-add.  Completeness of the ladder relies only on
the complete group law; even scalar zero and intermediate infinity require no
special treatment. -/
def scalarMul (k : Fn) (P : Projective) : Circuit Projective := do
  let mut state : LadderState := ⟨infinity, P⟩
  for h:i in [0:256] do
    let bit ← f2z k.val.bits.bitsLE[i]
    let sum ← addComplete state.acc state.power
    let acc ← select bit state.acc sum
    let power ← double state.power
    state := ⟨acc, power⟩
  pure state.acc

private theorem f2z_isBit {b : LC Bool} {z : LC ℤ}
    (h : z.eval ρ.int = (b.eval ρ.bool).toInt) :
    z.eval ρ.int = 0 ∨ z.eval ρ.int = 1 := by
  cases hb : b.eval ρ.bool <;> simp [hb] at h <;> omega

@[spec] theorem scalarMul_sound {k : Fn} {P : Projective}
    (hk : k.Valid ρ) (hP : P.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (scalarMul k P)
    ⦃⇓ out => ⌜out.Valid ρ⌝⦄ := by
  mvcgen -trivial [scalarMul, LadderState.Valid] invariants
  · ⇓⟨_, state⟩ => ⌜state.Valid ρ⌝
  all_goals first
    | exact ⟨infinity_valid, hP⟩
    | assumption
    | aesop (add simp [LadderState.Valid])

@[spec] theorem scalarMul_complete {k : Fn} {P : Projective}
    (hk : k.Valid ρ) (hP : P.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (scalarMul k P)
    ⦃⇓ out => ⌜out.Valid ρ⌝⦄ := by
  mvcgen -trivial [scalarMul, LadderState.Valid] invariants
  · ⇓⟨_, state⟩ => ⌜state.Valid ρ⌝
  all_goals first
    | exact ⟨infinity_valid, hP⟩
    | assumption
    | (apply f2z_isBit; assumption)
    | aesop (add simp [LadderState.Valid])

theorem scalarMul_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Fn × Projective) =>
        Elem.WFRel lv rv l.1 r.1 ∧ Projective.WFRel lv rv l.2 r.2)
      (fun z => scalarMul z.1 z.2) Projective.WFRel := by
  wfgen' using [Projective.addComplete_wf, Projective.select_wf,
    Projective.double_wf] unfold [scalarMul, LadderState.WFRel]
  case inv1 =>
    exact fun _ _ _ _ => LadderState.WFRel
  all_goals aesop (add simp [LadderState.WFRel, Projective.WFRel,
    Elem.WFRel, U.WFRel, WF.LCEq])

/-- Check an affine public key against `y² = x³ - 3x + b`. -/
def assertOnCurve (x y : Fp) : Circuit Unit := do
  let y2 ← mul base y y
  let x2 ← mul base x x
  let x3 ← mul base x2 x
  let ax ← mul base curveA x
  let x3a ← add base x3 ax
  let rhs ← add base x3a curveB
  Modular.assertEq base y2 rhs

def OnCurveSpec (ρ : WF.Valuation) (x y : Fp) : Prop :=
  (y.evalNat ρ * y.evalNat ρ) % baseModulus =
    ((((x.evalNat ρ * x.evalNat ρ) % baseModulus) * x.evalNat ρ) %
      baseModulus +
      ((curveA.evalNat ρ * x.evalNat ρ) % baseModulus) +
      curveB.evalNat ρ) % baseModulus

@[spec] theorem assertOnCurve_sound {x y : Fp}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (assertOnCurve x y)
    ⦃⇓ _ => ⌜OnCurveSpec ρ x y⌝⦄ := by
  have ha : curveA.Valid ρ :=
    Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  have hb : curveB.Valid ρ :=
    Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  mvcgen [assertOnCurve, OnCurveSpec]
  omega

@[spec] theorem assertOnCurve_complete {x y : Fp}
    (hx : x.Valid ρ) (hy : y.Valid ρ) (hon : OnCurveSpec ρ x y) :
    ⦃⌜True⌝⦄ Complete.interp ρ (assertOnCurve x y)
    ⦃⇓ _ => ⌜OnCurveSpec ρ x y⌝⦄ := by
  have ha : curveA.Valid ρ :=
    Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  have hb : curveB.Valid ρ :=
    Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  mvcgen [assertOnCurve, OnCurveSpec]
  all_goals omega

theorem assertOnCurve_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Fp × Fp) =>
        Elem.WFRel lv rv l.1 r.1 ∧ Elem.WFRel lv rv l.2 r.2)
      (fun z => assertOnCurve z.1 z.2) (fun _ _ _ _ => True) := by
  wfgen' using [Modular.mul_wf, Modular.add_wf, Modular.assertEq_wf]
    unfold [assertOnCurve]

end Projective

end Freigen.F2Z.Examples.P256
