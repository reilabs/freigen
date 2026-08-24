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

@[simp] theorem base_modulus_eq : base.modulus = baseModulus := rfl

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

def mulByA (x : Fp) : Circuit Fp := mul base curveA x

def mulByB3 (x : Fp) : Circuit Fp := mul base curveB3 x

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

structure AddPrelude where
  t0 : Fp
  t1 : Fp
  t2 : Fp
  t3 : Fp
  t4 : Fp
  t5 : Fp

namespace AddPrelude

def Valid (s : AddPrelude) (ρ : WF.Valuation) : Prop :=
  s.t0.Valid ρ ∧ s.t1.Valid ρ ∧ s.t2.Valid ρ ∧
    s.t3.Valid ρ ∧ s.t4.Valid ρ ∧ s.t5.Valid ρ

def WFRel (lv rv : WF.Valuation) (l r : AddPrelude) : Prop :=
  Elem.WFRel lv rv l.t0 r.t0 ∧ Elem.WFRel lv rv l.t1 r.t1 ∧
    Elem.WFRel lv rv l.t2 r.t2 ∧ Elem.WFRel lv rv l.t3 r.t3 ∧
    Elem.WFRel lv rv l.t4 r.t4 ∧ Elem.WFRel lv rv l.t5 r.t5

end AddPrelude

structure AddCore where
  t3 : Fp
  t5 : Fp
  x1 : Fp
  z2 : Fp
  y0 : Fp
  t1a : Fp
  t4a : Fp

namespace AddCore

def Valid (s : AddCore) (ρ : WF.Valuation) : Prop :=
  s.t3.Valid ρ ∧ s.t5.Valid ρ ∧ s.x1.Valid ρ ∧ s.z2.Valid ρ ∧
    s.y0.Valid ρ ∧ s.t1a.Valid ρ ∧ s.t4a.Valid ρ

def WFRel (lv rv : WF.Valuation) (l r : AddCore) : Prop :=
  Elem.WFRel lv rv l.t3 r.t3 ∧ Elem.WFRel lv rv l.t5 r.t5 ∧
    Elem.WFRel lv rv l.x1 r.x1 ∧ Elem.WFRel lv rv l.z2 r.z2 ∧
    Elem.WFRel lv rv l.y0 r.y0 ∧ Elem.WFRel lv rv l.t1a r.t1a ∧
    Elem.WFRel lv rv l.t4a r.t4a

end AddCore

def addPrelude (P Q : Projective) : Circuit AddPrelude := do
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
  pure ⟨t0, t1, t2, t3, t4, t5⟩

def addCore (s : AddPrelude) : Circuit AddCore := do
  let t0 := s.t0
  let t1 := s.t1
  let t2 := s.t2
  let t3 := s.t3
  let t4 := s.t4
  let t5 := s.t5
  let z0 ← mulByA t4
  let x0 ← mulByB3 t2
  let z1 ← add base x0 z0
  let x1 ← sub base t1 z1
  let z2 ← add base t1 z1
  let y0 ← mul base x1 z2
  let t1d ← add base t0 t0
  let t1t ← add base t1d t0
  let t2a ← mulByA t2
  let t4b ← mulByB3 t4
  let t1a ← add base t1t t2a
  let t2s ← sub base t0 t2a
  let t2aa ← mulByA t2s
  let t4a ← add base t4b t2aa
  pure ⟨t3, t5, x1, z2, y0, t1a, t4a⟩

def addFinish (s : AddCore) : Circuit Projective := do
  let t3 := s.t3
  let t5 := s.t5
  let x1 := s.x1
  let z2 := s.z2
  let y0 := s.y0
  let t1a := s.t1a
  let t4a := s.t4a
  let t0m ← mul base t1a t4a
  let Y3 ← add base y0 t0m
  let t0x ← mul base t5 t4a
  let x2m ← mul base t3 x1
  let X3 ← sub base x2m t0x
  let t0z ← mul base t3 t1a
  let z3m ← mul base t5 z2
  let Z3 ← add base z3m t0z
  pure ⟨X3, Y3, Z3⟩

/-- Complete homogeneous-projective addition for short Weierstrass curves.
`curveB3` is `3*b`; `curveA` is `-3`.  No exceptional input cases are
excluded. -/
def addComplete (P Q : Projective) : Circuit Projective := do
  let prelude ← addPrelude P Q
  let core ← addCore prelude
  addFinish core

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

structure PreludeValue where
  t0 : Nat
  t1 : Nat
  t2 : Nat
  t3 : Nat
  t4 : Nat
  t5 : Nat
  deriving DecidableEq

structure CoreValue where
  t3 : Nat
  t5 : Nat
  x1 : Nat
  z2 : Nat
  y0 : Nat
  t1a : Nat
  t4a : Nat
  deriving DecidableEq

def AddPrelude.eval (s : AddPrelude) (ρ : WF.Valuation) : PreludeValue :=
  ⟨s.t0.evalNat ρ, s.t1.evalNat ρ, s.t2.evalNat ρ,
    s.t3.evalNat ρ, s.t4.evalNat ρ, s.t5.evalNat ρ⟩

def AddCore.eval (s : AddCore) (ρ : WF.Valuation) : CoreValue :=
  ⟨s.t3.evalNat ρ, s.t5.evalNat ρ, s.x1.evalNat ρ, s.z2.evalNat ρ,
    s.y0.evalNat ρ, s.t1a.evalNat ρ, s.t4a.evalNat ρ⟩

def preludeModel (P Q : Value) : PreludeValue :=
  let t0 := fmul P.X Q.X
  let t1 := fmul P.Y Q.Y
  let t2 := fmul P.Z Q.Z
  let t3p := fmul (fadd P.X P.Y) (fadd Q.X Q.Y)
  let t3 := fsub t3p (fadd t0 t1)
  let t4p := fmul (fadd P.X P.Z) (fadd Q.X Q.Z)
  let t4 := fsub t4p (fadd t0 t2)
  let t5p := fmul (fadd P.Y P.Z) (fadd Q.Y Q.Z)
  let t5 := fsub t5p (fadd t1 t2)
  ⟨t0, t1, t2, t3, t4, t5⟩

def coreModel (s : PreludeValue) : CoreValue :=
  let z0 := fmul aval s.t4
  let x0 := fmul b3val s.t2
  let z1 := fadd x0 z0
  let x1 := fsub s.t1 z1
  let z2 := fadd s.t1 z1
  let y0 := fmul x1 z2
  let t1t := fadd (fadd s.t0 s.t0) s.t0
  let t2a := fmul aval s.t2
  let t4b := fmul b3val s.t4
  let t1a := fadd t1t t2a
  let t2aa := fmul aval (fsub s.t0 t2a)
  let t4a := fadd t4b t2aa
  ⟨s.t3, s.t5, x1, z2, y0, t1a, t4a⟩

def finishModel (s : CoreValue) : Value :=
  ⟨fsub (fmul s.t3 s.x1) (fmul s.t5 s.t4a),
    fadd s.y0 (fmul s.t1a s.t4a),
    fadd (fmul s.t5 s.z2) (fmul s.t3 s.t1a)⟩

/-- Pure coordinate model of `addComplete`, split along the circuit phases so
the proof kernel can share intermediate contracts. -/
def addModel (P Q : Value) : Value :=
  finishModel (coreModel (preludeModel P Q))

def AddValueSpec (ρ : WF.Valuation) (P Q out : Projective) : Prop :=
  out.Valid ρ ∧ out.eval ρ = addModel (P.eval ρ) (Q.eval ρ)

def double (P : Projective) : Circuit Projective := addComplete P P

private theorem curveA_evalNat : curveA.evalNat ρ = aval := by
  exact Modular.ofNat_evalNat base _ (by native_decide) (by native_decide)

private theorem curveB3_evalNat : curveB3.evalNat ρ = b3val := by
  exact Modular.ofNat_evalNat base _ (by native_decide) (by native_decide)

def MulByASpec (ρ : WF.Valuation) (x out : Fp) : Prop :=
  out.Valid ρ ∧ out.evalNat ρ = fmul aval (x.evalNat ρ)

def MulByB3Spec (ρ : WF.Valuation) (x out : Fp) : Prop :=
  out.Valid ρ ∧ out.evalNat ρ = fmul b3val (x.evalNat ρ)

@[spec] theorem mulByA_sound {x : Fp} (hx : x.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (mulByA x)
    ⦃⇓ out => ⌜MulByASpec ρ x out⌝⦄ := by
  have ha : curveA.Valid ρ :=
    Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  simpa only [mulByA, MulByASpec, MulSpec, fmul, base_modulus_eq,
    curveA_evalNat] using Modular.mul_sound base ha hx

@[spec] theorem mulByA_complete {x : Fp} (hx : x.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (mulByA x)
    ⦃⇓ out => ⌜MulByASpec ρ x out⌝⦄ := by
  have ha : curveA.Valid ρ :=
    Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  simpa only [mulByA, MulByASpec, MulSpec, fmul, base_modulus_eq,
    curveA_evalNat] using Modular.mul_complete base ha hx

@[spec] theorem mulByB3_sound {x : Fp} (hx : x.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (mulByB3 x)
    ⦃⇓ out => ⌜MulByB3Spec ρ x out⌝⦄ := by
  have hb3 : curveB3.Valid ρ :=
    Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  simpa only [mulByB3, MulByB3Spec, MulSpec, fmul, base_modulus_eq,
    curveB3_evalNat] using Modular.mul_sound base hb3 hx

@[spec] theorem mulByB3_complete {x : Fp} (hx : x.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (mulByB3 x)
    ⦃⇓ out => ⌜MulByB3Spec ρ x out⌝⦄ := by
  have hb3 : curveB3.Valid ρ :=
    Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  simpa only [mulByB3, MulByB3Spec, MulSpec, fmul, base_modulus_eq,
    curveB3_evalNat] using Modular.mul_complete base hb3 hx

def PreludeSpec (ρ : WF.Valuation) (P Q : Projective)
    (out : AddPrelude) : Prop :=
  out.Valid ρ ∧ out.eval ρ = preludeModel (P.eval ρ) (Q.eval ρ)

def CoreSpec (ρ : WF.Valuation) (s : AddPrelude) (out : AddCore) : Prop :=
  out.Valid ρ ∧ out.eval ρ = coreModel (s.eval ρ)

def FinishSpec (ρ : WF.Valuation) (s : AddCore) (out : Projective) : Prop :=
  out.Valid ρ ∧ out.eval ρ = finishModel (s.eval ρ)

@[spec] theorem addPrelude_sound {P Q : Projective}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (addPrelude P Q)
    ⦃⇓ out => ⌜PreludeSpec ρ P Q out⌝⦄ := by
  unfold Valid at hP hQ
  mvcgen -trivial [addPrelude, PreludeSpec]
  all_goals simp_all only [PreludeSpec, MulSpec, AddSpec, SubSpec,
    AddPrelude.Valid, AddPrelude.eval, eval, preludeModel, fmul, fadd, fsub,
    base_modulus_eq, true_and]

@[spec] theorem addPrelude_complete {P Q : Projective}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (addPrelude P Q)
    ⦃⇓ out => ⌜PreludeSpec ρ P Q out⌝⦄ := by
  unfold Valid at hP hQ
  mvcgen -trivial [addPrelude, PreludeSpec]
  all_goals simp_all only [PreludeSpec, MulSpec, AddSpec, SubSpec,
    AddPrelude.Valid, AddPrelude.eval, eval, preludeModel, fmul, fadd, fsub,
    base_modulus_eq, true_and]

@[spec] theorem addCore_sound {s : AddPrelude} (hs : s.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (addCore s)
    ⦃⇓ out => ⌜CoreSpec ρ s out⌝⦄ := by
  unfold AddPrelude.Valid at hs
  mvcgen -trivial [addCore, CoreSpec]
  all_goals simp_all only [CoreSpec, MulByASpec, MulByB3Spec, MulSpec,
    AddSpec, SubSpec, AddCore.Valid,
    AddPrelude.eval, AddCore.eval, coreModel, fmul, fadd, fsub,
    base_modulus_eq, true_and]

@[spec] theorem addCore_complete {s : AddPrelude} (hs : s.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (addCore s)
    ⦃⇓ out => ⌜CoreSpec ρ s out⌝⦄ := by
  unfold AddPrelude.Valid at hs
  mvcgen -trivial [addCore, CoreSpec]
  all_goals simp_all only [CoreSpec, MulByASpec, MulByB3Spec, MulSpec,
    AddSpec, SubSpec, AddCore.Valid,
    AddPrelude.eval, AddCore.eval, coreModel, fmul, fadd, fsub,
    base_modulus_eq, true_and]

@[spec] theorem addFinish_sound {s : AddCore} (hs : s.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (addFinish s)
    ⦃⇓ out => ⌜FinishSpec ρ s out⌝⦄ := by
  unfold AddCore.Valid at hs
  mvcgen -trivial [addFinish, FinishSpec]
  all_goals simp_all only [FinishSpec, MulSpec, AddSpec, SubSpec, Valid,
    AddCore.eval, eval, finishModel, fmul, fadd, fsub, base_modulus_eq,
    true_and]

@[spec] theorem addFinish_complete {s : AddCore} (hs : s.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (addFinish s)
    ⦃⇓ out => ⌜FinishSpec ρ s out⌝⦄ := by
  unfold AddCore.Valid at hs
  mvcgen -trivial [addFinish, FinishSpec]
  all_goals simp_all only [FinishSpec, MulSpec, AddSpec, SubSpec, Valid,
    AddCore.eval, eval, finishModel, fmul, fadd, fsub, base_modulus_eq,
    true_and]

theorem addComplete_sound_value {P Q : Projective}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (addComplete P Q)
    ⦃⇓ out => ⌜AddValueSpec ρ P Q out⌝⦄ := by
  mvcgen -trivial [addComplete, AddValueSpec]
  all_goals simp_all only [AddValueSpec, PreludeSpec, CoreSpec, FinishSpec,
    addModel, true_and, implies_true]

theorem addComplete_complete_value {P Q : Projective}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (addComplete P Q)
    ⦃⇓ out => ⌜AddValueSpec ρ P Q out⌝⦄ := by
  mvcgen -trivial [addComplete, AddValueSpec]
  all_goals simp_all only [AddValueSpec, PreludeSpec, CoreSpec, FinishSpec,
    addModel, true_and, implies_true]

@[spec] theorem addComplete_sound {P Q : Projective}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (addComplete P Q)
    ⦃⇓ out => ⌜out.Valid ρ⌝⦄ := by
  apply Triple.iff_conseq.mp (addComplete_sound_value hP hQ) (by simp)
  simp only [PostCond.entails, SPred.entails_nil]
  exact ⟨fun _ h => h.1, ExceptConds.entails.refl _⟩

@[spec] theorem addComplete_complete {P Q : Projective}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (addComplete P Q)
    ⦃⇓ out => ⌜out.Valid ρ⌝⦄ := by
  apply Triple.iff_conseq.mp (addComplete_complete_value hP hQ) (by simp)
  simp only [PostCond.entails, SPred.entails_nil]
  exact ⟨fun _ h => h.1, ExceptConds.entails.refl _⟩

@[spec] theorem double_sound {P : Projective} (hP : P.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (double P)
    ⦃⇓ out => ⌜out.Valid ρ⌝⦄ := by
  simpa only [double] using addComplete_sound hP hP

@[spec] theorem double_complete {P : Projective} (hP : P.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (double P)
    ⦃⇓ out => ⌜out.Valid ρ⌝⦄ := by
  simpa only [double] using addComplete_complete hP hP

private theorem fpConst_wf (x : Nat) (hx : x < baseModulus)
    (lv rv : WF.Valuation) :
    Elem.WFRel lv rv (fpConst x hx) (fpConst x hx) := by
  unfold fpConst Modular.ofNat Elem.WFRel
  exact U.wfRel_bitVec lv rv _

private theorem curveA_wf (lv rv : WF.Valuation) :
    Elem.WFRel lv rv curveA curveA := by
  exact fpConst_wf _ _ lv rv

private theorem curveB3_wf (lv rv : WF.Valuation) :
    Elem.WFRel lv rv curveB3 curveB3 := by
  exact fpConst_wf _ _ lv rv

theorem mulByA_wf :
    WF.GadgetSpec (Elem.WFRel (p := base)) mulByA
      (Elem.WFRel (p := base)) := by
  unfold WF.GadgetSpec mulByA
  intro left right
  apply Modular.WF.Rel.strengthen
    (Modular.mul_wf base (curveA, left) (curveA, right))
  intro lv rv h
  exact ⟨curveA_wf lv rv, h⟩

theorem mulByB3_wf :
    WF.GadgetSpec (Elem.WFRel (p := base)) mulByB3
      (Elem.WFRel (p := base)) := by
  unfold WF.GadgetSpec mulByB3
  intro left right
  apply Modular.WF.Rel.strengthen
    (Modular.mul_wf base (curveB3, left) (curveB3, right))
  intro lv rv h
  exact ⟨curveB3_wf lv rv, h⟩

private theorem curveB_wf (lv rv : WF.Valuation) :
    Elem.WFRel lv rv curveB curveB := by
  exact fpConst_wf _ _ lv rv

theorem addPrelude_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Projective × Projective) =>
        WFRel lv rv l.1 r.1 ∧ WFRel lv rv l.2 r.2)
      (fun z => addPrelude z.1 z.2) AddPrelude.WFRel := by
  wfgen_steps' using [Modular.mul_wf, Modular.add_wf, Modular.sub_wf]
    unfold [addPrelude, WFRel, AddPrelude.WFRel]
  all_goals grind only

theorem addCore_wf :
    WF.GadgetSpec AddPrelude.WFRel addCore AddCore.WFRel := by
  wfgen_steps' using [mulByA_wf, mulByB3_wf, Modular.mul_wf,
    Modular.add_wf, Modular.sub_wf]
    unfold [addCore, AddPrelude.WFRel, AddCore.WFRel]
  all_goals grind only

theorem addFinish_wf :
    WF.GadgetSpec AddCore.WFRel addFinish WFRel := by
  wfgen_steps' using [Modular.mul_wf, Modular.add_wf, Modular.sub_wf]
    unfold [addFinish, AddCore.WFRel, WFRel]
  all_goals grind only

theorem addComplete_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Projective × Projective) =>
        WFRel lv rv l.1 r.1 ∧ WFRel lv rv l.2 r.2)
      (fun z => addComplete z.1 z.2) WFRel := by
  wfgen_steps' using [addPrelude_wf, addCore_wf, addFinish_wf]
    unfold [addComplete]
  all_goals grind only

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
  all_goals simp_all only [Modular.SelectSpec, Valid, true_and]

@[spec] theorem select_complete {b : LC ℤ} {P Q : Projective}
    (hP : P.Valid ρ) (hQ : Q.Valid ρ)
    (hb : b.eval ρ.int = 0 ∨ b.eval ρ.int = 1) :
    ⦃⌜True⌝⦄ Complete.interp ρ (select b P Q)
    ⦃⇓ out => ⌜out.Valid ρ⌝⦄ := by
  unfold Valid at hP hQ
  mvcgen -trivial [select, Valid]
  all_goals first
    | exact hb
    | simp_all only [Modular.SelectSpec, Valid, true_and]

theorem select_wf :
    WF.GadgetSpec
      (fun lv rv (l r : LC ℤ × Projective × Projective) =>
        WF.LCEq lv.int rv.int l.1 r.1 ∧
        WFRel lv rv l.2.1 r.2.1 ∧ WFRel lv rv l.2.2 r.2.2)
      (fun z => select z.1 z.2.1 z.2.2) WFRel := by
  wfgen_steps' using [Modular.select_wf] unfold [select, WFRel]
  all_goals grind only

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

private theorem range_mem_256 {i n : Nat} (hn : n ≤ 256)
    (hi : i ∈ [:n]) : i ∈ [:256] :=
  ⟨hi.1, lt_of_lt_of_le hi.2.1 hn, hi.2.2⟩

def ladderStep (k : Fn) (i : Nat) (hi : i ∈ [:256])
    (state : LadderState) : Circuit LadderState := do
  let bit ← f2z k.val.bits.bitsLE[i]
  let sum ← addComplete state.acc state.power
  let acc ← select bit state.acc sum
  let power ← double state.power
  pure ⟨acc, power⟩

def scalarLoop (k : Fn) (n : Nat) (hn : n ≤ 256)
    (initial : LadderState) : Circuit LadderState :=
  WF.foldRange [:n] initial fun i hi state =>
    ladderStep k i (range_mem_256 hn hi) state

/-- Little-endian double-and-add.  Completeness of the ladder relies only on
the complete group law; even scalar zero and intermediate infinity require no
special treatment. -/
def scalarMul (k : Fn) (P : Projective) : Circuit Projective := do
  let state ← scalarLoop k 256 (by omega) ⟨infinity, P⟩
  pure state.acc

private theorem f2z_isBit {ρ : WF.Valuation} {b : LC Bool} {z : LC ℤ}
    (h : z.eval ρ.int = (b.eval ρ.bool).toInt) :
    z.eval ρ.int = 0 ∨ z.eval ρ.int = 1 := by
  cases hb : b.eval ρ.bool <;> simp [hb] at h <;> omega

@[spec] theorem ladderStep_sound {k : Fn} {i : Nat} {hi : i ∈ [:256]}
    {state : LadderState} (_hk : k.Valid ρ) (hstate : state.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (ladderStep k i hi state)
    ⦃⇓ out => ⌜out.Valid ρ⌝⦄ := by
  mvcgen -trivial [ladderStep, LadderState.Valid]
  all_goals grind [LadderState.Valid]

@[spec] theorem ladderStep_complete {k : Fn} {i : Nat} {hi : i ∈ [:256]}
    {state : LadderState} (_hk : k.Valid ρ) (hstate : state.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (ladderStep k i hi state)
    ⦃⇓ out => ⌜out.Valid ρ⌝⦄ := by
  mvcgen -trivial [ladderStep, LadderState.Valid]
  all_goals first
    | (apply f2z_isBit; assumption)
    | grind [LadderState.Valid]

@[spec] theorem scalarLoop_sound {k : Fn} {n : Nat} {hn : n ≤ 256}
    {initial : LadderState} (hk : k.Valid ρ) (hinit : initial.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (scalarLoop k n hn initial)
    ⦃⇓ out => ⌜out.Valid ρ⌝⦄ := by
  mvcgen -trivial [scalarLoop, WF.foldRange, LadderState.Valid] invariants
  · ⇓⟨_, state⟩ => ⌜state.Valid ρ⌝
  all_goals grind [LadderState.Valid]

@[spec] theorem scalarLoop_complete {k : Fn} {n : Nat} {hn : n ≤ 256}
    {initial : LadderState} (hk : k.Valid ρ) (hinit : initial.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (scalarLoop k n hn initial)
    ⦃⇓ out => ⌜out.Valid ρ⌝⦄ := by
  mvcgen -trivial [scalarLoop, WF.foldRange, LadderState.Valid] invariants
  · ⇓⟨_, state⟩ => ⌜state.Valid ρ⌝
  all_goals grind [LadderState.Valid]

@[spec] theorem scalarMul_sound {k : Fn} {P : Projective}
    (hk : k.Valid ρ) (hP : P.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (scalarMul k P)
    ⦃⇓ out => ⌜out.Valid ρ⌝⦄ := by
  mvcgen -trivial [scalarMul, LadderState.Valid]
  all_goals first
    | exact ⟨infinity_valid, hP⟩
    | grind [LadderState.Valid]

@[spec] theorem scalarMul_complete {k : Fn} {P : Projective}
    (hk : k.Valid ρ) (hP : P.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (scalarMul k P)
    ⦃⇓ out => ⌜out.Valid ρ⌝⦄ := by
  mvcgen -trivial [scalarMul, LadderState.Valid]
  all_goals first
    | exact ⟨infinity_valid, hP⟩
    | grind [LadderState.Valid]

private theorem elem_bit_eval_eq {p : Params n} {lv rv : WF.Valuation}
    {l r : Elem p} (h : Elem.WFRel lv rv l r) (i : Fin n) :
    l.val.bits.bitsLE[i].eval lv.bool =
      r.val.bits.bitsLE[i].eval rv.bool := by
  exact h.2 i

private theorem infinity_wf (lv rv : WF.Valuation) :
    WFRel lv rv infinity infinity := by
  unfold infinity zero one WFRel
  exact ⟨fpConst_wf 0 (by native_decide) lv rv,
    fpConst_wf 1 (by native_decide) lv rv,
    fpConst_wf 0 (by native_decide) lv rv⟩

theorem ladderStep_wf (i : Nat) (hi : i ∈ [:256]) :
    WF.GadgetSpec
      (fun lv rv (l r : Fn × LadderState) =>
        Elem.WFRel lv rv l.1 r.1 ∧ LadderState.WFRel lv rv l.2 r.2)
      (fun z => ladderStep z.1 i hi z.2) LadderState.WFRel := by
  wfgen_steps' using [Projective.addComplete_wf, Projective.select_wf,
    Projective.double_wf] unfold [ladderStep, LadderState.WFRel]
  case vc9 =>
    unfold WF.LCEq
    apply elem_bit_eval_eq
    grind only
  case vc6 =>
    unfold WF.LCEq
    rename_i outLBit outRBit hrel
    have hk : Elem.WFRel leftVal rightVal left.1 right.1 := by
      grind only
    have hbit := elem_bit_eval_eq hk
      (⟨i, by grind⟩ : Fin 256)
    have hbitInt :
        (left.1.val.bits.bitsLE[i].eval leftVal.bool).toInt =
          (right.1.val.bits.bitsLE[i].eval rightVal.bool).toInt := by
      simpa only [Fin.getElem_fin] using congrArg Bool.toInt hbit
    exact hrel.1.2.1.trans (hbitInt.trans hrel.1.2.2.symm)
  all_goals grind only [LadderState.WFRel, Projective.WFRel]

theorem scalarLoop_wf (n : Nat) (hn : n ≤ 256) :
    WF.GadgetSpec
      (fun lv rv (l r : Fn × LadderState) =>
        Elem.WFRel lv rv l.1 r.1 ∧ LadderState.WFRel lv rv l.2 r.2)
      (fun z => scalarLoop z.1 n hn z.2) LadderState.WFRel := by
  unfold WF.GadgetSpec scalarLoop
  intro left right
  let I : WF.Post LadderState := fun lv rv leftState rightState =>
      Elem.WFRel lv rv left.1 right.1 ∧
        LadderState.WFRel lv rv leftState rightState
  have hloop : WF.Rel I
      (fun lv rv =>
      Elem.WFRel lv rv left.1 right.1 ∧
        LadderState.WFRel lv rv left.2 right.2)
      (WF.foldRange [:n] left.2 fun i hi state =>
        ladderStep left.1 i (range_mem_256 hn hi) state)
      (WF.foldRange [:n] right.2 fun i hi state =>
        ladderStep right.1 i (range_mem_256 hn hi) state) := by
    apply WF.Rel.foldRange_rule
    · intro lv rv h
      exact h
    · intro i hi
      unfold WF.RelHom
      intro A leftState rightState hA
      have hstep := (ladderStep_wf i (range_mem_256 hn hi)).relHom A
        (left.1, leftState) (right.1, rightState)
        (fun lv rv h => hA lv rv h)
      apply WF.Rel.mono hstep
      intro lv rv _ _ h
      exact ⟨h.1, (hA lv rv h.1).1, h.2⟩
  apply WF.Rel.mono hloop
  intro lv rv _ _ h
  exact h.2

theorem scalarMul_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Fn × Projective) =>
        Elem.WFRel lv rv l.1 r.1 ∧ Projective.WFRel lv rv l.2 r.2)
      (fun z => scalarMul z.1 z.2) Projective.WFRel := by
  unfold WF.GadgetSpec scalarMul
  intro left right
  let A : WF.Assumption := fun lv rv =>
    Elem.WFRel lv rv left.1 right.1 ∧ WFRel lv rv left.2 right.2
  have hloop := (scalarLoop_wf 256 (by omega)).relHom A
    (left.1, ⟨infinity, left.2⟩) (right.1, ⟨infinity, right.2⟩)
    (fun lv rv h => ⟨h.1, infinity_wf lv rv, h.2⟩)
  apply hloop.bind
  intro B leftState rightState hB
  apply WF.Rel.pure
  intro lv rv h
  exact (hB lv rv h).2.1

def curveCube (x : Fp) : Circuit Fp := do
  let x2 ← mul base x x
  mul base x2 x

def mulAdd (a x b : Fp) : Circuit Fp := do
  let ax ← mul base a x
  add base ax b

def curveLinear (x : Fp) : Circuit Fp := mulAdd curveA x curveB

def cubic (a x b : Fp) : Circuit Fp := do
  let x3 ← curveCube x
  let linear ← mulAdd a x b
  add base x3 linear

def curveRhs (x : Fp) : Circuit Fp := cubic curveA x curveB

/-- Check an affine public key against `y² = x³ - 3x + b`. -/
def assertOnCurve (x y : Fp) : Circuit Unit := do
  let y2 ← mul base y y
  let rhs ← curveRhs x
  Modular.assertEq base y2 rhs

def curveRhsValue (ρ : WF.Valuation) (x : Fp) : Nat :=
  fadd (fmul (fmul (x.evalNat ρ) (x.evalNat ρ)) (x.evalNat ρ))
    (fadd (fmul (curveA.evalNat ρ) (x.evalNat ρ)) (curveB.evalNat ρ))

def CurveCubeSpec (ρ : WF.Valuation) (x out : Fp) : Prop :=
  out.Valid ρ ∧
    out.evalNat ρ = fmul (fmul (x.evalNat ρ) (x.evalNat ρ)) (x.evalNat ρ)

def CurveLinearSpec (ρ : WF.Valuation) (x out : Fp) : Prop :=
  out.Valid ρ ∧ out.evalNat ρ =
    fadd (fmul (curveA.evalNat ρ) (x.evalNat ρ)) (curveB.evalNat ρ)

def MulAddSpec (ρ : WF.Valuation) (a x b out : Fp) : Prop :=
  out.Valid ρ ∧ out.evalNat ρ =
    fadd (fmul (a.evalNat ρ) (x.evalNat ρ)) (b.evalNat ρ)

def CubicSpec (ρ : WF.Valuation) (a x b out : Fp) : Prop :=
  out.Valid ρ ∧ out.evalNat ρ =
    fadd (fmul (fmul (x.evalNat ρ) (x.evalNat ρ)) (x.evalNat ρ))
      (fadd (fmul (a.evalNat ρ) (x.evalNat ρ)) (b.evalNat ρ))

def CurveRhsSpec (ρ : WF.Valuation) (x rhs : Fp) : Prop :=
  rhs.Valid ρ ∧ rhs.evalNat ρ = curveRhsValue ρ x

def OnCurveSpec (ρ : WF.Valuation) (x y : Fp) : Prop :=
  fmul (y.evalNat ρ) (y.evalNat ρ) = curveRhsValue ρ x

@[spec] theorem curveCube_sound {x : Fp} (hx : x.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (curveCube x)
    ⦃⇓ out => ⌜CurveCubeSpec ρ x out⌝⦄ := by
  mvcgen -trivial [curveCube]
  all_goals simp_all only [CurveCubeSpec, MulSpec, fmul, base_modulus_eq,
    true_and, implies_true]

@[spec] theorem curveCube_complete {x : Fp} (hx : x.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (curveCube x)
    ⦃⇓ out => ⌜CurveCubeSpec ρ x out⌝⦄ := by
  mvcgen -trivial [curveCube]
  all_goals simp_all only [CurveCubeSpec, MulSpec, fmul, base_modulus_eq,
    true_and, implies_true]

@[spec] theorem mulAdd_sound {a x b : Fp}
    (ha : a.Valid ρ) (hx : x.Valid ρ) (hb : b.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (mulAdd a x b)
    ⦃⇓ out => ⌜MulAddSpec ρ a x b out⌝⦄ := by
  mvcgen -trivial [mulAdd]
  all_goals simp_all only [MulAddSpec, MulSpec, AddSpec, fmul, fadd,
    base_modulus_eq, true_and, implies_true]

@[spec] theorem mulAdd_complete {a x b : Fp}
    (ha : a.Valid ρ) (hx : x.Valid ρ) (hb : b.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (mulAdd a x b)
    ⦃⇓ out => ⌜MulAddSpec ρ a x b out⌝⦄ := by
  mvcgen -trivial [mulAdd]
  all_goals simp_all only [MulAddSpec, MulSpec, AddSpec, fmul, fadd,
    base_modulus_eq, true_and, implies_true]

@[spec] theorem curveLinear_sound {x : Fp} (hx : x.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (curveLinear x)
    ⦃⇓ out => ⌜CurveLinearSpec ρ x out⌝⦄ := by
  have ha : curveA.Valid ρ :=
    Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  have hb : curveB.Valid ρ :=
    Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  simpa only [curveLinear, CurveLinearSpec, MulAddSpec] using
    mulAdd_sound ha hx hb

@[spec] theorem curveLinear_complete {x : Fp} (hx : x.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (curveLinear x)
    ⦃⇓ out => ⌜CurveLinearSpec ρ x out⌝⦄ := by
  have ha : curveA.Valid ρ :=
    Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  have hb : curveB.Valid ρ :=
    Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  simpa only [curveLinear, CurveLinearSpec, MulAddSpec] using
    mulAdd_complete ha hx hb

@[spec] theorem cubic_sound {a x b : Fp}
    (ha : a.Valid ρ) (hx : x.Valid ρ) (hb : b.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (cubic a x b)
    ⦃⇓ out => ⌜CubicSpec ρ a x b out⌝⦄ := by
  mvcgen -trivial [cubic]
  all_goals simp_all only [CubicSpec, CurveCubeSpec, MulAddSpec, AddSpec, fadd,
    base_modulus_eq, true_and, implies_true]

@[spec] theorem cubic_complete {a x b : Fp}
    (ha : a.Valid ρ) (hx : x.Valid ρ) (hb : b.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (cubic a x b)
    ⦃⇓ out => ⌜CubicSpec ρ a x b out⌝⦄ := by
  mvcgen -trivial [cubic]
  all_goals simp_all only [CubicSpec, CurveCubeSpec, MulAddSpec, AddSpec, fadd,
    base_modulus_eq, true_and, implies_true]

@[spec] theorem curveRhs_sound {x : Fp} (hx : x.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (curveRhs x)
    ⦃⇓ rhs => ⌜CurveRhsSpec ρ x rhs⌝⦄ := by
  have ha : curveA.Valid ρ :=
    Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  have hb : curveB.Valid ρ :=
    Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  simpa only [curveRhs, CurveRhsSpec, CubicSpec, curveRhsValue] using
    cubic_sound ha hx hb

@[spec] theorem curveRhs_complete {x : Fp} (hx : x.Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (curveRhs x)
    ⦃⇓ rhs => ⌜CurveRhsSpec ρ x rhs⌝⦄ := by
  have ha : curveA.Valid ρ :=
    Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  have hb : curveB.Valid ρ :=
    Modular.ofNat_valid base _ (by native_decide) (by native_decide)
  simpa only [curveRhs, CurveRhsSpec, CubicSpec, curveRhsValue] using
    cubic_complete ha hx hb

@[spec] theorem assertOnCurve_sound {x y : Fp}
    (hx : x.Valid ρ) (hy : y.Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (assertOnCurve x y)
    ⦃⇓ _ => ⌜OnCurveSpec ρ x y⌝⦄ := by
  mvcgen -trivial [assertOnCurve]
  all_goals simp_all only [OnCurveSpec, CurveRhsSpec, MulSpec, fmul,
    base_modulus_eq, implies_true]

@[spec] theorem assertOnCurve_complete {x y : Fp}
    (hx : x.Valid ρ) (hy : y.Valid ρ) (hon : OnCurveSpec ρ x y) :
    ⦃⌜True⌝⦄ Complete.interp ρ (assertOnCurve x y)
    ⦃⇓ _ => ⌜OnCurveSpec ρ x y⌝⦄ := by
  mvcgen -trivial [assertOnCurve]
  all_goals simp_all only [OnCurveSpec, CurveRhsSpec, MulSpec, fmul,
    base_modulus_eq, implies_true]

theorem curveCube_wf :
    WF.GadgetSpec (Elem.WFRel (p := base)) curveCube
      (Elem.WFRel (p := base)) := by
  wfgen_steps' using [Modular.mul_wf] unfold [curveCube]
  all_goals grind only

theorem mulAdd_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Fp × Fp × Fp) =>
        Elem.WFRel lv rv l.1 r.1 ∧
          Elem.WFRel lv rv l.2.1 r.2.1 ∧
          Elem.WFRel lv rv l.2.2 r.2.2)
      (fun z => mulAdd z.1 z.2.1 z.2.2) (Elem.WFRel (p := base)) := by
  wfgen_steps' using [Modular.mul_wf, Modular.add_wf] unfold [mulAdd]
  all_goals grind only

theorem curveLinear_wf :
    WF.GadgetSpec (Elem.WFRel (p := base)) curveLinear
      (Elem.WFRel (p := base)) := by
  unfold WF.GadgetSpec curveLinear
  intro left right
  apply Modular.WF.Rel.strengthen
    (mulAdd_wf (curveA, left, curveB) (curveA, right, curveB))
  intro lv rv h
  exact ⟨curveA_wf lv rv, h, curveB_wf lv rv⟩

theorem cubic_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Fp × Fp × Fp) =>
        Elem.WFRel lv rv l.1 r.1 ∧
          Elem.WFRel lv rv l.2.1 r.2.1 ∧
          Elem.WFRel lv rv l.2.2 r.2.2)
      (fun z => cubic z.1 z.2.1 z.2.2) (Elem.WFRel (p := base)) := by
  wfgen_steps' using [curveCube_wf, mulAdd_wf, Modular.add_wf] unfold [cubic]
  all_goals grind only

theorem curveRhs_wf :
    WF.GadgetSpec (Elem.WFRel (p := base)) curveRhs
      (Elem.WFRel (p := base)) := by
  unfold WF.GadgetSpec curveRhs
  intro left right
  apply Modular.WF.Rel.strengthen
    (cubic_wf (curveA, left, curveB) (curveA, right, curveB))
  intro lv rv h
  exact ⟨curveA_wf lv rv, h, curveB_wf lv rv⟩

theorem assertOnCurve_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Fp × Fp) =>
        Elem.WFRel lv rv l.1 r.1 ∧ Elem.WFRel lv rv l.2 r.2)
      (fun z => assertOnCurve z.1 z.2) (fun _ _ _ _ => True) := by
  wfgen_steps' using [Modular.mul_wf, curveRhs_wf, Modular.assertEq_wf]
    unfold [assertOnCurve]
  all_goals grind only

end Projective

end Freigen.F2Z.Examples.P256
