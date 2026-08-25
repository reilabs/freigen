import Freigen.Wheels
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.BooleanRing

namespace Freigen.F2Z

inductive RawLC (F : Type u) where
  | const (value : F)
  | var (index : Nat)
  | add (left right : RawLC F)
  | scale (factor : F) (value : RawLC F)

namespace RawLC

variable {F : Type u} [Semiring F]

def eval (valuation : Nat → F) : RawLC F → F
  | .const value => value
  | .var index => valuation index
  | .add left right => eval valuation left + eval valuation right
  | .scale factor value => factor * eval valuation value

def Equiv (left right : RawLC F) : Prop :=
  ∀ valuation, eval valuation left = eval valuation right

def semanticSetoid : Setoid (RawLC F) where
  r := Equiv
  iseqv := {
    refl := fun _ _ => rfl
    symm := fun h valuation => (h valuation).symm
    trans := fun hab hbc valuation => (hab valuation).trans (hbc valuation) }

def constant : RawLC F → F
  | .const value => value
  | .var _ => 0
  | .add left right => constant left + constant right
  | .scale factor value => factor * constant value

def coeff (index : Nat) : RawLC F → F
  | .const _ => 0
  | .var other => if other = index then 1 else 0
  | .add left right => coeff index left + coeff index right
  | .scale factor value => factor * coeff index value

@[simp] theorem eval_zero (raw : RawLC F) :
    eval (fun _ => 0) raw = constant raw := by
  induction raw <;> simp [eval, constant, *]

def basis (index : Nat) : Nat → F :=
  fun other => if other = index then 1 else 0

@[simp] theorem eval_basis (index : Nat) (raw : RawLC F) :
    eval (basis index) raw = constant raw + coeff index raw := by
  induction raw with
  | const value => simp [eval, constant, coeff]
  | var other =>
      by_cases h : other = index <;> simp [eval, constant, coeff, basis, h]
  | add left right hl hr =>
      simp only [eval, constant, coeff, hl, hr]
      ac_rfl
  | scale factor value ih =>
      simp [eval, constant, coeff, ih, mul_add]

theorem constant_eq_of_equiv {left right : RawLC F}
    (h : Equiv left right) : constant left = constant right := by
  simpa only [eval_zero] using h (fun _ => 0)

theorem coeff_eq_of_equiv {R : Type u} [Ring R]
    {left right : RawLC R} (h : Equiv left right) (index : Nat) :
    coeff index left = coeff index right := by
  have hconstant := constant_eq_of_equiv h
  have hbasis := h (basis index)
  simp only [eval_basis] at hbasis
  rw [hconstant] at hbasis
  exact add_left_cancel hbasis

end RawLC

/-- The canonical sparse form used at circuit-consumption boundaries.  This is
not the representation used while building a circuit. -/
structure Sparse (F : Type u) [Semiring F] where
  constant : F
  coeffs : Std.ExtTreeMap Nat F
  ne_zero : ∀ {index : Nat}, coeffs[index]? ≠ some 0

namespace Sparse

variable {F : Type u} [Semiring F]

def coeff (value : Sparse F) (index : Nat) : F :=
  value.coeffs[index]?.getD 0

@[ext] theorem ext {left right : Sparse F}
    (hconstant : left.constant = right.constant)
    (hcoeff : ∀ index, left.coeff index = right.coeff index) :
    left = right := by
  rcases left with ⟨leftConstant, leftCoeffs, hleft⟩
  rcases right with ⟨rightConstant, rightCoeffs, hright⟩
  simp only at hconstant hcoeff
  subst rightConstant
  congr 1
  apply Std.ExtTreeMap.ext_getElem?
  intro index
  have h := hcoeff index
  simp only [coeff] at h
  cases hl : leftCoeffs[index]? <;> cases hr : rightCoeffs[index]? <;> grind

def ofConst (value : F) : Sparse F where
  constant := value
  coeffs := ∅
  ne_zero := by simp

variable [DecidableEq F]

def singleton (index : Nat) : Sparse F where
  constant := 0
  coeffs := if (1 : F) = 0 then ∅ else {(index, 1)}
  ne_zero := by
    intro other
    by_cases h : (1 : F) = 0
    · simp_all
    · simp [h]
      change ((default : Std.ExtTreeMap Nat F).insert index 1)[other]? ≠ some (0 : F)
      rw [Std.ExtTreeMap.getElem?_insert]
      by_cases hi : index = other
      · simp [h, hi]
      · simp [default, hi]

def add (left right : Sparse F) : Sparse F where
  constant := left.constant + right.constant
  coeffs := Std.ExtTreeMap.mergeWith (fun _ => (· + ·)) left.coeffs right.coeffs
    |>.filter (fun _ coefficient => coefficient ≠ 0)
  ne_zero := by simp

def scale (factor : F) (value : Sparse F) : Sparse F where
  constant := factor * value.constant
  coeffs := value.coeffs.map (fun _ coefficient => factor * coefficient)
    |>.filter (fun _ coefficient => coefficient ≠ 0)
  ne_zero := by simp

omit [DecidableEq F] in
@[simp] theorem ofConst_constant (value : F) :
    (ofConst value).constant = value := rfl

omit [DecidableEq F] in
@[simp] theorem ofConst_coeff (value : F) (index : Nat) :
    (ofConst value).coeff index = 0 := rfl

@[simp] theorem singleton_constant (index : Nat) :
    (singleton (F := F) index).constant = 0 := rfl

@[simp] theorem singleton_coeff (index other : Nat) :
    (singleton (F := F) index).coeff other =
      if index = other then 1 else 0 := by
  by_cases hzero : (1 : F) = 0
  · have hall (x : F) : x = 0 := by
      calc
        x = x * 1 := (mul_one x).symm
        _ = x * 0 := by rw [hzero]
        _ = 0 := mul_zero x
    simp [singleton, coeff, hall]
  · by_cases h : index = other
    · simp [singleton, coeff, hzero, h]
    · simp [singleton, coeff, hzero, h]

@[simp] theorem add_constant (left right : Sparse F) :
    (add left right).constant = left.constant + right.constant := rfl

@[simp] theorem add_coeff (left right : Sparse F) (index : Nat) :
    (add left right).coeff index = left.coeff index + right.coeff index := by
  change (add left right).coeffs[index]?.getD 0 =
    left.coeffs[index]?.getD 0 + right.coeffs[index]?.getD 0
  simp only [add, Std.ExtTreeMap.getElem?_filter', Std.ExtTreeMap.getElem?_mergeWith]
  have := @left.ne_zero index
  have := @right.ne_zero index
  generalize left.coeffs[index]? = leftCoeff at *
  generalize right.coeffs[index]? = rightCoeff at *
  cases leftCoeff <;> cases rightCoeff <;> grind

@[simp] theorem scale_constant (factor : F) (value : Sparse F) :
    (scale factor value).constant = factor * value.constant := rfl

@[simp] theorem scale_coeff (factor : F) (value : Sparse F) (index : Nat) :
    (scale factor value).coeff index = factor * value.coeff index := by
  change (scale factor value).coeffs[index]?.getD 0 =
    factor * value.coeffs[index]?.getD 0
  simp only [scale, Std.ExtTreeMap.getElem?_filter', Std.ExtTreeMap.getElem?_map]
  generalize value.coeffs[index]? = coefficient at *
  cases coefficient <;> grind

end Sparse

namespace RawLC

variable {F : Type u} [Semiring F] [DecidableEq F]

def normalForm : RawLC F → Sparse F
  | .const value => Sparse.ofConst value
  | .var index => Sparse.singleton index
  | .add left right => Sparse.add left.normalForm right.normalForm
  | .scale factor value => Sparse.scale factor value.normalForm

@[simp] theorem normalForm_constant (raw : RawLC F) :
    raw.normalForm.constant = raw.constant := by
  induction raw <;> simp [normalForm, constant, *]

@[simp] theorem normalForm_coeff (raw : RawLC F) (index : Nat) :
    raw.normalForm.coeff index = raw.coeff index := by
  induction raw <;> simp [normalForm, coeff, *]

theorem normalForm_eq_of_equiv {R : Type u} [Ring R] [DecidableEq R]
    {left right : RawLC R} (h : Equiv left right) :
    left.normalForm = right.normalForm := by
  apply Sparse.ext
  · simpa using constant_eq_of_equiv h
  · intro index
    simpa using coeff_eq_of_equiv h index

end RawLC

def LC (F : Type u) [Semiring F] := Quotient (RawLC.semanticSetoid (F := F))

namespace LC

variable {F : Type u} [Semiring F]

instance [Repr F] : Repr (LC F) where
  reprPrec _ _ := "<linear combination>"

def eval (valuation : Nat → F) (value : LC F) : F :=
  Quotient.lift (RawLC.eval valuation)
    (fun left right h => by
      change RawLC.Equiv left right at h
      exact h valuation) value

@[ext] theorem ext {left right : LC F}
    (h : ∀ valuation, eval valuation left = eval valuation right) :
    left = right := by
  induction left using Quotient.inductionOn with
  | _ left =>
    induction right using Quotient.inductionOn with
    | _ right =>
      apply Quotient.sound
      intro valuation
      exact h valuation

theorem eq_iff_eval {left right : LC F} :
    left = right ↔ ∀ valuation, eval valuation left = eval valuation right := by
  constructor
  · intro h valuation
    rw [h]
  · exact ext

def ofConst (value : F) : LC F :=
  Quotient.mk _ (RawLC.const value)

instance : Coe F (LC F) := ⟨ofConst⟩

instance : Singleton Nat (LC F) where
  singleton index := Quotient.mk _ (RawLC.var index)

instance : Zero (LC F) := ⟨ofConst 0⟩
instance : One (LC F) := ⟨ofConst 1⟩

instance : Add (LC F) where
  add := Quotient.map₂ RawLC.add fun _ _ hl _ _ hr valuation => by
    simp only [RawLC.eval]
    rw [hl valuation, hr valuation]

def scale (factor : F) : LC F → LC F :=
  Quotient.map (RawLC.scale factor) fun _ _ h valuation => by
    simp only [RawLC.eval]
    rw [h valuation]

instance : SMul F (LC F) := ⟨scale⟩

def constant (value : LC F) : F :=
  eval (fun _ => 0) value

/-- Recover the unique sparse representative of a semantic linear
combination.  This is deliberately delayed until a consumer needs matrix
entries. -/
def normalForm {R : Type u} [Ring R] [DecidableEq R] (value : LC R) : Sparse R :=
  Quotient.lift RawLC.normalForm
    (fun _ _ h => RawLC.normalForm_eq_of_equiv h) value

@[simp] theorem eval_ofConst (valuation : Nat → F) (value : F) :
    eval valuation (ofConst value) = value := rfl

@[simp] theorem eval_zero (valuation : Nat → F) :
    eval valuation (0 : LC F) = 0 := rfl

@[simp] theorem eval_one (valuation : Nat → F) :
    eval valuation (1 : LC F) = 1 := rfl

@[simp] theorem eval_singleton (valuation : Nat → F) (index : Nat) :
    eval valuation ({index} : LC F) = valuation index := rfl

@[simp] theorem eval_add (valuation : Nat → F) (left right : LC F) :
    eval valuation (left + right) = eval valuation left + eval valuation right := by
  exact Quotient.inductionOn₂ left right fun _ _ => rfl

@[simp] theorem eval_scale (valuation : Nat → F) (factor : F) (value : LC F) :
    eval valuation (scale factor value) = factor * eval valuation value := by
  exact Quotient.inductionOn value fun _ => rfl

@[simp] theorem eval_smul (valuation : Nat → F) (factor : F) (value : LC F) :
    eval valuation (factor • value) = factor * eval valuation value := by
  exact eval_scale valuation factor value

@[simp] theorem ofConst_constant (value : F) :
    (ofConst value).constant = value := by simp [constant]

@[simp] theorem singleton_constant (index : Nat) :
    ({index} : LC F).constant = 0 := by simp [constant]

@[simp] theorem zero_constant : (0 : LC F).constant = 0 := by simp [constant]
@[simp] theorem one_constant : (1 : LC F).constant = 1 := by simp [constant]
@[simp] theorem add_constant {left right : LC F} :
    (left + right).constant = left.constant + right.constant := by simp [constant]

instance : AddCommMonoid (LC F) where
  add_assoc := by intros; apply ext; intro; simp [add_assoc]
  zero_add := by intros; apply ext; intro; simp
  add_zero := by intros; apply ext; intro; simp
  add_comm := by intros; apply ext; intro; simp [add_comm]
  nsmul n value := scale n value
  nsmul_zero := by intros; apply ext; intro; simp
  nsmul_succ := by intros; apply ext; intro; simp [Nat.cast_succ, add_mul]

instance : Module F (LC F) where
  mul_smul := by intros; apply ext; intro; simp [mul_assoc]
  one_smul := by intros; apply ext; intro; simp
  smul_zero := by intros; apply ext; intro; simp
  smul_add := by intros; apply ext; intro; simp [mul_add]
  add_smul := by intros; apply ext; intro; simp [add_mul]
  zero_smul := by intros; apply ext; intro; simp

@[simp] theorem eval_nsmul (valuation : Nat → F) (n : Nat) (value : LC F) :
    eval valuation (n • value) = n • eval valuation value := by
  change eval valuation (scale (n : F) value) = n • eval valuation value
  simp [nsmul_eq_mul]


instance {R : Type u} [Ring R] : AddCommGroup (LC R) :=
  Module.addCommMonoidToAddCommGroup R

@[simp] theorem eval_sub {R : Type u} [Ring R]
    (valuation : Nat → R) (left right : LC R) :
    eval valuation (left - right) = eval valuation left - eval valuation right := by
  rw [sub_eq_add_neg, eval_add, ← neg_one_smul R right, eval_smul]
  simp [sub_eq_add_neg]

instance (priority := 100) : NatCast (LC F) where
  natCast n := n • 1

@[simp] theorem eval_natCast (valuation : Nat → F) (n : Nat) :
    eval valuation (n : LC F) = n := by
  change eval valuation (n • (1 : LC F)) = (n : F)
  simp

@[simp] theorem eval_sum {I : Type*} (valuation : Nat → F)
    (s : Finset I) (f : I → LC F) :
    eval valuation (∑ i ∈ s, f i) = ∑ i ∈ s, eval valuation (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

@[simp] theorem eval_array_sum (valuation : Nat → F) (xs : Array (LC F)) :
    eval valuation xs.sum = (xs.map (eval valuation)).sum := by
  rw [← Array.sum_toList, ← Array.sum_toList]
  simp only [Array.toList_map]
  induction xs.toList with
  | nil => simp
  | cons x xs ih => simp [ih]

end LC

/- Keep clients at the `LC` abstraction boundary.  In particular, this lets
the witness-side unification hints recognize `LC Int` and `LC Bool` instead of
seeing the implementation's `Quotient` head symbol. -/
attribute [irreducible] LC

end Freigen.F2Z
