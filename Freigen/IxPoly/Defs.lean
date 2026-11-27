import Freigen.Iso

namespace Freigen

/--
IxPoly is a polynomial functor from I-indexed families to O-indexed families.
-/
structure IxPoly (I : Type ui) (O : Type uo) where
  Tag : O → Type v
  Field : (o : O) → Tag o → Type v
  Elem : (o : O) → (p : Tag o) → Field o p → I

namespace IxPoly

scoped infix :50 " ⟹ₚ " => IxPoly

variable { I : Type ui } { O : Type uo}

def Obj (F : I ⟹ₚ O) (X : I → Type w): O → Type _ :=
  fun o => Σ (p : F.Tag o), (a : F.Field o p) → X (F.Elem o p a)

instance {I O} : CoeFun (I ⟹ₚ O) (fun _ => (X : I → Type w) → O → Type _) where
  coe F := Obj F

def map {F : I ⟹ₚ O} {X : I → Type u} {Y : I → Type v}
    (f : (i : I) → X i → Y i) : (i: O) → F X i → F Y i
| _, ⟨p, g⟩ => ⟨p, fun a => f (F.Elem _ p a) (g a)⟩

theorem map_map {F : I ⟹ₚ O} {X Y Z : I → Type _}
    (f : (i : I) → X i → Y i) (g : (i : I) → Y i → Z i) (i : O) (x : F X i):
    map g i (map f i x) = map (fun i x => g i (f i x)) i x := by
  cases x
  rfl

theorem map_id {F : I ⟹ₚ O} {X : I → Type _} (i : O) (x : F X i):
    map (fun _ x => x) i x = x := by
  cases x
  rfl

abbrev Endo (I : Type u) := I ⟹ₚ I

/--
Initial algebra, i.e. the least fixed point of an endofunctor F : I ⟹ₚ I.
-/
inductive W (F : Endo I) : I → Type _ where
| mk : (i : I) → (p : F.Tag i) → ((a : F.Field i p) → W F (F.Elem i p a)) → W F i

def W.observe {F : Endo I} {i : I}: (W F i) → F (W F) i
| W.mk i p f => ⟨p, f⟩

def W.roll {F : Endo I} {i : I}: F (W F) i → W F i
| o => W.mk i o.1 o.2

namespace M

inductive Approx (F : Endo I) : Nat → I → Type _ where
| zero : (i : I) → Approx F 0 i
| _succ : (n : Nat) → (i : I) → (p : F.Tag i) → ((a : F.Field i p) → Approx F n (F.Elem i p a)) → Approx F (n + 1) i

def Approx.succ {F : Endo I} {n : Nat} {i : I}:
  F (Approx F n) i → Approx F (n + 1) i
| ⟨p, f⟩ => Approx._succ n i p f

inductive Agree (F : Endo I) : {n : Nat} → {i : I} → Approx F n i → Approx F (n + 1) i → Prop where
| zero : {i : I} → (x : Approx F 0 i) → (y : Approx F 1 i) → Agree F x y
| succ : {n : Nat} → {i : I} → (p : F.Tag i) →
  (f : (a : F.Field i p) → Approx F n (F.Elem i p a)) →
  (g : (a : F.Field i p) → Approx F (n + 1) (F.Elem i p a)) →
  ((a : F.Field i p) → Agree F (f a) (g a)) →
  Agree F (Approx._succ n i p f) (Approx._succ (n + 1) i p g)

end M

/--
Final coalgebra, i.e. the greatest fixed point of an endofunctor F : I ⟹ₚ I.
Represented here as a limit of a chain of finite approximations.
-/
structure M (F : Endo I) (i : I) where
  approx : (n : Nat) → M.Approx F n i
  agree : {n : Nat} → M.Agree F (approx n) (approx (n + 1))

namespace M

variable {F : Endo I}

def Approx.corec {X : I → Type w} {i : I}
    (f : (i : I) → X i → F X i) (x : X i):
  (n : Nat) → Approx F n i
| 0 => Approx.zero i
| n + 1 => Approx.succ (map (fun _ y => Approx.corec f y n) _ (f i x))

def corec {F : Endo I} {X : I → Type w} {i : I}
    (f : (i : I) → X i → F X i) (x : X i) : M F i where
  approx n := Approx.corec f x n
  agree := by
    intro n
    induction n generalizing x i with
    | zero =>
      apply M.Agree.zero
    | succ n ih =>
      apply M.Agree.succ
      intro a
      apply ih

def Approx.root {n i} : Approx F (n + 1) i → F.Tag i
| Approx._succ _ _ p _ => p

private theorem Agree.same_root {n i} {x : Approx F (n + 1) i} {y : Approx F (n + 2) i} (h : Agree F x y):
    y.root = x.root := by
  cases h; rfl

private theorem M.root_consistent {n i} {m : M F i}: (m.approx (n + 1)).root = (m.approx 1).root := by
  induction n generalizing i with
  | zero =>
    simp [M.Approx.root]
  | succ n ih =>
    rw [Agree.same_root (@m.agree (n + 1))]
    exact ih

def Approx.child {n i} : (a: Approx F (n + 1) i) → (index : F.Field i (Approx.root a)) → Approx F n (F.Elem i (Approx.root a) index)
| Approx._succ _ _ _ f, index => f index

def root {i} (m : M F i) : F.Tag i :=
  (m.approx 1).root

def Approx.childAt {n i} (x : Approx F (n + 1) i)
    (p : F.Tag i) (h : x.root = p) (a : F.Field i p) :
    Approx F n (F.Elem i p a) := by
  cases h
  exact x.child a

private theorem Approx.eta {n i} (x : Approx F (n + 1) i)
    (p : F.Tag i) (h : x.root = p) :
    Approx.succ ⟨p, x.childAt p h⟩ = x := by
  cases h
  cases x
  rfl

private theorem Agree.childAt {n i}
    {x : Approx F (n + 1) i} {y : Approx F (n + 2) i}
    (h : Agree F x y) (p : F.Tag i)
    (hx : x.root = p) (hy : y.root = p) (a : F.Field i p) :
    Agree F (x.childAt p hx a) (y.childAt p hy a) := by
  cases h with
  | succ p f g hfg =>
    cases hx
    cases hy
    exact hfg a

def childApprox {i} (m : M F i) (a : F.Field i m.root) (n : Nat) :
    Approx F n (F.Elem i m.root a) :=
  (m.approx (n + 1)).childAt m.root M.root_consistent a

private theorem childApprox_agree {i} (m : M F i) (a : F.Field i m.root) {n} :
    Agree F (m.childApprox a n) (m.childApprox a (n + 1)) := by
  exact Agree.childAt (@m.agree (n + 1)) m.root
    M.root_consistent M.root_consistent a

def child {i} (m : M F i) (a : F.Field i m.root) : M F (F.Elem i m.root a) where
  approx := m.childApprox a
  agree := m.childApprox_agree a

def prepend {i} (x : F (M F) i) : M F i where
  approx
    | 0 => Approx.zero i
    | n + 1 => Approx.succ (map (fun _ m => m.approx n) _ x)
  agree := by
    intro n
    cases n with
    | zero =>
      exact Agree.zero _ _
    | succ n =>
      rcases x with ⟨p, children⟩
      apply Agree.succ
      intro a
      exact (children a).agree

@[ext]
theorem ext {i} {x y : M F i} (h : ∀ n, x.approx n = y.approx n) : x = y := by
  cases x with
  | mk xa xh =>
    cases y with
    | mk ya yh =>
      have : xa = ya := funext h
      cases this
      rfl

def observe {i} : M F i ≃ F (M F) i where
  toFun m := ⟨m.root, m.child⟩
  invFun := prepend
  left_inv m := by
    apply M.ext
    intro n
    cases n with
    | zero =>
      cases m.approx 0
      rfl
    | succ n =>
      exact Approx.eta (m.approx (n + 1)) m.root M.root_consistent
  right_inv x := by
    rcases x with ⟨p, children⟩
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      funext a
      apply M.ext
      intro n
      simp only [child, childApprox, prepend, root, Approx.childAt]
      rfl

abbrev IxRel (X Y : I → Type w) := (i : I) → X i → Y i → Prop

instance {X Y : I → Type w} : LE (IxRel X Y) := ⟨fun R S => ∀ i x y, R i x y → S i x y⟩

def IxRel.diag {X : I → Type _} : IxRel X X := fun _ x y => x = y
def IxRel.union {X Y : I → Type _} (R S : IxRel X Y) : IxRel X Y :=
  fun _ x y => R _ x y ∨ S _ x y
def IxRel.upToEq {X : I → Type _} (R : IxRel X X) : IxRel X X :=
  IxRel.union IxRel.diag R
def IxRel.span (Seed : I → Type _) { X Y : I → Type _}
    (left : (i : I) → Seed i → X i) (right : (i : I) → Seed i → Y i): IxRel X Y :=
  fun i x y => ∃ s, x = left i s ∧ y = right i s

inductive LiftR {X Y} (F : I ⟹ₚ O) (R : IxRel X Y) : IxRel (F X) (F Y) where
| mk (o : O) (p : F.Tag o)
    (xs : ∀a, X (F.Elem o p a))
    (ys : ∀a, Y (F.Elem o p a))
    (children: ∀ a, R (F.Elem o p a) (xs a) (ys a)):
  LiftR F R o ⟨p, xs⟩ ⟨p, ys⟩

theorem LiftR.monotone (F : I ⟹ₚ O) {X Y} {R S : IxRel X Y} (h : R ≤ S) :
    LiftR F R ≤ LiftR F S := by
    intro o x y hxy
    cases hxy with
    | mk o p xs ys children =>
      apply LiftR.mk o p xs ys
      intro a
      apply h
      apply children

def bisimOp (F : Endo I) (R : IxRel (M F) (M F)) : IxRel (M F) (M F) :=
  fun i x y => LiftR F R i (x.observe) (y.observe)

open Lean.Order in
@[partial_fixpoint_monotone]
theorem LiftR.coind_monotone {X Y : I → Type w} {γ} [PartialOrder γ] (F : I ⟹ₚ O)
    (f : γ → IxRel X Y)
    (hf : @Lean.Order.monotone γ _ ((i : I) → X i → Y i → ReverseImplicationOrder) _ f) (o x y) :
    @Lean.Order.monotone γ _ ReverseImplicationOrder _ (fun z => LiftR F (f z) o x y) :=
  fun _ _ h => LiftR.monotone F (fun i a b => hf _ _ h i a b) o x y

coinductive Bisim (F : Endo I) : (i : I) → M F i → M F i → Prop where
| step {i x y} : LiftR F (Bisim F) i x.observe y.observe → Bisim F i x y

def ApproxEq {F : Endo I} (n : Nat) : IxRel (M F) (M F) :=
  fun _ x y => x.approx n = y.approx n

theorem bisimOp_R_of_R_prev {R : IxRel (M F) (M F)} {n : Nat}
    (hR : R ≤ ApproxEq n) : bisimOp F R ≤ ApproxEq (n + 1) := by
  intro i x y hxy
  change LiftR F R i (observe x) (observe y) at hxy
  generalize hx : observe x = ox at hxy
  generalize hy : observe y = oy at hxy
  cases hxy with
  | mk i p xs ys children =>
    have ex := congrArg (fun z => (observe (F := F)).symm z) hx
    have ey := congrArg (fun z => (observe (F := F)).symm z) hy
    simp only [Iso.symm_apply_apply] at ex ey
    rw [ex, ey]
    change (prepend ⟨p, xs⟩).approx (n + 1) =
      (prepend ⟨p, ys⟩).approx (n + 1)
    change Approx.succ (map (fun _ m => m.approx n) i ⟨p, xs⟩) =
      Approx.succ (map (fun _ m => m.approx n) i ⟨p, ys⟩)
    apply congrArg Approx.succ
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      funext a
      exact hR _ _ _ (children a)

theorem Bisim.le_ApproxEq : Bisim F ≤ ApproxEq n := by
  induction n with
  | zero =>
    intro i x y hxy
    unfold ApproxEq
    cases x.approx 0
    cases y.approx 0
    rfl
  | succ n ih =>
    intro i x y hxy
    cases hxy with
    | step h => exact bisimOp_R_of_R_prev ih i x y h

theorem bisim_le_eq {F : Endo I} : Bisim F ≤ (fun _ x y => x = y) := by
  intro i x y hxy
  ext n
  apply Bisim.le_ApproxEq
  exact hxy

theorem Bisim.coind { R : IxRel (M F) (M F) }
    (stable : R ≤ bisimOp F R) : R ≤ (fun _ x y => x = y) := by
  intro i x y hxy
  exact bisim_le_eq i x y (Bisim.coinduct F R stable i x y hxy)

theorem observe_corec {X i} {f : (i : I) → X i → F X i} {x : X i}:
    observe (corec f x) = map (fun _ y => corec f y) i (f i x) := by
  rfl

theorem eq_of_observe_eq {i} {x y : M F i} (h : x.observe = y.observe) : x = y :=
  IxPoly.M.observe.injective h

end M

end IxPoly

end Freigen
