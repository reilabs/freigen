import Freigen.IxPoly.Defs

namespace Freigen.IxPoly

variable {I : Type ui} {O : Type uo}

/--
the constant polynomial
-/
def C (v : O → Type v) : I ⟹ₚ O where
  Tag := v
  Field := fun _ _ => PEmpty
  Elem := fun _ _ => PEmpty.elim

def C_action { v : O → Type v } { x : I → Type w } {i : O}:
    (C v) x i ≃ v i where
  toFun := fun ⟨p, g⟩ => p
  invFun := fun p => ⟨p, fun a => PEmpty.elim a⟩
  left_inv := fun ⟨p, g⟩ => by
    simp only [Obj]
    congr 1
    ext x
    cases x

/--
variable selector
-/
def X (var : O → I) : I ⟹ₚ O where
  Tag := fun _ => PUnit
  Field := fun _ _ => PUnit
  Elem := fun o _ _ => var o

def X_action { var : O → I } { x : I → Type w } {i : O}:
    (X var) x i ≃ x (var i) where
  toFun := fun ⟨_, g⟩ => g ()
  invFun := fun x => ⟨(), fun _ => x⟩
  left_inv := fun ⟨_, g⟩ => by rfl

instance : Add (I ⟹ₚ O) where
  add F G := {
    Tag := fun o => F.Tag o ⊕' G.Tag o
    Field := fun o p => match p with
      | PSum.inl p' => F.Field o p'
      | PSum.inr p' => G.Field o p'
    Elem := fun o p a => match p with
      | PSum.inl p' => F.Elem o p' a
      | PSum.inr p' => G.Elem o p' a
  }

def add_action {F G : I ⟹ₚ O} {x : I → Type w} {i : O}:
    (F + G) x i ≃ F x i ⊕ G x i where
  toFun := fun ⟨p, g⟩ => match p with
    | PSum.inl p' => Sum.inl ⟨p', g⟩
    | PSum.inr p' => Sum.inr ⟨p', g⟩
  invFun
    | Sum.inl ⟨p', g⟩ => ⟨.inl p', g⟩
    | Sum.inr ⟨p', g⟩ => ⟨.inr p', g⟩
  left_inv := fun ⟨p, g⟩ => by
    cases p <;> {
      simp
    }
  right_inv := fun x => by
    cases x <;> {
      rename_i obj
      cases obj
      simp
    }

instance : Mul (I ⟹ₚ O) where
  mul F G := {
    Tag := fun o => F.Tag o ×' G.Tag o
    Field := fun o ⟨p1, p2⟩ => F.Field o p1 ⊕' G.Field o p2
    Elem := fun o p x => match x with
      | PSum.inl a => F.Elem o p.1 a
      | PSum.inr a => G.Elem o p.2 a
  }

def mul_action {F G : I ⟹ₚ O} {x : I → Type w} {i : O}:
    (F * G) x i ≃ F x i × G x i where
  toFun := fun ⟨⟨p1, p2⟩, g⟩ => ⟨⟨p1, fun a => g (.inl a)⟩, ⟨p2, fun a => g (.inr a)⟩⟩
  invFun := fun ⟨⟨p1, g1⟩, ⟨p2, g2⟩⟩ => ⟨⟨p1, p2⟩, fun x => match x with
    | PSum.inl a => g1 a
    | PSum.inr a => g2 a⟩
  left_inv := fun ⟨⟨p1, p2⟩, g⟩ => by
    simp only [Obj]
    congr 1
    ext x
    cases x <;> rfl

instance {n} : OfNat (I ⟹ₚ O) n where
  ofNat := C (fun _ => Fin n)

def zero_action {x : I → Type w} {i : O}:
    (0 : I ⟹ₚ O) x i ≃ Empty where
  toFun := fun ⟨p, _⟩ => Fin.elim0 p
  invFun := fun x => Empty.elim x
  left_inv := fun ⟨p, _⟩ => Fin.elim0 p
  right_inv := fun x => Empty.elim x

def addZero_action {F : I ⟹ₚ O} {x : I → Type w} {i : O}:
    (F + 0) x i ≃ F x i := by
  apply Iso.trans add_action
  apply Iso.trans
  · apply Iso.sumCongr (Iso.refl _) zero_action
  apply Iso.sumEmpty

def one_action {x : I → Type w} {i : O}:
    (1 : I ⟹ₚ O) x i ≃ Unit where
  toFun := fun ⟨p, g⟩ => ()
  invFun := fun _ => ⟨(0 : Fin 1), fun a => PEmpty.elim a⟩
  left_inv := fun ⟨p, g⟩ => by
    congr 1
    · rcases p with ⟨v, lt⟩
      have : v = 0 := Nat.lt_one_iff.mp lt
      simp_all
    · ext a; cases a
  right_inv := fun p => by rfl

end Freigen.IxPoly
