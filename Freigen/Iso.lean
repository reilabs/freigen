namespace Freigen

structure Iso (α : Sort u) (β : Sort v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x := by intro; rfl
  right_inv : ∀ y, toFun (invFun y) = y := by intro; rfl

scoped infixl:25 " ≃ " => Iso

namespace Iso

instance : CoeFun (α ≃ β) (fun _ => α → β) := ⟨Iso.toFun⟩

def symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩

def refl (α) : α ≃ α := ⟨id, id, fun _ => rfl, fun _ => rfl⟩

@[simp] theorem symm_apply_apply (e : α ≃ β) (x : α) : e.symm (e x) = x := e.left_inv x

@[simp] theorem apply_symm_apply (e : α ≃ β) (y : β) : e (e.symm y) = y := e.right_inv y

def trans (e : α ≃ β) (f : β ≃ γ) : α ≃ γ where
  toFun x := f (e x)
  invFun z := e.symm (f.symm z)
  left_inv x := by simp
  right_inv z := by simp

theorem injective (e : α ≃ β) : Function.Injective e := fun x y h => by
  rw [← e.symm_apply_apply x, h, e.symm_apply_apply]

def sumCongr (e : α ≃ β) (f : γ ≃ δ) : α ⊕ γ ≃ β ⊕ δ where
  toFun | .inl a => .inl (e a) | .inr c => .inr (f c)
  invFun | .inl b => .inl (e.symm b) | .inr d => .inr (f.symm d)
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp

def prodCongr (e : α ≃ β) (f : γ ≃ δ) : α × γ ≃ β × δ where
  toFun p := (e p.1, f p.2)
  invFun p := (e.symm p.1, f.symm p.2)
  left_inv p := by simp
  right_inv p := by simp

def sumEmpty (α) : α ⊕ Empty ≃ α where
  toFun | .inl a => a | .inr b => b.elim
  invFun := .inl
  left_inv x := by cases x with | inl => rfl | inr b => exact b.elim

end Iso

end Freigen
