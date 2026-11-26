import Freigen.Ast.JoinPoints
import Freigen.Ast.Bind

/-!
How the translation in the scope of a join point relates to `Expr.bind`:
translating with tail calls running `κ` is translating with tail calls as
returns, then binding `κ` (`tr_jump_eq`). The correctness proofs read an
eliminated join point, `(Jr S).bind b`, as the scope translated in the join
point's own mode through this equation.
-/

namespace Freigen.Ast.JoinPoints

variable {L : Language} [L.Blocks] {V : L.Tp → Type}

omit [L.Blocks] in
theorem stuck_bind {γ : L.Ctx} {t a b : L.Tp} (k₀ : V t → Expr L V γ a)
    (κ : V a → Expr L V γ b) : (stuck t k₀).bind κ = stuck t fun v => (k₀ v).bind κ :=
  rfl

omit [L.Blocks] in
theorem var_bind {γ : L.Ctx} {t a b : L.Tp} (x : PVar V t) (k₀ : V t → Expr L V γ a)
    (κ : V a → Expr L V γ b) : (var x k₀).bind κ = var x fun v => (k₀ v).bind κ := by
  rcases x with _ | _ <;> rfl

omit [L.Blocks] in
theorem vars_bind {γ : L.Ctx} {a b : L.Tp} {ts : List L.Tp} (xs : HList (PVar V) ts)
    (k₀ : HList V ts → Expr L V γ a) (κ : V a → Expr L V γ b) :
    (vars xs k₀).bind κ = vars xs fun vs => (k₀ vs).bind κ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [vars]
    rw [var_bind]
    congr 1
    funext v
    exact ih _

/-- Translating in the scope of a join point whose tail calls run `κ₀`, then
`κ`, is translating with tail calls running `κ₀`, followed by `κ`. -/
theorem tr_bind {γ : L.Ctx} {o : L.Tp} (e : Expr L (PVar V) γ o) :
    ∀ {o₁ o₂ τ : L.Tp} (n : Nat) (J : List Nat) (ℓ : Nat) (κ₀ : V τ → Expr L V γ o₁)
      (κ : V o₁ → Expr L V γ o₂),
      tr n J (.jump (o := o) ℓ fun y => (κ₀ y).bind κ) e = (tr n J (.jump ℓ κ₀) e).bind κ := by
  induction e with
  | ret x => intro _ _ _ n J ℓ κ₀ κ; rfl
  | lit tp v k ih =>
    intro _ _ _ n J ℓ κ₀ κ
    simp only [tr, Expr.bind]
    congr 1
    funext x
    exact ih _ _ _ _ _ _
  | builtin b args k ih =>
    intro _ _ _ n J ℓ κ₀ κ
    simp only [tr]
    rw [vars_bind]
    congr 1
    funext a
    simp only [Expr.bind]
    congr 1
    funext x
    exact ih _ _ _ _ _ _
  | @lam γ inp out o b k ihb ihk =>
    intro _ _ _ n J ℓ κ₀ κ
    by_cases hel : out = o ∧ ok (n + 1) J (some ℓ) (b (.inr n)) = true ∧
        ok (n + 1) (n :: J) (some n) (k (.inr n)) = true
    · obtain ⟨rfl, hb', hk'⟩ := hel
      rw [tr_lam_elim _ _ _ _ _ hb' hk', tr_lam_elim _ _ _ _ _ hb' hk', Expr.bind_assoc]
      congr 1
      funext y
      exact ihb _ _ _ _ _ _
    · rw [tr_lam_keep _ _ _ _ _ hel, tr_lam_keep _ _ _ _ _ hel]
      simp only [Expr.bind]
      congr 1
      funext f
      exact ihk _ _ _ _ _ _
  | @app γ inp out o f x k ih =>
    intro _ _ τ n J ℓ κ₀ κ
    simp only [tr]
    by_cases hc : (isLabel ℓ f && isRet n k) = true
    · rw [if_pos hc, if_pos hc]
      by_cases hi : inp = τ
      · subst hi
        rw [dif_pos rfl, dif_pos rfl, var_bind]
      · rw [dif_neg hi, dif_neg hi]
        rfl
    · rw [if_neg hc, if_neg hc, var_bind]
      congr 1
      funext f'
      rw [var_bind]
      congr 1
      funext x'
      simp only [Expr.bind]
      congr 1
      funext r
      exact ih _ _ _ _ _ _
  | ite c t e k iht ihe ihk =>
    intro _ _ _ n J ℓ κ₀ κ
    simp only [tr]
    by_cases hr : isRet n k = true
    · rw [if_pos hr, if_pos hr, var_bind]
      rfl
    · rw [if_neg hr, if_neg hr, var_bind]
      congr 1
      funext c'
      simp only [Expr.bind]
      congr 1
      funext r
      exact ihk _ _ _ _ _ _
  | loop body i k ihb ihk =>
    intro _ _ _ n J ℓ κ₀ κ
    simp only [tr]
    rw [var_bind]
    congr 1
    funext i'
    simp only [Expr.bind]
    congr 1
    funext r
    exact ihk _ _ _ _ _ _
  | op e i bl k ihb ihk =>
    intro _ _ _ n J ℓ κ₀ κ
    simp only [tr]
    rw [var_bind]
    congr 1
    funext i'
    simp only [Expr.bind]
    congr 1
    funext r
    exact ihk _ _ _ _ _ _

/-- In the scope of a join point, the translation of tail calls by `κ` is
their translation as returns, followed by `κ`. -/
theorem tr_jump_eq {γ : L.Ctx} {o o' τ : L.Tp} (n : Nat) (J : List Nat) (ℓ : Nat)
    (κ : V τ → Expr L V γ o') (e : Expr L (PVar V) γ o) :
    tr n J (.jump ℓ κ) e = (tr n J (.jump ℓ fun v => .ret v) e).bind κ :=
  tr_bind e n J ℓ (fun v => .ret v) κ

end Freigen.Ast.JoinPoints
