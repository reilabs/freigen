import Freigen.Ast.Defs

/-!
Well-formedness of PHOAS terms: two instantiations of a term, at different
variable types, have the same shape, with corresponding variables bound at
corresponding binders. Every term built by a function that is parametric in
the variable type is well-formed, but Lean cannot prove it internally, so
passes that inspect variables (by instantiating terms at a type of their
choice) take it as a hypothesis. `ast_wf` proves it for a concrete program.
-/

namespace Freigen.Ast

variable {L : Language} {V₁ V₂ : L.Tp → Type}

/-- Pairs of corresponding variables in scope. -/
abbrev WfCtx (L : Language) (V₁ V₂ : L.Tp → Type) := List (Σ t : L.Tp, V₁ t × V₂ t)

/-- Arguments, pairwise corresponding. -/
inductive WfArgs (Δ : WfCtx L V₁ V₂) : {ts : List L.Tp} → HList V₁ ts → HList V₂ ts → Prop
| nil : WfArgs Δ .nil .nil
| cons {t : L.Tp} {ts : List L.Tp} {x₁ : V₁ t} {x₂ : V₂ t} {xs₁ : HList V₁ ts}
    {xs₂ : HList V₂ ts} :
    ⟨t, x₁, x₂⟩ ∈ Δ → WfArgs Δ xs₁ xs₂ → WfArgs Δ (.cons x₁ xs₁) (.cons x₂ xs₂)

/-- Two instantiations of an expression with the same shape, whose variables
correspond by `Δ` and by the binders they are under. -/
inductive Expr.Wf : {γ : L.Ctx} → {o : L.Tp} → WfCtx L V₁ V₂ →
    Expr L V₁ γ o → Expr L V₂ γ o → Prop
| ret {γ o Δ} {x₁ : V₁ o} {x₂ : V₂ o} :
    ⟨o, x₁, x₂⟩ ∈ Δ → Wf (γ := γ) Δ (.ret x₁) (.ret x₂)
| lit {γ o Δ} {tp : L.AbiTp} {v : tp.val.Lit} {k₁ : V₁ tp.val → Expr L V₁ γ o}
    {k₂ : V₂ tp.val → Expr L V₂ γ o} :
    (∀ x₁ x₂, Wf (⟨tp.val, x₁, x₂⟩ :: Δ) (k₁ x₁) (k₂ x₂)) →
    Wf Δ (.lit tp v k₁) (.lit tp v k₂)
| builtin {γ o Δ inp out} {b : Builtin L inp out} {a₁ : HList V₁ inp} {a₂ : HList V₂ inp}
    {k₁ : V₁ out → Expr L V₁ γ o} {k₂ : V₂ out → Expr L V₂ γ o} :
    WfArgs Δ a₁ a₂ → (∀ x₁ x₂, Wf (⟨out, x₁, x₂⟩ :: Δ) (k₁ x₁) (k₂ x₂)) →
    Wf Δ (.builtin b a₁ k₁) (.builtin b a₂ k₂)
| lam {γ o Δ inp out} {b₁ : V₁ inp → Expr L V₁ γ out} {b₂ : V₂ inp → Expr L V₂ γ out}
    {k₁ : V₁ (.fn inp out) → Expr L V₁ γ o} {k₂ : V₂ (.fn inp out) → Expr L V₂ γ o} :
    (∀ x₁ x₂, Wf (⟨inp, x₁, x₂⟩ :: Δ) (b₁ x₁) (b₂ x₂)) →
    (∀ f₁ f₂, Wf (⟨.fn inp out, f₁, f₂⟩ :: Δ) (k₁ f₁) (k₂ f₂)) →
    Wf Δ (.lam b₁ k₁) (.lam b₂ k₂)
| app {γ o Δ inp out} {f₁ : V₁ (.fn inp out)} {f₂ : V₂ (.fn inp out)} {x₁ : V₁ inp}
    {x₂ : V₂ inp} {k₁ : V₁ out → Expr L V₁ γ o} {k₂ : V₂ out → Expr L V₂ γ o} :
    ⟨.fn inp out, f₁, f₂⟩ ∈ Δ → ⟨inp, x₁, x₂⟩ ∈ Δ →
    (∀ r₁ r₂, Wf (⟨out, r₁, r₂⟩ :: Δ) (k₁ r₁) (k₂ r₂)) →
    Wf Δ (.app f₁ x₁ k₁) (.app f₂ x₂ k₂)
| ite {γ o Δ out} {c₁ : V₁ .bool} {c₂ : V₂ .bool} {t₁ e₁ : Expr L V₁ γ out}
    {t₂ e₂ : Expr L V₂ γ out} {k₁ : V₁ out → Expr L V₁ γ o} {k₂ : V₂ out → Expr L V₂ γ o} :
    ⟨.bool, c₁, c₂⟩ ∈ Δ → Wf Δ t₁ t₂ → Wf Δ e₁ e₂ →
    (∀ r₁ r₂, Wf (⟨out, r₁, r₂⟩ :: Δ) (k₁ r₁) (k₂ r₂)) →
    Wf Δ (.ite c₁ t₁ e₁ k₁) (.ite c₂ t₂ e₂ k₂)
| loop {γ o Δ c} {b₁ : V₁ c → Expr L V₁ γ (.prod c .bool)}
    {b₂ : V₂ c → Expr L V₂ γ (.prod c .bool)} {i₁ : V₁ c} {i₂ : V₂ c}
    {k₁ : V₁ c → Expr L V₁ γ o} {k₂ : V₂ c → Expr L V₂ γ o} :
    ⟨c, i₁, i₂⟩ ∈ Δ → (∀ x₁ x₂, Wf (⟨c, x₁, x₂⟩ :: Δ) (b₁ x₁) (b₂ x₂)) →
    (∀ r₁ r₂, Wf (⟨c, r₁, r₂⟩ :: Δ) (k₁ r₁) (k₂ r₂)) →
    Wf Δ (.loop b₁ i₁ k₁) (.loop b₂ i₂ k₂)
| op {γ o Δ} {e : L.Op γ} {i₁ : V₁ (L.input γ e).val} {i₂ : V₂ (L.input γ e).val}
    {bl₁ : (b : L.Block γ e) → V₁ (L.blockInputs γ e b).val →
      Expr L V₁ (L.blockCtx γ e b) (L.blockOutputs γ e b).val}
    {bl₂ : (b : L.Block γ e) → V₂ (L.blockInputs γ e b).val →
      Expr L V₂ (L.blockCtx γ e b) (L.blockOutputs γ e b).val}
    {k₁ : V₁ (L.output γ e).val → Expr L V₁ γ o} {k₂ : V₂ (L.output γ e).val → Expr L V₂ γ o} :
    ⟨(L.input γ e).val, i₁, i₂⟩ ∈ Δ →
    (∀ b x₁ x₂, Wf (⟨(L.blockInputs γ e b).val, x₁, x₂⟩ :: Δ) (bl₁ b x₁) (bl₂ b x₂)) →
    (∀ r₁ r₂, Wf (⟨(L.output γ e).val, r₁, r₂⟩ :: Δ) (k₁ r₁) (k₂ r₂)) →
    Wf Δ (.op e i₁ bl₁ k₁) (.op e i₂ bl₂ k₂)

/-- Well-formedness of programs, with the definitions in scope in `Δ`. -/
inductive Program.WfIn {mainCtx : L.Ctx} {iT oT : L.AbiTp} :
    WfCtx L V₁ V₂ → Program L mainCtx iT oT V₁ → Program L mainCtx iT oT V₂ → Prop
| define {Δ γ inp out} {body₁ : V₁ (.fn inp out) → V₁ inp → Expr L V₁ γ out}
    {body₂ : V₂ (.fn inp out) → V₂ inp → Expr L V₂ γ out}
    {k₁ : V₁ (.fn inp out) → Program L mainCtx iT oT V₁}
    {k₂ : V₂ (.fn inp out) → Program L mainCtx iT oT V₂} :
    (∀ f₁ f₂ x₁ x₂, Expr.Wf (⟨inp, x₁, x₂⟩ :: ⟨.fn inp out, f₁, f₂⟩ :: Δ)
      (body₁ f₁ x₁) (body₂ f₂ x₂)) →
    (∀ f₁ f₂, WfIn (⟨.fn inp out, f₁, f₂⟩ :: Δ) (k₁ f₁) (k₂ f₂)) →
    WfIn Δ (.define body₁ k₁) (.define body₂ k₂)
| main {Δ} {body₁ : V₁ iT.val → Expr L V₁ mainCtx oT.val}
    {body₂ : V₂ iT.val → Expr L V₂ mainCtx oT.val} :
    (∀ x₁ x₂, Expr.Wf (⟨iT.val, x₁, x₂⟩ :: Δ) (body₁ x₁) (body₂ x₂)) →
    WfIn Δ (.main body₁) (.main body₂)

/-- A program is well-formed when any two of its instantiations are. -/
def Program.Wf {mainCtx : L.Ctx} {iT oT : L.AbiTp}
    (p : ∀ {V : L.Tp → Type}, Program L mainCtx iT oT V) : Prop :=
  ∀ (V₁ V₂ : L.Tp → Type), Program.WfIn [] (p (V := V₁)) (p (V := V₂))

/-! ## Weakening -/

theorem WfArgs.weaken {Δ Δ' : WfCtx L V₁ V₂} (hΔ : ∀ x ∈ Δ, x ∈ Δ') {ts : List L.Tp}
    {a₁ : HList V₁ ts} {a₂ : HList V₂ ts} (h : WfArgs Δ a₁ a₂) : WfArgs Δ' a₁ a₂ := by
  induction h with
  | nil => exact .nil
  | cons hx _ ih => exact .cons (hΔ _ hx) ih

private theorem cons_sub {Δ Δ' : WfCtx L V₁ V₂} (hΔ : ∀ x ∈ Δ, x ∈ Δ') (y : Σ t : L.Tp, V₁ t × V₂ t) :
    ∀ x ∈ y :: Δ, x ∈ y :: Δ' := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (hΔ _ hx)

theorem Expr.Wf.weaken {γ : L.Ctx} {o : L.Tp} {Δ Δ' : WfCtx L V₁ V₂}
    {e₁ : Expr L V₁ γ o} {e₂ : Expr L V₂ γ o} (h : Expr.Wf Δ e₁ e₂)
    (hΔ : ∀ x ∈ Δ, x ∈ Δ') : Expr.Wf Δ' e₁ e₂ := by
  induction h generalizing Δ' with
  | ret hx => exact .ret (hΔ _ hx)
  | lit _ ih => exact .lit fun x₁ x₂ => ih x₁ x₂ (cons_sub hΔ _)
  | builtin ha _ ih => exact .builtin (ha.weaken hΔ) fun x₁ x₂ => ih x₁ x₂ (cons_sub hΔ _)
  | lam _ _ ihb ihk =>
    exact .lam (fun x₁ x₂ => ihb x₁ x₂ (cons_sub hΔ _)) fun f₁ f₂ => ihk f₁ f₂ (cons_sub hΔ _)
  | app hf hx _ ih => exact .app (hΔ _ hf) (hΔ _ hx) fun r₁ r₂ => ih r₁ r₂ (cons_sub hΔ _)
  | ite hc _ _ _ iht ihe ihk =>
    exact .ite (hΔ _ hc) (iht hΔ) (ihe hΔ) fun r₁ r₂ => ihk r₁ r₂ (cons_sub hΔ _)
  | loop hi _ _ ihb ihk =>
    exact .loop (hΔ _ hi) (fun x₁ x₂ => ihb x₁ x₂ (cons_sub hΔ _))
      fun r₁ r₂ => ihk r₁ r₂ (cons_sub hΔ _)
  | op hi _ _ ihb ihk =>
    exact .op (hΔ _ hi) (fun b x₁ x₂ => ihb b x₁ x₂ (cons_sub hΔ _))
      fun r₁ r₂ => ihk r₁ r₂ (cons_sub hΔ _)

/-! ## Proving well-formedness -/

/-- Proves `Program.Wf p` for a concrete program `p`, after unfolding the
given definitions: by its constructors, with every binder introduced and every
variable found in scope. Blocks of operations without blocks are discharged by
their empty tag type. -/
syntax "ast_wf" ("[" ident,* "]")? : tactic

macro_rules
  | `(tactic| ast_wf) => `(tactic| ast_wf [])
  | `(tactic| ast_wf [$ds,*]) => `(tactic| (
      intro V₁ V₂
      simp only [$[$ds:ident],*]
      repeat' (first
        | intro _
        | exact List.Mem.head _
        | apply List.Mem.tail
        | constructor
        | (rename_i b _ _; cases b; done))))

end Freigen.Ast
