import Freigen.Ast.JoinPoints
import Freigen.Ast.Wf
import Freigen.Ast.Eval
import Freigen.CompM.Eutt

/-!
What join-point elimination preserves. `JP` relates an expression to its
translation, syntactically: by congruence, except that a join point `lam b k`
is related to the translation of its scope, in which the join point's tail
calls are related to the translation `κ` of its body. Related programs are
equivalent up to silent steps (`Program.JP.eutt`).

The proof is a simulation between the two evaluators' machine states (`SR`).
The source allocates the join point's closure, which the translation does
not, so references are related by a relation `ρ` that grows as both sides
allocate other closures, and values by `ρ` at function types (`VRel`). A
continuation pair is related by the mode of the expression it continues
(`KR`): normally, on related values. In the scope of a join point, the source
continuation receives the join point's result, the translation's what `κ`
returns, and calling the join point in the source is related to running `κ`
in the translation. In a branch of that scope, the translation's continuation
runs `κ` after the branch: there, calling the join point in the source is
related to returning in the translation.

The source takes more silent steps (the closure, the call, and returns into
continuations of the form `fun r => ret r`), never fewer, so the simulation
skips steps only on the source's side, except for returns, which it may skip
on either. `Pad` records the returns a source continuation has accumulated.
-/

namespace Freigen.Ast.JoinPoints

variable {L : Language}

/-! ## The relation -/

section Relation

variable {V : L.Tp → Type}

/-- Relation modes: normal, or in the scope of the join point `j`, whose tail
calls are related to `κ`. -/
inductive RMode (V : L.Tp → Type) (γ : L.Ctx) : L.Tp → L.Tp → Type
| normal {o : L.Tp} : RMode V γ o o
| jump {o o' τ : L.Tp} (j : V (.fn τ o)) (κ : V τ → Expr L V γ o') : RMode V γ o o'

mutual

/-- An expression and its translation, in a mode, with corresponding
variables in `Δ`. -/
inductive JP : {γ : L.Ctx} → {o o' : L.Tp} → WfCtx L V V → RMode V γ o o' →
    Expr L V γ o → Expr L V γ o' → Prop
| sync {γ o o' Δ} {m : RMode V γ o o'} {e₁ : Expr L V γ o} {e₂ : Expr L V γ o'} :
    JPs Δ m e₁ e₂ → JP Δ m e₁ e₂
/-- A join point: its scope is related in its own mode to the translation, and
its body in the current mode to `κ`. -/
| elim {γ o o' Δ} {m : RMode V γ o o'} {τ : L.Tp} {b : V τ → Expr L V γ o}
    {k : V (.fn τ o) → Expr L V γ o} {κ : V τ → Expr L V γ o'} {e₂ : Expr L V γ o'} :
    (∀ y₁ y₂, JP (⟨τ, y₁, y₂⟩ :: Δ) m (b y₁) (κ y₂)) →
    (∀ j, JP Δ (.jump j κ) (k j) e₂) →
    JP Δ m (.lam b k) e₂
/-- A tail call of the join point. -/
| jump {γ o o' Δ τ} {j : V (.fn τ o)} {κ : V τ → Expr L V γ o'} {y₁ y₂ : V τ} :
    ⟨τ, y₁, y₂⟩ ∈ Δ → JP Δ (.jump j κ) (.app j y₁ fun r => .ret r) (κ y₂)

/-- Nodes that the source and the translation both evaluate in one step. -/
inductive JPs : {γ : L.Ctx} → {o o' : L.Tp} → WfCtx L V V → RMode V γ o o' →
    Expr L V γ o → Expr L V γ o' → Prop
| ret {γ o Δ} {x₁ x₂ : V o} :
    ⟨o, x₁, x₂⟩ ∈ Δ → JPs (γ := γ) Δ .normal (.ret x₁) (.ret x₂)
| lit {γ o o' Δ} {m : RMode V γ o o'} {tp : L.AbiTp} {v : tp.val.Lit}
    {k₁ : V tp.val → Expr L V γ o} {k₂ : V tp.val → Expr L V γ o'} :
    (∀ x₁ x₂, JP (⟨tp.val, x₁, x₂⟩ :: Δ) m (k₁ x₁) (k₂ x₂)) →
    JPs Δ m (.lit tp v k₁) (.lit tp v k₂)
| builtin {γ o o' Δ} {m : RMode V γ o o'} {inp out} {b : Builtin L inp out}
    {a₁ a₂ : HList V inp} {k₁ : V out → Expr L V γ o} {k₂ : V out → Expr L V γ o'} :
    WfArgs Δ a₁ a₂ → (∀ x₁ x₂, JP (⟨out, x₁, x₂⟩ :: Δ) m (k₁ x₁) (k₂ x₂)) →
    JPs Δ m (.builtin b a₁ k₁) (.builtin b a₂ k₂)
| lam {γ o o' Δ} {m : RMode V γ o o'} {inp out} {b₁ b₂ : V inp → Expr L V γ out}
    {k₁ : V (.fn inp out) → Expr L V γ o} {k₂ : V (.fn inp out) → Expr L V γ o'} :
    (∀ x₁ x₂, JP (⟨inp, x₁, x₂⟩ :: Δ) .normal (b₁ x₁) (b₂ x₂)) →
    (∀ f₁ f₂, JP (⟨.fn inp out, f₁, f₂⟩ :: Δ) m (k₁ f₁) (k₂ f₂)) →
    JPs Δ m (.lam b₁ k₁) (.lam b₂ k₂)
| app {γ o o' Δ} {m : RMode V γ o o'} {inp out} {f₁ f₂ : V (.fn inp out)} {x₁ x₂ : V inp}
    {k₁ : V out → Expr L V γ o} {k₂ : V out → Expr L V γ o'} :
    ⟨.fn inp out, f₁, f₂⟩ ∈ Δ → ⟨inp, x₁, x₂⟩ ∈ Δ →
    (∀ r₁ r₂, JP (⟨out, r₁, r₂⟩ :: Δ) m (k₁ r₁) (k₂ r₂)) →
    JPs Δ m (.app f₁ x₁ k₁) (.app f₂ x₂ k₂)
| ite {γ o o' Δ} {m : RMode V γ o o'} {out} {c₁ c₂ : V .bool} {t₁ e₁ t₂ e₂ : Expr L V γ out}
    {k₁ : V out → Expr L V γ o} {k₂ : V out → Expr L V γ o'} :
    ⟨.bool, c₁, c₂⟩ ∈ Δ → JP Δ .normal t₁ t₂ → JP Δ .normal e₁ e₂ →
    (∀ r₁ r₂, JP (⟨out, r₁, r₂⟩ :: Δ) m (k₁ r₁) (k₂ r₂)) →
    JPs Δ m (.ite c₁ t₁ e₁ k₁) (.ite c₂ t₂ e₂ k₂)
/-- A branch returning to the join point's scope: its paths call the join
point, and the translation's continuation is `κ`. -/
| iteJump {γ o o' Δ τ} {j : V (.fn τ o)} {κ : V τ → Expr L V γ o'} {c₁ c₂ : V .bool}
    {t₁ e₁ : Expr L V γ o} {t₂ e₂ : Expr L V γ τ} :
    ⟨.bool, c₁, c₂⟩ ∈ Δ → JP Δ (.jump j fun v => .ret v) t₁ t₂ →
    JP Δ (.jump j fun v => .ret v) e₁ e₂ →
    JPs Δ (.jump j κ) (.ite c₁ t₁ e₁ fun r => .ret r) (.ite c₂ t₂ e₂ κ)
| loop {γ o o' Δ} {m : RMode V γ o o'} {c} {b₁ b₂ : V c → Expr L V γ (.prod c .bool)}
    {i₁ i₂ : V c} {k₁ : V c → Expr L V γ o} {k₂ : V c → Expr L V γ o'} :
    ⟨c, i₁, i₂⟩ ∈ Δ → (∀ x₁ x₂, JP (⟨c, x₁, x₂⟩ :: Δ) .normal (b₁ x₁) (b₂ x₂)) →
    (∀ r₁ r₂, JP (⟨c, r₁, r₂⟩ :: Δ) m (k₁ r₁) (k₂ r₂)) →
    JPs Δ m (.loop b₁ i₁ k₁) (.loop b₂ i₂ k₂)
| op {γ o o' Δ} {m : RMode V γ o o'} {e : L.Op γ} {i₁ i₂ : V (L.input γ e).val}
    {bl₁ bl₂ : (b : L.Block γ e) → V (L.blockInputs γ e b).val →
      Expr L V (L.blockCtx γ e b) (L.blockOutputs γ e b).val}
    {k₁ : V (L.output γ e).val → Expr L V γ o} {k₂ : V (L.output γ e).val → Expr L V γ o'} :
    ⟨(L.input γ e).val, i₁, i₂⟩ ∈ Δ →
    (∀ b x₁ x₂, JP (⟨(L.blockInputs γ e b).val, x₁, x₂⟩ :: Δ) .normal (bl₁ b x₁) (bl₂ b x₂)) →
    (∀ r₁ r₂, JP (⟨(L.output γ e).val, r₁, r₂⟩ :: Δ) m (k₁ r₁) (k₂ r₂)) →
    JPs Δ m (.op e i₁ bl₁ k₁) (.op e i₂ bl₂ k₂)

end

/-- A program and its translation: definitions by congruence. -/
inductive Program.JP {mainCtx : L.Ctx} {iT oT : L.AbiTp} :
    WfCtx L V V → Program L mainCtx iT oT V → Program L mainCtx iT oT V → Prop
| define {Δ γ inp out} {body₁ body₂ : V (.fn inp out) → V inp → Expr L V γ out}
    {k₁ k₂ : V (.fn inp out) → Program L mainCtx iT oT V} :
    (∀ f₁ f₂ x₁ x₂, JoinPoints.JP (⟨inp, x₁, x₂⟩ :: ⟨.fn inp out, f₁, f₂⟩ :: Δ) .normal
      (body₁ f₁ x₁) (body₂ f₂ x₂)) →
    (∀ f₁ f₂, Program.JP (⟨.fn inp out, f₁, f₂⟩ :: Δ) (k₁ f₁) (k₂ f₂)) →
    Program.JP Δ (.define body₁ k₁) (.define body₂ k₂)
| main {Δ} {body₁ body₂ : V iT.val → Expr L V mainCtx oT.val} :
    (∀ x₁ x₂, JoinPoints.JP (⟨iT.val, x₁, x₂⟩ :: Δ) .normal (body₁ x₁) (body₂ x₂)) →
    Program.JP Δ (.main body₁) (.main body₂)

theorem cons_sub {Δ Δ' : WfCtx L V V} (hΔ : ∀ x ∈ Δ, x ∈ Δ')
    (y : Σ t : L.Tp, V t × V t) : ∀ x ∈ y :: Δ, x ∈ y :: Δ' := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (hΔ _ hx)

mutual

theorem JP.weaken {γ : L.Ctx} {o o' : L.Tp} {Δ Δ' : WfCtx L V V} {m : RMode V γ o o'}
    {e₁ : Expr L V γ o} {e₂ : Expr L V γ o'} :
    JP Δ m e₁ e₂ → (∀ x ∈ Δ, x ∈ Δ') → JP Δ' m e₁ e₂
  | JP.sync s, h => .sync (JPs.weaken s h)
  | JP.elim hb hk, h =>
    .elim (fun y₁ y₂ => JP.weaken (hb y₁ y₂) (cons_sub h _)) fun j => JP.weaken (hk j) h
  | JP.jump hy, h => .jump (h _ hy)

theorem JPs.weaken {γ : L.Ctx} {o o' : L.Tp} {Δ Δ' : WfCtx L V V} {m : RMode V γ o o'}
    {e₁ : Expr L V γ o} {e₂ : Expr L V γ o'} :
    JPs Δ m e₁ e₂ → (∀ x ∈ Δ, x ∈ Δ') → JPs Δ' m e₁ e₂
  | .ret hx, h => .ret (h _ hx)
  | .lit hk, h => .lit fun x₁ x₂ => JP.weaken (hk x₁ x₂) (cons_sub h _)
  | .builtin ha hk, h => .builtin (ha.weaken h) fun x₁ x₂ => JP.weaken (hk x₁ x₂) (cons_sub h _)
  | .lam hb hk, h =>
    .lam (fun x₁ x₂ => JP.weaken (hb x₁ x₂) (cons_sub h _))
      fun f₁ f₂ => JP.weaken (hk f₁ f₂) (cons_sub h _)
  | .app hf hx hk, h =>
    .app (h _ hf) (h _ hx) fun r₁ r₂ => JP.weaken (hk r₁ r₂) (cons_sub h _)
  | .ite hc ht he hk, h =>
    .ite (h _ hc) (JP.weaken ht h) (JP.weaken he h) fun r₁ r₂ => JP.weaken (hk r₁ r₂) (cons_sub h _)
  | .iteJump hc ht he, h => .iteJump (h _ hc) (JP.weaken ht h) (JP.weaken he h)
  | .loop hi hb hk, h =>
    .loop (h _ hi) (fun x₁ x₂ => JP.weaken (hb x₁ x₂) (cons_sub h _))
      fun r₁ r₂ => JP.weaken (hk r₁ r₂) (cons_sub h _)
  | .op hi hb hk, h =>
    .op (h _ hi) (fun b x₁ x₂ => JP.weaken (hb b x₁ x₂) (cons_sub h _))
      fun r₁ r₂ => JP.weaken (hk r₁ r₂) (cons_sub h _)

end

end Relation

/-! ## Values and heaps -/

variable {M : L.Model}

/-- Types without functions, whose values contain no references. -/
def _root_.Freigen.Ast.Tp.FnFree {B : Type} : Ast.Tp B → Prop
  | .base _ => True
  | .uInt32 => True
  | .bool => True
  | .unit => True
  | .array t => t.FnFree
  | .prod a b => a.FnFree ∧ b.FnFree
  | .fn _ _ => False

theorem _root_.Freigen.Ast.IsAbiTp.fnFree {B : Type} {abi : B → Bool} {t : Ast.Tp B}
    (h : IsAbiTp abi t) : t.FnFree := by
  induction h with
  | base _ | uInt32 | bool | unit => trivial
  | array _ ih => exact ih
  | prod _ _ iha ihb => exact ⟨iha, ihb⟩

/-- Primitives neither take nor return references. The models of such
languages cannot observe how references are numbered. -/
def _root_.Freigen.Ast.Language.PrimFnFree (L : Language) : Prop :=
  ∀ {inp : List L.Tp} {out : L.Tp}, L.Prim inp out → (∀ t ∈ inp, t.FnFree) ∧ out.FnFree

/-- References related across the two heaps. -/
abbrev Refs := FnRef → FnRef → Prop

/-- Values related at a type: equal, except for references, related by `ρ`. -/
def VRel (ρ : Refs) : (t : L.Tp) → M.V t → M.V t → Prop
  | .base _, x, y => x = y
  | .uInt32, x, y => x = y
  | .bool, x, y => x = y
  | .unit, _, _ => True
  | .array t, xs, ys =>
    xs.size = ys.size ∧ ∀ i (h₁ : i < xs.size) (h₂ : i < ys.size), VRel ρ t xs[i] ys[i]
  | .prod a b, x, y => VRel ρ a x.1 y.1 ∧ VRel ρ b x.2 y.2
  | .fn _ _, f, g => ρ f g

theorem VRel.mono {ρ ρ' : Refs} (hρ : ∀ a b, ρ a b → ρ' a b) :
    ∀ {t : L.Tp} {x y : M.V t}, VRel ρ t x y → VRel ρ' t x y
  | .base _, _, _, h | .uInt32, _, _, h | .bool, _, _, h | .unit, _, _, h => h
  | .array _, _, _, ⟨hs, h⟩ => ⟨hs, fun i h₁ h₂ => VRel.mono hρ (h i h₁ h₂)⟩
  | .prod _ _, _, _, ⟨ha, hb⟩ => ⟨VRel.mono hρ ha, VRel.mono hρ hb⟩
  | .fn _ _, _, _, h => hρ _ _ h

/-- At types without functions, related values are equal. -/
theorem VRel.iff_eq {ρ : Refs} : ∀ {t : L.Tp}, t.FnFree → ∀ {x y : M.V t},
    VRel ρ t x y ↔ x = y
  | .base _, _, _, _ | .uInt32, _, _, _ | .bool, _, _, _ => Iff.rfl
  | .unit, _, _, _ => ⟨fun _ => rfl, fun _ => trivial⟩
  | .array t, h, xs, ys => by
    refine ⟨fun ⟨hs, hx⟩ => Array.ext hs fun i h₁ h₂ =>
      (VRel.iff_eq (t := t) h).mp (hx i h₁ h₂), ?_⟩
    rintro rfl
    exact ⟨rfl, fun i h₁ _ => (VRel.iff_eq (t := t) h).mpr rfl⟩
  | .prod _ _, ⟨ha, hb⟩, x, y => by
    rw [show VRel ρ (.prod _ _) x y = (VRel ρ _ x.1 y.1 ∧ VRel ρ _ x.2 y.2) from rfl,
      VRel.iff_eq ha, VRel.iff_eq hb]
    exact ⟨fun ⟨h₁, h₂⟩ => Prod.ext h₁ h₂, fun h => h ▸ ⟨rfl, rfl⟩⟩
  | .fn _ _, h, _, _ => h.elim

theorem VRel.refl_abi {ρ : Refs} {t : L.AbiTp} (x : M.V t.val) : VRel ρ t.val x x :=
  (VRel.iff_eq t.property.fnFree).mpr rfl

theorem VRel.eq_abi {ρ : Refs} {t : L.AbiTp} {x y : M.V t.val} (h : VRel ρ t.val x y) : x = y :=
  (VRel.iff_eq t.property.fnFree).mp h

/-- Arguments, pairwise related. -/
def VArgs (ρ : Refs) : {ts : List L.Tp} → HList M.V ts → HList M.V ts → Prop
  | [], .nil, .nil => True
  | _ :: _, .cons x xs, .cons y ys => VRel ρ _ x y ∧ VArgs ρ xs ys

theorem VArgs.iff_eq {ρ : Refs} : ∀ {ts : List L.Tp}, (∀ t ∈ ts, t.FnFree) →
    ∀ {xs ys : HList M.V ts}, VArgs ρ xs ys ↔ xs = ys
  | [], _, .nil, .nil => ⟨fun _ => rfl, fun _ => trivial⟩
  | _ :: _, h, .cons x xs, .cons y ys => by
    rw [show VArgs ρ (.cons x xs) (.cons y ys) = (VRel ρ _ x y ∧ VArgs ρ xs ys) from rfl,
      VRel.iff_eq (h _ List.mem_cons_self), VArgs.iff_eq fun t ht => h t (List.mem_cons_of_mem _ ht)]
    exact ⟨fun ⟨h₁, h₂⟩ => h₁ ▸ h₂ ▸ rfl, fun h => by cases h; exact ⟨rfl, rfl⟩⟩

/-- Builtins map related arguments to related results, and fail together. -/
theorem Builtin.denote_rel (hprim : L.PrimFnFree) {ρ : Refs} {inp : List L.Tp} {out : L.Tp}
    (b : Builtin L inp out) {a₁ a₂ : HList M.V inp} (ha : VArgs ρ a₁ a₂) :
    Option.Rel (VRel ρ out) (b.denote M a₁) (b.denote M a₂) := by
  cases b with
  | prim p =>
    obtain ⟨hi, ho⟩ := hprim p
    cases (VArgs.iff_eq hi).mp ha
    rcases h : Builtin.denote M (.prim p) a₁ with _ | r
    · exact .none
    · exact .some ((VRel.iff_eq ho).mpr rfl)
  | pair =>
    rcases a₁ with _ | ⟨x₁, _ | ⟨y₁, _ | _⟩⟩
    rcases a₂ with _ | ⟨x₂, _ | ⟨y₂, _ | _⟩⟩
    exact .some ⟨ha.1, ha.2.1⟩
  | fst =>
    rcases a₁ with _ | ⟨p₁, _ | _⟩
    rcases a₂ with _ | ⟨p₂, _ | _⟩
    exact .some ha.1.1
  | snd =>
    rcases a₁ with _ | ⟨p₁, _ | _⟩
    rcases a₂ with _ | ⟨p₂, _ | _⟩
    exact .some ha.1.2
  | arrEmpty =>
    cases a₁
    cases a₂
    exact .some (show VRel ρ (.array _) #[] #[] from
      ⟨rfl, fun i h => (Nat.not_lt_zero _ h).elim⟩)
  | arrPush =>
    rcases a₁ with _ | ⟨xs, _ | ⟨x, _ | _⟩⟩
    rcases a₂ with _ | ⟨ys, _ | ⟨y, _ | _⟩⟩
    obtain ⟨⟨hs, hxs⟩, hx, _⟩ := ha
    refine .some ⟨by simp [hs], fun i h₁ h₂ => ?_⟩
    simp only [Array.size_push] at h₁ h₂ ⊢
    rw [Array.getElem_push, Array.getElem_push]
    by_cases hi : i < xs.size
    · rw [dif_pos hi, dif_pos (hs ▸ hi)]
      exact hxs i hi (hs ▸ hi)
    · rw [dif_neg hi, dif_neg (hs ▸ hi)]
      exact hx
  | arrGet =>
    rcases a₁ with _ | ⟨xs, _ | ⟨i, _ | _⟩⟩
    rcases a₂ with _ | ⟨ys, _ | ⟨j, _ | _⟩⟩
    obtain ⟨⟨hs, hxs⟩, hij, _⟩ := ha
    cases (hij : i = j)
    simp only [Builtin.denote]
    by_cases hi : i.toNat < xs.size
    · rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem (hs ▸ hi)]
      exact .some (hxs _ hi (hs ▸ hi))
    · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hi),
        Array.getElem?_eq_none (hs ▸ Nat.le_of_not_lt hi)]
      exact .none
  | arrSet =>
    rcases a₁ with _ | ⟨xs, _ | ⟨i, _ | ⟨x, _ | _⟩⟩⟩
    rcases a₂ with _ | ⟨ys, _ | ⟨j, _ | ⟨y, _ | _⟩⟩⟩
    obtain ⟨⟨hs, hxs⟩, hij, hx, _⟩ := ha
    cases (hij : i = j)
    simp only [Builtin.denote]
    by_cases hi : i.toNat < xs.size
    · rw [dif_pos hi, dif_pos (hs ▸ hi)]
      refine .some ⟨by simp [hs], fun k h₁ h₂ => ?_⟩
      simp only [Array.getElem_set]
      by_cases hk : i.toNat = k
      · rw [if_pos hk, if_pos hk]
        exact hx
      · rw [if_neg hk, if_neg hk]
        exact hxs k (by simpa using h₁) (by simpa using h₂)
    · rw [dif_neg hi, dif_neg (hs ▸ hi)]
      exact .none
  | arrLen =>
    rcases a₁ with _ | ⟨xs, _ | _⟩
    rcases a₂ with _ | ⟨ys, _ | _⟩
    obtain ⟨⟨hs, _⟩, _⟩ := ha
    exact .some (by simp only [hs]; rfl)
  | uAdd | uSub | uMul | uDiv | uMod | uEq | uLt | uLe | and | or | bEq =>
    rcases a₁ with _ | ⟨x₁, _ | ⟨y₁, _ | _⟩⟩
    rcases a₂ with _ | ⟨x₂, _ | ⟨y₂, _ | _⟩⟩
    obtain ⟨hx, hy, _⟩ := ha
    cases (hx : x₁ = x₂)
    cases (hy : y₁ = y₂)
    exact .some rfl
  | not =>
    rcases a₁ with _ | ⟨x₁, _ | _⟩
    rcases a₂ with _ | ⟨x₂, _ | _⟩
    obtain ⟨hx, _⟩ := ha
    cases (hx : x₁ = x₂)
    exact .some rfl

/-- Variables in scope, related. -/
def VRelCtx (ρ : Refs) (Δ : WfCtx L M.V M.V) : Prop :=
  ∀ x ∈ Δ, VRel ρ x.1 x.2.1 x.2.2

theorem VRelCtx.mono {ρ ρ' : Refs} (hρ : ∀ a b, ρ a b → ρ' a b) {Δ : WfCtx L M.V M.V}
    (h : VRelCtx ρ Δ) : VRelCtx ρ' Δ :=
  fun x hx => VRel.mono hρ (h x hx)

theorem VRelCtx.cons {ρ : Refs} {Δ : WfCtx L M.V M.V} (h : VRelCtx ρ Δ) {t : L.Tp}
    {x y : M.V t} (hxy : VRel ρ t x y) : VRelCtx ρ (⟨t, x, y⟩ :: Δ) := by
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact hxy
  · exact h z hz

theorem VRelCtx.args {ρ : Refs} {Δ : WfCtx L M.V M.V} (h : VRelCtx ρ Δ) {ts : List L.Tp}
    {a₁ a₂ : HList M.V ts} (ha : WfArgs Δ a₁ a₂) : VArgs ρ a₁ a₂ := by
  induction ha with
  | nil => trivial
  | cons hx _ ih => exact ⟨h _ hx, ih⟩

/-- Related references resolve to related closures, at the same types. -/
def HRel (ρ : Refs) (h₁ h₂ : Heap L M) : Prop :=
  ∀ r₁ r₂, ρ r₁ r₂ → ∃ (γ : L.Ctx) (i o : L.Tp) (g₁ g₂ : M.V i → Expr L M.V γ o),
    h₁.lookup r₁ = some g₁ ∧ h₂.lookup r₂ = some g₂ ∧
    ∃ Δ, VRelCtx ρ Δ ∧ ∀ x₁ x₂, JP (⟨i, x₁, x₂⟩ :: Δ) .normal (g₁ x₁) (g₂ x₂)

theorem HRel.mono {ρ : Refs} {h₁ h₂ h₁' h₂' : Heap L M} (h : HRel ρ h₁ h₂) (hle₁ : h₁ ≤ h₁')
    (hle₂ : h₂ ≤ h₂') : HRel ρ h₁' h₂' := by
  intro r₁ r₂ hr
  obtain ⟨γ, i, o, g₁, g₂, hg₁, hg₂, hb⟩ := h r₁ r₂ hr
  exact ⟨γ, i, o, g₁, g₂, Heap.lookup_mono hle₁ hg₁, Heap.lookup_mono hle₂ hg₂, hb⟩

/-- Allocating related closures on both sides relates their references. -/
theorem HRel.alloc {ρ : Refs} {h₁ h₂ : Heap L M} (h : HRel ρ h₁ h₂) {γ : L.Ctx} {i o : L.Tp}
    (f₁ f₂ : M.V (.fn i o) → M.V i → Expr L M.V γ o) {Δ : WfCtx L M.V M.V}
    (hΔ : VRelCtx (fun a b => ρ a b ∨ a = (h₁.alloc f₁).2 ∧ b = (h₂.alloc f₂).2) Δ)
    (hf : ∀ x₁ x₂, JP (⟨i, x₁, x₂⟩ :: Δ) .normal (f₁ (h₁.alloc f₁).2 x₁) (f₂ (h₂.alloc f₂).2 x₂)) :
    HRel (fun a b => ρ a b ∨ a = (h₁.alloc f₁).2 ∧ b = (h₂.alloc f₂).2)
      (h₁.alloc f₁).1 (h₂.alloc f₂).1 := by
  have hmono : ∀ a b, ρ a b → ρ a b ∨ a = (h₁.alloc f₁).2 ∧ b = (h₂.alloc f₂).2 :=
    fun _ _ h => .inl h
  rintro r₁ r₂ (hr | ⟨rfl, rfl⟩)
  · obtain ⟨γ', i', o', g₁, g₂, hg₁, hg₂, Δ', hΔ', hb⟩ := h r₁ r₂ hr
    exact ⟨γ', i', o', g₁, g₂, Heap.lookup_mono (Heap.le_alloc _ _) hg₁,
      Heap.lookup_mono (Heap.le_alloc _ _) hg₂, Δ', hΔ'.mono hmono, hb⟩
  · exact ⟨γ, i, o, _, _, Heap.lookup_alloc .., Heap.lookup_alloc .., Δ, hΔ, hf⟩

/-! ## The simulation -/

open EvalState

/-- `K'` is `K` after some returns: what a continuation becomes when it is
passed to `ret`-continued calls. -/
inductive Pad {γ : L.Ctx} {R : Type} {o : L.Tp} :
    (Heap L M → M.V o → EvalState L M (γ, R)) → (Heap L M → M.V o → EvalState L M (γ, R)) → Prop
| refl (K : Heap L M → M.V o → EvalState L M (γ, R)) : Pad K K
| step {K K' : Heap L M → M.V o → EvalState L M (γ, R)} :
    Pad K K' → Pad K fun s r => .cont s (.ret r) K'

theorem Pad.trans {γ : L.Ctx} {R : Type} {o : L.Tp}
    {K K' K'' : Heap L M → M.V o → EvalState L M (γ, R)}
    (h : Pad K K') (h' : Pad K' K'') : Pad K K'' := by
  induction h' with
  | refl => exact h
  | step _ ih => exact .step ih

/-- Worlds extending `(ρ, h₁, h₂)`. -/
def Ext (ρ : Refs) (h₁ h₂ : Heap L M) (ρ' : Refs) (h₁' h₂' : Heap L M) : Prop :=
  (∀ a b, ρ a b → ρ' a b) ∧ h₁ ≤ h₁' ∧ h₂ ≤ h₂'

theorem Ext.refl (ρ : Refs) (h₁ h₂ : Heap L M) : Ext ρ h₁ h₂ ρ h₁ h₂ :=
  ⟨fun _ _ h => h, le_rfl, le_rfl⟩

theorem Ext.trans {ρ ρ' ρ'' : Refs} {h₁ h₂ h₁' h₂' h₁'' h₂'' : Heap L M}
    (h : Ext ρ h₁ h₂ ρ' h₁' h₂') (h' : Ext ρ' h₁' h₂' ρ'' h₁'' h₂'') :
    Ext ρ h₁ h₂ ρ'' h₁'' h₂'' :=
  ⟨fun a b hab => h'.1 a b (h.1 a b hab), le_trans h.2.1 h'.2.1, le_trans h.2.2 h'.2.2⟩

mutual

/-- Related machine states. -/
inductive SR : {i : L.Ctx × Type} → EvalState L M i → EvalState L M i → Prop
| done {γ : L.Ctx} {R : Type} (r : R) : SR (.done (γ := γ) r) (.done r)
/-- Returns may be skipped on either side. -/
| tauL {γ : L.Ctx} {R : Type} {t : L.Tp} {h : Heap L M} {v : M.V t}
    {K : Heap L M → M.V t → EvalState L M (γ, R)} {st₂ : EvalState L M (γ, R)} :
    SR (K h v) st₂ → SR (.cont h (.ret v) K) st₂
| tauR {γ : L.Ctx} {R : Type} {t : L.Tp} {h : Heap L M} {v : M.V t}
    {K : Heap L M → M.V t → EvalState L M (γ, R)} {st₁ : EvalState L M (γ, R)} :
    SR st₁ (K h v) → SR st₁ (.cont h (.ret v) K)
/-- The source allocates a join point. -/
| alloc {γ : L.Ctx} {R : Type} {inp out o : L.Tp} {h : Heap L M}
    {b : M.V inp → Expr L M.V γ out} {k : M.V (.fn inp out) → Expr L M.V γ o}
    {K : Heap L M → M.V o → EvalState L M (γ, R)} {st₂ : EvalState L M (γ, R)} :
    SR (.cont (h.alloc fun _ x => b x).1 (k (h.alloc fun _ x => b x).2) K) st₂ →
    SR (.cont h (.lam b k) K) st₂
/-- The source calls a join point. -/
| call {γ : L.Ctx} {R : Type} {inp out o : L.Tp} {h : Heap L M} {f : M.V (.fn inp out)}
    {g : M.V inp → Expr L M.V γ out} {x : M.V inp} {k : M.V out → Expr L M.V γ o}
    {K : Heap L M → M.V o → EvalState L M (γ, R)} {st₂ : EvalState L M (γ, R)} :
    h.lookup f = some g → SR (.cont h (g x) fun s r => .cont s (k r) K) st₂ →
    SR (.cont h (.app f x k) K) st₂
/-- Both sides evaluate related expressions under related continuations. -/
| expr {γ : L.Ctx} {R : Type} {o o' : L.Tp} {m : RMode M.V γ o o'} {Δ : WfCtx L M.V M.V}
    {ρ : Refs} {h₁ h₂ : Heap L M} {e₁ : Expr L M.V γ o} {e₂ : Expr L M.V γ o'}
    {K₁ K₁' : Heap L M → M.V o → EvalState L M (γ, R)}
    {K₂ : Heap L M → M.V o' → EvalState L M (γ, R)} :
    JPs Δ m e₁ e₂ → HRel ρ h₁ h₂ → VRelCtx ρ Δ → KR m ρ h₁ h₂ K₁ K₂ → Pad K₁ K₁' →
    SR (.cont h₁ e₁ K₁') (.cont h₂ e₂ K₂)

/-- Related continuations, in a mode, at the world `(ρ, h₁, h₂)`. -/
inductive KR : {γ : L.Ctx} → {R : Type} → {o o' : L.Tp} → RMode M.V γ o o' → Refs →
    Heap L M → Heap L M → (Heap L M → M.V o → EvalState L M (γ, R)) →
    (Heap L M → M.V o' → EvalState L M (γ, R)) → Prop
/-- On related values, in every extending world. -/
| normal {γ : L.Ctx} {R : Type} {o : L.Tp} {ρ : Refs} {h₁ h₂ : Heap L M}
    {K₁ K₂ : Heap L M → M.V o → EvalState L M (γ, R)} :
    (∀ ρ' h₁' h₂', Ext ρ h₁ h₂ ρ' h₁' h₂' → HRel ρ' h₁' h₂' →
      ∀ v₁ v₂, VRel ρ' o v₁ v₂ → SR (K₁ h₁' v₁) (K₂ h₂' v₂)) →
    KR .normal ρ h₁ h₂ K₁ K₂
/-- In the scope of a join point resolving to `b`: running `b` under the
source continuation is related to running `κ` under the translation's. -/
| scope {γ : L.Ctx} {R : Type} {o o' τ : L.Tp} {ρ : Refs} {h₁ h₂ : Heap L M}
    {j : M.V (.fn τ o)} {κ : M.V τ → Expr L M.V γ o'} {b : M.V τ → Expr L M.V γ o}
    {K₁ : Heap L M → M.V o → EvalState L M (γ, R)}
    {K₂ : Heap L M → M.V o' → EvalState L M (γ, R)} :
    h₁.lookup j = some b →
    (∀ ρ' h₁' h₂', Ext ρ h₁ h₂ ρ' h₁' h₂' → HRel ρ' h₁' h₂' →
      ∀ y₁ y₂, VRel ρ' τ y₁ y₂ → ∀ K₁', Pad K₁ K₁' →
        SR (.cont h₁' (b y₁) K₁') (.cont h₂' (κ y₂) K₂)) →
    KR (.jump j κ) ρ h₁ h₂ K₁ K₂
/-- In a branch of the scope of a join point: the translation's continuation
runs `κ`, after returns. -/
| branch {γ : L.Ctx} {R : Type} {o o' τ : L.Tp} {ρ : Refs} {h₁ h₂ : Heap L M}
    {j : M.V (.fn τ o)} {κ : M.V τ → Expr L M.V γ o'} {b : M.V τ → Expr L M.V γ o}
    {K₁ K₁b : Heap L M → M.V o → EvalState L M (γ, R)}
    {K₂ : Heap L M → M.V o' → EvalState L M (γ, R)}
    {K₂b : Heap L M → M.V τ → EvalState L M (γ, R)} :
    h₁.lookup j = some b →
    (∀ ρ' h₁' h₂', Ext ρ h₁ h₂ ρ' h₁' h₂' → HRel ρ' h₁' h₂' →
      ∀ y₁ y₂, VRel ρ' τ y₁ y₂ → ∀ K₁', Pad K₁ K₁' →
        SR (.cont h₁' (b y₁) K₁') (.cont h₂' (κ y₂) K₂)) →
    Pad K₁ K₁b → Pad (fun s r => .cont s (κ r) K₂) K₂b →
    KR (.jump j fun v => .ret v) ρ h₁ h₂ K₁b K₂b

end

theorem KR.mono {γ : L.Ctx} {R : Type} {o o' : L.Tp} {m : RMode M.V γ o o'} {ρ ρ' : Refs}
    {h₁ h₂ h₁' h₂' : Heap L M} {K₁ : Heap L M → M.V o → EvalState L M (γ, R)}
    {K₂ : Heap L M → M.V o' → EvalState L M (γ, R)} (h : KR m ρ h₁ h₂ K₁ K₂)
    (hext : Ext ρ h₁ h₂ ρ' h₁' h₂') : KR m ρ' h₁' h₂' K₁ K₂ := by
  cases h with
  | normal hk => exact .normal fun ρ'' h₁'' h₂'' he => hk ρ'' h₁'' h₂'' (hext.trans he)
  | scope hl hb =>
    exact .scope (Heap.lookup_mono hext.2.1 hl) fun ρ'' h₁'' h₂'' he => hb ρ'' h₁'' h₂'' (hext.trans he)
  | branch hl hb hp₁ hp₂ =>
    exact .branch (Heap.lookup_mono hext.2.1 hl)
      (fun ρ'' h₁'' h₂'' he => hb ρ'' h₁'' h₂'' (hext.trans he)) hp₁ hp₂

theorem SR.padL {γ : L.Ctx} {R : Type} {o : L.Tp} {K K' : Heap L M → M.V o → EvalState L M (γ, R)}
    (hp : Pad K K') {h : Heap L M} {v : M.V o} {st₂ : EvalState L M (γ, R)}
    (hs : SR (K h v) st₂) : SR (K' h v) st₂ := by
  induction hp with
  | refl => exact hs
  | step _ ih => exact .tauL ih

theorem SR.padR {γ : L.Ctx} {R : Type} {o : L.Tp} {K K' : Heap L M → M.V o → EvalState L M (γ, R)}
    (hp : Pad K K') {h : Heap L M} {v : M.V o} {st₁ : EvalState L M (γ, R)}
    (hs : SR st₁ (K h v)) : SR st₁ (K' h v) := by
  induction hp with
  | refl => exact hs
  | step _ ih => exact .tauR ih

/-- Related expressions, run under related continuations, give related states. -/
theorem build {γ : L.Ctx} {o o' : L.Tp} {Δ : WfCtx L M.V M.V} {m : RMode M.V γ o o'}
    {e₁ : Expr L M.V γ o} {e₂ : Expr L M.V γ o'} (d : JP Δ m e₁ e₂) {R : Type} {ρ : Refs}
    {h₁ h₂ : Heap L M} {K₁ K₁' : Heap L M → M.V o → EvalState L M (γ, R)}
    {K₂ : Heap L M → M.V o' → EvalState L M (γ, R)}
    (hH : HRel ρ h₁ h₂) (hΔ : VRelCtx ρ Δ) (hK : KR m ρ h₁ h₂ K₁ K₂) (hP : Pad K₁ K₁') :
    SR (.cont h₁ e₁ K₁') (.cont h₂ e₂ K₂) :=
  match d with
  | JP.sync s => .expr s hH hΔ hK hP
  | @JP.elim _ _ _ _ _ _ _ _ b _ _ _ hb hk =>
    have hle := Heap.le_alloc h₁ fun _ x => b x
    .alloc <| build (hk _) (hH.mono hle le_rfl) hΔ
      (.scope (Heap.lookup_alloc ..) fun ρ' h₁' h₂' he hH' y₁ y₂ hy K₁x hpad =>
        build (hb y₁ y₂) hH' ((hΔ.mono he.1).cons hy)
          (hK.mono (Ext.trans ⟨fun _ _ h => h, hle, le_rfl⟩ he))
          (hP.trans hpad))
      (.refl _)
  | JP.jump hy => by
    cases hK with
    | scope hl hb =>
      exact .call hl (hb _ _ _ (.refl ..) hH _ _ (hΔ _ hy) _ (.step hP))
    | branch hl hb hp₁ hp₂ =>
      exact .call hl (.tauR (SR.padR hp₂ (hb _ _ _ (.refl ..) hH _ _ (hΔ _ hy) _
        (.step (hp₁.trans hP)))))

end Freigen.Ast.JoinPoints
