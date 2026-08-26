import Freigen.IxPoly.Basic
import Freigen.Eff

namespace Freigen

def ITree
    {Γ : Type u} (E : Γ → Type u) [Eff.Spec E]
    (γ : Γ) (α : Type v) : Type _ :=
  (Eff.Step Γ E).M (γ, α)

namespace ITree

open IxPoly

variable {Γ : Type u} {E : Γ → Type u} [eS : Eff.Spec E]

def corec
    {A : Γ × Type v → Type w}
    (f : (i : Γ × Type v) → A i → Eff.Step Γ E A i) :
    {i : Γ × Type v} → A i → ITree E i.1 i.2 :=
  IxPoly.M.corec f

def observe {γ : Γ} {α : Type v} :
    ITree E γ α ≃ Eff.Step Γ E (fun i => ITree E i.1 i.2) (γ, α) :=
  IxPoly.M.observe

def roll {γ : Γ} {α : Type v} :
    Eff.Step Γ E (fun i => ITree E i.1 i.2) (γ, α) → ITree E γ α :=
  IxPoly.M.observe.symm

theorem observe_roll {γ : Γ} {α : Type v}
    (x : Eff.Step Γ E (fun i => ITree E i.1 i.2) (γ, α)) :
    observe (roll x) = x :=
  observe.apply_symm_apply _

theorem roll_observe {γ : Γ} {α : Type v} (x : ITree E γ α) :
    roll (observe x) = x :=
  observe.symm_apply_apply _

theorem observe_corec
    {A : Γ × Type v → Type w}
    (f : (i : Γ × Type v) → A i → Eff.Step Γ E A i)
    {i : Γ × Type v} (a : A i) :
    observe (corec f a) =
      IxPoly.map (fun _ y => corec f y) i (f i a) :=
  IxPoly.M.observe_corec

def ret {γ : Γ} {α : Type v} (x : α) : ITree E γ α :=
  roll <| Eff.Step.ret x

def op {γ : Γ} {α : Type v} (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      ITree E (eS.blockCtx γ e t) (eS.blockOutputs γ e t))
    (k : eS.output γ e → ITree E γ α) :
    ITree E γ α :=
  roll $ Eff.Step.op e blocks k

theorem roll_ret {γ : Γ} {α : Type v} (x : α) :
    roll (E := E) (Eff.Step.ret (γ := γ) x) = ret (γ := γ) x :=
  rfl

theorem roll_op {γ : Γ} {α : Type v} (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      ITree E (eS.blockCtx γ e t) (eS.blockOutputs γ e t))
    (k : eS.output γ e → ITree E γ α) :
    roll (E := E) (Eff.Step.op e blocks k) = op e blocks k :=
  rfl

@[simp]
theorem observe_ret {γ : Γ} {α : Type v} (x : α) :
    observe (ret x (E := E) (γ := γ)) = Eff.Step.ret x :=
  rfl

@[simp]
theorem observe_op {γ : Γ} {α : Type v} (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      ITree E (eS.blockCtx γ e t) (eS.blockOutputs γ e t))
    (k : eS.output γ e → ITree E γ α) :
    observe (op e blocks k (E := E)) = Eff.Step.op e blocks k :=
  rfl

protected def casesOn
    {motive : (i : Γ × Type v) → ITree E i.1 i.2 → Sort w}
    {γ : Γ} {α : Type v} (x : ITree E γ α)
    (ret : ∀ {γ : Γ} {α : Type v} x, motive (γ, α) (ret x))
    (op : ∀ {γ : Γ} {α : Type v} e blocks k,
      motive (γ, α) (op e blocks k)) :
    motive (γ, α) x := by
  have : x = roll (observe x) := (observe.symm_apply_apply _).symm
  rw [this]
  cases observe x using Eff.Step.casesOn <;> apply_assumption

inductive BisimRelF
    (R : (i : Γ × Type v) → ITree E i.1 i.2 → ITree E i.1 i.2 → Prop) :
    (i : Γ × Type v) →
    Eff.Step Γ E (fun i => ITree E i.1 i.2) i →
    Eff.Step Γ E (fun i => ITree E i.1 i.2) i → Prop where
| ret {γ : Γ} {α : Type v} (x : α) :
    BisimRelF R (γ, α) (Eff.Step.ret x) (Eff.Step.ret x)
| op {γ : Γ} {α : Type v} (e : E γ)
    (k1 k2 : eS.output γ e → ITree E γ α)
    (blocks1 blocks2 :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      ITree E (eS.blockCtx γ e t) (eS.blockOutputs γ e t))
    (h1 : ∀ o, R (γ, α) (k1 o) (k2 o))
    (h2 : ∀ t i,
      R (eS.blockCtx γ e t, eS.blockOutputs γ e t)
        (blocks1 t i) (blocks2 t i)) :
    BisimRelF R (γ, α)
      (Eff.Step.op e blocks1 k1)
      (Eff.Step.op e blocks2 k2)

theorem BisimRelF.toLiftR
    {R : (i : Γ × Type v) → ITree E i.1 i.2 → ITree E i.1 i.2 → Prop} :
    BisimRelF R ≤ IxPoly.M.LiftR (Eff.Step Γ E) R := by
  intro i x y hxy
  cases hxy <;> constructor
  case ret => intro a; cases a
  case op =>
    intro a
    cases a <;> apply_assumption

theorem BisimRelF.refl {R}
    (hrefl : ∀ {i : Γ × Type v} (x : ITree E i.1 i.2), R i x x)
    {i : Γ × Type v}
    (x : Eff.Step Γ E (fun i => ITree E i.1 i.2) i) :
    BisimRelF R i x x := by
  cases x using Eff.Step.casesOn <;> constructor <;> intros <;> apply_assumption

theorem BisimRelF.refl_upToEq {R}
    {i : Γ × Type v}
    (x : Eff.Step Γ E (fun i => ITree E i.1 i.2) i) :
    BisimRelF (M.IxRel.upToEq R) i x x := by
  apply BisimRelF.refl
  intros
  apply Or.inl
  rfl

theorem bisim
    {γ : Γ} {α : Type v}
    (R : (i : Γ × Type v) → ITree E i.1 i.2 → ITree E i.1 i.2 → Prop)
    (step : ∀ {i x y}, R i x y → BisimRelF R i (observe x) (observe y))
    {x y : ITree E γ α} (hxy : R (γ, α) x y) :
    x = y := by
  apply IxPoly.M.Bisim.coind (R := R)
  · intro i x y hxy
    apply BisimRelF.toLiftR
    apply step hxy
  · assumption

theorem bisim_up_to_eq
    {γ : Γ} {α : Type v}
    (R : (i : Γ × Type v) → ITree E i.1 i.2 → ITree E i.1 i.2 → Prop)
    (step : ∀ {i x y}, R i x y →
      BisimRelF (M.IxRel.upToEq R) i (observe x) (observe y))
    {x y : ITree E γ α} (hxy : R (γ, α) x y) :
    x = y := by
  apply bisim (R := M.IxRel.upToEq R)
  · intro _ x y hxy
    cases hxy
    · rename_i h
      cases h
      apply BisimRelF.refl_upToEq
    · apply step
      assumption
  · right
    assumption

theorem bisim₂
    {i : Γ × Type v} {Seed : Γ × Type v → Type w}
    (left right : (i : Γ × Type v) → Seed i → ITree E i.1 i.2)
    (step : ∀ {i} (s : Seed i),
      BisimRelF (M.IxRel.span Seed left right) i
        (observe (left i s)) (observe (right i s)))
    (seed : Seed i) :
    left i seed = right i seed := by
  apply bisim (R := M.IxRel.span Seed left right)
  intro i x y hxy
  rcases hxy with ⟨s, rfl, rfl⟩
  apply step
  exists seed

theorem bisim₂_up_to_eq
    {i : Γ × Type v} {Seed : Γ × Type v → Type w}
    (left right : (i : Γ × Type v) → Seed i → ITree E i.1 i.2)
    (step : ∀ {i} (s : Seed i),
      BisimRelF (M.IxRel.upToEq (M.IxRel.span Seed left right)) i
        (observe (left i s)) (observe (right i s)))
    (seed : Seed i) :
    left i seed = right i seed := by
  apply bisim_up_to_eq (R := M.IxRel.span Seed left right)
  intro i x y hxy
  rcases hxy with ⟨s, rfl, rfl⟩
  apply step
  exists seed

abbrev BindCarrier
    (E : Γ → Type u) [Eff.Spec E]
    (α : Type v) (i : Γ × Type v) : Type _ :=
  (ITree E i.1 α × (α → ITree E i.1 i.2)) ⊕ ITree E i.1 i.2

def bindCo {α : Type v} (i : Γ × Type v) :
    BindCarrier E α i → Eff.Step Γ E (BindCarrier E α) i
| .inl (e, f) => match e.observe with
  | ⟨.ret x, _⟩ => IxPoly.map (fun _ => .inr) _ (f x).observe
  | ⟨.op e, cont⟩ => ⟨.op e, fun
    | .inl o => .inl (cont $ .inl o, f)
    | .inr b => .inr (cont $ .inr b)
  ⟩
| .inr e => IxPoly.map (fun _ => .inr) _ e.observe

theorem bindCo_copy
    {α : Type v} {i : Γ × Type v} {x : ITree E i.1 i.2} :
    corec (bindCo (α := α)) (.inr x) = x := by
  rcases i with ⟨γ, β⟩
  apply bisim (R := fun _ x y => x = corec (bindCo (α := α)) (.inr y))
  intro j x y hxy
  rcases j with ⟨δ, A⟩
  cases hxy
  · rw [observe_corec]
    simp only [bindCo, IxPoly.map_map]
    cases y.observe using Eff.Step.casesOn with
    | ret =>
      simp only [Eff.Step.map_ret]
      constructor
    | op =>
      simp only [Eff.Step.map_op]
      constructor <;> intros <;> rfl
  · rfl

instance {γ : Γ} : Monad (ITree E γ) where
  pure := fun x => ret x
  bind {α β} (a : ITree E γ α) (f : α → ITree E γ β) :=
    corec bindCo ((.inl (a, f)) : BindCarrier E α (γ, β))

@[simp]
theorem ret_bind
    {γ : Γ} {α β : Type v} {x : α}
    {f : α → ITree E γ β} :
    ret x >>= f = f x := by
  apply observe.injective
  change observe
      (corec bindCo
        ((.inl (ret x, f)) : BindCarrier E α (γ, β))) =
    observe (f x)
  rw [observe_corec]
  simp only [bindCo, observe_ret, Eff.Step.ret, IxPoly.map]
  rcases observe (f x) with ⟨p, g⟩
  change
    (⟨p, fun a => corec bindCo (.inr (g a))⟩ :
      Eff.Step Γ E (fun i => ITree E i.1 i.2) (γ, β)) =
    ⟨p, g⟩
  congr 1
  funext a
  exact bindCo_copy

@[simp]
theorem op_bind
    {γ : Γ} {α β : Type v}
    {e : E γ}
    {blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      ITree E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)}
    {k : eS.output γ e → ITree E γ α}
    {f : α → ITree E γ β} :
    (op e blocks k) >>= f =
      op e
        blocks
        (fun o => k o >>= f) := by
  apply observe.injective
  change observe
      (corec bindCo
        ((.inl (op e blocks k, f)) : BindCarrier E α (γ, β))) =
    observe (op e blocks (fun o => k o >>= f))
  rw [observe_corec]
  simp only [bindCo, observe_op, IxPoly.map]
  simp only [Eff.Step.op]
  congr 2
  ext a; cases a
  · rfl
  · simp [bindCo_copy]

def Approx.bindFast
    {E : Γ → Type u} [eS : Eff.Spec.{u, v} E]
    {γ : Γ} {α β : Type v} (f : α → ITree E γ β) :
    {n : Nat} →
      IxPoly.M.Approx (Eff.Step Γ E) n (γ, α) →
      IxPoly.M.Approx (Eff.Step Γ E) n (γ, β)
  | 0, .zero _ => .zero _
  | n + 1, @IxPoly.M.Approx._succ _ _ _ (γ, α) p children =>
      match p with
      | .ret value => (f value).approx (n + 1)
      | .op e =>
        ._succ n (γ, β) (Eff.NodeTag.op e) fun
          | .inl output => Approx.bindFast f (children (.inl output))
          | .inr block => children (.inr block)

theorem Approx.bindFast_agree
    {E : Γ → Type u} [eS : Eff.Spec.{u, v} E]
    {γ : Γ} {α β : Type v} (f : α → ITree E γ β)
    {n : Nat}
    {x : IxPoly.M.Approx (Eff.Step Γ E) n (γ, α)}
    {y : IxPoly.M.Approx (Eff.Step Γ E) (n + 1) (γ, α)}
    (h : IxPoly.M.Agree (Eff.Step Γ E) x y) :
    IxPoly.M.Agree (Eff.Step Γ E)
      (Approx.bindFast f x) (Approx.bindFast f y) := by
  cases h with
  | zero => exact .zero _ _
  | succ p children children' hchildren =>
    cases p with
    | ret value =>
      simp only [Approx.bindFast]
      exact (f value).agree
    | op e =>
      simp only [Approx.bindFast]
      apply IxPoly.M.Agree.succ
      intro field
      cases field with
      | inl output =>
        exact Approx.bindFast_agree f (hchildren (Sum.inl output))
      | inr block => exact hchildren (Sum.inr block)

def bindFast
    {E : Γ → Type u} [eS : Eff.Spec.{u, v} E]
    {γ : Γ} {α β : Type v}
    (x : ITree E γ α) (f : α → ITree E γ β) :
    ITree E γ β where
  approx n := Approx.bindFast f (x.approx n)
  agree := Approx.bindFast_agree f x.agree

@[simp]
theorem bindFast_ret
    {E : Γ → Type u} [eS : Eff.Spec.{u, v} E]
    {γ : Γ} {α β : Type v} (value : α)
    (f : α → ITree E γ β) :
    bindFast (ret value) f = f value := by
  apply IxPoly.M.ext
  intro n
  change Approx.bindFast f
    ((IxPoly.M.prepend (Eff.Step.ret value)).approx n) = (f value).approx n
  cases n with
  | zero =>
    cases (f value).approx 0
    rfl
  | succ n => rfl

@[simp]
theorem bindFast_op
    {E : Γ → Type u} [eS : Eff.Spec.{u, v} E]
    {γ : Γ} {α β : Type v} (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      ITree E (eS.blockCtx γ e t) (eS.blockOutputs γ e t))
    (k : eS.output γ e → ITree E γ α)
    (f : α → ITree E γ β) :
    bindFast (op e blocks k) f =
      op e blocks (fun output => bindFast (k output) f) := by
  apply IxPoly.M.ext
  intro n
  change Approx.bindFast f
    ((IxPoly.M.prepend (Eff.Step.op e blocks k)).approx n) =
    (IxPoly.M.prepend (Eff.Step.op e blocks
      (fun output => bindFast (k output) f))).approx n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [IxPoly.M.prepend, IxPoly.map, IxPoly.M.Approx.succ,
      Eff.Step.op, Approx.bindFast, bindFast]
    congr 1
    funext field
    cases field with
    | inl output => rfl
    | inr block =>
      rcases block with ⟨tag, input⟩
      rfl

theorem bindFast_eq_bind
    {E : Γ → Type u} [eS : Eff.Spec.{u, v} E]
    {γ : Γ} {α β : Type v}
    (x : ITree E γ α) (f : α → ITree E γ β) :
    bindFast x f = x >>= f := by
  apply bisim₂_up_to_eq (i := (γ, β))
    (Seed := fun i => ITree E i.1 α × (α → ITree E i.1 i.2))
    (left := fun _ state => bindFast state.1 state.2)
    (right := fun _ state => state.1 >>= state.2)
    (seed := (x, f))
  intro i state
  rcases i with ⟨δ, A⟩
  rcases state with ⟨tree, continuation⟩
  have htree : tree = roll (observe tree) := (roll_observe tree).symm
  rw [htree]
  cases observe tree using Eff.Step.casesOn with
  | ret value =>
    simp only [roll_ret, bindFast_ret, ret_bind]
    apply BisimRelF.refl_upToEq
  | op e blocks k =>
    simp only [roll_op, bindFast_op, op_bind, observe_op]
    apply BisimRelF.op
    · intro output
      right
      exact ⟨(k output, continuation), rfl, rfl⟩
    · intro tag input
      left
      rfl

@[simp]
theorem hasOp_bind
    {F : Γ → Type u} {γ : Γ} {α β : Type v}
    [Eff.Spec F] [Eff.Has F E]
    {e : F γ}
    {blocks :
      (t : Eff.Spec.blockTag γ e) →
      Eff.Spec.blockInputs γ e t →
      ITree E (Eff.Spec.blockCtx γ e t) (Eff.Spec.blockOutputs γ e t)}
    {k : Eff.Spec.output γ e → ITree E γ α}
    {f : α → ITree E γ β} :
    (roll (Eff.Step.Has.op e blocks k) >>= f) =
      roll
        (Eff.Step.Has.op e blocks
          (fun o => k o >>= f)) := by
  simp only [Eff.Step.Has.op, roll_op, op_bind]

inductive BindPureRel (γ : Γ) :
    (α : Type v) → ITree E γ α → ITree E γ α → Prop where
| root {α} (m : ITree E γ α) : BindPureRel γ α (m >>= pure) m
| refl {α} (m : ITree E γ α) : BindPureRel γ α m m

theorem bind_pure {γ : Γ} {α : Type v} (a : ITree E γ α) :
    a >>= pure = a := by
  apply bisim₂_up_to_eq
    (i := (γ, α))
    (Seed := fun i => ITree E i.1 i.2)
    (left := fun _ x => x >>= pure)
    (right := fun _ x => x)
    (seed := a)
  intro i m
  rcases i with ⟨δ, A⟩
  have hm : m = roll (observe m) := (observe.symm_apply_apply _).symm
  rw [hm]
  cases observe m using Eff.Step.casesOn with
  | ret =>
    simp [roll_ret, ret_bind, pure, BisimRelF.refl_upToEq]
  | op e blocks k =>
    simp only [roll_op, op_bind, observe_op]
    apply BisimRelF.op
    · intro
      right
      apply Exists.intro
      apply And.intro <;> rfl
    · intros; left; rfl

theorem bind_assoc
    {δ : Γ} {α β γ : Type v}
    {a : ITree E δ α}
    {f : α → ITree E δ β}
    {g : β → ITree E δ γ} :
    (a >>= f) >>= g = a >>= fun x => f x >>= g := by
  apply bisim₂_up_to_eq
    (i := (δ, γ))
    (Seed := fun i =>
      ITree E i.1 α ×
      (α → ITree E i.1 β) ×
      (β → ITree E i.1 i.2))
    (left := fun _ ⟨x, f, g⟩ => (x >>= f) >>= g)
    (right := fun _ ⟨x, f, g⟩ => x >>= fun y => f y >>= g)
    (seed := ⟨a, f, g⟩)
  intro i ⟨x, f, g⟩
  rcases i with ⟨ε, A⟩
  simp only
  have hx : x = roll (observe x) := (observe.symm_apply_apply _).symm
  rw [hx]
  cases observe x using Eff.Step.casesOn with
  | ret =>
    simp [roll_ret, ret_bind, BisimRelF.refl_upToEq]
  | op e blocks k =>
    simp only [roll_op, op_bind, observe_op]
    apply BisimRelF.op
    · intro o
      right
      exists ⟨k o, f, g⟩
    · intros; left; rfl

instance {γ : Γ} : LawfulMonad (ITree E γ) := LawfulMonad.mk' _
  bind_pure
  (fun _ _ => ret_bind)
  (fun _ _ _ => bind_assoc)

section Loops

variable [Eff.Has Eff.Tau E]

def tau {γ : Γ} {α : Type v} (x : ITree E γ α) : ITree E γ α :=
  roll $ Eff.Step.tau x

@[simp]
theorem observe_tau {γ : Γ} {α : Type v} (x : ITree E γ α) :
    observe (tau x) = Eff.Step.tau x := rfl

@[simp]
theorem tau_bind
    {γ : Γ} {α β : Type v} {x : ITree E γ α}
    {f : α → ITree E γ β} :
    tau x >>= f = tau (x >>= f) := by
  apply observe.injective
  simp only [tau, Eff.Step.tau, hasOp_bind]

private abbrev LoopCarrier
    (E : Γ → Type u) [Eff.Spec E]
    (α β : Type v) (i : Γ × Type v) : Type _ :=
  ((α → ITree E i.1 (α ⊕ β)) ×
    ITree E i.1 (α ⊕ β) ×
    (β → ITree E i.1 i.2)) ⊕
  ITree E i.1 i.2

private def loopCo {α β : Type v} (i : Γ × Type v) :
    LoopCarrier E α β i → Eff.Step Γ E (LoopCarrier E α β) i
| .inl (body, m, f) => match m.observe with
  | ⟨.ret (.inr v), _⟩ => IxPoly.map (fun _ => .inr) _ (f v).observe
  | ⟨.ret (.inl v), _⟩ => Eff.Step.tau (.inl (body, body v, f))
  | ⟨.op e, k⟩ => Eff.Step.op e
      (fun t i => .inr (k $ .inr ⟨t, i⟩))
      (fun o => .inl (body, k (.inl o), f))
| .inr m => IxPoly.map (fun _ => .inr) _ m.observe

private theorem observe_loopCo
    {α β : Type v} {i : Γ × Type v}
    (x : LoopCarrier E α β i) :
    observe (corec (loopCo (E := E) (α := α) (β := β)) x) =
      IxPoly.map
        (fun _ y => corec (loopCo (E := E) (α := α) (β := β)) y)
      i (loopCo i x) :=
  observe_corec _ _

private theorem loopCo_op
    {α β δ : Type v} {γ : Γ}
    (body : α → ITree E γ (α ⊕ β))
    (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      ITree E (eS.blockCtx γ e t) (eS.blockOutputs γ e t))
    (next : eS.output γ e → ITree E γ (α ⊕ β))
    (k : β → ITree E γ δ) :
    loopCo (γ, δ)
        ((.inl (body, op e blocks next, k)) :
          LoopCarrier E α β (γ, δ)) =
      Eff.Step.op e
        (fun t i => .inr (blocks t i))
        (fun o => .inl (body, next o, k)) := by
  simp only [loopCo, observe_op, Eff.Step.op]

private theorem loopCo_copy
    {α β : Type v} {i : Γ × Type v}
    {x : ITree E i.1 i.2} :
    corec (loopCo (α := α) (β := β)) (.inr x) = x := by
  rcases i with ⟨γ, δ⟩
  apply bisim
    (R := fun i x y =>
      x = corec (loopCo (α := α) (β := β)) (.inr y))
  intro j x y hxy
  rcases j with ⟨ε, A⟩
  cases hxy
  · rw [observe_corec]
    simp only [loopCo, IxPoly.map_map]
    cases y.observe using Eff.Step.casesOn with
    | ret =>
      simp only [Eff.Step.map_ret]
      constructor
    | op =>
      simp only [Eff.Step.map_op]
      constructor <;> intros <;> rfl
  · rfl

def loop
    {γ : Γ} {α β δ : Type v}
    (body : α → ITree E γ (α ⊕ β))
    (initial : α) (k : β → ITree E γ δ) :
    ITree E γ δ :=
  corec loopCo
    ((.inl (body, body initial, k)) : LoopCarrier E α β (γ, δ))

theorem loop_def
    {γ : Γ} {α β δ : Type v}
    {body : α → ITree E γ (α ⊕ β)}
    {initial : α} {k : β → ITree E γ δ} :
    loop body initial k =
      (body initial >>= fun x => match x with
        | .inr v => k v
        | .inl v => tau (loop body v k)) := by
  unfold loop
  apply bisim₂_up_to_eq
    (i := (γ, δ))
    (Seed := LoopCarrier E α β)
    (left := fun _ x => corec loopCo x)
    (right := fun _ x => match x with
      | .inr t => t
      | .inl (body, m, f) => m >>= fun x => match x with
        | .inr v => f v
        | .inl v => tau $ corec loopCo (.inl (body, body v, f)))
    (seed :=
      ((.inl (body, body initial, k)) :
        LoopCarrier E α β (γ, δ)))
  intro i x
  rcases i with ⟨ε, A⟩
  cases x with
  | inr m =>
    rw [observe_corec]
    simp only [loopCo, IxPoly.map_map]
    cases m.observe using Eff.Step.casesOn with
    | ret =>
      simp only [Eff.Step.map_ret]
      apply BisimRelF.refl_upToEq
    | op e blocks k =>
      simp only [Eff.Step.map_op]
      apply BisimRelF.op
      · intro o
        right
        exists (.inr (k o))
      · intros
        left
        exact loopCo_copy
  | inl m =>
    rcases m with ⟨body, m, f⟩
    simp only
    have hm : m = roll (observe m) := (observe.symm_apply_apply _).symm
    rw [hm]
    cases observe m using Eff.Step.casesOn with
    | ret x =>
      simp only [roll_ret, ret_bind]
      cases x with
      | inr v =>
        simp only
        rw [observe_loopCo
          (E := E) (α := α) (β := β)
          ((.inl (body, ret (.inr v), f)) :
            LoopCarrier E α β (ε, A))]
        simp only [loopCo, observe_ret, Eff.Step.ret, IxPoly.map_map,
          loopCo_copy, IxPoly.map_id]
        apply BisimRelF.refl_upToEq
      | inl v =>
        simp only
        rw [observe_loopCo
          (E := E) (α := α) (β := β)
          ((.inl (body, ret (.inl v), f)) :
            LoopCarrier E α β (ε, A))]
        simp only [loopCo, observe_ret, Eff.Step.ret, Eff.Step.map_tau,
          observe_tau]
        apply BisimRelF.op
        · intro
          left
          rfl
        · intro t
          exact (nomatch Eff.Step.Has.lowerBlockTag t)
    | op e blocks k =>
      simp only [roll_op, op_bind]
      rw [observe_loopCo
        (E := E) (α := α) (β := β)
        ((.inl (body, op e blocks k, f)) :
          LoopCarrier E α β (ε, A))]
      rw [loopCo_op, Eff.Step.map_op]
      simp only [observe_op]
      apply BisimRelF.op
      · intro o
        right
        exists (.inl (body, k o, f))
      · intros
        left
        exact loopCo_copy

private theorem loopCo_bind
    {γ : Γ} {α β δ : Type v}
    (body : α → ITree E γ (α ⊕ β))
    (m : ITree E γ (α ⊕ β)) (k : β → ITree E γ δ) :
    (corec loopCo
      ((.inl (body, m, pure)) : LoopCarrier E α β (γ, β)) >>= k) =
      corec loopCo
        ((.inl (body, m, k)) : LoopCarrier E α β (γ, δ)) := by
  symm
  apply bisim₂_up_to_eq
    (i := (γ, δ))
    (Seed := fun i =>
      (α → ITree E i.1 (α ⊕ β)) ×
      ITree E i.1 (α ⊕ β) ×
      (β → ITree E i.1 i.2))
    (left := fun _ ⟨body, m, k⟩ =>
      corec loopCo (.inl (body, m, k)))
    (right := fun i ⟨body, m, k⟩ =>
      (corec loopCo
        ((.inl (body, m, pure)) : LoopCarrier E α β (i.1, β)) :
          ITree E i.1 β) >>= k)
    (seed := ⟨body, m, k⟩)
  intro i seed
  rcases i with ⟨ε, A⟩
  rcases seed with ⟨body, m, k⟩
  have hm : m = roll (observe m) := (observe.symm_apply_apply _).symm
  rw [hm]
  cases observe m using Eff.Step.casesOn with
  | ret x =>
    cases x with
    | inr v =>
      have unfold : ∀ {j : Type v} (f : β → ITree E ε j),
          corec loopCo
            ((.inl (body, ret (.inr v), f)) :
              LoopCarrier E α β (ε, j)) = f v := by
        intro j f
        apply observe.injective
        rw [observe_loopCo]
        simp only [loopCo, observe_ret, Eff.Step.ret, IxPoly.map_map,
          loopCo_copy, IxPoly.map_id]
      simp only [roll_ret]
      rw [unfold k, unfold pure]
      simp only [pure, ret_bind]
      apply BisimRelF.refl_upToEq
    | inl v =>
      have unfold : ∀ {j : Type v} (f : β → ITree E ε j),
          corec loopCo
              ((.inl (body, ret (.inl v), f)) :
                LoopCarrier E α β (ε, j)) =
            tau
              (corec loopCo
                ((.inl (body, body v, f)) :
                  LoopCarrier E α β (ε, j))) := by
        intro j f
        apply observe.injective
        rw [observe_loopCo]
        simp only [loopCo, observe_ret, Eff.Step.ret, Eff.Step.map_tau,
          observe_tau]
        rfl
      simp only [roll_ret]
      rw [unfold k, unfold pure]
      simp only [tau_bind, observe_tau]
      apply BisimRelF.op
      · intro
        right
        exists ⟨body, body v, k⟩
      · intro t
        exact (nomatch Eff.Step.Has.lowerBlockTag t)
  | op e blocks next =>
    have unfold : ∀ {j : Type v} (f : β → ITree E ε j),
        corec loopCo
            ((.inl (body, op e blocks next, f)) :
              LoopCarrier E α β (ε, j)) =
          op (E := E) (α := j) e blocks
            (fun o =>
              corec loopCo
                ((.inl (body, next o, f)) :
                  LoopCarrier E α β (ε, j))) := by
      intro j f
      apply observe.injective
      have hco :
          loopCo (ε, j) (.inl (body, op e blocks next, f)) =
            Eff.Step.op e
              (fun t x =>
                (.inr (blocks t x) :
                  LoopCarrier E α β
                    (eS.blockCtx ε e t, eS.blockOutputs ε e t)))
              (fun o => .inl (body, next o, f)) := by
        simp only [loopCo, observe_op, Eff.Step.op]
      rw [observe_loopCo, observe_op, hco, Eff.Step.map_op]
      congr 1
      funext t x
      exact loopCo_copy
    simp only [roll_op]
    rw [unfold k, unfold pure]
    simp only [op_bind, observe_op]
    apply BisimRelF.op
    · intro o
      right
      exists ⟨body, next o, k⟩
    · intros
      left
      rfl

theorem loop_bind
    {γ : Γ} {α β δ : Type v}
    (body : α → ITree E γ (α ⊕ β))
    (initial : α) (k : β → ITree E γ δ) :
    loop body initial pure >>= k = loop body initial k :=
  loopCo_bind body (body initial) k

end Loops

section Fail

variable [Eff.Has Eff.Fail E]
def fail {γ : Γ} {α : Type v} : ITree E γ α := roll $ Eff.Step.fail

@[simp]
theorem fail_bind
    {γ : Γ} {α β : Type v} {f : α → ITree E γ β} :
    fail >>= f = fail := by
  apply observe.injective
  simp only [fail, Eff.Step.fail, hasOp_bind, observe_roll]
  congr
  ext o
  cases o

end Fail

end Freigen.ITree
