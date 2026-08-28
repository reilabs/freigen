import Freigen.IxPoly.Basic

namespace Freigen.Eff

class Spec {Γ : Type u} (tag : Γ → Type u) where
  output : (γ : Γ) → tag γ → Type v
  blockTag : (γ : Γ) → tag γ → Type u
  blockCtx : (γ : Γ) → (t : tag γ) → blockTag γ t → Γ
  blockInputs : (γ : Γ) → (t : tag γ) → blockTag γ t → Type v
  blockOutputs : (γ : Γ) → (t : tag γ) → blockTag γ t → Type v

abbrev Handler
    {Γ : Type u}
    (E : Γ → Type u) [s : Spec.{u, v} E]
    (M : Γ → Type v → Type w) :=
  {γ : Γ} →
  (e : E γ) →
  ((t : s.blockTag γ e) →
    s.blockInputs γ e t →
    M (s.blockCtx γ e t) (s.blockOutputs γ e t)) →
  M γ (s.output γ e)

inductive NodeTag (Γ : Type u) (T : Γ → Type u) [s : Spec.{u, v} T]
    (γ : Γ) (R : Type v) : Type (max u v) where
| ret : R → NodeTag Γ T γ R
| op (t : T γ) : NodeTag Γ T γ R

abbrev NodeTag.fields {Γ : Type u} {T : Γ → Type u} {γ} [s : Spec T]
    {R : Type v} : NodeTag Γ T γ R → Type (max u v)
| ret _ => PEmpty
| op e => s.output γ e ⊕ ((t : s.blockTag γ e) × s.blockInputs γ e t)

def NodeTag.elem {Γ : Type u} {T : Γ → Type u} {γ} [s : Spec T] {α : Type v} :
    (t : NodeTag Γ T γ α) → (p : t.fields) → Γ × Type v
| ret _ => nofun
| op e => fun
  | Sum.inl _ => (γ, α)
  | Sum.inr ⟨o, _⟩ => (s.blockCtx γ e o, s.blockOutputs γ e o)

def NoEff {Γ : Type u} : Γ → Type u := fun _ => PEmpty

instance {Γ : Type u} : Spec (@NoEff Γ) where
  output := nofun
  blockTag := nofun
  blockCtx := nofun
  blockInputs := nofun
  blockOutputs := nofun

def Sum {Γ : Type u} (T₁ T₂ : Γ → Type u) : Γ → Type u := fun γ => T₁ γ ⊕ T₂ γ

infixr:65 " ⊕ₑ " => Sum

instance sumInst {Γ : Type u} {T₁ T₂ : Γ → Type u}
    [Spec T₁] [Spec T₂] : Spec (T₁ ⊕ₑ T₂) where
  output := fun
    | γ, Sum.inl t => Spec.output γ t
    | γ, Sum.inr t => Spec.output γ t
  blockTag := fun
    | γ, Sum.inl t => Spec.blockTag γ t
    | γ, Sum.inr t => Spec.blockTag γ t
  blockCtx := fun
    | γ, Sum.inl t, b => Spec.blockCtx γ t b
    | γ, Sum.inr t, b => Spec.blockCtx γ t b
  blockInputs := fun
    | γ, Sum.inl t => Spec.blockInputs γ t
    | γ, Sum.inr t => Spec.blockInputs γ t
  blockOutputs := fun
    | γ, Sum.inl t => Spec.blockOutputs γ t
    | γ, Sum.inr t => Spec.blockOutputs γ t

class inductive Has {Γ : Type u} :
    (a : Γ → Type u) → [Spec a] →
    (b : Γ → Type u) → [Spec b] → Type _ where
| here {α : Γ → Type u} [s : Spec α] : Has α α
| inl {α β γ : Γ → Type u}
    [Spec α] [Spec β] [Spec γ] :
    Has α β → Has α (β ⊕ₑ γ)
| inr {α β γ : Γ → Type u}
    [Spec α] [Spec β] [Spec γ] :
    Has α γ → Has α (β ⊕ₑ γ)

instance [Spec α] : Has α α := Has.here
instance [Spec α] [Spec β] [Spec γ] [r : Has α β] :
    Has α (β ⊕ₑ γ) := Has.inl r
instance [Spec α] [Spec β] [Spec γ] [r : Has α γ] :
    Has α (β ⊕ₑ γ) := Has.inr r

def Has.mk {Γ} {α β : Γ → Type u} {γ : Γ} [Spec α] [Spec β] [r: Has α β] : α γ → β γ
| a => match r with
  | Has.here => a
  | Has.inl r => Sum.inl (Has.mk a)
  | Has.inr r => Sum.inr (Has.mk a)

def Has.out {Γ} {α β : Γ → Type u} {γ : Γ} [Spec α] [Spec β] [r: Has α β] : β γ → Option (α γ)
| b => match r, b with
  | Has.here, b => some b
  | Has.inl _, Sum.inl a => Has.out a
  | Has.inl _, Sum.inr _ => none
  | Has.inr _, Sum.inl _ => none
  | Has.inr _, Sum.inr a => Has.out a

def Step (Γ : Type u) (T : Γ → Type u) [Spec T] :
    IxPoly.Endo (Γ × Type v) where
  Tag := fun (γ, α) => NodeTag Γ T γ α
  Field := fun _ n => n.fields
  Elem := fun _ n p => n.elem p

structure TauCarrier : Type v
def Tau {Γ : Type u} : Γ → Type v := fun _ => TauCarrier

instance tauSpec {Γ : Type u} : Spec (Tau (Γ := Γ)) where
  output := fun _ _ => PUnit
  blockTag := fun _ _ => PEmpty
  blockCtx := nofun
  blockInputs := nofun
  blockOutputs := nofun

structure FailCarrier : Type v
def Fail {Γ : Type u} : Γ → Type v := fun _ => FailCarrier

instance failSpec {Γ : Type u} : Spec (Fail (Γ := Γ)) where
  output := fun _ _ => PEmpty
  blockTag := fun _ _ => PEmpty
  blockCtx := nofun
  blockInputs := nofun
  blockOutputs := nofun

namespace Step

def ret {Γ E α Y} {γ : Γ} [Spec E] (x : α) : Step Γ E Y (γ, α) := ⟨.ret x, fun a => PEmpty.elim a⟩
def op {Γ E α Y} {γ : Γ} [s: Spec E] (e : E γ)
    (blocks : (t : s.blockTag γ e) → s.blockInputs γ e t → Y (s.blockCtx γ e t, s.blockOutputs γ e t))
    (k : (o : s.output γ e) → Y (γ, α)) : Step Γ E Y (γ, α) :=
  ⟨.op e, fun
    | Sum.inl o => k o
    | Sum.inr ⟨t, i⟩ => blocks t i
  ⟩

def Has.lowerBlockTag
    {Γ : Type u} {E F : Γ → Type u} {γ : Γ}
    [s : Spec E] [s' : Spec F] [h : Has F E]
    {e : F γ} (t : s.blockTag γ (Has.mk (r := h) e)) :
    s'.blockTag γ e :=
  match h with
  | Has.here => t
  | Has.inl r => lowerBlockTag (h:=r) t
  | Has.inr r => lowerBlockTag (h:=r) t

def Has.lowerBlockInput
    {Γ : Type u} {E F : Γ → Type u} {γ : Γ}
    [s : Spec E] [s' : Spec F] [h : Has F E] :
    {e : F γ} →
    (t : s.blockTag γ (Has.mk (r := h) e)) →
    s.blockInputs γ (Has.mk (r := h) e) t →
    s'.blockInputs γ e (lowerBlockTag t) :=
  match h with
  | Has.here => fun _ i => i
  | Has.inl r => fun t i => lowerBlockInput (h:=r) t i
  | Has.inr r => fun t i => lowerBlockInput (h:=r) t i

def Has.liftBlockOutput
    {Γ : Type u} {E F : Γ → Type u} {γ : Γ}
    {Y : Γ × Type v → Type w}
    [s : Spec E] [s' : Spec F] [h : Has F E] :
    {e : F γ} →
    (t : s.blockTag γ (Has.mk (r := h) e)) →
    Y (s'.blockCtx γ e (Has.lowerBlockTag t),
      s'.blockOutputs γ e (Has.lowerBlockTag t)) →
    Y (s.blockCtx γ (Has.mk (r := h) e) t,
      s.blockOutputs γ (Has.mk (r := h) e) t) := match h with
  | Has.here => fun _ x => x
  | Has.inl r => fun t x => liftBlockOutput (h:=r) t x
  | Has.inr r => fun t x => liftBlockOutput (h:=r) t x

def Has.lowerOutput
    {Γ : Type u} {E F : Γ → Type u} {γ : Γ}
    [s : Spec E] [s' : Spec F] [h : Has F E]
    {e : F γ} (o : s.output γ (Has.mk (r := h) e)) :
    s'.output γ e := match h with
  | Has.here => o
  | Has.inl r => lowerOutput (h:=r) o
  | Has.inr r => lowerOutput (h:=r) o

def Has.op
    {Γ : Type u} {E F : Γ → Type u} {γ : Γ} {α : Type v}
    {Y : Γ × Type v → Type w}
    [s : Spec E] [s' : Spec F] [h : Has F E]
    (e : F γ)
    (blocks :
      (t : s'.blockTag γ e) →
      s'.blockInputs γ e t →
      Y (s'.blockCtx γ e t, s'.blockOutputs γ e t))
    (k : s'.output γ e → Y (γ, α)) :
    Step Γ E Y (γ, α) :=
  Step.op (Has.mk e)
     (fun t i => Has.liftBlockOutput t $ blocks (Has.lowerBlockTag t) (Has.lowerBlockInput t i))
     (fun o => k (Has.lowerOutput o))

theorem Has.liftBlockOutput_naturality
      {Γ : Type u} {E F : Γ → Type u} {γ : Γ}
      {Y : Γ × Type v → Type w} {Z : Γ × Type v → Type z}
      [s : Spec E] [s' : Spec F] [h : Has F E]
      (f : (i : Γ × Type v) → Y i → Z i) {e : F γ}
      (t : s.blockTag γ (Has.mk (r := h) e))
      (x : Y (s'.blockCtx γ e (Has.lowerBlockTag t),
        s'.blockOutputs γ e (Has.lowerBlockTag t))) :
      f _ (Has.liftBlockOutput (Y := Y) t x) =
        Has.liftBlockOutput (Y := Z) t (f _ x) := by
    induction h with
    | here => rfl
    | inl r ih => exact ih t x
    | inr r ih => exact ih t x

def tau
    {Γ : Type u} {E : Γ → Type u} {γ : Γ} {α : Type v}
    {Y : Γ × Type v → Type w}
    [Spec E] [Has Tau E]
    (x : Y (γ, α)) :
    Step Γ E Y (γ, α) :=
  Has.op (F := Tau) TauCarrier.mk nofun
    (fun _ => x)

def fail
    {Γ : Type u} {E : Γ → Type u} {γ : Γ} {α : Type v}
    {Y : Γ × Type v → Type w}
    [Spec E] [Has Fail E] :
    Step Γ E Y (γ, α) :=
  Has.op (F := Fail) FailCarrier.mk nofun nofun

protected def casesOn
    {Γ : Type u} {E : Γ → Type u}
    {Y : Γ × Type v → Type w} [Spec E]
    {motive : (i : Γ × Type v) → Step Γ E Y i → Sort z}
    {i : Γ × Type v} (x : Step Γ E Y i)
    (ret : ∀ {γ : Γ} {α : Type v} x, motive (γ, α) (ret x))
    (op : ∀ {γ : Γ} {α : Type v} e blocks k,
      motive (γ, α) (op e blocks k)) :
    motive i x := by
  rcases x with ⟨tag, fields⟩
  cases tag with
  | ret a =>
    convert ret a
    simp only [Step.ret]
    congr 2
    ext a; cases a
  | op e =>
    convert op e (fun t i => fields (.inr ⟨t, i⟩)) (fun o => fields (.inl o))
    simp only [Step.op]
    congr 2
    ext a; cases a <;> rfl

@[simp]
theorem map_ret
    {Γ : Type u} {E : Γ → Type u} [Spec E]
    {Y : Γ × Type v → Type w} {Z : Γ × Type v → Type z}
    {f : (i : Γ × Type v) → Y i → Z i}
    {γ : Γ} {α : Type v} {x : α} :
    IxPoly.map (F := Step Γ E) f (γ, α) (Step.ret x) = Step.ret x := by
  simp only [IxPoly.map, ret]
  congr 1
  ext a; cases a

@[simp]
theorem map_op
    {Γ : Type u} {E : Γ → Type u} [h : Spec E]
    {Y : Γ × Type v → Type w} {Z : Γ × Type v → Type z}
    {f : (i : Γ × Type v) → Y i → Z i}
    {γ : Γ} {α : Type v}
    {e : E γ}
    {blocks :
      (t : h.blockTag γ e) →
      h.blockInputs γ e t →
      Y (h.blockCtx γ e t, h.blockOutputs γ e t)}
    {k : h.output γ e → Y (γ, α)} :
    IxPoly.map (F := Step Γ E) f (γ, α) (Step.op e blocks k) =
      Step.op e (fun t i => f _ (blocks t i)) (fun o => f _ (k o)) := by
  simp only [IxPoly.map, op]
  congr 1
  ext a; cases a <;> rfl

@[simp]
theorem map_hasOp
      {Γ : Type u} {E F : Γ → Type u}
      [Spec E] [Spec F] [Has F E]
      {Y : Γ × Type v → Type w} {Z : Γ × Type v → Type z}
      (f : (i : Γ × Type v) → Y i → Z i)
      {γ : Γ} {α : Type v}
      (e : F γ)
      (blocks :
        (t : Spec.blockTag γ e) →
        Spec.blockInputs γ e t →
        Y (Spec.blockCtx γ e t, Spec.blockOutputs γ e t))
      (k : Spec.output γ e → Y (γ, α)) :
      IxPoly.map (F := Step Γ E) f (γ, α) (Has.op e blocks k) =
        Has.op e
          (fun t i => f _ (blocks t i))
          (fun o => f _ (k o)) := by
    unfold Has.op
    rw [map_op]
    congr 1
    funext t i
    apply Has.liftBlockOutput_naturality

@[simp]
theorem map_tau
    {Γ : Type u} {E : Γ → Type u}
    [Spec E] [Has Tau E]
    {Y : Γ × Type v → Type w} {Z : Γ × Type v → Type z}
    {f : (i : Γ × Type v) → Y i → Z i}
    {γ : Γ} {α : Type v} {x : Y (γ, α)} :
    IxPoly.map (F := Step Γ E) f (γ, α) (Step.tau x) =
      Step.tau (f (γ, α) x) := by
  simp only [tau, map_hasOp]
  congr 1
  ext a
  cases a

end Step

end Freigen.Eff
