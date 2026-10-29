import Freigen.Free.Raw
import Freigen.ExactCodensity

namespace Freigen

variable {Γ : Type u} {E : Γ → Type u} [eS : Eff.Spec.{u, v} E]
  {γ : Γ} {α β : Type v}

def Free
    {Γ : Type u} (E : Γ → Type u) [Eff.Spec.{u, v} E]
    (γ : Γ) (α : Type v) : Type _ :=
  ExactCodensity (RawFree E γ) α

def Free.toRaw (x : Free E γ α) : RawFree E γ α :=
  ExactCodensity.equiv x

def Free.ofRaw (x : RawFree E γ α) : Free E γ α :=
  ExactCodensity.equiv.symm x

def Free.op
    (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      Free E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)) :
    Free E γ (eS.output γ e) :=
  Free.ofRaw <|
    RawFree.op e (fun t i => Free.toRaw (blocks t i))

instance : Monad (Free E γ) :=
  inferInstanceAs
    (Monad (ExactCodensity (RawFree E γ)))

instance : LawfulMonad (Free E γ) :=
  inferInstanceAs
    (LawfulMonad (ExactCodensity (RawFree E γ)))

@[simp]
theorem Free.toRaw_ofRaw (x : RawFree E γ α) :
    Free.toRaw (Free.ofRaw x) = x :=
  ExactCodensity.equiv.apply_symm_apply x

@[simp]
theorem Free.ofRaw_toRaw (x : Free E γ α) :
    Free.ofRaw (Free.toRaw x) = x :=
  ExactCodensity.equiv.symm_apply_apply x

theorem Free.toRaw_injective :
    Function.Injective
      (Free.toRaw (E := E) (γ := γ) (α := α)) :=
  ExactCodensity.equiv.injective

@[simp]
theorem Free.toRaw_pure (x : α) :
    Free.toRaw (pure x : Free E γ α) =
      (pure x : RawFree E γ α) :=
  ExactCodensity.equiv_pure x

@[simp]
theorem Free.toRaw_bind
    (x : Free E γ α)
    (f : α → Free E γ β) :
    Free.toRaw (x >>= f) =
      Free.toRaw x >>= fun a => Free.toRaw (f a) :=
  ExactCodensity.equiv_bind x f

@[simp]
theorem Free.toRaw_op
    (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      Free E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)) :
    Free.toRaw (α := no_index _) (Free.op e blocks) =
      RawFree.op e (fun t input =>
        Free.toRaw (blocks t input)) :=
  ExactCodensity.equiv.apply_symm_apply _

theorem Free.op_injective (e : E γ) :
    Function.Injective (Free.op e) := by
  intro blocks₁ blocks₂ h
  have hraw :
      RawFree.op e (fun t input =>
        Free.toRaw (blocks₁ t input)) =
      RawFree.op e (fun t input =>
        Free.toRaw (blocks₂ t input)) := by
    simpa only [Free.toRaw_op] using
      congrArg (Free.toRaw (E := E)) h
  have hblocks := RawFree.op_injective e hraw
  funext t input
  apply Free.toRaw_injective
  exact congrFun (congrFun hblocks t) input

@[simp]
theorem Free.op_inj
    (e : E γ)
    {blocks₁ blocks₂ :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      Free E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)} :
    @Eq (no_index _) (Free.op e blocks₁) (Free.op e blocks₂) ↔
      blocks₁ = blocks₂ :=
  (Free.op_injective e).eq_iff

@[simp]
theorem Free.op_ne_pure
    (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      Free E (eS.blockCtx γ e t) (eS.blockOutputs γ e t))
    (x : eS.output γ e) :
    Ne (α := no_index _) (Free.op e blocks) (pure x) := by
  intro h
  apply RawFree.op_ne_pure e
    (fun t input => Free.toRaw (blocks t input)) x
  simpa only [Free.toRaw_op, Free.toRaw_pure] using
    congrArg (Free.toRaw (E := E)) h

@[simp]
theorem Free.pure_ne_op
    (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      Free E (eS.blockCtx γ e t) (eS.blockOutputs γ e t))
    (x : eS.output γ e) :
    Ne (α := no_index _) (pure x) (op e blocks) :=
  Ne.symm (op_ne_pure e blocks x)

@[simp]
theorem Free.pure_ne_op_bind
    {e : E γ}
    {blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      Free E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)}
    {k : eS.output γ e → Free E γ α}
    {x : α} :
    pure x ≠ bind (α := no_index _) (Free.op e blocks) k := by
  intro h
  apply RawFree.pure_ne_op_bind e
    (fun t input => Free.toRaw (blocks t input))
    (fun output => Free.toRaw (k output)) x
  simpa only [Free.toRaw_pure, Free.toRaw_bind, Free.toRaw_op] using
    congrArg (Free.toRaw (E := E)) h

theorem Free.op_bind_effect_eq
    {e₁ e₂ : E γ}
    {blocks₁ :
      (t : eS.blockTag γ e₁) →
      eS.blockInputs γ e₁ t →
      Free E (eS.blockCtx γ e₁ t) (eS.blockOutputs γ e₁ t)}
    {blocks₂ :
      (t : eS.blockTag γ e₂) →
      eS.blockInputs γ e₂ t →
      Free E (eS.blockCtx γ e₂ t) (eS.blockOutputs γ e₂ t)}
    {k₁ : eS.output γ e₁ → Free E γ α}
    {k₂ : eS.output γ e₂ → Free E γ α}
    (h :
      (Free.op e₁ blocks₁ >>= k₁) =
        (Free.op e₂ blocks₂ >>= k₂)) :
    e₁ = e₂ := by
  apply RawFree.op_bind_effect_eq
  simpa only [Free.toRaw_bind, Free.toRaw_op] using
    congrArg (Free.toRaw (E := E)) h

private theorem Free.op_bind_payload_eq
    (e : E γ)
    (blocks₁ blocks₂ :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      Free E (eS.blockCtx γ e t) (eS.blockOutputs γ e t))
    (k₁ k₂ : eS.output γ e → Free E γ α)
    (h :
      (Free.op e blocks₁ >>= k₁) =
        (Free.op e blocks₂ >>= k₂)) :
    blocks₁ = blocks₂ ∧ k₁ = k₂ := by
  have hraw :
      (RawFree.op e (fun t input =>
          Free.toRaw (blocks₁ t input)) >>=
        fun output => Free.toRaw (k₁ output)) =
      (RawFree.op e (fun t input =>
          Free.toRaw (blocks₂ t input)) >>=
        fun output => Free.toRaw (k₂ output)) := by
    simpa only [Free.toRaw_bind, Free.toRaw_op] using
      congrArg (Free.toRaw (E := E)) h
  rcases (RawFree.op_bind_inj e e _ _ _ _).mp hraw with
    ⟨_, hOp, hk⟩
  have hblocks :=
    RawFree.op_injective e (eq_of_heq hOp)
  have hk := eq_of_heq hk
  constructor
  · funext t input
    apply Free.toRaw_injective
    exact congrFun (congrFun hblocks t) input
  · funext output
    apply Free.toRaw_injective
    exact congrFun hk output

@[simp]
theorem Free.op_bind_inj
    {e₁ e₂ : E γ}
    {blocks₁ :
      (t : eS.blockTag γ e₁) →
      eS.blockInputs γ e₁ t →
      Free E (eS.blockCtx γ e₁ t) (eS.blockOutputs γ e₁ t)}
    {blocks₂ :
      (t : eS.blockTag γ e₂) →
      eS.blockInputs γ e₂ t →
      Free E (eS.blockCtx γ e₂ t) (eS.blockOutputs γ e₂ t)}
    {k₁ : eS.output γ e₁ → Free E γ α}
    {k₂ : eS.output γ e₂ → Free E γ α} :
    bind (α := no_index _) (Free.op e₁ blocks₁) k₁ =
        bind (α := no_index _) (Free.op e₂ blocks₂) k₂ ↔
      ∃ _h : e₁ = e₂,
        HEq (Free.op e₁ blocks₁) (Free.op e₂ blocks₂) ∧
          HEq k₁ k₂ := by
  constructor
  · intro h
    have he := Free.op_bind_effect_eq h
    subst e₂
    rcases Free.op_bind_payload_eq e₁ blocks₁ blocks₂ k₁ k₂ h with
      ⟨hblocks, hk⟩
    exact ⟨rfl,
      heq_of_eq (congrArg (Free.op e₁) hblocks),
      heq_of_eq hk⟩
  · rintro ⟨he, hOp, hk⟩
    subst e₂
    rw [eq_of_heq hOp, eq_of_heq hk]

@[simp]
theorem Free.op_bind_inj'
    {e₁ e₂ : E γ}
    {blocks₁ :
      (t : eS.blockTag γ e₁) →
      eS.blockInputs γ e₁ t →
      Free E (eS.blockCtx γ e₁ t) (eS.blockOutputs γ e₁ t)}
    {blocks₂ :
      (t : eS.blockTag γ e₂) →
      eS.blockInputs γ e₂ t →
      Free E (eS.blockCtx γ e₂ t) (eS.blockOutputs γ e₂ t)}
    {k : eS.output γ e₁ →
      Free E γ (eS.output γ e₂)} :
    @Eq (no_index _) (bind (α := no_index _) (Free.op e₁ blocks₁) k)
        (Free.op e₂ blocks₂) ↔
      ∃ _h : e₁ = e₂,
        HEq (Free.op e₁ blocks₁) (Free.op e₂ blocks₂) ∧
          HEq k (fun x : eS.output γ e₂ =>
            (pure x : Free E γ (eS.output γ e₂))) := by
  simpa only [bind_pure] using
    @Free.op_bind_inj _ _ _ _ _ e₁ e₂ blocks₁ blocks₂ k
      (fun x : eS.output γ e₂ =>
        (pure x : Free E γ (eS.output γ e₂)))

abbrev Free.Family :=
  fun i : Γ × Type v => Free E i.1 i.2

def Free.toRawAt (i : Γ × Type v) :
    Free.Family (E := E) i → IxPoly.W (Eff.Step Γ E) i :=
  fun x => Free.toRaw x

def Free.ofRawAt (i : Γ × Type v) :
    IxPoly.W (Eff.Step Γ E) i → Free.Family (E := E) i :=
  fun x => Free.ofRaw x

def Free.roll
    {γ : Γ} {α : Type v}
    (x : Eff.Step Γ E (Free.Family (E := E)) (γ, α)) :
    Free E γ α :=
  Free.ofRaw <|
    IxPoly.W.roll (IxPoly.map (Free.toRawAt (E := E)) _ x)

@[simp]
theorem Free.toRaw_roll
    {γ : Γ} {α : Type v}
    (x : Eff.Step Γ E (Free.Family (E := E)) (γ, α)) :
    Free.toRaw (Free.roll x) =
      IxPoly.W.roll (IxPoly.map (Free.toRawAt (E := E)) _ x) :=
  ExactCodensity.equiv.apply_symm_apply _

theorem Free.ofRaw_roll
    {i : Γ × Type v}
    (x : Eff.Step Γ E (RawFree.At E) i) :
    Free.ofRawAt i (IxPoly.W.roll x) =
      Free.roll
        (IxPoly.map (Free.ofRawAt (E := E)) i x) := by
  rcases i with ⟨γ, α⟩
  rcases x with ⟨p, children⟩
  apply Free.toRaw_injective
  rw [Free.toRaw_roll]
  simp only [IxPoly.map, Free.toRawAt, Free.ofRawAt,
    Free.toRaw_ofRaw]

private theorem Free.roll_ret
    {γ : Γ} {α : Type v} (x : α) :
    Free.roll (E := E) (Eff.Step.ret (γ := γ) x) =
      (pure x : Free E γ α) := by
  apply Free.toRaw_injective
  simp only [Free.toRaw_roll, Free.toRaw_pure, IxPoly.map,
    IxPoly.W.roll, Eff.Step.ret]
  congr 2
  funext field
  exact PEmpty.elim field

private theorem Free.roll_op
    {γ : Γ} {α : Type v}
    (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      Free E (eS.blockCtx γ e t) (eS.blockOutputs γ e t))
    (k : eS.output γ e → Free E γ α) :
    Free.roll (E := E) (Eff.Step.op e blocks k) =
      Free.op e blocks >>= k := by
  apply Free.toRaw_injective
  rw [Free.toRaw_roll, Free.toRaw_bind, Free.toRaw_op]
  change
    IxPoly.W.roll
        (IxPoly.map (Free.toRawAt (E := E)) _
          (Eff.Step.op e blocks k)) =
      RawFree.bind
        (RawFree.op e (fun t input =>
          Free.toRaw (blocks t input)))
        (fun output => Free.toRaw (k output))
  unfold RawFree.op
  rw [RawFree.bind]
  simp only [IxPoly.map, IxPoly.W.roll, Eff.Step.op]
  congr 2
  funext field
  cases field <;> rfl

protected def Free.recOn
    {motive :
      (γ : Γ) → (α : Type v) → Free E γ α → Sort w}
    {γ : Γ} {α : Type v} (x : Free E γ α)
    (ret :
      ∀ {γ : Γ} {α : Type v} (value : α),
        motive γ α (pure value))
    (op :
      ∀ {γ : Γ} {α : Type v}
        (e : E γ)
        (blocks :
          (t : eS.blockTag γ e) →
          eS.blockInputs γ e t →
          Free E (eS.blockCtx γ e t) (eS.blockOutputs γ e t))
        (k : eS.output γ e → Free E γ α),
        (∀ t input,
          motive (eS.blockCtx γ e t) (eS.blockOutputs γ e t)
            (blocks t input)) →
        (∀ output, motive γ α (k output)) →
        motive γ α (Free.op e blocks >>= k)) :
    motive γ α x := by
  have h : Free.ofRawAt (γ, α) (Free.toRaw x) = x :=
    Free.ofRaw_toRaw x
  rw [← h]
  exact RawFree.recOn
    (motive := fun i raw =>
      motive i.1 i.2 (Free.ofRawAt i raw))
    (fun {i} rawLayer ih => by
      let layer : Eff.Step Γ E (Free.Family (E := E)) i :=
        IxPoly.map (Free.ofRawAt (E := E)) i rawLayer
      have hroll :
          Free.roll layer =
            Free.ofRawAt i (IxPoly.W.roll rawLayer) := by
        simpa only [layer, IxPoly.map] using
          (Free.ofRaw_roll rawLayer).symm
      have layerIh :
          ∀ field,
            motive
              ((Eff.Step Γ E).Elem i layer.1 field).1
              ((Eff.Step Γ E).Elem i layer.1 field).2
              (layer.2 field) := by
        intro field
        exact ih field
      rw [← hroll]
      exact Eff.Step.casesOn layer
        (motive := fun i layer =>
          (∀ field,
            motive
              ((Eff.Step Γ E).Elem i layer.1 field).1
              ((Eff.Step Γ E).Elem i layer.1 field).2
              (layer.2 field)) →
          motive i.1 i.2 (Free.roll layer))
        (fun value _ => by
          rw [Free.roll_ret]
          exact ret value)
        (fun e blocks k ih => by
          rw [Free.roll_op]
          exact op e blocks k
            (fun t input => ih (.inr ⟨t, input⟩))
            (fun output => ih (.inl output)))
        layerIh)
    (Free.toRaw x)

protected def Free.casesOn
    {motive :
      (γ : Γ) → (α : Type v) → Free E γ α → Sort w}
    {γ : Γ} {α : Type v} (x : Free E γ α)
    (ret :
      ∀ {γ : Γ} {α : Type v} (value : α),
        motive γ α (pure value))
    (op :
      ∀ {γ : Γ} {α : Type v}
        (e : E γ)
        (blocks :
          (t : eS.blockTag γ e) →
          eS.blockInputs γ e t →
          Free E (eS.blockCtx γ e t) (eS.blockOutputs γ e t))
        (k : eS.output γ e → Free E γ α),
        motive γ α (Free.op e blocks >>= k)) :
    motive γ α x :=
  x.recOn ret (fun e blocks k _ _ => op e blocks k)

def Free.interp
    {M : Γ → Type v → Type w}
    [monadM : (γ : Γ) → Monad (M γ)]
    (handler : Eff.Handler E M)
    (x : Free E γ α) :
    M γ α :=
  RawFree.interp monadM handler (Free.toRaw x)

@[simp]
theorem Free.interp_pure
    {M : Γ → Type v → Type w}
    [monadM : (γ : Γ) → Monad (M γ)]
    (handler : Eff.Handler E M)
    (x : α) :
    Free.interp handler (pure x : Free E γ α) =
      @pure (M γ) (monadM γ).toApplicative.toPure α x :=
  rfl

@[simp]
theorem Free.interp_bind
    {M : Γ → Type v → Type w}
    [monadM : (γ : Γ) → Monad (M γ)]
    [lawfulM : (γ : Γ) → @LawfulMonad (M γ) (monadM γ)]
    (handler : Eff.Handler E M)
    (x : Free E γ α)
    (f : α → Free E γ β) :
    Free.interp handler (x >>= f) =
      @Bind.bind (M γ) (monadM γ).toBind _ _
        (Free.interp handler x)
        (fun a => Free.interp handler (f a)) := by
  rw [Free.interp, Free.toRaw_bind]
  exact RawFree.interp_bind monadM lawfulM handler
    (Free.toRaw x)
    (fun a => Free.toRaw (f a))

@[simp]
theorem Free.interp_op
    {M : Γ → Type v → Type w}
    [monadM : (γ : Γ) → Monad (M γ)]
    [lawfulM : (γ : Γ) → @LawfulMonad (M γ) (monadM γ)]
    (handler : Eff.Handler E M)
    (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      Free E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)) :
    Free.interp (α := no_index _) handler (Free.op e blocks) =
      handler e (fun t input =>
        Free.interp handler (blocks t input)) := by
  letI := monadM γ
  letI := lawfulM γ
  rw [Free.interp, Free.toRaw_op]
  exact RawFree.interp_op monadM lawfulM handler e
    (fun t input => Free.toRaw (blocks t input))

def Free.extendL
    {Γ : Type u} {E F : Γ → Type u} [sE: Eff.Spec E] [sF: Eff.Spec F]
    (γ : Γ) (α : Type v) : Free E γ α → Free (F ⊕ₑ E) γ α :=
  Free.interp (fun e blocks =>
    op (E := F ⊕ₑ E) (.inr e) blocks
  )

def Free.interpL
    {Γ : Type u} {E F : Γ → Type u} [sE: Eff.Spec E] [sF: Eff.Spec F]
    {γ : Γ} {α : Type v} (handler : Eff.Handler F (Free E)) :
  Free (F ⊕ₑ E) γ α → Free E γ α := interp (fun e i => match e with
    | .inl e => handler e i
    | .inr e => op e i
  )

def Free.UnusedL {Γ} {γ : Γ} {F E : Γ → Type u} [sF: Eff.Spec F] [sE: Eff.Spec E] : Free (F ⊕ₑ E) γ α → Prop :=
  fun y => ∃ (x : Free E γ α), Free.extendL γ α x = y

@[simp]
theorem Free.unusedL_extendL
    {Γ : Type u} {γ : Γ} {F E : Γ → Type u}
    [sF : Eff.Spec F] [sE : Eff.Spec E]
    (x : Free E γ α) :
    UnusedL (F := F) (Free.extendL γ α x) :=
  ⟨x, rfl⟩

theorem Free.unusedL_op_bind {Γ} {γ : Γ} {F E : Γ → Type u} [sF: Eff.Spec F] [sE: Eff.Spec E] {e : E γ ⊕ F γ}
    {f : Eff.Spec.output (tag := E ⊕ₑ F) γ e → Free (E ⊕ₑ F) γ α}
    {blocks : (t : Eff.Spec.blockTag (tag := E ⊕ₑ F) γ e) →
        Eff.Spec.blockInputs (tag := E ⊕ₑ F) γ e t →
        Free (E ⊕ₑ F) (Eff.Spec.blockCtx (tag := E ⊕ₑ F) γ e t) (Eff.Spec.blockOutputs (tag := E ⊕ₑ F) γ e t)} :
    (UnusedL (op e blocks >>= f)) ↔ (e.isRight ∧ (∀ t i, (blocks t i).UnusedL) ∧  ∀ a, UnusedL (f a)) := by
  apply Iff.intro
  · rintro ⟨x, h⟩
    cases x using Free.casesOn with
    | ret =>
      exfalso
      exact Free.pure_ne_op_bind h
    | op e' blocks k =>
      simp only [extendL, interp_bind, interp_op, op_bind_inj, exists_and_left, exists_prop] at h
      rcases h with ⟨hOp, rfl, hK⟩
      simp only [Sum.isRight_inr, true_and]
      simp only [heq_eq_eq, op_inj] at hOp
      cases hOp
      simp only [heq_eq_eq] at hK
      cases hK
      simp only
      apply And.intro <;> intros <;> apply Free.unusedL_extendL
  · rintro ⟨hE, hB, hK⟩
    rw [Sum.isRight_iff] at hE
    rcases hE with ⟨e, rfl⟩
    simp only [UnusedL, extendL]
    simp only [UnusedL] at hB hK ⊢
    choose B hB using hB
    choose K hK using hK
    exists op e B >>= K
    simp only [interp_bind, interp_op, op_bind_inj, heq_eq_eq, op_inj, exists_const]
    apply And.intro <;> ext <;> apply_assumption

end Freigen
