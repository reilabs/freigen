import Freigen.Free.MayReturn

/-!
Laws for the effect-stack operations used to erase effects: extending with
an unused effect, eliding it again, and interpreting the leftmost effect.
-/

namespace Freigen.Free

variable {Γ : Type u} {E F : Γ → Type u}
  [sE : Eff.Spec.{u, v} E] [sF : Eff.Spec.{u, v} F]
  {γ : Γ} {α β : Type v}

/-! ## Extension -/

@[simp]
theorem extendL_pure (a : α) :
    extendL (F := F) γ α (pure a : Free E γ α) = pure a :=
  rfl

@[simp]
theorem extendL_bind (x : Free E γ α) (f : α → Free E γ β) :
    extendL (F := F) γ β (x >>= f) =
      extendL γ α x >>= fun a => extendL γ β (f a) :=
  interp_bind _ x f

@[simp]
theorem extendL_op (e : E γ)
    (blocks :
      (t : sE.blockTag γ e) →
      sE.blockInputs γ e t →
      Free E (sE.blockCtx γ e t) (sE.blockOutputs γ e t)) :
    extendL (F := F) γ (no_index _) (op e blocks) =
      op (E := F ⊕ₑ E) (.inr e) fun t i => extendL _ _ (blocks t i) :=
  interp_op _ e blocks

theorem extendL_injective :
    Function.Injective (extendL (E := E) (F := F) γ α) := by
  intro x y h
  induction x using Free.recOn with
  | ret a =>
    cases y using Free.casesOn with
    | ret b => simpa [pure_inj] using h
    | op e blocks k =>
      simp only [extendL_pure, extendL_bind, extendL_op] at h
      exact absurd h pure_ne_op_bind
  | op e blocks k ihb ihk =>
    cases y using Free.casesOn with
    | ret b =>
      simp only [extendL_pure, extendL_bind, extendL_op] at h
      exact absurd h.symm pure_ne_op_bind
    | op e' blocks' k' =>
      simp only [extendL_bind, extendL_op, op_bind_inj] at h
      rcases h with ⟨he, hb, hk⟩
      cases he
      simp only [heq_eq_eq, op_inj] at hb hk
      have hb : blocks = blocks' := by
        funext t i
        exact ihb t i (congrFun (congrFun hb t) i)
      have hk : k = k' := by
        funext o
        exact ihk o (congrFun hk o)
      rw [hb, hk]

@[simp]
theorem mayReturn_extendL_iff {x : Free E γ α} {a : α} :
    (extendL (F := F) γ α x).MayReturn a ↔ x.MayReturn a := by
  induction x using Free.recOn with
  | ret b => simp
  | op e blocks k _ ih => simp [ih]

/-! ## Unused effects -/

@[simp]
theorem unusedL_pure (a : α) : UnusedL (F := F) (pure a : Free (F ⊕ₑ E) γ α) :=
  ⟨pure a, rfl⟩

/-- A bind leaves an effect unused when its first part does, and the
continuation does on every reachable result. -/
theorem unusedL_bind {x : Free (F ⊕ₑ E) γ α} {f : α → Free (F ⊕ₑ E) γ β}
    (hx : UnusedL x) (hf : ∀ a, x.MayReturn a → UnusedL (f a)) :
    UnusedL (x >>= f) := by
  rcases hx with ⟨y, rfl⟩
  induction y using Free.recOn with
  | ret a => simpa using hf a (by simp)
  | op e blocks k _ ih =>
    simp only [extendL_bind, extendL_op, bind_assoc]
    rw [unusedL_op_bind]
    refine ⟨rfl, fun t i => unusedL_extendL _, fun o => ih o fun a ha => hf a ?_⟩
    simp only [extendL_bind, extendL_op, mayReturn_op_bind_iff]
    exact ⟨o, ha⟩

/-! ## Elision -/

theorem noLeft_of_unusedL {m : Free (F ⊕ₑ E) γ α} (hm : UnusedL m) :
    RawFree.NoLeft (toRaw m) := by
  rcases hm with ⟨y, rfl⟩
  induction y using Free.recOn with
  | ret a => exact .ret
  | op e blocks k ihb ihk =>
    rw [extendL_bind, extendL_op, toRaw_bind, toRaw_op]
    change RawFree.NoLeft (RawFree.bind (RawFree.op _ _) _)
    rw [RawFree.bind_op]
    exact .op fun
      | .inl o => ihk o
      | .inr ⟨t, i⟩ => ihb t i

/-- Remove an unused effect. -/
def elideL (m : Free (F ⊕ₑ E) γ α) (hm : UnusedL m) : Free E γ α :=
  ofRaw (RawFree.elideL (toRaw m) (noLeft_of_unusedL hm))

@[simp]
theorem elideL_pure (a : α) (hm : UnusedL (F := F) (pure a : Free (F ⊕ₑ E) γ α)) :
    elideL (pure a) hm = pure a :=
  rfl

theorem elideL_op_bind {e : E γ}
    {blocks :
      (t : sE.blockTag γ e) →
      sE.blockInputs γ e t →
      Free (F ⊕ₑ E) (sE.blockCtx γ e t) (sE.blockOutputs γ e t)}
    {k : sE.output γ e → Free (F ⊕ₑ E) γ α}
    (hm : UnusedL (op (E := F ⊕ₑ E) (.inr e) blocks >>= k))
    (hb : ∀ t i, UnusedL (blocks t i)) (hk : ∀ o, UnusedL (k o)) :
    elideL (op (E := F ⊕ₑ E) (.inr e) blocks >>= k) hm =
      op e (fun t i => elideL (blocks t i) (hb t i)) >>=
        fun o => elideL (k o) (hk o) := by
  apply toRaw_injective
  have hraw : toRaw (op (E := F ⊕ₑ E) (.inr e) blocks >>= k) =
      RawFree.op (E := F ⊕ₑ E) (.inr e) (fun t i => toRaw (blocks t i)) >>=
        fun o => toRaw (k o) := by
    simp only [toRaw_bind, toRaw_op]
  have key : ∀ (r : RawFree (F ⊕ₑ E) γ α) (hr : RawFree.NoLeft r),
      r = toRaw (op (E := F ⊕ₑ E) (.inr e) blocks >>= k) →
      RawFree.elideL r hr =
        toRaw (op e (fun t i => elideL (blocks t i) (hb t i)) >>=
          fun o => elideL (k o) (hk o)) := by
    rintro r hr h
    rw [hraw] at h
    subst h
    rw [RawFree.elideL_op_bind hr (fun t i => noLeft_of_unusedL (hb t i))
      (fun o => noLeft_of_unusedL (hk o))]
    simp only [toRaw_bind, toRaw_op, elideL, toRaw_ofRaw]
  rw [elideL, toRaw_ofRaw]
  exact key _ _ rfl

theorem not_unusedL_op_inl_bind {e : F γ}
    {blocks :
      (t : sF.blockTag γ e) →
      sF.blockInputs γ e t →
      Free (F ⊕ₑ E) (sF.blockCtx γ e t) (sF.blockOutputs γ e t)}
    {k : sF.output γ e → Free (F ⊕ₑ E) γ α} :
    ¬ UnusedL (op (E := F ⊕ₑ E) (.inl e) blocks >>= k) := by
  rw [unusedL_op_bind]
  exact fun h => Bool.false_ne_true h.1

@[simp]
theorem extendL_elideL (m : Free (F ⊕ₑ E) γ α) (hm : UnusedL m) :
    extendL γ α (elideL m hm) = m := by
  induction m using Free.recOn with
  | ret a => rfl
  | op e blocks k ihb ihk =>
    rcases e with e | e
    · exact absurd hm not_unusedL_op_inl_bind
    · have h := (unusedL_op_bind (E := F) (F := E)).mp hm
      rw [elideL_op_bind hm h.2.1 h.2.2, extendL_bind, extendL_op]
      simp only [ihb, ihk]

theorem elideL_eq_iff {m : Free (F ⊕ₑ E) γ α} {hm : UnusedL m}
    {y : Free E γ α} :
    elideL m hm = y ↔ m = extendL (F := F) γ α y := by
  constructor
  · rintro rfl
    simp
  · rintro rfl
    exact extendL_injective (F := F) (by simp)

@[simp]
theorem elideL_extendL (y : Free E γ α) (hm : UnusedL (extendL (F := F) γ α y)) :
    elideL (extendL γ α y) hm = y :=
  elideL_eq_iff.mpr rfl

theorem elideL_bind {x : Free (F ⊕ₑ E) γ α} {f : α → Free (F ⊕ₑ E) γ β}
    (hm : UnusedL (x >>= f)) (hx : UnusedL x) (hf : ∀ a, UnusedL (f a)) :
    elideL (x >>= f) hm = elideL x hx >>= fun a => elideL (f a) (hf a) := by
  rw [elideL_eq_iff]
  simp

/-! ## Interpreting the leftmost effect -/

@[simp]
theorem interpL_pure (handler : Eff.Handler F (Free E)) (a : α) :
    interpL (γ := γ) handler (pure a : Free (F ⊕ₑ E) γ α) = pure a :=
  rfl

@[simp]
theorem interpL_bind (handler : Eff.Handler F (Free E))
    (x : Free (F ⊕ₑ E) γ α) (f : α → Free (F ⊕ₑ E) γ β) :
    interpL handler (x >>= f) =
      interpL handler x >>= fun a => interpL handler (f a) :=
  interp_bind _ x f

@[simp]
theorem interpL_op_inl (handler : Eff.Handler F (Free E)) (e : F γ)
    (blocks :
      (t : sF.blockTag γ e) →
      sF.blockInputs γ e t →
      Free (F ⊕ₑ E) (sF.blockCtx γ e t) (sF.blockOutputs γ e t)) :
    interpL (α := no_index _) handler (op (E := F ⊕ₑ E) (.inl e) blocks) =
      handler e fun t i => interpL handler (blocks t i) :=
  interp_op _ (E := F ⊕ₑ E) (.inl e) blocks

@[simp]
theorem interpL_op_inr (handler : Eff.Handler F (Free E)) (e : E γ)
    (blocks :
      (t : sE.blockTag γ e) →
      sE.blockInputs γ e t →
      Free (F ⊕ₑ E) (sE.blockCtx γ e t) (sE.blockOutputs γ e t)) :
    interpL (α := no_index _) handler (op (E := F ⊕ₑ E) (.inr e) blocks) =
      op e fun t i => interpL handler (blocks t i) :=
  interp_op _ (E := F ⊕ₑ E) (.inr e) blocks

end Freigen.Free
