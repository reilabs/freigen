import Freigen.ITree.WF
import Freigen.CompM.MayReturn
import Freigen.Free.Basic

namespace Freigen.CompM

def WF {Γ : Type u} {E : Γ → Type u} [s: Eff.Spec E] {γ : Γ} {α : Type v} (t : CompM E γ α) : Prop :=
  ITree.WF (ExactCodensity.equiv t)

def toFree {Γ : Type u} {E : Γ → Type u} [s: Eff.Spec E] {γ : Γ} {α : Type v} (t : CompM E γ α) (h : WF t) :
    Free E γ α :=
  h.recC (motive := fun x _ => Free E x.γ x.α)
  (fun ⟨_, _, t⟩ _ recur =>
    t.casesOn (motive := fun (γ, α) t =>
      ((y : ITree.WF.Packed E) → ITree.WF.Child y ⟨γ, α, t⟩ → Free E y.γ y.α) → Free E γ α)
      (fun v _ => pure v)
      (fun e blocks k recur =>
        Free.op e (fun t i => recur ⟨_, _, blocks t i⟩  ITree.WF.Child.op_block) >>= (fun i =>
          recur ⟨_, _, k i⟩ ITree.WF.Child.op_cont
        )
      ) recur
  )

variable {Γ : Type u} {E : Γ → Type u} [eS : Eff.Spec E] {γ : Γ}

/-! ## Well-foundedness -/

private theorem child_block {α : Type v} {e : E γ}
    {blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      CompM E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)}
    {k : eS.output γ e → CompM E γ α} (t i) :
    ITree.WF.Child ⟨_, _, ExactCodensity.equiv (blocks t i)⟩
      ⟨γ, α, ExactCodensity.equiv (op e blocks >>= k)⟩ :=
  ITree.WF.Child.op_block (e := e)
    (blocks := fun t i => ExactCodensity.equiv (blocks t i))
    (k := fun o => ExactCodensity.equiv (k o))

private theorem child_cont {α : Type v} {e : E γ}
    {blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      CompM E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)}
    {k : eS.output γ e → CompM E γ α} (o) :
    ITree.WF.Child ⟨_, _, ExactCodensity.equiv (k o)⟩
      ⟨γ, α, ExactCodensity.equiv (op e blocks >>= k)⟩ :=
  ITree.WF.Child.op_cont (e := e)
    (blocks := fun t i => ExactCodensity.equiv (blocks t i))
    (k := fun o => ExactCodensity.equiv (k o))

@[simp]
theorem wf_pure {α : Type v} (a : α) : WF (pure a : CompM E γ α) :=
  Acc.intro _ fun _ h => absurd h ITree.WF.Child.not_ret

@[simp]
theorem wf_op_bind_iff {α : Type v} {e : E γ}
    {blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      CompM E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)}
    {k : eS.output γ e → CompM E γ α} :
    WF (bind (α := no_index _) (op e blocks) k) ↔ (∀ t i, WF (blocks t i)) ∧ ∀ o, WF (k o) := by
  constructor
  · intro h
    exact ⟨fun t i => h.inv (child_block t i), fun o => h.inv (child_cont o)⟩
  · rintro ⟨hb, hk⟩
    refine Acc.intro _ fun y hy => ?_
    rcases ITree.WF.Child.inv_op
        (blocks := fun t i => ExactCodensity.equiv (blocks t i))
        (k := fun o => ExactCodensity.equiv (k o)) hy with
      ⟨t, i, rfl⟩ | ⟨o, rfl⟩
    · exact hb t i
    · exact hk o

/-- Induction over well-founded computations: blocks and continuations of
an operation are smaller than the operation. -/
theorem WF.induction
    {motive : ∀ {γ : Γ} {α : Type v}, CompM E γ α → Prop}
    (pure : ∀ {γ : Γ} {α : Type v} (a : α), motive (pure a : CompM E γ α))
    (op : ∀ {γ : Γ} {α : Type v} (e : E γ)
      (blocks :
        (t : eS.blockTag γ e) →
        eS.blockInputs γ e t →
        CompM E (eS.blockCtx γ e t) (eS.blockOutputs γ e t))
      (k : eS.output γ e → CompM E γ α),
      (∀ t i, WF (blocks t i)) → (∀ o, WF (k o)) →
      (∀ t i, motive (blocks t i)) → (∀ o, motive (k o)) →
      motive (CompM.op e blocks >>= k))
    {α : Type v} {x : CompM E γ α} (h : WF x) : motive x := by
  suffices ∀ p : ITree.WF.Packed E, Acc ITree.WF.Child p →
      ∀ x : CompM E p.γ p.α, ExactCodensity.equiv x = p.t → motive x from
    this _ h x rfl
  intro p hp
  induction hp with
  | intro p hp ih =>
    rcases p with ⟨γ, α, t⟩
    intro (x : CompM E γ α) (hx : ExactCodensity.equiv x = t)
    subst hx
    rcases eq_pure_or_op_bind x with ⟨a, rfl⟩ | ⟨e, blocks, k, rfl⟩
    · exact pure a
    · exact op e blocks k
        (fun t i => hp _ (child_block t i)) (fun o => hp _ (child_cont o))
        (fun t i => ih _ (child_block t i) _ rfl)
        (fun o => ih _ (child_cont o) _ rfl)

/-- The continuation of a bind only needs to be well-founded on results the
first computation can actually return. -/
theorem wf_bind {α β : Type v} {x : CompM E γ α} {f : α → CompM E γ β}
    (hx : WF x) (hf : ∀ a, x.MayReturn a → WF (f a)) : WF (x >>= f) := by
  revert f
  refine WF.induction
    (motive := fun {γ α} (x : CompM E γ α) =>
      ∀ {β : Type v} {f : α → CompM E γ β},
        (∀ a, x.MayReturn a → WF (f a)) → WF (x >>= f))
    ?_ ?_ hx
  · intro _ _ a _ f hf
    simpa using hf a (.pure a)
  · intro _ _ e blocks k hb _ _ ih _ f hf
    rw [bind_assoc, wf_op_bind_iff]
    exact ⟨hb, fun o => ih o fun a ha => hf a (.op o ha)⟩

@[simp]
theorem wf_map {α β : Type v} {x : CompM E γ α} (f : α → β) (hx : WF x) :
    WF (f <$> x) := by
  rw [← bind_pure_comp]
  exact wf_bind hx fun a _ => wf_pure (f a)

@[simp]
theorem wf_op_iff {e : E γ}
    {blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      CompM E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)} :
    WF (α := no_index _) (op e blocks) ↔ ∀ t i, WF (blocks t i) := by
  rw [← bind_pure (op e blocks), wf_op_bind_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, wf_pure⟩⟩

theorem wf_tauBlocks [Eff.Has.{u, 0} Eff.Tau E] (t) (i) :
    WF (tauBlocks (E := E) (γ := γ) t i) :=
  nomatch Eff.Step.Has.lowerBlockTag (F := Eff.Tau) (E := E) t

theorem wf_failBlocks [Eff.Has.{u, 0} Eff.Fail E] (t) (i) :
    WF (failBlocks (E := E) (γ := γ) t i) :=
  nomatch Eff.Step.Has.lowerBlockTag (F := Eff.Fail) (E := E) t

theorem wf_failCont [Eff.Has.{u, 0} Eff.Fail E] {α : Type} (o) :
    WF (failCont (E := E) (γ := γ) (α := α) o) :=
  nomatch Eff.Step.Has.lowerOutput (F := Eff.Fail) (E := E) o

@[simp]
theorem wf_tick_bind_iff [Eff.Has.{u, 0} Eff.Tau E] {α : Type}
    {k : Unit → CompM E γ α} :
    WF (tick >>= k) ↔ WF (k ()) := by
  rw [tick_bind k tauBlocks, wf_op_bind_iff]
  refine ⟨fun ⟨_, h⟩ => h (Eff.Step.Has.liftOutput PUnit.unit),
    fun h => ⟨fun t => ?_, fun _ => h⟩⟩
  exact nomatch Eff.Step.Has.lowerBlockTag (F := Eff.Tau) (E := E) t

@[simp]
theorem wf_fail [Eff.Has.{u, 0} Eff.Fail E] {α : Type} :
    WF (fail : CompM E γ α) := by
  rw [fail_eq failBlocks failCont, wf_op_bind_iff]
  refine ⟨fun t => ?_, fun o => ?_⟩
  · exact nomatch Eff.Step.Has.lowerBlockTag (F := Eff.Fail) (E := E) t
  · exact nomatch Eff.Step.Has.lowerOutput (F := Eff.Fail) (E := E) o

/-! ## Reification

Since well-foundedness is a proposition, these hold for any choice of
proofs. Reification has no bind law: a continuation that is only
well-founded on reachable results has no reification at other values. Binds
are handled once, on the whole erasure pipeline (`CompM.Implements`). -/

theorem toFree_congr {α : Type v} {x y : CompM E γ α} (h : x = y)
    (hx : WF x) (hy : WF y) : toFree x hx = toFree y hy := by
  subst h
  rfl

@[simp]
theorem toFree_pure {α : Type v} (a : α) (h : WF (pure a : CompM E γ α)) :
    toFree (pure a) h = pure a := by
  rw [toFree, Acc.recC]
  rfl

theorem toFree_op_bind {α : Type v} (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      CompM E (eS.blockCtx γ e t) (eS.blockOutputs γ e t))
    (k : eS.output γ e → CompM E γ α)
    (h : WF (op e blocks >>= k))
    (hb : ∀ t i, WF (blocks t i)) (hk : ∀ o, WF (k o)) :
    toFree (op e blocks >>= k) h =
      Free.op e (fun t i => toFree (blocks t i) (hb t i)) >>=
        fun o => toFree (k o) (hk o) := by
  rw [toFree, Acc.recC]
  rfl

@[simp]
theorem mayReturn_toFree_iff {α : Type v} {x : CompM E γ α} {h : WF x}
    {a : α} : (toFree x h).MayReturn a ↔ x.MayReturn a := by
  refine WF.induction
    (motive := fun {γ α} (x : CompM E γ α) =>
      ∀ (h : WF x) (a : α), (toFree x h).MayReturn a ↔ x.MayReturn a)
    ?_ ?_ h h a
  · intro _ _ b _ _
    simp
  · intro _ _ e blocks k hb hk _ ih _ _
    rw [toFree_op_bind e blocks k _ hb hk]
    simp [ih]

end Freigen.CompM
