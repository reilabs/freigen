import Freigen.ITree.Basic
import Freigen.ExactCodensity
import Freigen.Eff

namespace Freigen

def CompM
    {Γ : Type u} (E : Γ → Type u) [Eff.Spec E]
    (γ : Γ) (α : Type v) : Type _ :=
  ExactCodensity (ITree E γ) α

variable
  {Γ : Type u} {E : Γ → Type u} [eS : Eff.Spec E]
  {γ : Γ} {α β : Type}

instance {γ : Γ} : Monad (CompM E γ) :=
  inferInstanceAs (Monad (ExactCodensity (ITree E γ)))

instance {γ : Γ} : LawfulMonad (CompM E γ) :=
  inferInstanceAs (LawfulMonad (ExactCodensity (ITree E γ)))

namespace CompM

private def treeEquiv {γ : Γ} {α : Type v} :
    CompM E γ α ≃ ITree E γ α :=
  ExactCodensity.equiv

private def actionEquiv
    {I : Type ui} {O : Type uo}
    {F : IxPoly I O}
    {X : I → Type ux} {Y : I → Type uy}
    (e : (i : I) → X i ≃ Y i)
    (o : O) :
    F X o ≃ F Y o where
  toFun := IxPoly.map (fun i => e i) o
  invFun := IxPoly.map (fun i => (e i).symm) o
  left_inv x := by
    rw [IxPoly.map_map]
    simpa only [Equiv.symm_apply_apply] using IxPoly.map_id o x
  right_inv y := by
    rw [IxPoly.map_map]
    simpa only [Equiv.apply_symm_apply] using IxPoly.map_id o y

def observe {γ : Γ} {α : Type v} :
    CompM E γ α ≃
      Eff.Step Γ E (fun i => CompM E i.1 i.2) (γ, α) :=
  treeEquiv.trans <|
    ITree.observe.trans <|
      actionEquiv (fun _ => treeEquiv.symm) (γ, α)

def roll {γ : Γ} {α : Type v} :
    Eff.Step Γ E (fun i => CompM E i.1 i.2) (γ, α) →
      CompM E γ α :=
  observe.symm

@[simp]
theorem observe_roll
    {γ : Γ} {α : Type v}
    (x : Eff.Step Γ E (fun i => CompM E i.1 i.2) (γ, α)) :
    observe (roll x) = x :=
  observe.apply_symm_apply x

@[simp]
theorem roll_observe
    {γ : Γ} {α : Type v}
    (x : CompM E γ α) :
    roll (observe x) = x :=
  observe.symm_apply_apply x

def corec
    {A : Γ × Type v → Type w}
    (f : (i : Γ × Type v) → A i → Eff.Step Γ E A i)
    {i : Γ × Type v}
    (a : A i) :
    CompM E i.1 i.2 :=
  treeEquiv.symm (ITree.corec f a)

theorem observe_corec
    {A : Γ × Type v → Type w}
    (f : (i : Γ × Type v) → A i → Eff.Step Γ E A i)
    {i : Γ × Type v}
    (a : A i) :
    observe (corec f a) =
      IxPoly.map
        (fun _ y => corec f y)
        i
        (f i a) := by
  change
    IxPoly.map (fun _ x => treeEquiv.symm x) i
      (ITree.observe
        (treeEquiv (treeEquiv.symm (ITree.corec f a)))) =
    IxPoly.map (fun _ y => treeEquiv.symm (ITree.corec f y)) i (f i a)
  rw [Equiv.apply_symm_apply, ITree.observe_corec]
  rw [IxPoly.map_map]

theorem eq_of_observe_eq
    {γ : Γ} {α : Type v}
    {x y : CompM E γ α}
    (h : observe x = observe y) :
    x = y :=
  observe.injective h

private theorem bind_def
    {γ : Γ} {α β : Type}
    (x : CompM E γ α) (f : α → CompM E γ β) :
    x >>= f = ⟨fun g => x.run fun a => (f a).run g, by
      intros
      conv => lhs; rw [←x.exact]
      rw [bind_assoc]
      simp only [ExactCodensity.exact]⟩ := by
  rfl

def tick {γ : Γ} [Eff.Has.{u, 0} Eff.Tau E] :
    CompM E γ Unit :=
  ⟨fun f => ITree.tau (f ()), by simp⟩

def fail {γ : Γ} [Eff.Has Eff.Fail E] :
    CompM E γ α :=
  ⟨fun _ => ITree.fail, by simp⟩

def op {γ : Γ} (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      CompM E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)) :
    CompM E γ (eS.output γ e) :=
  ⟨fun f => ITree.op e (fun t i => (blocks t i).run pure) f, by simp⟩

private def liftLCo
    {L R : Γ → Type u} [lS : Eff.Spec.{u, v} L] [rS : Eff.Spec.{u, v} R]
    (i : Γ × Type v) (x : CompM L i.1 i.2) :
    Eff.Step Γ (L ⊕ₑ R) (fun i => CompM L i.1 i.2) i :=
  Eff.Step.casesOn (observe x)
    (motive := fun i _ =>
      Eff.Step Γ (L ⊕ₑ R) (fun i => CompM L i.1 i.2) i)
    (fun value => Eff.Step.ret value)
    (fun e blocks k =>
      Eff.Step.op (show (L ⊕ₑ R) _ from Sum.inl e) blocks k)

def liftL
    {L R : Γ → Type u} [lS : Eff.Spec.{u, v} L] [rS : Eff.Spec.{u, v} R]
    {γ : Γ} {α : Type v} (x : CompM L γ α) :
    CompM (L ⊕ₑ R) γ α :=
  corec (i := (γ, α)) (liftLCo (L := L) (R := R)) x

private def liftRCo
    {L R : Γ → Type u} [lS : Eff.Spec.{u, v} L] [rS : Eff.Spec.{u, v} R]
    (i : Γ × Type v) (x : CompM R i.1 i.2) :
    Eff.Step Γ (L ⊕ₑ R) (fun i => CompM R i.1 i.2) i :=
  Eff.Step.casesOn (observe x)
    (motive := fun i _ =>
      Eff.Step Γ (L ⊕ₑ R) (fun i => CompM R i.1 i.2) i)
    (fun value => Eff.Step.ret value)
    (fun e blocks k =>
      Eff.Step.op (show (L ⊕ₑ R) _ from Sum.inr e) blocks k)

def liftR
    {L R : Γ → Type u} [lS : Eff.Spec.{u, v} L] [rS : Eff.Spec.{u, v} R]
    {γ : Γ} {α : Type v} (x : CompM R γ α) :
    CompM (L ⊕ₑ R) γ α :=
  corec (i := (γ, α)) (liftRCo (L := L) (R := R)) x

abbrev OpMap
    {Γ : Type u} (L R : Γ → Type u)
    [Eff.Spec.{u, v} L] [Eff.Spec.{u, v} R]
    (X : Γ × Type v → Type w) :=
  {i : Γ × Type v} → Eff.Step Γ L X i → Eff.Step Γ R X i

private def interpLCo
    {L R : Γ → Type u} [lS : Eff.Spec.{u, v} L] [rS : Eff.Spec.{u, v} R]
    (mapOp : OpMap L R (fun i => CompM (L ⊕ₑ R) i.1 i.2))
    (i : Γ × Type v) (x : CompM (L ⊕ₑ R) i.1 i.2) :
    Eff.Step Γ R (fun i => CompM (L ⊕ₑ R) i.1 i.2) i :=
  Eff.Step.casesOn (observe x)
    (motive := fun i _ =>
      Eff.Step Γ R (fun i => CompM (L ⊕ₑ R) i.1 i.2) i)
    (fun value => Eff.Step.ret value)
    (fun e blocks k => match e with
      | .inl e => mapOp (Eff.Step.op e blocks k)
      | .inr e => Eff.Step.op e blocks k)

def interpL
    {L R : Γ → Type u} [lS : Eff.Spec.{u, v} L] [rS : Eff.Spec.{u, v} R]
    {γ : Γ} {α : Type v} (x : CompM (L ⊕ₑ R) γ α)
    (mapOp : OpMap L R (fun i => CompM (L ⊕ₑ R) i.1 i.2)) :
    CompM R γ α :=
  corec (i := (γ, α)) (interpLCo mapOp) x

private def interpRCo
    {L R : Γ → Type u} [lS : Eff.Spec.{u, v} L] [rS : Eff.Spec.{u, v} R]
    (mapOp : OpMap R L (fun i => CompM (L ⊕ₑ R) i.1 i.2))
    (i : Γ × Type v) (x : CompM (L ⊕ₑ R) i.1 i.2) :
    Eff.Step Γ L (fun i => CompM (L ⊕ₑ R) i.1 i.2) i :=
  Eff.Step.casesOn (observe x)
    (motive := fun i _ =>
      Eff.Step Γ L (fun i => CompM (L ⊕ₑ R) i.1 i.2) i)
    (fun value => Eff.Step.ret value)
    (fun e blocks k => match e with
      | .inl e => Eff.Step.op e blocks k
      | .inr e => mapOp (Eff.Step.op e blocks k))

def interpR
    {L R : Γ → Type u} [lS : Eff.Spec.{u, v} L] [rS : Eff.Spec.{u, v} R]
    {γ : Γ} {α : Type v} (x : CompM (L ⊕ₑ R) γ α)
    (mapOp : OpMap R L (fun i => CompM (L ⊕ₑ R) i.1 i.2)) :
    CompM L γ α :=
  corec (i := (γ, α)) (interpRCo mapOp) x

def loop
    {γ : Γ} [Eff.Has Eff.Tau E]
    (body : α → CompM E γ (α ⊕ β)) (init : α) :
    CompM E γ β := {
  run := fun f => ITree.loop (fun a => (body a).run pure) init f
  exact := by
    intros
    apply ITree.loop_bind
}

theorem loop_def [Eff.Has Eff.Tau E]
  (body : α → CompM E γ (α ⊕ β))
  (s : α) :
  CompM.loop body s =
    body s >>= fun
      | .inr v  => pure v
      | .inl v => CompM.tick (E := E) (γ := γ) *> CompM.loop body v := by
  apply ExactCodensity.equiv.injective
  change (CompM.loop body s).run pure =
    ((body s >>= fun
      | .inr v => pure v
      | .inl v =>
        CompM.tick (E := E) (γ := γ) *> CompM.loop body v) :
        CompM E γ β).run pure
  simp only [loop, bind_def]
  rw [ITree.loop_def]
  rw [ExactCodensity.exact]
  congr 1
  funext x
  cases x <;> rfl

abbrev forInStepToSum : ForInStep α → α ⊕ α
  | .yield x => .inl x
  | .done x => .inr x

instance {γ : Γ} [Eff.Has Eff.Tau E] :
    ForIn (CompM E γ) Lean.Loop Unit where
  forIn _ init body := loop (fun a => forInStepToSum <$> (body () a)) init

end Freigen.CompM

/-! ## Observation laws

These describe `observe` on the monad operations, so that proofs about
`CompM` never see the codensity encoding or the underlying `ITree`. -/

namespace Freigen.CompM

variable
  {Γ : Type u} {E : Γ → Type u} [eS : Eff.Spec E]
  {γ : Γ}

@[simp]
theorem observe_pure {α : Type v} (x : α) :
    observe (pure x : CompM E γ α) = Eff.Step.ret x := by
  change IxPoly.map (fun _ => treeEquiv.symm) (γ, α)
    (ITree.observe (ITree.ret (E := E) (γ := γ) x)) = _
  rw [ITree.observe_ret, Eff.Step.map_ret]

@[simp]
theorem observe_op_bind {α : Type v} (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      CompM E (eS.blockCtx γ e t) (eS.blockOutputs γ e t))
    (k : eS.output γ e → CompM E γ α) :
    observe (bind (α := no_index _) (op e blocks) k) = Eff.Step.op e blocks k := by
  change IxPoly.map (fun _ => treeEquiv.symm) (γ, α)
    (ITree.observe (ITree.op e (fun t i => treeEquiv (blocks t i))
      (fun o => treeEquiv (k o)))) = _
  rw [ITree.observe_op]
  simp only [IxPoly.map, Eff.Step.op]
  congr 1
  funext x
  cases x <;> apply Equiv.symm_apply_apply

theorem roll_ret {α : Type v} (x : α) :
    roll (Eff.Step.ret x) = (pure x : CompM E γ α) :=
  observe.injective (by simp)

theorem roll_op {α : Type v} (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      CompM E (eS.blockCtx γ e t) (eS.blockOutputs γ e t))
    (k : eS.output γ e → CompM E γ α) :
    roll (Eff.Step.op e blocks k) = op e blocks >>= k :=
  observe.injective (by simp)

/-- Every computation is a return or an operation followed by a
continuation. -/
theorem eq_pure_or_op_bind {α : Type v} (x : CompM E γ α) :
    (∃ a, x = pure a) ∨
      ∃ (e : E γ) (blocks :
          (t : eS.blockTag γ e) →
          eS.blockInputs γ e t →
          CompM E (eS.blockCtx γ e t) (eS.blockOutputs γ e t))
        (k : eS.output γ e → CompM E γ α),
        x = op e blocks >>= k := by
  suffices h : ∀ (i : Γ × Type v)
      (s : Eff.Step Γ E (fun i => CompM E i.1 i.2) i),
      (∃ a, roll (γ := i.1) (α := i.2) s = pure a) ∨
        ∃ (e : E i.1) (blocks :
            (t : eS.blockTag i.1 e) →
            eS.blockInputs i.1 e t →
            CompM E (eS.blockCtx i.1 e t) (eS.blockOutputs i.1 e t))
          (k : eS.output i.1 e → CompM E i.1 i.2),
          roll (γ := i.1) (α := i.2) s = op e blocks >>= k by
    simpa only [roll_observe] using h (γ, α) (observe x)
  intro i s
  cases s using Eff.Step.casesOn with
  | ret a => exact .inl ⟨a, roll_ret a⟩
  | op e blocks k => exact .inr ⟨e, blocks, k, roll_op e blocks k⟩

theorem pure_inj {α : Type v} {a b : α} :
    (pure a : CompM E γ α) = pure b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have h := congrArg observe h
  simp only [observe_pure, Eff.Step.ret] at h
  injection h with h
  injection h

theorem pure_ne_op_bind {α : Type v} {a : α} {e : E γ}
    {blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      CompM E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)}
    {k : eS.output γ e → CompM E γ α} :
    pure a ≠ op e blocks >>= k := by
  intro h
  have h := congrArg observe h
  simp only [observe_pure, observe_op_bind, Eff.Step.ret, Eff.Step.op] at h
  injection h with h
  injection h

theorem op_bind_inj {α : Type v} {e₁ e₂ : E γ}
    {blocks₁ :
      (t : eS.blockTag γ e₁) →
      eS.blockInputs γ e₁ t →
      CompM E (eS.blockCtx γ e₁ t) (eS.blockOutputs γ e₁ t)}
    {blocks₂ :
      (t : eS.blockTag γ e₂) →
      eS.blockInputs γ e₂ t →
      CompM E (eS.blockCtx γ e₂ t) (eS.blockOutputs γ e₂ t)}
    {k₁ : eS.output γ e₁ → CompM E γ α}
    {k₂ : eS.output γ e₂ → CompM E γ α} :
    op e₁ blocks₁ >>= k₁ = op e₂ blocks₂ >>= k₂ ↔
      ∃ _h : e₁ = e₂, HEq blocks₁ blocks₂ ∧ HEq k₁ k₂ := by
  constructor
  · intro h
    have h := congrArg observe h
    simp only [observe_op_bind, Eff.Step.op] at h
    injection h with htag hfields
    injection htag with he
    subst he
    have hfields := eq_of_heq hfields
    refine ⟨rfl, heq_of_eq ?_, heq_of_eq ?_⟩
    · funext t i
      exact congrFun hfields (.inr ⟨t, i⟩)
    · funext o
      exact congrFun hfields (.inl o)
  · rintro ⟨rfl, hb, hk⟩
    cases hb
    cases hk
    rfl

section Tau

variable [Eff.Has.{u, 0} Eff.Tau E]

/-- The operation a silent step is made of. -/
abbrev tauOp (γ : Γ) : E γ := Eff.Has.mk (α := Eff.Tau) Eff.TauCarrier.mk

/-- `Tau` has no blocks. -/
def tauBlocks :
    (t : eS.blockTag γ (tauOp γ)) →
    eS.blockInputs γ (tauOp γ) t →
    CompM E (eS.blockCtx γ (tauOp γ) t) (eS.blockOutputs γ (tauOp γ) t) :=
  fun t => nomatch Eff.Step.Has.lowerBlockTag (F := Eff.Tau) (E := E) t

@[simp]
theorem observe_tick_bind {α : Type} (k : Unit → CompM E γ α) :
    observe (tick >>= k) = Eff.Step.tau (k ()) := by
  change IxPoly.map (fun _ => treeEquiv.symm) (γ, α)
    (ITree.observe (ITree.tau (E := E) (treeEquiv (k ())))) = _
  rw [ITree.observe_tau]
  simp only [IxPoly.map, Eff.Step.tau, Eff.Step.Has.op, Eff.Step.op]
  congr 1
  funext x
  rcases x with _ | ⟨t, _⟩
  · apply Equiv.symm_apply_apply
  · exact nomatch Eff.Step.Has.lowerBlockTag t

/-- A silent step is an operation of the `Tau` effect. Its blocks are
irrelevant, as `Tau` has none. -/
theorem tick_bind {α : Type} (k : Unit → CompM E γ α)
    (blocks :
      (t : eS.blockTag γ (tauOp γ)) →
      eS.blockInputs γ (tauOp γ) t →
      CompM E (eS.blockCtx γ (tauOp γ) t) (eS.blockOutputs γ (tauOp γ) t)) :
    tick >>= k = op (tauOp γ) blocks >>= fun _ => k () := by
  apply observe.injective
  rw [observe_op_bind, observe_tick_bind]
  simp only [Eff.Step.tau, Eff.Step.Has.op]
  congr 1
  funext t
  exact nomatch Eff.Step.Has.lowerBlockTag t

end Tau

section Fail

variable [Eff.Has.{u, 0} Eff.Fail E]

/-- The operation failure is made of. -/
abbrev failOp (γ : Γ) : E γ := Eff.Has.mk (α := Eff.Fail) Eff.FailCarrier.mk

/-- `Fail` has no blocks. -/
def failBlocks :
    (t : eS.blockTag γ (failOp γ)) →
    eS.blockInputs γ (failOp γ) t →
    CompM E (eS.blockCtx γ (failOp γ) t) (eS.blockOutputs γ (failOp γ) t) :=
  fun t => nomatch Eff.Step.Has.lowerBlockTag (F := Eff.Fail) (E := E) t

/-- `Fail` has no outputs. -/
def failCont {α : Type} : eS.output γ (failOp γ) → CompM E γ α :=
  fun o => nomatch Eff.Step.Has.lowerOutput (F := Eff.Fail) (E := E) o

@[simp]
theorem observe_fail {α : Type} :
    observe (fail : CompM E γ α) = Eff.Step.fail := by
  change IxPoly.map (fun _ => treeEquiv.symm) (γ, α)
    (ITree.observe (ITree.fail (E := E))) = _
  simp only [ITree.fail, ITree.observe_roll]
  simp only [IxPoly.map, Eff.Step.fail, Eff.Step.Has.op, Eff.Step.op]
  congr 1
  funext x
  rcases x with o | ⟨t, _⟩
  · exact nomatch Eff.Step.Has.lowerOutput o
  · exact nomatch Eff.Step.Has.lowerBlockTag t

/-- Failure is an operation of the `Fail` effect. Its blocks and
continuation are irrelevant, as `Fail` has neither blocks nor outputs. -/
theorem fail_eq {α : Type}
    (blocks :
      (t : eS.blockTag γ (failOp γ)) →
      eS.blockInputs γ (failOp γ) t →
      CompM E (eS.blockCtx γ (failOp γ) t) (eS.blockOutputs γ (failOp γ) t))
    (k : eS.output γ (failOp γ) → CompM E γ α) :
    (fail : CompM E γ α) = op (failOp γ) blocks >>= k := by
  apply observe.injective
  rw [observe_op_bind, observe_fail]
  simp only [Eff.Step.fail, Eff.Step.Has.op]
  congr 1
  · funext t
    exact nomatch Eff.Step.Has.lowerBlockTag t
  · funext o
    exact nomatch Eff.Step.Has.lowerOutput o

@[simp]
theorem fail_bind {α β : Type} (f : α → CompM E γ β) :
    (fail : CompM E γ α) >>= f = fail :=
  rfl

end Fail

end Freigen.CompM
