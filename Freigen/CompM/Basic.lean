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

instance {γ : Γ} : Monad (CompM E γ) where
  pure value := {
    run := fun f => f value
    exact := by simp
    result := pure value
    result_eq := rfl
  }
  bind x f := {
    run := fun g => x.run fun value => (f value).run g
    exact := by
      intro β g
      conv => lhs; rw [← x.exact]
      rw [bind_assoc]
      simp only [ExactCodensity.exact]
    result := ITree.bindFast x.result fun value => (f value).result
    result_eq := by
      rw [ITree.bindFast_eq_bind, x.result_eq]
      conv_lhs =>
        rhs
        intro value
        rw [(f value).result_eq]
      exact x.exact _
  }

instance {γ : Γ} : LawfulMonad (CompM E γ) := LawfulMonad.mk' _
  (by intros; apply ExactCodensity.ext; intros; rfl)
  (by intros; apply ExactCodensity.ext; intros; rfl)
  (by intros; apply ExactCodensity.ext; intros; rfl)

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
    x >>= f = {
      run := fun g => x.run fun a => (f a).run g
      exact := by
        intros
        conv => lhs; rw [←x.exact]
        rw [bind_assoc]
        simp only [ExactCodensity.exact]
      result := ITree.bindFast x.result fun a => (f a).result
      result_eq := by
        rw [ITree.bindFast_eq_bind, x.result_eq]
        conv_lhs =>
          rhs
          intro a
          rw [(f a).result_eq]
        exact x.exact _
    } := by
  rfl

def tick {γ : Γ} [Eff.Has.{u, 0} Eff.Tau E] :
    CompM E γ Unit := {
  run := fun f => ITree.tau (f ())
  exact := by simp
  result := ITree.tau (pure ())
  result_eq := rfl
}

def fail {γ : Γ} [Eff.Has Eff.Fail E] :
    CompM E γ α := {
  run := fun _ => ITree.fail
  exact := by simp
  result := ITree.fail
  result_eq := rfl
}

def op {γ : Γ} (e : E γ)
    (blocks :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      CompM E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)) :
    CompM E γ (eS.output γ e) := {
  run := fun f => ITree.op e (fun t i => (blocks t i).result) f
  exact := by simp
  result := ITree.op e (fun t i => (blocks t i).result) pure
  result_eq := rfl
}

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

private def liftLApprox
    {L R : Γ → Type u} [Eff.Spec.{u, v} L] [Eff.Spec.{u, v} R] :
    {n : Nat} → {i : Γ × Type v} →
      IxPoly.M.Approx (Eff.Step Γ L) n i →
      IxPoly.M.Approx (Eff.Step Γ (L ⊕ₑ R)) n i
  | 0, _, .zero _ => .zero _
  | n + 1, _, ._succ _ _ p children =>
      .succ <| Eff.Step.casesOn ⟨p, children⟩
        (motive := fun i _ => Eff.Step Γ (L ⊕ₑ R)
          (IxPoly.M.Approx (Eff.Step Γ (L ⊕ₑ R)) n) i)
        (fun value => Eff.Step.ret value)
        (fun e blocks k => Eff.Step.op (Sum.inl e)
          (fun t input => liftLApprox (blocks t input))
          (fun output => liftLApprox (k output)))

private theorem liftLApprox_agree
    {L R : Γ → Type u} [Eff.Spec.{u, v} L] [Eff.Spec.{u, v} R]
    {n : Nat} {i : Γ × Type v}
    {x : IxPoly.M.Approx (Eff.Step Γ L) n i}
    {y : IxPoly.M.Approx (Eff.Step Γ L) (n + 1) i}
    (h : IxPoly.M.Agree (Eff.Step Γ L) x y) :
    IxPoly.M.Agree (Eff.Step Γ (L ⊕ₑ R))
      (liftLApprox x) (liftLApprox y) := by
  induction h with
  | zero => exact .zero _ _
  | succ p children children' hchildren ih =>
    cases p with
    | ret value =>
      simp only [liftLApprox, Eff.Step.casesOn, Eff.Step.ret]
      apply IxPoly.M.Agree.succ
      intro field
      exact nomatch field
    | op e =>
      simp only [liftLApprox, Eff.Step.casesOn, Eff.Step.op]
      apply IxPoly.M.Agree.succ
      intro field
      cases field with
      | inl output => exact ih (Sum.inl output)
      | inr block =>
        rcases block with ⟨tag, input⟩
        exact ih (Sum.inr ⟨tag, input⟩)

private def liftLTree
    {L R : Γ → Type u} [Eff.Spec.{u, v} L] [Eff.Spec.{u, v} R]
    {i : Γ × Type v} (x : ITree L i.1 i.2) :
    ITree (L ⊕ₑ R) i.1 i.2 where
  approx n := liftLApprox (x.approx n)
  agree := liftLApprox_agree x.agree

def liftL
    {L R : Γ → Type u} [lS : Eff.Spec.{u, v} L] [rS : Eff.Spec.{u, v} R]
    {γ : Γ} {α : Type v} (x : CompM L γ α) :
    CompM (L ⊕ₑ R) γ α :=
  treeEquiv.symm (liftLTree (L := L) (R := R) (i := (γ, α)) x.result)

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

private def liftRApprox
    {L R : Γ → Type u} [Eff.Spec.{u, v} L] [Eff.Spec.{u, v} R] :
    {n : Nat} → {i : Γ × Type v} →
      IxPoly.M.Approx (Eff.Step Γ R) n i →
      IxPoly.M.Approx (Eff.Step Γ (L ⊕ₑ R)) n i
  | 0, _, .zero _ => .zero _
  | n + 1, _, ._succ _ _ p children =>
      .succ <| Eff.Step.casesOn ⟨p, children⟩
        (motive := fun i _ => Eff.Step Γ (L ⊕ₑ R)
          (IxPoly.M.Approx (Eff.Step Γ (L ⊕ₑ R)) n) i)
        (fun value => Eff.Step.ret value)
        (fun e blocks k => Eff.Step.op (Sum.inr e)
          (fun t input => liftRApprox (blocks t input))
          (fun output => liftRApprox (k output)))

private theorem liftRApprox_agree
    {L R : Γ → Type u} [Eff.Spec.{u, v} L] [Eff.Spec.{u, v} R]
    {n : Nat} {i : Γ × Type v}
    {x : IxPoly.M.Approx (Eff.Step Γ R) n i}
    {y : IxPoly.M.Approx (Eff.Step Γ R) (n + 1) i}
    (h : IxPoly.M.Agree (Eff.Step Γ R) x y) :
    IxPoly.M.Agree (Eff.Step Γ (L ⊕ₑ R))
      (liftRApprox x) (liftRApprox y) := by
  induction h with
  | zero => exact .zero _ _
  | succ p children children' hchildren ih =>
    cases p with
    | ret value =>
      simp only [liftRApprox, Eff.Step.casesOn, Eff.Step.ret]
      apply IxPoly.M.Agree.succ
      intro field
      exact nomatch field
    | op e =>
      simp only [liftRApprox, Eff.Step.casesOn, Eff.Step.op]
      apply IxPoly.M.Agree.succ
      intro field
      cases field with
      | inl output => exact ih (Sum.inl output)
      | inr block =>
        rcases block with ⟨tag, input⟩
        exact ih (Sum.inr ⟨tag, input⟩)

private def liftRTree
    {L R : Γ → Type u} [Eff.Spec.{u, v} L] [Eff.Spec.{u, v} R]
    {i : Γ × Type v} (x : ITree R i.1 i.2) :
    ITree (L ⊕ₑ R) i.1 i.2 where
  approx n := liftRApprox (x.approx n)
  agree := liftRApprox_agree x.agree

def liftR
    {L R : Γ → Type u} [lS : Eff.Spec.{u, v} L] [rS : Eff.Spec.{u, v} R]
    {γ : Γ} {α : Type v} (x : CompM R γ α) :
    CompM (L ⊕ₑ R) γ α :=
  treeEquiv.symm (liftRTree (L := L) (R := R) (i := (γ, α)) x.result)

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
  run := fun f => ITree.loop (fun a => (body a).result) init f
  exact := by
    intros
    apply ITree.loop_bind
  result := ITree.loop (fun a => (body a).result) init pure
  result_eq := rfl
}

theorem loop_def [Eff.Has Eff.Tau E]
  (body : α → CompM E γ (α ⊕ β))
  (s : α) :
  CompM.loop body s =
    body s >>= fun
      | .inr v  => pure v
      | .inl v => CompM.tick (E := E) (γ := γ) *> CompM.loop body v := by
  apply ExactCodensity.equiv.injective
  change (CompM.loop body s).result =
    ((body s >>= fun
      | .inr v => pure v
      | .inl v =>
        CompM.tick (E := E) (γ := γ) *> CompM.loop body v) :
        CompM E γ β).result
  simp only [loop, bind_def]
  rw [ITree.loop_def]
  rw [(body s).result_eq]
  rw [ITree.bindFast_eq_bind]
  symm
  refine ((body s).exact _).trans ?_
  rw [(body s).exact]
  congr 1
  funext x
  cases x with
  | inr value => rfl
  | inl value =>
    change ITree.bindFast (ITree.tau (pure ()))
      (fun _ => ITree.loop (fun a => (body a).result) value pure) =
      ITree.tau (ITree.loop (fun a => (body a).result) value pure)
    rw [ITree.bindFast_eq_bind, ITree.tau_bind]
    congr 1
    apply ITree.ret_bind

abbrev forInStepToSum : ForInStep α → α ⊕ α
  | .yield x => .inl x
  | .done x => .inr x

instance {γ : Γ} [Eff.Has Eff.Tau E] :
    ForIn (CompM E γ) Lean.Loop Unit where
  forIn _ init body := loop (fun a => forInStepToSum <$> (body () a)) init

end Freigen.CompM
