import Freigen.CompM.Implements

/-!
Equivalence of computations up to silent steps (`Eutt`): the two perform the
same operations, with equivalent blocks and continuations, and return the
same results, but either may take finitely many silent steps the other does
not. Failure is an operation like any other, so equivalent computations fail
together. A program transformation that preserves `Eutt` preserves every
certificate (`Corr.of_eutt`).

`Eutt` is coinductive: computations are equivalent when they are related by
a simulation, a relation closed under one step of `EuttF`. A step either
matches an operation (a silent step being the operation of `Tau`) with
related blocks and continuations, matches equal results, or skips a silent
step on one side. Skipping is inductive, so a computation that only takes
silent steps is equivalent only to another such computation.
-/

namespace Freigen.CompM

variable {Γ : Type c} {E : Γ → Type u} [eS : Eff.Spec.{_, u, 0} E]
  [Eff.Has.{_, u, 0} Eff.Tau E]

/-- One step of `Eutt`, with what follows related by `R`. -/
inductive EuttF (R : ∀ {γ : Γ} {α : Type}, CompM E γ α → CompM E γ α → Prop) :
    {γ : Γ} → {α : Type} → CompM E γ α → CompM E γ α → Prop
| pure {γ : Γ} {α : Type} (a : α) : EuttF R (pure a : CompM E γ α) (pure a)
| op {γ : Γ} {α : Type} (e : E γ)
    {b₁ b₂ :
      (t : eS.blockTag γ e) →
      eS.blockInputs γ e t →
      CompM E (eS.blockCtx γ e t) (eS.blockOutputs γ e t)}
    {k₁ k₂ : eS.output γ e → CompM E γ α} :
    (∀ t i, R (b₁ t i) (b₂ t i)) → (∀ o, R (k₁ o) (k₂ o)) →
    EuttF R (op e b₁ >>= k₁) (op e b₂ >>= k₂)
| tauL {γ : Γ} {α : Type} {x y : CompM E γ α} :
    EuttF R x y → EuttF R (tick >>= fun _ => x) y
| tauR {γ : Γ} {α : Type} {x y : CompM E γ α} :
    EuttF R x y → EuttF R x (tick >>= fun _ => y)

/-- `x` and `y` are equivalent up to silent steps: they are related by a
simulation. -/
def Eutt {γ : Γ} {α : Type} (x y : CompM E γ α) : Prop :=
  ∃ R : ∀ {γ : Γ} {α : Type}, CompM E γ α → CompM E γ α → Prop,
    (∀ {γ : Γ} {α : Type} {x y : CompM E γ α}, R x y → EuttF R x y) ∧ R x y

theorem EuttF.mono {R S : ∀ {γ : Γ} {α : Type}, CompM E γ α → CompM E γ α → Prop}
    (hRS : ∀ {γ : Γ} {α : Type} {x y : CompM E γ α}, R x y → S x y)
    {γ : Γ} {α : Type} {x y : CompM E γ α} (h : EuttF R x y) : EuttF S x y := by
  induction h with
  | pure a => exact .pure a
  | op e hb hk => exact .op e (fun t i => hRS (hb t i)) fun o => hRS (hk o)
  | tauL _ ih => exact .tauL ih
  | tauR _ ih => exact .tauR ih

namespace Eutt

/-- Coinduction: a simulation relates only equivalent computations. -/
theorem coind (R : ∀ {γ : Γ} {α : Type}, CompM E γ α → CompM E γ α → Prop)
    (step : ∀ {γ : Γ} {α : Type} {x y : CompM E γ α}, R x y → EuttF R x y)
    {γ : Γ} {α : Type} {x y : CompM E γ α} (h : R x y) : Eutt x y :=
  ⟨R, step, h⟩

theorem unfold {γ : Γ} {α : Type} {x y : CompM E γ α} (h : Eutt x y) :
    EuttF Eutt x y := by
  obtain ⟨R, step, hR⟩ := h
  exact (step hR).mono fun h => ⟨R, step, h⟩

theorem refl {γ : Γ} {α : Type} (x : CompM E γ α) : Eutt x x := by
  refine coind (fun x y => x = y) ?_ rfl
  rintro γ α x _ rfl
  rcases eq_pure_or_op_bind x with ⟨a, rfl⟩ | ⟨e, b, k, rfl⟩
  · exact .pure a
  · exact .op e (fun _ _ => rfl) fun _ => rfl

end Eutt

/-! ## Shapes of computations

Silent steps are operations, so the shapes a step can have overlap; these
facts tell them apart. -/

theorem tick_bind_inj {γ : Γ} {α : Type} {x y : CompM E γ α}
    (h : (tick >>= fun _ => x) = tick >>= fun _ => y) : x = y := by
  rw [tick_bind _ tauBlocks, tick_bind _ tauBlocks] at h
  obtain ⟨_, _, hk⟩ := op_bind_inj.mp h
  exact congrFun (eq_of_heq hk) (Eff.Step.Has.liftOutput (F := Eff.Tau) PUnit.unit)

theorem pure_ne_tick_bind {γ : Γ} {α : Type} {a : α} {x : CompM E γ α} :
    pure a ≠ tick >>= fun _ => x := by
  rw [tick_bind _ tauBlocks]
  exact pure_ne_op_bind

/-- Lowering an output through an effect inclusion loses nothing. -/
theorem _root_.Freigen.Eff.Step.Has.lowerOutput_injective {F : Γ → Type u}
    [Eff.Spec.{_, u, 0} F] {E : Γ → Type u} [Eff.Spec.{_, u, 0} E] (h : Eff.Has F E)
    {γ : Γ} {e : F γ} :
    Function.Injective (Eff.Step.Has.lowerOutput (h := h) (e := e)) := by
  induction h with
  | here => intro a b hab; exact hab
  | inl _ ih => intro a b hab; exact ih hab
  | inr _ ih => intro a b hab; exact ih hab

/-- A silent step has a single output. -/
theorem tauOp_output_eq {γ : Γ} (o₁ o₂ : eS.output γ (tauOp γ)) : o₁ = o₂ :=
  Eff.Step.Has.lowerOutput_injective (F := Eff.Tau) inferInstance (by exact rfl)

/-- A silent step, as the `Tau` operation with any blocks and
continuation. -/
theorem op_tau_bind {γ : Γ} {α : Type}
    {b : (t : eS.blockTag γ (tauOp γ)) → eS.blockInputs γ (tauOp γ) t →
      CompM E (eS.blockCtx γ (tauOp γ) t) (eS.blockOutputs γ (tauOp γ) t)}
    {k : eS.output γ (tauOp γ) → CompM E γ α} (o : eS.output γ (tauOp γ)) :
    op (tauOp γ) b >>= k = tick >>= fun _ => k o := by
  rw [tick_bind _ b]
  congr 1
  funext o'
  rw [tauOp_output_eq o' o]

namespace Eutt

/-- A silent step on the left can be dropped. -/
theorem tick_left {γ : Γ} {α : Type} {x y : CompM E γ α}
    (h : Eutt (tick >>= fun _ => x) y) : Eutt x y := by
  refine coind (fun x y => Eutt x y ∨ Eutt (tick >>= fun _ => x) y) ?_ (.inr h)
  rintro γ α x y (h | h)
  · exact h.unfold.mono fun h => Or.inl h
  have key : ∀ {X Y : CompM E γ α}, EuttF Eutt X Y → ∀ x, X = (tick >>= fun _ => x) →
      EuttF (fun x y => Eutt x y ∨ Eutt (tick >>= fun _ => x) y) x Y := by
    intro X Y h
    induction h with
    | pure a =>
      intro x hx
      exact absurd hx pure_ne_tick_bind
    | @op e b₁ b₂ k₁ k₂ _ hk =>
      intro x hx
      rw [tick_bind _ tauBlocks] at hx
      obtain ⟨rfl, _, hk'⟩ := op_bind_inj.mp hx
      have hx : k₁ = fun _ => x := eq_of_heq hk'
      subst hx
      rw [op_tau_bind (Eff.Step.Has.liftOutput (F := Eff.Tau) PUnit.unit)]
      exact .tauR ((hk _).unfold.mono fun h => Or.inl h)
    | tauL h _ =>
      intro x hx
      cases tick_bind_inj hx
      exact h.mono fun h => Or.inl h
    | tauR _ ih =>
      intro x hx
      exact .tauR (ih x hx)
  exact key h.unfold x rfl

end Eutt

/-! ## Certificates -/

open Eff (Fail Tau)

variable {Γ' : Type c'} {F : Γ' → Type u'} [sF : Eff.Spec.{_, u', 0} F]

/-- Certificates are invariant under equivalence: a computation equivalent to
a correct one is correct. -/
theorem Corr.of_eutt {E : Γ → Type u} [Eff.Spec.{_, u, 0} E]
    {spec : Free.SimSpec E F} {γ : Γ} {γ' : Γ'} {α β : Type} {f : β → α}
    {x y : CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α} {s : Free F γ' β}
    (hx : Corr spec f x s) (h : Eutt x y) : Corr spec f y s := by
  induction hx with
  | @pure γ γ' α β f b =>
    have key : ∀ {X Y : CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α}, EuttF Eutt X Y →
        X = Pure.pure (f b) → Corr spec f Y (Pure.pure b : Free F γ' β) := by
      intro X Y h
      induction h with
      | pure a =>
        intro hx
        cases pure_inj.mp hx
        exact .pure b
      | op e _ _ =>
        intro hx
        exact absurd hx.symm pure_ne_op_bind
      | tauL _ _ =>
        intro hx
        exact absurd hx.symm pure_ne_tick_bind
      | tauR _ ih => exact fun hx => .tick (ih hx)
    exact key h.unfold rfl
  | @tick γ γ' α β f k s _ ih =>
    have hk : (CompM.tick (E := Fail ⊕ₑ Tau ⊕ₑ E) (γ := γ) >>= k) =
        CompM.tick >>= fun _ => k () := rfl
    exact ih (Eutt.tick_left (hk ▸ h))
  | @op γ γ' α β f o blocks blocks' k k' _ _ ihb ihk =>
    have key : ∀ {X Y : CompM (Fail ⊕ₑ Tau ⊕ₑ E) γ α}, EuttF Eutt X Y →
        X = CompM.op (.inr (.inr (spec.src o))) blocks >>= k →
        Corr spec f Y (Free.op (spec.tgt o) blocks' >>= k') := by
      intro X Y h
      induction h with
      | pure a =>
        intro hx
        exact absurd hx pure_ne_op_bind
      | op e hb hk =>
        intro hx
        obtain ⟨rfl, hb', hk'⟩ := op_bind_inj.mp hx
        cases hb'
        cases hk'
        exact .op o (fun t i => ihb t i (hb _ _)) fun a => ihk a (hk _)
      | tauL _ _ =>
        intro hx
        rw [tick_bind _ tauBlocks] at hx
        obtain ⟨he, _, _⟩ := op_bind_inj.mp hx
        cases he
      | tauR _ ih => exact fun hx => .tick (ih hx)
    exact key h.unfold rfl

end Freigen.CompM
