import Freigen.Free.Defs

/-!
Simulation up to erasure between `Free` programs, possibly over different
effects, contexts and result types.

`Free.Sim spec f x y`: `x` simulates `y` up to erasure. Every value `y` can
see (a block input, an operation output, its result) is erased by `spec` to a
value of `x`, and `x` answers each of `y`'s moves at that erasure: operations
are paired in lockstep by `spec`, and `x`'s result is `f` of `y`'s. It is
the least relation such that

- `pure (f b)` simulates `pure b`;
- `op (src o) blocks >>= k` simulates `op (tgt o) blocks' >>= k'` for a pair
  `o` of `spec`, when the matching block of `src o` on the erasure of every
  input `i'` simulates the block of `tgt o` on `i'`, and `k` at the erasure of
  every output `o'` simulates `k' o'`.

Erasure goes from `y` to `x`, and is injective (the spec's `_injective`
fields): it loses no information, so `x` carries everything `y` computes. It
need not be surjective, and `x` is unconstrained where it is not: at outputs
that erase no output of `y`'s operation (a certificate for a false
assertion), and in blocks of `x` that match none of `y`'s. So `Sim` is a
simulation, not an equation; under the identity spec, whose erasures are
identities, it is equality (`Sim.id_eq_iff`, and `Sim.id_map_iff` for a
result erasure `f`).
-/

namespace Freigen

variable {Γ : Type c} {E : Γ → Type u} [sE : Eff.Spec.{_, u, v} E]
  {Γ' : Type c'} {F : Γ' → Type u'} [sF : Eff.Spec.{_, u', v} F]

/-- Operations of `E` paired with operations of `F`, with erasures. Each pair
`o : Op γ γ'` has a source `src o` and a target `tgt o`; each block `t` of
`tgt o` is matched with block `tag o t` of `src o`. `inp o t` and `out o t`
erase the inputs and results of block `t` to those of its match, and `res o`
erases the outputs of `tgt o` to those of `src o`. All erasures are
injective. -/
structure Free.SimSpec (E : Γ → Type u) [sE : Eff.Spec.{_, u, v} E] (F : Γ' → Type u')
    [sF : Eff.Spec.{_, u', v} F] where
  Op : Γ → Γ' → Type w
  src : Op γ γ' → E γ
  tgt : Op γ γ' → F γ'
  tag : (o : Op γ γ') → sF.blockTag γ' (tgt o) → sE.blockTag γ (src o)
  inp : (o : Op γ γ') → (t : sF.blockTag γ' (tgt o)) →
    sF.blockInputs γ' (tgt o) t → sE.blockInputs γ (src o) (tag o t)
  out : (o : Op γ γ') → (t : sF.blockTag γ' (tgt o)) →
    sF.blockOutputs γ' (tgt o) t → sE.blockOutputs γ (src o) (tag o t)
  res : (o : Op γ γ') → sF.output γ' (tgt o) → sE.output γ (src o)
  inp_injective : ∀ {γ γ'} (o : Op γ γ') t, Function.Injective (inp o t)
  out_injective : ∀ {γ γ'} (o : Op γ γ') t, Function.Injective (out o t)
  res_injective : ∀ {γ γ'} (o : Op γ γ'), Function.Injective (res o)

/-- `x` simulates `y` up to erasure: operations paired by `spec`; for every
block input and output of `y`, `x`'s block and continuation at its erasure
simulate `y`'s; and `x`'s result is `f` of `y`'s. -/
inductive Free.Sim (spec : Free.SimSpec.{_, u, v, _, u', w} E F) :
    {γ : Γ} → {γ' : Γ'} → {α β : Type v} → (β → α) → Free E γ α → Free F γ' β → Prop
| pure {γ : Γ} {γ' : Γ'} {α β : Type v} {f : β → α} (b : β) :
    Free.Sim spec f (Pure.pure (f b) : Free E γ α) (Pure.pure b : Free F γ' β)
| op {γ : Γ} {γ' : Γ'} {α β : Type v} {f : β → α} (o : spec.Op γ γ')
    {blocks :
      (t : sE.blockTag γ (spec.src o)) →
      sE.blockInputs γ (spec.src o) t →
      Free E (sE.blockCtx γ (spec.src o) t) (sE.blockOutputs γ (spec.src o) t)}
    {blocks' :
      (t : sF.blockTag γ' (spec.tgt o)) →
      sF.blockInputs γ' (spec.tgt o) t →
      Free F (sF.blockCtx γ' (spec.tgt o) t) (sF.blockOutputs γ' (spec.tgt o) t)}
    {k : sE.output γ (spec.src o) → Free E γ α} {k' : sF.output γ' (spec.tgt o) → Free F γ' β} :
    (∀ t i', Free.Sim spec (spec.out o t)
      (blocks (spec.tag o t) (spec.inp o t i')) (blocks' t i')) →
    (∀ o', Free.Sim spec f (k (spec.res o o')) (k' o')) →
    Free.Sim spec f (Free.op (spec.src o) blocks >>= k) (Free.op (spec.tgt o) blocks' >>= k')

namespace Free.Sim

variable {spec : Free.SimSpec E F} {γ : Γ} {γ' : Γ'} {α β α' β' : Type v}

theorem pure_of_eq {f : β → α} {a : α} {b : β} (h : a = f b) :
    Free.Sim spec f (Pure.pure a : Free E γ α) (Pure.pure b : Free F γ' β) :=
  h ▸ .pure b

theorem bind {f : β → α} {g : β' → α'} {x : Free E γ α} {y : Free F γ' β}
    {h : α → Free E γ α'} {h' : β → Free F γ' β'} (hxy : Free.Sim spec f x y)
    (hh : ∀ b, Free.Sim spec g (h (f b)) (h' b)) :
    Free.Sim spec g (x >>= h) (y >>= h') := by
  induction hxy with
  | pure b => simpa using hh b
  | op o hb _ _ ih =>
    simp only [bind_assoc]
    exact .op o hb fun o' => ih o' hh

end Free.Sim

/-! ## The identity spec -/

/-- Each operation, paired with itself. -/
inductive Free.SimSpec.IdOp (E : Γ → Type u) : Γ → Γ → Type u
| mk {γ : Γ} (e : E γ) : IdOp E γ γ

/-- The source and target of an `IdOp`: the operation. -/
def Free.SimSpec.IdOp.op : {γ γ' : Γ} → IdOp E γ γ' → E γ
| _, _, .mk e => e

/-- The identity spec: each operation paired with itself, each block matched
to itself, and identities as erasures. -/
def Free.SimSpec.id : Free.SimSpec.{_, u, v, _, u, u} E E where
  Op := IdOp E
  src := IdOp.op
  tgt | .mk e => e
  tag | .mk _ => _root_.id
  inp | .mk _ => fun _ => _root_.id
  out | .mk _ => fun _ => _root_.id
  res | .mk _ => _root_.id
  inp_injective | .mk _ => fun _ => Function.injective_id
  out_injective | .mk _ => fun _ => Function.injective_id
  res_injective | .mk _ => Function.injective_id

namespace Free.Sim

variable {γ γ₁ γ₂ : Γ} {α β : Type v}

theorem id_refl (x : Free E γ α) : Free.Sim Free.SimSpec.id id x x := by
  induction x using Free.recOn with
  | ret a => exact .pure a
  | op e blocks k ihb ihk => exact .op (spec := .id) (.mk e) (fun t i => ihb t i) ihk

/-- A program simulates its image under `f`, up to `f`. -/
theorem id_map (f : β → α) (y : Free E γ β) : Free.Sim Free.SimSpec.id f (f <$> y) y := by
  induction y using Free.recOn with
  | ret b =>
    rw [map_pure]
    exact .pure b
  | op e blocks k _ ih =>
    rw [map_bind]
    exact .op (spec := .id) (.mk e) (fun t i => id_refl _) fun o => ih o f

private theorem id_map_aux {f : β → α} {x : Free E γ₁ α} {y : Free E γ₂ β}
    (h : Free.Sim Free.SimSpec.id f x y) : ∀ hγ : γ₁ = γ₂, hγ ▸ x = f <$> y := by
  induction h with
  | pure b =>
    intro hγ
    cases hγ
    simp
  | @op _ _ _ _ _ o b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    cases o with | mk e => ?_
    intro hγ
    cases hγ
    have hblocks : b₁ = b₂ := by
      funext t i
      exact (show b₁ t i = _root_.id <$> b₂ t i from ihb t i rfl).trans (LawfulFunctor.id_map _)
    subst hblocks
    change Free.op e b₁ >>= k₁ = _
    rw [map_bind]
    congr 1
    funext o
    exact ihk o rfl

/-- Under the identity spec, `x` simulates `y` up to `f` exactly when it is
`y`'s image under `f`. -/
theorem id_map_iff {f : β → α} {x : Free E γ α} {y : Free E γ β} :
    Free.Sim Free.SimSpec.id f x y ↔ x = f <$> y :=
  ⟨fun h => id_map_aux h rfl, fun h => h ▸ id_map f y⟩

/-- Under the identity spec, up to the identity, agreement is equality. -/
theorem id_eq_iff {x y : Free E γ α} : Free.Sim Free.SimSpec.id id x y ↔ x = y := by
  simpa using id_map_iff (f := id) (x := x) (y := y)

end Free.Sim

end Freigen
