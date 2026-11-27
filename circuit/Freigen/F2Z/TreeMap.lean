import Lean
import Mathlib.Algebra.Ring.Defs

/-!
Missing extensional tree-map lemmas.
-/

namespace Std.Internal.List.Const

universe u v

variable {α : Type u} {β : Type v} [BEq α] [LawfulBEq α]

private def mergeStep (f : β → β → β) (l : List ((_ : α) × β))
    (p : ((_ : α) × β)) : List ((_ : α) × β) :=
  alterKey p.1 (fun
    | none => some p.2
    | some old => some (f old p.2)) l

private theorem getValue?_foldl_mergeStep (f : β → β → β) (k : α)
    (l₁ l₂ : List ((_ : α) × β))
    (h₁ : DistinctKeys l₁) (h₂ : DistinctKeys l₂) :
    getValue? k (l₂.foldl (mergeStep f) l₁) =
      Option.merge f (getValue? k l₁) (getValue? k l₂) := by
  induction l₂ generalizing l₁ with
  | nil =>
    simp only [List.foldl_nil, getValue?_nil]
    cases getValue? k l₁ <;> rfl
  | cons p l ih =>
    rcases p with ⟨pk, pv⟩
    have hl : DistinctKeys l := h₂.tail
    have hp : containsKey pk l = false := h₂.containsKey_eq_false
    simp only [List.foldl_cons]
    have hm : DistinctKeys (mergeStep f l₁ ⟨pk, pv⟩) := by
      exact h₁.constAlterKey
    rw [ih _ hm hl]
    simp only [mergeStep]
    rw [getValue?_alterKey pk k _ _ h₁]
    simp only [getValue?_cons]
    split <;> rename_i hpk
    · have hEq : pk = k := eq_of_beq hpk
      subst pk
      have hk : getValue? k l = none := getValue?_eq_none.mpr hp
      cases getValue? k l₁ <;> simp [hk, Option.merge]
    · simp [hpk, Option.merge]

universe w

private def foldMapList {γ : Type w} [AddCommMonoid γ]
    (φ : α → β → γ) (l : List ((_ : α) × β)) : γ :=
  l.foldl (fun acc p => acc + φ p.1 p.2) 0

private theorem add_right_comm' {γ : Type w} [AddCommMonoid γ]
    (a b c : γ) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b c, ← add_assoc]

omit [BEq α] [LawfulBEq α] in
private theorem foldl_eq_add_foldMapList {γ : Type w} [AddCommMonoid γ]
    (φ : α → β → γ) (l : List ((_ : α) × β)) (init : γ) :
    l.foldl (fun acc p => acc + φ p.1 p.2) init =
      init + foldMapList φ l := by
  induction l generalizing init with
  | nil => simp [foldMapList]
  | cons p l ih =>
    rw [List.foldl_cons, ih]
    change (init + φ p.1 p.2) + foldMapList φ l =
      init + l.foldl (fun acc p => acc + φ p.1 p.2) (0 + φ p.1 p.2)
    rw [ih]
    simp [add_assoc]

omit [BEq α] [LawfulBEq α] in
private theorem foldMapList_cons {γ : Type w} [AddCommMonoid γ]
    (φ : α → β → γ) (p : ((_ : α) × β))
    (l : List ((_ : α) × β)) :
    foldMapList φ (p :: l) = φ p.1 p.2 + foldMapList φ l := by
  change l.foldl (fun acc p => acc + φ p.1 p.2) (0 + φ p.1 p.2) = _
  rw [foldl_eq_add_foldMapList]
  simp

omit [BEq α] [LawfulBEq α] in
private theorem foldMapList_perm {γ : Type w} [AddCommMonoid γ]
    (φ : α → β → γ) {l₁ l₂ : List ((_ : α) × β)} (h : l₁.Perm l₂) :
    foldMapList φ l₁ = foldMapList φ l₂ := by
  apply h.foldl_eq'
  intro x _ y _ z
  exact add_right_comm' z (φ x.1 x.2) (φ y.1 y.2)

private theorem foldMapList_mergeStep {γ : Type w} [AddCommMonoid γ]
    (φ : α → β → γ) (f : β → β → β)
    (hf : ∀ k a b, φ k (f a b) = φ k a + φ k b)
    (p : ((_ : α) × β)) (l : List ((_ : α) × β))
    (hl : DistinctKeys l) :
    foldMapList φ (mergeStep f l p) = foldMapList φ l + φ p.1 p.2 := by
  induction l with
  | nil =>
    rcases p with ⟨pk, pv⟩
    simp [mergeStep, foldMapList, alterKey, Std.Internal.List.insertEntry]
  | cons q l ih =>
    rcases p with ⟨pk, pv⟩
    rcases q with ⟨qk, qv⟩
    have hp := alterKey_cons_perm
      (k := pk)
      (f := fun
        | none => some pv
        | some old => some (f old pv))
      (k' := qk) (v' := qv) (l := l)
    unfold mergeStep
    rw [foldMapList_perm φ hp]
    by_cases hqk : qk == pk
    · simp only [hqk, ↓reduceIte]
      have heq : qk = pk := eq_of_beq hqk
      subst qk
      rw [foldMapList_cons, foldMapList_cons]
      change φ pk (f qv pv) + foldMapList φ l =
        (φ pk qv + foldMapList φ l) + φ pk pv
      rw [hf]
      exact add_right_comm' (φ pk qv) (φ pk pv) (foldMapList φ l)
    · simp only [hqk, Bool.false_eq_true, ↓reduceIte]
      rw [foldMapList_cons]
      change φ qk qv + foldMapList φ (mergeStep f l ⟨pk, pv⟩) =
        foldMapList φ (⟨qk, qv⟩ :: l) + φ pk pv
      rw [ih hl.tail, foldMapList_cons]
      exact (add_assoc _ _ _).symm

private theorem foldMapList_foldl_mergeStep {γ : Type w} [AddCommMonoid γ]
    (φ : α → β → γ) (f : β → β → β)
    (hf : ∀ k a b, φ k (f a b) = φ k a + φ k b)
    (l₁ l₂ : List ((_ : α) × β)) (h₁ : DistinctKeys l₁)
    (h₂ : DistinctKeys l₂) :
    foldMapList φ (l₂.foldl (mergeStep f) l₁) =
      foldMapList φ l₁ + foldMapList φ l₂ := by
  induction l₂ generalizing l₁ with
  | nil => simp [foldMapList]
  | cons p l ih =>
    rw [List.foldl_cons]
    have hm : DistinctKeys (mergeStep f l₁ p) := h₁.constAlterKey
    rw [ih _ hm h₂.tail, foldMapList_mergeStep φ f hf p l₁ h₁,
      foldMapList_cons]
    simp only [add_assoc]

end Std.Internal.List.Const

namespace Std.DTreeMap.Const

universe u v w

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering}

private theorem mergeWith_model_perm [Ord α] [TransOrd α] [BEq α]
    [LawfulBEqOrd α]
    (f : β → β → β)
    (t₁ t₂ : DTreeMap.Internal.Impl α (fun _ => β)) (h₁ : t₁.WF) :
    (DTreeMap.Internal.Impl.Const.mergeWith (fun _ => f) t₁ t₂ h₁.balanced).impl.toListModel.Perm
      (t₂.toListModel.foldl (Std.Internal.List.Const.mergeStep f) t₁.toListModel) := by
  simp only [DTreeMap.Internal.Impl.Const.mergeWith,
    DTreeMap.Internal.Impl.foldl_eq_foldl]
  refine (List.foldl_rel
    (r := fun (a : DTreeMap.Internal.Impl.BalancedTree α (fun _ => β))
      (b : List ((_ : α) × β)) => a.impl.WF ∧ a.impl.toListModel.Perm b)
    ⟨h₁, .refl _⟩ ?_).2
  intro p _ a b hab
  refine ⟨hab.1.constAlter, ?_⟩
  exact (DTreeMap.Internal.Impl.Const.toListModel_alter
    hab.1.balanced hab.1.ordered).trans
      (Std.Internal.List.Const.alterKey_of_perm
        hab.1.ordered.distinctKeys hab.2)

private theorem get?_mergeWith [TransCmp cmp] [LawfulEqCmp cmp]
    (f : β → β → β) (t₁ t₂ : DTreeMap α (fun _ => β) cmp) (k : α) :
    get? (mergeWith (fun _ => f) t₁ t₂) k =
      Option.merge f (get? t₁ k) (get? t₂ k) := by
  letI : Ord α := ⟨cmp⟩
  letI : BEq α := beqOfOrd
  letI : LawfulBEq α := inferInstance
  cases t₁ with
  | mk i₁ h₁ =>
    cases t₂ with
    | mk i₂ h₂ =>
      let out := DTreeMap.Internal.Impl.Const.mergeWith
        (fun _ => f) i₁ i₂ h₁.balanced
      have hout : out.impl.WF := h₁.constMergeWith
      change DTreeMap.Internal.Impl.Const.get? out.impl k =
        Option.merge f (DTreeMap.Internal.Impl.Const.get? i₁ k)
          (DTreeMap.Internal.Impl.Const.get? i₂ k)
      rw [DTreeMap.Internal.Impl.Const.get?_eq_getValue? hout.ordered,
        DTreeMap.Internal.Impl.Const.get?_eq_getValue? h₁.ordered,
        DTreeMap.Internal.Impl.Const.get?_eq_getValue? h₂.ordered]
      rw [Std.Internal.List.getValue?_of_perm hout.ordered.distinctKeys
        (mergeWith_model_perm f i₁ i₂ h₁)]
      exact Std.Internal.List.Const.getValue?_foldl_mergeStep f k _ _
        h₁.ordered.distinctKeys h₂.ordered.distinctKeys

private theorem foldMap_mergeWith [TransCmp cmp] [LawfulEqCmp cmp]
    {γ : Type w} [AddCommMonoid γ]
    (φ : α → β → γ) (f : β → β → β)
    (hf : ∀ k a b, φ k (f a b) = φ k a + φ k b)
    (t₁ t₂ : DTreeMap α (fun _ => β) cmp) :
    (mergeWith (fun _ => f) t₁ t₂).foldl
        (fun acc k v => acc + φ k v) 0 =
      t₁.foldl (fun acc k v => acc + φ k v) 0 +
        t₂.foldl (fun acc k v => acc + φ k v) 0 := by
  letI : Ord α := ⟨cmp⟩
  letI : BEq α := beqOfOrd
  letI : LawfulBEq α := inferInstance
  cases t₁ with
  | mk i₁ h₁ =>
    cases t₂ with
    | mk i₂ h₂ =>
      change (DTreeMap.Internal.Impl.Const.mergeWith
          (fun _ => f) i₁ i₂ h₁.balanced).impl.foldl
            (fun acc k v => acc + φ k v) 0 =
        i₁.foldl (fun acc k v => acc + φ k v) 0 +
          i₂.foldl (fun acc k v => acc + φ k v) 0
      simp only [DTreeMap.Internal.Impl.foldl_eq_foldl]
      change Std.Internal.List.Const.foldMapList φ
          (DTreeMap.Internal.Impl.Const.mergeWith
            (fun _ => f) i₁ i₂ h₁.balanced).impl.toListModel =
        Std.Internal.List.Const.foldMapList φ i₁.toListModel +
          Std.Internal.List.Const.foldMapList φ i₂.toListModel
      rw [Std.Internal.List.Const.foldMapList_perm φ
        (mergeWith_model_perm f i₁ i₂ h₁)]
      exact Std.Internal.List.Const.foldMapList_foldl_mergeStep φ f hf _ _
        h₁.ordered.distinctKeys h₂.ordered.distinctKeys

end Std.DTreeMap.Const

namespace Std.ExtTreeMap

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
variable {cmp : α → α → Ordering}

@[simp] theorem getElem?_mergeWith [TransCmp cmp] [LawfulEqCmp cmp]
    (f : β → β → β) (t₁ t₂ : ExtTreeMap α β cmp) (k : α) :
    (mergeWith (fun _ => f) t₁ t₂)[k]? =
      Option.merge f t₁[k]? t₂[k]? := by
  cases t₁ with
  | mk t₁ =>
    cases t₂ with
    | mk t₂ =>
      change ExtDTreeMap.Const.get?
        (ExtDTreeMap.Const.mergeWith (fun _ => f) t₁ t₂) k =
          Option.merge f (ExtDTreeMap.Const.get? t₁ k)
            (ExtDTreeMap.Const.get? t₂ k)
      exact ExtDTreeMap.inductionOn₂ t₁ t₂ fun m₁ m₂ =>
        DTreeMap.Const.get?_mergeWith f m₁ m₂ k

/-- Folds the entries of a tree map through a function into a commutative additive monoid. -/
def foldMap [TransCmp cmp] [AddCommMonoid γ]
    (t : ExtTreeMap α β cmp) (φ : α → β → γ) : γ :=
  t.foldl (fun acc k v => acc + φ k v) 0

private def foldMapList [AddCommMonoid γ]
    (φ : α → β → γ) (l : List (α × β)) : γ :=
  l.foldl (fun acc p => acc + φ p.1 p.2) 0

private theorem foldl_eq_add_foldMapList [AddCommMonoid γ]
    (φ : α → β → γ) (l : List (α × β)) (init : γ) :
    l.foldl (fun acc p => acc + φ p.1 p.2) init =
      init + foldMapList φ l := by
  induction l generalizing init with
  | nil => simp [foldMapList]
  | cons p l ih =>
    rw [List.foldl_cons, ih]
    change (init + φ p.1 p.2) + foldMapList φ l =
      init + l.foldl (fun acc p => acc + φ p.1 p.2) (0 + φ p.1 p.2)
    rw [ih]
    simp [add_assoc]

private theorem foldMapList_cons [AddCommMonoid γ]
    (φ : α → β → γ) (p : α × β) (l : List (α × β)) :
    foldMapList φ (p :: l) = φ p.1 p.2 + foldMapList φ l := by
  change l.foldl (fun acc p => acc + φ p.1 p.2) (0 + φ p.1 p.2) = _
  rw [foldl_eq_add_foldMapList]
  simp

private theorem foldMap_eq_list [TransCmp cmp] [AddCommMonoid γ]
    (t : ExtTreeMap α β cmp) (φ : α → β → γ) :
    foldMap t φ = foldMapList φ t.toList := by
  exact foldl_eq_foldl_toList

theorem foldMap_congr [TransCmp cmp] [AddCommMonoid γ]
    (t : ExtTreeMap α β cmp) (φ ψ : α → β → γ)
    (h : ∀ k v, (k, v) ∈ t.toList → φ k v = ψ k v) :
    foldMap t φ = foldMap t ψ := by
  rw [foldMap_eq_list, foldMap_eq_list]
  generalize t.toList = l at h ⊢
  induction l with
  | nil => rfl
  | cons p l ih =>
      rw [foldMapList_cons, foldMapList_cons]
      congr 1
      · exact h p.1 p.2 (by simp)
      · apply ih
        intro k v hmem
        exact h k v (by simp [hmem])

@[simp]
theorem foldMap_empty [TransCmp cmp] [AddCommMonoid γ]
    (φ : α → β → γ) :
    foldMap (empty : ExtTreeMap α β cmp) φ = 0 := by
  rw [foldMap_eq_list]
  rfl

@[simp]
theorem foldMap_singleton [TransCmp cmp] [LawfulEqCmp cmp]
    [AddCommMonoid γ] (k : α) (v : β) (φ : α → β → γ) :
    foldMap ({(k, v)} : ExtTreeMap α β cmp) φ = φ k v := by
  let t : ExtTreeMap α β cmp := {(k, v)}
  have hlen : t.toList.length = 1 := by
    simp [t, Std.ExtTreeMap.singleton_eq_insert,
      Std.ExtTreeMap.length_toList, Std.ExtTreeMap.size_insert]
  have hmem : (k, v) ∈ t.toList := by
    simp [t]
  have hlist : t.toList = [(k, v)] := by
    cases ht : t.toList with
    | nil => simp_all
    | cons p l =>
      cases l with
      | nil => simp_all
      | cons q l => simp_all
  change foldMap t φ = φ k v
  rw [foldMap_eq_list, hlist, foldMapList_cons]
  simp [foldMapList]

/-- Combining map values is sent to addition when each combined entry is. -/
@[simp]
theorem foldMap_mergeWith [TransCmp cmp] [LawfulEqCmp cmp]
    [AddCommMonoid γ]
    (t₁ t₂ : ExtTreeMap α β cmp) (φ : α → β → γ) (f : β → β → β)
    (hf : ∀ k a b, φ k (f a b) = φ k a + φ k b) :
    foldMap (mergeWith (fun _ => f) t₁ t₂) φ =
      foldMap t₁ φ + foldMap t₂ φ := by
  cases t₁ with
  | mk t₁ =>
    cases t₂ with
    | mk t₂ =>
      change ExtDTreeMap.foldl (fun acc k v => acc + φ k v) 0
          (ExtDTreeMap.Const.mergeWith (fun _ => f) t₁ t₂) =
        ExtDTreeMap.foldl (fun acc k v => acc + φ k v) 0 t₁ +
          ExtDTreeMap.foldl (fun acc k v => acc + φ k v) 0 t₂
      exact ExtDTreeMap.inductionOn₂ t₁ t₂ fun m₁ m₂ =>
        DTreeMap.Const.foldMap_mergeWith φ f hf m₁ m₂

/-- Filtering entries whose contribution is zero does not affect `foldMap`. -/
@[simp]
theorem foldMap_filter [TransCmp cmp] [AddCommMonoid γ]
    (t : ExtTreeMap α β cmp) (φ : α → β → γ) (p : α → β → Bool)
    (h : ∀ k v, p k v = false → φ k v = 0) :
    foldMap (t.filter p) φ = foldMap t φ := by
  rw [foldMap_eq_list, foldMap_eq_list, toList_filter]
  induction t.toList with
  | nil => rfl
  | cons q l ih =>
    rcases q with ⟨k, v⟩
    by_cases hp : p k v
    · simp only [List.filter_cons, hp, ↓reduceIte, foldMapList_cons, ih]
    · have hp' : p k v = false := by
        cases hpv : p k v <;> simp_all
      simp only [List.filter_cons, hp', Bool.false_eq_true, ↓reduceIte,
        foldMapList_cons, ih, h k v hp', zero_add]

/-- Mapping entries before `foldMap` is the same as composing the entry function. -/
@[simp] theorem foldMap_map [TransCmp cmp] [AddCommMonoid γ]
    (t : ExtTreeMap α β cmp) (φ : α → δ → γ) (f : α → β → δ) :
    foldMap (t.map f) φ = foldMap t (fun k v => φ k (f k v)) := by
  rw [foldMap_eq_list, foldMap_eq_list, toList_map]
  unfold foldMapList
  rw [List.foldl_map]

/-- Multiplication by a constant can be pulled out of `foldMap`. -/
@[simp] theorem foldMap_const_mul [TransCmp cmp] [Semiring γ]
    (t : ExtTreeMap α β cmp) (φ : α → β → γ) (a : γ) :
    foldMap t (fun k v => a * φ k v) = a * foldMap t φ := by
  rw [foldMap_eq_list, foldMap_eq_list]
  induction t.toList with
  | nil => simp [foldMapList]
  | cons p l ih =>
    rw [foldMapList_cons, foldMapList_cons, ih, mul_add]

end Std.ExtTreeMap
