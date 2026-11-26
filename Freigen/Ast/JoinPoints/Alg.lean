import Freigen.Ast.JoinPoints.Rel
import Freigen.Ast.JoinPoints.Bind

/-!
The translation is related to its input (`Program.joinPoints_jp`), for
well-formed inputs. The pass reads its input at one instantiation, where join
points are labels, and decides at others, where binders are labels too
(`ok`); well-formedness relates these to each other and to the instantiation
the evaluator runs.

`ok` cannot tell apart variables that agree on whether they are join point
labels, and which (`Compat`), so its result is the same on any two
corresponding instantiations (`ok_congr`). The translation is then related to
the evaluator's instantiation by induction (`tr_jp`), with `Good` relating the
contexts: variables of the translation's input are the evaluator's, or labels
of join points in scope, each of one variable.
-/

namespace Freigen.Ast.JoinPoints

variable {L : Language} [L.Blocks]

/-! ## Deciding is invariant -/

section Congr

variable {V V' : L.Tp → Type}

/-- Variables `ok` cannot tell apart: labels below `n`, and the same join
point labels. -/
def Compat (n : Nat) (J : List Nat) {t : L.Tp} (x : PVar V t) (y : PVar V' t) : Prop :=
  (∀ l, x = .inr l → l < n) ∧ (∀ l, y = .inr l → l < n) ∧ (∀ l ∈ J, x = .inr l ↔ y = .inr l)

def CompatCtx (n : Nat) (J : List Nat) (Δ : WfCtx L (PVar V) (PVar V')) : Prop :=
  ∀ {t : L.Tp} {x : PVar V t} {y : PVar V' t}, ⟨t, x, y⟩ ∈ Δ → Compat n J x y

omit [L.Blocks] in
theorem Compat.free_eq {n : Nat} {J : List Nat} {t : L.Tp} {x : PVar V t} {y : PVar V' t}
    (h : Compat n J x y) : free J x = free J y := by
  rcases x with x | l <;> rcases y with y | l'
  · rfl
  · by_cases hl : l' ∈ J
    · exact nomatch (h.2.2 l' hl).mpr rfl
    · simp [free, hl]
  · by_cases hl : l ∈ J
    · exact nomatch (h.2.2 l hl).mp rfl
    · simp [free, hl]
  · by_cases hl : l ∈ J
    · cases (h.2.2 l hl).mp rfl
      rfl
    · by_cases hl' : l' ∈ J
      · cases (h.2.2 l' hl').mpr rfl
        rfl
      · simp [free, hl, hl']

omit [L.Blocks] in
theorem Compat.isLabel_eq {n : Nat} {J : List Nat} {ℓ : Nat} (hℓ : ℓ ∈ J) {t : L.Tp}
    {x : PVar V t} {y : PVar V' t} (h : Compat n J x y) : isLabel ℓ x = isLabel ℓ y := by
  have := h.2.2 ℓ hℓ
  rcases x with x | l <;> rcases y with y | l' <;> simp_all [isLabel]

omit [L.Blocks] in
theorem Compat.fresh {n : Nat} {J : List Nat} (t : L.Tp) :
    Compat (n + 1) J (.inr n : PVar V t) (.inr n : PVar V' t) := by
  refine ⟨fun l hl => ?_, fun l hl => ?_, fun l _ => ?_⟩
  · cases hl
    omega
  · cases hl
    omega
  · simp

omit [L.Blocks] in
theorem Compat.succ {n : Nat} {J : List Nat} {t : L.Tp} {x : PVar V t} {y : PVar V' t}
    (h : Compat n J x y) : Compat (n + 1) J x y :=
  ⟨fun l hl => Nat.lt_succ_of_lt (h.1 l hl), fun l hl => Nat.lt_succ_of_lt (h.2.1 l hl), h.2.2⟩

omit [L.Blocks] in
/-- Old variables, once a fresh label becomes a join point's. -/
theorem Compat.jp {n : Nat} {J : List Nat} {t : L.Tp} {x : PVar V t} {y : PVar V' t}
    (h : Compat n J x y) : Compat (n + 1) (n :: J) x y := by
  refine ⟨fun l hl => Nat.lt_succ_of_lt (h.1 l hl), fun l hl => Nat.lt_succ_of_lt (h.2.1 l hl),
    fun l hl => ?_⟩
  rcases List.mem_cons.mp hl with rfl | hl
  · constructor
    · intro hx
      exact (Nat.lt_irrefl _ (h.1 _ hx)).elim
    · intro hy
      exact (Nat.lt_irrefl _ (h.2.1 _ hy)).elim
  · exact h.2.2 l hl

omit [L.Blocks] in
theorem CompatCtx.cons {n : Nat} {J : List Nat} {Δ : WfCtx L (PVar V) (PVar V')}
    (h : CompatCtx n J Δ) {t : L.Tp} {x : PVar V t} {y : PVar V' t} (hxy : Compat n J x y) :
    CompatCtx n J (⟨t, x, y⟩ :: Δ) := by
  intro t' x' y' he
  rcases List.mem_cons.mp he with he | he
  · cases he
    exact hxy
  · exact h he

omit [L.Blocks] in
theorem CompatCtx.succ {n : Nat} {J : List Nat} {Δ : WfCtx L (PVar V) (PVar V')}
    (h : CompatCtx n J Δ) : CompatCtx (n + 1) J Δ :=
  fun he => (h he).succ

omit [L.Blocks] in
theorem CompatCtx.jp {n : Nat} {J : List Nat} {Δ : WfCtx L (PVar V) (PVar V')}
    (h : CompatCtx n J Δ) : CompatCtx (n + 1) (n :: J) Δ :=
  fun he => (h he).jp

omit [L.Blocks] in
theorem freeArgs_eq {n : Nat} {J : List Nat} {Δ : WfCtx L (PVar V) (PVar V')}
    (hc : CompatCtx n J Δ) {ts : List L.Tp} {aA : HList (PVar V) ts} {aB : HList (PVar V') ts}
    (h : WfArgs Δ aA aB) : freeArgs J aA = freeArgs J aB := by
  induction h with
  | nil => rfl
  | cons hx _ ih =>
    simp only [freeArgs]
    rw [(hc hx).free_eq, ih]

omit [L.Blocks] in
theorem isRet_eq {n : Nat} {J : List Nat} {Δ : WfCtx L (PVar V) (PVar V')} {γ : L.Ctx}
    {t o : L.Tp} {kA : PVar V t → Expr L (PVar V) γ o} {kB : PVar V' t → Expr L (PVar V') γ o}
    (h : ∀ x y, Expr.Wf (⟨t, x, y⟩ :: Δ) (kA x) (kB y)) (hc : CompatCtx n J Δ) :
    isRet n kA = isRet n kB := by
  have w := h (.inr n) (.inr n)
  unfold isRet
  generalize kA (.inr n) = eA at w
  generalize kB (.inr n) = eB at w
  cases w with
  | @ret _ _ _ xA xB hx =>
    rcases List.mem_cons.mp hx with hx | hx
    · cases hx
      rfl
    · obtain ⟨h₁, h₂, _⟩ := hc hx
      have hA : isLabel n xA = false := by
        rcases xA with _ | l
        · rfl
        · simp only [isLabel, beq_eq_false_iff_ne]
          exact Nat.ne_of_lt (h₁ l rfl)
      have hB : isLabel n xB = false := by
        rcases xB with _ | l
        · rfl
        · simp only [isLabel, beq_eq_false_iff_ne]
          exact Nat.ne_of_lt (h₂ l rfl)
      simp only [hA, hB]
  | _ => rfl

/-- `ok` decides alike on corresponding instantiations. -/
theorem ok_congr {γ : L.Ctx} {o : L.Tp} {Δ : WfCtx L (PVar V) (PVar V')}
    {eA : Expr L (PVar V) γ o} {eB : Expr L (PVar V') γ o} (h : Expr.Wf Δ eA eB) :
    ∀ {n : Nat} {J : List Nat} {a : Option Nat}, CompatCtx n J Δ → (∀ l ∈ J, l < n) →
      (∀ ℓ, a = some ℓ → ℓ ∈ J) → ok n J a eA = ok n J a eB := by
  have hJs : ∀ {n : Nat} {J : List Nat}, (∀ l ∈ J, l < n) → ∀ l ∈ J, l < n + 1 :=
    fun hJ l hl => Nat.lt_succ_of_lt (hJ l hl)
  have hJn : ∀ {n : Nat} {J : List Nat}, (∀ l ∈ J, l < n) → ∀ l ∈ n :: J, l < n + 1 := by
    intro n J hJ l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · omega
    · exact Nat.lt_succ_of_lt (hJ l hl)
  have hnone : ∀ ℓ, (none : Option Nat) = some ℓ → ℓ ∈ ([] : List Nat) := fun _ h => nomatch h
  have hnone' : ∀ {J : List Nat} ℓ, (none : Option Nat) = some ℓ → ℓ ∈ J := fun _ h => nomatch h
  have fresh : ∀ {n : Nat} {J : List Nat} {Δ : WfCtx L (PVar V) (PVar V')} {t : L.Tp},
      CompatCtx n J Δ → (∀ l ∈ J, l < n) →
      CompatCtx (n + 1) J (⟨t, (.inr n : PVar V t), (.inr n : PVar V' t)⟩ :: Δ) :=
    fun hc hJ => CompatCtx.cons (CompatCtx.succ hc) (.fresh _)
  induction h with
  | ret hx =>
    intro n J a hc _ _
    cases a
    · exact (hc hx).free_eq
    · rfl
  | lit _ ih =>
    intro n J a hc hJ ha
    simp only [ok]
    exact ih _ _ (fresh hc hJ) (hJs hJ) ha
  | builtin hargs _ ih =>
    intro n J a hc hJ ha
    simp only [ok]
    rw [freeArgs_eq hc hargs, ih _ _ (fresh hc hJ) (hJs hJ) ha]
  | lam _ _ ihb ihk =>
    intro n J a hc hJ ha
    simp only [ok]
    rw [ihb _ _ (a := a) (fresh hc hJ) (hJs hJ) ha,
      ihb _ _ (a := none) (fresh hc hJ) (hJs hJ) hnone',
      ihk _ _ (a := some n) (CompatCtx.cons (CompatCtx.jp hc) (.fresh _)) (hJn hJ)
        (fun _ h => by cases h; exact List.mem_cons_self),
      ihk _ _ (a := a) (fresh hc hJ) (hJs hJ) ha]
  | app hf hx hk ih =>
    intro n J a hc hJ ha
    cases a with
    | none =>
      simp only [ok]
      rw [(hc hf).free_eq, (hc hx).free_eq, ih _ _ (a := none) (fresh hc hJ) (hJs hJ) hnone']
    | some ℓ =>
      simp only [ok]
      rw [(hc hf).free_eq, (hc hx).free_eq, ih _ _ (a := some ℓ) (fresh hc hJ) (hJs hJ) ha,
        (hc hf).isLabel_eq (ha ℓ rfl), isRet_eq hk hc]
  | ite hcnd _ _ hk iht ihe ihk =>
    intro n J a hc hJ ha
    cases a with
    | none =>
      simp only [ok]
      rw [(hc hcnd).free_eq, iht (a := none) hc hJ hnone', ihe (a := none) hc hJ hnone',
        ihk _ _ (a := none) (fresh hc hJ) (hJs hJ) hnone']
    | some ℓ =>
      simp only [ok]
      rw [(hc hcnd).free_eq, iht (a := none) hc hJ hnone', ihe (a := none) hc hJ hnone',
        iht (a := some ℓ) hc hJ ha, ihe (a := some ℓ) hc hJ ha,
        ihk _ _ (a := some ℓ) (fresh hc hJ) (hJs hJ) ha, isRet_eq hk hc]
  | loop hi _ _ ihb ihk =>
    intro n J a hc hJ ha
    simp only [ok]
    rw [(hc hi).free_eq, ihb _ _ (a := none) (fresh hc hJ) (hJs hJ) hnone',
      ihk _ _ (a := a) (fresh hc hJ) (hJs hJ) ha]
  | op hi _ _ ihb ihk =>
    intro n J a hc hJ ha
    simp only [ok]
    rw [(hc hi).free_eq, ihk _ _ (a := a) (fresh hc hJ) (hJs hJ) ha]
    congr 2
    exact List.all_congr rfl fun b => ihb b _ _ (a := none) (fresh hc hJ) (hJs hJ) hnone'

end Congr

/-! ## The translation is related to its input -/

section Translation

variable {V : L.Tp → Type}

/-- How the contexts of the translation relate: `Δw` pairs the evaluator's
variables with those of the translation's input, which are its own variables
(paired in `Δ`) or labels of join points in `J`, each of one variable. `Δd`
pairs the translation's input with itself, for deciding with `ok`. -/
structure Good (n : Nat) (J : List Nat) (Δw : WfCtx L V (PVar V))
    (Δd : WfCtx L (PVar V) (PVar V)) (Δ : WfCtx L V V) : Prop where
  lt : ∀ l ∈ J, l < n
  inl : ∀ {t : L.Tp} {v v' : V t}, ⟨t, v, .inl v'⟩ ∈ Δw → ⟨t, v, v'⟩ ∈ Δ
  inr : ∀ {t : L.Tp} {v : V t} {l : Nat}, ⟨t, v, .inr l⟩ ∈ Δw → l ∈ J
  uniq : ∀ {t t' : L.Tp} {v : V t} {v' : V t'} {l : Nat},
    ⟨t, v, .inr l⟩ ∈ Δw → ⟨t', v', .inr l⟩ ∈ Δw → (⟨t, v⟩ : Σ t, V t) = ⟨t', v'⟩
  diag : CompatCtx n J Δd

omit [L.Blocks] in
theorem Good.nil : Good (V := V) 0 [] [] [] [] :=
  ⟨nofun, nofun, nofun, nofun, nofun⟩

omit [L.Blocks] in
theorem Good.succ {n : Nat} {J : List Nat} {Δw : WfCtx L V (PVar V)}
    {Δd : WfCtx L (PVar V) (PVar V)} {Δ : WfCtx L V V} (h : Good n J Δw Δd Δ) :
    Good (n + 1) J Δw Δd Δ :=
  ⟨fun l hl => Nat.lt_succ_of_lt (h.lt l hl), h.inl, h.inr, h.uniq, CompatCtx.succ h.diag⟩

omit [L.Blocks] in
/-- A variable of the translation's input, paired with the evaluator's. -/
theorem Good.var {n : Nat} {J : List Nat} {Δw : WfCtx L V (PVar V)}
    {Δd : WfCtx L (PVar V) (PVar V)} {Δ : WfCtx L V V} (h : Good n J Δw Δd Δ) {t : L.Tp}
    (v v' : V t) :
    Good n J (⟨t, v, .inl v'⟩ :: Δw) (⟨t, .inl v', .inl v'⟩ :: Δd) (⟨t, v, v'⟩ :: Δ) := by
  refine ⟨h.lt, fun hm => ?_, fun hm => ?_, fun hm hm' => ?_, ?_⟩
  · rcases List.mem_cons.mp hm with hm | hm
    · cases hm
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (h.inl hm)
  · rcases List.mem_cons.mp hm with hm | hm
    · cases hm
    · exact h.inr hm
  · rcases List.mem_cons.mp hm with hm | hm
    · cases hm
    rcases List.mem_cons.mp hm' with hm' | hm'
    · cases hm'
    exact h.uniq hm hm'
  · exact CompatCtx.cons h.diag ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun _ _ => Iff.rfl⟩

omit [L.Blocks] in
/-- A join point: its label is fresh. -/
theorem Good.jp {n : Nat} {J : List Nat} {Δw : WfCtx L V (PVar V)}
    {Δd : WfCtx L (PVar V) (PVar V)} {Δ : WfCtx L V V} (h : Good n J Δw Δd Δ) {t : L.Tp}
    (j : V t) :
    Good (n + 1) (n :: J) (⟨t, j, .inr n⟩ :: Δw) (⟨t, .inr n, .inr n⟩ :: Δd) Δ := by
  have hfresh : ∀ {t' : L.Tp} {v : V t'}, ⟨t', v, (.inr n : PVar V t')⟩ ∉ Δw :=
    fun hm => Nat.lt_irrefl _ (h.lt _ (h.inr hm))
  refine ⟨fun l hl => ?_, fun hm => ?_, fun hm => ?_, fun hm hm' => ?_, ?_⟩
  · rcases List.mem_cons.mp hl with rfl | hl
    · omega
    · exact Nat.lt_succ_of_lt (h.lt l hl)
  · rcases List.mem_cons.mp hm with hm | hm
    · cases hm
    · exact h.inl hm
  · rcases List.mem_cons.mp hm with hm | hm
    · cases hm
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (h.inr hm)
  · rcases List.mem_cons.mp hm with hm | hm <;> rcases List.mem_cons.mp hm' with hm' | hm'
    · cases hm
      cases hm'
      rfl
    · cases hm
      exact (hfresh hm').elim
    · cases hm'
      exact (hfresh hm).elim
    · exact h.uniq hm hm'
  · exact CompatCtx.cons (CompatCtx.jp h.diag) (.fresh _)

omit [L.Blocks] in
theorem Good.free {n : Nat} {J : List Nat} {Δw : WfCtx L V (PVar V)}
    {Δd : WfCtx L (PVar V) (PVar V)} {Δ : WfCtx L V V} (h : Good n J Δw Δd Δ) {t : L.Tp}
    {v : V t} {x : PVar V t} (hm : ⟨t, v, x⟩ ∈ Δw) (hf : JoinPoints.free J x = true) :
    ∃ v', x = .inl v' ∧ ⟨t, v, v'⟩ ∈ Δ := by
  rcases x with v' | l
  · exact ⟨v', rfl, h.inl hm⟩
  · simp [JoinPoints.free] at hf
    exact absurd (h.inr hm) hf

omit [L.Blocks] in
theorem Good.vars {n : Nat} {J : List Nat} {Δw : WfCtx L V (PVar V)}
    {Δd : WfCtx L (PVar V) (PVar V)} {Δ : WfCtx L V V} (h : Good n J Δw Δd Δ)
    {ts : List L.Tp} {a₁ : HList V ts} {aC : HList (PVar V) ts} (ha : WfArgs Δw a₁ aC)
    (hf : freeArgs J aC = true) :
    ∃ a₂, WfArgs Δ a₁ a₂ ∧ ∀ {γ : L.Ctx} {o : L.Tp} (K : HList V ts → Expr L V γ o),
      vars aC K = K a₂ := by
  induction ha with
  | nil => exact ⟨.nil, .nil, fun _ => rfl⟩
  | cons hx _ ih =>
    change (JoinPoints.free J _ && freeArgs J _) = true at hf
    simp only [Bool.and_eq_true] at hf
    obtain ⟨v', rfl, hm⟩ := h.free hx hf.1
    obtain ⟨a₂, ha₂, hK⟩ := ih hf.2
    exact ⟨.cons v' a₂, .cons hm ha₂, fun K => hK fun vs => K (.cons v' vs)⟩

/-- Modes of the translation and of the relation agree: a join point label
stands for the evaluator's join point. -/
inductive ModeRel (J : List Nat) (Δw : WfCtx L V (PVar V)) :
    {γ : L.Ctx} → {o o' : L.Tp} → Mode V γ o o' → RMode V γ o o' → Prop
| normal {γ : L.Ctx} {o : L.Tp} : ModeRel J Δw (γ := γ) (o := o) .normal .normal
| jump {γ : L.Ctx} {o o' τ : L.Tp} {ℓ : Nat} {j : V (.fn τ o)} {κ : V τ → Expr L V γ o'} :
    ⟨.fn τ o, j, .inr ℓ⟩ ∈ Δw → ℓ ∈ J → ModeRel J Δw (.jump ℓ κ) (.jump j κ)

omit [L.Blocks] in
theorem ModeRel.mono {J J' : List Nat} {Δw Δw' : WfCtx L V (PVar V)} {γ : L.Ctx} {o o' : L.Tp}
    {tm : Mode V γ o o'} {rm : RMode V γ o o'} (h : ModeRel J Δw tm rm)
    (hJ : ∀ l ∈ J, l ∈ J') (hΔ : ∀ x ∈ Δw, x ∈ Δw') : ModeRel J' Δw' tm rm := by
  cases h with
  | normal => exact .normal
  | jump hm hℓ => exact .jump (hΔ _ hm) (hJ _ hℓ)

omit [L.Blocks] in
theorem ModeRel.act {J : List Nat} {Δw : WfCtx L V (PVar V)} {γ : L.Ctx} {o o' : L.Tp}
    {tm : Mode V γ o o'} {rm : RMode V γ o o'} (h : ModeRel J Δw tm rm) :
    ∀ ℓ, tm.act = some ℓ → ℓ ∈ J := by
  cases h with
  | normal => exact fun _ h => nomatch h
  | jump _ hℓ =>
    intro ℓ h
    cases h
    exact hℓ

omit [L.Blocks] in
theorem ModeRel.cons {J : List Nat} {Δw : WfCtx L V (PVar V)} {γ : L.Ctx} {o o' : L.Tp}
    {tm : Mode V γ o o'} {rm : RMode V γ o o'} (h : ModeRel J Δw tm rm)
    (x : Σ t : L.Tp, V t × PVar V t) : ModeRel J (x :: Δw) tm rm :=
  h.mono (fun _ h => h) fun _ h => List.mem_cons_of_mem _ h

/-- Deciding on the translation's own instantiation, from deciding on fresh
labels. -/
theorem ok_inst {n : Nat} {J : List Nat} {a : Option Nat} {Δd : WfCtx L (PVar V) (PVar V)}
    {γ : L.Ctx} {t o : L.Tp} {k : PVar V t → Expr L (PVar V) γ o}
    (hd : ∀ x y, Expr.Wf (⟨t, x, y⟩ :: Δd) (k x) (k y)) (hc : CompatCtx n J Δd)
    (hJ : ∀ l ∈ J, l < n) (ha : ∀ ℓ, a = some ℓ → ℓ ∈ J)
    (h : ok (n + 1) J a (k (.inr n)) = true) (v : V t) : ok (n + 1) J a (k (.inl v)) = true := by
  have hcomp : Compat (n + 1) J (.inr n : PVar V t) (.inl v : PVar V t) := by
    refine ⟨fun l hl => ?_, nofun, fun l hl => ?_⟩
    · cases hl
      omega
    · constructor
      · intro he
        cases he
        exact (Nat.lt_irrefl _ (hJ _ hl)).elim
      · nofun
  rw [← ok_congr (hd (.inr n) (.inl v)) (CompatCtx.cons (CompatCtx.succ hc) hcomp)
    (fun l hl => Nat.lt_succ_of_lt (hJ l hl)) ha]
  exact h

omit [L.Blocks] in
/-- A continuation the pass tests as returning returns. -/
theorem isRet_ret {n : Nat} {J : List Nat} {Δw : WfCtx L V (PVar V)}
    {Δd : WfCtx L (PVar V) (PVar V)} {Δ : WfCtx L V V} (hg : Good n J Δw Δd Δ) {γ : L.Ctx}
    {t o : L.Tp} {k₁ : V t → Expr L V γ o} {kC : PVar V t → Expr L (PVar V) γ o}
    (hk : ∀ r₁ r₂, Expr.Wf (⟨t, r₁, r₂⟩ :: Δw) (k₁ r₁) (kC r₂))
    (hd : ∀ x y, Expr.Wf (⟨t, x, y⟩ :: Δd) (kC x) (kC y)) (h : isRet n kC = true) :
    ∃ e : t = o, e ▸ k₁ = fun r => .ret r := by
  unfold isRet at h
  have hd' := hd (.inr n) (.inr n)
  have hk' := fun r₁ => hk r₁ (.inr n)
  generalize kC (.inr n) = eC at hd' hk' h
  cases hd' with
  | @ret _ _ _ x _ hx =>
    rcases x with _ | l
    · simp [isLabel] at h
    simp only [isLabel, beq_iff_eq] at h
    subst h
    rcases List.mem_cons.mp hx with hx | hx
    · cases hx
      refine ⟨rfl, funext fun r₁ => ?_⟩
      show k₁ r₁ = Expr.ret r₁
      have w := hk' r₁
      generalize k₁ r₁ = e₁ at w ⊢
      cases w with
      | ret hy =>
        rcases List.mem_cons.mp hy with hy | hy
        · cases hy
          rfl
        · exact (Nat.lt_irrefl _ (hg.lt _ (hg.inr hy))).elim
    · exact (Nat.lt_irrefl _ ((hg.diag hx).1 _ rfl)).elim
  | _ => simp at h

/-- The translation is related to its input, in agreeing modes, where `ok`
holds. -/
theorem tr_jp {γ : L.Ctx} {o : L.Tp} {Δw : WfCtx L V (PVar V)} {e₁ : Expr L V γ o}
    {eC : Expr L (PVar V) γ o} (hw : Expr.Wf Δw e₁ eC) :
    ∀ {o' : L.Tp} {n : Nat} {J : List Nat} {Δd : WfCtx L (PVar V) (PVar V)} {Δ : WfCtx L V V}
      {tm : Mode V γ o o'} {rm : RMode V γ o o'},
      Expr.Wf Δd eC eC → Good n J Δw Δd Δ → ModeRel J Δw tm rm → ok n J tm.act eC = true →
      JP Δ rm e₁ (tr n J tm eC) := by
  have hnone : ∀ {J : List Nat} ℓ, (none : Option Nat) = some ℓ → ℓ ∈ J := fun _ h => nomatch h
  induction hw with
  | ret hx =>
    intro o' n J Δd Δ tm rm _ hg hm hok
    cases hm with
    | normal =>
      simp only [ok, Mode.act] at hok
      obtain ⟨v', rfl, hm⟩ := hg.free hx hok
      exact .sync (.ret hm)
    | jump => simp [ok, Mode.act] at hok
  | lit _ ih =>
    intro o' n J Δd Δ tm rm hd hg hm hok
    cases hd with
    | lit hd' =>
      simp only [ok] at hok
      simp only [tr]
      exact .sync (.lit fun x₁ x₂ => ih x₁ (.inl x₂) (hd' _ _) (hg.var x₁ x₂).succ (hm.cons _)
        (ok_inst hd' hg.diag hg.lt hm.act hok x₂))
  | builtin ha _ ih =>
    intro o' n J Δd Δ tm rm hd hg hm hok
    cases hd with
    | builtin _ hd' =>
      simp only [ok, Bool.and_eq_true] at hok
      obtain ⟨a₂, ha₂, hK⟩ := hg.vars ha hok.1
      simp only [tr]
      rw [hK]
      exact .sync (.builtin ha₂ fun x₁ x₂ => ih x₁ (.inl x₂) (hd' _ _) (hg.var x₁ x₂).succ
        (hm.cons _) (ok_inst hd' hg.diag hg.lt hm.act hok.2 x₂))
  | @lam _ o₀ Δw inp out b₁ bC k₁ kC _ _ ihb ihk =>
    intro o' n J Δd Δ tm rm hd hg hm hok
    cases hd with
    | lam hdb hdk =>
      have hbody : ∀ {o'' : L.Tp} {tm' : Mode V _ out o''} {rm' : RMode V _ out o''},
          ModeRel J Δw tm' rm' →
          ok (n + 1) J tm'.act (bC (.inr n)) = true →
          ∀ y₁ y₂, JP (⟨inp, y₁, y₂⟩ :: Δ) rm' (b₁ y₁) (tr (n + 1) J tm' (bC (.inl y₂))) :=
        fun hm' hok' y₁ y₂ => ihb y₁ (.inl y₂) (hdb _ _) (hg.var y₁ y₂).succ (hm'.cons _)
          (ok_inst hdb hg.diag hg.lt hm'.act hok' y₂)
      have hcong : ok (n + 1) J none (bC (.inr n)) = true →
          ok (n + 1) J tm.act (kC (.inr n)) = true →
          JP Δ rm (.lam b₁ k₁) (.lam (fun x => tr (n + 1) J .normal (bC (.inl x)))
            fun f => tr (n + 1) J tm (kC (.inl f))) :=
        fun h₁ h₂ => .sync (.lam (hbody (tm' := .normal) (rm' := .normal) .normal h₁)
          fun f₁ f₂ => ihk f₁ (.inl f₂) (hdk _ _)
          (hg.var f₁ f₂).succ (hm.cons _) (ok_inst hdk hg.diag hg.lt hm.act h₂ f₂))
      simp only [ok, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
      by_cases hel : out = o₀ ∧ ok (n + 1) J tm.act (bC (.inr n)) = true ∧
          ok (n + 1) (n :: J) (some n) (kC (.inr n)) = true
      · obtain ⟨rfl, hb', hk'⟩ := hel
        rw [tr_lam_elim _ _ _ _ _ hb' hk', ← tr_jump_eq]
        exact .elim (hbody hm hb') fun j => ihk j (.inr n) (hdk _ _) (hg.jp j)
          (.jump List.mem_cons_self List.mem_cons_self) hk'
      · rw [tr_lam_keep _ _ _ _ _ hel]
        rcases hok with ⟨⟨h', h₁⟩, h₂⟩ | ⟨h₁, h₂⟩
        · exact absurd ⟨h', h₁, h₂⟩ hel
        · exact hcong h₁ h₂
  | @app _ _ Δw inp out f₁ fC x₁ xC k₁ kC hf hx hk ih =>
    intro o' n J Δd Δ tm rm hd hg hm hok
    cases hd with
    | app _ _ hdk =>
      have hcong : ∀ {tm : Mode V _ _ o'} {rm : RMode V _ _ o'}, ModeRel J Δw tm rm →
          JoinPoints.free J fC = true → JoinPoints.free J xC = true →
          ok (n + 1) J tm.act (kC (.inr n)) = true →
          JP Δ rm (.app f₁ x₁ k₁)
            (var fC fun f => var xC fun x => .app f x fun r => tr (n + 1) J tm (kC (.inl r))) := by
        intro tm rm hm hff hfx hk'
        obtain ⟨f₂, rfl, hf₂⟩ := hg.free hf hff
        obtain ⟨x₂, rfl, hx₂⟩ := hg.free hx hfx
        exact .sync (.app hf₂ hx₂ fun r₁ r₂ => ih r₁ (.inl r₂) (hdk _ _) (hg.var r₁ r₂).succ
          (hm.cons _) (ok_inst hdk hg.diag hg.lt hm.act hk' r₂))
      cases hm with
      | normal =>
        simp only [ok, Mode.act, Bool.and_eq_true] at hok
        simp only [tr]
        exact hcong .normal hok.1.1 hok.1.2 hok.2
      | @jump _ τ ℓ j κ hjm hℓ =>
        simp only [ok, Mode.act, Bool.or_eq_true, Bool.and_eq_true] at hok
        simp only [tr]
        by_cases hlr : (isLabel ℓ fC && isRet n kC) = true
        · rw [if_pos hlr]
          simp only [Bool.and_eq_true] at hlr
          obtain ⟨hl, hr⟩ := hlr
          rcases fC with f₂ | l
          · simp [isLabel] at hl
          simp only [isLabel, beq_iff_eq] at hl
          subst hl
          have hxfree : JoinPoints.free J xC = true := by
            rcases hok with ⟨_, h⟩ | ⟨⟨h, _⟩, _⟩
            · exact h
            · simp [JoinPoints.free] at h
              exact absurd hℓ h
          obtain ⟨x₂, rfl, hx₂⟩ := hg.free hx hxfree
          have hu := hg.uniq hf hjm
          simp only [Sigma.mk.injEq, Tp.fn.injEq] at hu
          obtain ⟨⟨rfl, rfl⟩, hfj⟩ := hu
          cases hfj
          obtain ⟨e, hk₁⟩ := isRet_ret hg hk hdk hr
          cases e
          have hk₁' : k₁ = fun r => .ret r := hk₁
          subst hk₁'
          rw [dif_pos rfl]
          exact .jump hx₂
        · rw [if_neg hlr]
          rcases hok with ⟨⟨h₁, h₂⟩, _⟩ | ⟨⟨h₁, h₂⟩, h₃⟩
          · exact absurd (by simp [h₁, h₂]) hlr
          · exact hcong (.jump hjm hℓ) h₁ h₂ h₃
  | @ite _ _ _ out c₁ cC t₁ e₁ tC eC k₁ kC hc _ _ hk iht ihe ihk =>
    intro o' n J Δd Δ tm rm hd hg hm hok
    cases hd with
    | ite _ hdt hde hdk =>
      cases hm with
      | normal =>
        simp only [ok, Mode.act, Bool.and_eq_true] at hok
        obtain ⟨⟨⟨hfc, hot⟩, hoe⟩, hok'⟩ := hok
        obtain ⟨c₂, rfl, hc₂⟩ := hg.free hc hfc
        simp only [tr]
        exact .sync (.ite hc₂ (iht hdt hg .normal hot) (ihe hde hg .normal hoe)
          fun r₁ r₂ => ihk r₁ (.inl r₂) (hdk _ _) (hg.var r₁ r₂).succ .normal
            (ok_inst hdk hg.diag hg.lt hnone hok' r₂))
      | jump hjm hℓ =>
        simp only [ok, Mode.act] at hok
        simp only [tr]
        by_cases hr : isRet n kC = true
        · rw [if_pos hr] at hok ⊢
          simp only [Bool.and_eq_true] at hok
          obtain ⟨⟨hfc, hot⟩, hoe⟩ := hok
          obtain ⟨c₂, rfl, hc₂⟩ := hg.free hc hfc
          obtain ⟨e, hk₁⟩ := isRet_ret hg hk hdk hr
          cases e
          have hk₁' : k₁ = fun r => .ret r := hk₁
          subst hk₁'
          exact .sync (.iteJump hc₂ (iht hdt hg (.jump hjm hℓ) hot) (ihe hde hg (.jump hjm hℓ) hoe))
        · rw [if_neg hr] at hok ⊢
          simp only [Bool.and_eq_true] at hok
          obtain ⟨⟨⟨hfc, hot⟩, hoe⟩, hok'⟩ := hok
          obtain ⟨c₂, rfl, hc₂⟩ := hg.free hc hfc
          exact .sync (.ite hc₂ (iht hdt hg .normal hot) (ihe hde hg .normal hoe)
            fun r₁ r₂ => ihk r₁ (.inl r₂) (hdk _ _) (hg.var r₁ r₂).succ ((ModeRel.jump hjm hℓ).cons _)
              (ok_inst hdk hg.diag hg.lt (fun _ h => by cases h; exact hℓ) hok' r₂))
  | loop hi _ _ ihb ihk =>
    intro o' n J Δd Δ tm rm hd hg hm hok
    cases hd with
    | loop _ hdb hdk =>
      simp only [ok, Bool.and_eq_true] at hok
      obtain ⟨⟨hfi, hob⟩, hok'⟩ := hok
      obtain ⟨i₂, rfl, hi₂⟩ := hg.free hi hfi
      simp only [tr]
      exact .sync (.loop hi₂ (fun x₁ x₂ => ihb x₁ (.inl x₂) (hdb _ _) (hg.var x₁ x₂).succ .normal
          (ok_inst hdb hg.diag hg.lt hnone hob x₂))
        fun r₁ r₂ => ihk r₁ (.inl r₂) (hdk _ _) (hg.var r₁ r₂).succ (hm.cons _)
          (ok_inst hdk hg.diag hg.lt hm.act hok' r₂))
  | op hi _ _ ihb ihk =>
    intro o' n J Δd Δ tm rm hd hg hm hok
    cases hd with
    | op _ hdb hdk =>
      simp only [ok, Bool.and_eq_true, List.all_eq_true] at hok
      obtain ⟨⟨hfi, hbl⟩, hok'⟩ := hok
      obtain ⟨i₂, rfl, hi₂⟩ := hg.free hi hfi
      simp only [tr]
      exact .sync (.op hi₂ (fun b x₁ x₂ => ihb b x₁ (.inl x₂) (hdb b _ _) (hg.var x₁ x₂).succ
          .normal (ok_inst (hdb b) hg.diag hg.lt hnone (hbl b (Language.Blocks.complete _ _ b)) x₂))
        fun r₁ r₂ => ihk r₁ (.inl r₂) (hdk _ _) (hg.var r₁ r₂).succ (hm.cons _)
          (ok_inst hdk hg.diag hg.lt hm.act hok' r₂))

omit [L.Blocks] in
theorem freeArgs_nil : ∀ {ts : List L.Tp} (a : HList (PVar V) ts), freeArgs [] a = true
  | [], .nil => rfl
  | _ :: _, .cons x xs => by
    rcases x with _ | _ <;> simp [freeArgs, JoinPoints.free, freeArgs_nil xs]

/-- With no join point in scope, everything can be translated normally. -/
theorem ok_nil {γ : L.Ctx} {o : L.Tp} (e : Expr L (PVar V) γ o) (n : Nat) :
    ok n [] none e = true := by
  induction e generalizing n with
  | ret x => rcases x with _ | _ <;> rfl
  | lit _ _ _ ih => exact ih _ _
  | builtin _ args _ ih => simp only [ok, freeArgs_nil, ih, Bool.and_self]
  | lam _ _ ihb ihk => simp only [ok, ihb, ihk, Bool.and_self, Bool.or_true]
  | app f x _ ih => rcases f with _ | _ <;> rcases x with _ | _ <;> simp [ok, JoinPoints.free, ih]
  | ite c _ _ _ iht ihe ihk => rcases c with _ | _ <;> simp [ok, JoinPoints.free, iht, ihe, ihk]
  | loop _ i _ ihb ihk => rcases i with _ | _ <;> simp [ok, JoinPoints.free, ihb, ihk]
  | op _ i _ _ ihb ihk => rcases i with _ | _ <;> simp [ok, JoinPoints.free, ihb, ihk]

theorem trProg_jp {mainCtx : L.Ctx} {iT oT : L.AbiTp} {Δw : WfCtx L V (PVar V)}
    {p₁ : Program L mainCtx iT oT V} {pC : Program L mainCtx iT oT (PVar V)}
    (hw : Program.WfIn Δw p₁ pC) :
    ∀ {Δd : WfCtx L (PVar V) (PVar V)} {Δ : WfCtx L V V}, Program.WfIn Δd pC pC →
      Good 0 [] Δw Δd Δ → Program.JP Δ p₁ (trProg pC) := by
  induction hw with
  | define hb _ ih =>
    intro Δd Δ hd hg
    cases hd with
    | define hdb hdk =>
      exact .define (fun f₁ f₂ x₁ x₂ => tr_jp (hb f₁ (.inl f₂) x₁ (.inl x₂)) (hdb _ _ _ _)
          ((hg.var f₁ f₂).var x₁ x₂) .normal (ok_nil _ 0))
        fun f₁ f₂ => ih f₁ (.inl f₂) (hdk _ _) (hg.var f₁ f₂)
  | main hb =>
    intro Δd Δ hd hg
    cases hd with
    | main hdb =>
      exact .main fun x₁ x₂ => tr_jp (hb x₁ (.inl x₂)) (hdb _ _) (hg.var x₁ x₂) .normal (ok_nil _ 0)

end Translation

/-- A well-formed program is related to its translation. -/
theorem _root_.Freigen.Ast.Program.joinPoints_jp {mainCtx : L.Ctx} {iT oT : L.AbiTp}
    {p : ∀ {V : L.Tp → Type}, Program L mainCtx iT oT V} (hp : Ast.Program.Wf p)
    (V : L.Tp → Type) :
    Program.JP [] (p (V := V)) (Ast.Program.joinPoints p (V := V)) :=
  trProg_jp (hp V (PVar V)) (hp (PVar V) (PVar V)) Good.nil

end Freigen.Ast.JoinPoints
