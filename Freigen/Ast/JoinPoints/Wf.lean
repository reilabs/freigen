import Freigen.Ast.JoinPoints.Alg

/-!
The translation of a well-formed program is well-formed
(`Program.joinPoints_wf`), so passes can be composed. Two instantiations of
the translation's input decide alike (`ok_congr`) and build the same shapes.
-/

namespace Freigen.Ast.JoinPoints

variable {L : Language} [L.Blocks] {V₁ V₂ : L.Tp → Type}

/-- Corresponding variables of two instantiations of the translation's
input: variables of the outputs, corresponding in `Δo`, or the same label
below `n`. -/
def Sim (n : Nat) (Δx : WfCtx L (PVar V₁) (PVar V₂)) (Δo : WfCtx L V₁ V₂) : Prop :=
  ∀ {t : L.Tp} {x : PVar V₁ t} {y : PVar V₂ t}, ⟨t, x, y⟩ ∈ Δx →
    (∃ a b, x = .inl a ∧ y = .inl b ∧ ⟨t, a, b⟩ ∈ Δo) ∨ (∃ l, x = .inr l ∧ y = .inr l ∧ l < n)

/-- Continuations building corresponding outputs on corresponding variables,
in any larger context. -/
def KW {γ : L.Ctx} {t o : L.Tp} (Δo : WfCtx L V₁ V₂) (kA : V₁ t → Expr L V₁ γ o)
    (kB : V₂ t → Expr L V₂ γ o) : Prop :=
  ∀ Δ' a b, (∀ z ∈ Δo, z ∈ Δ') → ⟨t, a, b⟩ ∈ Δ' → Expr.Wf Δ' (kA a) (kB b)

section

omit [L.Blocks]

theorem Sim.nil : Sim (V₁ := V₁) (V₂ := V₂) (L := L) 0 [] [] := nofun

theorem Sim.compat {n : Nat} {J : List Nat} {Δx : WfCtx L (PVar V₁) (PVar V₂)}
    {Δo : WfCtx L V₁ V₂} (h : Sim n Δx Δo) : CompatCtx n J Δx := by
  intro t x y hm
  rcases h hm with ⟨a, b, rfl, rfl, _⟩ | ⟨l, rfl, rfl, hl⟩
  · exact ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun _ _ => by simp⟩
  · refine ⟨fun l' h => ?_, fun l' h => ?_, fun _ _ => by simp⟩ <;> cases h <;> exact hl

theorem Sim.mono {n : Nat} {Δx : WfCtx L (PVar V₁) (PVar V₂)} {Δo Δo' : WfCtx L V₁ V₂}
    (h : Sim n Δx Δo) (hΔ : ∀ z ∈ Δo, z ∈ Δo') : Sim n Δx Δo' := by
  intro t x y hm
  rcases h hm with ⟨a, b, rfl, rfl, hab⟩ | hl
  · exact .inl ⟨a, b, rfl, rfl, hΔ _ hab⟩
  · exact .inr hl

theorem Sim.var {n : Nat} {Δx : WfCtx L (PVar V₁) (PVar V₂)} {Δo : WfCtx L V₁ V₂}
    (h : Sim n Δx Δo) {t : L.Tp} (a : V₁ t) (b : V₂ t) :
    Sim (n + 1) (⟨t, .inl a, .inl b⟩ :: Δx) (⟨t, a, b⟩ :: Δo) := by
  intro t' x y hm
  rcases List.mem_cons.mp hm with hm | hm
  · cases hm
    exact .inl ⟨a, b, rfl, rfl, List.mem_cons_self⟩
  · rcases h hm with ⟨a', b', rfl, rfl, hab⟩ | ⟨l, rfl, rfl, hl⟩
    · exact .inl ⟨a', b', rfl, rfl, List.mem_cons_of_mem _ hab⟩
    · exact .inr ⟨l, rfl, rfl, Nat.lt_succ_of_lt hl⟩

theorem Sim.label {n : Nat} {Δx : WfCtx L (PVar V₁) (PVar V₂)} {Δo : WfCtx L V₁ V₂}
    (h : Sim n Δx Δo) (t : L.Tp) : Sim (n + 1) (⟨t, .inr n, .inr n⟩ :: Δx) Δo := by
  intro t' x y hm
  rcases List.mem_cons.mp hm with hm | hm
  · cases hm
    exact .inr ⟨n, rfl, rfl, Nat.lt_succ_self n⟩
  · rcases h hm with hab | ⟨l, rfl, rfl, hl⟩
    · exact .inl hab
    · exact .inr ⟨l, rfl, rfl, Nat.lt_succ_of_lt hl⟩

theorem KW.mono {γ : L.Ctx} {t o : L.Tp} {Δo Δo' : WfCtx L V₁ V₂} {kA : V₁ t → Expr L V₁ γ o}
    {kB : V₂ t → Expr L V₂ γ o} (h : KW Δo kA kB) (hΔ : ∀ z ∈ Δo, z ∈ Δo') : KW Δo' kA kB :=
  fun Δ' a b hΔ' hab => h Δ' a b (fun z hz => hΔ' z (hΔ z hz)) hab

theorem stuck_wf {γ : L.Ctx} {t o : L.Tp} {Δo : WfCtx L V₁ V₂} {kA : V₁ t → Expr L V₁ γ o}
    {kB : V₂ t → Expr L V₂ γ o} (h : KW Δo kA kB) : Expr.Wf Δo (stuck t kA) (stuck t kB) :=
  .builtin .nil fun _ _ => .lit fun _ _ => .builtin
    (.cons (List.mem_cons_of_mem _ List.mem_cons_self) (.cons List.mem_cons_self .nil))
    fun _ _ => h _ _ _ (fun _ hz => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hz))) List.mem_cons_self

theorem var_wf {n : Nat} {Δx : WfCtx L (PVar V₁) (PVar V₂)} {Δo : WfCtx L V₁ V₂}
    (hs : Sim n Δx Δo) {γ : L.Ctx} {t o : L.Tp} {x : PVar V₁ t} {y : PVar V₂ t}
    (hm : ⟨t, x, y⟩ ∈ Δx) {kA : V₁ t → Expr L V₁ γ o} {kB : V₂ t → Expr L V₂ γ o}
    (h : KW Δo kA kB) : Expr.Wf Δo (var x kA) (var y kB) := by
  rcases hs hm with ⟨a, b, rfl, rfl, hab⟩ | ⟨l, rfl, rfl, _⟩
  · exact h Δo a b (fun _ h => h) hab
  · exact stuck_wf h

theorem vars_wf {n : Nat} {Δx : WfCtx L (PVar V₁) (PVar V₂)} {Δo : WfCtx L V₁ V₂}
    (hs : Sim n Δx Δo) {γ : L.Ctx} {o : L.Tp} {ts : List L.Tp} {aA : HList (PVar V₁) ts}
    {aB : HList (PVar V₂) ts} (ha : WfArgs Δx aA aB) :
    ∀ {Δo' : WfCtx L V₁ V₂} {KA : HList V₁ ts → Expr L V₁ γ o} {KB : HList V₂ ts → Expr L V₂ γ o},
      (∀ z ∈ Δo, z ∈ Δo') →
      (∀ Δ' as bs, (∀ z ∈ Δo', z ∈ Δ') → WfArgs Δ' as bs → Expr.Wf Δ' (KA as) (KB bs)) →
      Expr.Wf Δo' (vars aA KA) (vars aB KB) := by
  induction ha with
  | nil => exact fun _ h => h _ _ _ (fun _ h => h) .nil
  | cons hx _ ih =>
    intro Δo' KA KB hΔ h
    exact var_wf (Sim.mono hs hΔ) hx fun Δ' a b hΔ' hab =>
      ih (fun z hz => hΔ' z (hΔ z hz)) fun Δ'' as bs hΔ'' has =>
        h Δ'' _ _ (fun z hz => hΔ'' z (hΔ' z hz)) (.cons (hΔ'' _ hab) has)

end

/-- Corresponding modes: normal, or of the same join point label with
corresponding translations of its tail calls. -/
inductive MRel (Δo : WfCtx L V₁ V₂) : {γ : L.Ctx} → {o o' : L.Tp} → Mode V₁ γ o o' →
    Mode V₂ γ o o' → Prop
| normal {γ : L.Ctx} {o : L.Tp} : MRel Δo (γ := γ) (o := o) .normal .normal
| jump {γ : L.Ctx} {o o' τ : L.Tp} {ℓ : Nat} {κA : V₁ τ → Expr L V₁ γ o'}
    {κB : V₂ τ → Expr L V₂ γ o'} :
    KW Δo κA κB → MRel Δo (o := o) (.jump ℓ κA) (.jump ℓ κB)

omit [L.Blocks] in
theorem MRel.mono {Δo Δo' : WfCtx L V₁ V₂} {γ : L.Ctx} {o o' : L.Tp} {tmA : Mode V₁ γ o o'}
    {tmB : Mode V₂ γ o o'} (h : MRel Δo tmA tmB) (hΔ : ∀ z ∈ Δo, z ∈ Δo') : MRel Δo' tmA tmB := by
  cases h with
  | normal => exact .normal
  | jump hk => exact .jump (hk.mono hΔ)

omit [L.Blocks] in
theorem MRel.act {Δo : WfCtx L V₁ V₂} {γ : L.Ctx} {o o' : L.Tp} {tmA : Mode V₁ γ o o'}
    {tmB : Mode V₂ γ o o'} (h : MRel Δo tmA tmB) : tmA.act = tmB.act := by
  cases h <;> rfl

omit [L.Blocks] in
private theorem sub_cons {Δ : WfCtx L V₁ V₂} (z : Σ t : L.Tp, V₁ t × V₂ t) :
    ∀ x ∈ Δ, x ∈ z :: Δ := fun _ h => List.mem_cons_of_mem _ h

/-- Corresponding instantiations translate to corresponding outputs. -/
theorem tr_wf {γ : L.Ctx} {o : L.Tp} {Δx : WfCtx L (PVar V₁) (PVar V₂)}
    {eA : Expr L (PVar V₁) γ o} {eB : Expr L (PVar V₂) γ o} (h : Expr.Wf Δx eA eB) :
    ∀ {o' : L.Tp} {n : Nat} {J : List Nat} {Δo : WfCtx L V₁ V₂} {tmA : Mode V₁ γ o o'}
      {tmB : Mode V₂ γ o o'}, Sim n Δx Δo → (∀ l ∈ J, l < n) → MRel Δo tmA tmB →
      (∀ ℓ, tmA.act = some ℓ → ℓ ∈ J) → Expr.Wf Δo (tr n J tmA eA) (tr n J tmB eB) := by
  have hJs : ∀ {n : Nat} {J : List Nat}, (∀ l ∈ J, l < n) → ∀ l ∈ J, l < n + 1 :=
    fun hJ l hl => Nat.lt_succ_of_lt (hJ l hl)
  have hnone : ∀ {J : List Nat} ℓ, (none : Option Nat) = some ℓ → ℓ ∈ J := fun _ h => nomatch h
  induction h with
  | ret hx =>
    intro o' n J Δo tmA tmB hs _ hm _
    cases hm with
    | normal =>
      simp only [tr]
      exact var_wf hs hx fun _ _ _ _ hab => .ret hab
    | jump hκ =>
      simp only [tr]
      exact stuck_wf hκ
  | lit _ ih =>
    intro o' n J Δo tmA tmB hs hJ hm ha
    simp only [tr]
    exact .lit fun x₁ x₂ => ih _ _ (Sim.var hs x₁ x₂) (hJs hJ) (hm.mono (sub_cons _)) ha
  | builtin hargs _ ih =>
    intro o' n J Δo tmA tmB hs hJ hm ha
    simp only [tr]
    exact vars_wf hs hargs (fun _ h => h) fun Δ' as bs hΔ' has =>
      .builtin has fun x₁ x₂ => ih _ _ (Sim.var (Sim.mono hs hΔ') x₁ x₂) (hJs hJ)
        ((hm.mono hΔ').mono (sub_cons _)) ha
  | @lam _ o₀ Δc inp out bA bB kA kB hb hk ihb ihk =>
    intro o' n J Δo tmA tmB hs hJ hm ha
    have hc : CompatCtx (n + 1) J (⟨inp, (.inr n : PVar V₁ inp), (.inr n : PVar V₂ inp)⟩ :: Δc) :=
      CompatCtx.cons (CompatCtx.succ (Sim.compat hs)) (.fresh _)
    have hcJ : CompatCtx (n + 1) (n :: J)
        (⟨.fn inp out, (.inr n : PVar V₁ _), (.inr n : PVar V₂ _)⟩ :: Δc) :=
      CompatCtx.cons (CompatCtx.jp (Sim.compat hs)) (.fresh _)
    have hcong : Expr.Wf Δo
        (.lam (fun x => tr (n + 1) J .normal (bA (.inl x))) fun f => tr (n + 1) J tmA (kA (.inl f)))
        (.lam (fun x => tr (n + 1) J .normal (bB (.inl x))) fun f => tr (n + 1) J tmB (kB (.inl f))) :=
      .lam (fun x₁ x₂ => ihb _ _ (Sim.var hs x₁ x₂) (hJs hJ) .normal hnone)
        fun f₁ f₂ => ihk _ _ (Sim.var hs f₁ f₂) (hJs hJ) (hm.mono (sub_cons _)) ha
    have hbeq := ok_congr (a := tmA.act) (hb (.inr n) (.inr n)) hc (hJs hJ) ha
    have hkeq := ok_congr (a := some n) (hk (.inr n) (.inr n)) hcJ (fun l hl => by
      rcases List.mem_cons.mp hl with rfl | hl
      · omega
      · exact Nat.lt_succ_of_lt (hJ l hl)) (fun _ h => by cases h; exact List.mem_cons_self)
    rw [hm.act] at hbeq
    by_cases hel : out = o₀ ∧ ok (n + 1) J tmA.act (bA (.inr n)) = true ∧
        ok (n + 1) (n :: J) (some n) (kA (.inr n)) = true
    · obtain ⟨rfl, hb', hk'⟩ := hel
      have hb'' : ok (n + 1) J tmB.act (bB (.inr n)) = true := by
        rw [← hbeq, ← hm.act]
        exact hb'
      rw [tr_lam_elim _ _ _ _ _ hb' hk', tr_lam_elim _ _ _ _ _ hb'' (hkeq ▸ hk'), ← tr_jump_eq,
        ← tr_jump_eq]
      exact ihk _ _ (Sim.label hs _) (fun l hl => by
        rcases List.mem_cons.mp hl with rfl | hl
        · omega
        · exact Nat.lt_succ_of_lt (hJ l hl))
        (.jump fun Δ' y₁ y₂ hΔ' hy => ihb _ _ (Sim.var (Sim.mono hs hΔ') y₁ y₂) (hJs hJ)
          ((hm.mono hΔ').mono (sub_cons _)) ha |>.weaken fun z hz => by
            rcases List.mem_cons.mp hz with rfl | hz
            · exact hy
            · exact hz)
        (fun _ h => by cases h; exact List.mem_cons_self)
    · have hel' : ¬(out = o₀ ∧ ok (n + 1) J tmB.act (bB (.inr n)) = true ∧
          ok (n + 1) (n :: J) (some n) (kB (.inr n)) = true) := by
        rintro ⟨h₁, h₂, h₃⟩
        refine hel ⟨h₁, ?_, hkeq ▸ h₃⟩
        rw [hm.act, hbeq]
        exact h₂
      rw [tr_lam_keep _ _ _ _ _ hel, tr_lam_keep _ _ _ _ _ hel']
      exact hcong
  | @app _ _ _ inp out fA fB xA xB kA kB hf hx hk ih =>
    intro o' n J Δo tmA tmB hs hJ hm ha
    have hcong : ∀ {tmA : Mode V₁ _ _ o'} {tmB : Mode V₂ _ _ o'}, MRel Δo tmA tmB →
        (∀ ℓ, tmA.act = some ℓ → ℓ ∈ J) →
        Expr.Wf Δo (var fA fun f => var xA fun x => .app f x fun r => tr (n + 1) J tmA (kA (.inl r)))
          (var fB fun f => var xB fun x => .app f x fun r => tr (n + 1) J tmB (kB (.inl r))) :=
      fun hm ha => var_wf hs hf fun Δ' f₁ f₂ hΔ' hf' =>
        var_wf (Sim.mono hs hΔ') hx fun Δ'' x₁ x₂ hΔ'' hx' =>
          .app (hΔ'' _ hf') hx' fun r₁ r₂ => ih _ _ (Sim.var (Sim.mono hs fun z hz => hΔ'' z (hΔ' z hz)) r₁ r₂)
            (hJs hJ) ((hm.mono fun z hz => hΔ'' z (hΔ' z hz)).mono (sub_cons _)) ha
    cases hm with
    | normal =>
      simp only [tr]
      exact hcong .normal hnone
    | @jump _ τ ℓ κA κB hκ =>
      simp only [tr]
      rw [(Sim.compat (J := [ℓ]) hs hf).isLabel_eq List.mem_cons_self,
        isRet_eq hk (Sim.compat (J := []) hs)]
      split
      · by_cases hinp : inp = τ
        · subst hinp
          rw [dif_pos rfl, dif_pos rfl]
          exact var_wf hs hx hκ
        · rw [dif_neg hinp, dif_neg hinp]
          exact stuck_wf hκ
      · exact hcong (.jump hκ) ha
  | @ite γc _ _ out cA cB tA eA tB eB kA kB hc _ _ hk iht ihe ihk =>
    intro o' n J Δo tmA tmB hs hJ hm ha
    cases hm with
    | normal =>
      simp only [tr]
      exact var_wf hs hc fun Δ' c₁ c₂ hΔ' hc' =>
        .ite hc' (iht (Sim.mono hs hΔ') hJ .normal hnone) (ihe (Sim.mono hs hΔ') hJ .normal hnone)
          fun r₁ r₂ => ihk _ _ (Sim.var (Sim.mono hs hΔ') r₁ r₂) (hJs hJ) .normal hnone
    | @jump _ τ ℓ κA κB hκ =>
      simp only [tr]
      rw [isRet_eq hk (Sim.compat (J := []) hs)]
      split
      · have hret : ∀ {Δ' : WfCtx L V₁ V₂}, MRel Δ' (γ := γc) (o := out)
            (.jump ℓ fun v => (.ret v : Expr L V₁ γc τ))
            (.jump ℓ fun v => (.ret v : Expr L V₂ γc τ)) :=
          fun {_} => .jump fun _ _ _ _ hab => .ret hab
        exact var_wf hs hc fun Δ' c₁ c₂ hΔ' hc' =>
          .ite hc' (iht (Sim.mono hs hΔ') hJ hret ha) (ihe (Sim.mono hs hΔ') hJ hret ha)
            fun r₁ r₂ => hκ _ _ _ (fun z hz => List.mem_cons_of_mem _ (hΔ' z hz)) List.mem_cons_self
      · exact var_wf hs hc fun Δ' c₁ c₂ hΔ' hc' =>
          .ite hc' (iht (Sim.mono hs hΔ') hJ .normal hnone) (ihe (Sim.mono hs hΔ') hJ .normal hnone)
            fun r₁ r₂ => ihk _ _ (Sim.var (Sim.mono hs hΔ') r₁ r₂) (hJs hJ)
              ((MRel.jump hκ).mono fun z hz => List.mem_cons_of_mem _ (hΔ' z hz)) ha
  | loop hi _ _ ihb ihk =>
    intro o' n J Δo tmA tmB hs hJ hm ha
    simp only [tr]
    exact var_wf hs hi fun Δ' i₁ i₂ hΔ' hi' =>
      .loop hi' (fun x₁ x₂ => ihb _ _ (Sim.var (Sim.mono hs hΔ') x₁ x₂) (hJs hJ) .normal hnone)
        fun r₁ r₂ => ihk _ _ (Sim.var (Sim.mono hs hΔ') r₁ r₂) (hJs hJ) ((hm.mono hΔ').mono (sub_cons _)) ha
  | op hi _ _ ihb ihk =>
    intro o' n J Δo tmA tmB hs hJ hm ha
    simp only [tr]
    exact var_wf hs hi fun Δ' i₁ i₂ hΔ' hi' =>
      .op hi' (fun b x₁ x₂ => ihb b _ _ (Sim.var (Sim.mono hs hΔ') x₁ x₂) (hJs hJ) .normal hnone)
        fun r₁ r₂ => ihk _ _ (Sim.var (Sim.mono hs hΔ') r₁ r₂) (hJs hJ) ((hm.mono hΔ').mono (sub_cons _)) ha

theorem trProg_wf {mainCtx : L.Ctx} {iT oT : L.AbiTp} {Δx : WfCtx L (PVar V₁) (PVar V₂)}
    {pA : Program L mainCtx iT oT (PVar V₁)} {pB : Program L mainCtx iT oT (PVar V₂)}
    (h : Program.WfIn Δx pA pB) :
    ∀ {Δo : WfCtx L V₁ V₂}, Sim 0 Δx Δo → Program.WfIn Δo (trProg pA) (trProg pB) := by
  have hnone : ∀ ℓ, (none : Option Nat) = some ℓ → ℓ ∈ ([] : List Nat) := fun _ h => nomatch h
  induction h with
  | define hb _ ih =>
    intro Δo hs
    refine .define (fun f₁ f₂ x₁ x₂ => tr_wf (hb _ _ _ _) ?_ (fun _ h => nomatch h) .normal hnone)
      fun f₁ f₂ => ih _ _ ?_
    · intro t x y hm
      rcases List.mem_cons.mp hm with hm | hm
      · cases hm
        exact .inl ⟨x₁, x₂, rfl, rfl, List.mem_cons_self⟩
      rcases List.mem_cons.mp hm with hm | hm
      · cases hm
        exact .inl ⟨f₁, f₂, rfl, rfl, List.mem_cons_of_mem _ List.mem_cons_self⟩
      rcases hs hm with ⟨a, b, rfl, rfl, hab⟩ | ⟨l, _, _, hl⟩
      · exact .inl ⟨a, b, rfl, rfl, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hab)⟩
      · omega
    · intro t x y hm
      rcases List.mem_cons.mp hm with hm | hm
      · cases hm
        exact .inl ⟨f₁, f₂, rfl, rfl, List.mem_cons_self⟩
      rcases hs hm with ⟨a, b, rfl, rfl, hab⟩ | ⟨l, _, _, hl⟩
      · exact .inl ⟨a, b, rfl, rfl, List.mem_cons_of_mem _ hab⟩
      · omega
  | main hb =>
    intro Δo hs
    refine .main fun x₁ x₂ => tr_wf (hb _ _) ?_ (fun _ h => nomatch h) .normal hnone
    intro t x y hm
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm
      exact .inl ⟨x₁, x₂, rfl, rfl, List.mem_cons_self⟩
    rcases hs hm with ⟨a, b, rfl, rfl, hab⟩ | ⟨l, _, _, hl⟩
    · exact .inl ⟨a, b, rfl, rfl, List.mem_cons_of_mem _ hab⟩
    · omega

end Freigen.Ast.JoinPoints

/-- Join-point elimination keeps programs well-formed. -/
theorem Freigen.Ast.Program.joinPoints_wf {L : Language} [L.Blocks] {γ : L.Ctx}
    {iT oT : L.AbiTp} {p : ∀ {V : L.Tp → Type}, Program L γ iT oT V} (hp : Program.Wf p) :
    Program.Wf (Program.joinPoints p) :=
  fun _ _ => JoinPoints.trProg_wf (hp _ _) JoinPoints.Sim.nil
