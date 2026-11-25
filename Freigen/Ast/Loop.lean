import Freigen.Ast.Cert

/-!
Counted loops: source loops `for h : i in lo...<hi` with a `UInt32` counter,
over a state, and their AST `Expr.forRange`, a closure for the body called
from an `Expr.loop` that advances the counter. Their certificate rules
(`ExprCert.forIn'`) step the AST and the source in lockstep, so they need no
invariant: the body is certified on every counter in the range and every
related state. The source is unfolded one iteration at a time by
`Rco.forIn'_u32_step`.
-/

namespace Freigen.Ast

open Std

/-! ## Source ranges -/

theorem Rco.mem_u32 {lo hi i : UInt32} : i ∈ (lo...<hi) ↔ lo ≤ i ∧ i < hi := Iff.rfl

/-- Below a bound, the successor does not wrap. -/
theorem UInt32.toNat_add_one_of_lt {lo hi : UInt32} (h : lo < hi) :
    (lo + 1).toNat = lo.toNat + 1 := by
  have := UInt32.lt_iff_toNat_lt.mp h
  have := UInt32.toNat_lt hi
  rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt (by omega)]

theorem Rco.toList_u32_cons {lo hi : UInt32} (h : lo < hi) :
    (lo...<hi).toList = lo :: ((lo + 1)...<hi).toList := by
  rw [Rco.toList_eq_if_roo, if_pos h, Roo.toList_eq_match_rco]
  have : PRange.succ? lo = some (lo + 1) := by
    show (if lo + 1 = 0 then none else some (lo + 1)) = _
    rw [if_neg]
    intro h0
    have := congrArg UInt32.toNat h0
    rw [UInt32.toNat_add_one_of_lt h] at this
    simp at this
  simp [this]

theorem Rco.mem_of_mem_succ_u32 {lo hi i : UInt32} (h : lo < hi) (hi' : i ∈ ((lo + 1)...<hi)) :
    i ∈ (lo...<hi) := by
  obtain ⟨h1, h2⟩ := Rco.mem_u32.mp hi'
  refine Rco.mem_u32.mpr ⟨?_, h2⟩
  have := UInt32.le_iff_toNat_le.mp h1
  rw [UInt32.toNat_add_one_of_lt h] at this
  exact UInt32.le_iff_toNat_le.mpr (by omega)

theorem Rco.forIn'_u32_step {m : Type → Type w} [Monad m] [LawfulMonad m] {σ : Type}
    {lo hi : UInt32} (h : lo < hi) {init : σ}
    {f : (i : UInt32) → i ∈ (lo...<hi) → σ → m (ForInStep σ)} :
    forIn' (lo...<hi) init f =
      f lo (Rco.mem_u32.mpr ⟨UInt32.le_refl _, h⟩) init >>= fun
        | .yield b => forIn' ((lo + 1)...<hi) b fun i hi' => f i (Rco.mem_of_mem_succ_u32 h hi')
        | .done b => pure b := by
  simp only [Rco.forIn'_eq_forIn'_toList]
  rw [List.forIn'_congr (Rco.toList_u32_cons h) rfl
    (g := fun a m b => f a (Rco.mem_toList_iff_mem.mp (by rw [Rco.toList_u32_cons h]; exact m)) b)
    (fun _ _ _ => rfl)]
  rw [List.forIn'_cons]
  congr 1
  funext st
  cases st <;> rfl

theorem Rco.forIn'_u32_empty {m : Type → Type w} [Monad m] [LawfulMonad m] {σ : Type}
    {lo hi : UInt32} (h : ¬ lo < hi) {init : σ}
    {f : (i : UInt32) → i ∈ (lo...<hi) → σ → m (ForInStep σ)} :
    forIn' (lo...<hi) init f = pure init := by
  rw [Rco.forIn'_eq_if, dif_neg h]

/-! ## The AST of a counted loop -/

/-- One iteration of a counted loop over `(counter, state)`: call the body
`f`, then advance the counter and keep going while the body asks to and the
counter is below `hi`. The counter never wraps: it is below `hi` whenever
it is incremented. -/
def Expr.forStep {L : Language} {Var : L.Tp → Type} {γ : L.Ctx} {c : L.Tp}
    (hi : Var .uInt32) (f : Var (.fn (.prod .uInt32 c) (.prod c .bool))) :
    Var (.prod .uInt32 c) → Expr L Var γ (.prod (.prod .uInt32 c) .bool) := fun st =>
  .builtin .fst h![st] fun i =>
  .app f st fun r =>
  .builtin .fst h![r] fun x =>
  .builtin .snd h![r] fun go =>
  .lit .uInt32 (1 : UInt32) fun one =>
  .builtin .uAdd h![i, one] fun i' =>
  .builtin .uLt h![i', hi] fun more =>
  .builtin .and h![go, more] fun go' =>
  .builtin .pair h![i', x] fun st' =>
  .builtin .pair h![st', go'] .ret

/-- `for i in lo...<hi` over a state starting at `init`: the body, a closure
over `(i, state)`, returns the next state and whether to continue. An empty
range runs no iteration. -/
def Expr.forRange {L : Language} {Var : L.Tp → Type} {γ : L.Ctx} {c o : L.Tp}
    (lo hi : Var .uInt32) (body : Var .uInt32 → Var c → Expr L Var γ (.prod c .bool))
    (init : Var c) (k : Var c → Expr L Var γ o) : Expr L Var γ o :=
  .lam (inp := .prod .uInt32 c)
    (fun p => .builtin .fst h![p] fun i => .builtin .snd h![p] fun x => body i x) fun f =>
  .builtin .uLt h![lo, hi] fun ne =>
  .ite ne
    (.builtin .pair h![lo, init] fun st =>
      .loop (Expr.forStep hi f) st fun st => .builtin .snd h![st] .ret)
    (.ret init) k

/-- How a loop body's result, the next state and whether to continue,
represents a source step. -/
def StepRel {V σ : Type} (R : V → σ → Prop) : V × Bool → ForInStep σ → Prop
  | p, .yield a => p.2 = true ∧ R p.1 a
  | p, .done a => p.2 = false ∧ R p.1 a

/-! ## Certificate rules -/

variable {L : Language} {M : L.Model} {Γ' : Type c} {F : Γ' → Type u}
  [Eff.Spec.{_, u, 0} F] {spec : Free.SimSpec (L.denote M) F}
  {γ : L.Ctx} {γ' : Γ'} {o : L.Tp} {h : Heap L M} {α : Type}

open CompM (Corr)

namespace ExprCert

variable {R : M.V o → α → Prop}

/-- A branch on a known condition. -/
private theorem ite_const {out : L.Tp} {α' : Type} {Ri : M.V out → α' → Prop} (c : Bool)
    {t e : Expr L M.V γ out} {s : Free F γ' α'}
    (hs : ExprCert spec h (if c then t else e) Ri s)
    {k : M.V out → Expr L M.V γ o} {tk : α' → Free F γ' α}
    (hk : ∀ v a, Ri v a → ExprCert spec h (k v) R (tk a)) :
    ExprCert spec h (.ite c t e k) R (s >>= tk) := by
  intro h' hle β β' S K tK hK
  rw [Expr.denote_ite]
  simp only [bind_assoc]
  refine .tick (hs h' hle _ _ _ fun h'' hle' v a hR => ?_)
  exact hk v a hR h'' (_root_.le_trans hle hle') S K tK (hK.mono hle')

/-- A loop, by one unfolding: the body is certified on the current state, and
on each of its results, the loop's next step (another iteration, or the
continuation) is. -/
theorem loop_unfold {c : L.Tp} {β : Type} {body : M.V c → Expr L M.V γ (.prod c .bool)}
    {init : M.V c} {k : M.V c → Expr L M.V γ o} {Rb : M.V (.prod c .bool) → β → Prop}
    {s : Free F γ' β} (hb : ExprCert spec h (body init) Rb s) {tk : β → Free F γ' α}
    (hk : ∀ v b, Rb v b → ExprCert spec h (cond v.2 (.loop body v.1 k) (k v.1)) R (tk b)) :
    ExprCert spec h (.loop body init k) R (s >>= tk) := by
  intro h' hle β₁ β' g K tK hK
  rw [Expr.denote_loop]
  simp only [bind_assoc]
  refine .tick ?_
  refine hb h' hle g _ _ fun h'' hle' v b hR => ?_
  have := hk v b hR h'' (_root_.le_trans hle hle') g K tK (hK.mono hle')
  cases hv : v.2 <;> simp only [hv, cond_true, cond_false] at this ⊢ <;> exact this

/-- What one iteration from counter `i` returns: the next counter and
whether it is below the bound, or a stop, with the state. -/
private def IterRel {V σ : Type} (R : V → σ → Prop) (i hi : UInt32) :
    (UInt32 × V) × Bool → ForInStep σ → Prop
  | v, .yield a => v.1.1 = i + 1 ∧ v.2 = decide (i + 1 < hi) ∧ R v.1.2 a
  | v, .done a => v.2 = false ∧ R v.1.2 a

theorem Rco.mem_mono_u32 {lo i hi j : UInt32} (hlo : lo ≤ i) (hj : j ∈ (i...<hi)) :
    j ∈ (lo...<hi) :=
  Rco.mem_u32.mpr ⟨UInt32.le_trans hlo (Rco.mem_u32.mp hj).1, (Rco.mem_u32.mp hj).2⟩

/-- The loop from counter `i`, given a function certificate for the body's
closure. -/
private theorem loop_from {c : L.Tp} {σ : Type} {Ri : M.V c → σ → Prop} {lo hi : UInt32}
    {f : (i : UInt32) → i ∈ (lo...<hi) → σ → Free F γ' (ForInStep σ)}
    {r : M.V (.fn (.prod .uInt32 c) (.prod c .bool))}
    (hf : FnCert (γ := γ) spec h r
      (fun (p : M.V (.prod .uInt32 c)) (q : {q : UInt32 × σ // q.1 ∈ (lo...<hi)}) =>
        p.1 = q.1.1 ∧ Ri p.2 q.1.2)
      (fun _ => StepRel Ri) (fun q => f q.1.1 q.2 q.1.2)) :
    ∀ n (i : UInt32), hi.toNat - i.toNat = n → (hlo : lo ≤ i) → i < hi → ∀ x a, Ri x a →
      ExprCert spec h
        (.loop (γ := γ) (Expr.forStep hi r) (i, x) fun st => .builtin .snd h![st] .ret) Ri
        (ForIn'.forIn' (i...<hi) a fun j hj => f j (Rco.mem_mono_u32 hlo hj)) := by
  intro n
  induction n with
  | zero =>
    intro i hn _ hlt
    have := UInt32.lt_iff_toNat_lt.mp hlt
    omega
  | succ n ih =>
    intro i hn hlo hlt x a hR
    rw [Rco.forIn'_u32_step hlt]
    refine loop_unfold (c := .prod .uInt32 c) (Rb := IterRel Ri i hi) ?_ ?_
    · simp only [Expr.forStep]
      refine builtin rfl ?_
      rw [← bind_pure (f i _ a)]
      refine app hf (x := (i, x)) (y := ⟨(i, a), Rco.mem_mono_u32 hlo
        (Rco.mem_u32.mpr ⟨UInt32.le_refl _, hlt⟩)⟩) ⟨rfl, hR⟩ fun v st hst => ?_
      refine builtin rfl (builtin rfl (lit (builtin rfl (builtin rfl (builtin rfl
        (builtin rfl (builtin rfl (ret ?_))))))))
      cases st with
      | yield b =>
        obtain ⟨h1, h2⟩ := hst
        exact ⟨rfl, by simp [h1], h2⟩
      | done b =>
        obtain ⟨h1, h2⟩ := hst
        exact ⟨by simp [h1], h2⟩
    · rintro ⟨⟨i', x'⟩, go⟩ st hst
      cases st with
      | done b =>
        obtain ⟨rfl, h2⟩ := hst
        exact builtin rfl (ret h2)
      | yield b =>
        obtain ⟨rfl, rfl, h2⟩ := hst
        have hsucc := UInt32.toNat_add_one_of_lt hlt
        by_cases hlt' : i + 1 < hi
        · simp only [decide_eq_true hlt', cond_true]
          have hlo' : lo ≤ i + 1 := UInt32.le_iff_toNat_le.mpr (by
            have := UInt32.le_iff_toNat_le.mp hlo; omega)
          exact ih (i + 1) (by omega) hlo' hlt' x' b h2
        · simp only [decide_eq_false hlt', cond_false]
          rw [Rco.forIn'_u32_empty hlt']
          exact builtin rfl (ret h2)

/-- A counted loop `for h : i in lo...<hi` over a state related by `Ri`: the
body is certified on every counter in the range (with its membership) and
related state, its results related by `StepRel Ri`. No invariant: the AST and
the source step in lockstep. -/
theorem forIn' {c : L.Tp} {σ : Type} {Ri : M.V c → σ → Prop} {lo hi : UInt32}
    {body : M.V .uInt32 → M.V c → Expr L M.V γ (.prod c .bool)}
    {f : (i : UInt32) → i ∈ (lo...<hi) → σ → Free F γ' (ForInStep σ)}
    (hb : ∀ (i : M.V .uInt32) (hm : i ∈ (lo...<hi)) x a, Ri x a →
      ExprCert spec h (body i x) (StepRel Ri) (f i hm a))
    {init : M.V c} {a₀ : σ} (hinit : Ri init a₀)
    {k : M.V c → Expr L M.V γ o} {tk : σ → Free F γ' α}
    (hk : ∀ x a, Ri x a → ExprCert spec h (k x) R (tk a)) :
    ExprCert spec h (Expr.forRange lo hi body init k) R (ForIn'.forIn' (lo...<hi) a₀ f >>= tk) := by
  refine lam (αi := {q : UInt32 × σ // q.1 ∈ (lo...<hi)}) (αo := fun _ => ForInStep σ)
    (Ri := fun (p : M.V (.prod .uInt32 c)) q => p.1 = q.1.1 ∧ Ri p.2 q.1.2)
    (Ro := fun _ => StepRel Ri) (src := fun q => f q.1.1 q.2 q.1.2) ?_ ?_
  · rintro ⟨i, x⟩ ⟨⟨i', a⟩, hm⟩ ⟨h1, hR⟩
    cases h1
    exact builtin rfl (builtin rfl (hb i hm x a hR))
  · intro h' r hle hf
    refine builtin (r := decide (lo < hi)) rfl ?_
    by_cases hlt : lo < hi
    · simp only [decide_eq_true hlt]
      refine ite_const (Ri := Ri) true ?_ fun x a hR => (hk x a hR).mono hle
      refine builtin rfl ?_
      have hn := loop_from hf _ lo rfl (UInt32.le_refl _) hlt init a₀ hinit
      exact hn
    · simp only [decide_eq_false hlt]
      rw [Rco.forIn'_u32_empty hlt]
      exact ite_const (Ri := Ri) false (ret hinit) fun x a hR => (hk x a hR).mono hle

theorem forIn'_tail {c : L.Tp} {σ : Type} {lo hi : UInt32} {R : M.V c → σ → Prop}
    {body : M.V .uInt32 → M.V c → Expr L M.V γ (.prod c .bool)}
    {f : (i : UInt32) → i ∈ (lo...<hi) → σ → Free F γ' (ForInStep σ)}
    (hb : ∀ (i : M.V .uInt32) (hm : i ∈ (lo...<hi)) x a, R x a →
      ExprCert spec h (body i x) (StepRel R) (f i hm a))
    {init : M.V c} {a₀ : σ} (hinit : R init a₀) :
    ExprCert spec h (Expr.forRange lo hi body init fun v => .ret v) R
      (ForIn'.forIn' (lo...<hi) a₀ f) := by
  simpa using forIn' (tk := pure) hb hinit fun _ _ hR => ret hR

/-- `for i in lo...<hi`, without the membership: the same loop. -/
theorem forIn {c : L.Tp} {σ : Type} {Ri : M.V c → σ → Prop} {lo hi : UInt32}
    {body : M.V .uInt32 → M.V c → Expr L M.V γ (.prod c .bool)}
    {f : UInt32 → σ → Free F γ' (ForInStep σ)}
    (hb : ∀ (i : M.V .uInt32) (_ : i ∈ (lo...<hi)) x a, Ri x a →
      ExprCert spec h (body i x) (StepRel Ri) (f i a))
    {init : M.V c} {a₀ : σ} (hinit : Ri init a₀)
    {k : M.V c → Expr L M.V γ o} {tk : σ → Free F γ' α}
    (hk : ∀ x a, Ri x a → ExprCert spec h (k x) R (tk a)) :
    ExprCert spec h (Expr.forRange lo hi body init k) R (ForIn.forIn (lo...<hi) a₀ f >>= tk) :=
  forIn' (f := fun i _ a => f i a) hb hinit hk

theorem forIn_tail {c : L.Tp} {σ : Type} {lo hi : UInt32} {R : M.V c → σ → Prop}
    {body : M.V .uInt32 → M.V c → Expr L M.V γ (.prod c .bool)}
    {f : UInt32 → σ → Free F γ' (ForInStep σ)}
    (hb : ∀ (i : M.V .uInt32) (_ : i ∈ (lo...<hi)) x a, R x a →
      ExprCert spec h (body i x) (StepRel R) (f i a))
    {init : M.V c} {a₀ : σ} (hinit : R init a₀) :
    ExprCert spec h (Expr.forRange lo hi body init fun v => .ret v) R
      (ForIn.forIn (lo...<hi) a₀ f) :=
  forIn'_tail (f := fun i _ a => f i a) hb hinit

/-- A loop body asking to continue with the state `x`. -/
theorem yield {c : L.Tp} {σ : Type} {Ri : M.V c → σ → Prop} {x : M.V c} {a : σ}
    (hR : Ri x a) :
    ExprCert spec h (.lit .bool true fun t => .builtin .pair h![x, t] fun p => .ret p :
        Expr L M.V γ (.prod c .bool))
      (StepRel Ri) (pure (ForInStep.yield a) : Free F γ' _) :=
  lit (builtin rfl (ret ⟨rfl, hR⟩))

/-- A loop body stopping with the state `x` (`break`). -/
theorem done {c : L.Tp} {σ : Type} {Ri : M.V c → σ → Prop} {x : M.V c} {a : σ}
    (hR : Ri x a) :
    ExprCert spec h (.lit .bool false fun t => .builtin .pair h![x, t] fun p => .ret p :
        Expr L M.V γ (.prod c .bool))
      (StepRel Ri) (pure (ForInStep.done a) : Free F γ' _) :=
  lit (builtin rfl (ret ⟨rfl, hR⟩))

end ExprCert
