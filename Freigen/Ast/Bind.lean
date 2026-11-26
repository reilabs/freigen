import Freigen.Ast.Eval
import Freigen.CompM.Eutt

/-!
Sequencing expressions: `e.bind k` runs `e`, then `k` on its value. The AST is
in continuation-passing style, so `bind` replaces the returns at the end of
`e`'s continuation chain by `k`. It does not enter branches, loop bodies,
closures or blocks, which return into continuations of their own, so `k`
appears once. Evaluating `e.bind k` is evaluating `e` and then `k`, up to the
silent step of the return it replaces (`Expr.denote_bind`).
-/

namespace Freigen.Ast

variable {L : Language} {V : L.Tp → Type} {γ : L.Ctx}

/-- `e`, followed by `k` on its value. -/
def Expr.bind {a b : L.Tp} : Expr L V γ a → (V a → Expr L V γ b) → Expr L V γ b
  | .ret v, k => k v
  | .lit tp v k', k => .lit tp v fun x => (k' x).bind k
  | .builtin bi args k', k => .builtin bi args fun x => (k' x).bind k
  | .lam f k', k => .lam f fun x => (k' x).bind k
  | .app f x k', k => .app f x fun r => (k' r).bind k
  | .ite c t e k', k => .ite c t e fun r => (k' r).bind k
  | .loop body i k', k => .loop body i fun r => (k' r).bind k
  | .op e i bl k', k => .op e i bl fun r => (k' r).bind k

theorem Expr.bind_assoc {a b c : L.Tp} (e : Expr L V γ a) (f : V a → Expr L V γ b)
    (g : V b → Expr L V γ c) : (e.bind f).bind g = e.bind fun y => (f y).bind g := by
  induction e with
  | ret v => rfl
  | lit tp v k ih => simp only [Expr.bind, ih]
  | builtin bi args k ih => simp only [Expr.bind, ih]
  | lam f' k ihb ih => simp only [Expr.bind, ih]
  | app f' x k ih => simp only [Expr.bind, ih]
  | ite c t e k iht ihe ih => simp only [Expr.bind, ih]
  | loop body i k ihb ih => simp only [Expr.bind, ih]
  | op e i bl k ihb ih => simp only [Expr.bind, ih]

/-! ## The semantic law -/

namespace BindSim

open CompM EvalState

variable {M : L.Model}

/-- States that evaluate alike: the same expression under alike
continuations, or a `bind` against its parts. -/
inductive BR : {i : L.Ctx × Type} → EvalState L M i → EvalState L M i → Prop
| done {γ : L.Ctx} {R : Type} (r : R) : BR (.done (γ := γ) r) (.done r)
| same {γ : L.Ctx} {R : Type} {t : L.Tp} {s : Heap L M} {e : Expr L M.V γ t}
    {K₁ K₂ : Heap L M → M.V t → EvalState L M (γ, R)} :
    (∀ s v, BR (K₁ s v) (K₂ s v)) → BR (.cont s e K₁) (.cont s e K₂)
| bind {γ : L.Ctx} {R : Type} {a b : L.Tp} {s : Heap L M} {e : Expr L M.V γ a}
    {k : M.V a → Expr L M.V γ b} {K₁ K₂ : Heap L M → M.V b → EvalState L M (γ, R)} :
    (∀ s v, BR (K₁ s v) (K₂ s v)) →
    BR (.cont s (e.bind k) K₁) (.cont s e fun s v => .cont s (k v) K₂)

/-- The computations of alike states. -/
def Rb {γ : L.Ctx} {α : Type} (x y : EvalM L M γ α) : Prop :=
  ∃ st₁ st₂ : EvalState L M (γ, α), BR st₁ st₂ ∧ x = st₁.run ∧ y = st₂.run

theorem Rb.of {γ : L.Ctx} {α : Type} {st₁ st₂ : EvalState L M (γ, α)} (h : BR st₁ st₂) :
    Rb st₁.run st₂.run :=
  ⟨st₁, st₂, h, rfl, rfl⟩

private theorem sync {γ : L.Ctx} {α : Type} {x y : EvalM L M γ α} (h : Rb x y) :
    EuttF Rb (tick >>= fun _ => x) (tick >>= fun _ => y) := by
  rw [tick_bind _ tauBlocks, tick_bind _ tauBlocks]
  exact .op _ (fun t => nomatch Eff.Step.Has.lowerBlockTag (F := Eff.Tau) (E := EvalEff L M) t)
    fun _ => h

private theorem sync_fail {γ : L.Ctx} {α : Type} : EuttF Rb (fail : EvalM L M γ α) fail := by
  rw [fail_eq failBlocks failCont]
  exact .op _ (fun t => nomatch Eff.Step.Has.lowerBlockTag (F := Eff.Fail) (E := EvalEff L M) t)
    fun o => nomatch Eff.Step.Has.lowerOutput (F := Eff.Fail) (E := EvalEff L M) o

private theorem done_cont {γ : L.Ctx} {t : L.Tp} :
    ∀ (_ : Heap L M) (v : M.V t), BR (.done (L := L) (M := M) (γ := γ) v) (.done v) :=
  fun _ v => .done v

/-- The same expression under alike continuations: both take one step. -/
private theorem step_same {γ : L.Ctx} {R : Type} {t : L.Tp} (s : Heap L M) (e : Expr L M.V γ t)
    {K₁ K₂ : Heap L M → M.V t → EvalState L M (γ, R)} (hK : ∀ s v, BR (K₁ s v) (K₂ s v)) :
    EuttF Rb (EvalState.cont s e K₁).run (EvalState.cont s e K₂).run := by
  cases e with
  | ret v =>
    rw [run_ret, run_ret]
    exact sync (.of (hK s v))
  | lit tp v k =>
    rw [run_lit, run_lit]
    exact sync (.of (.same hK))
  | builtin b args k =>
    rcases h : b.denote M args with _ | r
    · rw [run_builtin_none _ h, run_builtin_none _ h]
      exact sync_fail
    · rw [run_builtin _ h, run_builtin _ h]
      exact sync (.of (.same hK))
  | lam f k =>
    rw [run_lam, run_lam]
    exact sync (.of (.same hK))
  | app f x k =>
    rcases h : s.lookup (γ := γ) f with _ | g
    · rw [run_app_none _ h, run_app_none _ h]
      exact sync_fail
    · rw [run_app _ h, run_app _ h]
      exact sync (.of (.same fun _ _ => .same hK))
  | ite c t e k =>
    rw [run_ite, run_ite]
    exact sync (.of (.same fun _ _ => .same hK))
  | loop body i k =>
    rw [run_loop, run_loop]
    refine sync (.of (.same fun s' r => ?_))
    cases r.2
    · exact .same hK
    · exact .same hK
  | op e i bl k =>
    rw [run_op, run_op]
    exact .op _ (fun _ _ => .of (.same done_cont)) fun _ => .of (.same hK)

theorem step {i : L.Ctx × Type} {st₁ st₂ : EvalState L M i} (h : BR st₁ st₂) :
    EuttF Rb st₁.run st₂.run := by
  cases h with
  | done r =>
    simp only [run_done]
    exact .pure r
  | same hK => exact step_same _ _ hK
  | @bind _ _ _ _ s e k K₁ K₂ hK =>
    cases e with
    | ret v =>
      rw [run_ret]
      exact .tauR (step_same s (k v) hK)
    | lit tp v k' =>
      rw [Expr.bind, run_lit, run_lit]
      exact sync (.of (.bind hK))
    | builtin b args k' =>
      rcases h : b.denote M args with _ | r
      · rw [Expr.bind, run_builtin_none _ h, run_builtin_none _ h]
        exact sync_fail
      · rw [Expr.bind, run_builtin _ h, run_builtin _ h]
        exact sync (.of (.bind hK))
    | lam f k' =>
      rw [Expr.bind, run_lam, run_lam]
      exact sync (.of (.bind hK))
    | app f x k' =>
      rcases h : s.lookup (γ := _) f with _ | g
      · rw [Expr.bind, run_app_none _ h, run_app_none _ h]
        exact sync_fail
      · rw [Expr.bind, run_app _ h, run_app _ h]
        exact sync (.of (.same fun _ _ => .bind hK))
    | ite c t e k' =>
      rw [Expr.bind, run_ite, run_ite]
      exact sync (.of (.same fun _ _ => .bind hK))
    | loop body i k' =>
      rw [Expr.bind, run_loop, run_loop]
      refine sync (.of (.same fun s' r => ?_))
      cases r.2
      · exact .bind hK
      · exact .bind (e := .loop body r.1 k') hK
    | op e i bl k' =>
      rw [Expr.bind, run_op, run_op]
      exact .op _ (fun _ _ => .of (.same done_cont)) fun _ => .of (.bind hK)

end BindSim

open BindSim in
/-- Evaluating `e.bind k` is evaluating `e`, then `k` on its value, from the
heap `e` leaves. -/
theorem Expr.denote_bind {M : L.Model} {a b : L.Tp} (e : Expr L M.V γ a)
    (k : M.V a → Expr L M.V γ b) (s : Heap L M) :
    CompM.Eutt ((e.bind k).denote s) (e.denote s >>= fun p => (k p.2).denote p.1) := by
  have h := Expr.run_cont s e fun s v => EvalState.cont s (k v) fun s r => .done (s, r)
  rw [show (e.denote s >>= fun p => (k p.2).denote p.1) = _ from h.symm]
  exact CompM.Eutt.coind Rb (fun ⟨_, _, h, hx, hy⟩ => hx ▸ hy ▸ step h)
    (.of (.bind fun _ v => .done (_, v)))

end Freigen.Ast
