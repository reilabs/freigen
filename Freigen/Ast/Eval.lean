import Freigen.Ast.Heap
import Freigen.CompM.MayReturn

/-!
Structural facts about the evaluator: evaluation decomposes along the
continuation stack, every expression form has an unfolding equation, and the
heap only grows. Certificate rules are proved from these facts alone and never
unfold the corecursor.
-/

namespace Freigen.Ast

open CompM (tick fail)

variable {eff : EffSig} {γ : eff.Ctx} {R S : Type}

namespace EvalState

private def bindAux {i : eff.Ctx × Type} :
    EvalState eff i → (i.2 → EvalState eff (i.1, S)) → EvalState eff (i.1, S)
  | .done r, f => f r
  | .cont s e k, f => .cont s e fun s' v => bindAux (k s' v) f

/-- Append a continuation to a machine state. -/
def bind (st : EvalState eff (γ, R)) (f : R → EvalState eff (γ, S)) :
    EvalState eff (γ, S) :=
  bindAux st f

/-- The computation a machine state evaluates to. -/
def run (st : EvalState eff (γ, R)) : EvalM eff γ R :=
  CompM.corec Expr.denoteCo st

private theorem observe_run (st : EvalState eff (γ, R)) :
    CompM.observe st.run =
      IxPoly.map (fun _ y => CompM.corec Expr.denoteCo y) (γ, R)
        (Expr.denoteCo _ st) :=
  CompM.observe_corec (i := (γ, R)) _ _

/-! ## Single steps -/

private theorem run_eq_tau {st st' : EvalState eff (γ, R)}
    (h : Expr.denoteCo _ st = Eff.Step.tau st') :
    st.run = tick >>= fun _ => st'.run := by
  apply CompM.eq_of_observe_eq
  rw [observe_run, h, Eff.Step.map_tau, CompM.observe_tick_bind]
  rfl

private theorem run_eq_fail {st : EvalState eff (γ, R)}
    (h : Expr.denoteCo _ st = Eff.Step.fail) :
    st.run = fail := by
  apply CompM.eq_of_observe_eq
  rw [observe_run, h, CompM.observe_fail]
  simp only [Eff.Step.fail, Eff.Step.map_hasOp]
  congr 1
  · funext t
    exact nomatch t
  · funext o
    exact nomatch o

@[simp]
theorem run_done (r : R) : (done r : EvalState eff (γ, R)).run = pure r := by
  apply CompM.eq_of_observe_eq
  rw [observe_run, CompM.observe_pure]
  exact Eff.Step.map_ret

variable (s : Heap eff)

theorem run_ret {i : Tp} (v : Tp.denote i)
    (K : Heap eff → Tp.denote i → EvalState eff (γ, R)) :
    (cont s (.ret v) K).run = tick >>= fun _ => (K s v).run :=
  run_eq_tau rfl

theorem run_lit {o : Tp} (tp : AbiTp) (v : tp.val.denote)
    (k : Tp.denote tp.val → Expr eff Tp.denote γ o)
    (K : Heap eff → Tp.denote o → EvalState eff (γ, R)) :
    (cont s (.lit tp v k) K).run = tick >>= fun _ => (cont s (k v) K).run :=
  run_eq_tau rfl

theorem run_builtin {inp : List Tp} {out o : Tp} {b : Builtin inp out}
    {args : HList Tp.denote inp} {r : Tp.denote out}
    (h : b.denote args = some r)
    (k : Tp.denote out → Expr eff Tp.denote γ o)
    (K : Heap eff → Tp.denote o → EvalState eff (γ, R)) :
    (cont s (.builtin b args k) K).run =
      tick >>= fun _ => (cont s (k r) K).run :=
  run_eq_tau (by simp only [Expr.denoteCo, h])

theorem run_builtin_none {inp : List Tp} {out o : Tp} {b : Builtin inp out}
    {args : HList Tp.denote inp}
    (h : b.denote args = none)
    (k : Tp.denote out → Expr eff Tp.denote γ o)
    (K : Heap eff → Tp.denote o → EvalState eff (γ, R)) :
    (cont s (.builtin b args k) K).run = fail :=
  run_eq_fail (by simp only [Expr.denoteCo, h])

theorem run_lam {inp out o : Tp}
    (b : Tp.denote inp → Expr eff Tp.denote γ out)
    (k : Tp.denote (.fn inp out) → Expr eff Tp.denote γ o)
    (K : Heap eff → Tp.denote o → EvalState eff (γ, R)) :
    (cont s (.lam b k) K).run =
      tick >>= fun _ =>
        (cont (s.alloc fun _ x => b x).1 (k (s.alloc fun _ x => b x).2) K).run :=
  run_eq_tau rfl

theorem run_app {inp out o : Tp} {f : Tp.denote (.fn inp out)}
    {g : Tp.denote inp → Expr eff Tp.denote γ out}
    (h : s.lookup f = some g) (x : Tp.denote inp)
    (k : Tp.denote out → Expr eff Tp.denote γ o)
    (K : Heap eff → Tp.denote o → EvalState eff (γ, R)) :
    (cont s (.app f x k) K).run =
      tick >>= fun _ => (cont s (g x) fun s' r => cont s' (k r) K).run :=
  run_eq_tau (by simp only [Expr.denoteCo, h])

theorem run_app_none {inp out o : Tp} {f : Tp.denote (.fn inp out)}
    (h : s.lookup (γ := γ) f = none) (x : Tp.denote inp)
    (k : Tp.denote out → Expr eff Tp.denote γ o)
    (K : Heap eff → Tp.denote o → EvalState eff (γ, R)) :
    (cont s (.app f x k) K).run = fail :=
  run_eq_fail (by simp only [Expr.denoteCo, h])

theorem run_ite {out o : Tp} (c : Bool) (t e : Expr eff Tp.denote γ out)
    (k : Tp.denote out → Expr eff Tp.denote γ o)
    (K : Heap eff → Tp.denote o → EvalState eff (γ, R)) :
    (cont s (.ite c t e k) K).run =
      tick >>= fun _ =>
        (cont s (if c then t else e) fun s' r => cont s' (k r) K).run :=
  run_eq_tau rfl

theorem run_loop {c o : Tp}
    (body : Tp.denote c → Expr eff Tp.denote γ (.prod c .bool))
    (init : Tp.denote c) (k : Tp.denote c → Expr eff Tp.denote γ o)
    (K : Heap eff → Tp.denote o → EvalState eff (γ, R)) :
    (cont s (.loop body init k) K).run =
      tick >>= fun _ =>
        (cont s (body init) fun s' r =>
          bif r.2 then cont s' (.loop body r.1 k) K
          else cont s' (k r.1) K).run := by
  refine run_eq_tau ?_
  simp only [Expr.denoteCo]
  congr 2
  funext s' r
  rcases r with ⟨next, _ | _⟩ <;> rfl

theorem run_op {o : Tp} (e : eff.tag γ) (inp : Tp.denote (eff.input γ e).val)
    (blocks :
      (b : eff.blockTag γ e) →
      Tp.denote (eff.blockInputs γ e b).val →
      Expr eff Tp.denote (eff.blockCtx γ e b) (eff.blockOutputs γ e b).val)
    (k : Tp.denote (eff.output γ e).val → Expr eff Tp.denote γ o)
    (K : Heap eff → Tp.denote o → EvalState eff (γ, R)) :
    (cont s (.op e inp blocks k) K).run =
      CompM.op (E := EvalEff eff) (.inr (.inr (Sigma.mk e inp : eff.denote γ)))
          (fun t x => (cont s (blocks t x) fun _ r => done r).run) >>=
        fun o => (cont s (k o) K).run := by
  apply CompM.eq_of_observe_eq
  rw [observe_run, CompM.observe_op_bind]
  exact Eff.Step.map_op

/-! ## Decomposition -/

/-- Running a state under an appended continuation is running the state, then
the continuation. -/
private def BindRel {γ : eff.Ctx} {α : Type} (x y : EvalM eff γ α) : Prop :=
  ∃ (R : Type) (st : EvalState eff (γ, R)) (f : R → EvalState eff (γ, α)),
    x = (st.bind f).run ∧ y = st.run >>= fun r => (f r).run

theorem run_bind (st : EvalState eff (γ, R)) (f : R → EvalState eff (γ, S)) :
    (st.bind f).run = st.run >>= fun r => (f r).run := by
  refine CompM.coind (R := BindRel) ?_ ⟨R, st, f, rfl, rfl⟩
  rintro γ α _ _ ⟨R, st, f, rfl, rfl⟩
  -- A silent step on both sides, continuing with related states.
  have tau : ∀ (st' : EvalState eff (γ, R)) (x : EvalM eff γ α)
      (y : EvalM eff γ R),
      x = (tick >>= fun _ => (st'.bind f).run) →
      y = (tick >>= fun _ => st'.run) →
      CompM.CoindStep BindRel x (y >>= fun r => (f r).run) := by
    rintro st' _ _ rfl rfl
    refine .inr ⟨_, CompM.tauBlocks, CompM.tauBlocks, fun _ => (st'.bind f).run,
      fun _ => st'.run >>= fun r => (f r).run, ?_, ?_, fun _ _ => .inl rfl,
      fun _ => .inr ⟨R, st', f, rfl, rfl⟩⟩
    · exact CompM.tick_bind _ _
    · rw [bind_assoc]
      exact CompM.tick_bind _ _
  have failing : ∀ (x : EvalM eff γ α) (y : EvalM eff γ R),
      x = fail → y = fail →
      CompM.CoindStep BindRel x (y >>= fun r => (f r).run) := by
    rintro _ _ rfl rfl
    exact .inl (CompM.fail_bind _).symm
  cases st with
  | done r =>
    left
    rw [run_done, pure_bind]
    rfl
  | cont s e K =>
    change CompM.CoindStep BindRel (cont s e fun s' v => (K s' v).bind f).run _
    cases e with
    | ret v => exact tau (K s v) _ _ (run_ret ..) (run_ret ..)
    | lit tp v k => exact tau (cont s (k v) K) _ _ (run_lit ..) (run_lit ..)
    | builtin b args k =>
      rcases h : b.denote args with _ | r
      · exact failing _ _ (run_builtin_none _ h ..) (run_builtin_none _ h ..)
      · exact tau (cont s (k r) K) _ _ (run_builtin _ h ..) (run_builtin _ h ..)
    | lam b k => exact tau (cont _ (k _) K) _ _ (run_lam ..) (run_lam ..)
    | app g x k =>
      rcases h : s.lookup g with _ | g
      · exact failing _ _ (run_app_none _ h ..) (run_app_none _ h ..)
      · exact tau (cont s (g x) fun s' r => cont s' (k r) K) _ _
          (run_app _ h ..) (run_app _ h ..)
    | ite c t e k =>
      exact tau (cont s (if c then t else e) fun s' r => cont s' (k r) K) _ _
        (run_ite ..) (run_ite ..)
    | loop body init k =>
      refine tau (cont s (body init) fun s' r =>
          bif r.2 then cont s' (.loop body r.1 k) K
          else cont s' (k r.1) K) _ _ ?_ (run_loop ..)
      rw [run_loop]
      congr 2
      funext _
      congr 1
      show cont _ _ _ = cont _ _ _
      congr 1
      funext s' r
      rcases r with ⟨next, _ | _⟩ <;> rfl
    | op e inp blocks k =>
      rw [run_op, run_op, bind_assoc]
      exact .inr ⟨_, _, _, _, _, rfl, rfl, fun _ _ => .inl rfl,
        fun o => .inr ⟨R, cont s (k o) K, f, rfl, rfl⟩⟩

/-! ## Heap growth -/

private def growsAux {i : eff.Ctx × Type} (Q : i.2 → Prop) :
    EvalState eff i → Prop
  | .done r => Q r
  | .cont s _ k => ∀ s' v, s ≤ s' → growsAux Q (k s' v)

/-- Every final value reachable from the state, from any heap extending the
current one, satisfies `Q`. -/
def Grows (Q : R → Prop) (st : EvalState eff (γ, R)) : Prop :=
  growsAux Q st

/-- Everything a state may return satisfies the invariant it grows. -/
theorem Grows.mayReturn {Q : R → Prop} {st : EvalState eff (γ, R)}
    (hst : st.Grows Q) {r : R} (h : st.run.MayReturn r) : Q r := by
  refine CompM.mayReturn_corec (f := Expr.denoteCo) (Grows Q) Q ?_ hst h
  intro st hst
  have failing : CompM.StepInv (Grows Q) Q
      (Eff.Step.fail : Eff.Step eff.Ctx (EvalEff eff) (EvalState eff) (γ, R)) :=
    fun o => nomatch Eff.Step.Has.lowerOutput (F := Eff.Fail) (E := EvalEff eff) o
  cases st with
  | done r => exact hst
  | cont s e K =>
    cases e with
    | ret v => exact fun _ => hst s v le_rfl
    | lit tp v k => exact fun _ => hst
    | builtin b args k =>
      simp only [Expr.denoteCo]
      split
      · exact fun _ => hst
      · exact failing
    | lam b k =>
      have hco : Expr.denoteCo _ (cont s (.lam b k) K) =
          Eff.Step.tau (cont (s.alloc fun _ x => b x).1
            (k (s.alloc fun _ x => b x).2) K) :=
        rfl
      rw [hco]
      intro _ s' v hs'
      exact hst s' v (le_trans (Heap.le_alloc s fun _ x => b x) hs')
    | app g x k =>
      simp only [Expr.denoteCo]
      split
      · exact failing
      · intro _ s' _ hs' s'' v hs''
        exact hst s'' v (le_trans hs' hs'')
    | ite c t e k =>
      intro _ s' _ hs' s'' v hs''
      exact hst s'' v (le_trans hs' hs'')
    | loop body init k =>
      intro _ s' r hs'
      rcases r with ⟨next, _ | _⟩ <;>
        exact fun s'' v hs'' => hst s'' v (le_trans hs' hs'')
    | op e inp blocks k => exact fun _ => hst

end EvalState

open EvalState

/-! ## Unfolding equations -/

namespace Expr

variable {o : Tp} (s : Heap eff)

private theorem denote_eq (e : Expr eff Tp.denote γ o) :
    e.denote s = (cont s e fun s r => done (s, r)).run :=
  rfl

/-- Evaluation under a pending continuation. -/
private theorem run_cont {i : Tp} (e : Expr eff Tp.denote γ i)
    (K : Heap eff → Tp.denote i → EvalState eff (γ, R)) :
    (cont s e K).run = e.denote s >>= fun p => (K p.1 p.2).run :=
  run_bind (cont s e fun s r => done (s, r)) fun p => K p.1 p.2

theorem denote_ret (v : Tp.denote o) :
    (Expr.ret v : Expr eff Tp.denote γ o).denote s =
      tick >>= fun _ => pure (s, v) := by
  rw [denote_eq, run_ret, run_done]

theorem denote_lit (tp : AbiTp) (v : tp.val.denote)
    (k : Tp.denote tp.val → Expr eff Tp.denote γ o) :
    (Expr.lit tp v k).denote s = tick >>= fun _ => (k v).denote s :=
  run_lit ..

theorem denote_builtin {inp : List Tp} {out : Tp} {b : Builtin inp out}
    {args : HList Tp.denote inp} {r : Tp.denote out}
    (h : b.denote args = some r)
    (k : Tp.denote out → Expr eff Tp.denote γ o) :
    (Expr.builtin b args k).denote s = tick >>= fun _ => (k r).denote s :=
  run_builtin _ h ..

theorem denote_builtin_none {inp : List Tp} {out : Tp} {b : Builtin inp out}
    {args : HList Tp.denote inp} (h : b.denote args = none)
    (k : Tp.denote out → Expr eff Tp.denote γ o) :
    (Expr.builtin b args k).denote s = fail :=
  run_builtin_none _ h ..

/-- Builtins in one equation, for rewriting when the result is computable. -/
theorem denote_builtin_eq {inp : List Tp} {out : Tp} (b : Builtin inp out)
    (args : HList Tp.denote inp) (k : Tp.denote out → Expr eff Tp.denote γ o) :
    (Expr.builtin b args k).denote s =
      match b.denote args with
      | some r => tick >>= fun _ => (k r).denote s
      | none => fail := by
  rcases h : b.denote args with _ | r
  · exact denote_builtin_none _ h k
  · exact denote_builtin _ h k

theorem denote_lam {inp out : Tp}
    (b : Tp.denote inp → Expr eff Tp.denote γ out)
    (k : Tp.denote (.fn inp out) → Expr eff Tp.denote γ o) :
    (Expr.lam b k).denote s =
      tick >>= fun _ =>
        (k (s.alloc fun _ x => b x).2).denote (s.alloc fun _ x => b x).1 :=
  run_lam ..

theorem denote_app {inp out : Tp} {f : Tp.denote (.fn inp out)}
    {g : Tp.denote inp → Expr eff Tp.denote γ out}
    (h : s.lookup f = some g) (x : Tp.denote inp)
    (k : Tp.denote out → Expr eff Tp.denote γ o) :
    (Expr.app f x k).denote s =
      tick >>= fun _ => (g x).denote s >>= fun p => (k p.2).denote p.1 := by
  rw [denote_eq, run_app _ h, run_cont]
  rfl

theorem denote_app_none {inp out : Tp} {f : Tp.denote (.fn inp out)}
    (h : s.lookup (γ := γ) f = none) (x : Tp.denote inp)
    (k : Tp.denote out → Expr eff Tp.denote γ o) :
    (Expr.app f x k).denote s = fail :=
  run_app_none _ h ..

/-- Calls in one equation, for rewriting when the lookup is computable. -/
theorem denote_app_eq {inp out : Tp} (f : Tp.denote (.fn inp out))
    (x : Tp.denote inp) (k : Tp.denote out → Expr eff Tp.denote γ o) :
    (Expr.app f x k).denote s =
      match s.lookup f with
      | some g => tick >>= fun _ => (g x).denote s >>= fun p => (k p.2).denote p.1
      | none => fail := by
  rcases h : s.lookup (γ := γ) f with _ | g
  · exact denote_app_none _ h x k
  · exact denote_app _ h x k

theorem denote_ite {out : Tp} (c : Bool) (t e : Expr eff Tp.denote γ out)
    (k : Tp.denote out → Expr eff Tp.denote γ o) :
    (Expr.ite c t e k).denote s =
      tick >>= fun _ =>
        (if c then t else e).denote s >>= fun p => (k p.2).denote p.1 := by
  rw [denote_eq, run_ite, run_cont]
  rfl

theorem denote_loop {c : Tp}
    (body : Tp.denote c → Expr eff Tp.denote γ (.prod c .bool))
    (init : Tp.denote c) (k : Tp.denote c → Expr eff Tp.denote γ o) :
    (Expr.loop body init k).denote s =
      tick >>= fun _ =>
        (body init).denote s >>= fun p =>
          bif p.2.2 then (Expr.loop body p.2.1 k).denote p.1
          else (k p.2.1).denote p.1 := by
  rw [denote_eq, run_loop, run_cont]
  congr 2
  funext _
  congr 1
  funext p
  cases p.2.2 <;> rfl

/-- Effects are forwarded. Blocks are independent evaluations from the current
heap, whose final heap is dropped. -/
theorem denote_op (e : eff.tag γ) (inp : Tp.denote (eff.input γ e).val)
    (blocks :
      (b : eff.blockTag γ e) →
      Tp.denote (eff.blockInputs γ e b).val →
      Expr eff Tp.denote (eff.blockCtx γ e b) (eff.blockOutputs γ e b).val)
    (k : Tp.denote (eff.output γ e).val → Expr eff Tp.denote γ o) :
    (Expr.op e inp blocks k).denote s =
      CompM.op (E := EvalEff eff) (.inr (.inr (Sigma.mk e inp : eff.denote γ)))
          (fun t x => Prod.snd <$> (blocks t x).denote s) >>=
        fun o => (k o).denote s := by
  rw [denote_eq, run_op]
  congr 2
  funext t x
  rw [run_cont]
  simp only [run_done, bind_pure_comp]
  rfl

/-- The heap only grows: every final heap an evaluation may end in extends
the initial one. -/
theorem le_of_mayReturn {e : Expr eff Tp.denote γ o} {s' : Heap eff}
    {v : Tp.denote o} (h : (e.denote s).MayReturn (s', v)) : s ≤ s' :=
  Grows.mayReturn (R := Heap eff × Tp.denote o) (Q := fun p => s ≤ p.1)
    (st := cont s e fun s r => done (s, r)) (fun _ _ hs => hs) h

end Expr

/-! ## Programs -/

namespace Program

variable {mainCtx : eff.Ctx} {iT oT : AbiTp}

/-- Defining a function allocates its closure, which refers to its own
reference, and continues in the extended heap. -/
theorem denote'_go_define {inp out : Tp} (s : Heap eff)
    (body : Tp.denote (.fn inp out) → Tp.denote inp → Expr eff Tp.denote γ out)
    (k : Tp.denote (.fn inp out) → Program eff mainCtx iT oT Tp.denote)
    (x : iT.val.denote) :
    denote'.go x s (.define body k) =
      denote'.go x (s.alloc fun f x => body f x).1
        (k (s.alloc fun f x => body f x).2) :=
  rfl

theorem denote'_go_main (s : Heap eff)
    (body : Tp.denote iT.val → Expr eff Tp.denote mainCtx oT.val)
    (x : iT.val.denote) :
    denote'.go x s (.main body) = (body x).denote s :=
  rfl

theorem denote_eq (p : Program eff mainCtx iT oT Tp.denote) (x : iT.val.denote) :
    p.denote x = Prod.snd <$> denote'.go x (Heap.empty eff) p :=
  rfl

/-- A defined function's reference resolves to its body, closed over the
reference itself. -/
theorem lookup_define {inp out : Tp} (s : Heap eff)
    (body : Tp.denote (.fn inp out) → Tp.denote inp → Expr eff Tp.denote γ out) :
    (s.alloc fun f x => body f x).1.lookup (s.alloc fun f x => body f x).2 =
      some (body (s.alloc fun f x => body f x).2) :=
  Heap.lookup_alloc ..

end Program

end Freigen.Ast
