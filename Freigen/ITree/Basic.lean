import Mathlib.Data.PFunctor.Univariate.M
import Freigen.Free

/-!
# Interaction trees: a coinductive denotation domain with effects, divergence, and failure

`Comp Op α` is a Lean realisation of **interaction trees** (Xia et al.) over the effect signature
`Effect Op`, built as the final coalgebra (`PFunctor.M`) of the one-step functor

```
Pos := ret α | tau | fail | vis (e : Effect Op x)     -- positions
Ar  := ret ↦ ∅ | tau ↦ Unit | fail ↦ ∅ | vis e ↦ x   -- arities (children)
```

so a computation is a (possibly infinite) tree whose leaves are `ret a` / `fail`, with internal
`tau` (a silent step — the guard that makes recursion productive) and `vis e k` (perform effect
`e`, branch on its result).  This is the domain in which **recursion** denotes: `Comp.iter`/`fix`
is a *guarded corecursion*, total without any termination proof, and divergence is an infinite
chain of `tau`s.

Universes: `Effect Op x : Type 1`, so positions live in `Type 1`; arities (`x : Type`) live in
`Type 0`.  `PFunctor.{1,0}` accommodates exactly this, and `Comp Op α : Type 1` — matching
`Free (Effect Op) α`.

This file builds the core: the type, constructors and their `dest` laws, `bind` (corecursive) with
its computation laws, and the guarded fixpoint `iter`/`fix`.  Weak bisimulation, convergence, and
soundness build on top (subsequent sections / files).
-/

namespace Freigen
namespace ITree

universe u

variable {Op : Type → Type → Type 1}

/-! ## The one-step functor -/

/-- One-step *positions* of an interaction tree. -/
inductive Pos (Op : Type → Type → Type 1) (α : Type) : Type 1
  | ret  : α → Pos Op α
  | tau  : Pos Op α
  | fail : Pos Op α
  | vis  : {x : Type} → Effect Op x → Pos Op α

/-- Arity (set of children) of each position. -/
@[reducible] def Ar {Op α} : Pos Op α → Type
  | .ret _        => PEmpty
  | .tau          => PUnit
  | .fail         => PEmpty
  | .vis (x := x) _ => x

/-- The polynomial one-step functor of interaction trees. -/
@[reducible] def P (Op : Type → Type → Type 1) (α : Type) : PFunctor.{1, 0} := ⟨Pos Op α, Ar⟩

/-- Interaction trees over `Effect Op` returning `α`: the final coalgebra of `P`. -/
def Comp (Op : Type → Type → Type 1) (α : Type) : Type 1 := (P Op α).M

/-! ## Constructors and their destructor laws

`M.mk`/`M.dest` are mutually inverse, so each constructor's `dest` computes by `M.dest_mk`. -/

/-- Converge with a value. -/
def ret (a : α) : Comp Op α := PFunctor.M.mk ⟨Pos.ret a, PEmpty.elim⟩
/-- A silent step (the recursion guard; an infinite chain of these is divergence). -/
def tau (t : Comp Op α) : Comp Op α := PFunctor.M.mk ⟨Pos.tau, fun _ => t⟩
/-- Abort (e.g. an out-of-bounds read on a non-`Inhabited` element type). -/
def fail : Comp Op α := PFunctor.M.mk ⟨Pos.fail, PEmpty.elim⟩
/-- Perform effect `e`, continue with `k` on its result. -/
def vis {x : Type} (e : Effect Op x) (k : x → Comp Op α) : Comp Op α := PFunctor.M.mk ⟨Pos.vis e, k⟩

@[simp] theorem dest_ret (a : α) :
    (ret (Op := Op) a).dest = ⟨Pos.ret a, PEmpty.elim⟩ := PFunctor.M.dest_mk _
@[simp] theorem dest_tau (t : Comp Op α) :
    (tau t).dest = ⟨Pos.tau, fun _ => t⟩ := PFunctor.M.dest_mk _
@[simp] theorem dest_fail :
    (fail (Op := Op) (α := α)).dest = ⟨Pos.fail, PEmpty.elim⟩ := PFunctor.M.dest_mk _
@[simp] theorem dest_vis {x : Type} (e : Effect Op x) (k : x → Comp Op α) :
    (vis e k).dest = ⟨Pos.vis e, k⟩ := PFunctor.M.dest_mk _

/-- Two trees with equal one-step unfoldings are equal (destructor is injective). -/
theorem eq_of_dest_eq {x y : Comp Op α} (h : x.dest = y.dest) : x = y := by
  rw [← PFunctor.M.mk_dest x, ← PFunctor.M.mk_dest y, h]

/-- A destructor view: every tree is `ret`/`fail`/`tau`/`vis`.  (Used pervasively below to case on
    a tree by its head while keeping a real equation, rather than only its `dest`.) -/
theorem cases_view {α : Type} (x : Comp Op α) :
    (∃ a, x = ret a) ∨ x = fail ∨ (∃ t, x = tau t) ∨
      (∃ (β : Type) (e : Effect Op β) (k : β → Comp Op α), x = vis e k) := by
  obtain ⟨p, c, hd⟩ : ∃ p c, x.dest = ⟨p, c⟩ := ⟨_, _, rfl⟩
  match p, c, hd with
  | .ret a, c, hd =>
    exact Or.inl ⟨a, eq_of_dest_eq (by
      rw [hd, dest_ret]; exact Sigma.ext rfl (heq_of_eq (funext fun e => e.elim)))⟩
  | .fail, c, hd =>
    exact Or.inr (Or.inl (eq_of_dest_eq (by
      rw [hd, dest_fail]; exact Sigma.ext rfl (heq_of_eq (funext fun e => e.elim)))))
  | .tau, c, hd =>
    exact Or.inr (Or.inr (Or.inl ⟨c PUnit.unit, eq_of_dest_eq (by rw [hd, dest_tau])⟩))
  | .vis e, c, hd =>
    exact Or.inr (Or.inr (Or.inr ⟨_, e, c, eq_of_dest_eq (by rw [hd, dest_vis])⟩))

/-! ## Bind, by corecursion

State of the corecursion is `Comp Op α ⊕ Comp Op β`: `inl` is "still running the first tree"
(splice in `k a` at each `ret a`), `inr` is "copying the spliced result tree". -/

/-- The bind coalgebra (one step). -/
def bindCo {α β : Type} (k : α → Comp Op β) :
    (Comp Op α ⊕ Comp Op β) → (P Op β).Obj (Comp Op α ⊕ Comp Op β)
  | .inl m =>
    match m.dest with
    | ⟨p, c⟩ =>
      match p, c with
      | .ret a, _ => match (k a).dest with | ⟨b, g⟩ => ⟨b, fun i => .inr (g i)⟩
      | .tau,  c => ⟨Pos.tau, fun u => .inl (c u)⟩
      | .fail, _ => ⟨Pos.fail, PEmpty.elim⟩
      | .vis e, c => ⟨Pos.vis e, fun i => .inl (c i)⟩
  | .inr t =>
    match t.dest with | ⟨b, g⟩ => ⟨b, fun i => .inr (g i)⟩

/-- Monadic bind on interaction trees. -/
def bind {α β : Type} (m : Comp Op α) (k : α → Comp Op β) : Comp Op β :=
  PFunctor.M.corec (bindCo k) (.inl m)

/-- Copying an already-built tree (the `inr` state) is the identity. -/
theorem corec_inr {α β : Type} (k : α → Comp Op β) (t : Comp Op β) :
    PFunctor.M.corec (bindCo k) (.inr t) = t := by
  refine PFunctor.M.bisim
    (fun x y => x = PFunctor.M.corec (bindCo k) (.inr y)) ?_ _ _ rfl
  intro x y hxy
  subst hxy
  obtain ⟨b, g, hy⟩ : ∃ b g, y.dest = ⟨b, g⟩ := ⟨_, _, rfl⟩
  refine ⟨b, fun i => PFunctor.M.corec (bindCo k) (.inr (g i)), g, ?_, hy, fun i => rfl⟩
  rw [PFunctor.M.dest_corec]
  simp only [bindCo, hy, PFunctor.map]
  rfl

/-! ### Bind computation laws -/

@[simp] theorem bind_ret {α β : Type} (a : α) (k : α → Comp Op β) : bind (ret a) k = k a := by
  apply eq_of_dest_eq
  obtain ⟨b, g, hk⟩ : ∃ b g, (k a).dest = ⟨b, g⟩ := ⟨_, _, rfl⟩
  rw [bind, PFunctor.M.dest_corec]
  simp only [bindCo, dest_ret, hk, PFunctor.map, Function.comp_def, corec_inr]

@[simp] theorem bind_tau {α β : Type} (t : Comp Op α) (k : α → Comp Op β) :
    bind (tau t) k = tau (bind t k) := by
  apply eq_of_dest_eq
  simp only [bind, PFunctor.M.dest_corec, bindCo, dest_tau, PFunctor.map, Function.comp_def]

@[simp] theorem bind_fail {α β : Type} (k : α → Comp Op β) : bind (fail : Comp Op α) k = fail := by
  apply eq_of_dest_eq
  simp only [bind, PFunctor.M.dest_corec, bindCo, dest_fail, PFunctor.map, Function.comp_def]
  congr 1
  funext e
  exact e.elim

@[simp] theorem bind_vis {α β x : Type} (e : Effect Op x) (c : x → Comp Op α) (k : α → Comp Op β) :
    bind (vis e c) k = vis e (fun i => bind (c i) k) := by
  apply eq_of_dest_eq
  simp only [bind, PFunctor.M.dest_corec, bindCo, dest_vis, PFunctor.map, Function.comp_def]

/-- Interaction trees are a monad (`pure = ret`, `bind` as above). -/
instance : Monad (Comp Op) where
  pure := ret
  bind := bind

@[simp] theorem pure_def {α} (a : α) : (pure a : Comp Op α) = ret a := rfl
@[simp] theorem bind_def {α β} (m : Comp Op α) (k : α → Comp Op β) : m >>= k = bind m k := rfl

/-- Right identity: `bind m ret = m` (by bisimulation). -/
theorem bind_ret_right {α} (m : Comp Op α) : bind m ret = m := by
  suffices H : ∀ x y : Comp Op α, (x = bind y ret ∨ x = y) → x = y from H _ _ (Or.inl rfl)
  refine PFunctor.M.bisim _ ?_
  rintro x y (rfl | rfl)
  · rcases cases_view y with ⟨a, rfl⟩ | rfl | ⟨t', rfl⟩ | ⟨δ, e, c, rfl⟩
    · rw [bind_ret]
      exact ⟨Pos.ret a, PEmpty.elim, PEmpty.elim, dest_ret a, dest_ret a, fun i => i.elim⟩
    · rw [bind_fail]
      exact ⟨Pos.fail, PEmpty.elim, PEmpty.elim, dest_fail, dest_fail, fun i => i.elim⟩
    · rw [bind_tau]
      exact ⟨Pos.tau, _, _, dest_tau _, dest_tau _, fun _ => Or.inl rfl⟩
    · rw [bind_vis]
      exact ⟨Pos.vis e, _, _, dest_vis _ _, dest_vis _ _, fun i => Or.inl rfl⟩
  · obtain ⟨p, c, hd⟩ : ∃ p c, x.dest = ⟨p, c⟩ := ⟨_, _, rfl⟩
    exact ⟨p, c, c, hd, hd, fun _ => Or.inr rfl⟩

/-- Associativity of `bind` (by bisimulation). -/
theorem bind_assoc {α β γ} (m : Comp Op α) (k : α → Comp Op β) (h : β → Comp Op γ) :
    bind (bind m k) h = bind m (fun a => bind (k a) h) := by
  suffices H : ∀ x y : Comp Op γ,
      ((∃ m, x = bind (bind m k) h ∧ y = bind m (fun a => bind (k a) h)) ∨ x = y) → x = y from
    H _ _ (Or.inl ⟨m, rfl, rfl⟩)
  refine PFunctor.M.bisim _ ?_
  rintro x y (⟨m, rfl, rfl⟩ | rfl)
  · rcases cases_view m with ⟨a, rfl⟩ | rfl | ⟨t, rfl⟩ | ⟨δ, e, c, rfl⟩
    · rw [bind_ret, bind_ret]
      obtain ⟨p, c', hd'⟩ : ∃ p c', (bind (k a) h).dest = ⟨p, c'⟩ := ⟨_, _, rfl⟩
      exact ⟨p, c', c', hd', hd', fun _ => Or.inr rfl⟩
    · rw [bind_fail, bind_fail, bind_fail]
      exact ⟨Pos.fail, PEmpty.elim, PEmpty.elim, dest_fail, dest_fail, fun i => i.elim⟩
    · rw [bind_tau, bind_tau, bind_tau]
      exact ⟨Pos.tau, _, _, dest_tau _, dest_tau _, fun _ => Or.inl ⟨t, rfl, rfl⟩⟩
    · rw [bind_vis, bind_vis, bind_vis]
      exact ⟨Pos.vis e, _, _, dest_vis _ _, dest_vis _ _, fun i => Or.inl ⟨c i, rfl, rfl⟩⟩
  · obtain ⟨p, c, hd⟩ : ∃ p c, x.dest = ⟨p, c⟩ := ⟨_, _, rfl⟩
    exact ⟨p, c, c, hd, hd, fun _ => Or.inr rfl⟩

/-! ## Divergence is representable -/

/-- The always-`tau` tree: a canonical divergent (non-terminating, effect-free) computation. -/
def spin : Comp Op α :=
  PFunctor.M.corec (fun _ : Unit => (⟨Pos.tau, fun _ => ()⟩ : (P Op α).Obj Unit)) ()

/-- `spin` is its own `tau` unfolding — it never makes progress (divergence). -/
theorem spin_eq : (spin : Comp Op α) = tau spin := by
  apply eq_of_dest_eq
  conv_lhs => rw [spin, PFunctor.M.dest_corec]
  simp only [PFunctor.map, dest_tau, Function.comp_def]
  rfl

/-! ## Guarded recursion: the iteration combinator

`iter f a` runs `f a : Comp (α ⊕ β)`; on `inl a'` it loops (guarded by a `tau`, which is what
makes the corecursion productive — no termination proof needed), on `inr b` it returns `b`.  This
is the Elgot iteration operator, the basis for denoting recursive definitions. -/

/-- The iteration coalgebra (one step of running the body tree). -/
def iterCo {α β : Type} (f : α → Comp Op (α ⊕ β)) :
    Comp Op (α ⊕ β) → (P Op β).Obj (Comp Op (α ⊕ β))
  | t =>
    match t.dest with
    | ⟨p, c⟩ =>
      match p, c with
      | .ret (.inl a'), _ => ⟨Pos.tau, fun _ => f a'⟩
      | .ret (.inr b),  _ => ⟨Pos.ret b, PEmpty.elim⟩
      | .tau,  c => ⟨Pos.tau, fun u => c u⟩
      | .fail, _ => ⟨Pos.fail, PEmpty.elim⟩
      | .vis e, c => ⟨Pos.vis e, fun i => c i⟩

/-- Elgot iteration: loop `f` from `a`, guarded by `tau`. -/
def iter {α β : Type} (f : α → Comp Op (α ⊕ β)) (a : α) : Comp Op β :=
  PFunctor.M.corec (iterCo f) (f a)

/-- The continuation of one iteration step: loop (guarded by `tau`) or stop. -/
def iterK {α β : Type} (f : α → Comp Op (α ⊕ β)) : (α ⊕ β) → Comp Op β
  | .inl a' => tau (iter f a')
  | .inr b  => ret b

/-- **The fixpoint law.** `iter f a` unfolds to: run `f a`, then loop or return.  (Recursive call
    `iter f a'` is guarded by a `tau`.)  This is what makes `iter` a genuine fixpoint of its
    defining equation, proved by coinduction. -/
theorem iter_unfold {α β : Type} (f : α → Comp Op (α ⊕ β)) (a : α) :
    iter f a = bind (f a) (iterK f) := by
  -- bisimulation up to "equal, or both are (iter-run / bind-run) of the same body tree"
  suffices H : ∀ x y : Comp Op β,
      (x = y ∨ ∃ t, x = PFunctor.M.corec (iterCo f) t ∧ y = bind t (iterK f)) → x = y by
    exact H _ _ (Or.inr ⟨f a, rfl, rfl⟩)
  refine PFunctor.M.bisim _ ?_
  rintro x y (rfl | ⟨t, rfl, rfl⟩)
  · obtain ⟨a0, g0, hd⟩ : ∃ a0 g0, x.dest = ⟨a0, g0⟩ := ⟨_, _, rfl⟩
    exact ⟨a0, g0, g0, hd, hd, fun _ => Or.inl rfl⟩
  · obtain ⟨p, c, hd⟩ : ∃ p c, t.dest = ⟨p, c⟩ := ⟨_, _, rfl⟩
    match p, c, hd with
    | .ret (.inl a'), c, hd =>
      exact ⟨Pos.tau, fun _ => PFunctor.M.corec (iterCo f) (f a'),
                      fun _ => PFunctor.M.corec (iterCo f) (f a'),
        by simp only [PFunctor.M.dest_corec, iterCo, hd, PFunctor.map, Function.comp_def],
        by simp only [bind, PFunctor.M.dest_corec, bindCo, hd, iterK, iter, dest_tau,
                      PFunctor.map, Function.comp_def, corec_inr],
        fun _ => Or.inl rfl⟩
    | .ret (.inr b), c, hd =>
      exact ⟨Pos.ret b, PEmpty.elim, PEmpty.elim,
        by simp only [PFunctor.M.dest_corec, iterCo, hd, PFunctor.map, Function.comp_def]
           exact congrArg (Sigma.mk _) (funext fun e => e.elim),
        by simp only [bind, PFunctor.M.dest_corec, bindCo, hd, iterK, dest_ret,
                      PFunctor.map, Function.comp_def]
           exact congrArg (Sigma.mk _) (funext fun e => e.elim),
        fun i => i.elim⟩
    | .tau, c, hd =>
      exact ⟨Pos.tau, fun u => PFunctor.M.corec (iterCo f) (c u),
                      fun u => bind (c u) (iterK f),
        by simp only [PFunctor.M.dest_corec, iterCo, hd, PFunctor.map, Function.comp_def],
        by simp only [bind, PFunctor.M.dest_corec, bindCo, hd, PFunctor.map, Function.comp_def],
        fun u => Or.inr ⟨c u, rfl, rfl⟩⟩
    | .fail, c, hd =>
      exact ⟨Pos.fail, PEmpty.elim, PEmpty.elim,
        by simp only [PFunctor.M.dest_corec, iterCo, hd, PFunctor.map, Function.comp_def]
           exact congrArg (Sigma.mk _) (funext fun e => e.elim),
        by simp only [bind, PFunctor.M.dest_corec, bindCo, hd, PFunctor.map, Function.comp_def]
           exact congrArg (Sigma.mk _) (funext fun e => e.elim),
        fun i => i.elim⟩
    | .vis e, c, hd =>
      exact ⟨Pos.vis e, fun i => PFunctor.M.corec (iterCo f) (c i),
                        fun i => bind (c i) (iterK f),
        by simp only [PFunctor.M.dest_corec, iterCo, hd, PFunctor.map, Function.comp_def],
        by simp only [bind, PFunctor.M.dest_corec, bindCo, hd, PFunctor.map, Function.comp_def],
        fun i => Or.inr ⟨c i, rfl, rfl⟩⟩

/-! ## General recursion: `mrec`

`iter` only captures *tail* recursion: its step `σ → Comp (σ ⊕ ρ)` loops on `inl` and stops on
`inr`, with no room for "make a recursive call, then continue with its result".  General (incl.
non-tail) recursion needs the recursive call to be a node *inside* the tree, so the continuation
after it is preserved.  We add one operation — a `call` effect — to the signature, let the body be
an interaction tree over `CallOp Op σ ρ` (calls allowed anywhere), and tie the knot by
**interpreting** every `call` back into the body, guarded by a `tau`.  This subsumes `iter`. -/

/-- The signature `Op` extended with a single recursive-call operation `call : σ → ρ`. -/
inductive CallOp (Op : Type → Type → Type 1) (σ ρ : Type) : Type → Type → Type 1
  | base {I O : Type} : Op I O → CallOp Op σ ρ I O
  | call : CallOp Op σ ρ σ ρ

variable {σ ρ : Type}

/-- One step of interpreting a body tree: external effects (`base`) pass through (renamed back to
    `Op`); a `call inp` is replaced by the body re-run on `inp` (with the call's continuation
    spliced after), guarded by a `tau` (which makes the corecursion productive). -/
def interpCo (body : σ → Comp (CallOp Op σ ρ) ρ) {γ : Type} :
    Comp (CallOp Op σ ρ) γ → (P Op γ).Obj (Comp (CallOp Op σ ρ) γ)
  | t =>
    match t.dest with
    | ⟨.ret b, _⟩ => ⟨Pos.ret b, PEmpty.elim⟩
    | ⟨.tau, c⟩   => ⟨Pos.tau, c⟩
    | ⟨.fail, _⟩  => ⟨Pos.fail, PEmpty.elim⟩
    | ⟨.vis e, c⟩ =>
      match e with
      | Effect.mk (CallOp.base o) inp => ⟨Pos.vis (Effect.mk o inp), c⟩
      | Effect.mk CallOp.call inp     => ⟨Pos.tau, fun _ => bind (body inp) c⟩

/-- Interpret a body tree (calls allowed) into a plain `Comp Op` tree, by guarded corecursion. -/
def interp (body : σ → Comp (CallOp Op σ ρ) ρ) {γ : Type} (t : Comp (CallOp Op σ ρ) γ) :
    Comp Op γ :=
  PFunctor.M.corec (interpCo body) t

/-- **General recursion.** `mrec body` ties the recursive knot: run the body, interpreting each
    self-`call` by re-running the body.  Unlike `iter`, the body may call itself in any position
    (the continuation after a call is kept in the tree), so non-tail recursion is supported. -/
def mrec (body : σ → Comp (CallOp Op σ ρ) ρ) (s : σ) : Comp Op ρ :=
  interp body (body s)

/-! ### `interp` computation laws -/

@[simp] theorem interp_ret (body : σ → Comp (CallOp Op σ ρ) ρ) {γ} (b : γ) :
    interp body (ret b) = ret b := by
  apply eq_of_dest_eq
  simp only [interp, PFunctor.M.dest_corec, interpCo, dest_ret, PFunctor.map, Function.comp_def]
  congr 1; funext e; exact e.elim

@[simp] theorem interp_tau (body : σ → Comp (CallOp Op σ ρ) ρ) {γ} (t : Comp (CallOp Op σ ρ) γ) :
    interp body (tau t) = tau (interp body t) := by
  apply eq_of_dest_eq
  simp only [interp, PFunctor.M.dest_corec, interpCo, dest_tau, PFunctor.map, Function.comp_def]

@[simp] theorem interp_fail (body : σ → Comp (CallOp Op σ ρ) ρ) {γ} :
    interp body (fail : Comp (CallOp Op σ ρ) γ) = fail := by
  apply eq_of_dest_eq
  simp only [interp, PFunctor.M.dest_corec, interpCo, dest_fail, PFunctor.map, Function.comp_def]
  congr 1; funext e; exact e.elim

/-- External effects pass through interpretation unchanged (renamed from `base o` back to `o`). -/
@[simp] theorem interp_vis_base (body : σ → Comp (CallOp Op σ ρ) ρ) {γ} {I O : Type}
    (o : Op I O) (inp : I) (c : O → Comp (CallOp Op σ ρ) γ) :
    interp body (vis (Effect.mk (CallOp.base o) inp) c) = vis (Effect.mk o inp) (fun x => interp body (c x)) := by
  apply eq_of_dest_eq
  simp only [interp, PFunctor.M.dest_corec, interpCo, dest_vis, PFunctor.map, Function.comp_def]

/-- A self-`call inp` is interpreted as the body re-run on `inp` (continuation `c` spliced after),
    guarded by a `tau` — the recursion's unfolding step. -/
@[simp] theorem interp_vis_call (body : σ → Comp (CallOp Op σ ρ) ρ) {γ}
    (inp : σ) (c : ρ → Comp (CallOp Op σ ρ) γ) :
    interp body (vis (Effect.mk CallOp.call inp) c) = tau (interp body (bind (body inp) c)) := by
  apply eq_of_dest_eq
  simp only [interp, PFunctor.M.dest_corec, interpCo, dest_vis, PFunctor.map, Function.comp_def,
             dest_tau]

/-- **`interp` is a monad morphism**: it commutes with `bind`.  This is what makes *non-tail*
    recursion compute correctly — the work after a recursive call (`k`) is pushed through the
    interpretation.  Proved by bisimulation (using `bind_assoc` at the `call` step). -/
theorem interp_bind (body : σ → Comp (CallOp Op σ ρ) ρ) {β γ}
    (m : Comp (CallOp Op σ ρ) β) (k : β → Comp (CallOp Op σ ρ) γ) :
    interp body (bind m k) = bind (interp body m) (fun x => interp body (k x)) := by
  suffices H : ∀ x y : Comp Op γ,
      ((∃ m : Comp (CallOp Op σ ρ) β, x = interp body (bind m k) ∧
          y = bind (interp body m) (fun x => interp body (k x))) ∨ x = y) → x = y from
    H _ _ (Or.inl ⟨m, rfl, rfl⟩)
  refine PFunctor.M.bisim _ ?_
  rintro x y (⟨m, rfl, rfl⟩ | rfl)
  · rcases cases_view m with ⟨a, rfl⟩ | rfl | ⟨t, rfl⟩ | ⟨δ, e, c, rfl⟩
    · rw [bind_ret, interp_ret, bind_ret]
      obtain ⟨p, c', hd'⟩ : ∃ p c', (interp body (k a)).dest = ⟨p, c'⟩ := ⟨_, _, rfl⟩
      exact ⟨p, c', c', hd', hd', fun _ => Or.inr rfl⟩
    · simp only [bind_fail, interp_fail]
      exact ⟨Pos.fail, PEmpty.elim, PEmpty.elim, dest_fail, dest_fail, fun i => i.elim⟩
    · rw [bind_tau, interp_tau, interp_tau, bind_tau]
      exact ⟨Pos.tau, _, _, dest_tau _, dest_tau _, fun _ => Or.inl ⟨t, rfl, rfl⟩⟩
    · cases e with
      | @mk I O op inp =>
        cases op with
        | base o =>
          rw [bind_vis, interp_vis_base, interp_vis_base, bind_vis]
          exact ⟨Pos.vis (Effect.mk o inp), _, _, dest_vis _ _, dest_vis _ _,
                 fun i => Or.inl ⟨c i, rfl, rfl⟩⟩
        | call =>
          rw [bind_vis, interp_vis_call, interp_vis_call, bind_tau]
          exact ⟨Pos.tau, _, _, dest_tau _, dest_tau _,
                 fun _ => Or.inl ⟨bind (body inp) c, by rw [bind_assoc], rfl⟩⟩
  · obtain ⟨p, c, hd⟩ : ∃ p c, x.dest = ⟨p, c⟩ := ⟨_, _, rfl⟩
    exact ⟨p, c, c, hd, hd, fun _ => Or.inr rfl⟩

/-! ## Embedding source computations -/

/-- Embed an ordinary (finite, total) source computation into the ITree domain. -/
def ofFree {α} : Free (Effect Op) α → Comp Op α
  | .Pure a     => ret a
  | .Impure e c => vis e (fun x => ofFree (c x))

@[simp] theorem ofFree_pure {α} (a : α) : ofFree (Free.Pure a : Free (Effect Op) α) = ret a := rfl

/-- `ofFree` is a monad homomorphism. -/
theorem ofFree_bind {α β} (m : Free (Effect Op) α) (k : α → Free (Effect Op) β) :
    ofFree (freeBind m k) = bind (ofFree m) (fun a => ofFree (k a)) := by
  induction m with
  | Pure a => simp [freeBind, ofFree, bind_ret]
  | Impure e c ih => simp [freeBind, ofFree, bind_vis, ih]

/-- `ofFree` commutes with `forIn` over a list (it is a monad homomorphism). -/
theorem ofFree_listForIn {α β : Type} (l : List α) (init : β)
    (f : α → β → Free (Effect Op) (ForInStep β)) :
    ofFree (forIn l init f) = forIn l init (fun a b => ofFree (f a b)) := by
  induction l generalizing init with
  | nil => simp only [List.forIn_nil]; rfl
  | cons x xs ih =>
    simp only [List.forIn_cons, free_bind_eq, ofFree_bind, bind_def]
    congr 1; funext s; cases s with
    | done b => rfl
    | yield b => exact ih b

/-- `ofFree` commutes with the bounded `forIn` loop — the bridge that makes the `Comp` denotation
    of a `forN` correspond to the `Free` spec's loop. -/
theorem ofFree_forIn {β : Type} (r : Std.Legacy.Range) (init : β)
    (f : Nat → β → Free (Effect Op) (ForInStep β)) :
    ofFree (forIn r init f) = forIn r init (fun i a => ofFree (f i a)) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact ofFree_listForIn _ init f

/-! ## Observing convergence

`stepN n c` runs the tree for up to `n` steps, peeling `tau`s and following the single `ret`,
returning `some a` if a value is reached (and `none` on running out of fuel, on `fail`, or on a
visible effect — this observation function is for the effect-free/divergence story).  `Converges`
is "reaches a value in some finite number of steps".  Crucially this is an *observation* of the
already-total denotation, not the denotation itself. -/

/-- Run up to `n` steps, peeling `tau`s, returning the value if reached. -/
def stepN {α} : Nat → Comp Op α → Option α
  | 0,     _ => none
  | n + 1, c =>
    match c.dest with
    | ⟨.ret a, _⟩ => some a
    | ⟨.tau, k⟩   => stepN n (k PUnit.unit)
    | _           => none

/-- The tree reaches a value in finitely many steps. -/
def Converges {α} (c : Comp Op α) (a : α) : Prop := ∃ n, stepN n c = some a

@[simp] theorem stepN_ret {α} (n : Nat) (a : α) : stepN (n + 1) (ret a : Comp Op α) = some a := by
  simp only [stepN, dest_ret]

theorem stepN_tau {α} (n : Nat) (t : Comp Op α) : stepN (n + 1) (tau t) = stepN n t := by
  simp only [stepN, dest_tau]

/-- `spin` **diverges**: it never reaches a value. -/
theorem spin_diverges {α} (a : α) : ¬ Converges (spin : Comp Op α) a := by
  rintro ⟨n, hn⟩
  induction n with
  | zero => simp [stepN] at hn
  | succ m ih =>
    rw [spin_eq, stepN_tau] at hn
    exact ih hn

/-! ## General adequacy of `iter`

The operational meaning of iterating a pure step `step : α → α ⊕ β`: loop on `inl`, stop on `inr`.
`runStep` runs it for up to `n` steps.  **`iter_converges`** is the adequacy theorem: whenever the
operational iteration reaches a result, the coinductive `iter` denotation *converges to the same
value* — proved generally (for any `step`), by induction, using the `iter` fixpoint law.  This is
the "recursion denotes soundly into the ITree domain" result; the toy `down` below is one instance. -/

/-- Operational iteration of a pure step, up to `n` steps. -/
def runStep {α β : Type} (step : α → α ⊕ β) : Nat → α → Option β
  | 0,     _ => none
  | n + 1, a => match step a with
                | .inl a' => runStep step n a'
                | .inr b  => some b

/-- **Adequacy:** if the operational iteration of `step` reaches `b`, the `iter` denotation
    converges to `b`.  General in `step` — this is `iter` computing the right thing. -/
theorem iter_converges {α β : Type} (step : α → α ⊕ β) :
    ∀ (n : Nat) (a : α) (b : β), runStep step n a = some b →
      Converges (iter (fun a => ret (Op := Op) (step a)) a) b := by
  intro n
  induction n with
  | zero => intro a b h; simp [runStep] at h
  | succ m ih =>
    intro a b h
    have hstep : iter (fun a => ret (Op := Op) (step a)) a
               = iterK (fun a => ret (Op := Op) (step a)) (step a) := by
      rw [iter_unfold]; simp only [bind_ret]
    rw [runStep] at h
    rw [hstep]
    cases hsa : step a with
    | inl a' =>
      rw [hsa] at h
      obtain ⟨k, hk⟩ := ih a' b h
      exact ⟨k + 1, by simp only [hsa, iterK]; rw [stepN_tau]; exact hk⟩
    | inr b' =>
      rw [hsa] at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨1, by simp only [hsa, iterK]; exact stepN_ret 0 b'⟩

/-! ## A worked recursive instance: countdown -/

/-- One step of countdown: at `0` stop with `0`, else loop on the predecessor. -/
def downStep : Nat → Nat ⊕ Nat
  | 0     => .inr 0
  | n + 1 => .inl n

/-- Countdown from `n` to `0` by guarded recursion. -/
def down (n : Nat) : Comp Op Nat := iter (fun n => ret (downStep n)) n

/-- Countdown converges to `0` from every `n` — an instance of the general `iter_converges`. -/
theorem down_converges (n : Nat) : Converges (down n : Comp Op Nat) 0 := by
  apply iter_converges (Op := Op) downStep (n + 1) n 0
  induction n with
  | zero => rfl
  | succ m ih => rw [runStep]; simpa [downStep] using ih

end ITree
end Freigen
