import Freigen.ITree.Eutt

/-!
# Adequacy of `mrec`: the reflected recursion is `≈` the source recursion

This is the generic theorem behind the **merged** `reflect%` recursion path: the `mrec` denotation of
a reflected recursive `def` is weakly bisimilar (`≈`) to the source.  The bounded path gets its
soundness for free (`denoteProg … = e …` definitionally); the recursive path's soundness is `≈`
(the `tau`-guarded knot is only weakly bisimilar to its finite source), and *this* file proves it
generically so the elaborator can emit it like any other soundness proof.

The crux is `adeqBody`: interpreting a call-body tree (`interp ∘ ofFree`) is `≈` to running the same
tree with the source `e` plugged in at each `call` (`ofFree ∘ runSrc`), **given** the source is
adequate at every call argument below a bound (`Ho`) and every call in the tree respects that bound
(`callsLt`).  It is a single structural induction using the `Eutt` congruences — no transitivity,
no termination measure (the bound + `callsLt` carry the well-foundedness, discharged per-`N` by the
caller once `N`'s `cond` has reduced and the unreachable branch is gone).
-/

namespace Freigen
namespace ITree

variable {Op : Type → Type → Type 1} {ρ : Type}

/-- Run a call-body tree with the source `e` plugged in at each `call`: a `call k` is replaced by
    "run `e k`, then continue".  External (`base`) effects are relabelled back to `Op`. -/
def runSrc (e : Nat → Free (Effect Op) ρ) {γ : Type} :
    Free (Effect (CallOp Op Nat ρ)) γ → Free (Effect Op) γ
  | .Pure a => .Pure a
  | .Impure (.mk (.base o) i) c => .Impure (.mk o i) (fun x => runSrc e (c x))
  | .Impure (.mk .call i) c => freeBind (e i) (fun v => runSrc e (c v))

/-- Every `call` argument in the tree is `< bound`. -/
def callsLt (bound : Nat) {γ : Type} : Free (Effect (CallOp Op Nat ρ)) γ → Prop
  | .Pure _ => True
  | .Impure (.mk (.base _) _) c => ∀ x, callsLt bound (c x)
  | .Impure (.mk .call i) c => i < bound ∧ ∀ x, callsLt bound (c x)

@[simp] theorem callsLt_pure (bound : Nat) {γ} (a : γ) :
    callsLt (Op := Op) (ρ := ρ) bound (.Pure a) = True := rfl

/-- **The adequacy step.** Interpreting a call-body is `≈` to running it with the source plugged in,
    provided the source is adequate below `bound` and the tree only calls below `bound`. -/
theorem adeqBody (body : Nat → Comp (CallOp Op Nat ρ) ρ) (e : Nat → Free (Effect Op) ρ)
    (bound : Nat) (Ho : ∀ k, k < bound → mrec body k ≈ ofFree (e k)) :
    ∀ {γ : Type} (t : Free (Effect (CallOp Op Nat ρ)) γ), callsLt bound t →
      interp body (ofFree t) ≈ ofFree (runSrc e t) := by
  intro γ t
  induction t with
  | Pure a => intro _; simp only [ofFree, runSrc, interp_ret]; exact eutt_refl _
  | Impure ef c ih =>
    cases ef with
    | @mk I O op i =>
      cases op with
      | base o =>
        intro h
        simp only [ofFree, runSrc, interp_vis_base]
        exact eutt_vis_cong _ (fun x => ih x (h x))
      | call =>
        intro h
        simp only [ofFree, runSrc, interp_vis_call, interp_bind, ofFree_bind]
        refine eutt_tau_left ?_
        exact eutt_bind_cong (Ho i h.1) (fun x => ih x (h.2 x))

/-- `adeqBody` with the `runSrc = e` bridge folded in, so one tactic discharges the step against the
    source directly. -/
theorem adeqBody' (body : Nat → Comp (CallOp Op Nat ρ) ρ) (e : Nat → Free (Effect Op) ρ)
    (N : Nat) (t : Free (Effect (CallOp Op Nat ρ)) ρ)
    (IH : ∀ k, k < N → mrec body k ≈ ofFree (e k)) (hcl : callsLt N t)
    (hrun : runSrc e t = e N) :
    interp body (ofFree t) ≈ ofFree (e N) := by
  rw [← hrun]; exact adeqBody body e N IH t hcl

/-- **`mrec` adequacy (strong-induction shell).** Given that each recursion step is adequate using
    the adequacy of all *smaller* arguments, the whole reflected recursion is `≈` its source.  The
    per-function step `Hstep` is what the elaborator discharges with `adeqBody`. -/
theorem mrec_adequacy (body : Nat → Comp (CallOp Op Nat ρ) ρ) (e : Nat → Free (Effect Op) ρ)
    (Hstep : ∀ N, (∀ k, k < N → mrec body k ≈ ofFree (e k)) → mrec body N ≈ ofFree (e N)) :
    ∀ N, mrec body N ≈ ofFree (e N) :=
  fun N => Nat.strongRecOn N Hstep

end ITree
end Freigen
