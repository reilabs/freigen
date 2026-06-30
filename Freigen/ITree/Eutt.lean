import Freigen.ITree.Basic

/-!
# Weak bisimulation (`eutt`) for interaction trees

`Eutt` is *equivalence up to `tau`*: two computations are related when, ignoring finitely many
silent `tau` steps, they have the same `ret`/`fail`/`vis` structure (with `eutt`-related effect
continuations), and two divergent computations are related.  It collapses to equality on the
`tau`-free (bounded) fragment, and lets a `tau`-guarded recursion be related to its result.

We define it in the standard bisimulation-up-to-`tau` style: a one-step functor `EuttF R`
(inductive, so finitely many `tau`s can be stripped on either side; the both-`tau` case recurses
through `R`, which handles divergence), and `Eutt x y` as *the existence of a bisimulation* —
`∃ R, (∀ a b, R a b → EuttF R a b) ∧ R x y`.  No native coinduction needed.
-/

namespace Freigen
namespace ITree

universe u
variable {Op : Type → Type → Type 1} {α : Type}

/-! ## The one-step functor and `Eutt` (`cases_view` is now in `ITree.lean`) -/

/-- One step of weak bisimulation parameterised by the relation `R` for effect continuations.
    `tauL`/`tauR` strip a single `tau` (inductive — so finitely many can be removed); `tau` relates
    two `tau`-headed trees through `R` (which is where divergence is handled). -/
inductive EuttF (R : Comp Op α → Comp Op α → Prop) : Comp Op α → Comp Op α → Prop where
  | ret  (a : α) : EuttF R (ret a) (ret a)
  | fail : EuttF R (fail : Comp Op α) fail
  | vis  {β : Type} (e : Effect Op β) (kx ky : β → Comp Op α) (h : ∀ i, R (kx i) (ky i)) :
      EuttF R (vis e kx) (vis e ky)
  | tau  (tx ty : Comp Op α) (h : R tx ty) : EuttF R (tau tx) (tau ty)
  | tauL {y : Comp Op α} (tx : Comp Op α) (h : EuttF R tx y) : EuttF R (tau tx) y
  | tauR {x : Comp Op α} (ty : Comp Op α) (h : EuttF R x ty) : EuttF R x (tau ty)

/-- `x ≈ y`: there is a bisimulation (`EuttF`-closed relation) relating `x` and `y`. -/
def Eutt (x y : Comp Op α) : Prop :=
  ∃ R : Comp Op α → Comp Op α → Prop, (∀ a b, R a b → EuttF R a b) ∧ R x y

@[inherit_doc] scoped infix:50 " ≈ " => Eutt

/-! ## Reflexivity / equality -/

/-- One step relating a tree to itself, for any relation reflexive on the relevant children. -/
theorem euttF_diag {R : Comp Op α → Comp Op α → Prop} (hR : ∀ x, R x x) (a : Comp Op α) :
    EuttF R a a := by
  rcases cases_view a with ⟨v, rfl⟩ | rfl | ⟨t, rfl⟩ | ⟨β, e, k, rfl⟩
  · exact .ret v
  · exact .fail
  · exact .tau t t (hR t)
  · exact .vis e k k (fun _ => hR _)

/-- Reflexivity (holds even for divergent trees, via the `tau` case). -/
theorem eutt_refl (x : Comp Op α) : x ≈ x :=
  ⟨Eq, fun _ _ h => h ▸ euttF_diag (fun _ => rfl) _, rfl⟩

theorem Eutt.of_eq {x y : Comp Op α} (h : x = y) : x ≈ y := h ▸ eutt_refl x

/-- A leading `tau` can be stripped: `tau t ≈ t`. -/
theorem eutt_tau (t : Comp Op α) : tau t ≈ t := by
  refine ⟨fun x y => x = tau y ∨ x = y, ?_, Or.inl rfl⟩
  rintro a b (rfl | rfl)
  · exact .tauL b (euttF_diag (fun _ => Or.inr rfl) b)
  · exact euttF_diag (fun _ => Or.inr rfl) a

/-! ## The `Eutt` algebra: monotonicity, congruences

These are the lemmas that let `≈` be *constructed* rather than only stated — exactly what's needed
to discharge the soundness of a reflected program whose denotation is `≈` (not `=`) to its source. -/

/-- `EuttF` is monotone in its relation argument. -/
theorem EuttF.mono {R R' : Comp Op α → Comp Op α → Prop} (h : ∀ a b, R a b → R' a b)
    {x y : Comp Op α} (he : EuttF R x y) : EuttF R' x y := by
  induction he with
  | ret a            => exact .ret a
  | fail             => exact .fail
  | vis e kx ky hk   => exact .vis e kx ky (fun i => h _ _ (hk i))
  | tau tx ty ht     => exact .tau tx ty (h _ _ ht)
  | tauL tx _ ih     => exact .tauL tx ih
  | tauR ty _ ih     => exact .tauR ty ih

/-- `Eutt` is itself a bisimulation (the largest one): one `EuttF`-step relating through `Eutt`. -/
theorem eutt_closed {x y : Comp Op α} (h : x ≈ y) : EuttF Eutt x y := by
  obtain ⟨R, hR, hxy⟩ := h
  exact (hR x y hxy).mono (fun a b hab => ⟨R, hR, hab⟩)

/-- Strip a leading `tau` on the left while keeping the relation: `x ≈ y → tau x ≈ y`. -/
theorem eutt_tau_left {x y : Comp Op α} (h : x ≈ y) : tau x ≈ y := by
  refine ⟨fun a b => (a = tau x ∧ b = y) ∨ a ≈ b, ?_, Or.inl ⟨rfl, rfl⟩⟩
  rintro a b (⟨rfl, rfl⟩ | hab)
  · exact .tauL x ((eutt_closed h).mono (fun _ _ h => Or.inr h))
  · exact (eutt_closed hab).mono (fun _ _ h => Or.inr h)

/-- `vis`-congruence: related continuations give related `vis` nodes. -/
theorem eutt_vis_cong {β : Type} (e : Effect Op β) {k1 k2 : β → Comp Op α}
    (h : ∀ i, k1 i ≈ k2 i) : vis e k1 ≈ vis e k2 := by
  refine ⟨fun a b => (a = vis e k1 ∧ b = vis e k2) ∨ a ≈ b, ?_, Or.inl ⟨rfl, rfl⟩⟩
  rintro a b (⟨rfl, rfl⟩ | hab)
  · exact .vis e k1 k2 (fun i => Or.inr (h i))
  · exact (eutt_closed hab).mono (fun _ _ h => Or.inr h)

/-- **`bind`-congruence for `≈`**: bisimilar prefixes with pointwise-bisimilar continuations give
    bisimilar binds.  Proved by bisimulation, casing on the prefix relation by *induction* on one
    `EuttF`-step (so the finitely-many leading `tau`s of the prefix are stripped). -/
theorem eutt_bind_cong {β : Type} {m1 m2 : Comp Op α} {k1 k2 : α → Comp Op β}
    (hm : m1 ≈ m2) (hk : ∀ x, k1 x ≈ k2 x) : bind m1 k1 ≈ bind m2 k2 := by
  refine ⟨fun a b => (∃ p q, p ≈ q ∧ a = bind p k1 ∧ b = bind q k2) ∨ a ≈ b, ?_,
    Or.inl ⟨m1, m2, hm, rfl, rfl⟩⟩
  rintro a b (⟨p, q, hpq, rfl, rfl⟩ | hab)
  · have hE := eutt_closed hpq
    clear hpq
    induction hE with
    | ret x =>
      rw [bind_ret, bind_ret]
      exact (eutt_closed (hk x)).mono (fun _ _ h => Or.inr h)
    | fail => rw [bind_fail, bind_fail]; exact .fail
    | vis e kx ky hkk =>
      rw [bind_vis, bind_vis]
      exact .vis e _ _ (fun i => Or.inl ⟨kx i, ky i, hkk i, rfl, rfl⟩)
    | tau tx ty ht =>
      rw [bind_tau, bind_tau]
      exact .tau _ _ (Or.inl ⟨tx, ty, ht, rfl, rfl⟩)
    | tauL tx _ ih => rw [bind_tau]; exact .tauL _ ih
    | tauR ty _ ih => rw [bind_tau]; exact .tauR _ ih
  · exact (eutt_closed hab).mono (fun _ _ h => Or.inr h)

end ITree
end Freigen
