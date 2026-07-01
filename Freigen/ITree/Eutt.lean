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
theorem eutt_refl (x : Comp Op α) : Eutt x x :=
  ⟨Eq, fun _ _ h => h ▸ euttF_diag (fun _ => rfl) _, rfl⟩

theorem Eutt.of_eq {x y : Comp Op α} (h : x = y) : Eutt x y := h ▸ eutt_refl x

/-- A leading `tau` can be stripped: `tau t ≈ t`. -/
theorem eutt_tau (t : Comp Op α) : Eutt (tau t) t := by
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
theorem eutt_closed {x y : Comp Op α} (h : Eutt x y) : EuttF Eutt x y := by
  obtain ⟨R, hR, hxy⟩ := h
  exact (hR x y hxy).mono (fun a b hab => ⟨R, hR, hab⟩)

/-- Strip a leading `tau` on the left while keeping the relation: `x ≈ y → tau x ≈ y`. -/
theorem eutt_tau_left {x y : Comp Op α} (h : Eutt x y) : Eutt (tau x) y := by
  refine ⟨fun a b => (a = tau x ∧ b = y) ∨ Eutt a b, ?_, Or.inl ⟨rfl, rfl⟩⟩
  rintro a b (⟨rfl, rfl⟩ | hab)
  · exact .tauL x ((eutt_closed h).mono (fun _ _ h => Or.inr h))
  · exact (eutt_closed hab).mono (fun _ _ h => Or.inr h)

/-- `vis`-congruence: related continuations give related `vis` nodes. -/
theorem eutt_vis_cong {β : Type} (e : Effect Op β) {k1 k2 : β → Comp Op α}
    (h : ∀ i, Eutt (k1 i) (k2 i)) : Eutt (vis e k1) (vis e k2) := by
  refine ⟨fun a b => (a = vis e k1 ∧ b = vis e k2) ∨ Eutt a b, ?_, Or.inl ⟨rfl, rfl⟩⟩
  rintro a b (⟨rfl, rfl⟩ | hab)
  · exact .vis e k1 k2 (fun i => Or.inr (h i))
  · exact (eutt_closed hab).mono (fun _ _ h => Or.inr h)

/-- **`bind`-congruence for `≈`**: bisimilar prefixes with pointwise-bisimilar continuations give
    bisimilar binds.  Proved by bisimulation, casing on the prefix relation by *induction* on one
    `EuttF`-step (so the finitely-many leading `tau`s of the prefix are stripped). -/
theorem eutt_bind_cong {β : Type} {m1 m2 : Comp Op α} {k1 k2 : α → Comp Op β}
    (hm : Eutt m1 m2) (hk : ∀ x, Eutt (k1 x) (k2 x)) : Eutt (bind m1 k1) (bind m2 k2) := by
  refine ⟨fun a b => (∃ p q, Eutt p q ∧ a = bind p k1 ∧ b = bind q k2) ∨ Eutt a b, ?_,
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

/-! ## Symmetry and transitivity

`Eutt` is symmetric (flip the bisimulation) and transitive.  Transitivity is the hard coinductive
lemma: simple induction on the two one-step relations gets stuck on the `tau`/`tauL` interleaving,
so we go through leading-`tau` cancellation (`eutt_untau_left/right`), finite `tau`-stripping
(`Strip`), and head-matching (`match_ret`/`match_fail`/`match_vis`), then assemble.  The `ret`/`tau`/
`vis`/`fail` constructors are `def`s over `M.mk`, so the inversions use `dest`-based injectivity. -/

theorem EuttF.symm {R : Comp Op α → Comp Op α → Prop} {x y} (h : EuttF R x y) :
    EuttF (fun a b => R b a) y x := by
  induction h with
  | ret a => exact .ret a
  | fail => exact .fail
  | vis e kx ky hk => exact .vis e ky kx (fun i => hk i)
  | tau tx ty ht => exact .tau ty tx ht
  | tauL tx _ ih => exact .tauR tx ih
  | tauR ty _ ih => exact .tauL ty ih

theorem Eutt.symm {x y : Comp Op α} (h : Eutt x y) : Eutt y x := by
  obtain ⟨R, hR, hxy⟩ := h
  exact ⟨fun a b => R b a, fun a b hab => (hR b a hab).symm, hxy⟩

theorem dfst {x y : Comp Op α} (h : x = y) : x.dest.1 = y.dest.1 := by rw [h]
theorem tau_inj {s t : Comp Op α} (h : tau s = tau t) : s = t := by
  have := congrArg PFunctor.M.dest h; rw [dest_tau, dest_tau] at this
  injection this with _ hc; exact congrFun hc PUnit.unit
theorem ret_inj {a b : α} (h : (ret a : Comp Op α) = ret b) : a = b := by
  have := dfst h; rw [dest_ret, dest_ret] at this; exact Pos.ret.inj this

theorem eutt_untau_left {x y : Comp Op α} (h : Eutt (tau x) y) : Eutt x y := by
  obtain ⟨R, hR, h0⟩ := h
  refine ⟨fun a b => R a b ∨ R (tau a) b, ?_, Or.inr h0⟩
  have key : ∀ w b, EuttF R w b → ∀ a, w = tau a → EuttF (fun a b => R a b ∨ R (tau a) b) a b := by
    intro w b hwb
    induction hwb with
    | ret c => intro a hw; exact absurd (dfst hw) (by simp)
    | fail => intro a hw; exact absurd (dfst hw) (by simp)
    | vis e kx ky _ => intro a hw; exact absurd (dfst hw) (by simp)
    | tau ta tb ht => intro a hw; obtain rfl := tau_inj hw
                      exact .tauR tb ((hR ta tb ht).mono (fun _ _ h => Or.inl h))
    | tauL tx h' _ => intro a hw; obtain rfl := tau_inj hw
                      exact h'.mono (fun _ _ h => Or.inl h)
    | tauR tb h' ih => intro a hw; exact .tauR tb (ih a hw)
  rintro a b (hab | hab)
  · exact (hR a b hab).mono (fun _ _ h => Or.inl h)
  · exact key (tau a) b (hR (tau a) b hab) a rfl

theorem eutt_untau_right {x y : Comp Op α} (h : Eutt x (tau y)) : Eutt x y :=
  (eutt_untau_left h.symm).symm

inductive Strip : Comp Op α → Comp Op α → Prop
  | refl (x : Comp Op α) : Strip x x
  | tau {t y : Comp Op α} : Strip t y → Strip (tau t) y

theorem euttF_strip_left {R : Comp Op α → Comp Op α → Prop} {x x' z}
    (s : Strip x x') (h : EuttF R x' z) : EuttF R x z := by
  induction s with
  | refl _ => exact h
  | tau _ ih => exact .tauL _ (ih h)
theorem euttF_strip_right {R : Comp Op α → Comp Op α → Prop} {x z z'}
    (s : Strip z z') (h : EuttF R x z') : EuttF R x z := by
  induction s with
  | refl _ => exact h
  | tau _ ih => exact .tauR _ (ih h)

theorem vis_inj {β1 β2 : Type} {e1 : Effect Op β1} {k1 : β1 → Comp Op α}
    {e2 : Effect Op β2} {k2 : β2 → Comp Op α} (h : vis e1 k1 = vis e2 k2) :
    β1 = β2 ∧ HEq e1 e2 ∧ HEq k1 k2 := by
  have := congrArg PFunctor.M.dest h; rw [dest_vis, dest_vis] at this
  injection this with hp hc; injection hp with hb he; exact ⟨hb, he, hc⟩

theorem match_ret {a : α} {x y : Comp Op α} (hxy : Eutt x y) (s : Strip x (ret a)) :
    Strip y (ret a) := by
  generalize hu : (ret a : Comp Op α) = u at s ⊢
  induction s generalizing y with
  | refl _ =>
    subst hu
    obtain ⟨R, hR, h0⟩ := hxy
    have key : ∀ w z, EuttF R w z → w = ret a → Strip z (ret a) := by
      intro w z hwz
      induction hwz with
      | ret b => intro hw; obtain rfl := ret_inj hw; exact .refl _
      | fail => intro hw; exact absurd (dfst hw) (by simp)
      | vis e kx ky _ => intro hw; exact absurd (dfst hw) (by simp)
      | tau ta tb _ => intro hw; exact absurd (dfst hw) (by simp)
      | tauL tx _ _ => intro hw; exact absurd (dfst hw) (by simp)
      | tauR tb _ ih => intro hw; exact .tau (ih hw)
    exact key (ret a) y (hR _ _ h0) rfl
  | tau s' ih => exact ih (eutt_untau_left hxy) hu

theorem match_fail {x y : Comp Op α} (hxy : Eutt x y) (s : Strip x fail) :
    Strip y fail := by
  generalize hu : (fail : Comp Op α) = u at s ⊢
  induction s generalizing y with
  | refl _ =>
    subst hu
    obtain ⟨R, hR, h0⟩ := hxy
    have key : ∀ w z, EuttF R w z → w = (fail : Comp Op α) → Strip z fail := by
      intro w z hwz
      induction hwz with
      | ret b => intro hw; exact absurd (dfst hw) (by simp)
      | fail => intro hw; exact .refl _
      | vis e kx ky _ => intro hw; exact absurd (dfst hw) (by simp)
      | tau ta tb _ => intro hw; exact absurd (dfst hw) (by simp)
      | tauL tx _ _ => intro hw; exact absurd (dfst hw) (by simp)
      | tauR tb _ ih => intro hw; exact .tau (ih hw)
    exact key fail y (hR _ _ h0) rfl
  | tau s' ih => exact ih (eutt_untau_left hxy) hu

theorem match_vis {β : Type} {e : Effect Op β} {k : β → Comp Op α} {x y : Comp Op α}
    (hxy : Eutt x y) (s : Strip x (vis e k)) :
    ∃ k', Strip y (vis e k') ∧ ∀ i, Eutt (k i) (k' i) := by
  generalize hu : (vis e k : Comp Op α) = u at s ⊢
  induction s generalizing y with
  | refl _ =>
    subst hu
    obtain ⟨R, hR, h0⟩ := hxy
    have key : ∀ w z, EuttF R w z → w = vis e k →
        ∃ k', Strip z (vis e k') ∧ ∀ i, R (k i) (k' i) := by
      intro w z hwz
      induction hwz with
      | ret b => intro hw; exact absurd (dfst hw) (by simp)
      | fail => intro hw; exact absurd (dfst hw) (by simp)
      | tau ta tb _ => intro hw; exact absurd (dfst hw) (by simp)
      | tauL tx _ _ => intro hw; exact absurd (dfst hw) (by simp)
      | vis e2 kx ky hkk =>
          intro hw
          obtain ⟨rfl, he, hk⟩ := vis_inj hw
          obtain rfl := eq_of_heq he
          obtain rfl := eq_of_heq hk
          exact ⟨ky, .refl _, hkk⟩
      | tauR tb _ ih => intro hw; obtain ⟨k', hs, hk⟩ := ih hw; exact ⟨k', .tau hs, hk⟩
    obtain ⟨k', hs, hk⟩ := key (vis e k) y (hR _ _ h0) rfl
    exact ⟨k', hs, fun i => ⟨R, hR, hk i⟩⟩
  | tau s' ih => exact ih (eutt_untau_left hxy) hu

theorem Eutt.trans {x y z : Comp Op α} (hxy : Eutt x y) (hyz : Eutt y z) : Eutt x z := by
  refine ⟨fun a c => ∃ b, Eutt a b ∧ Eutt b c, ?_, ⟨y, hxy, hyz⟩⟩
  rintro a c ⟨b, hab, hbc⟩
  rcases cases_view a with ⟨v, rfl⟩ | rfl | ⟨t, rfl⟩ | ⟨β, e, k, rfl⟩
  · exact euttF_strip_right (match_ret hbc (match_ret hab (.refl _))) (.ret v)
  · exact euttF_strip_right (match_fail hbc (match_fail hab (.refl _))) .fail
  · rcases cases_view c with ⟨v, rfl⟩ | rfl | ⟨tc, rfl⟩ | ⟨γ, ec, kc, rfl⟩
    · exact euttF_strip_left (match_ret hab.symm (match_ret hbc.symm (.refl _))) (.ret v)
    · exact euttF_strip_left (match_fail hab.symm (match_fail hbc.symm (.refl _))) .fail
    · exact .tau t tc ⟨b, eutt_untau_left hab, eutt_untau_right hbc⟩
    · obtain ⟨kb, sb, hkb⟩ := match_vis hbc.symm (.refl _)
      obtain ⟨kt, st, hkt⟩ := match_vis hab.symm sb
      exact euttF_strip_left st (.vis ec kt kc (fun i => ⟨kb i, (hkt i).symm, (hkb i).symm⟩))
  · obtain ⟨kb, sb, hkb⟩ := match_vis hab (.refl _)
    obtain ⟨kc, sc, hkc⟩ := match_vis hbc sb
    exact euttF_strip_right sc (.vis e k kc (fun i => ⟨kb i, hkb i, hkc i⟩))


/-! ## `Eutt` is an equivalence: the `Setoid` instance

With reflexivity, symmetry, and transitivity in hand, weak bisimulation is a genuine equivalence
relation, so `Comp Op α` is a lawful `Setoid` and `≈` supports `calc`/`Trans`. -/

instance : Setoid (Comp Op α) where
  r := Eutt
  iseqv := ⟨eutt_refl, Eutt.symm, Eutt.trans⟩

instance : Trans (@Eutt Op α) (@Eutt Op α) (@Eutt Op α) := ⟨Eutt.trans⟩

end ITree
end Freigen
