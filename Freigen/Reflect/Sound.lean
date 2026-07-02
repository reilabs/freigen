import Freigen.Ast
import Freigen.Free
import Freigen.ITree

/-!
# Compositional soundness lemmas for the reflector

The reflector builds its `≈`-soundness proof **structurally**, mirroring the source term: as it walks
a `Free` program it emits, at every node, an equation

```
denote C = ITree.bind (ofFree e) Kf          -- (★)
```

(`Kf` = the denotation of the reflected continuation), assembled from the equation of the sub-terms
by the congruence lemma for that node.  This is what lets a proof-erased `vget`/`vset`/`aget`/`aset`
carry the *actual* in-bounds proof from the source (`sc_vget … (h : i < n)` is literally `dif_pos h`)
— no `simp`, no decidability, no reachability of a hypothesis: the proof term mirrors the term.

Each `sc_*` is one node's step of (★); every other `Code` node's step is definitional (`rfl`).  The
whole per-program proof is a tree of these applied to each other, `Eutt.of_eq`-lifted at the very top.
-/

namespace Freigen
open Freigen.ITree

variable {Op : Type → Type → Type 1} {SOp : Type → Type}

/-- `ITree.bind` distributes over a boolean branch. -/
theorem bind_cond {α β : Type} (c : Bool) (a b : Comp Op α) (k : α → Comp Op β) :
    ITree.bind (cond c a b) k = cond c (ITree.bind a k) (ITree.bind b k) := by cases c <;> rfl

/-! ## Pure-atom steps: the reflected partial-op nodes carry the source's proof

`sc_pop` is the one generic step; each per-op `sc_*` bridges the source's proof (`h : i < n`, …) to
`POp.denote … = some v` (a `dif_pos`).  A new `POp` needs exactly one bridging lemma here. -/

/-- Generic **partial-op step**: when the op's denotation succeeds, the `pop` node steps to its
    continuation — the erased `fail` branch is closed by `h`. -/
theorem sc_pop {α b : Tp} {as : List Tp} (o : POp as b) (args : HList Tp.denote as)
    {v : b.denote} (kk : b.denote → Code Op SOp (KC Op) Tp.denote α)
    (h : POp.denote o args = some v) :
    denote (Code.pop o args kk) = denote (kk v) := by
  simp only [denote]
  rw [h]

/-- **Vector get**, in bounds by the *source's* proof `h`. -/
theorem sc_vget {α a : Tp} {n : Nat} (v : Vector a.denote n) (i : Nat)
    (kk : a.denote → Code Op SOp (KC Op) Tp.denote α) (h : i < n) :
    denote (Code.pop .vget (.cons v (.cons i .nil)) kk) = denote (kk (v[i]'h)) :=
  sc_pop .vget (.cons v (.cons i .nil)) kk (by exact dif_pos h)

/-- **Vector set**, in bounds by the source's proof `h`. -/
theorem sc_vset {α a : Tp} {n : Nat} (v : Vector a.denote n) (i : Nat) (x : a.denote)
    (kk : Vector a.denote n → Code Op SOp (KC Op) Tp.denote α) (h : i < n) :
    denote (Code.pop .vset (.cons v (.cons i (.cons x .nil))) kk) = denote (kk (v.set i x h)) :=
  sc_pop .vset (.cons v (.cons i (.cons x .nil))) kk (by exact dif_pos h)

/-- **Array get**, in bounds by the source's proof `h`. -/
theorem sc_aget {α a : Tp} (v : Array a.denote) (i : Nat)
    (kk : a.denote → Code Op SOp (KC Op) Tp.denote α) (h : i < v.size) :
    denote (Code.pop .aget (.cons v (.cons i .nil)) kk) = denote (kk (v[i]'h)) :=
  sc_pop .aget (.cons v (.cons i .nil)) kk (by exact dif_pos h)

/-- **Array set**, in bounds by the source's proof `h`. -/
theorem sc_aset {α a : Tp} (v : Array a.denote) (i : Nat) (x : a.denote)
    (kk : Array a.denote → Code Op SOp (KC Op) Tp.denote α) (h : i < v.size) :
    denote (Code.pop .aset (.cons v (.cons i (.cons x .nil))) kk) = denote (kk (v.set i x h)) :=
  sc_pop .aset (.cons v (.cons i (.cons x .nil))) kk (by exact dif_pos h)

/-- **Upcast `array → vec n`**, valid by the source's length proof `h : arr.size = n`. -/
theorem sc_arrToVec {α a : Tp} {n : Nat} (arr : Array a.denote)
    (kk : Vector a.denote n → Code Op SOp (KC Op) Tp.denote α) (h : arr.size = n) :
    denote (Code.pop .arrToVec (.cons arr .nil) kk) = denote (kk ⟨arr, h⟩) :=
  sc_pop .arrToVec (.cons arr .nil) kk (by exact dif_pos h)

/-- **Upcast `nat → fin n`**, valid by the source's bound proof `h : m < n`. -/
theorem sc_natToFin {α : Tp} {n : Nat} (m : Nat)
    (kk : Fin n → Code Op SOp (KC Op) Tp.denote α) (h : m < n) :
    denote (Code.pop .natToFin (.cons m .nil) kk) = denote (kk ⟨m, h⟩) :=
  sc_pop .natToFin (.cons m .nil) kk (by exact dif_pos h)

/-! ## Node steps of the invariant (★) -/

/-- A `pure a` reflected via its continuation: `Kf a`, un-bound by `bind_ret`. -/
theorem sc_pure {X : Type} {α : Tp} (a : X) (C : Comp Op α.denote) (Kf : X → Comp Op α.denote)
    (hC : C = Kf a) : C = ITree.bind (ofFree (@Free.pure Op SOp X a)) Kf := by
  rw [show (ofFree (@Free.pure Op SOp X a) : Comp Op X) = ret a from rfl, ITree.bind_ret]; exact hC

/-- An effect `op`: `vis`-congruence, its continuation given by the IH. -/
theorem sc_op {I R α : Tp} {X : Type} (o : Op I.denote R.denote) (i : I.denote)
    (c : R.denote → Free Op SOp X) (kbody : R.denote → Code Op SOp (KC Op) Tp.denote α)
    (Kf : X → Comp Op α.denote)
    (ih : ∀ r, denote (kbody r) = ITree.bind (ofFree (c r)) Kf) :
    denote (Code.op o i kbody) = ITree.bind (ofFree (Free.op o i c)) Kf := by
  show vis (Effect.mk o i) (fun r => denote (kbody r)) = ITree.bind (ofFree (Free.op o i c)) Kf
  rw [show ofFree (Free.op o i c) = vis (Effect.mk o i) (fun r => ofFree (c r)) from rfl, bind_vis]
  exact congrArg _ (funext ih)

/-- A `ITree.bind x f`: the walk's fused form `C` matched to the source's `ITree.bind`-`ITree.bind`, via
    `ofFree_bind` + associativity. -/
theorem sc_bind {X Y : Type} {α : Tp} (x : Free Op SOp Y) (f : Y → Free Op SOp X)
    (Kf : X → Comp Op α.denote) (C : Comp Op α.denote)
    (hC : C = ITree.bind (ofFree x) (fun r => ITree.bind (ofFree (f r)) Kf)) :
    C = ITree.bind (ofFree (Free.bind x f)) Kf := by
  rw [hC, ofFree_bind, bind_assoc]

/-- A boolean branch: `ITree.bind` distributes over `cond`, each arm given by its IH. -/
theorem sc_cond {X : Type} {α : Tp} (c : Bool) (t e : Free Op SOp X)
    (T E : Code Op SOp (KC Op) Tp.denote α) (Kf : X → Comp Op α.denote)
    (iht : denote T = ITree.bind (ofFree t) Kf) (ihe : denote E = ITree.bind (ofFree e) Kf) :
    denote (Code.ite c T E) = ITree.bind (ofFree (cond c t e)) Kf := by
  show cond c (denote T) (denote E) = ITree.bind (ofFree (cond c t e)) Kf
  rw [ofFree_cond, bind_cond, iht, ihe]

/-- A scoped block `hop s b cont`: the block runs inline (`hB : denote B = ofFree b`), the tail by
    the IH; assembled by associativity. -/
theorem sc_scope {β α : Tp} {X : Type} (s : SOp β.denote) (b : Free Op SOp β.denote)
    (cont : β.denote → Free Op SOp X) (B : Code Op SOp (KC Op) Tp.denote β)
    (K' : β.denote → Code Op SOp (KC Op) Tp.denote α) (Kf : X → Comp Op α.denote)
    (hB : denote B = ofFree b)
    (ih : ∀ x, denote (K' x) = ITree.bind (ofFree (cont x)) Kf) :
    denote (Code.scope s B K') = ITree.bind (ofFree (Free.hop s b cont)) Kf := by
  show ITree.bind (denote B) (fun x => denote (K' x)) = ITree.bind (ofFree (Free.hop s b cont)) Kf
  rw [show ofFree (Free.hop s b cont) = ITree.bind (ofFree b) (fun x => ofFree (cont x)) from rfl,
      bind_assoc, hB]
  exact congrArg _ (funext ih)

/-- A call to a helper subroutine: the subroutine's denotation `cf args` is equal to the source's
    `ofFree` by the helper's own (★)-proof (`hcf`); the continuation passes through `ITree.bind`. -/
theorem sc_call {as : List Tp} {b α : Tp}
    (cf : HList Tp.denote as → Comp Op b.denote) (args : HList Tp.denote as)
    (K' : b.denote → Code Op SOp (KC Op) Tp.denote α) (m : Comp Op b.denote) (hcf : cf args = m) :
    denote (Code.call cf args K') = ITree.bind m (fun r => denote (K' r)) := by
  show ITree.bind (cf args) (fun r => denote (K' r)) = ITree.bind m (fun r => denote (K' r))
  rw [hcf]

end Freigen
