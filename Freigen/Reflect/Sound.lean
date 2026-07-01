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

Each `sc_*` is one node's step of (★); each `L_*`/`Code`-level `rfl` is a pure-atom step.  The whole
per-program proof is a tree of these applied to each other, `Eutt.of_eq`-lifted at the very top.
-/

namespace Freigen
open Freigen.ITree

variable {Op : Type → Type → Type 1} {SOp : Type → Type}

/-- `ITree.bind` distributes over a boolean branch. -/
theorem bind_cond {α β : Type} (c : Bool) (a b : Comp Op α) (k : α → Comp Op β) :
    ITree.bind (cond c a b) k = cond c (ITree.bind a k) (ITree.bind b k) := by cases c <;> rfl

/-! ## Pure-atom steps: the reflected collection nodes carry the source's in-bounds proof -/

/-- **Vector get**, in bounds by the *source's* proof `h`. -/
theorem sc_vget {α elemT : Tp} {n : Nat} (v : Vector elemT.denote n) (i : Nat)
    (kk : elemT.denote → Code Op SOp (KC Op) Tp.denote α) (h : i < n) :
    denote (Code.vget v i kk) = denote (kk (v[i]'h)) := dif_pos h

/-- **Vector set**, in bounds by the source's proof `h`. -/
theorem sc_vset {α elemT : Tp} {n : Nat} (v : Vector elemT.denote n) (i : Nat) (x : elemT.denote)
    (kk : Vector elemT.denote n → Code Op SOp (KC Op) Tp.denote α) (h : i < n) :
    denote (Code.vset v i x kk) = denote (kk (v.set i x h)) := dif_pos h

/-- **Array get**, in bounds by the source's proof `h`. -/
theorem sc_aget {α elemT : Tp} (v : Array elemT.denote) (i : Nat)
    (kk : elemT.denote → Code Op SOp (KC Op) Tp.denote α) (h : i < v.size) :
    denote (Code.aget v i kk) = denote (kk (v[i]'h)) := dif_pos h

/-- **Array set**, in bounds by the source's proof `h`. -/
theorem sc_aset {α elemT : Tp} (v : Array elemT.denote) (i : Nat) (x : elemT.denote)
    (kk : Array elemT.denote → Code Op SOp (KC Op) Tp.denote α) (h : i < v.size) :
    denote (Code.aset v i x kk) = denote (kk (v.set i x h)) := dif_pos h

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

/-- Close off a top-level walk (continuation `mkRet`, so `Kf = ret`): `ITree.bind (ofFree e) ret = ofFree e`. -/
theorem sc_top {α : Tp} (e : Free Op SOp α.denote) (C : Comp Op α.denote)
    (hC : C = ITree.bind (ofFree e) ret) : C = ofFree e := by rw [hC, bind_ret_right]

end Freigen
