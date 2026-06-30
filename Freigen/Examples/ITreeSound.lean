import Freigen.Reflect
import Freigen.DenoteITree
import Freigen.Examples.Circuit.Basic

/-!
# The ITree denotation of a reflected program equals the embedded source

A concrete soundness instance for the retargeted denotation: reflect a (terminating, recursion-
free) host program, denote the resulting AST into the interaction-tree domain with `denoteProgI`,
and check it equals `ITree.ofFree` of the original `Free` computation.  For the bounded fragment
this holds definitionally (the ITree carries no `tau`/`fail`), exactly mirroring how the original
`reflect%` soundness is `rfl` — only now in the coinductive domain `Comp`.
-/

namespace Freigen

open ITree

/-- A small host program: a `hint`, then return its result. -/
def hostEx (k : Nat) : Free (Effect CircOp) Nat := do
  let n ← hintF k (fun s => s)
  pure n

/-- Reflect it to a closed AST (`∀ F V, Prog …`). -/
def gEx := reflect% hostEx

/-- **ITree soundness (native interpreter):** denoting the reflected AST directly into `Comp` with
    `denoteProgI` yields the embedding of the source computation. -/
example (k : Nat) :
    denoteProgI (gEx.1 (KleisliFI CircOp) Tp.denote) (.cons k .nil) = ofFree (hostEx k) := by
  unfold gEx
  simp only [denoteProgI, denoteI, hostEx, hintF, bind_ret, denoteValI, Bin.denote, HList.head]
  -- both sides are now `vis (mk hint (k, id)) (fun r => ret r)`; reduce the source `>>= pure`
  show _ = ofFree (Free.Impure (Effect.mk CircOp.hint (k, fun s => s)) Free.Pure)
  rfl

/-- **General ITree soundness (the whole non-recursive language):** for *every* reflected program,
    its interaction-tree meaning — the `Free` denotation embedded by `ofFree` — is the embedding of
    the source.  This holds for all reflected programs at once: it is just `ofFree` applied to the
    existing `reflect%` soundness.  (For a recursive program — which `Free` cannot denote — the
    corresponding result is `ITree.iter_converges`, proved generally in `Freigen.ITree`.) -/
theorem itree_sound_ofFree {mainArgs : List Tp} {τ : Tp}
    {e : HList Tp.denote mainArgs → Free (Effect CircOp) τ.denote}
    {g : Closed CircOp mainArgs τ}
    (h : ∀ args, denoteProg (g (KleisliF CircOp) Tp.denote) args = e args) :
    ∀ args, ofFree (denoteProg (g (KleisliF CircOp) Tp.denote) args) = ofFree (e args) :=
  fun args => congrArg ofFree (h args)

-- e.g. instantiated at the `hostEx` reflection:
example (k : Nat) :
    ofFree (denoteProg (gEx.1 (KleisliF CircOp) Tp.denote) (.cons k .nil)) = ofFree (hostEx k) :=
  congrArg ofFree (gEx.2 k)

end Freigen
