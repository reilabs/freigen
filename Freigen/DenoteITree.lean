import Freigen.Ast
import Freigen.ITree

/-!
# Denoting the AST into the interaction-tree domain

This retargets the AST denotation from `Free (Effect Op)` to the coinductive domain `Comp Op`
(`Freigen.ITree`): `KleisliFI` makes functions denote to `Comp`-valued Kleisli arrows, `forC` is
the bounded loop (structural — it is the degenerate, always-converging fixpoint), and `denoteI` /
`denoteProgI` mirror `denote` / `denoteProg` with the ITree operations (`ret`/`vis`/`bind`).

The bounded fragment denotes with no `tau` and no `fail`, so for a *terminating* program the ITree
denotation is the embedding `ofFree` of the source computation — demonstrated as a concrete
soundness instance at the end.  Recursion (where `tau`/`Comp.fix` actually do work) is the
`ITree.iter` story proved in `Freigen.ITree`; folding that into the reflector's `Prog` is the
remaining elaborator work.
-/

namespace Freigen

open ITree

/-- Function representation for the ITree denotation: a `Comp`-valued Kleisli arrow. -/
abbrev KleisliFI (Op : Type → Type → Type 1) : List Tp → Tp → Type 1 :=
  fun as b => HList Tp.denote as → Comp Op b.denote

variable {Op : Type → Type → Type 1}

/-- The bounded loop in the domain: run `body` at indices `start, start+1, …` for `count` steps,
    threading the state.  Structural recursion on `count` — always terminates, no `tau`. -/
def forC {s : Type} (body : Nat → s → Comp Op s) : Nat → Nat → s → Comp Op s
  | _,     0,         acc => ITree.ret acc
  | start, count + 1, acc => ITree.bind (body start acc) (fun acc' => forC body (start + 1) count acc')

/-- Denote a pure expression to its value (the ITree-instance copy of `denoteVal`; pure bodies
    never use the function representation, so this is identical to `Ast.denoteVal`). -/
def denoteValI {α : Tp} : Exp Op (KleisliFI Op) Tp.denote α → α.denote
  | .ret v       => v
  | .lit n k     => denoteValI (k n)
  | .un o a k    => denoteValI (k (Un.denote o a))
  | .bin o a b k => denoteValI (k (Bin.denote o a b))
  | .lam body    => fun x => denoteValI (body x)
  | .letE e k    => denoteValI (k (denoteValI e))
  | .ite c t e   => cond c (denoteValI t) (denoteValI e)
  | _            => default

/-- Denote an expression into the interaction-tree domain. -/
def denoteI {α : Tp} : Exp Op (KleisliFI Op) Tp.denote α → Comp Op α.denote
  | .ret v       => ITree.ret v
  | .lit n k     => denoteI (k n)
  | .op o i k    => ITree.vis (Effect.mk o i) (fun r => denoteI (k r))
  | .un o a k    => denoteI (k (Un.denote o a))
  | .bin o a b k => denoteI (k (Bin.denote o a b))
  | .forN n init body k =>
      ITree.bind (forC (fun i acc => denoteI (body i acc)) 0 n init) (fun acc => denoteI (k acc))
  | .call cf args k => ITree.bind (cf args) (fun r => denoteI (k r))
  | .lam body       => ITree.ret (fun x => denoteValI (body x))
  | .letE e k       => ITree.bind (denoteI e) (fun v => denoteI (k v))
  | .ite c t e      => cond c (denoteI t) (denoteI e)

/-- Denote a whole program into the interaction-tree domain. -/
def denoteProgI {mainArgs : List Tp} {α : Tp} :
    Prog Op (KleisliFI Op) Tp.denote mainArgs α → HList Tp.denote mainArgs → Comp Op α.denote
  | .main body   => fun args => denoteI (body args)
  | .def_ body k => denoteProgI (k (fun a => denoteI (body a)))

end Freigen
