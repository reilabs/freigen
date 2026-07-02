import Freigen.Free
import Freigen.Ast.Tp
import Freigen.ITree

/-!
# The AST: syntax and denotation

`Code`/`Prog` is a dumb, typed imperative AST indexed by the object types `Tp`: instructions, reified
arithmetic (`un`/`bin`), boolean branches, **calls to top-level function definitions** (`call` +
`Prog.def_`/`Prog.rec_`), and scoped blocks.  It is PHOAS over a function family `F` and values `V`,
with the effect signatures `Op`/`SOp` opaque.

`denoteProg` gives it meaning **uniformly in the interaction-tree domain `Comp`**: a function denotes
as a `Comp`-Kleisli subroutine, and a recursive definition is tied by `mrec` — so a `Prog` cannot be
mapped into a finite monad (the AST does not assume termination).  `ofFree` embeds the *source* `Free`
program into `Comp`, which is what a reflected `Prog` is compared against.  A pretty-printer renders a
closed `Prog` for inspection.
-/

namespace Freigen

open Freigen.ITree

/-- ITree semantics of a source `Free` program: a scoped block is *run* inline (`bind`). -/
def ofFree {Op : Type → Type → Type 1} {SOp : Type → Type} :
    {α : Type} → Free Op SOp α → Comp Op α
  | _, .pure a    => ret a
  | _, .op o i k  => vis (Effect.mk o i) (fun r => ofFree (k r))
  | _, .hop _ b k => ITree.bind (ofFree b) (fun x => ofFree (k x))

/-- `ofFree` is a **monad morphism**: it commutes with `bind`. -/
theorem ofFree_bind {Op : Type → Type → Type 1} {SOp : Type → Type} {α β}
    (m : Free Op SOp α) (k : α → Free Op SOp β) :
    ofFree (Free.bind m k) = ITree.bind (ofFree m) (fun x => ofFree (k x)) := by
  induction m with
  | pure a => simp only [Free.bind, ofFree, ITree.bind_ret]
  | op o i c ih =>
      simp only [Free.bind, ofFree, ITree.bind_vis]
      exact congrArg (vis (Effect.mk o i)) (funext fun r => ih r k)
  | hop s b c _ ihc =>
      simp only [Free.bind, ofFree, ITree.bind_assoc]
      exact congrArg (ITree.bind (ofFree b)) (funext fun x => ihc x k)

/-- `ofFree` distributes over a boolean branch (needed to align `denote`'s `ite`/`cond` with the
    source, without splitting the surrounding equality). -/
theorem ofFree_cond {Op : Type → Type → Type 1} {SOp : Type → Type} {α}
    (c : Bool) (a b : Free Op SOp α) :
    ofFree (cond c a b) = cond c (ofFree a) (ofFree b) := by cases c <;> rfl

/-- The dumb, typed imperative AST.  `F as b` names a top-level function `as → b`; `V α` an atom. -/
inductive Code (Op : Type → Type → Type 1) (SOp : Type → Type)
    (F : List Tp → Tp → Type 1) (V : Tp → Type) : Tp → Type 1
  | ret   {α} : V α → Code Op SOp F V α
  | lit   {α β} : α.denote → (V α → Code Op SOp F V β) → Code Op SOp F V β
  | un    {α a b} : Un a b → V a → (V b → Code Op SOp F V α) → Code Op SOp F V α
  | bin   {α a b c} : Bin a b c → V a → V b → (V c → Code Op SOp F V α) → Code Op SOp F V α
  /-- A **partial primitive** (`POp`: collection get/set, refinement upcasts), *proof-erased*: the
      arguments carry no proof (an index is a plain `Nat`), so a failing obligation (out-of-range,
      size mismatch — `POp.denote … = none`) **fails** in the denotation. -/
  | pop   {α as b} : POp as b → HList V as → (V b → Code Op SOp F V α) → Code Op SOp F V α
  /-- **Vector construction** `#v[e₀, …, eₙ₋₁]` from `n` element atoms.  The atoms are held as a
      `Vector (V a) n`, which at `V := Tp.denote` *is* the object vector — so its denotation is trivial. -/
  | vec   {α a n} : Vector (V a) n → (V (.vec a n) → Code Op SOp F V α) → Code Op SOp F V α
  /-- **Array construction** `#[e₀, …, eₙ₋₁]` from element atoms (a `List (V a)`). -/
  | arr   {α a} : List (V a) → (V (.array a) → Code Op SOp F V α) → Code Op SOp F V α
  | op    {α I R} : Op I.denote R.denote → V I → (V R → Code Op SOp F V α) → Code Op SOp F V α
  | ite   {α} : V .bool → Code Op SOp F V α → Code Op SOp F V α → Code Op SOp F V α
  | call  {α as b} : F as b → HList V as → (V b → Code Op SOp F V α) → Code Op SOp F V α
  | scope {α β} : SOp β.denote → Code Op SOp F V β → (V β → Code Op SOp F V α) → Code Op SOp F V α

/-- A whole program: a telescope of pulled-out function **definitions** (`def_`) ending in `main`.
    Each `def_` binds a function name `F as b` the rest may `call`. -/
inductive Prog (Op : Type → Type → Type 1) (SOp : Type → Type)
    (F : List Tp → Tp → Type 1) (V : Tp → Type) (mainArgs : List Tp) (α : Tp) : Type 2
  | main : (HList V mainArgs → Code Op SOp F V α) → Prog Op SOp F V mainArgs α
  | def_ {as b} : (HList V as → Code Op SOp F V b) →
      (F as b → Prog Op SOp F V mainArgs α) → Prog Op SOp F V mainArgs α
  /-- A **recursive** function definition `arg → res`.  Its body lives over the **call-extended
      signature** `CallOp Op` — a self-call is the `CallOp.call` operation — so it may recur in any
      position; it is denoted by `mrec`.  The body is parametric in `F` (it reaches the recursive
      knot through `call`, not through a name).  This node's very existence makes a total `Prog →
      Free` map **impossible to define** (no `mrec` in an inductive monad): the AST can't promise
      termination. -/
  | rec_ {arg res} :
      (∀ F', V arg → Code (CallOp Op arg.denote res.denote) SOp F' V res) →
      (F [arg] res → Prog Op SOp F V mainArgs α) → Prog Op SOp F V mainArgs α

/-- A closed program, parametric in the function/value representations. -/
def Closed (Op : Type → Type → Type 1) (SOp : Type → Type) (mainArgs : List Tp) (α : Tp) : Type 2 :=
  ∀ F V, Prog Op SOp F V mainArgs α

/-- Comp-Kleisli: a function `as → b` denotes as a **subroutine in the interaction-tree domain**. -/
abbrev KC (Op : Type → Type → Type 1) : List Tp → Tp → Type 1 :=
  fun as b => HList Tp.denote as → Comp Op b.denote

/-- **The AST's meaning** — denote a `Code` *uniformly* into the interaction-tree domain `Comp`
    (`V := Tp.denote`, `F := KC`).  A `call` binds a subroutine's result, a scoped block runs inline;
    nothing here knows or cares whether the program (or a callee) is recursive. -/
def denote {Op : Type → Type → Type 1} {SOp : Type → Type} :
    {α : Tp} → Code Op SOp (KC Op) Tp.denote α → Comp Op α.denote
  | _, .ret v      => ret v
  | _, .lit a k    => denote (k a)
  | _, .un o a k   => denote (k (Un.denote o a))
  | _, .bin o a b k => denote (k (Bin.denote o a b))
  | _, .pop o args k => match POp.denote o args with
      | some v => denote (k v)
      | none   => fail
  | _, .vec elems k => denote (k elems)
  | _, .arr elems k => denote (k elems.toArray)
  | _, .op o i k   => vis (Effect.mk o i) (fun r => denote (k r))
  | _, .ite c t e  => cond c (denote t) (denote e)
  | _, .call cf args k => ITree.bind (cf args) (fun r => denote (k r))
  | _, .scope _ b k => ITree.bind (denote b) (fun x => denote (k x))

/-- Denote a whole program into `Comp` — **uniformly**: `main` denotes to a function of the inputs,
    a `def_` binds its body's `Comp`-subroutine, and a **`rec_` ties the recursive knot with `mrec`**.
    There is deliberately no `Free`-valued analogue: `mrec` has no inductive counterpart, so a `Prog`
    cannot be denoted into a finite monad — the AST does not (and cannot) assume termination. -/
def denoteProg {Op : Type → Type → Type 1} {SOp : Type → Type} {mainArgs : List Tp} {α : Tp} :
    Prog Op SOp (KC Op) Tp.denote mainArgs α → HList Tp.denote mainArgs → Comp Op α.denote
  | .main body   => fun args => denote (body args)
  | .def_ body k => denoteProg (k (fun a => denote (body a)))
  | @Prog.rec_ _ _ _ _ _ _ arg res body k =>
      denoteProg (k (fun args =>
        mrec (fun s => denote (body (KC (CallOp Op arg.denote res.denote)) s)) (HList.head args)))

/-! ## A pretty-printer -/

abbrev PpV : Tp → Type := fun _ => String
abbrev PpF : List Tp → Tp → Type 1 := fun _ _ => ULift String
private def ppIndent (d : Nat) : String := String.join (List.replicate d "  ")

private def hlistStrings : {as : List Tp} → HList PpV as → List String
  | [],    .nil       => []
  | _::_,  .cons x xs => x :: hlistStrings xs

private def freshHList : (as : List Tp) → Nat → HList PpV as × Nat
  | [],    i => (.nil, i)
  | _::as, i => let (xs, j) := freshHList as (i + 1); (.cons s!"x{i}" xs, j)

private def ppBinders (as : List Tp) (argv : HList PpV as) : String :=
  String.intercalate ", " ((hlistStrings argv).zip (as.map Tp.toTypeStr) |>.map
    (fun (n, t) => s!"{n} : {t}"))

private def ppCode {Op : Type → Type → Type 1} {SOp : Type → Type} {α : Tp}
    (name : {I R : Type} → Op I R → String) (sname : {β : Type} → SOp β → String) :
    Nat → Nat → Code Op SOp PpF PpV α → (String × Nat)
  | d, i, .ret v      => (s!"{ppIndent d}{v}", i)
  | d, i, @Code.lit _ _ _ _ α _ a k =>
      let v := s!"v{i}"; let (r, j) := ppCode name sname d (i+1) (k v)
      (s!"{ppIndent d}let {v} := {Tp.toStr α a}\n{r}", j)
  | d, i, .un o a k =>
      let v := s!"v{i}"; let (r, j) := ppCode name sname d (i+1) (k v)
      (s!"{ppIndent d}let {v} := {Un.sym o}{a}\n{r}", j)
  | d, i, .bin o a b k =>
      let v := s!"v{i}"
      let rhs := if Bin.sym o == "," then s!"({a}, {b})" else s!"{a} {Bin.sym o} {b}"
      let (r, j) := ppCode name sname d (i+1) (k v)
      (s!"{ppIndent d}let {v} := {rhs}\n{r}", j)
  | d, i, .pop o args k =>
      let v := s!"v{i}"; let (r, j) := ppCode name sname d (i+1) (k v)
      (s!"{ppIndent d}let {v} := {POp.render o args}\n{r}", j)
  | d, i, .vec elems k =>
      let v := s!"v{i}"; let (r, j) := ppCode name sname d (i+1) (k v)
      (s!"{ppIndent d}let {v} := #v[{String.intercalate ", " elems.toList}]\n{r}", j)
  | d, i, .arr elems k =>
      let v := s!"v{i}"; let (r, j) := ppCode name sname d (i+1) (k v)
      (s!"{ppIndent d}let {v} := #[{String.intercalate ", " elems}]\n{r}", j)
  | d, i, .op o inp k =>
      let v := s!"v{i}"; let (r, j) := ppCode name sname d (i+1) (k v)
      (s!"{ppIndent d}let {v} ← {name o}({inp})\n{r}", j)
  | d, i, .ite c t e =>
      let (ts, j) := ppCode name sname (d+1) i t; let (es, j) := ppCode name sname (d+1) j e
      (s!"{ppIndent d}if {c} then\n{ts}\n{ppIndent d}else\n{es}", j)
  | d, i, .call cf args k =>
      let v := s!"v{i}"; let (r, j) := ppCode name sname d (i+1) (k v)
      (s!"{ppIndent d}let {v} := {cf.down}({String.intercalate ", " (hlistStrings args)})\n{r}", j)
  | d, i, .scope s b k =>
      let (bs, j) := ppCode name sname (d+1) i b
      let v := s!"v{j}"; let (r, l) := ppCode name sname d (j+1) (k v)
      (s!"{ppIndent d}let {v} ← {sname s} unconstrained\n{bs}\n{r}", l)

private def ppProg {Op : Type → Type → Type 1} {SOp : Type → Type} {mainArgs : List Tp} {α : Tp}
    (name : {I R : Type} → Op I R → String) (sname : {β : Type} → SOp β → String) :
    Nat → Prog Op SOp PpF PpV mainArgs α → (String × Nat)
  | i, @Prog.main _ _ _ _ mainArgs _ body =>
      let (argv, i) := freshHList mainArgs i
      let (b, i) := ppCode name sname 1 i (body argv)
      (s!"def main({ppBinders mainArgs argv}) =>\n{b}", i)
  | i, @Prog.def_ _ _ _ _ _ _ as _ body k =>
      let f := s!"f{i}"; let i := i + 1
      let (argv, i) := freshHList as i
      let (b, i) := ppCode name sname 1 i (body argv)
      let (rest, i) := ppProg name sname i (k (ULift.up f))
      (s!"def {f}({ppBinders as argv}) =>\n{b}\n{rest}", i)
  | i, @Prog.rec_ _ _ _ _ _ _ arg res body k =>
      let f := s!"f{i}"; let x := s!"x{i+1}"; let i := i + 2
      let callName : {I R : Type} → Freigen.ITree.CallOp Op arg.denote res.denote I R → String :=
        fun o => match o with | .base o' => name o' | .call => s!"{f} (self-call)"
      let (b, i) := ppCode callName sname 1 i (body PpF x)
      let (rest, i) := ppProg name sname i (k (ULift.up f))
      (s!"rec {f}({x} : {arg.toTypeStr}) =>\n{b}\n{rest}", i)

/-- Pretty-print a closed program. -/
def pp {Op : Type → Type → Type 1} {SOp : Type → Type}
    (name : {I R : Type} → Op I R → String) (sname : {β : Type} → SOp β → String)
    {mainArgs : List Tp} {α : Tp} (c : Closed Op SOp mainArgs α) : String :=
  (ppProg name sname 0 (c PpF PpV)).1

end Freigen
