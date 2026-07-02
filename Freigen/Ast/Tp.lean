import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Defs

/-!
# The object-type universe `Tp` and its reified primitive operations

A small, closed universe of the types the dumb AST may mention (`Bool`/`Nat`/`ZMod n`/`Unit`/`×`/
`Vector`/`Array`/`⊕`/`→`), denoted back into Lean by `Tp.denote`, together with the **reified**
primitive operations:

* `Un`/`Bin` — **total** unary/binary primitives (arithmetic, comparison, field ops, tupling,
  projection, injection), denoting to plain Lean functions;
* `POp` — **partial** (proof-erased) primitives (collection get/set, refinement upcasts), denoting
  to `Option`-valued functions — `none` is the erased proof obligation failing, which the single
  `Code.pop` node turns into a *failing* computation.

Reifying primitives into explicit op nodes — rather than embedding opaque Lean functions — is what
lets the AST spill *typed, inspectable* structure into a target.
-/

namespace Freigen

/-- The universe of object-language types the AST may mention. -/
inductive Tp : Type
  | bool : Tp
  | nat : Tp
  | zmod : Nat → Tp
  | unit : Tp
  | prod : Tp → Tp → Tp
  | fn : Tp → Tp → Tp
  | vec : Tp → Nat → Tp
  | array : Tp → Tp
  | sum : Tp → Tp → Tp
  | fin : Nat → Tp

/-- Denote an object type back into Lean.  Reducible so type-class search and unification see
    through it to the underlying Lean type. -/
@[reducible] def Tp.denote : Tp → Type
  | .bool     => Bool
  | .nat      => Nat
  | .zmod n   => ZMod n
  | .unit     => Unit
  | .prod a b => a.denote × b.denote
  | .fn a b   => a.denote → b.denote
  | .vec a n  => Vector a.denote n
  | .array a  => Array a.denote
  | .sum a b  => a.denote ⊕ b.denote
  | .fin n    => Fin n

/-- A heterogeneous list: `HList β [i₀, i₁, …]` holds a `β i₀`, a `β i₁`, ….  Used for the
    argument tuples of (multi-argument) function definitions. -/
inductive HList {ι : Type} (β : ι → Type) : List ι → Type
  | nil : HList β []
  | cons {i is} : β i → HList β is → HList β (i :: is)

/-- The first element of a non-empty `HList`. -/
def HList.head {ι : Type} {β : ι → Type} {i is} : HList β (i :: is) → β i
  | .cons x _ => x
/-- All but the first element of a non-empty `HList`. -/
def HList.tail {ι : Type} {β : ι → Type} {i is} : HList β (i :: is) → HList β is
  | .cons _ xs => xs

/-- Unary primitive operations, indexed by (argument, result) object type. -/
inductive Un : Tp → Tp → Type
  | not : Un .bool .bool
  | fst {a b : Tp} : Un (.prod a b) a
  | snd {a b : Tp} : Un (.prod a b) b
  | inl {a b : Tp} : Un a (.sum a b)
  | inr {a b : Tp} : Un b (.sum a b)
  /-- **Total downcast** `v.toArray` : forget a vector's static length. -/
  | toArray {a : Tp} {n : Nat} : Un (.vec a n) (.array a)
  /-- **Total downcast** `i.val` : forget a `Fin`'s bound. -/
  | finVal {n : Nat} : Un (.fin n) .nat

/-- Binary primitive operations, indexed by (left, right, result) object type. -/
inductive Bin : Tp → Tp → Tp → Type
  | add : Bin .nat .nat .nat
  | sub : Bin .nat .nat .nat
  | mul : Bin .nat .nat .nat
  | pow : Bin .nat .nat .nat
  | eq  : Bin .nat .nat .bool
  | lt  : Bin .nat .nat .bool
  | ble : Bin .nat .nat .bool
  | and : Bin .bool .bool .bool
  | or  : Bin .bool .bool .bool
  | addZ {n : Nat} : Bin (.zmod n) (.zmod n) (.zmod n)
  | subZ {n : Nat} : Bin (.zmod n) (.zmod n) (.zmod n)
  | mulZ {n : Nat} : Bin (.zmod n) (.zmod n) (.zmod n)
  /-- Field power with a `Nat` exponent. -/
  | powZ {n : Nat} : Bin (.zmod n) .nat (.zmod n)
  | pair {a b : Tp} : Bin a b (.prod a b)

/-- Denote a unary primitive to its Lean operation. -/
def Un.denote {a b : Tp} : Un a b → a.denote → b.denote
  | .not, x => !x
  | .fst, p => p.1
  | .snd, p => p.2
  | .inl, x => Sum.inl x
  | .inr, x => Sum.inr x
  | .toArray, v => v.toArray
  | .finVal, i => i.val

/-- Denote a binary primitive to its Lean operation. -/
def Bin.denote {a b c : Tp} : Bin a b c → a.denote → b.denote → c.denote
  | .add,  x, y => x + y
  | .sub,  x, y => x - y
  | .mul,  x, y => x * y
  | .pow,  x, y => x ^ y
  | .eq,   x, y => x == y
  | .lt,   x, y => decide (x < y)
  | .ble,  x, y => decide (x ≤ y)
  | .and,  x, y => x && y
  | .or,   x, y => x || y
  | .addZ, x, y => x + y
  | .subZ, x, y => x - y
  | .mulZ, x, y => x * y
  | .powZ, x, y => x ^ y
  | .pair, x, y => (x, y)

/-- **Partial** primitive operations, indexed by (argument list, result) object types.  These are
    the *proof-erased* primitives — collection get/set and refinement upcasts — whose Lean
    counterparts require a proof (an in-bounds index, a size equality) that the AST drops.  Their
    denotation is `Option`-valued (`none` = the erased obligation fails); the single `Code.pop`
    node turns `none` into a failing computation.  Adding a partial primitive = one constructor
    here + one `denote` arm + one `sexpName` arm + one `sc_*` bridging lemma. -/
inductive POp : List Tp → Tp → Type
  /-- **Vector get** `v[i]` (erased: `i < n`). -/
  | vget {a : Tp} {n : Nat} : POp [.vec a n, .nat] a
  /-- **Vector set** `v[i] := x` (erased: `i < n`). -/
  | vset {a : Tp} {n : Nat} : POp [.vec a n, .nat, a] (.vec a n)
  /-- **Array get** `a[i]` (erased: `i < a.size`). -/
  | aget {a : Tp} : POp [.array a, .nat] a
  /-- **Array set** `a[i] := x` (erased: `i < a.size`). -/
  | aset {a : Tp} : POp [.array a, .nat, a] (.array a)
  /-- **Upcast** `array a → vec a n` (erased: `arr.size = n`). -/
  | arrToVec {a : Tp} {n : Nat} : POp [.array a] (.vec a n)
  /-- **Upcast** `nat → fin n` (erased: `m < n`). -/
  | natToFin {n : Nat} : POp [.nat] (.fin n)
  /-- **Strict select** `c ? x : y` — both branches evaluated, the boolean picks.  Total (its
      denotation is always `some`); lives here so pure `if` needs no continuation duplication. -/
  | select {a : Tp} : POp [.bool, a, a] a

/-- Denote a partial primitive; `none` is the erased proof obligation failing. -/
def POp.denote : {as : List Tp} → {b : Tp} → POp as b → HList Tp.denote as → Option b.denote
  | _, _, @POp.vget _ n, .cons v (.cons i .nil) =>
      if h : i < n then some (v[i]'h) else none
  | _, _, @POp.vset _ n, .cons v (.cons i (.cons x .nil)) =>
      if h : i < n then some (v.set i x h) else none
  | _, _, .aget, .cons v (.cons i .nil) =>
      if h : i < v.size then some (v[i]'h) else none
  | _, _, .aset, .cons v (.cons i (.cons x .nil)) =>
      if h : i < v.size then some (v.set i x h) else none
  | _, _, @POp.arrToVec _ n, .cons arr .nil =>
      if h : arr.size = n then some ⟨arr, h⟩ else none
  | _, _, @POp.natToFin n, .cons m .nil =>
      if h : m < n then some ⟨m, h⟩ else none
  | _, _, .select, .cons c (.cons x (.cons y .nil)) =>
      some (bif c then x else y)

end Freigen
