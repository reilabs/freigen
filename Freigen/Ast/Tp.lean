import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Defs

/-!
# The object-type universe `Tp` and its reified primitive operations

A small, closed universe of the types the dumb AST may mention (`Bool`/`Nat`/`ZMod n`/`Unit`/`×`/
`Vector`/`Array`/`⊕`/`→`), denoted back into Lean by `Tp.denote`, together with the **reified**
unary/binary primitive operations `Un`/`Bin` (arithmetic, comparison, field ops, tupling, projection,
injection).  Collection get/set are *not* here — being proof-erased and *partial* (an out-of-range
index fails), they live as dedicated `Code` nodes denoting into `Comp`, not as total `Bin` ops.
Reifying arithmetic into explicit op nodes — rather than embedding
opaque Lean functions — is what lets the AST spill *typed, inspectable* structure into a target.
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
  | and : Bin .bool .bool .bool
  | or  : Bin .bool .bool .bool
  | addZ {n : Nat} : Bin (.zmod n) (.zmod n) (.zmod n)
  | subZ {n : Nat} : Bin (.zmod n) (.zmod n) (.zmod n)
  | mulZ {n : Nat} : Bin (.zmod n) (.zmod n) (.zmod n)
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
  | .and,  x, y => x && y
  | .or,   x, y => x || y
  | .addZ, x, y => x + y
  | .subZ, x, y => x - y
  | .mulZ, x, y => x * y
  | .pair, x, y => (x, y)

/-! ## Pretty-printing helpers -/

/-- Render a host literal of object type `α` (scalars print their value; functions print a
    placeholder). -/
def Tp.toStr : (α : Tp) → α.denote → String
  | .bool,     b => toString b
  | .nat,      n => toString n
  | .zmod n,   x => s!"{x.val}#{n}"
  | .unit,     _ => "()"
  | .prod a b, p => s!"({Tp.toStr a p.1}, {Tp.toStr b p.2})"
  | .fn _ _,   _ => "<fn>"
  | .vec a _,  v => "#v[" ++ String.intercalate ", " (v.toList.map (Tp.toStr a)) ++ "]"
  | .array a,  v => "#[" ++ String.intercalate ", " (v.toList.map (Tp.toStr a)) ++ "]"
  | .sum a b,  x => match x with
                    | .inl y => s!"inl {Tp.toStr a y}"
                    | .inr y => s!"inr {Tp.toStr b y}"
  | .fin _,    i => toString i.val

/-- Render an object *type* (`ZMod n` prints as `Field<n>`). -/
def Tp.toTypeStr : Tp → String
  | .bool     => "Bool"
  | .nat      => "Nat"
  | .zmod n   => s!"Field<{n}>"
  | .unit     => "Unit"
  | .prod a b => s!"({a.toTypeStr} × {b.toTypeStr})"
  | .fn a b   => s!"({a.toTypeStr} → {b.toTypeStr})"
  | .vec a n  => s!"Vector<{a.toTypeStr}, {n}>"
  | .array a  => s!"Array<{a.toTypeStr}>"
  | .sum a b  => s!"({a.toTypeStr} ⊕ {b.toTypeStr})"
  | .fin n    => s!"Fin<{n}>"

/-- Symbol for a unary primitive. -/
def Un.sym {a b : Tp} : Un a b → String
  | .not => "!" | .fst => ".1 " | .snd => ".2 " | .inl => "inl " | .inr => "inr "
  | .toArray => ".toArray " | .finVal => ".val "

/-- Symbol for a binary primitive. -/
def Bin.sym {a b c : Tp} : Bin a b c → String
  | .add => "+" | .sub => "-" | .mul => "*" | .pow => "^" | .eq => "==" | .and => "&&" | .or => "||"
  | .addZ => "+" | .subZ => "-" | .mulZ => "*" | .pair => ","

end Freigen
