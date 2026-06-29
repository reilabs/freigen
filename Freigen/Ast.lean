import Freigen.Free
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Defs

/-!
# A PHOAS A-normal AST for free-monadic programs, with its denotation

**PHOAS** (Parametric Higher-Order Abstract Syntax): object-language binders are Lean binders
over an abstract variable representation `V : Tp → Type` (and functions over `F`).

The AST is indexed by a small *object type universe* `Tp` (booleans, naturals, `ZMod n`, unit,
products, functions), with a denotation `Tp.denote : Tp → Type`.  Programs are in **A-normal
form** (operands are atoms `V _`; results are named via continuations) and consist of a
telescope of pulled-out function definitions (`Prog.def_`) ending in `Prog.main`.  `denote`
interprets a program back into `Free (Effect Op)`.  This file also has a pretty-printer.
-/

namespace Freigen

/-! ## The object type universe -/

/-- The universe of object-language types the AST may mention. -/
inductive Tp : Type
  /-- Booleans. -/
  | bool : Tp
  /-- Naturals. -/
  | nat : Tp
  /-- The integers mod `n`. -/
  | zmod : Nat → Tp
  /-- The unit type. -/
  | unit : Tp
  /-- Product (tuple) types. -/
  | prod : Tp → Tp → Tp
  /-- Function types. -/
  | fn : Tp → Tp → Tp
  /-- Fixed-length vectors `Vector α n`. -/
  | vec : Tp → Nat → Tp
  /-- Dynamic-length arrays `Array α`. -/
  | array : Tp → Tp

/-- Denote an object type back into Lean.  Reducible so that type-class search (e.g.
    `ToString`) and unification see through it to the underlying Lean type. -/
@[reducible] def Tp.denote : Tp → Type
  | .bool     => Bool
  | .nat      => Nat
  | .zmod n   => ZMod n
  | .unit     => Unit
  | .prod a b => a.denote × b.denote
  | .fn a b   => a.denote → b.denote
  | .vec a n  => Vector a.denote n
  | .array a  => Array a.denote

/-- Every object type is inhabited (so a *pure* expression always has a denotable value, and the
    proof-erased `vecGet` has a `default` to fall back on for out-of-range indices). -/
instance instInhabitedDenote : {α : Tp} → Inhabited α.denote
  | .bool     => ⟨false⟩
  | .nat      => ⟨0⟩
  | .zmod _   => ⟨0⟩
  | .unit     => ⟨()⟩
  | .prod a b => ⟨(@default _ (instInhabitedDenote (α := a)), @default _ (instInhabitedDenote (α := b)))⟩
  | .fn _ b   => ⟨fun _ => @default _ (instInhabitedDenote (α := b))⟩
  | .vec a n  => ⟨Vector.replicate n (@default _ (instInhabitedDenote (α := a)))⟩
  | .array _  => ⟨#[]⟩

/-! ## Heterogeneous lists (function argument tuples) -/

/-- A heterogeneous list: `HList β [i₀, i₁, …]` holds a `β i₀`, a `β i₁`, ….  Used for the
    argument lists of (multi-argument) functions. -/
inductive HList {ι : Type} (β : ι → Type) : List ι → Type
  | nil : HList β []
  | cons {i is} : β i → HList β is → HList β (i :: is)

/-- The first element of a non-empty `HList`. -/
def HList.head {ι : Type} {β : ι → Type} {i is} : HList β (i :: is) → β i
  | .cons x _ => x
/-- All but the first element of a non-empty `HList`. -/
def HList.tail {ι : Type} {β : ι → Type} {i is} : HList β (i :: is) → HList β is
  | .cons _ xs => xs

/-! ## Pure primitive operations -/

/-- Unary primitive operations, indexed by (argument, result) object type. -/
inductive Un : Tp → Tp → Type
  | not : Un .bool .bool
  | fst {a b : Tp} : Un (.prod a b) a
  | snd {a b : Tp} : Un (.prod a b) b

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
  /-- Index a vector at a (`Nat`) position.  **Proof-erased**: the index is a plain atom carrying
      no in-bounds proof, so the denotation is *total* — `getElem!`, falling back to the element
      type's `default` on an out-of-range index.  The reflector reconciles this erased access with
      the host's proof-carrying `v[i]'h` by emitting a *bridge* proof (see `Reflect.lean`). -/
  | vecGet {a : Tp} {n : Nat} : Bin (.vec a n) .nat a

/-- Denote a unary primitive to its Lean operation. -/
def Un.denote : Un a b → a.denote → b.denote
  | .not, x => !x
  | .fst, p => p.1
  | .snd, p => p.2

/-- Denote a binary primitive to its Lean operation. -/
def Bin.denote : Bin a b c → a.denote → b.denote → c.denote
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
  | .vecGet, v, i => v[i]!

/-! ## The AST -/

/-- Free-monadic PHOAS programs over an operation signature `Op`, in A-normal form.
    Functions are a second PHOAS variable family `F : List Tp → Tp → Type 1` (`F as b` names
    a function `as → b`, in the same spirit as `V` names values); they are *defined* at the
    top level (see `Prog`), and `call` invokes one by name.  Every operand is an atom (`V _`). -/
inductive Exp (Op : Type → Type → Type 1) (F : List Tp → Tp → Type 1) (V : Tp → Type) : Tp → Type 1
  /-- Tail position: return the atom `v`. -/
  | ret {α : Tp} : V α → Exp Op F V α
  /-- Bind a host literal `n : α.denote` as an atom, then continue. -/
  | lit {α β : Tp} : α.denote → (V α → Exp Op F V β) → Exp Op F V β
  /-- Perform operation `Op I.denote R.denote`: its **input** is the atom `i : V I`, and its
      **result** `R` is bound in the continuation.  The (`Tp`-agnostic) op is instantiated at
      the *denotations* of the object types `I`/`R`, which is how the AST threads typing in. -/
  | op {α I R : Tp} : Op I.denote R.denote → V I → (V R → Exp Op F V α) → Exp Op F V α
  /-- Apply a unary primitive to an atom, binding the result. -/
  | un {α a b : Tp} : Un a b → V a → (V b → Exp Op F V α) → Exp Op F V α
  /-- Apply a binary primitive to two atoms, binding the result. -/
  | bin {α a b c : Tp} : Bin a b c → V a → V b → (V c → Exp Op F V α) → Exp Op F V α
  /-- A bounded `for` loop over `0,…,n-1`: thread the state atom through `n`
      iterations of `body` (index and current state in, new state out), then bind the
      final state into the continuation. -/
  | forN {α s : Tp} : Nat → V s → (V .nat → V s → Exp Op F V s) → (V s → Exp Op F V α) → Exp Op F V α
  /-- Call a bound function on an `HList` of argument atoms, binding its result.  The function
      itself is *not* defined here — it is one of the program's top-level definitions (see
      `Prog`), referenced by its name `F as b`. -/
  | call {α : Tp} {as : List Tp} {b : Tp} :
      F as b → HList V as → (V b → Exp Op F V α) → Exp Op F V α
  /-- A *pure* object-language function value `α → β`.  Its body must be pure (built from
      `ret`/`lit`/`un`/`bin`/`lam`); used e.g. for a `hint`'s evaluator.  Bind it with `letE`. -/
  | lam {α β : Tp} : (V α → Exp Op F V β) → Exp Op F V (.fn α β)
  /-- `let`: name the result of a (sub)expression as an atom, then continue. -/
  | letE {α β : Tp} : Exp Op F V α → (V α → Exp Op F V β) → Exp Op F V β

/-- A whole program: a telescope of (monomorphic) function **definitions** pulled out in front
    of the `main` body.  Each `def_` binds a function-name `F as b` that the rest of the
    program (later definitions and `main`) may `call`; a definition's body cannot mention its
    own name, so programs are non-recursive by construction. -/
inductive Prog (Op : Type → Type → Type 1) (F : List Tp → Tp → Type 1) (V : Tp → Type)
    (mainArgs : List Tp) (α : Tp) : Type 1
  /-- The main body, after all definitions: itself a function of the program's inputs
      `mainArgs` (their atoms delivered as an `HList`). -/
  | main : (HList V mainArgs → Exp Op F V α) → Prog Op F V mainArgs α
  /-- A function definition `as → b` (body taking its arguments as an `HList`), binding its
      name in the rest of the program. -/
  | def_ {as : List Tp} {b : Tp} :
      (HList V as → Exp Op F V b) → (F as b → Prog Op F V mainArgs α) → Prog Op F V mainArgs α

/-- A *closed* program from inputs `mainArgs` to `α`: parametric in the function and variable
    representations. -/
def Closed (Op : Type → Type → Type 1) (mainArgs : List Tp) (α : Tp) : Type 2 :=
  ∀ F V, Prog Op F V mainArgs α

/-- The function representation used by `denote`: a function `as → b` denotes to a Kleisli
    arrow from the denoted argument tuple, `HList Tp.denote as → Free (Effect Op) b.denote`. -/
abbrev KleisliF (Op : Type → Type → Type 1) : List Tp → Tp → Type 1 :=
  fun as b => HList Tp.denote as → Free (Effect Op) b.denote

/-- Denote a **pure** expression directly to its value — used to denote a `lam`'s body to a
    Lean function.  Effectful/looping constructors don't occur in a pure body; they fall to
    `default`. -/
def denoteVal {Op : Type → Type → Type 1} {α : Tp} : Exp Op (KleisliF Op) Tp.denote α → α.denote
  | .ret v       => v
  | .lit n k     => denoteVal (k n)
  | .un o a k    => denoteVal (k (Un.denote o a))
  | .bin o a b k => denoteVal (k (Bin.denote o a b))
  | .lam body    => fun x => denoteVal (body x)
  | .letE e k    => denoteVal (k (denoteVal e))
  | _            => default

/-- Denote an expression to a real `Free (Effect Op)` computation; a `call` applies the
    (already-denoted) function bound by an enclosing `Prog.def_`, and a `lam` denotes to a
    pure Lean function via `denoteVal`. -/
def denote {Op : Type → Type → Type 1} {α : Tp} :
    Exp Op (KleisliF Op) Tp.denote α → Free (Effect Op) α.denote
  | .ret v       => Free.Pure v
  | .lit n k     => denote (k n)
  | .op o i k    => Free.Impure (Effect.mk o i) (fun r => denote (k r))
  | .un o a k    => denote (k (Un.denote o a))
  | .bin o a b k => denote (k (Bin.denote o a b))
  | .forN n init body k =>
    freeBind
      (forIn [0:n] init
        (fun i acc => freeBind (denote (body i acc)) (fun acc' => Free.Pure (ForInStep.yield acc'))))
      (fun acc => denote (k acc))
  | .call cf args k => freeBind (cf args) (fun r => denote (k r))
  | .lam body       => Free.Pure (fun x => denoteVal (body x))
  | .letE e k       => freeBind (denote e) (fun v => denote (k v))

/-- Denote a whole program to a function from its inputs: each `def_` denotes its body to a
    Lean (Kleisli) function and binds it for the rest; `main` denotes to a function of the
    program's input tuple. -/
def denoteProg {Op : Type → Type → Type 1} {mainArgs : List Tp} {α : Tp} :
    Prog Op (KleisliF Op) Tp.denote mainArgs α → HList Tp.denote mainArgs → Free (Effect Op) α.denote
  | .main body   => fun args => denote (body args)
  | .def_ body k => denoteProg (k (fun a => denote (body a)))

/-! ## A pretty-printer (instantiating `V := fun _ => String`) -/

/-- Render a host literal of object type `α` for the pretty-printer.  Scalars print
    their value; functions (and `ZMod`, lacking a uniform `ToString`) print a placeholder. -/
def Tp.toStr : (α : Tp) → α.denote → String
  | .bool,     b => toString b
  | .nat,      n => toString n
  | .zmod n,   x => s!"{x.val}#{n}"          -- residue `#` modulus
  | .unit,     _ => "()"
  | .prod a b, p => s!"({Tp.toStr a p.1}, {Tp.toStr b p.2})"
  | .fn _ _,   _ => "<fn>"
  | .vec a _,  v => "#v[" ++ String.intercalate ", " (v.toList.map (Tp.toStr a)) ++ "]"
  | .array a,  v => "#[" ++ String.intercalate ", " (v.toList.map (Tp.toStr a)) ++ "]"

/-- Render an object *type* for the pretty-printer (`ZMod n` prints as `Field<n>`). -/
def Tp.toTypeStr : Tp → String
  | .bool     => "Bool"
  | .nat      => "Nat"
  | .zmod n   => s!"Field<{n}>"
  | .unit     => "Unit"
  | .prod a b => s!"({a.toTypeStr} × {b.toTypeStr})"
  | .fn a b   => s!"({a.toTypeStr} → {b.toTypeStr})"
  | .vec a n  => s!"Vector<{a.toTypeStr}, {n}>"
  | .array a  => s!"Array<{a.toTypeStr}>"

/-- Symbol for a unary primitive, for the pretty-printer. -/
def Un.sym : Un a b → String
  | .not => "!" | .fst => ".1 " | .snd => ".2 "

/-- Symbol for a binary primitive, for the pretty-printer. -/
def Bin.sym : Bin a b c → String
  | .add => "+" | .sub => "-" | .mul => "*" | .pow => "^" | .eq => "==" | .and => "&&" | .or => "||"
  | .addZ => "+" | .subZ => "-" | .mulZ => "*" | .pair => "," | .vecGet => "[]"

/-- Indentation (two spaces per nesting level) for the pretty-printer. -/
private def ppIndent (d : Nat) : String := String.join (List.replicate d "  ")

/-- Value representation for pretty-printing: every atom is its name string. -/
abbrev PpV : Tp → Type := fun _ => String
/-- Function representation for pretty-printing: a function name (in `Type 1` via
    `ULift`, to match `Exp`'s `F : List Tp → Tp → Type 1`). -/
abbrev PpF : List Tp → Tp → Type 1 := fun _ _ => ULift String

/-- Collect the name strings out of a pretty-printing argument `HList`. -/
def hlistStrings : {as : List Tp} → HList PpV as → List String
  | [],    .nil       => []
  | _::_,  .cons x xs => x :: hlistStrings xs

/-- A fresh argument `HList` of names `x{i}, x{i+1}, …` for a pretty-printed function body. -/
def freshHList : (as : List Tp) → Nat → HList PpV as × Nat
  | [],    i => (.nil, i)
  | _::as, i => let (xs, j) := freshHList as (i + 1); (.cons s!"x{i}" xs, j)

/-- Render a typed binder list `x0 : T0, x1 : T1, …` from argument names and their types. -/
def ppBinders (as : List Tp) (argv : HList PpV as) : String :=
  String.intercalate ", " ((hlistStrings argv).zip (as.map Tp.toTypeStr) |>.map
    (fun (n, t) => s!"{n} : {t}"))

/-- Worker for `pp`, threading the nesting depth `d` (for indentation) and a fresh-name
    counter `i`.  Every binding is emitted on its own line at depth `d`; `forN`/`letFun`
    bodies are rendered one level deeper.  Note the `op`/`call` cases can render their
    operands directly — only possible because they are now atoms (here, `String`s). -/
private def ppAux {Op : Type → Type → Type 1} {α : Tp}
    (name : {I R : Type} → Op I R → String) :
    Nat → Nat → Exp Op PpF PpV α → (String × Nat)
  | d, i, .ret v => (s!"{ppIndent d}{v}", i)
  | d, i, @Exp.lit _ _ _ α _ val k =>
    let v := s!"v{i}"
    let i := i + 1
    let (rest, i) := ppAux name d i (k v)
    (s!"{ppIndent d}let {v} := {Tp.toStr α val}\n{rest}", i)
  | d, i, .letE (.lam body) k =>
    -- the common shape: `let v := λ x => …`
    let arg := s!"x{i}"
    let i := i + 1
    let (b, i) := ppAux name (d + 1) i (body arg)
    let v := s!"v{i}"
    let i := i + 1
    let (rest, i) := ppAux name d i (k v)
    (s!"{ppIndent d}let {v} := λ {arg} =>\n{b}\n{rest}", i)
  | d, i, .letE e k =>
    let (eStr, i) := ppAux name d i e
    let v := s!"v{i}"
    let i := i + 1
    let (rest, i) := ppAux name d i (k v)
    (s!"{ppIndent d}let {v} :=\n{eStr}\n{rest}", i)
  | d, i, .lam body =>
    let arg := s!"x{i}"
    let i := i + 1
    let (b, i) := ppAux name (d + 1) i (body arg)
    (s!"{ppIndent d}λ {arg} =>\n{b}", i)
  | d, i, .op o inp k =>
    let v := s!"v{i}"
    let i := i + 1
    let (rest, i) := ppAux name d i (k v)
    (s!"{ppIndent d}let {v} ← {name o}({inp})\n{rest}", i)
  | d, i, .un o a k =>
    let v := s!"v{i}"
    let i := i + 1
    let (rest, i) := ppAux name d i (k v)
    (s!"{ppIndent d}let {v} := {Un.sym o}{a}\n{rest}", i)
  | d, i, .bin o a b k =>
    let v := s!"v{i}"
    let i := i + 1
    let (rest, i) := ppAux name d i (k v)
    -- `pair` reads better as a tuple than as an infix `,`
    let rhs := if Bin.sym o == "," then s!"({a}, {b})"
               else if Bin.sym o == "[]" then s!"{a}[{b}]"
               else s!"{a} {Bin.sym o} {b}"
    (s!"{ppIndent d}let {v} := {rhs}\n{rest}", i)
  | d, i, .forN n init body k =>
    let iv := s!"i{i}"
    let av := s!"a{i}"
    let i := i + 1
    let (b, i) := ppAux name (d + 1) i (body iv av)
    let v := s!"v{i}"
    let i := i + 1
    let (rest, i) := ppAux name d i (k v)
    (s!"{ppIndent d}let {v} := forN {n} from {init} via λ {iv} {av} =>\n{b}\n{rest}", i)
  | d, i, .call cf args k =>
    let v := s!"v{i}"
    let i := i + 1
    let (rest, i) := ppAux name d i (k v)
    (s!"{ppIndent d}let {v} := {cf.down}({String.intercalate ", " (hlistStrings args)})\n{rest}", i)

/-- Worker for `pp` over a whole `Prog`: print each pulled-out function definition (`f{i} = λ
    … => …`), then the `main` body. -/
private def ppProgAux {Op : Type → Type → Type 1} {mainArgs : List Tp} {α : Tp}
    (name : {I R : Type} → Op I R → String) :
    Nat → Prog Op PpF PpV mainArgs α → (String × Nat)
  | i, @Prog.main _ _ _ mainArgs _ body =>
    let (argv, i) := freshHList _ i
    let (b, i) := ppAux name 1 i (body argv)
    (s!"def main({ppBinders mainArgs argv}) =>\n{b}", i)
  | i, @Prog.def_ _ _ _ _ _ as _ body k =>
    let f := s!"f{i}"
    let i := i + 1
    let (argv, i) := freshHList _ i
    let (b, i) := ppAux name 1 i (body argv)
    let (rest, i) := ppProgAux name i (k (ULift.up f))
    (s!"def {f}({ppBinders as argv}) =>\n{b}\n{rest}", i)

/-- Pretty-print a whole program: the function definitions, then `def main`. -/
def pp {Op : Type → Type → Type 1} {mainArgs : List Tp} {α : Tp}
    (name : {I R : Type} → Op I R → String) (p : Prog Op PpF PpV mainArgs α) : String :=
  (ppProgAux name 0 p).1

end Freigen
