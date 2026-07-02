import Freigen.Ast.Tp
import Freigen.Ast.Basic

/-!
# A uniform S-expression serialization of `Prog`

**The** printer: `sexp` renders a closed `Prog` into a fully-parenthesized, prefix,
type-annotated S-expression — the format the `#compile` facet writes to `.prog` files and the Rust
SDK (`rust/`) parses back into a client-side AST.

Design rules that make it trivial to parse:

* every construct is a parenthesized list with a fixed keyword head — no infix syntax, no
  significant whitespace (indentation is cosmetic);
* every `let` binder is annotated with its object type, so a consumer can type every value without
  inference;
* everything is a bare token — variables, keywords, numbers, and names (`def` names, custom
  op/scope names: their grammatical position disambiguates them, so they need no quoting).
  Double-quoted strings are *reserved* for guest-language string literals, should `Tp` ever grow
  them.

## Grammar

```
program ::= (program decl*)
decl    ::= (def NAME params TYPE block)       ; a top-level function definition
          | (rec NAME params TYPE block)       ; a recursive definition (exactly one parameter)
          | (main params TYPE block)           ; the entry point
params  ::= ((VAR TYPE)*)
block   ::= (block stmt* term)
stmt    ::= (let VAR TYPE expr)
term    ::= (ret VAR)
          | (if VAR block block)               ; branch in tail position
expr    ::= (lit VALUE)                        ; a host literal
          | (un UNOP VAR)                      ; total unary primitive
          | (bin BINOP VAR VAR)                ; total binary primitive
          | (pop POP VAR*)                     ; partial (proof-erased) primitive — may fail
          | (vec VAR*)                         ; vector construction
          | (arr VAR*)                         ; array construction
          | (fold NAT VAR (IVAR AVAR) block)   ; bounded fold: trip count, init, (index, acc) block
          | (vgen NAT (IVAR) block)            ; bounded generator (Vector.ofFn)
          | (op NAME VAR)                      ; a custom first-order effect (client-interpreted)
          | (self VAR)                         ; the self-call inside a rec body
          | (call NAME VAR*)                   ; call a top-level definition
          | (scope NAME block)                 ; a scoped construct carrying an in-monad block
TYPE    ::= bool | nat | unit
          | (zmod NAT) | (fin NAT) | (vec TYPE NAT) | (array TYPE)
          | (prod TYPE TYPE) | (sum TYPE TYPE) | (fn TYPE TYPE)
VALUE   ::= true | false | NAT | unit | opaque
          | (pair VALUE VALUE) | (vec VALUE*) | (array VALUE*) | (inl VALUE) | (inr VALUE)
UNOP    ::= not | fst | snd | inl | inr | to-array | fin-val
BINOP   ::= add | sub | mul | pow | eq | lt | le | and | or
          | addf | subf | mulf | powf | pair
POP     ::= vget | vset | aget | aset | select | (arr-to-vec NAT) | (nat-to-fin NAT)
```

Numeric `VALUE`s are plain decimal and are typed by the annotation on their binder (`nat`,
`(zmod p)` — the canonical representative — or `(fin n)`).  A `(fn …)`-typed literal has no
serializable payload and renders as `opaque`.
-/

namespace Freigen

/-- Render an object type as an S-expression. -/
def Tp.toSexp : Tp → String
  | .bool     => "bool"
  | .nat      => "nat"
  | .zmod n   => s!"(zmod {n})"
  | .unit     => "unit"
  | .prod a b => s!"(prod {a.toSexp} {b.toSexp})"
  | .fn a b   => s!"(fn {a.toSexp} {b.toSexp})"
  | .vec a n  => s!"(vec {a.toSexp} {n})"
  | .array a  => s!"(array {a.toSexp})"
  | .sum a b  => s!"(sum {a.toSexp} {b.toSexp})"
  | .fin n    => s!"(fin {n})"

/-- Render a host literal of object type `α` as an S-expression value.  Scalars are typed by their
    binder's annotation; a function literal has no serializable payload (`opaque`). -/
def Tp.toSexpVal : (α : Tp) → α.denote → String
  | .bool,     b => toString b
  | .nat,      n => toString n
  | .zmod _,   x => toString x.val
  | .unit,     _ => "unit"
  | .prod a b, p => s!"(pair {a.toSexpVal p.1} {b.toSexpVal p.2})"
  | .fn _ _,   _ => "opaque"
  | .vec a _,  v => "(vec" ++ String.join (v.toList.map (fun x => " " ++ a.toSexpVal x)) ++ ")"
  | .array a,  v => "(array" ++ String.join (v.toList.map (fun x => " " ++ a.toSexpVal x)) ++ ")"
  | .sum a b,  x => match x with
                    | .inl y => s!"(inl {a.toSexpVal y})"
                    | .inr y => s!"(inr {b.toSexpVal y})"
  | .fin _,    i => toString i.val

/-- S-expression keyword for a unary primitive. -/
def Un.sexpName {a b : Tp} : Un a b → String
  | .not => "not" | .fst => "fst" | .snd => "snd" | .inl => "inl" | .inr => "inr"
  | .toArray => "to-array" | .finVal => "fin-val"

/-- S-expression keyword for a binary primitive (`ZMod` arithmetic gets its own `…f` names, so a
    consumer needs no type dispatch). -/
def Bin.sexpName {a b c : Tp} : Bin a b c → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .pow => "pow"
  | .eq => "eq" | .lt => "lt" | .ble => "le" | .and => "and" | .or => "or"
  | .addZ => "addf" | .subZ => "subf" | .mulZ => "mulf" | .powZ => "powf"
  | .pair => "pair"

/-- S-expression head for a partial primitive — the upcasts carry their target bound. -/
def POp.sexpName : {as : List Tp} → {b : Tp} → POp as b → String
  | _, _, .vget => "vget" | _, _, .vset => "vset"
  | _, _, .aget => "aget" | _, _, .aset => "aset"
  | _, _, @POp.arrToVec _ n => s!"(arr-to-vec {n})"
  | _, _, @POp.natToFin n  => s!"(nat-to-fin {n})"
  | _, _, .select => "select"

/-- Value representation for serialization: every atom is its variable name. -/
abbrev SexpV : Tp → Type := fun _ => String
/-- Function representation for serialization: a definition is its display name. -/
abbrev SexpF : List Tp → Tp → Type 1 := fun _ _ => ULift String

namespace Sexp

private def ind (d : Nat) : String := String.join (List.replicate d "  ")

private def hlistStrings : {as : List Tp} → HList SexpV as → List String
  | [],    .nil       => []
  | _::_,  .cons x xs => x :: hlistStrings xs

private def freshHList : (as : List Tp) → Nat → HList SexpV as × Nat
  | [],    i => (.nil, i)
  | _::as, i => let (xs, j) := freshHList as (i + 1); (.cons s!"x{i}" xs, j)

private def params (as : List Tp) (argv : HList SexpV as) : String :=
  "(" ++ String.intercalate " "
    ((hlistStrings argv).zip (as.map Tp.toSexp) |>.map (fun (n, t) => s!"({n} {t})")) ++ ")"

/-- Wrap statement lines (already indented at `d + 1`) into a `(block …)` at depth `d`. -/
private def blockAt (d : Nat) (stmts : String) : String :=
  ind d ++ "(block\n" ++ stmts ++ ")"

/-- Serialize a `Code` chain into statement lines at depth `d` (a fresh-name counter `i` threads
    through).  `opE` renders an op node applied to its argument atom —
    parameterized so a `rec_` body can render the `CallOp.call` self-call structurally. -/
private def sCode {Op : Type → Type → Type 1} {SOp : Type → Type} {α : Tp}
    (opE : {I R : Type} → Op I R → String → String) (sname : {β : Type} → SOp β → String) :
    Nat → Nat → Code Op SOp SexpF SexpV α → (String × Nat)
  | d, i, .ret v => (s!"{ind d}(ret {v})", i)
  | d, i, @Code.lit _ _ _ _ β _ a k =>
      let v := s!"v{i}"; let (r, j) := sCode opE sname d (i+1) (k v)
      (s!"{ind d}(let {v} {β.toSexp} (lit {β.toSexpVal a}))\n{r}", j)
  | d, i, @Code.un _ _ _ _ _ _ b o a k =>
      let v := s!"v{i}"; let (r, j) := sCode opE sname d (i+1) (k v)
      (s!"{ind d}(let {v} {b.toSexp} (un {o.sexpName} {a}))\n{r}", j)
  | d, i, @Code.bin _ _ _ _ _ _ _ c o a b k =>
      let v := s!"v{i}"; let (r, j) := sCode opE sname d (i+1) (k v)
      (s!"{ind d}(let {v} {c.toSexp} (bin {o.sexpName} {a} {b}))\n{r}", j)
  | d, i, @Code.pop _ _ _ _ _ _ b o args k =>
      let v := s!"v{i}"; let (r, j) := sCode opE sname d (i+1) (k v)
      let argStr := String.join ((hlistStrings args).map (" " ++ ·))
      (s!"{ind d}(let {v} {b.toSexp} (pop {o.sexpName}{argStr}))\n{r}", j)
  | d, i, @Code.vec _ _ _ _ _ a n elems k =>
      let v := s!"v{i}"; let (r, j) := sCode opE sname d (i+1) (k v)
      let argStr := String.join (elems.toList.map (" " ++ ·))
      (s!"{ind d}(let {v} {(Tp.vec a n).toSexp} (vec{argStr}))\n{r}", j)
  | d, i, @Code.arr _ _ _ _ _ a elems k =>
      let v := s!"v{i}"; let (r, j) := sCode opE sname d (i+1) (k v)
      let argStr := String.join (elems.map (" " ++ ·))
      (s!"{ind d}(let {v} {(Tp.array a).toSexp} (arr{argStr}))\n{r}", j)
  | d, i, @Code.fold _ _ _ _ _ a n init body k =>
      let iv := s!"i{i}"; let av := s!"a{i+1}"
      let (bs, j) := sCode opE sname (d+2) (i+2) (body iv av)
      let v := s!"v{j}"; let (r, l) := sCode opE sname d (j+1) (k v)
      (s!"{ind d}(let {v} {a.toSexp} (fold {n} {init} ({iv} {av})\n{blockAt (d+1) bs}))\n{r}", l)
  | d, i, @Code.vgen _ _ _ _ _ a n body k =>
      let iv := s!"i{i}"
      let (bs, j) := sCode opE sname (d+2) (i+1) (body iv)
      let v := s!"v{j}"; let (r, l) := sCode opE sname d (j+1) (k v)
      (s!"{ind d}(let {v} {(Tp.vec a n).toSexp} (vgen {n} ({iv})\n{blockAt (d+1) bs}))\n{r}", l)
  | d, i, @Code.op _ _ _ _ _ _ R o inp k =>
      let v := s!"v{i}"; let (r, j) := sCode opE sname d (i+1) (k v)
      (s!"{ind d}(let {v} {R.toSexp} {opE o inp})\n{r}", j)
  | d, i, .ite c t e =>
      let (ts, j) := sCode opE sname (d+2) i t
      let (es, j) := sCode opE sname (d+2) j e
      (s!"{ind d}(if {c}\n{blockAt (d+1) ts}\n{blockAt (d+1) es})", j)
  | d, i, @Code.call _ _ _ _ _ _ b cf args k =>
      let v := s!"v{i}"; let (r, j) := sCode opE sname d (i+1) (k v)
      let argStr := String.join ((hlistStrings args).map (" " ++ ·))
      (s!"{ind d}(let {v} {b.toSexp} (call {cf.down}{argStr}))\n{r}", j)
  | d, i, @Code.scope _ _ _ _ _ β s b k =>
      let (bs, j) := sCode opE sname (d+2) i b
      let v := s!"v{j}"; let (r, l) := sCode opE sname d (j+1) (k v)
      (s!"{ind d}(let {v} {β.toSexp} (scope {sname s}\n{blockAt (d+1) bs}))\n{r}", l)

private def sProg {Op : Type → Type → Type 1} {SOp : Type → Type} {mainArgs : List Tp} {α : Tp}
    (name : {I R : Type} → Op I R → String) (sname : {β : Type} → SOp β → String) :
    Nat → Prog Op SOp SexpF SexpV mainArgs α → (String × Nat)
  | i, @Prog.main _ _ _ _ mainArgs α body =>
      let (argv, i) := freshHList mainArgs i
      let opE : {I R : Type} → Op I R → String → String := fun o a => s!"(op {name o} {a})"
      let (b, i) := sCode opE sname 3 i (body argv)
      (s!"{ind 1}(main {params mainArgs argv} {α.toSexp}\n{blockAt 2 b})", i)
  | i, @Prog.def_ _ _ _ _ _ _ as b nm body k =>
      let (argv, i) := freshHList as i
      let opE : {I R : Type} → Op I R → String → String := fun o a => s!"(op {name o} {a})"
      let (bs, i) := sCode opE sname 3 i (body argv)
      let (rest, i) := sProg name sname i (k (ULift.up nm))
      (s!"{ind 1}(def {nm} {params as argv} {b.toSexp}\n{blockAt 2 bs})\n{rest}", i)
  | i, @Prog.rec_ _ _ _ _ _ _ arg res nm body k =>
      let x := s!"x{i}"; let i := i + 1
      let opE : {I R : Type} → Freigen.ITree.CallOp Op arg.denote res.denote I R →
          String → String := fun o a => match o with
        | .base o' => s!"(op {name o'} {a})"
        | .call    => s!"(self {a})"
      let (bs, i) := sCode opE sname 3 i (body SexpF x)
      let (rest, i) := sProg name sname i (k (ULift.up nm))
      (s!"{ind 1}(rec {nm} {params [arg] (.cons x .nil)} {res.toSexp}\n{blockAt 2 bs})\n{rest}", i)

end Sexp

/-- Serialize a closed program into the uniform S-expression format (grammar in this module's
    docstring) — the machine-facing sibling of `pp`. -/
def sexp {Op : Type → Type → Type 1} {SOp : Type → Type}
    (name : {I R : Type} → Op I R → String) (sname : {β : Type} → SOp β → String)
    {mainArgs : List Tp} {α : Tp} (c : Closed Op SOp mainArgs α) : String :=
  "(program\n" ++ (Sexp.sProg name sname 0 (c SexpF SexpV)).1 ++ ")\n"

end Freigen
