import Freigen.Ast.Defs

/-!
Printing AST programs as S-expressions. Programs are instantiated with
strings for variables, so binders are named while printing. A continuation
chain prints as a sequence of statements, `(let x e)`, rather than as nested
terms, so long programs stay flat.

The printed form is meant to be parsed back, so it carries every type that
cannot be inferred bottom-up from variables already in scope: literal types,
the element type of `arrEmpty`, parameter types, and the context and output
type of definitions and the entry point. The rest follows from these and the
signature: builtin results from their arguments, branch and loop results from
their bodies and initial values, and operation and block types from the
operation's tag. Blocks are named, so they need no fixed order.

The grammar, in EBNF over tokens: parentheses and atoms, separated by
whitespace, which is otherwise insignificant.

```
program  = "(" "program" { define } main ")" ;
define   = "(" "define" var ctx param tp stmts ")" ;
main     = "(" "main" ctx param tp stmts ")" ;
param    = "(" var tp ")" ;
stmts    = { let } ret ;
let      = "(" "let" var rhs ")" ;
ret      = "(" "ret" var ")" ;
body     = ret | "(" "do" let { let } ret ")" ;
rhs      = "(" "lit" tp val ")"
         | "(" "arrEmpty" tp ")"
         | "(" builtin { var } ")"
         | "(" "fun" param stmts ")"
         | "(" "app" var var ")"
         | "(" "if" var body body ")"
         | "(" "loop" var "(" "fun" param stmts ")" ")"
         | "(" "op" tag var { block } ")" ;
block    = "(" "block" name "(" var ")" stmts ")" ;
builtin  = "uAdd" | "uSub" | "uMul" | "uDiv" | "uMod" | "uEq" | "uLt" | "uLe"
         | "not" | "and" | "or" | "bEq" | "pair" | "fst" | "snd"
         | "arrPush" | "arrGet" | "arrSet" | "arrLen" ;
tp       = "u32" | "bool" | "unit" | "(" "array" tp ")"
         | "(" "prod" tp tp ")" | "(" "fn" tp tp ")" ;
val      = digit { digit } | "true" | "false" | "(" ")"
         | "(" "array" { val } ")" | "(" "pair" val val ")" ;
var      = ( "v" | "f" ) digit { digit } ;
ctx      = atom ;  (* a context name of the signature *)
tag      = atom ;  (* an operation name of the signature *)
name     = atom ;  (* a block name of the operation *)
```

Variables are `f` for function types and `v` otherwise, numbered in reading
order, so each is bound once. A definition's name is in scope in its own body
and in everything after it, a parameter in its body, and a `let`-bound
variable in the statements after it, including nested ones. A `val` has the
shape of its literal's type, with `u32` values in decimal.
-/

namespace Freigen.Ast

inductive Sexp
| atom (s : String)
| list (xs : List Sexp)

namespace Sexp

partial def flat : Sexp → String
| atom s => s
| list xs => "(" ++ " ".intercalate (xs.map flat) ++ ")"

/-- Print within `width` columns where possible. A list that does not fit
keeps its head and its first `hang head` children on the first line, and puts
each remaining child on its own line, indented by two. -/
partial def pretty (s : Sexp) (hang : String → Option Nat := fun _ => none)
    (width : Nat := 80) : String :=
  go 0 s
where
  go (ind : Nat) (s : Sexp) : String :=
    let f := s.flat
    if ind + f.length ≤ width then f else
    match s with
    | atom a => a
    | list [] => "()"
    | list (x :: xs) =>
      let h := match x with | atom a => (hang a).getD xs.length | list _ => 0
      let lead := xs.take h
      let rest := xs.drop h
      let first := "(" ++ " ".intercalate ((x :: lead).map flat)
      let pad := "".pushn ' ' (ind + 2)
      first ++ String.join (rest.map fun c => "\n" ++ pad ++ go (ind + 2) c) ++ ")"

end Sexp

/-! ## Signatures -/

/-- Names of a signature's contexts, operations and blocks, and each
operation's blocks in printing order. -/
class EffSig.Print (eff : EffSig) where
  ctxName : eff.Ctx → String
  tagName : (γ : eff.Ctx) → eff.tag γ → String
  blocks : (γ : eff.Ctx) → (e : eff.tag γ) → List (eff.blockTag γ e)
  blockName : (γ : eff.Ctx) → (e : eff.tag γ) → eff.blockTag γ e → String

/-! ## Types, values and builtins -/

def Tp.sexp : Tp → Sexp
| .uInt32 => .atom "u32"
| .bool => .atom "bool"
| .unit => .atom "unit"
| .array tp => .list [.atom "array", tp.sexp]
| .prod a b => .list [.atom "prod", a.sexp, b.sexp]
| .fn a b => .list [.atom "fn", a.sexp, b.sexp]

def Tp.valSexp : (tp : Tp) → tp.denote → Sexp
| .uInt32, v => .atom (toString v)
| .bool, v => .atom (toString v)
| .unit, _ => .list []
| .array tp, xs => .list (.atom "array" :: xs.toList.map (Tp.valSexp tp))
| .prod a b, (x, y) => .list [.atom "pair", a.valSexp x, b.valSexp y]
| .fn _ _, r => .atom ("fn#" ++ toString (show Nat from r))

def Builtin.name : Builtin inp out → String
| .uAdd => "uAdd" | .uSub => "uSub" | .uMul => "uMul" | .uDiv => "uDiv"
| .uMod => "uMod" | .uEq => "uEq" | .uLt => "uLt" | .uLe => "uLe"
| .not => "not" | .and => "and" | .or => "or" | .bEq => "bEq"
| .pair => "pair" | .fst => "fst" | .snd => "snd"
| .arrEmpty => "arrEmpty" | .arrPush => "arrPush" | .arrGet => "arrGet"
| .arrSet => "arrSet" | .arrLen => "arrLen"

/-- A builtin applied to its arguments. `arrEmpty` has none to infer its
element type from, so it carries it. -/
def Builtin.sexp (b : Builtin inp out) (args : List Sexp) : Sexp :=
  match out, b with
  | .array a, .arrEmpty => .list [.atom b.name, a.sexp]
  | _, _ => .list (.atom b.name :: args)

def HList.atoms : HList (fun _ : Tp => String) ts → List Sexp
| .nil => []
| .cons x xs => .atom x :: HList.atoms xs

/-! ## Expressions and programs -/

/-- Variables are numbered in binding order, so every name is distinct.
Functions are `f`, other values `v`. -/
def varName (tp : Tp) (n : Nat) : String :=
  (match tp with | .fn _ _ => "f" | _ => "v") ++ toString n

variable {eff : EffSig} [EffSig.Print eff]

/-- A body: one statement as itself, several as `(do …)`. -/
def Sexp.body : List Sexp → Sexp
| [s] => s
| ss => .list (.atom "do" :: ss)

def Sexp.letS (x : String) (rhs : Sexp) : Sexp := .list [.atom "let", .atom x, rhs]

def Sexp.param (x : String) (tp : Tp) : Sexp := .list [.atom x, tp.sexp]

def Sexp.funS (x : String) (tp : Tp) (body : List Sexp) : Sexp :=
  .list (.atom "fun" :: .param x tp :: body)

/-- The statements of an expression, numbering binders from `n` in reading
order; also returns the next free number. -/
def Expr.sexps {γ tp} (n : Nat) : Expr eff (fun _ => String) γ tp → List Sexp × Nat
| .ret v => ([.list [.atom "ret", .atom v]], n)
| .lit t v k =>
    let x := varName t.val n
    let (ss, n) := (k x).sexps (n + 1)
    (.letS x (.list [.atom "lit", t.val.sexp, t.val.valSexp v]) :: ss, n)
| .builtin (out := o) b args k =>
    let x := varName o n
    let (ss, n) := (k x).sexps (n + 1)
    (.letS x (b.sexp (HList.atoms args)) :: ss, n)
| .lam (inp := i) (out := o) f k =>
    let x := varName (.fn i o) n
    let y := varName i (n + 1)
    let (fs, n) := (f y).sexps (n + 2)
    let (ss, n) := (k x).sexps n
    (.letS x (.funS y i fs) :: ss, n)
| .app (out := o) f y k =>
    let x := varName o n
    let (ss, n) := (k x).sexps (n + 1)
    (.letS x (.list [.atom "app", .atom f, .atom y]) :: ss, n)
| .ite (out := o) c t e k =>
    let x := varName o n
    let (ts, n) := t.sexps (n + 1)
    let (es, n) := e.sexps n
    let (ss, n) := (k x).sexps n
    (.letS x (.list [.atom "if", .atom c, .body ts, .body es]) :: ss, n)
| .loop (c := c) body init k =>
    let x := varName c n
    let y := varName c (n + 1)
    let (bs, n) := (body y).sexps (n + 2)
    let (ss, n) := (k x).sexps n
    (.letS x (.list [.atom "loop", .atom init, .funS y c bs]) :: ss, n)
| .op (γ := γ) e inp blocks k =>
    let x := varName (eff.output γ e).val n
    let (bs, n) := (EffSig.Print.blocks γ e).attach.foldl (init := ([], n + 1))
      fun (bs, n) ⟨b, _⟩ =>
        let y := varName (eff.blockInputs γ e b).val n
        let (ss, n) := (blocks b y).sexps (n + 1)
        let name := EffSig.Print.blockName γ e b
        (bs ++ [.list (.atom "block" :: .atom name :: .list [.atom y] :: ss)], n)
    let (ss, n) := (k x).sexps n
    (.letS x (.list (.atom "op" :: .atom (EffSig.Print.tagName γ e) :: .atom inp :: bs)) :: ss,
      n)

def Program.sexps {γ i o} (n : Nat) : Program eff γ i o (fun _ => String) → List Sexp
| .define (γ := γ') (inp := i') (out := o') body k =>
    let f := varName (.fn i' o') n
    let x := varName i' (n + 1)
    let (bs, n) := (body f x).sexps (n + 2)
    let ctx := Sexp.atom (EffSig.Print.ctxName γ')
    .list ([.atom "define", .atom f, ctx, .param x i', o'.sexp] ++ bs) :: (k f).sexps n
| .main body =>
    let x := varName i.val n
    let ctx := Sexp.atom (EffSig.Print.ctxName γ)
    [.list ([.atom "main", ctx, .param x i.val, o.val.sexp] ++ ((body x).sexps (n + 1)).1)]

def Program.toSexp {γ i o} (p : Program eff γ i o (fun _ => String)) : Sexp :=
  .list (.atom "program" :: p.sexps 0)

/-- How many children of each form stay on its first line: the header before
the statements or sub-bodies. -/
def astHang : String → Option Nat
| "program" | "do" => some 0
| "let" | "if" | "loop" | "fun" => some 1
| "op" | "block" => some 2
| "main" => some 3
| "define" => some 4
| _ => none

def Program.pretty {γ i o} (p : Program eff γ i o (fun _ => String)) (width : Nat := 80) :
    String :=
  p.toSexp.pretty astHang width

end Freigen.Ast
