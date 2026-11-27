import Freigen.Circuit.Defs
import Freigen.Ast.Macro
import Freigen.Ast.Print

/-!
The `Circuit` DSL as an AST language. Its effects are lifted like its types:
the language shares the DSL's contexts (`Circuit.Scope`), and every type an
operation mentions is a `Tp`.

Wires and field elements are base types. A hint takes a vector of wires and
passes their values to its block, which returns a vector of field elements,
and the hint as many fresh wires. The model interprets them over
`ZMod P` and a circuit context, so one AST serves every prime and context.

The lift (`lift`) fixes how source values are represented (`Rep`, indexed by
the AST type and the source type, and erased injectively): object types by
themselves, `Cert`s by `()` (they are subsingletons, like proofs), and
`CertW`s by their wire. It
represents each DSL operation by an AST operation (`OpRep`), every value
crossing between them at a `Rep`: operations that return a `Cert` in the DSL
return `unit` in the AST.
-/

namespace Freigen.Circuit.Lift

open Ast

/-! ## Syntax -/

inductive Base
| field
| wire
deriving DecidableEq

abbrev Tp := Ast.Tp Base
abbrev AbiTp := Ast.AbiTp Base fun _ => true

abbrev Tp.field : Tp := .base .field
abbrev Tp.wire : Tp := .base .wire

/-- Circuit primitives: field arithmetic, and linear combinations of wires.
`fInv` is the inverse in `ZMod P`, with `0⁻¹ = 0`. -/
inductive Prim : List Tp → Tp → Type
| fAdd : Prim [.field, .field] .field
| fSub : Prim [.field, .field] .field
| fMul : Prim [.field, .field] .field
| fNeg : Prim [.field] .field
| fInv : Prim [.field] .field
| wAdd : Prim [.wire, .wire] .wire
| wSub : Prim [.wire, .wire] .wire
| wNeg : Prim [.wire] .wire
| wScale : Prim [.field, .wire] .wire

inductive ConstraintOp
| assertR1C
| rangeCheck (n : Nat)
| assertSpread (n : Nat)
/-- A hint over `n` wires, returning `m` fresh ones. -/
| hint (n m : Nat)

/-- Hint blocks have no operations (yet). -/
inductive HintOp

abbrev Tag : Scope → Type
| .constraint => ConstraintOp
| .hint => HintOp

def language : Language where
  Ctx := Scope
  Base := Base
  abi := fun _ => true
  Prim := Prim
  Op := Tag
  input := fun
    | .constraint, .assertR1C => .prod (.base .wire) (.prod (.base .wire) (.base .wire))
    | .constraint, .rangeCheck _ => .base .wire
    | .constraint, .assertSpread _ => .prod (.base .wire) (.base .wire)
    | .constraint, .hint n _ => .vec n (.base .wire)
  output := fun
    | .constraint, .assertR1C => .unit
    | .constraint, .rangeCheck _ => .unit
    | .constraint, .assertSpread _ => .unit
    | .constraint, .hint _ m => .vec m (.base .wire)
  Block := fun
    | .constraint, .hint _ _ => Unit
    | .constraint, .assertR1C => Empty
    | .constraint, .rangeCheck _ => Empty
    | .constraint, .assertSpread _ => Empty
  blockCtx := fun
    | .constraint, .hint _ _, _ => .hint
    | .constraint, .assertR1C, b => nomatch b
    | .constraint, .rangeCheck _, b => nomatch b
    | .constraint, .assertSpread _, b => nomatch b
  blockInputs := fun
    | .constraint, .hint n _, _ => .vec n (.base .field)
    | .constraint, .assertR1C, b => nomatch b
    | .constraint, .rangeCheck _, b => nomatch b
    | .constraint, .assertSpread _, b => nomatch b
  blockOutputs := fun
    | .constraint, .hint _ m, _ => .vec m (.base .field)
    | .constraint, .assertR1C, b => nomatch b
    | .constraint, .rangeCheck _, b => nomatch b
    | .constraint, .assertSpread _, b => nomatch b

/-! ## Printing -/

def Base.sexp : Base → Sexp
| .field => .atom "field"
| .wire => .atom "wire"

instance : Language.Print language where
  baseSexp := Base.sexp
  primSexp := fun p args => match p with
    | .fAdd => .list (.atom "fAdd" :: args)
    | .fSub => .list (.atom "fSub" :: args)
    | .fMul => .list (.atom "fMul" :: args)
    | .fNeg => .list (.atom "fNeg" :: args)
    | .fInv => .list (.atom "fInv" :: args)
    | .wAdd => .list (.atom "wAdd" :: args)
    | .wSub => .list (.atom "wSub" :: args)
    | .wNeg => .list (.atom "wNeg" :: args)
    | .wScale => .list (.atom "wScale" :: args)
  ctxName
    | .constraint => "constraint"
    | .hint => "hint"
  opSexp := fun
    | .constraint, .assertR1C => .atom "assertR1C"
    | .constraint, .rangeCheck n => .list [.atom "rangeCheck", .atom (toString n)]
    | .constraint, .assertSpread n => .list [.atom "assertSpread", .atom (toString n)]
    | .constraint, .hint n m => .list [.atom "hint", .atom (toString n), .atom (toString m)]
  blocks := fun
    | .constraint, .hint _ _ => [()]
    | .constraint, .assertR1C => []
    | .constraint, .rangeCheck _ => []
    | .constraint, .assertSpread _ => []
  blockName := fun
    | .constraint, .hint _ _, _ => "body"
    | .constraint, .assertR1C, b => nomatch b
    | .constraint, .rangeCheck _, b => nomatch b
    | .constraint, .assertSpread _, b => nomatch b

/-! ## Model -/

section Model

variable (P : Nat) [ctx : Context P]

abbrev Base.denote : Base → Type
| .field => ZMod P
| .wire => ctx.W

/-- The model over `ZMod P` and a circuit context. -/
def model : language.Model where
  denote := Base.denote P
  prim := fun p args => match p, args with
    | .fAdd, h![a, b] => some (a + b)
    | .fSub, h![a, b] => some (a - b)
    | .fMul, h![a, b] => some (a * b)
    | .fNeg, h![a] => some (-a)
    | .fInv, h![a] => some a⁻¹
    | .wAdd, h![a, b] => some (a + b)
    | .wSub, h![a, b] => some (a - b)
    | .wNeg, h![a] => some (-a)
    | .wScale, h![c, w] => some (c • w)

/-- How source types are represented, indexed by their AST type and the
source type. -/
inductive Rep : AbiTp → Type → Type
/-- An object type, by itself. -/
| self (t : AbiTp) : Rep t ((model P).V t.val)
/-- A certificate, by `()`. -/
| cert (A : Assertion (ZMod P) ctx.W) : Rep .unit (Cert A)
/-- A wire with a certificate about it, by the wire. -/
| certW (Q : ctx.W → Assertion (ZMod P) ctx.W) : Rep (.base .wire) (CertW Q)

/-- The erasure of represented values. By `casesOn`, which reduces on a
constructor whatever its indices. -/
def Rep.erase {t : AbiTp} {α : Type} (r : Rep P t α) : α → (model P).V t.val :=
  Rep.casesOn (motive := fun t α _ => α → (model P).V t.val) r
    (fun _ v => v) (fun _ _ => ()) (fun _ w => w.val)

theorem Rep.erase_injective :
    ∀ {t : AbiTp} {α : Type} (r : Rep P t α), Function.Injective (Rep.erase P r)
| _, _, .self _ => fun _ _ h => h
| _, _, .cert A => fun c₁ c₂ _ => Subsingleton.elim (α := Cert A) c₁ c₂
| _, _, .certW _ => fun ⟨_, c₁⟩ ⟨_, c₂⟩ h => by
    cases h
    cases Subsingleton.elim c₁ c₂
    rfl

/-- How DSL operations are represented: each by its AST operation. -/
inductive OpRep : (γ : Scope) → Circuit.Eff P ctx γ → Type 1
| assertR1C (a b c : ctx.W) :
    OpRep .constraint (Circuit.ConstraintEff.assertR1C a b c : Circuit.Eff P ctx .constraint)
| rangeCheck (n : Nat) (a : ctx.W) :
    OpRep .constraint (Circuit.ConstraintEff.rangeCheck n a : Circuit.Eff P ctx .constraint)
| assertSpread (n : Nat) (a b : ctx.W) :
    OpRep .constraint (Circuit.ConstraintEff.assertSpread n a b : Circuit.Eff P ctx .constraint)
| hint (n m : Nat) (args : Vector ctx.W n) :
    OpRep .constraint (Circuit.ConstraintEff.hint n m args : Circuit.Eff P ctx .constraint)

/-- The `Circuit` lift, for every prime and circuit context. Arguments are
objects, and so are a hint's inputs and results; certificates are represented
by `()`. -/
def lift : Lift language (model P) where
  SrcOp := Circuit.Eff P ctx
  -- Found at `Scope`, which `language.Ctx` is by unfolding.
  srcSpec := (inferInstance : Eff.Spec (Γ := Scope) (Circuit.Eff P ctx))
  Rep := Rep P
  erase := Rep.erase P
  erase_injective := Rep.erase_injective P
  OpRep := OpRep P
  op
  | .assertR1C .. => .assertR1C
  | .rangeCheck n _ => .rangeCheck n
  | .assertSpread n .. => .assertSpread n
  | .hint n m _ => .hint n m
  input
  | .assertR1C a b c => (a, (b, c))
  | .rangeCheck _ a => a
  | .assertSpread _ a b => (a, b)
  | .hint _ _ args => args
  block | .hint .., _ => ()
  blockInput | .hint .., _ => .self _
  blockOutput | .hint .., _ => .self _
  output
  | .assertR1C a b c => .cert (R1CSAssertion a b c)
  | .rangeCheck n a => .cert (RangeAssertion n a)
  | .assertSpread n a b => .cert (SpreadAssertion n a b)
  | .hint .. => .self _

/-- The simulation spec AST programs are compared to DSL programs by. -/
abbrev simSpec : Free.SimSpec (language.denote (model P)) (Circuit.Eff P ctx) :=
  (lift P).simSpec

end Model

attribute [lift_base lift] Base.field Base.wire

/-! ## Templates -/

section
variable {V : language.Tp → Type} {o : language.Tp}

/-- Pair the wires, then assert `a * b = c`. -/
def assertR1CAst (a b c : V (.base .wire)) (k : V .unit → Expr language V .constraint o) :
    Expr language V .constraint o :=
  .builtin .pair h![b, c] fun bc =>
  .builtin .pair h![a, bc] fun abc =>
  .op (L := language) (γ := Scope.constraint) ConstraintOp.assertR1C abc (fun b => Empty.elim b) k

/-- Pair the wires, then assert that `b` is the spread of `a`. -/
def assertSpreadAst (n : Nat) (a b : V (.base .wire)) (k : V .unit → Expr language V .constraint o) :
    Expr language V .constraint o :=
  .builtin .pair h![a, b] fun ab =>
  .op (L := language) (γ := Scope.constraint) (ConstraintOp.assertSpread n) ab (fun b => Empty.elim b) k

end

/-! ## Rules -/

namespace Rules

variable {P : Nat} [ctx : Context P] {h : Heap language (model P)} {o : language.Tp}

/-- `assertR1C`: the continuation receives the `Cert`, erased. -/
@[lift_rule lift] theorem assertR1C {a b c : ctx.W} {α : Type}
    {R : (model P).V o → α → Prop}
    {k : (model P).V .unit → Expr language (model P).V .constraint o}
    {tk : Cert (R1CSAssertion a b c) → Free (Circuit.Eff P ctx) .constraint α}
    (hk : ∀ u (r : Cert (R1CSAssertion a b c)), ExprCert (simSpec P) h (k u) R (tk r)) :
    ExprCert (simSpec P) h (assertR1CAst a b c k) R (Circuit.assertR1C a b c >>= tk) :=
  ExprCert.builtin (spec := simSpec P) (γ := Scope.constraint)
    (b := @Builtin.pair language (.base .wire) (.base .wire)) (r := (b, c)) rfl <|
  ExprCert.builtin (spec := simSpec P) (γ := Scope.constraint)
    (b := @Builtin.pair language (.base .wire) (.prod (.base .wire) (.base .wire))) (r := (a, (b, c)))
    rfl <|
  ExprCert.op (spec := simSpec P) (.mk _ (.assertR1C a b c)) (blocks := fun b => Empty.elim b)
    (fun t => nomatch t) fun r => hk _ r

/-- A hint: the block is certified for every input, against a source block
returning the same field elements; the continuation at every result. -/
@[lift_rule lift] theorem hint {n m : Nat}
    {args : Vector ctx.W n} {β : Type} {R : (model P).V o → β → Prop}
    {body : (model P).V (.vec n (.base .field)) → Expr language (model P).V .hint (.vec m (.base .field))}
    {src : (model P).V (.vec n (.base .field)) → Hint P (Vector (ZMod P) m)}
    (hb : ∀ xs, ExprCert (simSpec P) h (body xs) Eq (src xs))
    {k : (model P).V (.vec m (.base .wire)) → Expr language (model P).V .constraint o}
    {tk : Vector ctx.W m → Free (Circuit.Eff P ctx) .constraint β}
    (hk : ∀ ws, ExprCert (simSpec P) h (k ws) R (tk ws)) :
    ExprCert (simSpec P) h
      (.op (L := language) (γ := Scope.constraint) (ConstraintOp.hint n m) args
        (fun _ => body) k) R
      (Circuit.hint args src >>= tk) :=
  ExprCert.op (spec := simSpec P) (.mk _ (.hint n m args)) (blocks := fun _ => body)
    (fun _ y => hb y) hk

/-- `rangeCheck`: the continuation receives the checked wire, its `Cert`
erased. -/
@[lift_rule lift] theorem rangeCheck {n : Nat} {a : ctx.W} {α : Type}
    {R : (model P).V o → α → Prop}
    {k : (model P).V .unit → Expr language (model P).V .constraint o}
    {tk : WUInt P n → Free (Circuit.Eff P ctx) .constraint α}
    (hk : ∀ u (w : WUInt P n), a = w.val → ExprCert (simSpec P) h (k u) R (tk w)) :
    ExprCert (simSpec P) h
      (.op (L := language) (γ := Scope.constraint) (ConstraintOp.rangeCheck n) a
        (fun b => Empty.elim b) k) R
      (Circuit.rangeCheck n a >>= tk) := by
  simp only [Circuit.rangeCheck]
  exact ExprCert.op (spec := simSpec P) (.mk _ (.rangeCheck n a)) (blocks := fun b => Empty.elim b)
    (fun t => nomatch t)
    fun c => hk _ ⟨a, c⟩ rfl

/-- `assertSpread`: the continuation receives the `Cert`, erased. -/
@[lift_rule lift] theorem assertSpread {n : Nat} {a b : ctx.W} {α : Type}
    {R : (model P).V o → α → Prop}
    {k : (model P).V .unit → Expr language (model P).V .constraint o}
    {tk : Cert (SpreadAssertion n a b) → Free (Circuit.Eff P ctx) .constraint α}
    (hk : ∀ u (r : Cert (SpreadAssertion n a b)), ExprCert (simSpec P) h (k u) R (tk r)) :
    ExprCert (simSpec P) h (assertSpreadAst n a b k) R (Circuit.assertSpread n a b >>= tk) :=
  ExprCert.builtin (spec := simSpec P) (γ := Scope.constraint)
    (b := @Builtin.pair language (.base .wire) (.base .wire)) (r := (a, b)) rfl <|
  ExprCert.op (spec := simSpec P) (.mk _ (.assertSpread n a b)) (blocks := fun b => Empty.elim b)
    (fun t => nomatch t) fun r => hk _ r

/-- `assertR1C` in tail position: the certificate is the result. -/
@[lift_rule lift] theorem assertR1C_tail {a b c : ctx.W} :
    ExprCert (simSpec P) h (assertR1CAst a b c fun u => .ret u)
      (fun v r => v = (lift P).erase (Rep.cert (P := P) (R1CSAssertion a b c)) r)
      (Circuit.assertR1C a b c) := by
  have := assertR1C (h := h) (a := a) (b := b) (c := c) (o := .unit)
    (R := fun v r => v = (lift P).erase (Rep.cert (P := P) (R1CSAssertion a b c)) r) (tk := pure)
    (k := fun u => .ret u) fun _ _ => .ret rfl
  convert this using 1
  exact (bind_pure (Circuit.assertR1C a b c)).symm

/-- `rangeCheck` in tail position: the result is the checked wire. -/
@[lift_rule lift] theorem rangeCheck_tail {n : Nat} {a : ctx.W} :
    ExprCert (simSpec P) h
      (.op (L := language) (γ := Scope.constraint) (ConstraintOp.rangeCheck n) a
        (fun b => Empty.elim b) fun _ => .ret a)
      (fun v w => v = (lift P).erase (Rep.certW (P := P) (RangeAssertion n)) w)
      (Circuit.rangeCheck n a) := by
  have := rangeCheck (h := h) (n := n) (a := a)
    (R := fun v w => v = (lift P).erase (Rep.certW (P := P) (RangeAssertion n)) w) (tk := pure)
    (k := fun _ => .ret a) fun _ _ hw => .ret hw
  convert this using 1
  · congr
  · exact (bind_pure (Circuit.rangeCheck n a)).symm

/-- `assertSpread` in tail position: the certificate is the result. -/
@[lift_rule lift] theorem assertSpread_tail {n : Nat} {a b : ctx.W} :
    ExprCert (simSpec P) h (assertSpreadAst n a b fun u => .ret u)
      (fun v r => v = (lift P).erase (Rep.cert (P := P) (SpreadAssertion n a b)) r)
      (Circuit.assertSpread n a b) := by
  have := assertSpread (h := h) (n := n) (a := a) (b := b) (o := .unit)
    (R := fun v r => v = (lift P).erase (Rep.cert (P := P) (SpreadAssertion n a b)) r) (tk := pure)
    (k := fun u => .ret u) fun _ _ => .ret rfl
  convert this using 1
  exact (bind_pure (Circuit.assertSpread n a b)).symm

/-! ### Primitives -/

section Prims

variable {γ : Scope} {α : Type} {R : (model P).V o → α → Prop}

/-- Primitives: the continuation is certified at the result, so the source's
facts about it carry over.

As in every rule, the AST's binders (here the continuation's) are typed as
values of object types, `(model P).V t`: the AST is read off the conclusion,
and must not mention the model's parameters. -/
@[lift_rule lift] theorem fAdd {a b : ZMod P}
    {k : (model P).V (.base .field) → Expr language (model P).V γ o}
    {tk : (model P).V (.base .field) → Free (Circuit.Eff P ctx) γ α}
    (hk : ExprCert (simSpec P) h (k (a + b)) R (tk (a + b))) :
    ExprCert (simSpec P) h (.builtin (.prim .fAdd) h![a, b] k) R (tk (a + b)) :=
  ExprCert.builtin rfl hk

@[lift_rule lift] theorem fSub {a b : ZMod P}
    {k : (model P).V (.base .field) → Expr language (model P).V γ o}
    {tk : (model P).V (.base .field) → Free (Circuit.Eff P ctx) γ α}
    (hk : ExprCert (simSpec P) h (k (a - b)) R (tk (a - b))) :
    ExprCert (simSpec P) h (.builtin (.prim .fSub) h![a, b] k) R (tk (a - b)) :=
  ExprCert.builtin rfl hk

@[lift_rule lift] theorem fMul {a b : ZMod P}
    {k : (model P).V (.base .field) → Expr language (model P).V γ o}
    {tk : (model P).V (.base .field) → Free (Circuit.Eff P ctx) γ α}
    (hk : ExprCert (simSpec P) h (k (a * b)) R (tk (a * b))) :
    ExprCert (simSpec P) h (.builtin (.prim .fMul) h![a, b] k) R (tk (a * b)) :=
  ExprCert.builtin rfl hk

@[lift_rule lift] theorem fNeg {a : ZMod P}
    {k : (model P).V (.base .field) → Expr language (model P).V γ o}
    {tk : (model P).V (.base .field) → Free (Circuit.Eff P ctx) γ α}
    (hk : ExprCert (simSpec P) h (k (-a)) R (tk (-a))) :
    ExprCert (simSpec P) h (.builtin (.prim .fNeg) h![a] k) R (tk (-a)) :=
  ExprCert.builtin rfl hk

@[lift_rule lift] theorem fInv {a : ZMod P}
    {k : (model P).V (.base .field) → Expr language (model P).V γ o}
    {tk : (model P).V (.base .field) → Free (Circuit.Eff P ctx) γ α}
    (hk : ExprCert (simSpec P) h (k (a⁻¹ : ZMod P)) R (tk (a⁻¹ : ZMod P))) :
    ExprCert (simSpec P) h (.builtin (.prim .fInv) h![a] k) R (tk (a⁻¹ : ZMod P)) :=
  ExprCert.builtin rfl hk

@[lift_rule lift] theorem wAdd {a b : ctx.W}
    {k : (model P).V (.base .wire) → Expr language (model P).V γ o}
    {tk : (model P).V (.base .wire) → Free (Circuit.Eff P ctx) γ α}
    (hk : ExprCert (simSpec P) h (k (a + b)) R (tk (a + b))) :
    ExprCert (simSpec P) h (.builtin (.prim .wAdd) h![a, b] k) R (tk (a + b)) :=
  ExprCert.builtin rfl hk

@[lift_rule lift] theorem wSub {a b : ctx.W}
    {k : (model P).V (.base .wire) → Expr language (model P).V γ o}
    {tk : (model P).V (.base .wire) → Free (Circuit.Eff P ctx) γ α}
    (hk : ExprCert (simSpec P) h (k (a - b)) R (tk (a - b))) :
    ExprCert (simSpec P) h (.builtin (.prim .wSub) h![a, b] k) R (tk (a - b)) :=
  ExprCert.builtin rfl hk

@[lift_rule lift] theorem wNeg {a : ctx.W}
    {k : (model P).V (.base .wire) → Expr language (model P).V γ o}
    {tk : (model P).V (.base .wire) → Free (Circuit.Eff P ctx) γ α}
    (hk : ExprCert (simSpec P) h (k (-a)) R (tk (-a))) :
    ExprCert (simSpec P) h (.builtin (.prim .wNeg) h![a] k) R (tk (-a)) :=
  ExprCert.builtin rfl hk

@[lift_rule lift] theorem wScale {c : ZMod P} {w : ctx.W}
    {k : (model P).V (.base .wire) → Expr language (model P).V γ o}
    {tk : (model P).V (.base .wire) → Free (Circuit.Eff P ctx) γ α}
    (hk : ExprCert (simSpec P) h (k (c • w)) R (tk (c • w))) :
    ExprCert (simSpec P) h (.builtin (.prim .wScale) h![c, w] k) R (tk (c • w)) :=
  ExprCert.builtin rfl hk

end Prims

end Rules

end Freigen.Circuit.Lift
