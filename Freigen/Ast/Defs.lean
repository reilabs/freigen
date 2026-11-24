import Freigen.Eff
import Freigen.Free.Basic
import Freigen.CompM.Basic
import Freigen.CompM.Implements
import Freigen.Wheels
import Std.Data.ExtHashMap.Lemmas

namespace Freigen.Ast

/-- Object-language types, over a language's base types `B`. -/
inductive Tp (B : Type)
| base (b : B)
| uInt32
| bool
| array (tp : Tp B)
| unit
| prod (fst : Tp B) (snd : Tp B)
| fn (inp : Tp B) (out : Tp B)
deriving DecidableEq

def FnRef : Type := Nat

/-- Denotation of types, given a denotation `D` of the base types. -/
abbrev Tp.denote {B : Type} (D : B → Type) : Tp B → Type
| .base b => D b
| .uInt32 => UInt32
| .bool => Bool
| .array tp => Array (Tp.denote D tp)
| .unit => Unit
| .prod l r => Tp.denote D l × Tp.denote D r
| .fn _ _ => FnRef

/-- Literal values: core values only, since base types have no syntactic
values (their literals are primitives). -/
abbrev Tp.Lit {B : Type} (tp : Tp B) : Type := Tp.denote (fun _ => Empty) tp

/-- A literal, as a value of any denotation. -/
@[reducible] def Tp.embed {B : Type} {D : B → Type} : (tp : Tp B) → tp.Lit → Tp.denote D tp
| .base _, v => nomatch v
| .uInt32, v => v
| .bool, v => v
| .array tp, v => v.map (Tp.embed tp)
| .unit, v => v
| .prod a b, v => (Tp.embed a v.1, Tp.embed b v.2)
| .fn _ _, v => v

/-- Types that may cross effect boundaries and program entry points, given
which base types may. -/
inductive IsAbiTp {B : Type} (abi : B → Bool) : Tp B → Prop
| base {b} : abi b = true → IsAbiTp abi (.base b)
| uInt32 : IsAbiTp abi .uInt32
| bool : IsAbiTp abi .bool
| unit : IsAbiTp abi .unit
| array {tp} : IsAbiTp abi tp → IsAbiTp abi (Tp.array tp)
| prod {fst snd} : IsAbiTp abi fst → IsAbiTp abi snd → IsAbiTp abi (Tp.prod fst snd)

abbrev AbiTp (B : Type) (abi : B → Bool) := {tp : Tp B // IsAbiTp abi tp}

section
variable {B : Type} {abi : B → Bool}
abbrev AbiTp.base (b : B) (h : abi b = true := by rfl) : AbiTp B abi := ⟨.base b, .base h⟩
abbrev AbiTp.uInt32 : AbiTp B abi := ⟨.uInt32, .uInt32⟩
abbrev AbiTp.bool : AbiTp B abi := ⟨.bool, .bool⟩
abbrev AbiTp.unit : AbiTp B abi := ⟨.unit, .unit⟩
abbrev AbiTp.array (tp : AbiTp B abi) : AbiTp B abi :=
  ⟨.array tp.val, .array tp.property⟩
abbrev AbiTp.prod (fst snd : AbiTp B abi) : AbiTp B abi :=
  ⟨.prod fst.val snd.val, .prod fst.property snd.property⟩
end

/-- A language: the vocabulary of ASTs. Its contexts, base types, primitives,
and operations with the type at each of their positions, all syntactic. Their
meaning is given by a `Model`. Contexts and operations are small (`Type`): the
evaluator's heap stores contexts and syntax, and its results must be values.
A source DSL is related to it by a `Lift`. -/
structure Language where
  Ctx : Type
  [decidableEqCtx : DecidableEq Ctx]
  Base : Type
  [decidableEqBase : DecidableEq Base]
  abi : Base → Bool
  Prim : List (Tp Base) → Tp Base → Type
  Op : Ctx → Type
  input : (γ : Ctx) → Op γ → AbiTp Base abi
  output : (γ : Ctx) → Op γ → AbiTp Base abi
  Block : (γ : Ctx) → Op γ → Type
  blockCtx : (γ : Ctx) → (e : Op γ) → Block γ e → Ctx
  blockInputs : (γ : Ctx) → (e : Op γ) → Block γ e → AbiTp Base abi
  blockOutputs : (γ : Ctx) → (e : Op γ) → Block γ e → AbiTp Base abi

attribute [instance] Language.decidableEqCtx Language.decidableEqBase

abbrev Language.Tp (L : Language) : Type := Ast.Tp L.Base
abbrev Language.AbiTp (L : Language) : Type := Ast.AbiTp L.Base L.abi

/-- The meaning of a language's base types, primitives and operation results.
Models may depend on parameters (a field, a circuit context); the syntax does
not. -/
structure Language.Model (L : Language) where
  denote : L.Base → Type
  prim : {inp : List L.Tp} → {out : L.Tp} → L.Prim inp out →
    HList (Tp.denote denote) inp → Option (Tp.denote denote out)

/-- Values of a type in a model: the evaluator's variables. -/
abbrev Language.Model.V {L : Language} (M : L.Model) : L.Tp → Type :=
  Tp.denote M.denote

/-- The language's operations as effects under a model, with their inputs. -/
def Language.denote (L : Language) (M : L.Model) : L.Ctx → Type :=
  fun γ => Σ e : L.Op γ, M.V (L.input γ e).val

instance Language.denoteSpec (L : Language) (M : L.Model) : Eff.Spec (L.denote M) where
  output := fun γ ⟨e, _⟩ => M.V (L.output γ e).val
  blockTag := fun γ ⟨e, _⟩ => L.Block γ e
  blockCtx := fun γ ⟨e, _⟩ => L.blockCtx γ e
  blockInputs := fun γ ⟨e, _⟩ b => M.V (L.blockInputs γ e b).val
  blockOutputs := fun γ ⟨e, _⟩ b => M.V (L.blockOutputs γ e b).val

/-- The evaluator's effects: failure, silent steps, then the language's operations. -/
abbrev EvalEff (L : Language) (M : L.Model) : L.Ctx → Type :=
  Eff.Fail ⊕ₑ Eff.Tau ⊕ₑ L.denote M

abbrev EvalM (L : Language) (M : L.Model) (γ : L.Ctx) (α : Type) :=
  CompM (EvalEff L M) γ α

/-- Primitive operations. Data construction and projection are builtins too,
so the AST has a single node (and a single certificate rule) for all of them.
`prim` embeds the language's own primitives. -/
inductive Builtin (L : Language) : List L.Tp → L.Tp → Type
| uAdd : Builtin L [.uInt32, .uInt32] .uInt32
| uSub : Builtin L [.uInt32, .uInt32] .uInt32
| uMul : Builtin L [.uInt32, .uInt32] .uInt32
| uDiv : Builtin L [.uInt32, .uInt32] .uInt32
| uMod : Builtin L [.uInt32, .uInt32] .uInt32
| uEq : Builtin L [.uInt32, .uInt32] .bool
| uLt : Builtin L [.uInt32, .uInt32] .bool
| uLe : Builtin L [.uInt32, .uInt32] .bool

| not : Builtin L [.bool] .bool
| and : Builtin L [.bool, .bool] .bool
| or : Builtin L [.bool, .bool] .bool
| bEq : Builtin L [.bool, .bool] .bool

| pair {a b} : Builtin L [a, b] (.prod a b)
| fst {a b} : Builtin L [.prod a b] a
| snd {a b} : Builtin L [.prod a b] b

| arrEmpty {a} : Builtin L [] (.array a)
| arrPush {a} : Builtin L [.array a, a] (.array a)
| arrGet {a} : Builtin L [.array a, .uInt32] a
| arrSet {a} : Builtin L [.array a, .uInt32, a] (.array a)
| arrLen {a} : Builtin L [.array a] .uInt32

| prim {inp out} : L.Prim inp out → Builtin L inp out

/-- Semantics of builtins in a model. `none` means the evaluator fails
(out-of-bounds array access, or a failing primitive). Division and remainder
by zero follow `UInt32` (result `0` and the dividend respectively); array
lengths wrap modulo `2^32`. -/
def Builtin.denote {L : Language} (M : L.Model) {inp : List L.Tp} {out : L.Tp} :
    Builtin L inp out → HList M.V inp → Option (M.V out)
| .uAdd, h![x, y] => some (x + y)
| .uSub, h![x, y] => some (x - y)
| .uMul, h![x, y] => some (x * y)
| .uDiv, h![x, y] => some (x / y)
| .uMod, h![x, y] => some (x % y)
| .uEq, h![x, y] => some (decide (x = y))
| .uLt, h![x, y] => some (decide (x < y))
| .uLe, h![x, y] => some (decide (x ≤ y))
| .not, h![x] => some (!x)
| .and, h![x, y] => some (x && y)
| .or, h![x, y] => some (x || y)
| .bEq, h![x, y] => some (decide (x = y))
| .pair, h![x, y] => some (x, y)
| .fst, h![p] => some p.1
| .snd, h![p] => some p.2
| .arrEmpty, h![] => some #[]
| .arrPush, h![xs, x] => some (xs.push x)
| .arrGet, h![xs, i] => xs[i.toNat]?
| .arrSet, h![xs, i, x] =>
    if h : i.toNat < xs.size then some (xs.set i.toNat x h) else none
| .arrLen, h![xs] => some xs.size.toUInt32
| .prim p, args => M.prim p args

inductive Expr
    (L : Language) (Var : L.Tp → Type) :
    (γ : L.Ctx) → L.Tp → Type where
| ret {γ tp} : Var tp → Expr L Var γ tp
| lit {γ outK} : (tp : L.AbiTp) → (v : tp.val.Lit) →
    (Var tp → Expr L Var γ outK) → Expr L Var γ outK
| builtin {γ inp out outK} :
    (b : Builtin L inp out) → HList Var inp →
    (Var out → Expr L Var γ outK) → Expr L Var γ outK
| lam {γ inp out outK} : (Var inp → Expr L Var γ out) →
    (Var (.fn inp out) → Expr L Var γ outK) → Expr L Var γ outK
| app {γ inp out outK} : (f : Var (.fn inp out)) → (x : Var inp) →
    (Var out → Expr L Var γ outK) → Expr L Var γ outK
| ite {γ out outK} : (c : Var .bool) → (t e : Expr L Var γ out) →
    (Var out → Expr L Var γ outK) → Expr L Var γ outK
| loop {γ c outK} :
    (body : Var c → Expr L Var γ (Tp.prod c .bool)) →
    (init : Var c) →
    (Var c → Expr L Var γ outK) → Expr L Var γ outK
| op {γ outK} : (e : L.Op γ) → (inp : Var (L.input γ e)) →
    (blocks :
      (b : L.Block γ e) →
      Var (L.blockInputs γ e b) →
      Expr L Var (L.blockCtx γ e b) (L.blockOutputs γ e b)) →
    (Var (L.output γ e) → Expr L Var γ outK) →
    Expr L Var γ outK

inductive Program
    (L : Language)
    (mainCtx : L.Ctx)
    (mainInput mainOutput : L.AbiTp)
    (Var : L.Tp → Type) : Type where
| define {γ inp out} :
    (Var (.fn inp out) → Var inp → Expr L Var γ out) →
    (Var (.fn inp out) →
      Program L mainCtx mainInput mainOutput Var) →
    Program L mainCtx mainInput mainOutput Var
| main :
    (Var mainInput.val → Expr L Var mainCtx mainOutput.val) →
    Program L mainCtx mainInput mainOutput Var

structure Heap (L : Language) (M : L.Model) where
  next : Nat
  env :
    Std.ExtHashMap Nat
      (Σ γ : L.Ctx,
        Σ i : L.Tp,
        Σ o : L.Tp,
          M.V i → Expr L M.V γ o)
  env_supp : ∀ id, id < next ↔ env.contains id

instance {L : Language} {M : L.Model} : PartialOrder (Heap L M) where
  le s₁ s₂ := s₁.next ≤ s₂.next ∧ ∀ id, id < s₁.next → s₁.env.get? id = s₂.env.get? id
  le_refl := by simp
  le_trans := by grind
  le_antisymm := by
    rintro a b ⟨_, _⟩ ⟨_, _⟩
    rcases a with ⟨na, sa, _⟩
    rcases b with ⟨nb, sb, _⟩
    simp only at *
    have : na = nb := by grind
    cases this
    have : sa = sb := by grind
    cases this
    rfl

def Heap.empty (L : Language) (M : L.Model) : Heap L M where
  next := 0
  env := default
  env_supp := by simp [default]

def Heap.alloc
    {L : Language} {M : L.Model} {γ : L.Ctx} {i o : L.Tp}
    (s : Heap L M)
    (f :
      M.V (.fn i o) →
      M.V i →
      Expr L M.V γ o) :
    Heap L M × FnRef :=
  let id := s.next
  let s' : Heap L M := {
    next := id + 1
    env := s.env.insert id ⟨γ, i, o, f id⟩
    env_supp := by
      intro i
      cases s
      grind
  }
  (s', id)

def Heap.lookup
    {L : Language} {M : L.Model} {γ : L.Ctx} {i o : L.Tp}
    (s : Heap L M) :
    M.V (.fn i o) →
    Option (M.V i → Expr L M.V γ o) := fun x => do
  let x ← s.env.get? x
  match x with
  | ⟨γ', i', o', body⟩ =>
    if h : γ = γ' ∧ i = i' ∧ o = o' then
      pure $ h.1 ▸ h.2.1 ▸ h.2.2 ▸ body
    else
      none

inductive EvalState (L : Language) (M : L.Model) : L.Ctx × Type → Type 1 where
| done {γ} {R}: R → EvalState L M (γ, R)
| cont {γ} {R} {i : L.Tp}: Heap L M → Expr L M.V γ i →
    (Heap L M → M.V i → EvalState L M (γ, R)) → EvalState L M (γ, R)

def Expr.denoteCo {L : Language} {M : L.Model} (i : L.Ctx × Type) :
    EvalState L M i → Eff.Step L.Ctx (EvalEff L M) (EvalState L M) i
| .done v => Eff.Step.ret v
| .cont s e k => match e with
  | .ret v => Eff.Step.tau (k s v)
  | .lit tp v k' => Eff.Step.tau (EvalState.cont s (k' (tp.val.embed v)) k)
  | .builtin b args k' => match b.denote M args with
    | some r => Eff.Step.tau (EvalState.cont s (k' r) k)
    | none => Eff.Step.fail
  | .lam b k' =>
    let (s', l) := s.alloc (fun _ x => b x)
    Eff.Step.tau (EvalState.cont s' (k' l) k)
  | .app f x k' => match s.lookup f with
    | none => Eff.Step.fail
    | some f => Eff.Step.tau (EvalState.cont s (f x) fun s' r => EvalState.cont s' (k' r) k)
  | .ite c t e k' => Eff.Step.tau (EvalState.cont s (if c then t else e) fun s' r => EvalState.cont s' (k' r) k)
  | .loop body init k' =>
    -- `true` means "keep going"
    Eff.Step.tau (EvalState.cont s (body init) fun s' r => match r with
      | (next, true) => EvalState.cont s' (Expr.loop body next k') k
      | (next, false) => EvalState.cont s' (k' next) k
    )
  | .op e inp blocks k' =>
    Eff.Step.op (.inr $ .inr ⟨e, inp⟩) (fun tag inp =>
      EvalState.cont s (blocks tag inp) fun _ r => EvalState.done r
    ) fun o => EvalState.cont s (k' o) k

def Expr.denote {L : Language} {M : L.Model} {γ : L.Ctx} {o : L.Tp} (state : Heap L M)
    (expr : Expr L M.V γ o) : EvalM L M γ (Heap L M × M.V o) :=
  CompM.corec denoteCo (EvalState.cont state expr fun s r => EvalState.done (s, r))

def Program.denote' {L : Language} {M : L.Model} {γ} {iT oT}
    (p: Program L γ iT oT M.V) (i: M.V iT.val) :
    EvalM L M γ (Heap L M × M.V oT.val) :=
  go (Heap.empty _ _) p where
  go : Heap L M → Program L γ iT oT M.V →
    EvalM L M γ (Heap L M × M.V oT.val) := fun s => fun
  | .define body k =>
    let (s', f) := s.alloc (fun f x => body f x)
    go s' (k f)
  | .main body => Expr.denote s (body i)

def Program.denote {L : Language} {M : L.Model} {γ} {iT oT}
    (p: Program L γ iT oT M.V) (i: M.V iT.val) : EvalM L M γ (M.V oT.val) :=
  (·.2) <$> Program.denote' p i

/-! ## Lifts -/

/-- How a source DSL is lifted into a language under a model. The source has
its own operations `SrcOp` over the language's contexts: a source program and
its AST run in the same context.

Values: `r : Rep t α` says source values of type `α` are represented by AST
values of type `t`, by `erase r`, which is injective. Operations:
`c : OpRep γ e` says the source operation `e` is represented in its context
`γ` by the AST operation `op c` on `input c`; each block `t` of `e` by block
`block c t` of `op c`. Every value crossing between
them is represented at both its types, so the lift fixes how each is erased.
A lift may take parameters (a prime, a circuit context); lifted programs are
certified for all of them. -/
structure Lift (L : Language) (M : L.Model) where
  SrcOp : L.Ctx → Type u
  [srcSpec : Eff.Spec.{0, u, 0} SrcOp]
  Rep : L.AbiTp → Type → Type
  erase : {t : L.AbiTp} → {α : Type} → Rep t α → α → M.V t.val
  erase_injective : ∀ {t : L.AbiTp} {α : Type} (r : Rep t α), Function.Injective (erase r)
  OpRep : (γ : L.Ctx) → SrcOp γ → Type w
  op : {γ : L.Ctx} → {e : SrcOp γ} → OpRep γ e → L.Op γ
  input : {γ : L.Ctx} → {e : SrcOp γ} → (c : OpRep γ e) → M.V (L.input γ (op c)).val
  block : {γ : L.Ctx} → {e : SrcOp γ} → (c : OpRep γ e) →
    srcSpec.blockTag γ e → L.Block γ (op c)
  blockInput : {γ : L.Ctx} → {e : SrcOp γ} → (c : OpRep γ e) → (t : srcSpec.blockTag γ e) →
    Rep (L.blockInputs γ (op c) (block c t)) (srcSpec.blockInputs γ e t)
  blockOutput : {γ : L.Ctx} → {e : SrcOp γ} → (c : OpRep γ e) → (t : srcSpec.blockTag γ e) →
    Rep (L.blockOutputs γ (op c) (block c t)) (srcSpec.blockOutputs γ e t)
  output : {γ : L.Ctx} → {e : SrcOp γ} → (c : OpRep γ e) →
    Rep (L.output γ (op c)) (srcSpec.output γ e)

attribute [instance] Lift.srcSpec

namespace Lift

variable {L : Language} {M : L.Model}

/-- The pairs of a lift's simulation spec: a source operation with its
representation, in one context. -/
inductive Pair (ℓ : Lift.{u, w} L M) : L.Ctx → L.Ctx → Type (max u w)
| mk {γ : L.Ctx} (e : ℓ.SrcOp γ) (c : ℓ.OpRep γ e) : Pair ℓ γ γ

/-- The simulation spec of a lift: every eraser is the erasure at its
position's representation. -/
def simSpec (ℓ : Lift L M) : Free.SimSpec (L.denote M) ℓ.SrcOp where
  Op := ℓ.Pair
  src | .mk _ c => ⟨ℓ.op c, ℓ.input c⟩
  tgt | .mk e _ => e
  tag | .mk _ c => ℓ.block c
  inp | .mk _ c => fun t => ℓ.erase (ℓ.blockInput c t)
  out | .mk _ c => fun t => ℓ.erase (ℓ.blockOutput c t)
  res | .mk _ c => ℓ.erase (ℓ.output c)
  inp_injective | .mk _ _ => fun _ => ℓ.erase_injective _
  out_injective | .mk _ _ => fun _ => ℓ.erase_injective _
  res_injective | .mk _ _ => ℓ.erase_injective _

/-- The identity lift's representations: AST values only, by themselves. -/
inductive IdRep (L : Language) (M : L.Model) : L.AbiTp → Type → Type
| self (t : L.AbiTp) : IdRep L M t (M.V t.val)

/-- The identity lift's operation representations: each operation by itself. -/
inductive IdOpRep (L : Language) (M : L.Model) : (γ : L.Ctx) → L.denote M γ → Type
| mk {γ : L.Ctx} (e : L.Op γ) (x : M.V (L.input γ e).val) : IdOpRep L M γ ⟨e, x⟩

/-- The identity lift of a language: the source is over the language's own
operations, each represented by itself, and values by themselves. -/
abbrev id (L : Language) (M : L.Model) : Lift L M where
  SrcOp := L.denote M
  Rep := IdRep L M
  erase | .self _ => fun v => v
  erase_injective | .self _ => fun _ _ h => h
  OpRep := IdOpRep L M
  op | .mk e _ => e
  input | .mk _ x => x
  block | .mk _ _ => fun t => t
  blockInput | .mk _ _ => fun _ => .self _
  blockOutput | .mk _ _ => fun _ => .self _
  output | .mk _ _ => .self _

end Lift

/-- The program is correct against `t` on every input (`CompM.Corr` by the
lift's spec): wherever the source can take it, it terminates, never fails,
and performs the source's operations on the erasures of their arguments, and
its result is the erasure at `r i` of the source's. Where an operation
returns a value that erases no source output (a certificate for a false
assertion), it is unconstrained. The source's result type `α i`, and so its
representation `r i`, may depend on the input. -/
def ProgramCert {L : Language} {M : L.Model} (ℓ : Lift.{u, w} L M)
    {iTp oTp : L.AbiTp} {γ : L.Ctx} {α : M.V iTp.val → Type}
    (r : (i : M.V iTp.val) → ℓ.Rep oTp (α i))
    (p : ∀{V}, Program L γ iTp oTp V)
    (t : (i : M.V iTp.val) → Free ℓ.SrcOp γ (α i)) : Prop :=
  ∀ i, CompM.Corr ℓ.simSpec (ℓ.erase (r i)) (p.denote i) (t i)

end Freigen.Ast
