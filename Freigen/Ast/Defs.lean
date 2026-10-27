import Freigen.Eff
import Freigen.Free.Basic
import Freigen.CompM.Basic
import Freigen.CompM.WF
import Freigen.Wheels
import Std.Data.ExtHashMap.Lemmas

namespace Freigen.Ast

/-- Object-language types. -/
inductive Tp
| uInt32
| bool
| array (tp : Tp)
| unit
| prod (fst : Tp) (snd : Tp)
| fn (inp : Tp) (out : Tp)
deriving BEq, ReflBEq, LawfulBEq, DecidableEq

def FnRef : Type := Nat

abbrev Tp.denote : Tp → Type
| .uInt32 => UInt32
| .bool => Bool
| .array tp => Array (Tp.denote tp)
| .unit => Unit
| .prod l r => l.denote × r.denote
| .fn _ _ => FnRef

/-- Types that may cross effect boundaries and program entry points. -/
inductive IsAbiTp : Tp → Prop
| uInt32 : IsAbiTp .uInt32
| bool : IsAbiTp .bool
| unit : IsAbiTp .unit
| array {tp} : IsAbiTp tp → IsAbiTp (Tp.array tp)
| prod {fst snd} : IsAbiTp fst → IsAbiTp snd → IsAbiTp (Tp.prod fst snd)

abbrev AbiTp := {tp : Tp // IsAbiTp tp}

abbrev AbiTp.uInt32 : AbiTp := ⟨.uInt32, .uInt32⟩
abbrev AbiTp.bool : AbiTp := ⟨.bool, .bool⟩
abbrev AbiTp.unit : AbiTp := ⟨.unit, .unit⟩
abbrev AbiTp.array (tp : AbiTp) : AbiTp :=
  ⟨.array tp.val, .array tp.property⟩
abbrev AbiTp.prod (fst snd : AbiTp) : AbiTp :=
  ⟨.prod fst.val snd.val, .prod fst.property snd.property⟩

structure EffSig where
  Ctx : Type
  [decidableEqCtx : DecidableEq Ctx]
  tag : Ctx → Type
  input : (γ : Ctx) → tag γ → AbiTp
  output : (γ : Ctx) → tag γ → AbiTp
  blockTag : (γ : Ctx) → tag γ → Type
  blockCtx : (γ : Ctx) → (e : tag γ) → blockTag γ e → Ctx
  blockInputs : (γ : Ctx) → (e : tag γ) → blockTag γ e → AbiTp
  blockOutputs : (γ : Ctx) → (e : tag γ) → blockTag γ e → AbiTp

attribute [instance] EffSig.decidableEqCtx

/-- Pull the syntactic signature back along `Tp.denote`; inputs live in tags. -/
def EffSig.denote (s : EffSig) : s.Ctx → Type :=
  fun γ => Σ e : s.tag γ, (s.input γ e).val.denote

instance EffSig.denoteSpec (s : EffSig) : Eff.Spec s.denote where
  output := fun γ ⟨e, _⟩ => (s.output γ e).val.denote
  blockTag := fun γ ⟨e, _⟩ => s.blockTag γ e
  blockCtx := fun γ ⟨e, _⟩ => s.blockCtx γ e
  blockInputs := fun γ ⟨e, _⟩ b => (s.blockInputs γ e b).val.denote
  blockOutputs := fun γ ⟨e, _⟩ b => (s.blockOutputs γ e b).val.denote

/-- The evaluator's effects: failure, silent steps, then the user signature. -/
abbrev EvalEff (eff : EffSig) : eff.Ctx → Type :=
  Eff.Fail ⊕ₑ Eff.Tau ⊕ₑ eff.denote

abbrev EvalM (eff : EffSig) (γ : eff.Ctx) (α : Type) :=
  CompM (EvalEff eff) γ α

/-- Primitive operations. Data construction and projection are builtins too,
so the AST has a single node (and a single certificate rule) for all of them. -/
inductive Builtin : List Tp → Tp → Type
| uAdd : Builtin [.uInt32, .uInt32] .uInt32
| uSub : Builtin [.uInt32, .uInt32] .uInt32
| uMul : Builtin [.uInt32, .uInt32] .uInt32
| uDiv : Builtin [.uInt32, .uInt32] .uInt32
| uMod : Builtin [.uInt32, .uInt32] .uInt32
| uEq : Builtin [.uInt32, .uInt32] .bool
| uLt : Builtin [.uInt32, .uInt32] .bool
| uLe : Builtin [.uInt32, .uInt32] .bool

| not : Builtin [.bool] .bool
| and : Builtin [.bool, .bool] .bool
| or : Builtin [.bool, .bool] .bool
| bEq : Builtin [.bool, .bool] .bool

| pair {a b} : Builtin [a, b] (.prod a b)
| fst {a b} : Builtin [.prod a b] a
| snd {a b} : Builtin [.prod a b] b

| arrEmpty {a} : Builtin [] (.array a)
| arrPush {a} : Builtin [.array a, a] (.array a)
| arrGet {a} : Builtin [.array a, .uInt32] a
| arrSet {a} : Builtin [.array a, .uInt32, a] (.array a)
| arrLen {a} : Builtin [.array a] .uInt32

/-- Semantics of builtins. `none` means the evaluator fails (out-of-bounds
array access). Division and remainder by zero follow `UInt32` (result `0` and
the dividend respectively); array lengths wrap modulo `2^32`. -/
def Builtin.denote : Builtin inp out → HList Tp.denote inp → Option out.denote
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

inductive Expr
    (eff : EffSig) (Var : Tp → Type) :
    (γ : eff.Ctx) → Tp → Type where
| ret {γ tp} : Var tp → Expr eff Var γ tp
| lit {γ outK} : (tp : AbiTp) → (v : tp.val.denote) →
    (Var tp → Expr eff Var γ outK) → Expr eff Var γ outK
| builtin {γ inp out outK} :
    (b : Builtin inp out) → HList Var inp →
    (Var out → Expr eff Var γ outK) → Expr eff Var γ outK
| lam {γ inp out outK} : (Var inp → Expr eff Var γ out) →
    (Var (.fn inp out) → Expr eff Var γ outK) → Expr eff Var γ outK
| app {γ inp out outK} : (f : Var (.fn inp out)) → (x : Var inp) →
    (Var out → Expr eff Var γ outK) → Expr eff Var γ outK
| ite {γ out outK} : (c : Var .bool) → (t e : Expr eff Var γ out) →
    (Var out → Expr eff Var γ outK) → Expr eff Var γ outK
| loop {γ c outK} :
    (body : Var c → Expr eff Var γ (Tp.prod c .bool)) →
    (init : Var c) →
    (Var c → Expr eff Var γ outK) → Expr eff Var γ outK
| op {γ outK} : (e : eff.tag γ) → (inp : Var (eff.input γ e)) →
    (blocks :
      (b : eff.blockTag γ e) →
      Var (eff.blockInputs γ e b) →
      Expr eff Var (eff.blockCtx γ e b) (eff.blockOutputs γ e b)) →
    (Var (eff.output γ e) → Expr eff Var γ outK) →
    Expr eff Var γ outK

inductive Program
    (eff : EffSig)
    (mainCtx : eff.Ctx)
    (mainInput mainOutput : AbiTp)
    (Var : Tp → Type) : Type where
| define {γ inp out} :
    (Var (.fn inp out) → Var inp → Expr eff Var γ out) →
    (Var (.fn inp out) →
      Program eff mainCtx mainInput mainOutput Var) →
    Program eff mainCtx mainInput mainOutput Var
| main :
    (Var mainInput.val → Expr eff Var mainCtx mainOutput.val) →
    Program eff mainCtx mainInput mainOutput Var

structure Heap (eff : EffSig) where
  next : Nat
  env :
    Std.ExtHashMap Nat
      (Σ γ : eff.Ctx,
        Σ i : Tp,
        Σ o : Tp,
          Tp.denote i → Expr eff Tp.denote γ o)
  env_supp : ∀ id, id < next ↔ env.contains id

instance {eff} : PartialOrder (Heap eff) where
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

def Heap.empty (eff : EffSig) : Heap eff where
  next := 0
  env := default
  env_supp := by simp [default]

def Heap.alloc
    {eff : EffSig} {γ : eff.Ctx} {i o : Tp}
    (s : Heap eff)
    (f :
      Tp.denote (.fn i o) →
      Tp.denote i →
      Expr eff Tp.denote γ o) :
    Heap eff × FnRef :=
  let id := s.next
  let s' : Heap eff := {
    next := id + 1
    env := s.env.insert id ⟨γ, i, o, f id⟩
    env_supp := by
      intro i
      cases s
      grind
  }
  (s', id)

def Heap.lookup
    {eff : EffSig} {γ : eff.Ctx} {i o : Tp}
    (s : Heap eff) :
    Tp.denote (.fn i o) →
    Option (Tp.denote i → Expr eff Tp.denote γ o) := fun x => do
  let x ← s.env.get? x
  match x with
  | ⟨γ', i', o', body⟩ =>
    if h : γ = γ' ∧ i = i' ∧ o = o' then
      pure $ h.1 ▸ h.2.1 ▸ h.2.2 ▸ body
    else
      none

inductive EvalState (eff : EffSig): eff.Ctx × Type → Type _ where
| done {γ} {R}: R → EvalState eff (γ, R)
| cont {γ} {R} {i : Tp}: Heap eff → Expr eff Tp.denote γ i →
    (Heap eff → Tp.denote i → EvalState eff (γ, R)) → EvalState eff (γ, R)

def Expr.denoteCo {eff} (i : eff.Ctx × Type) : EvalState eff i → Eff.Step eff.Ctx (EvalEff eff) (EvalState eff) i
| .done v => Eff.Step.ret v
| .cont s e k => match e with
  | .ret v => Eff.Step.tau (k s v)
  | .lit _ v k' => Eff.Step.tau (EvalState.cont s (k' v) k)
  | .builtin b args k' => match b.denote args with
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

def Expr.denote {eff} {γ : eff.Ctx} {o : Tp} (state : Heap eff) (expr : Expr eff Tp.denote γ o) :
    EvalM eff γ (Heap eff × o.denote) :=
  CompM.corec denoteCo (EvalState.cont state expr fun s r => EvalState.done (s, r))

structure ExprCertAt {srcEff : EffSig} {tgtEff : srcEff.Ctx → Type} [Eff.Spec tgtEff]
    (handler : Eff.Handler srcEff.denote (Free tgtEff))
    {γ : srcEff.Ctx} {oTp : AbiTp}
    (h : Heap srcEff)
    (e : Expr srcEff Tp.denote γ oTp.val)
    (t : Free tgtEff γ oTp.val.denote) : Prop where
  wf : CompM.WF (Expr.denote h e)
  nofail : Free.UnusedL ((Expr.denote h e).toFree wf)
  correct :
    (·.2) <$> ((Expr.denote h e).toFree wf
      |>.elideL nofail
      |>.interpL (fun _ _ => pure ())
      |>.interp handler
    ) = t

def ExprCert {srcEff : EffSig} {tgtEff : srcEff.Ctx → Type} [Eff.Spec tgtEff]
    (handler : Eff.Handler srcEff.denote (Free tgtEff))
    {γ : srcEff.Ctx} {oTp : AbiTp}
    (h : Heap srcEff)
    (e : Expr srcEff Tp.denote γ oTp.val)
    (t : Free tgtEff γ oTp.val.denote) : Prop :=
  ∀ h', h ≤ h' → ExprCertAt handler h' e t

def Program.denote' {eff} {γ} {iT oT} (p: Program eff γ iT oT Tp.denote) (i: iT.val.denote):
    EvalM eff γ (Heap eff × oT.val.denote) :=
  go (Heap.empty _) p where
  go : Heap eff → Program eff γ iT oT Tp.denote →
    EvalM eff γ (Heap eff × oT.val.denote) := fun s => fun
  | .define body k =>
    let (s', f) := s.alloc (fun f x => body f x)
    go s' (k f)
  | .main body => Expr.denote s (body i)

def Program.denote {eff} {γ} {iT oT} (p: Program eff γ iT oT Tp.denote) (i: iT.val.denote):
    EvalM eff γ oT.val.denote :=
  (·.2) <$> Program.denote' p i

structure ProgramCert {srcEff : EffSig} {tgtEff : srcEff.Ctx → Type} [Eff.Spec tgtEff]
    (handler : Eff.Handler srcEff.denote (Free tgtEff))
    {iTp oTp : AbiTp} {γ : srcEff.Ctx}
    (p : ∀{V}, Program srcEff γ iTp oTp V)
    (t : iTp.val.denote → Free tgtEff γ oTp.val.denote) where
  wf : ∀ i, CompM.WF (p.denote i)
  nofail : ∀ i, Free.UnusedL ((p.denote i).toFree $ wf i)
  correct : ∀ i, (
    p.denote i
    |>.toFree (wf i)
    |>.elideL (nofail i)
    |>.interpL (fun _ _ => pure ())
    |>.interp handler
  ) = t i

end Freigen.Ast
