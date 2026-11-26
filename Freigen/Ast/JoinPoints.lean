import Freigen.Ast.Bind

/-!
Join-point elimination. Lean's `do` elaborator compiles a branch followed by
more code into a local closure, the join point, called in tail position at the
end of each path of the branch:

```
lam (fun y => rest) fun jp =>
  ite c (… app jp a ret) (… app jp b ret) ret
```

The pass turns the join point into the continuation of the branch, which
evaluates `rest` once, after either path, without a closure:

```
ite c (… ret a) (… ret b) (fun y => rest)
```

A closure `lam b k` is a join point when its result type is that of its scope
and its variable occurs in the scope only as the head of tail calls
`app jp y ret`, on every path of the scope that returns. Paths reach the end
of the scope through the continuations of every node, and through the branches
of an `ite` whose continuation returns. The pass replaces the tail calls on
the continuation spine by the body, and those in branches by returns, and makes
the body the continuation of each such branch. Since the spine ends once, and a
branch hands its value to its continuation, the body is placed once. That is,
the scope is translated with every tail call as a return (`Jr`) and followed by
the body (`Expr.bind`). Closures
that are not join points are kept: those used elsewhere, or whose scope also
returns without calling them (an early `return`).

The pass instantiates its input at variables that may be labels (`PVar`):
join point candidates are labels, so their occurrences can be found. `ok`
decides whether a scope can be translated, by instantiating its binders at
fresh labels; `tr` translates, given that it can. Where `ok` holds, `tr` never
meets a label outside a tail call; where it would (never, for well-formed
inputs), it produces an expression that fails (`stuck`), since PHOAS gives it
no variable to use.
-/

namespace Freigen.Ast

/-- An enumeration of each operation's blocks. The pass needs it to look for
join points used inside blocks, which are calls, not tail calls. -/
class Language.Blocks (L : Language) where
  blocks : (γ : L.Ctx) → (e : L.Op γ) → List (L.Block γ e)
  complete : ∀ γ e b, b ∈ blocks γ e

namespace JoinPoints

variable {L : Language} {V : L.Tp → Type}

/-- The pass's input variables: variables of the output, or labels. -/
abbrev PVar (V : L.Tp → Type) (t : L.Tp) : Type := V t ⊕ Nat

/-! ## Deciding join points -/

/-- The variable is none of the join point labels `J`. -/
def free (J : List Nat) {t : L.Tp} : PVar V t → Bool
  | .inl _ => true
  | .inr l => !J.contains l

def freeArgs (J : List Nat) : {ts : List L.Tp} → HList (PVar V) ts → Bool
  | [], .nil => true
  | _ :: _, .cons x xs => free J x && freeArgs J xs

/-- The variable is the label `ℓ`. -/
def isLabel (ℓ : Nat) {t : L.Tp} : PVar V t → Bool
  | .inl _ => false
  | .inr l => l == ℓ

/-- The continuation returns its argument, tested at the label `n`, which is
fresh. -/
def isRet {γ : L.Ctx} {t o : L.Tp} (n : Nat)
    (k : PVar V t → Expr L (PVar V) γ o) : Bool :=
  match k (.inr n) with
  | .ret x => isLabel n x
  | _ => false

variable [L.Blocks]

/-- Whether an expression can be translated in a mode: normal (`act = none`),
or in the scope of the join point `ℓ` (`act = some ℓ`), where returning is
calling it in tail position. Variables labelled by `J`, the join points in
scope, may only be called in tail position, and only the active one. Binders
are instantiated at fresh labels from `n` on. -/
def ok : {γ : L.Ctx} → {o : L.Tp} → (n : Nat) → (J : List Nat) → (act : Option Nat) →
    Expr L (PVar V) γ o → Bool
  | _, _, _, J, none, .ret x => free J x
  | _, _, _, _, some _, .ret _ => false
  | _, _, n, J, a, .lit _ _ k => ok (n + 1) J a (k (.inr n))
  | _, _, n, J, a, .builtin _ args k => freeArgs J args && ok (n + 1) J a (k (.inr n))
  | _, o, n, J, a, .lam (out := out) b k =>
    (decide (out = o) && ok (n + 1) J a (b (.inr n)) &&
        ok (n + 1) (n :: J) (some n) (k (.inr n))) ||
      (ok (n + 1) J none (b (.inr n)) && ok (n + 1) J a (k (.inr n)))
  | _, _, n, J, none, .app f x k => free J f && free J x && ok (n + 1) J none (k (.inr n))
  | _, _, n, J, some ℓ, .app f x k =>
    (isLabel ℓ f && isRet n k && free J x) ||
      (free J f && free J x && ok (n + 1) J (some ℓ) (k (.inr n)))
  | _, _, n, J, none, .ite c t e k =>
    free J c && ok n J none t && ok n J none e && ok (n + 1) J none (k (.inr n))
  | _, _, n, J, some ℓ, .ite c t e k =>
    if isRet n k then free J c && ok n J (some ℓ) t && ok n J (some ℓ) e
    else free J c && ok n J none t && ok n J none e && ok (n + 1) J (some ℓ) (k (.inr n))
  | _, _, n, J, a, .loop body init k =>
    free J init && ok (n + 1) J none (body (.inr n)) && ok (n + 1) J a (k (.inr n))
  | γ, _, n, J, a, .op e inp blocks k =>
    free J inp && (Language.Blocks.blocks γ e).all (fun b => ok (n + 1) J none (blocks b (.inr n))) &&
      ok (n + 1) J a (k (.inr n))

/-- Whether `lam b k` is a join point in the mode `act`. -/
def elimOk {γ : L.Ctx} {o inp out : L.Tp} (n : Nat) (J : List Nat) (act : Option Nat)
    (b : PVar V inp → Expr L (PVar V) γ out)
    (k : PVar V (.fn inp out) → Expr L (PVar V) γ o) : Bool :=
  decide (out = o) && ok (n + 1) J act (b (.inr n)) && ok (n + 1) (n :: J) (some n) (k (.inr n))

/-! ## Translation -/

/-- An expression of any type, for unreachable cases: it fails, by reading
an empty array. -/
def stuck {γ : L.Ctx} {o : L.Tp} (t : L.Tp) (k : V t → Expr L V γ o) : Expr L V γ o :=
  .builtin .arrEmpty .nil fun xs =>
    .lit AbiTp.uInt32 (0 : UInt32) fun i =>
      .builtin .arrGet h![xs, i] k

/-- A variable of the output, or `stuck` for a label. -/
def var {γ : L.Ctx} {o t : L.Tp} (x : PVar V t) (k : V t → Expr L V γ o) : Expr L V γ o :=
  match x with
  | .inl v => k v
  | .inr _ => stuck t k

def vars {γ : L.Ctx} {o : L.Tp} : {ts : List L.Tp} → HList (PVar V) ts →
    (HList V ts → Expr L V γ o) → Expr L V γ o
  | [], .nil, k => k .nil
  | _ :: _, .cons x xs, k => var x fun v => vars xs fun vs => k (.cons v vs)

/-- Translation modes: normal, or in the scope of the join point labelled `ℓ`,
whose tail calls are translated by `κ`. -/
inductive Mode (V : L.Tp → Type) (γ : L.Ctx) : L.Tp → L.Tp → Type
| normal {o : L.Tp} : Mode V γ o o
| jump {o o' τ : L.Tp} (ℓ : Nat) (κ : V τ → Expr L V γ o') : Mode V γ o o'

def Mode.act {γ : L.Ctx} {o o' : L.Tp} : Mode V γ o o' → Option Nat
  | .normal => none
  | .jump ℓ _ => some ℓ

/-- A join point's scope `e`, translated with its tail calls (of the join
point labelled `ℓ`) as returns, where that is possible: not where a path of
the scope returns without calling the join point, or uses it otherwise.
`trS` translates the scope in a mode; `tr` passes its own translation, so that
it recurses on the scope itself. -/
def Jr {γ : L.Ctx} {o τ : L.Tp} (n : Nat) (J : List Nat) (ℓ : Nat) (e : Expr L (PVar V) γ o)
    (trS : Mode V γ o τ → Expr L V γ τ) : Option (Expr L V γ τ) :=
  if ok n J (some ℓ) e then some (trS (.jump ℓ fun v => .ret v)) else none

/-- Translates an expression in a mode, eliminating the join points in it.
`J` labels the join points in scope; labels from `n` on are fresh. Labels are
counted as `ok` counts them, one per binder, so `tr` decides with `ok` at its
own counter. -/
def tr : {γ : L.Ctx} → {o o' : L.Tp} → (n : Nat) → (J : List Nat) → Mode V γ o o' →
    Expr L (PVar V) γ o → Expr L V γ o'
  | _, _, _, _, _, .normal, .ret x => var x .ret
  | _, _, _, _, _, .jump _ κ, .ret _ => stuck _ κ
  | _, _, _, n, J, m, .lit tp v k => .lit tp v fun x => tr (n + 1) J m (k (.inl x))
  | _, _, _, n, J, m, .builtin b args k =>
    vars args fun a => .builtin b a fun x => tr (n + 1) J m (k (.inl x))
  | _, o, o', n, J, m, .lam (out := out) b k =>
    if h : out = o then
      match (if ok (n + 1) J m.act (b (.inr n)) then
          Jr (n + 1) (n :: J) n (k (.inr n)) fun m' => tr (n + 1) (n :: J) m' (k (.inr n))
        else none) with
      | some s => s.bind fun y => tr (n + 1) J (Eq.mpr (congrArg (Mode V _ · o') h) m) (b (.inl y))
      | none => .lam (fun x => tr (n + 1) J .normal (b (.inl x))) fun f => tr (n + 1) J m (k (.inl f))
    else .lam (fun x => tr (n + 1) J .normal (b (.inl x))) fun f => tr (n + 1) J m (k (.inl f))
  | _, _, _, n, J, .normal, .app f x k =>
    var f fun f => var x fun x => .app f x fun r => tr (n + 1) J .normal (k (.inl r))
  | _, _, _, n, J, .jump ℓ (τ := τ) κ, .app (inp := inp) f x k =>
    if isLabel ℓ f && isRet n k then
      if h : inp = τ then var x fun y => κ (h ▸ y) else stuck _ κ
    else var f fun f => var x fun x => .app f x fun r => tr (n + 1) J (.jump ℓ κ) (k (.inl r))
  | _, _, _, n, J, .normal, .ite c t e k =>
    var c fun c => .ite c (tr n J .normal t) (tr n J .normal e) fun r =>
      tr (n + 1) J .normal (k (.inl r))
  | _, _, _, n, J, .jump ℓ κ, .ite c t e k =>
    if isRet n k then
      var c fun c => .ite c (tr n J (.jump ℓ fun v => .ret v) t) (tr n J (.jump ℓ fun v => .ret v) e) κ
    else
      var c fun c => .ite c (tr n J .normal t) (tr n J .normal e) fun r =>
        tr (n + 1) J (.jump ℓ κ) (k (.inl r))
  | _, _, _, n, J, m, .loop body init k =>
    var init fun i => .loop (fun x => tr (n + 1) J .normal (body (.inl x))) i fun r =>
      tr (n + 1) J m (k (.inl r))
  | _, _, _, n, J, m, .op e inp blocks k =>
    var inp fun i => .op e i (fun b x => tr (n + 1) J .normal (blocks b (.inl x))) fun r =>
      tr (n + 1) J m (k (.inl r))

/-- Eliminating a join point `lam b k`: its scope `Jr (k jp)`, followed by its
body. -/
theorem tr_lam_elim {γ : L.Ctx} {o o' inp : L.Tp} (n : Nat) (J : List Nat) (m : Mode V γ o o')
    (b : PVar V inp → Expr L (PVar V) γ o) (k : PVar V (.fn inp o) → Expr L (PVar V) γ o)
    (hb : ok (n + 1) J m.act (b (.inr n)) = true)
    (hk : ok (n + 1) (n :: J) (some n) (k (.inr n)) = true) :
    tr n J m (.lam b k) =
      (tr (n + 1) (n :: J) (.jump n fun v => .ret v) (k (.inr n))).bind fun y =>
        tr (n + 1) J m (b (.inl y)) := by
  simp only [tr, ↓reduceDIte, hb, ↓reduceIte, Jr, hk]
  rfl

/-- A closure that is not a join point is kept. -/
theorem tr_lam_keep {γ : L.Ctx} {o o' inp out : L.Tp} (n : Nat) (J : List Nat)
    (m : Mode V γ o o') (b : PVar V inp → Expr L (PVar V) γ out)
    (k : PVar V (.fn inp out) → Expr L (PVar V) γ o)
    (h : ¬(out = o ∧ ok (n + 1) J m.act (b (.inr n)) = true ∧
      ok (n + 1) (n :: J) (some n) (k (.inr n)) = true)) :
    tr n J m (.lam b k) =
      .lam (fun x => tr (n + 1) J .normal (b (.inl x))) fun f => tr (n + 1) J m (k (.inl f)) := by
  simp only [tr]
  split
  · rename_i he
    subst he
    by_cases hb : ok (n + 1) J m.act (b (.inr n)) = true
    · have hk : ¬ok (n + 1) (n :: J) (some n) (k (.inr n)) = true := fun hk => h ⟨rfl, hb, hk⟩
      simp only [hb, ↓reduceIte, Jr, hk]
      rfl
    · simp only [hb]
      rfl
  · rfl

/-- Translates a program: its definitions and entry point, from no labels. -/
def trProg {γ : L.Ctx} {iT oT : L.AbiTp} : Program L γ iT oT (PVar V) → Program L γ iT oT V
  | .define body k =>
    .define (fun f x => tr 0 [] .normal (body (.inl f) (.inl x))) fun f => trProg (k (.inl f))
  | .main body => .main fun x => tr 0 [] .normal (body (.inl x))

end JoinPoints

/-- Join-point elimination (see `Freigen.Ast.JoinPoints`). -/
def Program.joinPoints {L : Language} [L.Blocks] {γ : L.Ctx} {iT oT : L.AbiTp}
    (p : ∀ {V : L.Tp → Type}, Program L γ iT oT V) {V : L.Tp → Type} :
    Program L γ iT oT V :=
  JoinPoints.trProg (p (V := JoinPoints.PVar V))

end Freigen.Ast
