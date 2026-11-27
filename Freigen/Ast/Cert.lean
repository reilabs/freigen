import Freigen.Ast.Eval
import Freigen.CompM.Implements

/-!
Certificates and their rules. A program is certified by correctness
(`ExprCert`), proved compositionally: where evaluation goes, it is correct
against the source (`CompM.Corr`), with results related by a relation. A
source value may be represented by an AST value of another type (a proof of a
`Prop` by `()`), and continuations are only certified on related pairs. This
holds at every operation: each is paired with a source operation by a spec
(`Free.SimSpec`), which erases the source operation's output, and what its
blocks take and return, to the AST's; for a lift, every one of these by the
erasure at its representation (`Lift.simSpec`). An output that erases no source output
(a proof of a false `Prop`) constrains nothing.

Certificates are stated from every heap extending a given one, in
continuation style: evaluating the expression and then handing its final heap
and value to any certified continuation is correct against the source
followed by the continuation's source. The final heap is only ever passed to
the continuation, so certificates never mention it. Function certificates
(`FnCert`) say that a heap reference resolves to a correct body. Program
certificates are assembled from them.

Every rule is proved from the evaluator's unfolding equations and the heap
lemmas; none unfolds the evaluator. Rules share one shape: an AST template
under a continuation, premises for its holes, and a certificate for the
continuation on every result. Rules whose source ends in a bind come with a
tail-position variant, where the continuation is a return.
-/

namespace Freigen.Ast

open CompM (Corr)

variable {L : Language} {M : L.Model} {Γ' : Type c} {F : Γ' → Type u}
  [Eff.Spec.{_, u, 0} F] (spec : Free.SimSpec (L.denote M) F)

/-! ## Builtins that may fail

Their success is a premise of `ExprCert.builtin`; for
array accesses it follows from the source's bounds proof. -/

theorem Builtin.denote_arrGet {a : L.Tp} {xs : Array (M.V a)} {i : UInt32}
    (h : i.toNat < xs.size) :
    Builtin.denote M (.arrGet (a := a)) (h![xs, i] : HList M.V [.array a, .uInt32]) =
      some (xs[i.toNat]'h) := by
  simp [Builtin.denote, h]

theorem Builtin.denote_arrSet {a : L.Tp} {xs : Array (M.V a)} {i : UInt32} {x : M.V a}
    (h : i.toNat < xs.size) :
    Builtin.denote M (.arrSet (a := a)) (h![xs, i, x] : HList M.V [.array a, .uInt32, a]) =
      some (xs.set i.toNat x h) := by
  simp [Builtin.denote, h]

/-- A `u32` bounds check against an array's length bounds the index: lengths
wrap modulo `2^32`, so they only shrink. -/
theorem toNat_lt_size {α : Type} {i : UInt32} {xs : Array α} (h : i < xs.size.toUInt32) :
    i.toNat < xs.size := by
  have := UInt32.lt_iff_toNat_lt.mp h
  simp only [Nat.toUInt32] at this
  exact Nat.lt_of_lt_of_le this (Nat.mod_le _ _)

/-! ## Correctness -/

/-- On related values, `K` is correct against `tk` (up to `g`), from every
heap extending `h`. -/
def ContCert {γ : L.Ctx} {γ' : Γ'} {o : L.Tp} {α β β' : Type} (h : Heap L M)
    (R : M.V o → α → Prop) (g : β' → β)
    (K : Heap L M × M.V o → EvalM L M γ β) (tk : α → Free F γ' β') : Prop :=
  ∀ h', h ≤ h' → ∀ v a, R v a → Corr spec g (K (h', v)) (tk a)

/-- From every heap extending `h`, evaluating `e` followed by any certified
continuation is correct against `t` followed by the continuation's source.
The value of `e` and the result of `t` are related by `R`. -/
def ExprCert {γ : L.Ctx} {γ' : Γ'} {o : L.Tp} {α : Type} (h : Heap L M) (e : Expr L M.V γ o)
    (R : M.V o → α → Prop) (t : Free F γ' α) : Prop :=
  ∀ h', h ≤ h' → ∀ {β β' : Type} (g : β' → β)
    (K : Heap L M × M.V o → EvalM L M γ β) tk,
    ContCert spec h' R g K tk → Corr spec g (e.denote h' >>= K) (t >>= tk)

/-- `f` resolves in `h` to a body that is correct against `src` on related arguments,
with results related by `Ro`. The source's result type, and so the relation,
may depend on its argument. It holds in every extension of `h`; see
`FnCert.mono`. -/
def FnCert {γ : L.Ctx} {γ' : Γ'} {inp out : L.Tp} {α : Type} {β : α → Type} (h : Heap L M)
    (f : M.V (.fn inp out)) (Ri : M.V inp → α → Prop) (Ro : (y : α) → M.V out → β y → Prop)
    (src : (y : α) → Free F γ' (β y)) : Prop :=
  ∃ g : M.V inp → Expr L M.V γ out, h.lookup f = some g ∧
    ∀ x y, Ri x y → ExprCert spec h (g x) (Ro y) (src y)

/-- The rest of a program, run from heap `h`, is correct against `t` on every
input once the final heap is dropped, with results erased by `eo` (at the end,
the erasure at the result's representation). The result type, and so its
erasure, may depend on the input. -/
def ProgCert {γ : L.Ctx} {γ' : Γ'} {iT oT : L.AbiTp} {β : M.V iT.val → Type} (h : Heap L M)
    (p : Program L γ iT oT M.V) (eo : (i : M.V iT.val) → β i → M.V oT.val)
    (t : (i : M.V iT.val) → Free F γ' (β i)) : Prop :=
  ∀ i, Corr spec (eo i) (Prod.snd <$> Program.denote'.go i h p) (t i)

variable {spec} {γ : L.Ctx} {γ' : Γ'} {o : L.Tp} {h : Heap L M} {α : Type}

theorem ContCert.mono {β β' : Type} {R : M.V o → α → Prop} {S : β' → β}
    {K : Heap L M × M.V o → EvalM L M γ β}
    {tk : α → Free F γ' β'} (hK : ContCert spec h R S K tk) {h' : Heap L M}
    (hle : h ≤ h') : ContCert spec h' R S K tk :=
  fun h'' hle' => hK h'' (Heap.le_trans hle hle')

theorem ExprCert.mono {e : Expr L M.V γ o} {R : M.V o → α → Prop} {t : Free F γ' α}
    (he : ExprCert spec h e R t) {h' : Heap L M} (hle : h ≤ h') :
    ExprCert spec h' e R t :=
  fun h'' hle' => he h'' (Heap.le_trans hle hle')

theorem FnCert.mono {inp out : L.Tp} {β : α → Type} {f : M.V (.fn inp out)}
    {Ri : M.V inp → α → Prop} {Ro : (y : α) → M.V out → β y → Prop}
    {src : (y : α) → Free F γ' (β y)}
    (hf : FnCert (γ := γ) spec h f Ri Ro src) {h' : Heap L M} (hle : h ≤ h') :
    FnCert (γ := γ) spec h' f Ri Ro src := by
  obtain ⟨g, hg, hc⟩ := hf
  exact ⟨g, Heap.lookup_mono hle hg, fun x y hxy => (hc x y hxy).mono hle⟩

/-! ## Correctness rules

Continuation premises quantify over what is unknown: related pairs of an AST
value and a source value where an operation or a call returns. Where the
value is known (builtins, literals), the continuation is certified at it. -/

namespace ExprCert

variable {R : M.V o → α → Prop}

/-- The top level, with results erased by `f`: the trivial continuation
drops the final heap. -/
theorem corr {e : Expr L M.V γ o} {t : Free F γ' α} {f : α → M.V o}
    (he : ExprCert spec h e (fun v a => v = f a) t) : Corr spec f (Prod.snd <$> e.denote h) t := by
  have := he h (Heap.le_refl _) f (fun p => pure p.2) pure fun _ _ v a hR => .pure_of_eq hR
  simp only [bind_pure_comp, bind_pure] at this
  exact this

/-- Running `k` and then a certified continuation is itself a certified
continuation. -/
private theorem cont {i : L.Tp} {α' : Type} {Ri : M.V i → α' → Prop}
    {k : M.V i → Expr L M.V γ o} {tk : α' → Free F γ' α}
    (hk : ∀ v a, Ri v a → ExprCert spec h (k v) R (tk a))
    {h' : Heap L M} (hle : h ≤ h') {β β' : Type} {S : β' → β}
    {K : Heap L M × M.V o → EvalM L M γ β}
    {tK : α → Free F γ' β'} (hK : ContCert spec h' R S K tK) :
    ContCert spec h' Ri S (fun p => (k p.2).denote p.1 >>= K) (fun a => tk a >>= tK) :=
  fun h'' hle' v a hR => hk v a hR h'' (Heap.le_trans hle hle') S K tK (hK.mono hle')

theorem ret {v : M.V o} {a : α} (hR : R v a) :
    ExprCert spec h (.ret v : Expr L M.V γ o) R (pure a : Free F γ' α) := by
  intro h' _ β β' S K tK hK
  rw [Expr.denote_ret, bind_assoc, pure_bind]
  simpa using Corr.tick (hK h' (Heap.le_refl _) v a hR)

/-- A literal: the continuation is certified at its value. -/
theorem lit {tp : L.AbiTp} {v : tp.val.Lit} {k : M.V tp.val → Expr L M.V γ o}
    {t : Free F γ' α} (hk : ExprCert spec h (k (tp.val.embed v)) R t) :
    ExprCert spec h (.lit tp v k) R t := by
  intro h' hle β β' S K tK hK
  rw [Expr.denote_lit, bind_assoc]
  exact .tick (hk h' hle S K tK hK)

/-- A builtin, with a proof that it succeeds on these arguments: the
continuation is certified at its result, so the source's facts about the
result (a proof about it, a type depending on it) are available. -/
theorem builtin {inp : List L.Tp} {out : L.Tp} {b : Builtin L inp out}
    {args : HList M.V inp} {r : M.V out} (hb : b.denote M args = some r)
    {k : M.V out → Expr L M.V γ o} {t : Free F γ' α}
    (hk : ExprCert spec h (k r) R t) :
    ExprCert spec h (.builtin b args k) R t := by
  intro h' hle β β' S K tK hK
  rw [Expr.denote_builtin _ hb, bind_assoc]
  exact .tick (hk h' hle S K tK hK)

theorem ite {out : L.Tp} {α' : Type} {Ri : M.V out → α' → Prop} {c : Bool}
    {t e : Expr L M.V γ out} {st se : Free F γ' α'}
    (ht : ExprCert spec h t Ri st) (he : ExprCert spec h e Ri se)
    {k : M.V out → Expr L M.V γ o} {tk : α' → Free F γ' α}
    (hk : ∀ v a, Ri v a → ExprCert spec h (k v) R (tk a)) :
    ExprCert spec h (.ite c t e k) R ((if c then st else se) >>= tk) := by
  intro h' hle β β' S K tK hK
  rw [Expr.denote_ite]
  simp only [bind_assoc]
  refine .tick ?_
  cases c
  · exact he h' hle _ _ _ (cont hk hle hK)
  · exact ht h' hle _ _ _ (cont hk hle hK)

theorem ite_tail {c : Bool} {t e : Expr L M.V γ o} {st se : Free F γ' α}
    (ht : ExprCert spec h t R st) (he : ExprCert spec h e R se) :
    ExprCert spec h (.ite c t e fun v => .ret v) R (if c then st else se) := by
  simpa using ite ht he fun _ _ hR => ret hR

/-- A branch on a decidable proposition, computed by a builtin. Each branch is
certified under its side of the condition, so the source's proofs about it
are available in both certificates. -/
theorem dite {inp : List L.Tp} {b : Builtin L inp .bool} {args : HList M.V inp}
    {p : Prop} [Decidable p] (hb : b.denote M args = some (decide p)) {out : L.Tp}
    {α' : Type} {Ri : M.V out → α' → Prop} {t e : Expr L M.V γ out}
    {st : p → Free F γ' α'} {se : ¬p → Free F γ' α'}
    (ht : ∀ hp : p, ExprCert spec h t Ri (st hp))
    (he : ∀ hp : ¬p, ExprCert spec h e Ri (se hp))
    {k : M.V out → Expr L M.V γ o} {tk : α' → Free F γ' α}
    (hk : ∀ v a, Ri v a → ExprCert spec h (k v) R (tk a)) :
    ExprCert spec h (.builtin b args fun c => .ite c t e k) R (dite p st se >>= tk) := by
  refine builtin hb ?_
  intro h' hle β β' S K tK hK
  simp only [Expr.denote_ite, bind_assoc]
  refine .tick ?_
  by_cases hp : p
  · simp only [dif_pos hp, decide_eq_true hp, ↓reduceIte]
    exact ht hp h' hle _ _ _ (cont hk hle hK)
  · simp only [dif_neg hp, decide_eq_false hp, Bool.false_eq_true, ↓reduceIte]
    exact he hp h' hle _ _ _ (cont hk hle hK)

theorem dite_tail {inp : List L.Tp} {b : Builtin L inp .bool} {args : HList M.V inp}
    {p : Prop} [Decidable p] (hb : b.denote M args = some (decide p))
    {t e : Expr L M.V γ o} {st : p → Free F γ' α} {se : ¬p → Free F γ' α}
    (ht : ∀ hp : p, ExprCert spec h t R (st hp))
    (he : ∀ hp : ¬p, ExprCert spec h e R (se hp)) :
    ExprCert spec h (.builtin b args fun c => .ite c t e fun v => .ret v) R
      (_root_.dite p st se) := by
  simpa using dite hb ht he fun _ _ hR => ret hR

/-- Effects: a pair `q` of the spec, the AST's operation its source. Each
block of the source operation is matched by the AST's on the erasure of its
input, with results erased as the spec says (`hb`), and the continuation is
certified at the erasure of every output of the source operation (`hk`).
Outputs that erase no source output (a certificate for a false assertion)
leave nothing to certify. -/
theorem op (q : spec.Op γ γ')
    {blocks :
      (b : L.Block γ (spec.src q).1) →
      M.V (L.blockInputs γ (spec.src q).1 b).val →
      Expr L M.V (L.blockCtx γ (spec.src q).1 b) (L.blockOutputs γ (spec.src q).1 b).val}
    {sb :
      (t : Eff.Spec.blockTag γ' (spec.tgt q)) →
      Eff.Spec.blockInputs γ' (spec.tgt q) t →
      Free F (Eff.Spec.blockCtx γ' (spec.tgt q) t) (Eff.Spec.blockOutputs γ' (spec.tgt q) t)}
    (hb : ∀ t y, ExprCert spec h (blocks (spec.tag q t) (spec.inp q t y))
      (fun v a => v = spec.out q t a) (sb t y))
    {k : M.V (L.output γ (spec.src q).1).val → Expr L M.V γ o}
    {tk : Eff.Spec.output γ' (spec.tgt q) → Free F γ' α}
    (hk : ∀ a, ExprCert spec h (k (spec.res q a)) R (tk a)) :
    ExprCert spec h (.op (spec.src q).1 (spec.src q).2 blocks k) R
      (Free.op (spec.tgt q) sb >>= tk) := by
  intro h' hle β β' g K tK hK
  rw [Expr.denote_op, bind_assoc, bind_assoc]
  exact .op (E := L.denote M) q (fun t y => ((hb t y).mono hle).corr)
    fun a => hk a h' hle g K tK hK

/-- An operation over the identity spec: its source is the same operation. -/
theorem op_eq {γ : L.Ctx} {e : L.Op γ} {inp : M.V (L.input γ e).val}
    {blocks :
      (b : L.Block γ e) →
      M.V (L.blockInputs γ e b).val →
      Expr L M.V (L.blockCtx γ e b) (L.blockOutputs γ e b).val}
    {sb :
      (b : L.Block γ e) →
      M.V (L.blockInputs γ e b).val →
      Free (L.denote M) (L.blockCtx γ e b) (M.V (L.blockOutputs γ e b).val)}
    (hb : ∀ b x, ExprCert (Lift.id L M).simSpec h (blocks b x) Eq (sb b x))
    {k : M.V (L.output γ e).val → Expr L M.V γ o} {R : M.V o → α → Prop}
    {tk : M.V (L.output γ e).val → Free (L.denote M) γ α}
    (hk : ∀ v, ExprCert (Lift.id L M).simSpec h (k v) R (tk v)) :
    ExprCert (Lift.id L M).simSpec h (.op e inp blocks k) R
      (Free.op (E := L.denote M) (γ := γ) (Sigma.mk e inp : L.denote M γ) sb >>= tk) :=
  op (spec := (Lift.id L M).simSpec) (.mk ⟨e, inp⟩ (.mk e inp)) hb hk

theorem op_eq_tail {γ : L.Ctx} {e : L.Op γ} {inp : M.V (L.input γ e).val}
    {blocks :
      (b : L.Block γ e) →
      M.V (L.blockInputs γ e b).val →
      Expr L M.V (L.blockCtx γ e b) (L.blockOutputs γ e b).val}
    {sb :
      (b : L.Block γ e) →
      M.V (L.blockInputs γ e b).val →
      Free (L.denote M) (L.blockCtx γ e b) (M.V (L.blockOutputs γ e b).val)}
    (hb : ∀ b x, ExprCert (Lift.id L M).simSpec h (blocks b x) Eq (sb b x)) :
    ExprCert (Lift.id L M).simSpec h (.op e inp blocks fun v => .ret v) Eq
      (Free.op (E := L.denote M) (γ := γ) (Sigma.mk e inp : L.denote M γ) sb) := by
  have := op_eq (inp := inp) (tk := Pure.pure) (R := Eq) hb fun _ => ret rfl
  rwa [bind_pure] at this

/-- Local closures: the continuation is certified against every reference
that carries a function certificate for the body. -/
theorem lam {inp out : L.Tp} {αi : Type} {αo : αi → Type} {Ri : M.V inp → αi → Prop}
    {Ro : (y : αi) → M.V out → αo y → Prop} {b : M.V inp → Expr L M.V γ out}
    {src : (y : αi) → Free F γ' (αo y)}
    (hb : ∀ x y, Ri x y → ExprCert spec h (b x) (Ro y) (src y))
    {k : M.V (.fn inp out) → Expr L M.V γ o} {t : Free F γ' α}
    (hk : ∀ h' r, h ≤ h' → FnCert (γ := γ) spec h' r Ri Ro src → ExprCert spec h' (k r) R t) :
    ExprCert spec h (.lam b k) R t := by
  intro h' hle β β' S K tK hK
  rw [Expr.denote_lam, bind_assoc]
  have hal := Heap.le_alloc h' fun _ x => b x
  have hle' := Heap.le_trans hle hal
  exact .tick (hk _ _ hle' ⟨_, Heap.lookup_alloc .., fun x y hxy => (hb x y hxy).mono hle'⟩ _
    (Heap.le_refl _) S K tK (hK.mono hal))

/-- Calls: the callee's function certificate rules out the failing cases. -/
theorem app {inp out : L.Tp} {αi : Type} {αo : αi → Type} {Ri : M.V inp → αi → Prop}
    {Ro : (y : αi) → M.V out → αo y → Prop} {f : M.V (.fn inp out)}
    {src : (y : αi) → Free F γ' (αo y)} (hf : FnCert (γ := γ) spec h f Ri Ro src)
    {x : M.V inp} {y : αi} (hxy : Ri x y) {k : M.V out → Expr L M.V γ o}
    {tk : αo y → Free F γ' α} (hk : ∀ v a, Ro y v a → ExprCert spec h (k v) R (tk a)) :
    ExprCert spec h (.app f x k) R (src y >>= tk) := by
  intro h' hle β β' S K tK hK
  obtain ⟨g, hg, hc⟩ := hf
  rw [Expr.denote_app _ (Heap.lookup_mono hle hg)]
  simp only [bind_assoc]
  exact .tick (hc x y hxy h' hle _ _ _ (cont hk hle hK))

theorem app_tail {inp : L.Tp} {αi : Type} {αo : αi → Type} {Ri : M.V inp → αi → Prop}
    {Ro : (y : αi) → M.V o → αo y → Prop} {f : M.V (.fn inp o)}
    {src : (y : αi) → Free F γ' (αo y)} (hf : FnCert (γ := γ) spec h f Ri Ro src)
    {x : M.V inp} {y : αi} (hxy : Ri x y) :
    ExprCert spec h (.app f x fun v => .ret v : Expr L M.V γ o) (Ro y) (src y) := by
  simpa using app hf hxy fun _ _ hR => ret hR

end ExprCert

/-! ## Programs -/

namespace ProgCert

variable {iT oT : L.AbiTp} {β : M.V iT.val → Type} {eo : (i : M.V iT.val) → β i → M.V oT.val}
  {t : (i : M.V iT.val) → Free F γ' (β i)}

theorem main {body : M.V iT.val → Expr L M.V γ oT.val}
    (hb : ∀ i, ExprCert spec h (body i) (fun v a => v = eo i a) (t i)) :
    ProgCert spec h (.main body) eo t := by
  intro i
  rw [Program.denote'_go_main]
  exact (hb i).corr

/-- A non-recursive definition. Its body is certified at the current heap, for
any self-reference; the rest of the program is certified against every
reference that carries the resulting function certificate. -/
theorem define {δ : L.Ctx} {δ' : Γ'} {inp out : L.Tp} {αi : Type} {αo : αi → Type}
    {Ri : M.V inp → αi → Prop} {Ro : (y : αi) → M.V out → αo y → Prop}
    {body : M.V (.fn inp out) → M.V inp → Expr L M.V δ out}
    {src : (y : αi) → Free F δ' (αo y)}
    (hb : ∀ r x y, Ri x y → ExprCert spec h (body r x) (Ro y) (src y))
    {k : M.V (.fn inp out) → Program L γ iT oT M.V}
    (hk : ∀ h' r, h ≤ h' → FnCert (γ := δ) spec h' r Ri Ro src →
      ProgCert spec h' (k r) eo t) :
    ProgCert spec h (.define body k) eo t := by
  intro i
  rw [Program.denote'_go_define]
  have hle := Heap.le_alloc h fun f x => body f x
  exact hk _ _ hle ⟨_, Program.lookup_define .., fun x y hxy => (hb _ x y hxy).mono hle⟩ i

end ProgCert

/-- The public program certificate, from the empty heap, with the result
erased at its representation. -/
theorem ProgramCert.of_progCert {ℓ : Lift.{u, w} L M} {iT oT : L.AbiTp}
    {α : M.V iT.val → Type} {r : (i : M.V iT.val) → ℓ.Rep oT (α i)}
    {p : ∀ {V}, Program L γ iT oT V} {t : (i : M.V iT.val) → Free ℓ.SrcOp γ (α i)}
    (hp : ProgCert ℓ.simSpec (Heap.empty L M) p (fun i => ℓ.erase (r i)) t) :
    ProgramCert ℓ r p t := fun i => by
  rw [Program.denote_eq]
  exact hp i

end Freigen.Ast
