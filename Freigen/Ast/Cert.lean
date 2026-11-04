import Freigen.Ast.Eval
import Freigen.CompM.Implements

/-!
Certificates and their rules. An expression certificate says that, from every
heap extending a given one, evaluating the expression and then handing its
final heap and value to any good continuation implements the source followed
by the continuation's source. The final heap is only ever passed to the
continuation, so certificates never mention it. Function certificates say that
a heap reference resolves to a certified body. Program certificates are
assembled from them.

Every rule is proved from the evaluator's unfolding equations and the heap
lemmas; none unfolds the evaluator. Rules share one shape: an AST template
under a continuation, premises for its holes, and a certificate for the
continuation on every result. Rules whose source ends in a bind come with a
tail-position variant, where the continuation is a return.
-/

namespace Freigen.Ast

open CompM (Implements)

variable {eff : EffSig} {F : eff.Ctx → Type} [Eff.Spec.{0, 0} F]
  (handler : Eff.Handler eff.denote (Free F))

/-- `K` implements `tk` on every value, from every heap extending `h`. -/
def ContCert {γ : eff.Ctx} {o : Tp} {β : Type} (h : Heap eff)
    (K : Heap eff × o.denote → EvalM eff γ β) (tk : o.denote → Free F γ β) : Prop :=
  ∀ h', h ≤ h' → ∀ v, Implements handler (K (h', v)) (tk v)

/-- From every heap extending `h`, evaluating `e` followed by any certified
continuation implements `t` followed by the continuation's source. -/
def ExprCert {γ : eff.Ctx} {o : Tp} (h : Heap eff) (e : Expr eff Tp.denote γ o)
    (t : Free F γ o.denote) : Prop :=
  ∀ h', h ≤ h' → ∀ {β : Type} (K : Heap eff × o.denote → EvalM eff γ β) tk,
    ContCert handler h' K tk → Implements handler (e.denote h' >>= K) (t >>= tk)

/-- `f` resolves in `h` to a body that implements `src` on every argument. It
holds in every extension of `h`; see `FnCert.mono`. -/
def FnCert {γ : eff.Ctx} {inp out : Tp} (h : Heap eff) (f : Tp.denote (.fn inp out))
    (src : inp.denote → Free F γ out.denote) : Prop :=
  ∃ g, h.lookup f = some g ∧ ∀ x, ExprCert handler h (g x) (src x)

/-- The rest of a program, run from heap `h`, implements `t` on every input
once the final heap is dropped. -/
def ProgCert {γ : eff.Ctx} {iT oT : AbiTp} (h : Heap eff)
    (p : Program eff γ iT oT Tp.denote) (t : iT.val.denote → Free F γ oT.val.denote) :
    Prop :=
  ∀ i, Implements handler (Prod.snd <$> Program.denote'.go i h p) (t i)

/-- The identity handler: AST operations are source operations. -/
def idHandler (eff : EffSig) : Eff.Handler eff.denote (Free eff.denote) :=
  fun e blocks => Free.op e blocks

variable {handler} {γ : eff.Ctx} {o : Tp} {h : Heap eff}

theorem ContCert.mono {β : Type} {K : Heap eff × o.denote → EvalM eff γ β}
    {tk : o.denote → Free F γ β} (hK : ContCert handler h K tk) {h' : Heap eff}
    (hle : h ≤ h') : ContCert handler h' K tk :=
  fun h'' hle' => hK h'' (le_trans hle hle')

theorem ExprCert.mono {e : Expr eff Tp.denote γ o} {t : Free F γ o.denote}
    (he : ExprCert handler h e t) {h' : Heap eff} (hle : h ≤ h') :
    ExprCert handler h' e t :=
  fun h'' hle' => he h'' (le_trans hle hle')

theorem FnCert.mono {inp out : Tp} {f : Tp.denote (.fn inp out)}
    {src : inp.denote → Free F γ out.denote}
    (hf : FnCert handler h f src) {h' : Heap eff} (hle : h ≤ h') :
    FnCert handler h' f src := by
  obtain ⟨g, hg, hc⟩ := hf
  exact ⟨g, Heap.lookup_mono hle hg, fun x => (hc x).mono hle⟩

/-! ## Expressions -/

namespace ExprCert

/-- The top level: the trivial continuation drops the final heap. -/
theorem implements {e : Expr eff Tp.denote γ o} {t : Free F γ o.denote}
    (he : ExprCert handler h e t) : Implements handler (Prod.snd <$> e.denote h) t := by
  have := he h le_rfl (fun p => pure p.2) pure fun _ _ v => .pure v
  simp only [bind_pure_comp, bind_pure] at this
  exact this

/-- Running `k` and then a certified continuation is itself a certified
continuation. -/
private theorem cont {i : Tp} {k : i.denote → Expr eff Tp.denote γ o}
    {tk : i.denote → Free F γ o.denote} (hk : ∀ v, ExprCert handler h (k v) (tk v))
    {h' : Heap eff} (hle : h ≤ h') {β : Type} {K : Heap eff × o.denote → EvalM eff γ β}
    {tK : o.denote → Free F γ β} (hK : ContCert handler h' K tK) :
    ContCert handler h' (fun p => (k p.2).denote p.1 >>= K) (fun v => tk v >>= tK) :=
  fun h'' hle' v => hk v h'' (le_trans hle hle') K tK (hK.mono hle')

theorem ret (v : o.denote) :
    ExprCert handler h (.ret v : Expr eff Tp.denote γ o) (pure v) := by
  intro h' _ β K tK hK
  rw [Expr.denote_ret, bind_assoc, pure_bind]
  simpa using Implements.tick (hK h' le_rfl v)

theorem lit {tp : AbiTp} {v : tp.val.denote} {k : Tp.denote tp.val → Expr eff Tp.denote γ o}
    {tk : tp.val.denote → Free F γ o.denote} (hk : ∀ x, ExprCert handler h (k x) (tk x)) :
    ExprCert handler h (.lit tp v k) (tk v) := by
  intro h' hle β K tK hK
  rw [Expr.denote_lit, bind_assoc]
  exact .tick (hk v h' hle K tK hK)

/-- A builtin that may fail needs a proof that it succeeds on these
arguments. -/
theorem builtin {inp : List Tp} {out : Tp} {b : Builtin inp out}
    {args : HList Tp.denote inp} {r : out.denote} (hb : b.denote args = some r)
    {k : out.denote → Expr eff Tp.denote γ o} {tk : out.denote → Free F γ o.denote}
    (hk : ∀ x, ExprCert handler h (k x) (tk x)) :
    ExprCert handler h (.builtin b args k) (tk r) := by
  intro h' hle β K tK hK
  rw [Expr.denote_builtin _ hb, bind_assoc]
  exact .tick (hk r h' hle K tK hK)

theorem ite {out : Tp} {c : Bool} {t e : Expr eff Tp.denote γ out}
    {st se : Free F γ out.denote} (ht : ExprCert handler h t st)
    (he : ExprCert handler h e se) {k : out.denote → Expr eff Tp.denote γ o}
    {tk : out.denote → Free F γ o.denote} (hk : ∀ x, ExprCert handler h (k x) (tk x)) :
    ExprCert handler h (.ite c t e k) ((if c then st else se) >>= tk) := by
  intro h' hle β K tK hK
  rw [Expr.denote_ite]
  simp only [bind_assoc]
  refine .tick ?_
  cases c
  · exact he h' hle _ _ (cont hk hle hK)
  · exact ht h' hle _ _ (cont hk hle hK)

theorem ite_tail {c : Bool} {t e : Expr eff Tp.denote γ o} {st se : Free F γ o.denote}
    (ht : ExprCert handler h t st) (he : ExprCert handler h e se) :
    ExprCert handler h (.ite c t e fun v => .ret v) (if c then st else se) := by
  simpa using ite ht he ret

/-- Effects: each block is certified on its own, from the current heap; the
continuation is certified for every operation result. -/
theorem op {e : eff.tag γ} {inp : Tp.denote (eff.input γ e).val}
    {blocks :
      (b : eff.blockTag γ e) →
      Tp.denote (eff.blockInputs γ e b).val →
      Expr eff Tp.denote (eff.blockCtx γ e b) (eff.blockOutputs γ e b).val}
    {sb :
      (b : eff.blockTag γ e) →
      Tp.denote (eff.blockInputs γ e b).val →
      Free F (eff.blockCtx γ e b) (eff.blockOutputs γ e b).val.denote}
    (hb : ∀ b x, ExprCert handler h (blocks b x) (sb b x))
    {k : Tp.denote (eff.output γ e).val → Expr eff Tp.denote γ o}
    {tk : Tp.denote (eff.output γ e).val → Free F γ o.denote}
    (hk : ∀ x, ExprCert handler h (k x) (tk x)) :
    ExprCert handler h (.op e inp blocks k)
      (handler (Sigma.mk e inp : eff.denote γ) sb >>= tk) := by
  intro h' hle β K tK hK
  rw [Expr.denote_op, bind_assoc, bind_assoc]
  exact .op (E := eff.denote) _ (fun b x => ((hb b x).mono hle).implements)
    fun x => hk x h' hle K tK hK

theorem op_tail {e : eff.tag γ} {inp : Tp.denote (eff.input γ e).val}
    {blocks :
      (b : eff.blockTag γ e) →
      Tp.denote (eff.blockInputs γ e b).val →
      Expr eff Tp.denote (eff.blockCtx γ e b) (eff.blockOutputs γ e b).val}
    {sb :
      (b : eff.blockTag γ e) →
      Tp.denote (eff.blockInputs γ e b).val →
      Free F (eff.blockCtx γ e b) (eff.blockOutputs γ e b).val.denote}
    (hb : ∀ b x, ExprCert handler h (blocks b x) (sb b x)) :
    ExprCert handler h (.op e inp blocks fun v => .ret v)
      (handler (Sigma.mk e inp : eff.denote γ) sb) := by
  simpa using op hb ret

/-- Local closures: the continuation is certified against every reference
that carries a function certificate for the body. -/
theorem lam {inp out : Tp} {b : inp.denote → Expr eff Tp.denote γ out}
    {src : inp.denote → Free F γ out.denote} (hb : ∀ x, ExprCert handler h (b x) (src x))
    {k : Tp.denote (.fn inp out) → Expr eff Tp.denote γ o} {t : Free F γ o.denote}
    (hk : ∀ h' r, h ≤ h' → FnCert handler h' r src → ExprCert handler h' (k r) t) :
    ExprCert handler h (.lam b k) t := by
  intro h' hle β K tK hK
  rw [Expr.denote_lam, bind_assoc]
  have hal := Heap.le_alloc h' fun _ x => b x
  have hle' := le_trans hle hal
  exact .tick (hk _ _ hle' ⟨_, Heap.lookup_alloc .., fun x => (hb x).mono hle'⟩ _ le_rfl
    K tK (hK.mono hal))

/-- Calls: the callee's function certificate rules out the failing cases. -/
theorem app {inp out : Tp} {f : Tp.denote (.fn inp out)}
    {src : inp.denote → Free F γ out.denote} (hf : FnCert handler h f src)
    {x : inp.denote} {k : out.denote → Expr eff Tp.denote γ o}
    {tk : out.denote → Free F γ o.denote} (hk : ∀ v, ExprCert handler h (k v) (tk v)) :
    ExprCert handler h (.app f x k) (src x >>= tk) := by
  intro h' hle β K tK hK
  obtain ⟨g, hg, hc⟩ := hf
  rw [Expr.denote_app _ (Heap.lookup_mono hle hg)]
  simp only [bind_assoc]
  exact .tick (hc x h' hle _ _ (cont hk hle hK))

theorem app_tail {inp : Tp} {f : Tp.denote (.fn inp o)}
    {src : inp.denote → Free F γ o.denote} (hf : FnCert handler h f src) {x : inp.denote} :
    ExprCert handler h (.app f x fun v => .ret v) (src x) := by
  simpa using app hf ret

end ExprCert

/-! ## Programs -/

namespace ProgCert

variable {iT oT : AbiTp} {t : iT.val.denote → Free F γ oT.val.denote}

theorem main {body : iT.val.denote → Expr eff Tp.denote γ oT.val}
    (hb : ∀ i, ExprCert handler h (body i) (t i)) :
    ProgCert handler h (.main body) t := by
  intro i
  rw [Program.denote'_go_main]
  exact (hb i).implements

/-- A non-recursive definition. Its body is certified at the current heap, for
any self-reference; the rest of the program is certified against every
reference that carries the resulting function certificate. -/
theorem define {γ' : eff.Ctx} {inp out : Tp}
    {body : Tp.denote (.fn inp out) → inp.denote → Expr eff Tp.denote γ' out}
    {src : inp.denote → Free F γ' out.denote}
    (hb : ∀ r x, ExprCert handler h (body r x) (src x))
    {k : Tp.denote (.fn inp out) → Program eff γ iT oT Tp.denote}
    (hk : ∀ h' r, h ≤ h' → FnCert handler h' r src → ProgCert handler h' (k r) t) :
    ProgCert handler h (.define body k) t := by
  intro i
  rw [Program.denote'_go_define]
  have hle := Heap.le_alloc h fun f x => body f x
  exact hk _ _ hle ⟨_, Program.lookup_define .., fun x => (hb _ x).mono hle⟩ i

end ProgCert

/-- The public program certificate, from the empty heap. -/
theorem ProgramCert.of_progCert {iT oT : AbiTp}
    {p : ∀ {V}, Program eff γ iT oT V} {t : iT.val.denote → Free F γ oT.val.denote}
    (hp : ProgCert handler (Heap.empty eff) p t) : ProgramCert handler p t := by
  have hi : ∀ i, CompM.Implements handler (p.denote i) (t i) := fun i => by
    rw [Program.denote_eq]
    exact hp i
  exact {
    wf := fun i => (hi i).wf
    nofail := fun i => (hi i).nofail
    correct := fun i => (hi i).erase_eq _ _ }

end Freigen.Ast
