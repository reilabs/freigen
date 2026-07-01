import Freigen.Free
import Freigen.Reflect

/-!
# Recursion: reflecting a recursive `Free` function into a `Prog`

A structural-recursive `def f : Nat → Free Op SOp ρ` reflects into a `Prog` with a **`rec_` node** —
its body re-expressed over the call-extended signature (self-calls are the `CallOp.call` op), tied by
`mrec`, with `main` calling it.  Soundness is `mrec` adequacy: `denoteProg` of the reflected program
is `≈ ofFree (f N)` for every input `N`.  `mrec_adequacy` is the core lemma (`interp` of a call-body
is `≈` to running it with the source plugged in at each call); `recSound` packages it, and
`reflect%`'s recursive arm emits it, composing the `main`-call (`bind_ret_right`) with the `rec_`
body's adequacy.
-/

namespace Freigen

open Freigen.ITree

variable {Op : Type → Type → Type 1} {SOp : Type → Type} {ρ : Type}


/-- Run a call-body with the source `e` plugged in at each `call` (external `base` effects relabelled
    back to `Op`; a scoped block's own calls are plugged too). -/
def runSrc (e : Nat → Free Op SOp ρ) :
    {γ : Type} → Free (CallOp Op Nat ρ) SOp γ → Free Op SOp γ
  | _, .pure a => .pure a
  | _, .op (.base o) i c => .op o i (fun x => runSrc e (c x))
  | _, .op .call i c => Free.bind (e i) (fun v => runSrc e (c v))
  | _, .hop s b c => .hop s (runSrc e b) (fun x => runSrc e (c x))

/-- Every `call` argument in the body is `< bound`. -/
def callsLt (bound : Nat) : {γ : Type} → Free (CallOp Op Nat ρ) SOp γ → Prop
  | _, .pure _ => True
  | _, .op (.base _) _ c => ∀ x, callsLt bound (c x)
  | _, .op .call i c => i < bound ∧ ∀ x, callsLt bound (c x)
  | _, .hop _ b c => callsLt bound b ∧ ∀ x, callsLt bound (c x)

/-- **The adequacy step.** Interpreting a call-body is `≈` to running it with the source plugged in,
    given the source is adequate below `bound` and the body only calls below `bound`. -/
theorem adeqBody (body : Nat → Comp (CallOp Op Nat ρ) ρ) (e : Nat → Free Op SOp ρ)
    (bound : Nat) (Ho : ∀ k, k < bound → mrec body k ≈ ofFree (e k)) :
    ∀ {γ : Type} (t : Free (CallOp Op Nat ρ) SOp γ), callsLt bound t →
      interp body (ofFree t) ≈ ofFree (runSrc e t) := by
  intro γ t
  induction t with
  | pure a => intro _; simp only [ofFree, runSrc, interp_ret]; exact eutt_refl _
  | op o i c ih =>
      cases o with
      | base o' =>
          intro h
          simp only [ofFree, runSrc, interp_vis_base]
          exact eutt_vis_cong _ (fun x => ih x (h x))
      | call =>
          intro h
          simp only [ofFree, runSrc, interp_vis_call, interp_bind, ofFree_bind]
          refine eutt_tau_left ?_
          exact eutt_bind_cong (Ho i h.1) (fun x => ih x (h.2 x))
  | hop s b c ihb ihc =>
      intro h
      simp only [ofFree, runSrc, interp_bind]
      exact eutt_bind_cong (ihb h.1) (fun x => ihc x (h.2 x))

/-- **`mrec` adequacy (strong-induction shell)** over `ofFree`: the whole reflected recursion is `≈`
    its source, given each step is adequate using the adequacy of all smaller arguments. -/
theorem mrec_adequacy (body : Nat → Comp (CallOp Op Nat ρ) ρ) (e : Nat → Free Op SOp ρ)
    (Hstep : ∀ N, (∀ k, k < N → mrec body k ≈ ofFree (e k)) → mrec body N ≈ ofFree (e N)) :
    ∀ N, mrec body N ≈ ofFree (e N) :=
  fun N => Nat.strongRecOn N Hstep

/-- `adeqBody` with the `runSrc = e` bridge folded in — one step discharged against the source. -/
theorem adeqBody' (body : Nat → Comp (CallOp Op Nat ρ) ρ) (e : Nat → Free Op SOp ρ)
    (N : Nat) (t : Free (CallOp Op Nat ρ) SOp ρ)
    (IH : ∀ k, k < N → mrec body k ≈ ofFree (e k)) (hcl : callsLt N t)
    (hrun : runSrc e t = e N) :
    interp body (ofFree t) ≈ ofFree (e N) := by
  rw [← hrun]; exact adeqBody body e N IH t hcl

/-- **Generic recursion soundness** — what `reflect%` emits.  Given the reflected call-body
    `body` (a `Code` over the call-extended signature) and the source `f`, provided each call is
    below its argument (`hcl`) and running the body with `f` plugged in recovers `f` (`hrun`), the
    `mrec` denotation is `≈ ofFree ∘ f`.  Packages `denote_eq` + `mrec_adequacy` + `adeqBody'`. -/
theorem recSound {ρT : Tp}
    (body : Nat → Code (CallOp Op Nat ρT.denote) SOp (KC (CallOp Op Nat ρT.denote)) Tp.denote ρT)
    (cb : Nat → Free (CallOp Op Nat ρT.denote) SOp ρT.denote) (f : Nat → Free Op SOp ρT.denote)
    (hspec : ∀ N, denote (body N) = ofFree (cb N))
    (hrun : ∀ N, runSrc f (cb N) = f N)
    (hcl : ∀ N, callsLt N (cb N)) :
    ∀ N, mrec (fun s => denote (body s)) N ≈ ofFree (f N) := by
  have hbody : (fun s => denote (body s)) = fun s => ofFree (cb s) := funext hspec
  intro N
  rw [hbody]
  refine mrec_adequacy _ f ?_ N
  intro M IH
  exact adeqBody' _ _ _ _ IH (hcl M) (hrun M)

/-! ## The `reflect%` elaborator

`reflect% f` reflects a structural-recursive `def f : Nat → Free Op SOp ρ` into the recursion
denotation `fun N => mrec (…) N` and bundles its soundness `{ g // ∀ N, g N ≈ ofFree (f N) }`.  It
recognises the recursion (its equational lemmas), re-expresses the body over `CallOp` (self-calls →
`CallOp.call`), reflects that into a dumb `Code`, and discharges soundness via `recSound`. -/

open Lean Lean.Meta Lean.Elab.Term

/-- Recognise a structural `Nat` recursion and rebuild its recursion functional
    `fun rec k => bif k == 0 then base else step[rec, k-1]`; returns `(F, recTy)`. -/
private def reflectStructuralNatRec (fn : Expr) : MetaM (Option (Expr × Expr)) := do
  let some cName := fn.constName? | return none
  let some eqns ← getEqnsFor? cName | return none
  if eqns.size != 2 then return none
  let recTy ← inferType fn
  let .forallE _ σT _ _ := (← whnf recTy) | return none
  unless ← isDefEq σT (.const ``Nat []) do return none
  let extract (nm : Name) : MetaM (Option Expr × Option Expr) := do
    let some ci := (← getEnv).find? nm | return (none, none)
    forallTelescope ci.type fun bs body => do
      match_expr body with
      | Eq _ lhs rhs =>
        match_expr lhs.appArg! with
        | Nat.succ _ => return (none, some (← mkLambdaFVars bs rhs))
        | _          => return (some rhs, none)
      | _ => return (none, none)
  let (r01, s1) ← extract eqns[0]!
  let (r02, s2) ← extract eqns[1]!
  let some base := r01 <|> r02 | return none
  let some stepF := s1 <|> s2 | return none
  unless (stepF.find? (·.isConstOf cName)).isSome do return none
  withLocalDeclD `rec recTy fun rec =>
  withLocalDeclD `k σT fun k => do
    let condE ← mkAppM ``BEq.beq #[k, mkNatLit 0]
    let km1 ← mkAppM ``HSub.hSub #[k, mkNatLit 1]
    let succBody := (stepF.beta #[km1]).replace fun s => if s.isConstOf cName then some rec else none
    let bifE ← mkAppM ``cond #[condE, base, succBody]
    return some (← mkLambdaFVars #[rec, k] bifE, recTy)

/-- Re-express a recursion body over the `CallOp Op σ ρ` signature: self-calls (`recId _`) become the
    `call` effect, external effects `base`, `pure`/`bind`/`bif` rebuilt structurally. -/
private partial def toCallBody (recId : FVarId) (Op SOp σT ρT : Expr) (t : Expr) : MetaM Expr := do
  let t := t.consumeMData.headBeta
  if let .letE _ _ v b _ := t then return ← toCallBody recId Op SOp σT ρT (b.instantiate1 v)
  let callOp := mkAppN (.const ``ITree.CallOp []) #[Op, σT, ρT]
  if t.getAppFn.isFVar && t.getAppFn.fvarId! == recId then
    let some arg := t.getAppArgs.back? | throwError "reflect%: self-call has no argument"
    let callC := mkAppN (.const ``ITree.CallOp.call []) #[Op, σT, ρT]
    let pureC ← mkAppOptM ``Free.pure #[callOp, SOp, ρT]
    return ← mkAppM ``Free.op #[callC, arg, pureC]
  let doBind (x f : Expr) : MetaM Expr := do
    let .forallE _ X _ _ := (← whnf (← inferType f)) | throwError "reflect%: bind cont not a function"
    let xC ← toCallBody recId Op SOp σT ρT x
    let fC ← withLocalDeclD `a X fun ha => do
      mkLambdaFVars #[ha] (← toCallBody recId Op SOp σT ρT (f.beta #[ha]))
    mkAppM ``Free.bind #[xC, fC]
  match_expr t with
  | Free.pure _ _ _ r => mkAppOptM ``Free.pure #[callOp, SOp, none, r]
  | Pure.pure _ _ _ r => mkAppOptM ``Free.pure #[callOp, SOp, none, r]
  | Bind.bind _ _ _ _ x f => doBind x f
  | Free.bind _ _ _ _ x f => doBind x f
  | cond _ c m1 m2 => do
      let a ← toCallBody recId Op SOp σT ρT m1
      let b ← toCallBody recId Op SOp σT ρT m2
      mkAppM ``cond #[c, a, b]
  | Free.op _ _ _ I R o i k => do
      let baseO := mkAppN (.const ``ITree.CallOp.base []) #[Op, σT, ρT, I, R, o]
      let kC ← withLocalDeclD `x R fun hx => do
        mkLambdaFVars #[hx] (← toCallBody recId Op SOp σT ρT (k.beta #[hx]))
      mkAppM ``Free.op #[baseO, i, kC]
  | Free.hop _ _ _ β s b k => do
      let bC ← toCallBody recId Op SOp σT ρT b
      let kC ← withLocalDeclD `x β fun hx => do
        mkLambdaFVars #[hx] (← toCallBody recId Op SOp σT ρT (k.beta #[hx]))
      mkAppM ``Free.hop #[s, bC, kC]
  | _ =>
      match ← unfoldDefinition? t with
      | some t' => toCallBody recId Op SOp σT ρT t'
      | none    => throwError "reflect%: cannot reflect recursion body{indentExpr t}"

/-- Reflect a structural-recursive `def f : Nat → Free Op SOp ρ` into `{ g // ∀ N, g N ≈ ofFree
    (f N) }` — the `mrec` denotation and its soundness.  The recursive arm of `reflect%`. -/
def reflectRec (F recTy : Expr) (cName : Name) : TermElabM Expr := do
  let .forallE _ σT codom _ := (← whnf recTy) | throwError "reflect%: recursion must be `Nat → _`"
  let_expr Free Op SOp ρT := (← whnf codom)
    | throwError "reflect%: recursion result must be `Free Op SOp _`"
  let callOp := mkAppN (.const ``ITree.CallOp []) #[Op, σT, ρT]
  let σTp ← reifyTpOrThrow σT
  let ρTp ← reifyTpOrThrow ρT
  let kcCallOp ← mkAppM ``KC #[callOp]
  let denoteV := Lean.mkConst ``Tp.denote []
  let tpTy := (.const ``Tp [] : Expr)
  let σTpList ← mkListLit tpTy [σTp]
  let fTy ← mkArrow (← mkAppM ``List #[tpTy]) (← mkArrow tpTy (mkSort (.succ (.succ .zero))))
  let vTy ← mkArrow tpTy (mkSort (.succ .zero))
  let defs ← IO.mkRef (#[] : Array DefEntry)
  let defsUsed ← IO.mkRef (#[] : Array Name)
  let fFn := .const cName []
  -- `cb` : the Free call-body `fun s => …`
  let cb ← withLocalDeclD `s σT fun s => do
    let cbT ← withLocalDeclD `rec recTy fun rec =>
      toCallBody rec.fvarId! Op SOp σT ρT ((F.beta #[rec]).beta #[s])
    mkLambdaFVars #[s] cbT
  -- `recBody` : the `rec_` body `fun V0 F' argAtom => …`, parametric in the value/function reps
  let recBody ← withLocalDeclD `V0 vTy fun Vp0 => withLocalDeclD `F' fTy fun F' =>
    withLocalDeclD `arg (mkApp Vp0 σTp) fun argAtom => do
      let codeT ← withLocalDeclD `s σT fun s => withLocalDeclD `rec recTy fun rec => do
        let cbT ← toCallBody rec.fvarId! Op SOp σT ρT ((F.beta #[rec]).beta #[s])
        let env : Env := { Op := callOp, SOp, F := F', V := Vp0, subst := [(s.fvarId!, argAtom)],
                           defs, defsUsed }
        env.walkProg cbT (env.mkRet ·)
      mkLambdaFVars #[Vp0, F', argAtom] codeT
  -- `bodyCode` : `recBody` at `V := Tp.denote`, `F := KC callOp` — what `recSound`/`denoteProg` see
  let bodyCode := recBody.beta #[denoteV, kcCallOp]
  -- the soundness hypotheses (the body homom + `mrec` adequacy side-conditions)
  let eId := mkIdent cName
  let hspec ← withLocalDeclD `N σT fun N => do
    mkForallFVars #[N] (← mkEq (← mkAppM ``denote #[bodyCode.beta #[N]])
      (← mkAppM ``ofFree #[cb.beta #[N]]))
  let hspecPrf ← elabTermEnsuringType (← `(by
      intro N; simp only [Freigen.denote, Freigen.ofFree,
        Freigen.ofFree_bind, Freigen.ofFree_cond, Freigen.Bin.denote,
        Freigen.Un.denote, Freigen.ITree.bind_vis, Freigen.ITree.bind_ret,
        Freigen.ITree.bind_assoc])) (some hspec)
  let hrun ← withLocalDeclD `N σT fun N => do
    mkForallFVars #[N] (← mkEq (← mkAppM ``runSrc #[fFn, cb.beta #[N]]) (mkApp fFn N))
  let hrunPrf ← elabTermEnsuringType (← `(by
      intro N; rcases N with _ | m <;>
        simp [Freigen.runSrc, Freigen.Free.bind, Freigen.Free.bind_pure,
          $eId:term] <;> rfl)) (some hrun)
  let hcl ← withLocalDeclD `N σT fun N => do
    mkForallFVars #[N] (← mkAppM ``callsLt #[N, cb.beta #[N]])
  let hclPrf ← elabTermEnsuringType (← `(by
      intro N; rcases N with _ | m <;>
        simp [Freigen.callsLt, Freigen.Free.bind] <;> omega)) (some hcl)
  -- `recSoundApp` : ∀ N, mrec (fun s => denote (bodyCode s)) N ≈ ofFree (f N)   [mrec adequacy]
  let recSoundApp ← mkAppOptM ``recSound #[Op, SOp, ρTp, bodyCode, cb, fFn, hspecPrf, hrunPrf, hclPrf]
  -- `g` : the closed `Prog` — `rec_` (the reflected body) then `main(n) := call frec n`
  let g ← withLocalDeclD `Fp fTy fun Fp => withLocalDeclD `Vp vTy fun Vp => do
    let recBodyG := recBody.beta #[Vp]
    let frecTy := mkApp2 Fp σTpList ρTp
    let mainK ← withLocalDeclD `frec frecTy fun frec => do
      let mainLam ← withLocalDeclD `hargs (← mkAppM ``HList #[Vp, σTpList]) fun hargs => do
        let cont ← withLocalDeclD `r (mkApp Vp ρTp) fun r => do
          mkLambdaFVars #[r] (← mkAppOptM ``Code.ret #[Op, SOp, Fp, Vp, ρTp, r])
        mkLambdaFVars #[hargs]
          (← mkAppOptM ``Code.call #[Op, SOp, Fp, Vp, ρTp, σTpList, ρTp, frec, hargs, cont])
      mkLambdaFVars #[frec] (← mkAppOptM ``Prog.main #[Op, SOp, Fp, Vp, σTpList, ρTp, mainLam])
    mkLambdaFVars #[Fp, Vp]
      (← mkAppOptM ``Prog.rec_ #[Op, SOp, Fp, Vp, σTpList, ρTp, σTp, ρTp, recBodyG, mainK])
  let closedTy ← mkAppOptM ``Closed #[Op, SOp, σTpList, ρTp]
  let kc ← mkAppM ``KC #[Op]
  let ofFreeFn ← mkAppOptM ``ofFree #[Op, SOp, ρT]
  let nilD ← mkAppOptM ``HList.nil #[none, denoteV]
  let pred ← withLocalDeclD `g closedTy fun gv => do
    let body ← withLocalDeclD `N σT fun N => do
      let hlN ← mkAppOptM ``HList.cons #[none, denoteV, σTp, none, N, nilD]
      let lhs ← mkAppOptM ``denoteProg #[Op, SOp, σTpList, ρTp, mkAppN gv #[kc, denoteV], hlN]
      mkForallFVars #[N] (← mkAppM ``ITree.Eutt #[lhs, mkApp ofFreeFn (mkApp fFn N)])
    mkLambdaFVars #[gv] body
  -- proof: `denoteProg (g KC ⟨N⟩) = mrec (…) N` (bind right-identity), then `recSoundApp N`.
  let bodyFnC ← withLocalDeclD `s σT fun s => do
    mkLambdaFVars #[s] (← mkAppM ``denote #[bodyCode.beta #[s]])
  let proof ← withLocalDeclD `N σT fun N => do
    let hlN ← mkAppOptM ``HList.cons #[none, denoteV, σTp, none, N, nilD]
    let lhs ← mkAppOptM ``denoteProg #[Op, SOp, σTpList, ρTp, mkAppN g #[kc, denoteV], hlN]
    let rhs ← mkAppM ``mrec #[bodyFnC, N]
    let bridge ← elabTermEnsuringType (← `(by
        simp only [Freigen.denoteProg, Freigen.denote, Freigen.HList.head,
          Freigen.ITree.bind_ret_right])) (some (← mkEq lhs rhs))
    mkLambdaFVars #[N]
      (← mkAppM ``ITree.Eutt.trans #[← mkAppM ``ITree.Eutt.of_eq #[bridge], mkApp recSoundApp N])
  mkAppOptM ``Subtype.mk #[closedTy, pred, g, proof]

/-- **`reflect%`** — the unified entry point.  It does the right thing automatically:

* a `Free Op SOp α` **program value** → a `Prog` with a nullary `main`;
* a program `A₁ → … → Aₙ → Free Op SOp α` (of `Tp`-typed inputs) → a `Prog` whose `main` is a
  function of those inputs;
* a structural-recursive `def f : Nat → Free Op SOp ρ` → the `mrec` denotation.

Each returns a `{ · // · }` bundling the AST with its `≈`-soundness against the source. -/
elab "reflect% " t:term : term => do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  match_expr (← whnf (← inferType e)) with
  | Free _ _ _ => reflectMain e
  | _ =>
      match ← reflectStructuralNatRec e.getAppFn with
      | some (F, recTy) =>
          let some cName := e.getAppFn.constName?
            | throwError "reflect%: recursive source is not a definition"
          reflectRec F recTy cName
      | none => reflectMain e

/-! ## Demo: recursive `def`s through `reflect%` — automatic `mrec` denotation + `≈` soundness -/

/-- An empty first-order signature (pure recursion). -/
inductive NoOp : Type → Type → Type 1

/-- A tail-recursive `Free` function. -/
def countdown : Nat → Free NoOp NoScope Nat
  | 0     => .pure 0
  | n + 1 => countdown n

/-- `reflect%` reflects the recursive `def` into a **`Prog` with a `rec_` node** (self-calls are the
    `CallOp.call` op, tied by `mrec`) plus its soundness — the *same* `{ g : Closed // … denoteProg …
    ≈ ofFree … }` shape as the non-recursive arm, so recursion is first-class in `Prog`. -/
def countdownC := reflect% countdown

/-- `.1` is the closed `Prog` (a `rec_` + `main`). -/
example : Closed NoOp NoScope [.nat] .nat := countdownC.1
/-- `.2`: denoting the AST (`mrec` at the `rec_`) is `≈ ofFree` of the source, for every input. -/
example : ∀ N, denoteProg (countdownC.1 (KC NoOp) Tp.denote) (.cons N .nil)
    ≈ ofFree (countdown N) := countdownC.2

-- The recursion pretty-prints as a `rec` definition with a self-call, plus `main` calling it.
/-- info:
rec f0(x1 : Nat) =>
  let v2 := 0
  let v3 := x1 == v2
  if v3 then
    let v4 := 0
    v4
  else
    let v5 := 1
    let v6 := x1 - v5
    let v7 ← f0 (self-call)(v6)
    v7
def main(x8 : Nat) =>
  let v9 := f0(x8)
  v9
-/
#guard_msgs (whitespace := lax) in
  #eval IO.println (pp (fun o => nomatch o) (fun s => nomatch s) countdownC.1)

/-- **Non-tail** recursion (`sm n + 1`): the self-call sits under a `bind`.  `reflect%` handles
    it through the same path — `interp_bind` pushes the post-call `+1` through. -/
def sm : Nat → Free NoOp NoScope Nat
  | 0     => .pure 0
  | n + 1 => do let r ← sm n; pure (r + 1)

def smC := reflect% sm
example : ∀ N, denoteProg (smC.1 (KC NoOp) Tp.denote) (.cons N .nil) ≈ ofFree (sm N) := smC.2

end Freigen
