import Freigen.Scoped
import Freigen.ScopedReflect

/-!
# Recursion for the `FreeH` pipeline: `mrec` adequacy over `ofFreeH`

The general-recursion combinator `ITree.mrec` denotes a recursive `FreeH` function into `Comp Op`.
This file restates the `mrec` adequacy theorem over the `FreeH` source embedding `ofFreeH` (rather
than the old `Free`/`ofFree`), generic over the scoped signature `SOp` (a scoped block in a recursion
body is handled by `interp` being a monad morphism).  `mrec_adequacyH` is what a reflected recursion's
soundness reduces to: `∀ N, mrec body N ≈ ofFreeH (f N)`.
-/

namespace Freigen.Scoped

open Freigen.ITree

variable {Op : Type → Type → Type 1} {SOp : Type → Type} {ρ : Type}


/-- Run a call-body with the source `e` plugged in at each `call` (external `base` effects relabelled
    back to `Op`; a scoped block's own calls are plugged too). -/
def runSrcH (e : Nat → FreeH Op SOp ρ) :
    {γ : Type} → FreeH (CallOp Op Nat ρ) SOp γ → FreeH Op SOp γ
  | _, .pure a => .pure a
  | _, .op (.base o) i c => .op o i (fun x => runSrcH e (c x))
  | _, .op .call i c => FreeH.bind (e i) (fun v => runSrcH e (c v))
  | _, .hop s b c => .hop s (runSrcH e b) (fun x => runSrcH e (c x))

/-- Every `call` argument in the body is `< bound`. -/
def callsLtH (bound : Nat) : {γ : Type} → FreeH (CallOp Op Nat ρ) SOp γ → Prop
  | _, .pure _ => True
  | _, .op (.base _) _ c => ∀ x, callsLtH bound (c x)
  | _, .op .call i c => i < bound ∧ ∀ x, callsLtH bound (c x)
  | _, .hop _ b c => callsLtH bound b ∧ ∀ x, callsLtH bound (c x)

/-- **The adequacy step.** Interpreting a call-body is `≈` to running it with the source plugged in,
    given the source is adequate below `bound` and the body only calls below `bound`. -/
theorem adeqBodyH (body : Nat → Comp (CallOp Op Nat ρ) ρ) (e : Nat → FreeH Op SOp ρ)
    (bound : Nat) (Ho : ∀ k, k < bound → mrec body k ≈ ofFreeH (e k)) :
    ∀ {γ : Type} (t : FreeH (CallOp Op Nat ρ) SOp γ), callsLtH bound t →
      interp body (ofFreeH t) ≈ ofFreeH (runSrcH e t) := by
  intro γ t
  induction t with
  | pure a => intro _; simp only [ofFreeH, runSrcH, interp_ret]; exact eutt_refl _
  | op o i c ih =>
      cases o with
      | base o' =>
          intro h
          simp only [ofFreeH, runSrcH, interp_vis_base]
          exact eutt_vis_cong _ (fun x => ih x (h x))
      | call =>
          intro h
          simp only [ofFreeH, runSrcH, interp_vis_call, interp_bind, ofFreeH_bind]
          refine eutt_tau_left ?_
          exact eutt_bind_cong (Ho i h.1) (fun x => ih x (h.2 x))
  | hop s b c ihb ihc =>
      intro h
      simp only [ofFreeH, runSrcH, interp_bind]
      exact eutt_bind_cong (ihb h.1) (fun x => ihc x (h.2 x))

/-- **`mrec` adequacy (strong-induction shell)** over `ofFreeH`: the whole reflected recursion is `≈`
    its source, given each step is adequate using the adequacy of all smaller arguments. -/
theorem mrec_adequacyH (body : Nat → Comp (CallOp Op Nat ρ) ρ) (e : Nat → FreeH Op SOp ρ)
    (Hstep : ∀ N, (∀ k, k < N → mrec body k ≈ ofFreeH (e k)) → mrec body N ≈ ofFreeH (e N)) :
    ∀ N, mrec body N ≈ ofFreeH (e N) :=
  fun N => Nat.strongRecOn N Hstep

/-- `adeqBodyH` with the `runSrcH = e` bridge folded in — one step discharged against the source. -/
theorem adeqBodyH' (body : Nat → Comp (CallOp Op Nat ρ) ρ) (e : Nat → FreeH Op SOp ρ)
    (N : Nat) (t : FreeH (CallOp Op Nat ρ) SOp ρ)
    (IH : ∀ k, k < N → mrec body k ≈ ofFreeH (e k)) (hcl : callsLtH N t)
    (hrun : runSrcH e t = e N) :
    interp body (ofFreeH t) ≈ ofFreeH (e N) := by
  rw [← hrun]; exact adeqBodyH body e N IH t hcl

/-- **Generic recursion soundness** — what `reflect%` emits.  Given the reflected call-body
    `body` (a `Code` over the call-extended signature) and the source `f`, provided each call is
    below its argument (`hcl`) and running the body with `f` plugged in recovers `f` (`hrun`), the
    `mrec` denotation is `≈ ofFreeH ∘ f`.  Packages `denote_eq` + `mrec_adequacyH` + `adeqBodyH'`. -/
theorem recSound {ρT : Tp}
    (body : Nat → Code (CallOp Op Nat ρT.denote) SOp (KC (CallOp Op Nat ρT.denote)) Tp.denote ρT)
    (cb : Nat → FreeH (CallOp Op Nat ρT.denote) SOp ρT.denote) (f : Nat → FreeH Op SOp ρT.denote)
    (hspec : ∀ N, denote (body N) = ofFreeH (cb N))
    (hrun : ∀ N, runSrcH f (cb N) = f N)
    (hcl : ∀ N, callsLtH N (cb N)) :
    ∀ N, mrec (fun s => denote (body s)) N ≈ ofFreeH (f N) := by
  have hbody : (fun s => denote (body s)) = fun s => ofFreeH (cb s) := funext hspec
  intro N
  rw [hbody]
  refine mrec_adequacyH _ f ?_ N
  intro M IH
  exact adeqBodyH' _ _ _ _ IH (hcl M) (hrun M)

/-! ## The `reflect%` elaborator

`reflect% f` reflects a structural-recursive `def f : Nat → FreeH Op SOp ρ` into the recursion
denotation `fun N => mrec (…) N` and bundles its soundness `{ g // ∀ N, g N ≈ ofFreeH (f N) }`.  It
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
private partial def toCallBodyH (recId : FVarId) (Op SOp σT ρT : Expr) (t : Expr) : MetaM Expr := do
  let t := t.consumeMData.headBeta
  if let .letE _ _ v b _ := t then return ← toCallBodyH recId Op SOp σT ρT (b.instantiate1 v)
  let callOp := mkAppN (.const ``ITree.CallOp []) #[Op, σT, ρT]
  if t.getAppFn.isFVar && t.getAppFn.fvarId! == recId then
    let some arg := t.getAppArgs.back? | throwError "reflect%: self-call has no argument"
    let callC := mkAppN (.const ``ITree.CallOp.call []) #[Op, σT, ρT]
    let pureC ← mkAppOptM ``FreeH.pure #[callOp, SOp, ρT]
    return ← mkAppM ``FreeH.op #[callC, arg, pureC]
  let doBind (x f : Expr) : MetaM Expr := do
    let .forallE _ X _ _ := (← whnf (← inferType f)) | throwError "reflect%: bind cont not a function"
    let xC ← toCallBodyH recId Op SOp σT ρT x
    let fC ← withLocalDeclD `a X fun ha => do
      mkLambdaFVars #[ha] (← toCallBodyH recId Op SOp σT ρT (f.beta #[ha]))
    mkAppM ``FreeH.bind #[xC, fC]
  match_expr t with
  | FreeH.pure _ _ _ r => mkAppOptM ``FreeH.pure #[callOp, SOp, none, r]
  | Pure.pure _ _ _ r => mkAppOptM ``FreeH.pure #[callOp, SOp, none, r]
  | Bind.bind _ _ _ _ x f => doBind x f
  | FreeH.bind _ _ _ _ x f => doBind x f
  | cond _ c m1 m2 => do
      let a ← toCallBodyH recId Op SOp σT ρT m1
      let b ← toCallBodyH recId Op SOp σT ρT m2
      mkAppM ``cond #[c, a, b]
  | FreeH.op _ _ _ I R o i k => do
      let baseO := mkAppN (.const ``ITree.CallOp.base []) #[Op, σT, ρT, I, R, o]
      let kC ← withLocalDeclD `x R fun hx => do
        mkLambdaFVars #[hx] (← toCallBodyH recId Op SOp σT ρT (k.beta #[hx]))
      mkAppM ``FreeH.op #[baseO, i, kC]
  | FreeH.hop _ _ _ β s b k => do
      let bC ← toCallBodyH recId Op SOp σT ρT b
      let kC ← withLocalDeclD `x β fun hx => do
        mkLambdaFVars #[hx] (← toCallBodyH recId Op SOp σT ρT (k.beta #[hx]))
      mkAppM ``FreeH.hop #[s, bC, kC]
  | _ =>
      match ← unfoldDefinition? t with
      | some t' => toCallBodyH recId Op SOp σT ρT t'
      | none    => throwError "reflect%: cannot reflect recursion body{indentExpr t}"

/-- Reflect a structural-recursive `def f : Nat → FreeH Op SOp ρ` into `{ g // ∀ N, g N ≈ ofFreeH
    (f N) }` — the `mrec` denotation and its soundness.  The recursive arm of `reflect%`. -/
def reflectRec (F recTy : Expr) (cName : Name) : TermElabM Expr := do
  let .forallE _ σT codom _ := (← whnf recTy) | throwError "reflect%: recursion must be `Nat → _`"
  let_expr FreeH Op SOp ρT := (← whnf codom)
    | throwError "reflect%: recursion result must be `FreeH Op SOp _`"
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
  -- `cb` : the FreeH call-body `fun s => …`
  let cb ← withLocalDeclD `s σT fun s => do
    let cbT ← withLocalDeclD `rec recTy fun rec =>
      toCallBodyH rec.fvarId! Op SOp σT ρT ((F.beta #[rec]).beta #[s])
    mkLambdaFVars #[s] cbT
  -- `recBody` : the `rec_` body `fun V0 F' argAtom => …`, parametric in the value/function reps
  let recBody ← withLocalDeclD `V0 vTy fun Vp0 => withLocalDeclD `F' fTy fun F' =>
    withLocalDeclD `arg (mkApp Vp0 σTp) fun argAtom => do
      let codeT ← withLocalDeclD `s σT fun s => withLocalDeclD `rec recTy fun rec => do
        let cbT ← toCallBodyH rec.fvarId! Op SOp σT ρT ((F.beta #[rec]).beta #[s])
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
      (← mkAppM ``ofFreeH #[cb.beta #[N]]))
  let hspecPrf ← elabTermEnsuringType (← `(by
      intro N; simp only [Freigen.Scoped.denote, Freigen.Scoped.ofFreeH,
        Freigen.Scoped.ofFreeH_bind, Freigen.Scoped.ofFreeH_cond, Freigen.Scoped.Bin.denote,
        Freigen.Scoped.Un.denote, Freigen.ITree.bind_vis, Freigen.ITree.bind_ret,
        Freigen.ITree.bind_assoc])) (some hspec)
  let hrun ← withLocalDeclD `N σT fun N => do
    mkForallFVars #[N] (← mkEq (← mkAppM ``runSrcH #[fFn, cb.beta #[N]]) (mkApp fFn N))
  let hrunPrf ← elabTermEnsuringType (← `(by
      intro N; rcases N with _ | m <;>
        simp [Freigen.Scoped.runSrcH, Freigen.Scoped.FreeH.bind, Freigen.Scoped.FreeH.bind_pure,
          $eId:term] <;> rfl)) (some hrun)
  let hcl ← withLocalDeclD `N σT fun N => do
    mkForallFVars #[N] (← mkAppM ``callsLtH #[N, cb.beta #[N]])
  let hclPrf ← elabTermEnsuringType (← `(by
      intro N; rcases N with _ | m <;>
        simp [Freigen.Scoped.callsLtH, Freigen.Scoped.FreeH.bind] <;> omega)) (some hcl)
  -- `recSoundApp` : ∀ N, mrec (fun s => denote (bodyCode s)) N ≈ ofFreeH (f N)   [mrec adequacy]
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
  let ofFreeHead ← mkAppOptM ``ofFreeH #[Op, SOp, ρT]
  let nilD ← mkAppOptM ``HList.nil #[none, denoteV]
  let pred ← withLocalDeclD `g closedTy fun gv => do
    let body ← withLocalDeclD `N σT fun N => do
      let hlN ← mkAppOptM ``HList.cons #[none, denoteV, σTp, none, N, nilD]
      let lhs ← mkAppOptM ``denoteProg #[Op, SOp, σTpList, ρTp, mkAppN gv #[kc, denoteV], hlN]
      mkForallFVars #[N] (← mkAppM ``ITree.Eutt #[lhs, mkApp ofFreeHead (mkApp fFn N)])
    mkLambdaFVars #[gv] body
  -- proof: `denoteProg (g KC ⟨N⟩) = mrec (…) N` (bind right-identity), then `recSoundApp N`.
  let bodyFnC ← withLocalDeclD `s σT fun s => do
    mkLambdaFVars #[s] (← mkAppM ``denote #[bodyCode.beta #[s]])
  let proof ← withLocalDeclD `N σT fun N => do
    let hlN ← mkAppOptM ``HList.cons #[none, denoteV, σTp, none, N, nilD]
    let lhs ← mkAppOptM ``denoteProg #[Op, SOp, σTpList, ρTp, mkAppN g #[kc, denoteV], hlN]
    let rhs ← mkAppM ``mrec #[bodyFnC, N]
    let bridge ← elabTermEnsuringType (← `(by
        simp only [Freigen.Scoped.denoteProg, Freigen.Scoped.denote, Freigen.Scoped.HList.head,
          Freigen.ITree.bind_ret_right])) (some (← mkEq lhs rhs))
    mkLambdaFVars #[N]
      (← mkAppM ``ITree.Eutt.trans #[← mkAppM ``ITree.Eutt.of_eq #[bridge], mkApp recSoundApp N])
  mkAppOptM ``Subtype.mk #[closedTy, pred, g, proof]

/-- **`reflect%`** — the unified entry point.  It does the right thing automatically:

* a `FreeH Op SOp α` **program value** → a `Prog` with a nullary `main`;
* a program `A₁ → … → Aₙ → FreeH Op SOp α` (of `Tp`-typed inputs) → a `Prog` whose `main` is a
  function of those inputs;
* a structural-recursive `def f : Nat → FreeH Op SOp ρ` → the `mrec` denotation.

Each returns a `{ · // · }` bundling the AST with its `≈`-soundness against the source. -/
elab "reflect% " t:term : term => do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  match_expr (← whnf (← inferType e)) with
  | FreeH _ _ _ => reflectMain e
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

/-- A tail-recursive `FreeH` function. -/
def countdown : Nat → FreeH NoOp NoScope Nat
  | 0     => .pure 0
  | n + 1 => countdown n

/-- `reflect%` reflects the recursive `def` into a **`Prog` with a `rec_` node** (self-calls are the
    `CallOp.call` op, tied by `mrec`) plus its soundness — the *same* `{ g : Closed // … denoteProg …
    ≈ ofFreeH … }` shape as the non-recursive arm, so recursion is first-class in `Prog`. -/
def countdownC := reflect% countdown

/-- `.1` is the closed `Prog` (a `rec_` + `main`). -/
example : Closed NoOp NoScope [.nat] .nat := countdownC.1
/-- `.2`: denoting the AST (`mrec` at the `rec_`) is `≈ ofFreeH` of the source, for every input. -/
example : ∀ N, denoteProg (countdownC.1 (KC NoOp) Tp.denote) (.cons N .nil)
    ≈ ofFreeH (countdown N) := countdownC.2

-- Pretty-prints as `rec f0(x1 : Nat) => …` (with a self-call) and `def main(x) => f0(x)`.
#eval pp (fun o => nomatch o) (fun s => nomatch s) countdownC.1

/-- **Non-tail** recursion (`sm n + 1`): the self-call sits under a `bind`.  `reflect%` handles
    it through the same path — `interp_bind` pushes the post-call `+1` through. -/
def sm : Nat → FreeH NoOp NoScope Nat
  | 0     => .pure 0
  | n + 1 => do let r ← sm n; pure (r + 1)

def smC := reflect% sm
example : ∀ N, denoteProg (smC.1 (KC NoOp) Tp.denote) (.cons N .nil) ≈ ofFreeH (sm N) := smC.2

end Freigen.Scoped
