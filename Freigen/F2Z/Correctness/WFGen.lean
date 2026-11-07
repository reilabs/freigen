import Freigen.F2Z.Gadgets
import Lean.Meta.Sym.Pattern
import Lean.Meta.Sym.Simp.DiscrTree

namespace Freigen.F2Z.WF

open Lean Meta Elab Tactic

/-!
`wfgen'` is a deliberately incomplete, theorem-driven relational VC generator.

Unlike `wfgen`, it never tries a bag of unrelated lemmas and never invokes a
general-purpose solver.  A step is one of:

* a fixed logical decomposition (`∀`, `→`, `∧`, wrappers such as `GadgetSpec`),
* a rule indexed by the actual circuit-operation head,
* reflexivity or a local assumption,
* application of the unique theorem whose full conclusion matches the goal.

If none applies, the goal is returned to the user as a numbered VC.  Non-Prop
arguments introduced by rules are returned first as numbered invariant holes;
dependent symbolic execution pauses until those holes have been filled.
-/

/-- The generic loop rule used by `wfgen'`.  The invariant is an explicit
argument, so applying this theorem produces a user-visible invariant goal
instead of asking the tactic to synthesize a relation from the accumulator. -/
theorem Rel.forIn'_range_map_yield_bind_rule
    {leftCtx rightCtx : Context}
    (I : Post leftCtx rightCtx βL βR)
    {Q : Post leftCtx rightCtx γL γR}
    {P : Assumption leftCtx rightCtx} {xs : Std.Legacy.Range}
    {initL : βL} {initR : βR}
    {fL : (a : Nat) → a ∈ xs → βL → @Circuit leftCtx δL}
    {fR : (a : Nat) → a ∈ xs → βR → @Circuit rightCtx δR}
    {nextL : (a : Nat) → a ∈ xs → βL → δL → βL}
    {nextR : (a : Nat) → a ∈ xs → βR → δR → βR}
    {kL : βL → @Circuit leftCtx γL}
    {kR : βR → @Circuit rightCtx γR}
    (hinit : ∀ leftVal rightVal, P leftVal rightVal →
      I leftVal rightVal initL initR)
    (hstep : ∀ a h, RelHom
      (fun leftVal rightVal left right =>
        P leftVal rightVal ∧ I leftVal rightVal left right)
      (fun leftVal rightVal left right =>
        P leftVal rightVal ∧ I leftVal rightVal left right)
      (fun b => do
        let x ← fL a h b
        Pure.pure (nextL a h b x))
      (fun b => do
        let x ← fR a h b
        Pure.pure (nextR a h b x)))
    (hcont : ∀ (A : Assumption leftCtx rightCtx) left right,
      (∀ leftVal rightVal, A leftVal rightVal →
        P leftVal rightVal ∧ I leftVal rightVal left right) →
      Rel Q A (kL left) (kR right)) :
    Rel Q P
      ((forIn' xs initL fun a h b => do
        let x ← fL a h b
        Pure.pure (ForInStep.yield (nextL a h b x))) >>= kL)
      ((forIn' xs initR fun a h b => do
        let x ← fR a h b
        Pure.pure (ForInStep.yield (nextR a h b x))) >>= kR) :=
  Rel.forIn'_range_map_yield_bind
    (R := fun leftVal rightVal left right =>
      P leftVal rightVal ∧ I leftVal rightVal left right)
    (fun leftVal rightVal hP => ⟨hP, hinit leftVal rightVal hP⟩)
    hstep hcont

/-- Generic range-loop rule when the loop itself is the whole computation. -/
theorem Rel.forIn'_range_map_yield_rule
    {leftCtx rightCtx : Context}
    (I : Post leftCtx rightCtx βL βR)
    {Q : Post leftCtx rightCtx βL βR}
    {P : Assumption leftCtx rightCtx} {xs : Std.Legacy.Range}
    {initL : βL} {initR : βR}
    {fL : (a : Nat) → a ∈ xs → βL → @Circuit leftCtx δL}
    {fR : (a : Nat) → a ∈ xs → βR → @Circuit rightCtx δR}
    {nextL : (a : Nat) → a ∈ xs → βL → δL → βL}
    {nextR : (a : Nat) → a ∈ xs → βR → δR → βR}
    (hinit : ∀ leftVal rightVal, P leftVal rightVal →
      I leftVal rightVal initL initR)
    (hstep : ∀ a h, RelHom
      (fun leftVal rightVal left right =>
        P leftVal rightVal ∧ I leftVal rightVal left right)
      (fun leftVal rightVal left right =>
        P leftVal rightVal ∧ I leftVal rightVal left right)
      (fun b => do
        let x ← fL a h b
        Pure.pure (nextL a h b x))
      (fun b => do
        let x ← fR a h b
        Pure.pure (nextR a h b x)))
    (hpost : ∀ leftVal rightVal left right,
      P leftVal rightVal ∧ I leftVal rightVal left right →
      Q leftVal rightVal left right) :
    Rel Q P
      (forIn' xs initL fun a h b => do
        let x ← fL a h b
        Pure.pure (ForInStep.yield (nextL a h b x)))
      (forIn' xs initR fun a h b => do
        let x ← fR a h b
        Pure.pure (ForInStep.yield (nextR a h b x))) := by
  apply Rel.mono
    (Rel.forIn'_range_map_yield
      (R := fun leftVal rightVal left right =>
        P leftVal rightVal ∧ I leftVal rightVal left right)
      (fun leftVal rightVal hP => ⟨hP, hinit leftVal rightVal hP⟩)
      hstep)
  exact hpost

/-- A named range fold keeps concrete loop bounds opaque in downstream proof
terms.  This matters for large fixed loops: normalizing the elaborated `for`
expression while serializing a theorem can otherwise allocate a term linear
in the bound. -/
def foldRange [ctx : Context] (xs : Std.Legacy.Range) (init : β)
    (step : (a : Nat) → a ∈ xs → β → @Circuit ctx β) : @Circuit ctx β :=
  forIn' xs init fun a h state => do
    let next ← step a h state
    pure (ForInStep.yield next)

theorem Rel.foldRange_rule
    {leftCtx rightCtx : Context}
    {I : Post leftCtx rightCtx βL βR}
    {P : Assumption leftCtx rightCtx} {xs : Std.Legacy.Range}
    {initL : βL} {initR : βR}
    {stepL : (a : Nat) → a ∈ xs → βL → @Circuit leftCtx βL}
    {stepR : (a : Nat) → a ∈ xs → βR → @Circuit rightCtx βR}
    (hinit : ∀ leftVal rightVal, P leftVal rightVal →
      I leftVal rightVal initL initR)
    (hstep : ∀ a h, RelHom I I (stepL a h) (stepR a h)) :
    Rel I P (@foldRange _ leftCtx xs initL stepL)
      (@foldRange _ rightCtx xs initR stepR) := by
  unfold foldRange
  exact Rel.forIn'_range_yield hinit hstep

/-- A first-order matching surface for the vector-building loop generated by
`for` + `f2z` + `Vector.set!`.

The more abstract `forIn'_range_map_yield_bind_rule` is useful when applying a
theorem by hand, but its program arguments require higher-order matching (the
matcher would have to invent `fL` and `nextL` by abstracting subterms).  This
rule deliberately fixes only the *syntax of the operation*.  Its semantic
invariant `I`, initial-state proof, step proof, and continuation proof remain
explicit obligations. -/
theorem Rel.forIn'_range_f2z_set!_bind_rule
    {leftCtx rightCtx : Context}
    (I : Post leftCtx rightCtx
      (Vector leftCtx.Wℤ n) (Vector rightCtx.Wℤ n))
    {Q : Post leftCtx rightCtx γL γR}
    {P : Assumption leftCtx rightCtx} {xs : Std.Legacy.Range}
    {initL : Vector leftCtx.Wℤ n} {initR : Vector rightCtx.Wℤ n}
    {inputL : (a : Nat) → a ∈ xs → leftCtx.WBool}
    {inputR : (a : Nat) → a ∈ xs → rightCtx.WBool}
    {kL : Vector leftCtx.Wℤ n → @Circuit leftCtx γL}
    {kR : Vector rightCtx.Wℤ n → @Circuit rightCtx γR}
    (hinit : ∀ leftVal rightVal, P leftVal rightVal →
      I leftVal rightVal initL initR)
    (hstep : ∀ a h, RelHom
      (fun leftVal rightVal left right =>
        P leftVal rightVal ∧ I leftVal rightVal left right)
      (fun leftVal rightVal left right =>
        P leftVal rightVal ∧ I leftVal rightVal left right)
      (fun acc => do
        let value ← F2Z.f2z (ctx := leftCtx) (inputL a h)
        Pure.pure (acc.set! a value))
      (fun acc => do
        let value ← F2Z.f2z (ctx := rightCtx) (inputR a h)
        Pure.pure (acc.set! a value)))
    (hcont : ∀ (A : Assumption leftCtx rightCtx) left right,
      (∀ leftVal rightVal, A leftVal rightVal →
        P leftVal rightVal ∧ I leftVal rightVal left right) →
      Rel Q A (kL left) (kR right)) :
    Rel Q P
      ((forIn' xs initL fun a h acc => do
        let value ← F2Z.f2z (ctx := leftCtx) (inputL a h)
        Pure.pure (ForInStep.yield (acc.set! a value))) >>= kL)
      ((forIn' xs initR fun a h acc => do
        let value ← F2Z.f2z (ctx := rightCtx) (inputR a h)
        Pure.pure (ForInStep.yield (acc.set! a value))) >>= kR) :=
  Rel.forIn'_range_map_yield_bind
    (R := fun leftVal rightVal left right =>
      P leftVal rightVal ∧ I leftVal rightVal left right)
    (fun leftVal rightVal hP => ⟨hP, hinit leftVal rightVal hP⟩)
    hstep hcont

/-- Congruence for the derived integer value of the new `U` representation.
This is a semantic rule, rather than an instruction for the tactic to unfold
the concrete representation's evaluation function. -/
theorem LCEq.uIntVal
    {leftCtx rightCtx : Context}
    {leftVal : @Valuation leftCtx} {rightVal : @Valuation rightCtx}
    {left : @U leftCtx n} {right : @U rightCtx n}
    (h : ∀ i : Fin n,
      LCEq leftVal.int rightVal.int
        (@U.intBits leftCtx n left)[i]
        (@U.intBits rightCtx n right)[i]) :
    LCEq leftVal.int rightVal.int
      (@U.intVal leftCtx n left) (@U.intVal rightCtx n right) := by
  unfold U.intVal
  exact eval_sum fun i => eval_nsmul _ (h i)

/-- Use a gadget contract at the head of a bind, preserving the caller's
ambient assumptions and continuing from the gadget's postcondition. -/
theorem GadgetSpec.bind_rule
    {Input Output : Context → Type} {P Q}
    {gadget : ∀ {ctx}, Input ctx → @Circuit ctx (Output ctx)}
    (spec : GadgetSpec P gadget Q)
    {leftCtx rightCtx : Context} {γL γR : Type}
    {R : Post leftCtx rightCtx γL γR}
    {A : Assumption leftCtx rightCtx}
    {left : Input leftCtx} {right : Input rightCtx}
    {kL : Output leftCtx → @Circuit leftCtx γL}
    {kR : Output rightCtx → @Circuit rightCtx γR}
    (hinput : ∀ leftVal rightVal, A leftVal rightVal →
      P leftVal rightVal left right)
    (hcont : ∀ (B : Assumption leftCtx rightCtx) outL outR,
      (∀ leftVal rightVal, B leftVal rightVal →
        A leftVal rightVal ∧ Q leftVal rightVal outL outR) →
      Rel R B (kL outL) (kR outR)) :
    Rel R A (@gadget leftCtx left >>= kL)
      (@gadget rightCtx right >>= kR) :=
  ((spec.relHom leftCtx rightCtx) A left right hinput).bind kL kR hcont

/-- A bind rule with the continuation evaluated under the precise framed
postcondition.  This avoids accumulating a chain of abstract assumptions and
implications in straight-line circuits. -/
theorem GadgetSpec.bind_rule_direct
    {Input Output : Context → Type} {P Q}
    {gadget : ∀ {ctx}, Input ctx → @Circuit ctx (Output ctx)}
    (spec : GadgetSpec P gadget Q)
    {leftCtx rightCtx : Context} {γL γR : Type}
    {R : Post leftCtx rightCtx γL γR}
    {A : Assumption leftCtx rightCtx}
    {left : Input leftCtx} {right : Input rightCtx}
    {kL : Output leftCtx → @Circuit leftCtx γL}
    {kR : Output rightCtx → @Circuit rightCtx γR}
    (hinput : ∀ leftVal rightVal, A leftVal rightVal →
      P leftVal rightVal left right)
    (hcont : ∀ outL outR,
      Rel R (fun leftVal rightVal =>
        A leftVal rightVal ∧ Q leftVal rightVal outL outR)
        (kL outL) (kR outR)) :
    Rel R A (@gadget leftCtx left >>= kL)
      (@gadget rightCtx right >>= kR) := by
  apply ((spec.relHom leftCtx rightCtx) A left right hinput).bind kL kR
  intro S outL outR hS
  exact ((hcont outL outR).frame hS).mono fun _ _ _ _ h => h.2

/-- Use a gadget contract when the gadget is the entire remaining program,
while allowing the caller to carry a stronger ambient assumption. -/
theorem GadgetSpec.direct_rule
    {Input Output : Context → Type}
    {P : ∀ {leftCtx rightCtx},
      @Valuation leftCtx → @Valuation rightCtx →
      Input leftCtx → Input rightCtx → Prop}
    {Q : ∀ {leftCtx rightCtx},
      @Valuation leftCtx → @Valuation rightCtx →
      Output leftCtx → Output rightCtx → Prop}
    {gadget : ∀ {ctx}, Input ctx → @Circuit ctx (Output ctx)}
    (spec : GadgetSpec P gadget Q)
    {leftCtx rightCtx : Context}
    {A : Assumption leftCtx rightCtx}
    {left : Input leftCtx} {right : Input rightCtx}
    (hinput : ∀ leftVal rightVal, A leftVal rightVal →
      P leftVal rightVal left right) :
    Rel (Q (leftCtx := leftCtx) (rightCtx := rightCtx)) A
      (@gadget leftCtx left) (@gadget rightCtx right) :=
  ((spec leftCtx rightCtx left right).frame hinput).mono fun _ _ _ _ h => h.2

namespace WFGen

private def builtinRules : Array Name := #[
  ``HintRel.of_eq,
  ``HintRel.of_argsEq,
  ``eval_add,
  ``eval_sub,
  ``eval_smul,
  ``eval_nsmul,
  ``eval_sum,
  ``eval_reverse,
  ``lceq_getElem_of_mem_range,
  ``LCEq.uIntVal]

private partial def programOp (program : Expr) : Expr :=
  let program := program.consumeMData
  let fn := program.getAppFn
  let args := program.getAppRevArgs
  if fn.isLambda && !args.isEmpty then
    programOp (fn.betaRev args)
  else match program with
    | .lam _ _ body _ => programOp body
    | .letE _ _ value body _ => programOp (body.instantiate1 value)
    | _ =>
      if program.getAppFn.constName? == some ``Bind.bind then
        let args := program.getAppArgs
        if args.size ≥ 2 then programOp args[args.size - 2]! else program
      else
        program

private def relProgramHead? (target : Expr) : Option Name := do
  guard <| target.consumeMData.getAppFn.constName? == some ``Rel
  let args := target.consumeMData.getAppArgs
  guard <| args.size ≥ 2
  (programOp args[args.size - 2]!).consumeMData.getAppFn.constName?

/-- `Rel` rules are indexed by the constructor at the head of the left-hand
program.  This is the same important distinction made by `mvcgen`: the
operation head chooses a rule; theorem application merely checks that choice.
They are intentionally not mixed into the proposition-wide discrimination
tree below. -/
private def relRulesFor? (target : Expr) : Option (Array Name) := do
  match relProgramHead? target with
  | some ``Pure.pure => some #[``Rel.pure]
  | some ``F2Z.assertR1C => some #[``Rel.assertR1C]
  | some ``F2Z.f2z => some #[``Rel.f2z]
  | some ``F2Z.hint => some #[``Rel.hint]
  | some ``ForIn'.forIn' => some #[
      ``Rel.forIn'_range_f2z_set!_bind_rule,
      ``Rel.forIn'_range_map_yield_bind_rule,
      ``Rel.forIn'_range_map_yield_rule]
  | _ => none

/-- Relational Kleisli rules are likewise selected from the actual operation
at the head of the function body. -/
private def relHomRuleFor? (target : Expr) : Option Name := do
  guard <| target.consumeMData.getAppFn.constName? == some ``RelHom
  let args := target.consumeMData.getAppArgs
  guard <| args.size ≥ 2
  let left := args[args.size - 2]!
  let op := programOp left
  match op.consumeMData.getAppFn.constName? with
  | some ``F2Z.f2z =>
      if left.getUsedConstants.contains ``Vector.set! then
        some ``RelHom.f2z_set!
      else
        some ``RelHom.f2z
  | _ => none

/-- Congruence rules whose useful head is below the `LCEq` wrapper. -/
private def lcRuleFor? (target : Expr) : Option Name := do
  guard <| target.consumeMData.getAppFn.constName? == some ``LCEq
  let args := target.consumeMData.getAppArgs
  guard <| args.size ≥ 2
  let left := args[args.size - 2]!
  match left.consumeMData.getAppFn.constName? with
  | some ``U.intVal => some ``LCEq.uIntVal
  | some ``HSub.hSub => some ``eval_sub
  | _ => none

/-- Some congruence theorems state their premises as raw evaluation
equalities rather than through `LCEq`. Preserve semantic heads in those
premises too instead of delta-reducing them into large sums. -/
private def evalEqRuleFor? (target : Expr) : Option Name := do
  guard <| target.consumeMData.getAppFn.constName? == some ``Eq
  let eqArgs := target.consumeMData.getAppArgs
  guard <| eqArgs.size ≥ 2
  let left := eqArgs[eqArgs.size - 2]!
  guard <| left.consumeMData.getAppFn.constName? == some ``LC.eval
  let evalArgs := left.consumeMData.getAppArgs
  guard <| !evalArgs.isEmpty
  let value := evalArgs[evalArgs.size - 1]!
  match value.consumeMData.getAppFn.constName? with
  | some ``U.intVal => some ``LCEq.uIntVal
  | _ => none

structure Rule where
  declName : Name
  pattern : Sym.Pattern
deriving Inhabited

instance : BEq Rule where
  beq left right := left.declName == right.declName

structure RuleDB where
  tree : DiscrTree Rule := .empty
  gadgets : Std.HashMap Name (Array Name) := {}

private def RuleDB.insert (db : RuleDB) (rule : Rule) : RuleDB :=
  { tree := Sym.insertPattern db.tree rule.pattern rule }

private def RuleDB.insertGadget (db : RuleDB) (gadget rule : Name) : RuleDB :=
  let rules := db.gadgets[gadget]?.getD #[]
  { db with gadgets := db.gadgets.insert gadget (rules.push rule) }

structure RuleCacheState where
  patterns : Std.HashMap Name Sym.Pattern := {}
  builtinDB? : Option RuleDB := none
deriving Inhabited

/-- Pattern construction walks theorem types and builds proof/instance metadata.
Keep that work local to an environment, but share it between every `wfgen'`
invocation in that environment. -/
initialize ruleCacheExt : EnvExtension RuleCacheState ←
  registerEnvExtension (pure {}) (asyncMode := .local)

private def getRulePattern (declName : Name) : MetaM Sym.Pattern := do
  if let some pattern := (ruleCacheExt.getState (← getEnv)).patterns[declName]? then
    return pattern
  let pattern ← Sym.mkPatternFromDecl declName
  modifyEnv fun env => ruleCacheExt.modifyState env fun cache =>
    { cache with patterns := cache.patterns.insert declName pattern }
  return pattern

private def getBuiltinRuleDB : MetaM RuleDB := do
  if let some db := (ruleCacheExt.getState (← getEnv)).builtinDB? then
    return db
  let mut db : RuleDB := { tree := .empty }
  for declName in builtinRules do
    let pattern ← getRulePattern declName
    db := db.insert { declName, pattern }
  modifyEnv fun env => ruleCacheExt.modifyState env fun cache =>
    { cache with builtinDB? := some db }
  return db

private partial def instantiateSyntacticForalls
    (proof type : Expr) : MetaM (Expr × Expr) := do
  match type.consumeMData with
  | .forallE _ domain body _ =>
      let arg ← mkFreshExprMVar domain
      instantiateSyntacticForalls (mkApp proof arg) (body.instantiate1 arg)
  | _ => return (proof, type)

/-- If a supplied theorem concludes in `GadgetSpec _ gadget _`, recover the
head of `gadget`.  Such theorems are indexed separately from ordinary logical
rules: they apply to a `Rel` whose *program* starts with that gadget, not to a
goal whose proposition head is `GadgetSpec`. -/
private def gadgetHeadOfRule? (declName : Name) : MetaM (Option Name) := do
  let rule ← mkConstWithFreshMVarLevels declName
  let (_, conclusion) ← instantiateSyntacticForalls rule (← inferType rule)
  let conclusion := conclusion.consumeMData
  unless conclusion.getAppFn.constName? == some ``GadgetSpec do
    return none
  let args := conclusion.getAppArgs
  unless args.size ≥ 2 do return none
  let gadget := args[args.size - 2]!
  return (programOp gadget).consumeMData.getAppFn.constName?

private def buildRuleDB (extraRules : Array Name) : MetaM RuleDB := do
  let mut db ← getBuiltinRuleDB
  for declName in extraRules do
    unless builtinRules.contains declName do
      if let some gadget ← gadgetHeadOfRule? declName then
        db := db.insertGadget gadget declName
      else
        let pattern ← getRulePattern declName
        db := db.insert { declName, pattern }
  return db

private inductive SolveResult where
  | progressed (goals : List MVarId)
  | stuck

private def transparentWrapper? (target : Expr) : Option Name :=
  match target.consumeMData.getAppFn.constName? with
  | some name =>
      if name == ``GadgetSpec || name == ``RelHom ||
          name == ``VectorRel then
        some name
      else
        none
  | none => none

private def tryRflOrAssumption (goal : MVarId) : MetaM Bool := do
  if ← goal.assumptionCore then return true
  if let some _ ← observing? goal.refl then return true
  return false

/-- Turn the purely logical content of a local hypothesis into applicable
rules.  Quantifiers are retained, while conjunctions additionally expose
their projections.  This lets a gadget continuation consume one component of
the preceding gadget's postcondition without invoking a general proof search
or expanding that component definitionally. -/
private partial def localLogicalRules (targetHead : Option Name)
    (proof type : Expr) : MetaM (Array Expr) := do
  let type ← whnfCore type
  if !type.consumeMData.isForall &&
      type.consumeMData.getAppFn.constName? == targetHead then
    return #[proof]
  let type ← whnf type
  match type.consumeMData with
  | .forallE name domain body binderInfo =>
      withLocalDecl name binderInfo domain fun arg => do
        let rules ← localLogicalRules targetHead
          (mkApp proof arg) (body.instantiate1 arg)
        rules.mapM fun rule => mkLambdaFVars #[arg] rule
  | .app (.app (.const ``And _) left) right =>
      let leftProof := mkApp3 (mkConst ``And.left) left right proof
      let rightProof := mkApp3 (mkConst ``And.right) left right proof
      return #[proof] ++
        (← localLogicalRules targetHead leftProof left) ++
        (← localLogicalRules targetHead rightProof right)
  | _ => return #[proof]

private partial def conclusionHead? (type : Expr) : Option Name :=
  match type.consumeMData with
  | .forallE _ _ body _ => conclusionHead? body
  | type => type.getAppFn.constName?

private abbrev LocalRuleCache :=
  IO.Ref (Std.HashMap (FVarId × Name) (Array Expr))

private def tryLocalLogic (cache : LocalRuleCache)
    (goal : MVarId) : MetaM (Option (List MVarId)) := do
  let targetHead := conclusionHead? (← goal.getType)
  let cacheHead := targetHead.getD .anonymous
  -- Continuations add their strongest framed hypothesis last.  Searching
  -- newest-first usually finds the needed component immediately and avoids
  -- repeatedly traversing all weaker prefixes of a long bind chain.
  let lctx ← getLCtx
  for fvarId in lctx.getFVarIds.reverse do
    let localDecl := lctx.get! fvarId
    unless ← isProp localDecl.type do continue
    if let some head := conclusionHead? localDecl.type then
      if head == ``GadgetSpec || head == ``Rel || head == ``RelHom then
        continue
    let cacheKey := (localDecl.fvarId, cacheHead)
    let rules ← match (← cache.get)[cacheKey]? with
      | some rules => pure rules
      | none =>
          let rules ← localLogicalRules targetHead localDecl.toExpr localDecl.type
          cache.modify fun entries => entries.insert cacheKey rules
          pure rules
    let matching ← rules.filterM fun rule =>
      return conclusionHead? (← inferType rule) == targetHead
    let ordered := matching ++ rules.filter fun rule => !matching.contains rule
    for rule in ordered do
      if let some goals ← observing? do
        goal.apply rule { newGoals := .all, synthAssignedInstances := true }
      then
        return some goals
  return none

private def tryApplyRule (goal : MVarId) (rule : Rule) : MetaM (Option (List MVarId)) := do
  let proof ← mkConstWithFreshMVarLevels rule.declName
  observing? do
    goal.apply proof { newGoals := .all, synthAssignedInstances := true }

private def tryRules (goal : MVarId) (rules : Array Name) : MetaM (Option (List MVarId)) := do
  for declName in rules do
    let pattern ← getRulePattern declName
    if let some goals ← tryApplyRule goal { declName, pattern } then
      return some goals
  return none

private def instantiateRule (declName : Name) : MetaM Expr := do
  let rule ← mkConstWithFreshMVarLevels declName
  return (← instantiateSyntacticForalls rule (← inferType rule)).1

private partial def reduceProgramWrappers (program : Expr) : Expr :=
  let program := program.consumeMData
  let fn := program.getAppFn
  let args := program.getAppRevArgs
  if fn.isLambda && !args.isEmpty then
    reduceProgramWrappers (fn.betaRev args)
  else match program with
    | .letE _ _ value body _ => reduceProgramWrappers (body.instantiate1 value)
    | _ => program

private def bindParts? (program : Expr) : MetaM (Option (Expr × Expr)) := do
  let program := reduceProgramWrappers program
  unless program.consumeMData.getAppFn.constName? == some ``Bind.bind do
    return none
  let args := program.consumeMData.getAppArgs
  unless args.size ≥ 2 do return none
  return some (args[args.size - 2]!, args[args.size - 1]!)

private partial def prodLeafCount (type : Expr) : MetaM Nat := do
  let type ← whnfCore type
  if type.consumeMData.getAppFn.constName? == some ``Prod then
    let args := type.consumeMData.getAppArgs
    unless args.size == 2 do throwError "malformed product input type"
    return (← prodLeafCount args[0]!) + (← prodLeafCount args[1]!)
  return 1

private partial def packProdInput (type : Expr) (values : Array Expr)
    (index : Nat := 0) : MetaM (Expr × Nat) := do
  let type ← whnfCore type
  if type.consumeMData.getAppFn.constName? == some ``Prod then
    let args := type.consumeMData.getAppArgs
    unless args.size == 2 do throwError "malformed product input type"
    let (left, index) ← packProdInput args[0]! values index
    let (right, index) ← packProdInput args[1]! values index
    return (← mkAppM ``Prod.mk #[left, right], index)
  unless index < values.size do throwError "not enough gadget source arguments"
  return (values[index]!, index + 1)

/-- Recover a gadget's input from the concrete operation at the head of a
bind.  Binary and ternary contracts are written as lambdas over nested
products, so their components are the final operation arguments.  Doing this
syntactically avoids asking the unifier to normalize the entire remaining
circuit merely to discover a small tuple. -/
private def gadgetInputFromSource (inputType gadget source : Expr) : MetaM Expr := do
  let gadgetWhnf := reduceProgramWrappers gadget
  let sourceWhnf := reduceProgramWrappers source
  let sourceArgs := sourceWhnf.consumeMData.getAppArgs
  if gadgetWhnf.consumeMData.isLambda then
    let count ← prodLeafCount inputType
    unless count ≤ sourceArgs.size do
      throwError "not enough source arguments for gadget product input"
    let values := sourceArgs.extract (sourceArgs.size - count) sourceArgs.size
    return (← packProdInput inputType values).1
  if sourceArgs.isEmpty then throwError "gadget source has no input argument"
  return sourceArgs[sourceArgs.size - 1]!

/-- Match only the shallow operation application.  All large continuation
terms have already been assigned directly by the caller. -/
private def matchGadgetSource (gadget input source : Expr) : MetaM Unit := do
  let gadgetType ← whnf (← inferType gadget)
  let expected ← match gadgetType with
    | .forallE _ domain _ binderInfo =>
        if domain.consumeMData.isConstOf ``Context &&
            binderInfo != .default then
          let ctx ← mkFreshExprMVar domain
          pure (mkApp (mkApp gadget ctx) input)
        else
          pure (mkApp gadget input)
    | _ => pure (mkApp gadget input)
  let _ ← inferType expected
  let expected := reduceProgramWrappers expected
  let source := reduceProgramWrappers source
  unless expected.consumeMData.getAppFn == source.consumeMData.getAppFn do
    throwError "gadget source has the wrong operation head"
  let expectedArgs := expected.consumeMData.getAppArgs
  let sourceArgs := source.consumeMData.getAppArgs
  unless expectedArgs.size == sourceArgs.size do
    throwError "gadget source has the wrong number of arguments"
  for expectedArg in expectedArgs, sourceArg in sourceArgs do
    let expectedArg ← instantiateMVars expectedArg
    if let .mvar mvarId := expectedArg then
      mvarId.assign sourceArg
    else unless expectedArg == sourceArg || (← isDefEq expectedArg sourceArg) do
      throwError "gadget source argument does not match its contract"

private def mkGadgetBindRule (direct : Bool) (target spec : Expr) : MetaM Expr := do
  let specTypeRaw ← inferType spec
  let specType := specTypeRaw.consumeMData
  unless specType.getAppFn.constName? == some ``GadgetSpec do
    throwError "supplied theorem is not a `GadgetSpec`"
  let specArgs := specType.getAppArgs
  unless specArgs.size == 5 do
    throwError "malformed `GadgetSpec` theorem"
  let ruleName := if direct then
    ``GadgetSpec.bind_rule_direct
  else
    ``GadgetSpec.bind_rule
  let rule ← mkConstWithFreshMVarLevels ruleName
  let (params, _, _) ← forallMetaTelescopeReducing
    (← inferType rule) (some 5)
  -- The supplied theorem was indexed by its gadget head when the rule DB was
  -- built.  Instantiate the bind rule directly from its syntactic contract
  -- parameters instead of unifying two fully normalized contract types.
  params[0]!.mvarId!.assign specArgs[0]!
  params[1]!.mvarId!.assign specArgs[1]!
  params[2]!.mvarId!.assign specArgs[2]!
  params[3]!.mvarId!.assign specArgs[4]!
  params[4]!.mvarId!.assign specArgs[3]!
  let applied := mkAppN rule params
  let withSpec := mkApp applied spec

  let targetArgs := target.consumeMData.getAppArgs
  unless target.consumeMData.getAppFn.constName? == some ``Rel &&
      targetArgs.size == 8 do
    throwError "gadget bind rule expected a `Rel` target"
  let some (sourceL, contL) ← bindParts? targetArgs[6]!
    | throwError "gadget bind rule expected a left bind"
  let some (sourceR, contR) ← bindParts? targetArgs[7]!
    | throwError "gadget bind rule expected a right bind"

  let (bindParams, _, _) ← forallMetaTelescopeReducing
    (← inferType withSpec) (some 10)
  bindParams[0]!.mvarId!.assign targetArgs[0]!
  bindParams[1]!.mvarId!.assign targetArgs[1]!
  bindParams[2]!.mvarId!.assign targetArgs[2]!
  bindParams[3]!.mvarId!.assign targetArgs[3]!
  bindParams[4]!.mvarId!.assign targetArgs[4]!
  bindParams[5]!.mvarId!.assign targetArgs[5]!
  let inputL ← gadgetInputFromSource (mkApp specArgs[0]! targetArgs[0]!)
    specArgs[3]! sourceL
  let inputR ← gadgetInputFromSource (mkApp specArgs[0]! targetArgs[1]!)
    specArgs[3]! sourceR
  bindParams[6]!.mvarId!.assign inputL
  bindParams[7]!.mvarId!.assign inputR
  matchGadgetSource specArgs[3]! inputL sourceL
  matchGadgetSource specArgs[3]! inputR sourceR
  bindParams[8]!.mvarId!.assign contL
  bindParams[9]!.mvarId!.assign contR
  return mkAppN withSpec bindParams

private def mkGadgetBindRuleLegacy (direct : Bool) (spec : Expr) : MetaM Expr := do
  let ruleName := if direct then
    ``GadgetSpec.bind_rule_direct
  else
    ``GadgetSpec.bind_rule
  let rule ← mkConstWithFreshMVarLevels ruleName
  let (params, _, _) ← forallMetaTelescopeReducing
    (← inferType rule) (some 5)
  let applied := mkAppN rule params
  let appliedType ← inferType applied
  let .forallE _ expected _ _ ← whnf appliedType
    | throwError "malformed `GadgetSpec.bind_rule_direct`"
  unless ← isDefEq (← inferType spec) expected do
    throwError "supplied theorem is not a compatible `GadgetSpec`"
  return mkApp applied spec

private def mkGadgetDirectRule (target spec : Expr) : MetaM Expr := do
  let specType := (← inferType spec).consumeMData
  unless specType.getAppFn.constName? == some ``GadgetSpec do
    throwError "supplied theorem is not a `GadgetSpec`"
  let specArgs := specType.getAppArgs
  unless specArgs.size == 5 do
    throwError "malformed `GadgetSpec` theorem"
  let rule ← mkConstWithFreshMVarLevels ``GadgetSpec.direct_rule
  let (params, _, _) ← forallMetaTelescopeReducing
    (← inferType rule) (some 5)
  params[0]!.mvarId!.assign specArgs[0]!
  params[1]!.mvarId!.assign specArgs[1]!
  params[2]!.mvarId!.assign specArgs[2]!
  params[3]!.mvarId!.assign specArgs[4]!
  params[4]!.mvarId!.assign specArgs[3]!
  let withSpec := mkApp (mkAppN rule params) spec

  let targetArgs := target.consumeMData.getAppArgs
  unless target.consumeMData.getAppFn.constName? == some ``Rel &&
      targetArgs.size == 8 do
    throwError "direct gadget rule expected a `Rel` target"
  let (directParams, _, _) ← forallMetaTelescopeReducing
    (← inferType withSpec) (some 5)
  directParams[0]!.mvarId!.assign targetArgs[0]!
  directParams[1]!.mvarId!.assign targetArgs[1]!
  directParams[2]!.mvarId!.assign targetArgs[5]!
  let inputL ← gadgetInputFromSource (mkApp specArgs[0]! targetArgs[0]!)
    specArgs[3]! targetArgs[6]!
  let inputR ← gadgetInputFromSource (mkApp specArgs[0]! targetArgs[1]!)
    specArgs[3]! targetArgs[7]!
  directParams[3]!.mvarId!.assign inputL
  directParams[4]!.mvarId!.assign inputR
  matchGadgetSource specArgs[3]! inputL targetArgs[6]!
  matchGadgetSource specArgs[3]! inputR targetArgs[7]!
  return mkAppN withSpec directParams

private def tryGadgetRules (db : RuleDB) (direct : Bool) (goal : MVarId)
    (target : Expr) : MetaM (Option (List MVarId)) := do
  let some gadget := relProgramHead? target | return none
  let some rules := db.gadgets[gadget]? | return none
  for declName in rules do
    if let some goals ← observing? do
      let spec ← instantiateRule declName
      let proof ← mkGadgetBindRule direct target spec
      goal.apply proof { newGoals := .all, synthAssignedInstances := true }
    then
      return some goals
    if direct then
      let targetArgs := target.consumeMData.getAppArgs
      if targetArgs.size == 8 &&
          (← bindParts? targetArgs[6]!).isNone then
        let spec ← instantiateRule declName
        let proof ← try mkGadgetDirectRule target spec catch error =>
          throwError "failed to construct direct gadget rule for {declName}: {error.toMessageData}"
        return some (← try goal.apply proof {
          newGoals := .all, synthAssignedInstances := true } catch error =>
            throwError "failed to apply direct gadget rule for {declName}: {error.toMessageData}")
      continue
    if let some goals ← observing? do
      let spec ← instantiateRule declName
      let proof ← mkGadgetBindRuleLegacy direct spec
      goal.apply proof { newGoals := .all, synthAssignedInstances := true }
    then
      return some goals
  return none

private def solve (db : RuleDB) (cache : LocalRuleCache)
    (useLocalLogic : Bool)
    (goal : MVarId) : MetaM SolveResult :=
    goal.withContext do
  if ← goal.isAssigned then return .progressed []
  -- Do not delta-reduce the target here.  Semantic constructors such as
  -- `U.intVal` are precisely the heads used to select congruence rules.
  -- The tactic-level `dsimp only` performed on entry handles beta/iota/zeta
  -- redexes without erasing those heads.
  let normalized := goal
  let normalizedTarget ← instantiateMVars (← normalized.getType)

  -- A contract's postcondition is commonly exactly the premise needed by its
  -- continuation.  Consume such facts before expanding semantic congruence
  -- rules into strictly stronger componentwise obligations.
  if ← tryRflOrAssumption normalized then
    return .progressed []

  if let some rules := relRulesFor? normalizedTarget then
    if let some goals ← tryRules normalized rules then
      return .progressed goals
    return .stuck


  if let some goals ← tryGadgetRules db (!useLocalLogic) normalized normalizedTarget then
    return .progressed goals

  if let some declName := relHomRuleFor? normalizedTarget then
    let pattern ← getRulePattern declName
    if let some goals ← tryApplyRule normalized { declName, pattern } then
      return .progressed goals
    return .stuck

  -- Once syntax-directed circuit rules have had first choice, semantic leaf
  -- obligations should preferentially consume facts already established by
  -- preceding gadgets.
  if useLocalLogic then
    if let some goals ← tryLocalLogic cache normalized then
      return .progressed goals

  if let some declName := lcRuleFor? normalizedTarget then
    let pattern ← getRulePattern declName
    if let some goals ← tryApplyRule normalized { declName, pattern } then
      return .progressed goals
    return .stuck

  if let some declName := evalEqRuleFor? normalizedTarget then
    let pattern ← getRulePattern declName
    if let some goals ← tryApplyRule normalized { declName, pattern } then
      return .progressed goals
    return .stuck

  if let some wrapper := transparentWrapper? normalizedTarget then
    return .progressed [← unfoldTarget normalized wrapper]

  if normalizedTarget.consumeMData.isForall then
    let (_, next) ← normalized.intro1P
    return .progressed [next]

  if normalizedTarget.consumeMData.getAppFn.constName? == some ``And then
    return .progressed (← normalized.apply (mkConst ``And.intro) { newGoals := .all })

  if normalizedTarget.consumeMData.isConstOf ``True then
    return .progressed (← normalized.apply (mkConst ``True.intro))

  -- Symbolic matching may instantiate metavariables while checking Miller
  -- patterns. Lookup is only a classification step here, so run it
  -- transactionally and retain only the matching rule names.
  let candidates ← withoutModifyingState do
    Sym.SymM.run do
      let normalizedTarget ← Sym.share normalizedTarget
      let candidates := Sym.getMatch db.tree normalizedTarget
      candidates.filterM fun rule =>
        Option.isSome <$> rule.pattern.match? normalizedTarget
  if candidates.isEmpty then
    return .stuck
  if candidates.size > 1 then
    let names := candidates.map (·.declName)
    throwError "`wfgen'` found ambiguous rules for\n{normalizedTarget}\nCandidates: {names}"
  if let some goals ← tryApplyRule normalized candidates[0]! then
    return .progressed goals
  return .stuck

structure DriverState where
  pending : Array MVarId := #[]
  invariants : Array MVarId := #[]
  vcs : Array MVarId := #[]
  steps : Nat := 0

private def enqueueGenerated (state : DriverState) (goals : List MVarId) : MetaM DriverState := do
  let mut state := state
  let mut propGoals : Array MVarId := #[]
  let mut foundInvariant := false
  for goal in goals do
    if ← goal.isAssigned then continue
    let isPropGoal ← goal.withContext do
      isProp (← instantiateMVars (← goal.getType))
    if isPropGoal then
      propGoals := propGoals.push goal
    else
      foundInvariant := true
      goal.setKind .syntheticOpaque
      state := { state with invariants := state.invariants.push goal }
  -- An unknown invariant is a symbolic-execution barrier.  Keep all
  -- obligations depending on it visible, but do not simplify them until the
  -- user has supplied the invariant and invokes `wfgen'` again.
  if foundInvariant then
    for goal in propGoals do
      goal.setKind .syntheticOpaque
    state := { state with vcs := state.vcs ++ propGoals }
  else
    state := { state with pending := state.pending ++ propGoals }
  return state

private def run (db : RuleDB) (goals : List MVarId)
    (useLocalLogic : Bool := true) : MetaM DriverState := do
  let localRuleCache ←
    IO.mkRef ({} : Std.HashMap (FVarId × Name) (Array Expr))
  let mut state : DriverState := { pending := goals.toArray }
  while let some goal := state.pending.back? do
    state := { state with pending := state.pending.pop, steps := state.steps + 1 }
    if state.steps > 1024 then
      goal.setKind .syntheticOpaque
      state := { state with vcs := state.vcs.push goal }
      continue
    if ← goal.isAssigned then continue
    match ← solve db localRuleCache useLocalLogic goal with
    | .progressed generated =>
        state ← enqueueGenerated state generated
    | .stuck =>
        goal.setKind .syntheticOpaque
        state := { state with vcs := state.vcs.push goal }

  for h : i in [:state.invariants.size] do
    state.invariants[i].setTag <| Name.mkSimple s!"inv{i + 1}"
  for h : i in [:state.vcs.size] do
    state.vcs[i].setTag <| Name.mkSimple s!"vc{i + 1}"
  return state

private def resolveRuleNames (rules : Array Ident) : TacticM (Array Name) :=
  rules.mapM fun id => realizeGlobalConstNoOverloadWithInfo id.raw

private def evalWFGen (rules defs : Array Ident)
    (useLocalLogic : Bool := true) : TacticM Unit := do
  for defName in defs do
    evalTactic (← `(tactic| unfold $defName))
  evalTactic (← `(tactic| try dsimp only))
  evalTactic (← `(tactic| try simp only [bind_assoc, pure_bind]))
  let db ← buildRuleDB (← resolveRuleNames rules)
  let result ← run db (← getGoals) useLocalLogic
  let invariants ← result.invariants.filterM fun goal => not <$> goal.isAssigned
  let vcs ← result.vcs.filterM fun goal => not <$> goal.isAssigned
  setGoals (invariants.toList ++ vcs.toList)

elab "wfgen'" : tactic => evalWFGen #[] #[]

elab "wfgen'" "[" defs:ident,* "]" : tactic => evalWFGen #[] defs

elab "wfgen'" "using" "[" rules:ident,* "]" : tactic =>
  evalWFGen rules #[]

elab "wfgen'" "using" "[" rules:ident,* "]" "unfold" "[" defs:ident,* "]" : tactic =>
  evalWFGen rules defs

/-- Generate the circuit skeleton while leaving semantic leaf VCs to the
caller.  This is useful for wide straight-line gadgets whose local relations
are cheaper for a domain-specific finishing tactic than for generic search. -/
elab "wfgen_steps'" "using" "[" rules:ident,* "]" "unfold" "[" defs:ident,* "]" : tactic =>
  evalWFGen rules defs false

end WFGen

end Freigen.F2Z.WF
