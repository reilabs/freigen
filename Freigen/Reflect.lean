import Freigen.Ast

/-!
# The `reflect%` elaborator

Reflects a real Lean `Free (Effect Op)` computation into an explicit `Prog` AST, paired with a
`rfl`-backed proof that denoting the AST recovers the original computation.
-/

namespace Freigen

open Lean Lean.Meta Lean.Elab Lean.Elab.Term

/-! ## The `reflect%` elaborator

`reflect% e` takes a real Lean term `e : A₁ → … → Aₙ → Free (Effect Op) τ` (a function
returning a free-monadic value; `n = 0` is allowed) and produces

```
reflect% e : { g : A₁ → … → Aₙ → Exp Op Tp.denote τ̂ // ∀ a…, denote (g a…) = e a… }
```

where `τ̂` is the `Tp` reifying `τ`.  Every Lean type the walk needs (the result type, and
the type of each literal/atom) is reified into a `Tp` via `reifyTp`; if a type is not
expressible, the elaborator aborts.  The walk is continuation-passing, so the result
comes out A-normal, and `denote` of it is *definitionally* the original computation, so
the soundness proof is just `rfl`.
-/

/-- The denotation `Tp.denote : Tp → Type`, the variable representation `reflect%`
    targets (so the denoted program runs at the real Lean types). -/
private def denoteV : Expr := .const ``Tp.denote []

/-- Reify a Lean type into the object type universe `Tp`, or `none` if unsupported.
    Supported: `Bool`, `Nat`, `ZMod n`, `Unit`, products, `Vector`/`Array`, and
    (non-dependent) functions. -/
private partial def reifyTp (T : Expr) : MetaM (Option Expr) := do
  -- Match the head *before* reducing — `whnf` would unfold e.g. `ZMod 5` to `Fin 5`.
  match_expr T with
  | Bool     => return some (.const ``Tp.bool [])
  | Nat      => return some (.const ``Tp.nat [])
  | ZMod n   => return some (mkApp (.const ``Tp.zmod []) n)
  | PUnit    => return some (.const ``Tp.unit [])
  | Prod A B =>
    let some a ← reifyTp A | return none
    let some b ← reifyTp B | return none
    return some (mkApp2 (.const ``Tp.prod []) a b)
  | Vector A n =>
    let some a ← reifyTp A | return none
    return some (mkApp2 (.const ``Tp.vec []) a n)
  | Array A =>
    let some a ← reifyTp A | return none
    return some (mkApp (.const ``Tp.array []) a)
  | Sum A B =>
    let some a ← reifyTp A | return none
    let some b ← reifyTp B | return none
    return some (mkApp2 (.const ``Tp.sum []) a b)
  | _ =>
    -- a (non-dependent) function type `A → B`
    if let .forallE _ A B _ := T then
      if B.hasLooseBVars then return none      -- dependent Π: unsupported
      let some a ← reifyTp A | return none
      let some b ← reifyTp B | return none
      return some (mkApp2 (.const ``Tp.fn []) a b)
    else
      -- unfold a transparent alias one *delta* step and retry (e.g. `Unit` → `PUnit`, or a
      -- user abbrev `Fr := ZMod p` → `ZMod p`).  We unfold a single definition rather than
      -- `whnf`-ing, so we stop at a named head like `ZMod`/`Vector` instead of blasting through
      -- to its implementation (`whnf` would reduce `ZMod p` all the way to `Fin p`).
      match ← unfoldDefinition? T with
      | some T' => reifyTp T'
      | none    => return none

/-- Reify a Lean type into a `Tp`, aborting elaboration if it is unsupported. -/
private def reifyTpOrThrow (T : Expr) : MetaM Expr := do
  match ← reifyTp T with
  | some tp => return tp
  | none    => throwError "reflect%: type is not expressible as a `Tp` \
                           (supported: `Bool`/`Nat`/`ZMod _`/`Unit`/`×`/`Vector`/`Array`/`→`){indentExpr T}"

/-- One monomorphised function spill discovered during reflection: the source constant, its
    (object) argument-type list and result type, and the reflected body (a closed
    `HList V as → Exp Op F V b`, to become a top-level `Prog.def_`). -/
private structure DefEntry where
  name    : Name
  asList  : Expr
  retTp   : Expr
  bodyLam : Expr
  deriving Inhabited

/-- A reflection environment: the abstract function/variable representations `F`/`V` we build
    against, a substitution from continuation-bound host placeholders to object atoms, the
    running spill cache `defs`, whether we are inside a function body (bodies may not call
    definitions), and — during the second (build) pass — the function-name bound to each
    spill (`resolved`). -/
private structure Env where
  F : Expr
  V : Expr
  subst : List (FVarId × Expr)
  defs : IO.Ref (Array DefEntry)
  inBody : Bool := false
  resolved : Option (Array (DefEntry × Expr)) := none

/-- Bind a host literal `a : αTp.denote` as a fresh atom and feed that atom to `k`,
    wrapping the result in a `lit` node.  This is the A-normalisation step that turns a
    literal operand into an atom. -/
private def Env.mkLitBind (env : Env) (Op a αTp : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
  withLocalDeclD `v (mkApp env.V αTp) fun vx => do
    let body ← k vx
    let lam ← mkLambdaFVars #[vx] body
    mkAppOptM ``Exp.lit #[Op, env.F, env.V, αTp, none, a, lam]

/-- `letE`-bind a function value `lam bodyLam : Exp … (.fn αt βt)`, feeding its atom to `k`. -/
private def Env.mkLam (env : Env) (Op αt βt bodyLam : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
  let lamVal ← mkAppOptM ``Exp.lam #[Op, env.F, env.V, αt, βt, bodyLam]
  let fnTp := mkApp2 (.const ``Tp.fn []) αt βt
  withLocalDeclD `f (mkApp env.V fnTp) fun fAtom => do
    let lamK ← mkLambdaFVars #[fAtom] (← k fAtom)
    mkAppOptM ``Exp.letE #[Op, env.F, env.V, fnTp, none, lamVal, lamK]

/-- Emit a `ret` node returning the atom. -/
private def Env.mkRet (env : Env) (Op atom : Expr) : MetaM Expr :=
  mkAppOptM ``Exp.ret #[Op, env.F, env.V, none, atom]

/-- Build the argument tuple `HList env.V [tps]` from already-reflected atoms. -/
private def Env.mkArgHList (env : Env) (atoms : List Expr) : MetaM Expr := do
  let mut h ← mkAppOptM ``HList.nil #[none, env.V]
  for a in atoms.reverse do
    h ← mkAppM ``HList.cons #[a, h]
  pure h

/-- Project the `j`-th element out of an argument-`HList` value `hargs` (via `head`/`tail`). -/
private def projHList (hargs : Expr) (j : Nat) : MetaM Expr := do
  let mut h := hargs
  for _ in [0:j] do h ← mkAppM ``HList.tail #[h]
  mkAppM ``HList.head #[h]

/-- Pick the binary primitive for an arithmetic result type: `Nat` uses the `…` ops,
    `ZMod n` the `…Z` ops.  Returns the primitive and the result object type. -/
private def Env.arithOp (_env : Env) (natC zmodC : Name) (resTy : Expr) : MetaM (Expr × Expr) := do
  let cTp ← reifyTpOrThrow resTy
  match_expr cTp with
  | Tp.nat    => return (.const natC [], cTp)
  | Tp.zmod n => return (mkApp (.const zmodC []) n, cTp)
  | _         => throwError "reflect%: unsupported arithmetic result type{indentExpr cTp}"

/-- Build the projection primitive `@ctor a b` (`Un.fst`/`Un.snd`) for a value `p`
    whose object type must be a product `Tp.prod a b`. -/
private def Env.prodUn (_env : Env) (ctor : Name) (p : Expr) : MetaM Expr := do
  match_expr ← reifyTpOrThrow (← inferType p) with
  | Tp.prod a b => return mkApp2 (.const ctor []) a b
  | _           => throwError "reflect%: projection applied to a non-product{indentExpr p}"

mutual
  /-- Reflect a *pure* host value into an atom, A-normalising any arithmetic into a chain
      of `un`/`bin` lets, and feed the resulting atom to `k`.  Cases, in order:
      a continuation-bound variable is already an atom; a `ForInStep.yield` is unwrapped
      (loop-body tail); a value closed w.r.t. bound variables is `lit`-bound (also the
      point at which an unsupported type aborts); otherwise it must be a recognised
      primitive applied to sub-expressions, else we abort. -/
  private partial def Env.reflectExpr (env : Env) (Op a : Expr) (k : Expr → MetaM Expr) :
      MetaM Expr := do
    let a := a.consumeMData
    if let .fvar fid := a then
      if let some atom := env.subst.lookup fid then return ← k atom
    match_expr a with
    | ForInStep.yield _ v => return ← env.reflectExpr Op v k
    | ForInStep.done _ _  =>
        throwError "reflect%: `break`/early `return` inside a loop is not supported{indentExpr a}"
    | _ => pure ()
    -- a host lambda → an object-language `lam` value (its body reflected purely)
    if a.isLambda then
      if let .forallE _ A B _ := (← whnf (← inferType a)) then
        if let (some αt, some βt) := (← reifyTp A, ← reifyTp B) then
          let bodyLam ← withLocalDeclD `v (mkApp env.V αt) fun vArg =>
            withLocalDeclD `h A fun hx => do
              let env' := { env with subst := (hx.fvarId!, vArg) :: env.subst }
              mkLambdaFVars #[vArg] (← env'.reflectExpr Op (a.beta #[hx]) (env.mkRet Op ·))
          return ← env.mkLam Op αt βt bodyLam k
    -- closed w.r.t. bound variables → a literal (function arguments are allowed here)
    if !(a.hasAnyFVar fun fid => (env.subst.lookup fid).isSome) then
      return ← env.mkLitBind Op a (← reifyTpOrThrow (← inferType a)) k
    -- otherwise: a recognised primitive on sub-expressions
    match_expr a with
    | HMul.hMul _ _ _ _ x y => let (o, c) ← env.arithOp ``Bin.mul ``Bin.mulZ (← inferType a); env.reflectBin Op o c x y k
    | HAdd.hAdd _ _ _ _ x y => let (o, c) ← env.arithOp ``Bin.add ``Bin.addZ (← inferType a); env.reflectBin Op o c x y k
    | HSub.hSub _ _ _ _ x y => let (o, c) ← env.arithOp ``Bin.sub ``Bin.subZ (← inferType a); env.reflectBin Op o c x y k
    | HPow.hPow _ _ _ _ x y => env.reflectBin Op (.const ``Bin.pow []) (.const ``Tp.nat []) x y k
    | BEq.beq _ _ x y       => env.reflectBin Op (.const ``Bin.eq [])  (.const ``Tp.bool []) x y k
    | Bool.and x y          => env.reflectBin Op (.const ``Bin.and []) (.const ``Tp.bool []) x y k
    | Bool.or  x y          => env.reflectBin Op (.const ``Bin.or [])  (.const ``Tp.bool []) x y k
    | Bool.not x            => env.reflectUn  Op (.const ``Un.not [])   (.const ``Tp.bool []) x k
    | Prod.mk _ _ x y       =>
        let aTp ← reifyTpOrThrow (← inferType x)
        let bTp ← reifyTpOrThrow (← inferType y)
        env.reflectBin Op (mkApp2 (.const ``Bin.pair []) aTp bTp)
          (mkApp2 (.const ``Tp.prod []) aTp bTp) x y k
    | Prod.fst _ _ p        => env.reflectUn Op (← env.prodUn ``Un.fst p) (← reifyTpOrThrow (← inferType a)) p k
    | Prod.snd _ _ p        => env.reflectUn Op (← env.prodUn ``Un.snd p) (← reifyTpOrThrow (← inferType a)) p k
    | Sum.inl A B x         => do
        let aTp ← reifyTpOrThrow A; let bTp ← reifyTpOrThrow B
        env.reflectUn Op (mkApp2 (.const ``Un.inl []) aTp bTp) (mkApp2 (.const ``Tp.sum []) aTp bTp) x k
    | Sum.inr A B x         => do
        let aTp ← reifyTpOrThrow A; let bTp ← reifyTpOrThrow B
        env.reflectUn Op (mkApp2 (.const ``Un.inr []) aTp bTp) (mkApp2 (.const ``Tp.sum []) aTp bTp) x k
    -- vector indexing `v[i]` → the proof-erased `vecGet` (denotes to `getElem!`).  The index is
    -- kept as a `Nat`: a `Fin n` index is reflected as `i.val`, dropping its bound (and a `Nat`
    -- index drops its in-bounds proof).  The denotation gap (host `v[i]` vs erased `v[i]!`) is
    -- reconciled by `bridgeErase`, which is exactly where the dropped `Fin`/`Nat` proof reappears.
    | getElem _ idxTy _ _ _ v idx _ =>
        let natIdx ← match_expr idxTy with
          | Nat   => pure idx
          | Fin _ => mkAppM ``Fin.val #[idx]
          | _     => throwError "reflect%: a vector index must be `Nat` or `Fin _`{indentExpr idxTy}"
        match_expr ← reifyTpOrThrow (← inferType v) with
        | Tp.vec aTp n => env.reflectBin Op (mkApp2 (.const ``Bin.vecGet []) aTp n) aTp v natIdx k
        | _ => throwError "reflect%: `[]`-indexing is only supported on `Vector`{indentExpr a}"
    | _ => throwError "reflect%: cannot reflect this operation on a bound variable \
                       (no matching object primitive){indentExpr a}"

  /-- Reflect a binary primitive: reflect both operands to atoms, then emit a `bin` node
      binding the result (of object type `cTp`). -/
  private partial def Env.reflectBin (env : Env) (Op binOp cTp x y : Expr)
      (k : Expr → MetaM Expr) : MetaM Expr :=
    env.reflectExpr Op x fun ax =>
    env.reflectExpr Op y fun ay =>
    withLocalDeclD `v (mkApp env.V cTp) fun vc => do
      let lam ← mkLambdaFVars #[vc] (← k vc)
      mkAppOptM ``Exp.bin #[Op, env.F, env.V, none, none, none, none, binOp, ax, ay, lam]

  /-- Reflect a unary primitive: reflect the operand to an atom, then emit a `un` node. -/
  private partial def Env.reflectUn (env : Env) (Op unOp cTp x : Expr)
      (k : Expr → MetaM Expr) : MetaM Expr :=
    env.reflectExpr Op x fun ax =>
    withLocalDeclD `v (mkApp env.V cTp) fun vc => do
      let lam ← mkLambdaFVars #[vc] (← k vc)
      mkAppOptM ``Exp.un #[Op, env.F, env.V, none, none, none, unOp, ax, lam]
end

/-- Reflect a list of host value-arguments into atoms (left to right), then continue with the
    collected atom list. -/
private partial def Env.reflectArgList (env : Env) (Op : Expr) :
    List Expr → (List Expr → MetaM Expr) → MetaM Expr
  | [],      k => k []
  | a :: as, k => env.reflectExpr Op a (fun atom => env.reflectArgList Op as (fun atoms => k (atom :: atoms)))

mutual
  /-- Reflect a host `Free (Effect Op) _` expression into an `Exp Op V _`, in A-normal
      form.  `k` is the *final* continuation: it consumes the atom holding this
      computation's result and produces the tail of the program. -/
  private partial def walkProg (env : Env) (Op e : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
    let e := e.consumeMData.headBeta
    -- zeta-reduce `let`/`have` introduced by `do`-elaboration
    if let .letE _ _ v b _ := e then
      return ← walkProg env Op (b.instantiate1 v) k
    match_expr e with
    | Free.Pure _ _ a         => env.reflectExpr Op a k
    | Pure.pure _ _ _ a       => env.reflectExpr Op a k
    | Bind.bind _ _ _ _ x f   => walkBind env Op x f k
    | freeBind _ _ _ x f      => walkBind env Op x f k
    | ForIn.forIn _ _ _ _ beta range init body => walkForN env Op range init body beta k
    | cond _ c t e => walkIte env Op c t e k
    | Free.Impure _ _ _ eff cont =>
      -- `eff : Effect Op O` is `Effect.mk (o : Op I O) (inp : I)`; reify the (Lean) input and
      -- result types back to object types, then reflect the input atom
      match_expr eff with
      | Effect.mk _ I O o inp => do
          let Itp ← reifyTpOrThrow I
          let Otp ← reifyTpOrThrow O
          env.reflectExpr Op inp (fun ia => walkOp env Op Itp Otp o ia cont k)
      | _ => throwError "reflect%: effect is not an `Effect.mk`{indentExpr eff}"
    | _ =>
      -- a call to a user definition (a subroutine) → monomorphised `call`; otherwise (an
      -- effect primitive, or anything not call-shaped) unfold its head and inline
      match ← tryCall env Op e k with
      | some prog => pure prog
      | none =>
        match ← unfoldDefinition? e with
        | some e' => walkProg env Op e' k
        | none    => throwError "reflect%: don't know how to reflect computation{indentExpr e}"

  /-- Reflect a `bind x f`.  A *pure* `x` (`pure a`) is inlined via the monad left-identity
      law (`pure a >>= f ≡ f a`) — this elides the unit-typed `pure ()` actions that
      `do`-notation inserts between statements; otherwise `x` is an effect whose result atom
      is threaded into `f`. -/
  private partial def walkBind (env : Env) (Op x f : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
    match_expr x.consumeMData.headBeta with
    | Free.Pure _ _ a   => walkProg env Op (f.beta #[a]) k
    | Pure.pure _ _ _ a => walkProg env Op (f.beta #[a]) k
    | _                 => walkProg env Op x (fun xa => walkBindCont env Op f xa k)

  /-- Continue a `bind`: `f : X → Free _ τ` is the binder, `xa : V α` is the atom holding
      the bound value.  Apply `f` to a host placeholder (rewritten to `xa`) and walk its
      body with the same final continuation `k`. -/
  private partial def walkBindCont (env : Env) (Op f xa : Expr) (k : Expr → MetaM Expr) :
      MetaM Expr := do
    let fty ← whnf (← inferType f)
    let .forallE _ X _ _ := fty
      | throwError "reflect%: expected a continuation function, got{indentExpr fty}"
    withLocalDeclD `h X fun hx => do
      let env' := { env with subst := (hx.fvarId!, xa) :: env.subst }
      walkProg env' Op (f.beta #[hx]) k

  /-- Emit an `op` node.  `Itp`/`Otp : Tp` are the op's input/result object types and `cont :
      Otp.denote → Free _ τ` its continuation; we introduce the object variable `vx : V Otp`
      it binds and a host placeholder `hx : Otp.denote` (rewritten to `vx`), then walk the
      rest.  `Itp`/`Otp` are passed explicitly because `Op` is opaque (they can't be recovered
      from `o`'s type by inverting `Tp.denote`). -/
  private partial def walkOp (env : Env) (Op Itp Otp o ia cont : Expr) (k : Expr → MetaM Expr) :
      MetaM Expr := do
    let cty ← whnf (← inferType cont)
    let .forallE _ Rt _ _ := cty
      | throwError "reflect%: expected an op continuation, got{indentExpr cty}"
    withLocalDeclD `v (mkApp env.V Otp) fun vx =>
    withLocalDeclD `h Rt fun hx => do
      let env' := { env with subst := (hx.fvarId!, vx) :: env.subst }
      let body ← walkProg env' Op (cont.beta #[hx]) k
      let lam ← mkLambdaFVars #[vx] body
      mkAppOptM ``Exp.op #[Op, env.F, env.V, none, Itp, Otp, o, ia, lam]

  /-- Reflect a `ForIn.forIn` over a constant range `[0:n]` into a `forN` node.  `beta` is
      the (host) loop-state type; `body : Nat → β → Free _ (ForInStep β)`.  We require a
      literal `[0:n]` (start 0, step 1), reflect the initial state to an atom, build the
      body under fresh index/state atoms (its tail `ForInStep.yield` is unwrapped by
      `reflectExpr`), and thread the final state into `k`. -/
  private partial def walkForN (env : Env) (Op range init body beta : Expr)
      (k : Expr → MetaM Expr) : MetaM Expr := do
    let sTp ← reifyTpOrThrow beta
    let nExpr ← match_expr range with
      | Std.Legacy.Range.mk start stop step _ => do
          unless ← isDefEq start (mkNatLit 0) do
            throwError "reflect%: loop range must start at 0{indentExpr range}"
          unless ← isDefEq step (mkNatLit 1) do
            throwError "reflect%: loop range must have step 1{indentExpr range}"
          pure stop
      | _ => throwError "reflect%: loop range is not a literal `[0:n]`{indentExpr range}"
    env.reflectExpr Op init fun initAtom => do
      let bodyLam ← withLocalDeclD `i (mkApp env.V (.const ``Tp.nat [])) fun vi =>
                    withLocalDeclD `s (mkApp env.V sTp) fun vs =>
                    withLocalDeclD `hi (.const ``Nat []) fun hi =>
                    withLocalDeclD `hs beta fun hs => do
                      let env' := { env with
                        subst := (hi.fvarId!, vi) :: (hs.fvarId!, vs) :: env.subst }
                      let bodyExp ← walkProg env' Op (body.beta #[hi, hs]) (env.mkRet Op ·)
                      mkLambdaFVars #[vi, vs] bodyExp
      let contLam ← withLocalDeclD `r (mkApp env.V sTp) fun vr => do
                      mkLambdaFVars #[vr] (← k vr)
      mkAppOptM ``Exp.forN #[Op, env.F, env.V, none, sTp, nExpr, initAtom, bodyLam, contLam]

  /-- Reflect a boolean branch `bif c then t else e` (`cond c t e`) into an `Exp.ite`: reflect the
      condition to a `.bool` atom, walk each branch as a sub-computation, then thread the result. -/
  private partial def walkIte (env : Env) (Op c t e : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
    -- the program's continuation `k` is pushed into *both* branches, so `ite` has no trailing
    -- continuation and `denote (ite …) = cond …` definitionally (keeps the `rfl` soundness).
    env.reflectExpr Op c fun ca => do
      let tExp ← walkProg env Op t k
      let eExp ← walkProg env Op e k
      mkAppOptM ``Exp.ite #[Op, env.F, env.V, none, ca, tExp, eExp]

  /-- Try to reflect `e` as a *call* to a user definition (returning `some prog`), or decline
      (`none`) so the caller inlines it instead.  A call is recognised purely by reflection:
      `e` must be an applied global `def` whose unfolding is **not** a bare `Free.Impure`
      (that would be an effect primitive — inline it) and which, after splitting off its
      *type parameters* (binders a later argument or the result depends on), has exactly one
      *value argument* of reifiable type.  Calls inside a function body are declined (so they
      inline) to keep every spill in one scope.  Qualifying calls are monomorphised: the
      `(constant, arg-type, result-type)` signature is looked up in the spill cache — a hit
      re-uses the bound function, a miss reflects the specialised body into a fresh `letFun`. -/
  private partial def tryCall (env : Env) (Op e : Expr) (k : Expr → MetaM Expr) :
      MetaM (Option Expr) := do
    if env.inBody then return none
    let fn := e.getAppFn
    let some cName := fn.constName? | return none
    let some ci := (← getEnv).find? cName | return none
    let some cVal := ci.value? | return none
    let fArgs := e.getAppArgs
    let cValInst := cVal.instantiateLevelParams ci.levelParams fn.constLevels!
    -- effect primitives (smart constructors unfolding to a bare `Free.Impure`) are inlined
    match_expr (cValInst.beta fArgs).consumeMData.headBeta with
    | Free.Impure _ _ _ _ _ => return none
    | _ => pure ()
    -- classify each binder as a type parameter (depended upon later) or a value argument
    let valuePos ← forallTelescope (← inferType fn) fun xs cod => do
      let mut vps : Array Nat := #[]
      for i in [0:xs.size] do
        let mut dep := cod.containsFVar xs[i]!.fvarId!
        for j in [i+1:xs.size] do
          if (← inferType xs[j]!).containsFVar xs[i]!.fvarId! then dep := true
        unless dep do vps := vps.push i
      pure vps
    -- a definition with ≥1 value argument becomes a call; anything else inlines
    if valuePos.size == 0 then return none
    let valueArgs := valuePos.toList.map (fArgs[·]!)
    let mut argTps : Array Expr := #[]
    for va in valueArgs do
      let some t ← reifyTp (← inferType va) | return none
      argTps := argTps.push t
    let asList ← mkListLit (.const ``Tp []) argTps.toList
    let some retTp ← (match_expr (← whnf (← inferType e)) with
                        | Free _ R => reifyTp R | _ => pure none) | return none
    let sigMatches (d : DefEntry) : MetaM Bool := do
      pure (d.name == cName && (← isDefEq d.asList asList) && (← isDefEq d.retTp retTp))
    -- reflect the argument atoms, build their `HList`, and emit a `call` to function `cf`
    let emit (cf : Expr) : MetaM Expr :=
      env.reflectArgList Op valueArgs (fun atoms => do
        env.emitCall Op cf asList retTp (← env.mkArgHList atoms) k)
    match env.resolved with
    | some resolved =>
      -- build pass: emit a call to the pre-bound function-name for this spill
      let some (_, cf) ← resolved.findM? (fun de => sigMatches de.1) | return none
      some <$> emit cf
    | none =>
      -- discovery pass: reflect the specialised body once (the main expression is discarded),
      -- recording the spill so the build pass can bind a name for it
      unless (← (← env.defs.get).findM? sigMatches).isSome do
        let hlistTy ← mkAppM ``HList #[env.V, asList]
        let bodyLam ← withLocalDeclD `args hlistTy fun hargs => do
          let decls : Array (Name × (Array Expr → MetaM Expr)) :=
            valueArgs.toArray.map (fun va => (`x, fun _ => inferType va))
          withLocalDeclsD decls fun hxs => do
            let mut subst := env.subst
            for j in [0:hxs.size] do
              subst := (hxs[j]!.fvarId!, ← projHList hargs j) :: subst
            let mut fullArgs := fArgs
            for j in [0:valuePos.size] do
              fullArgs := fullArgs.set! (valuePos[j]!) hxs[j]!
            let env' := { env with subst, inBody := true }
            let bodyExp ← walkProg env' Op (cValInst.beta fullArgs) (env.mkRet Op ·)
            mkLambdaFVars #[hargs] bodyExp
        env.defs.modify (·.push { name := cName, asList, retTp, bodyLam })
      -- a throwaway function-name suffices: the discovery pass's expression is discarded
      some <$> emit (← mkFreshExprMVar (mkApp2 env.F asList retTp))

  /-- Emit a `call cf args k`, binding the result atom for the continuation. -/
  private partial def Env.emitCall (env : Env) (Op cf asList retTp hl : Expr)
      (k : Expr → MetaM Expr) : MetaM Expr := do
    let contLam ← withLocalDeclD `r (mkApp env.V retTp) fun vr => do mkLambdaFVars #[vr] (← k vr)
    mkAppOptM ``Exp.call #[Op, env.F, env.V, none, asList, retTp, cf, hl, contLam]
end

/-! ## Bridging the run-realm and the denote-realm

`reflect%` denotes a *proof-erased* primitive like `vecGet` to a *total* host operation
(`getElem!`), which is **not** definitionally the host's proof-carrying operation (`v[i]'h`) — so
the soundness proof is no longer `rfl`.  `bridgeErase` rebuilds the host term, rewriting each such
operation into the total form the AST denotes to, and returns the equality proof *inductively* as
it goes: a per-operation **bridge** lemma at the erased node (here `getElem!_pos`), and plain
congruence (`congr`/`congrFun`/`funext`) everywhere else.  It returns `none` when nothing is
rewritten (then `denote g` is *definitionally* the host term and the proof is `rfl`).

This is generic in the term, not the AST walk: each new proof-erased primitive adds one
`match_expr` arm with its bridge lemma; the congruence machinery is shared. -/

/-- `f a₁ … aₙ = f b₁ … bₙ` from the *last two* argument-equalities `hx : aₙ₋₁ = bₙ₋₁`,
    `hy : aₙ = bₙ` (the earlier arguments held fixed). -/
private def mkBinCongr (a hx hy : Expr) : MetaM Expr := do
  let args := a.getAppArgs
  let f := mkAppN a.getAppFn (args.extract 0 (args.size - 2))
  mkCongr (← mkCongrArg f hx) hy

/-- Rebuild `a`, rewriting each proof-erased primitive into the total operation its AST node
    denotes to, returning `some (erased, proof : a = erased)`, or `none` if `a` is unchanged. -/
private partial def bridgeErase (a : Expr) : MetaM (Option (Expr × Expr)) := do
  let a := a.consumeMData
  match_expr a with
  | getElem _ idxTy _ _ _ v idx h =>
    -- the bridge: `v[i]  =  v[i.val]!`, with the dropped bound supplied here — `h` for a `Nat`
    -- index, `i.isLt` for a `Fin n` one — then erase inside the vector/index and re-congruence.
    let (natIdx, boundPf) ← match_expr idxTy with
      | Nat   => pure (idx, h)
      | Fin _ => pure ((← mkAppM ``Fin.val #[idx]), (← mkAppM ``Fin.isLt #[idx]))
      | _     => throwError "bridgeErase: a vector index must be `Nat` or `Fin _`{indentExpr idxTy}"
    let bridge ← mkEqSymm (← mkAppM ``getElem!_pos #[v, natIdx, boundPf])
    let ev? ← bridgeErase v
    let ei? ← bridgeErase natIdx
    match ev?, ei? with
    | none, none => return some (← mkAppM ``getElem! #[v, natIdx], bridge)
    | _, _ =>
      let (ev, pv) := (ev?.getD (v, ← mkEqRefl v))
      let (ei, pi) := (ei?.getD (natIdx, ← mkEqRefl natIdx))
      let congr ← mkBinCongr (← mkAppM ``getElem! #[v, natIdx]) pv pi
      return some (← mkAppM ``getElem! #[ev, ei], ← mkEqTrans bridge congr)
  | _ =>
    if let .lam n ty _ bi := a then
      -- go under the binder; `funext` lifts the body equality to the lambda
      withLocalDecl n bi ty fun x => do
        match ← bridgeErase (a.beta #[x]) with
        | none          => return none
        | some (eb, pb) =>
          return some (← mkLambdaFVars #[x] eb, ← mkAppM ``funext #[← mkLambdaFVars #[x] pb])
    else if a.isApp then
      -- congruence over the application's arguments (head held fixed)
      let f := a.getAppFn
      let args := a.getAppArgs
      let mut erasedArgs : Array Expr := #[]
      let mut proofs : Array (Option Expr) := #[]
      let mut changed := false
      for arg in args do
        match ← bridgeErase arg with
        | some (e, p) => changed := true; erasedArgs := erasedArgs.push e; proofs := proofs.push (some p)
        | none        => erasedArgs := erasedArgs.push arg; proofs := proofs.push none
      if !changed then return none
      let mut acc ← mkEqRefl f
      for i in [0:args.size] do
        acc ← match proofs[i]! with
              | some p => mkCongr acc p
              | none   => mkCongrFun acc args[i]!
      return some (mkAppN f erasedArgs, acc)
    else
      return none

elab "reflect% " t:term : term => do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  -- Telescope the *type* (so this also works when `e` is a bare constant, not a
  -- literal `fun`), then apply `e` to the introduced arguments.
  forallTelescope (← inferType e) fun args codom => do
    let bty ← whnf codom
    let_expr Free F τ := bty
      | throwError "reflect%: the body must have type `Free F τ`, got{indentExpr bty}"
    let_expr Effect Op := F
      | throwError "reflect%: the functor must be `Effect Op`, got{indentExpr F}"
    -- the result type must be a supported object type (early, clear error)
    let _ ← reifyTpOrThrow τ
    -- `main`'s argument types must all be monomorphic (reify to `Tp`) and non-dependent: no
    -- argument may be a *type parameter* (used in a later argument's or the result's type).
    for i in [0:args.size] do
      if τ.containsFVar args[i]!.fvarId! then
        throwError "reflect%: `main`'s result type may not depend on its arguments"
      for j in [i+1:args.size] do
        if (← inferType args[j]!).containsFVar args[i]!.fvarId! then
          throwError "reflect%: `main` may not take a type-parameter argument\
                      {indentExpr (← inferType args[i]!)}"
    let mut mainArgTps : Array Expr := #[]
    for a in args do
      mainArgTps := mainArgTps.push (← reifyTpOrThrow (← inferType a))
    let mainArgsList ← mkListLit (.const ``Tp []) mainArgTps.toList
    -- Build the program against abstract `F : List Tp → Tp → Type 1` and `V : Tp → Type`.
    let tyTy := mkSort (.succ .zero)
    let tp := (.const ``Tp [] : Expr)
    let fTy ← mkArrow (mkApp (.const ``List [.zero]) tp) (← mkArrow tp (mkSort (.succ (.succ .zero))))
    withLocalDeclD `F fTy fun F => do
    withLocalDeclD `V (← mkArrow tp tyTy) fun V => do
      let defs ← IO.mkRef (#[] : Array DefEntry)
      let retK := fun (atom : Expr) => mkAppOptM ``Exp.ret #[Op, F, V, none, atom]
      let topBody := (← unfoldDefinition? (e.beta args)).getD (e.beta args)
      let hlistTy ← mkAppM ``HList #[V, mainArgsList]
      -- Walk `main` under an argument tuple `hargs`, substituting each host argument for its
      -- atom; `resolved` selects discovery (`none`) vs build (`some`) pass.
      let walkMain (resolved : Option (Array (DefEntry × Expr))) (hargs : Expr) : MetaM Expr := do
        let mut subst : List (FVarId × Expr) := []
        for i in [0:args.size] do
          subst := (args[i]!.fvarId!, ← projHList hargs i) :: subst
        walkProg { F := F, V := V, subst := subst, defs := defs, resolved := resolved } Op topBody retK
      -- Pass 1 (discovery): collect the function spills (their bodies); discard `main`.
      let _ ← withLocalDeclD `args hlistTy fun h => walkMain none h
      let entries ← defs.get
      -- Pass 2 (build): bind a name per spill, rebuild `main`, assemble the `Prog` with the
      -- definitions pulled out in front of `main` (definitions in discovery order).
      let prog ← withLocalDeclsD (entries.map fun d => (`f, fun _ => pure (mkApp2 F d.asList d.retTp)))
        fun cfs => do
          let resolved := entries.zip cfs
          let mainLam ← withLocalDeclD `args hlistTy fun h => do
            mkLambdaFVars #[h] (← walkMain (some resolved) h)
          let mut prog ← mkAppOptM ``Prog.main #[Op, F, V, mainArgsList, none, mainLam]
          for j in [0:entries.size] do
            let (d, cf) := resolved[entries.size - 1 - j]!
            prog ← mkAppOptM ``Prog.def_
              #[Op, F, V, mainArgsList, none, d.asList, d.retTp, d.bodyLam, ← mkLambdaFVars #[cf] prog]
          pure prog
      -- g := fun F V => prog   (`g.1` is `Closed Op mainArgs τ̂`)
      let g ← mkLambdaFVars #[F, V] prog
      let gTy ← inferType g
      let kf := mkApp (.const ``KleisliF []) Op
      -- the original arguments as an `HList Tp.denote mainArgs`, for the soundness statement
      let mut argHList ← mkAppOptM ``HList.nil #[none, denoteV]
      for (a, t) in (args.zip mainArgTps).reverse do
        argHList ← mkAppOptM ``HList.cons #[none, denoteV, t, none, a, argHList]
      -- predicate  fun g => ∀ args, denoteProg (g (KleisliF Op) Tp.denote) ⟨args…⟩ = e args
      let pred ← withLocalDeclD `g gTy fun gv => do
        let lhs ← mkAppOptM ``denoteProg #[Op, none, none, mkAppN gv #[kf, denoteV], argHList]
        let eq ← mkEq lhs (e.beta args)
        mkLambdaFVars #[gv] (← mkForallFVars args eq)
      -- proof  fun args => …   The denotation `denoteProg (g KleisliF Tp.denote) ⟨args…⟩` is
      -- *definitionally* the host term with every proof-erased primitive replaced by its total
      -- form; `bridgeErase` reconstructs that replacement on the host side with a proof, so the
      -- soundness proof is that bridge (or `rfl` when nothing is erased).
      let dp ← mkAppOptM ``denoteProg #[Op, none, none, mkAppN g #[kf, denoteV], argHList]
      let prf ← mkLambdaFVars args (← do
        match ← bridgeErase (e.beta args) with
        | none        => mkEqRefl dp                        -- denote g ≡ e args : `rfl`
        | some (_, p) => mkEqSymm p)                        -- p : e args = erased ≡ dp
      mkAppOptM ``Subtype.mk #[gTy, pred, g, prf]

end Freigen
