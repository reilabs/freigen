import Freigen.Ast
import Freigen.Free
import Freigen.ITree
import Freigen.Reflect.Sound
/-! ## The `reflect%` reflector — value arm

Reflects a `Free Op SOp α` program (which may call top-level helper functions) into a `Prog`: pure
computation is A-normalised into `un`/`bin`/`lit`; effects/scoped blocks pass through; **calls to
helper functions become `call` nodes, monomorphised and spilled as `def_`s** (a two-pass
discovery/build).

Soundness is proved **compositionally** (`pWalk`, below): the reflector walks the source a second time
at the concrete representation and assembles a congruence tree of `sc_*` lemmas mirroring the term —
no `simp`.  A proof-erased get/set inserts exactly the source's own in-bounds proof (`dif_pos h`), so
symbolic indices are sound at any depth. -/

namespace Freigen
open Lean Lean.Meta Lean.Elab.Term

/-- Reify a Lean type into a `Tp` (matching the head *before* `whnf`, so `ZMod n` stays `ZMod n`). -/
partial def reifyTp (T : Expr) : MetaM (Option Expr) := do
  match_expr T with
  | Bool     => return some (.const ``Tp.bool [])
  | Nat      => return some (.const ``Tp.nat [])
  | ZMod n   => return some (mkApp (.const ``Tp.zmod []) n)
  | PUnit    => return some (.const ``Tp.unit [])
  | Unit     => return some (.const ``Tp.unit [])
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
  | Fin n => return some (mkApp (.const ``Tp.fin []) n)
  | _ =>
      if let .forallE _ A B _ := T then
        if B.hasLooseBVars then return none
        let some a ← reifyTp A | return none
        let some b ← reifyTp B | return none
        return some (mkApp2 (.const ``Tp.fn []) a b)
      else match ← unfoldDefinition? T with
        | some T' => reifyTp T'
        | none    => return none

/-- Reify a Lean type into a `Tp`, aborting if unsupported. -/
def reifyTpOrThrow (T : Expr) : MetaM Expr := do
  match ← reifyTp T with
  | some tp => return tp
  | none    => throwError "reflect%: type not expressible as a `Tp`:{indentExpr T}"

/-- `Bin.add`/`Bin.addZ` picking on the (reified) arithmetic result type. -/
def arithOp (natC zmodC : Name) (resTy : Expr) : MetaM (Expr × Expr) := do
  let cTp ← reifyTpOrThrow resTy
  match_expr cTp with
  | Tp.nat    => return (.const natC [], cTp)
  | Tp.zmod n => return (mkApp (.const zmodC []) n, cTp)
  | _         => throwError "reflect%: unsupported arithmetic result type{indentExpr cTp}"

/-- `Un.fst`/`Un.snd` for a value of product type. -/
def prodUn (ctor : Name) (p : Expr) : MetaM Expr := do
  match_expr ← reifyTpOrThrow (← inferType p) with
  | Tp.prod a b => return mkApp2 (.const ctor []) a b
  | _           => throwError "reflect%: projection applied to a non-product{indentExpr p}"

/-- Project the `j`-th element out of an `HList` atom (`head ∘ tailʲ`). -/
def projHList (hargs : Expr) (j : Nat) : MetaM Expr := do
  let mut h := hargs
  for _ in [0:j] do h ← mkAppM ``HList.tail #[h]
  mkAppM ``HList.head #[h]

/-- A discovered (monomorphised) function spill: name, argument object-types, result object-type,
    and the reflected body `HList V as → Code …`. -/
structure DefEntry where
  name    : Name
  asList  : Expr
  retTp   : Expr
  bodyLam : Expr
  deriving Inhabited

/-- The reflection environment: the abstract `Op`/`SOp`/`F`/`V` we build against, a substitution
    from continuation-bound host placeholders to object atoms, the running spill cache, whether we
    are inside a function body (bodies may not call), and — on the build pass — the resolved names. -/
structure Env where
  Op : Expr
  SOp : Expr
  F : Expr
  V : Expr
  subst : List (FVarId × Expr)
  defs : IO.Ref (Array DefEntry)
  /-- Every source definition the reflector unfolds (helpers, smart-constructors, the program itself);
      recorded for the recursion arm's `mrec`-adequacy `simp`.  (The value arm proves compositionally.) -/
  defsUsed : IO.Ref (Array Name)
  inBody : Bool := false
  resolved : Option (Array (DefEntry × Expr)) := none

/-- Emit a `ret` node returning the atom. -/
def Env.mkRet (env : Env) (atom : Expr) : MetaM Expr :=
  mkAppOptM ``Code.ret #[env.Op, env.SOp, env.F, env.V, none, atom]

/-- Bind a host literal `a : αTp.denote` as an atom. -/
def Env.mkLitBind (env : Env) (a αTp : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
  withLocalDeclD `v (mkApp env.V αTp) fun vx => do
    let lam ← mkLambdaFVars #[vx] (← k vx)
    mkAppOptM ``Code.lit #[env.Op, env.SOp, env.F, env.V, αTp, none, a, lam]

/-- Build the argument tuple `HList V [tps]` from already-reflected atoms. -/
def Env.mkArgHList (env : Env) (atoms : List Expr) : MetaM Expr := do
  let mut h ← mkAppOptM ``HList.nil #[none, env.V]
  for a in atoms.reverse do h ← mkAppM ``HList.cons #[a, h]
  pure h

/-- Extract the elements of a `List` literal (`e₀ :: … :: []`). -/
partial def listLitElems : Expr → Option (List Expr)
  | e => match e.getAppFnArgs with
    | (``List.nil, _)            => some []
    | (``List.cons, #[_, x, xs]) => (listLitElems xs).map (x :: ·)
    | _                          => none

/-- Extract elements of a `List`/`Array` literal (`#[…]` = `List.toArray […]`). -/
def seqLitElems (e : Expr) : Option (List Expr) :=
  match e.getAppFnArgs with
  | (``List.toArray, #[_, lst]) => listLitElems lst
  | _                           => listLitElems e

/-- Build a `Vector (V a) n` atom-vector from element atoms (`⟨#[atoms], rfl⟩`). -/
def mkVecOfAtoms (V aTp nExpr : Expr) (atoms : List Expr) : MetaM Expr := do
  let elemTy := mkApp V aTp
  let arrExpr ← mkAppM ``List.toArray #[← mkListLit elemTy atoms]
  let proof ← mkExpectedTypeHint (← mkEqRefl nExpr) (← mkEq (← mkAppM ``Array.size #[arrExpr]) nExpr)
  mkAppOptM ``Vector.mk #[elemTy, nExpr, arrExpr, proof]

/-- Extract a `Nat` literal, seeing through `OfNat.ofNat`. -/
def natLitOf (e : Expr) : Option Nat :=
  e.nat? <|> (match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_, n, _]) => n.nat?
    | _                          => none)

/-- The `Fin n` literal `⟨k, by decide⟩`. -/
def mkFinLit (nExpr : Expr) (k : Nat) : MetaM Expr := do
  mkAppOptM ``Fin.mk #[nExpr, mkNatLit k, ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit k, nExpr])]

/-- Normalise a collection index to `(Nat-index, optional in-bounds proof)`: a `Fin n` index becomes
    `i.val` with `i.isLt`; a `Nat` index passes through unchanged. -/
def finIndexToNat (i : Expr) : MetaM (Expr × Option Expr) := do
  match_expr ← whnf (← inferType i) with
  | Fin _ => return (← mkAppM ``Fin.val #[i], some (← mkAppM ``Fin.isLt #[i]))
  | _     => return (i, none)

/-- Emit a `call cf args k`, binding the result atom for the continuation. -/
def Env.emitCall (env : Env) (cf asList retTp hl : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
  let contLam ← withLocalDeclD `r (mkApp env.V retTp) fun vr => do mkLambdaFVars #[vr] (← k vr)
  mkAppOptM ``Code.call #[env.Op, env.SOp, env.F, env.V, none, asList, retTp, cf, hl, contLam]

mutual
  /-- Reflect a *pure* host value into a `Code` atom, A-normalising arithmetic into `un`/`bin`/`lit`
      chains, then feed the atom to `k`. -/
  partial def Env.reflectAtom (env : Env) (a : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
    let a ← instantiateMVars a
    if let .fvar fid := a then
      if let some atom := env.subst.lookup fid then return ← k atom
    if !(a.hasAnyFVar fun fid => (env.subst.lookup fid).isSome) then
      return ← env.mkLitBind a (← reifyTpOrThrow (← inferType a)) k
    match_expr a with
    | HMul.hMul _ _ _ _ x y => let (o,c) ← arithOp ``Bin.mul ``Bin.mulZ (← inferType a); env.reflectBin o c x y k
    | HAdd.hAdd _ _ _ _ x y => let (o,c) ← arithOp ``Bin.add ``Bin.addZ (← inferType a); env.reflectBin o c x y k
    | HSub.hSub _ _ _ _ x y => let (o,c) ← arithOp ``Bin.sub ``Bin.subZ (← inferType a); env.reflectBin o c x y k
    | HPow.hPow _ _ _ _ x y => env.reflectBin (.const ``Bin.pow []) (.const ``Tp.nat []) x y k
    | BEq.beq _ _ x y       => env.reflectBin (.const ``Bin.eq []) (.const ``Tp.bool []) x y k
    | Bool.and x y          => env.reflectBin (.const ``Bin.and []) (.const ``Tp.bool []) x y k
    | Bool.or  x y          => env.reflectBin (.const ``Bin.or []) (.const ``Tp.bool []) x y k
    | Bool.not x            => env.reflectUn (.const ``Un.not []) (.const ``Tp.bool []) x k
    | Prod.mk _ _ x y =>
        let aTp ← reifyTpOrThrow (← inferType x); let bTp ← reifyTpOrThrow (← inferType y)
        env.reflectBin (mkApp2 (.const ``Bin.pair []) aTp bTp) (mkApp2 (.const ``Tp.prod []) aTp bTp) x y k
    | Prod.fst _ _ p => env.reflectUn (← prodUn ``Un.fst p) (← reifyTpOrThrow (← inferType a)) p k
    | Prod.snd _ _ p => env.reflectUn (← prodUn ``Un.snd p) (← reifyTpOrThrow (← inferType a)) p k
    | Sum.inl A B x =>
        let aTp ← reifyTpOrThrow A; let bTp ← reifyTpOrThrow B
        env.reflectUn (mkApp2 (.const ``Un.inl []) aTp bTp) (mkApp2 (.const ``Tp.sum []) aTp bTp) x k
    | Sum.inr A B x =>
        let aTp ← reifyTpOrThrow A; let bTp ← reifyTpOrThrow B
        env.reflectUn (mkApp2 (.const ``Un.inr []) aTp bTp) (mkApp2 (.const ``Tp.sum []) aTp bTp) x k
    | GetElem.getElem _ _ _ _ _ coll i _ =>
        -- `coll[i]` (with the *source* in-bounds proof, which the erased node drops): a `vget`/`aget`.
        let (natIdx, _) ← finIndexToNat i          -- a `Fin` index becomes `i.val`
        match_expr ← reifyTpOrThrow (← inferType coll) with
        | Tp.vec aTp nExpr => env.reflectGet ``Code.vget aTp (some nExpr) coll natIdx k
        | Tp.array aTp     => env.reflectGet ``Code.aget aTp none coll natIdx k
        | _ => throwError "reflect%: get on a non-collection value{indentExpr coll}"
    | Vector.ofFn nExpr elemTy f =>
        -- `Vector.ofFn f` : expand over the `n` `Fin` indices into a `#v[f 0, …, f (n-1)]`.
        let some n := natLitOf nExpr <|> natLitOf (← whnf nExpr)
          | throwError "reflect%: `Vector.ofFn` non-literal length: {nExpr} (ctor {nExpr.ctorName}, whnf {(← whnf nExpr).ctorName})"
        let aTp ← reifyTpOrThrow elemTy
        let elems ← (List.range n).mapM (fun kk => do pure (f.beta #[← mkFinLit nExpr kk]))
        env.reflectVec aTp nExpr elems k
    | Vector.set _ _ coll i x _ =>
        match_expr ← reifyTpOrThrow (← inferType coll) with
        | Tp.vec aTp nExpr => env.reflectSet ``Code.vset aTp (some nExpr) coll i x k
        | _ => throwError "reflect%: `Vector.set` on a non-vector{indentExpr coll}"
    | Array.set _ coll i x _ =>
        match_expr ← reifyTpOrThrow (← inferType coll) with
        | Tp.array aTp => env.reflectSet ``Code.aset aTp none coll i x k
        | _ => throwError "reflect%: `Array.set` on a non-array{indentExpr coll}"
    | Vector.mk _ nExpr arr _ =>
        match_expr ← reifyTpOrThrow (← inferType a) with
        -- a list literal is a construction; a runtime `arr` is an `array → vec` *cast* (`⟨arr, h⟩`).
        | Tp.vec aTp _ =>
            match seqLitElems arr with
            | some elems => env.reflectVec aTp nExpr elems k
            | none       => env.reflectCast ``Code.arrToVec (some aTp) nExpr arr k
        | _ => throwError "reflect%: `Vector.mk` at a non-vector type{indentExpr a}"
    | List.toArray _ lst =>
        let some elems := seqLitElems lst | throwError "reflect%: array not built from a list literal{indentExpr a}"
        match_expr ← reifyTpOrThrow (← inferType a) with
        | Tp.array aTp => env.reflectArr aTp elems k
        | _ => throwError "reflect%: array literal at a non-array type{indentExpr a}"
    | Fin.mk nExpr m _ => env.reflectCast ``Code.natToFin none nExpr m k     -- `⟨m, h⟩ : Fin n` cast
    | Vector.toArray A nExpr v =>                                            -- total downcast `v.toArray`
        let aTp ← reifyTpOrThrow A
        env.reflectUn (mkApp2 (.const ``Un.toArray []) aTp nExpr) (mkApp (.const ``Tp.array []) aTp) v k
    | Fin.val nExpr i =>                                                     -- total downcast `i.val`
        env.reflectUn (mkApp (.const ``Un.finVal []) nExpr) (.const ``Tp.nat []) i k
    | _ => throwError "reflect%: cannot reflect operand (not an atom or supported primitive):{indentExpr a}"

  /-- Reflect a **vector construction** `#v[e₀,…]`: reflect the elements, emit a `vec` node. -/
  partial def Env.reflectVec (env : Env) (aTp nExpr : Expr) (elems : List Expr) (k : Expr → MetaM Expr) : MetaM Expr :=
    env.reflectArgList elems fun atoms => do
      let vecVal ← mkVecOfAtoms env.V aTp nExpr atoms
      withLocalDeclD `v (mkApp env.V (mkApp2 (.const ``Tp.vec []) aTp nExpr)) fun vv => do
        let lam ← mkLambdaFVars #[vv] (← k vv)
        mkAppOptM ``Code.vec #[env.Op, env.SOp, env.F, env.V, none, aTp, nExpr, vecVal, lam]

  /-- Reflect an **array construction** `#[e₀,…]`: reflect the elements, emit an `arr` node. -/
  partial def Env.reflectArr (env : Env) (aTp : Expr) (elems : List Expr) (k : Expr → MetaM Expr) : MetaM Expr :=
    env.reflectArgList elems fun atoms => do
      let lst ← mkListLit (mkApp env.V aTp) atoms
      withLocalDeclD `v (mkApp env.V (mkApp (.const ``Tp.array []) aTp)) fun vv => do
        let lam ← mkLambdaFVars #[vv] (← k vv)
        mkAppOptM ``Code.arr #[env.Op, env.SOp, env.F, env.V, none, aTp, lst, lam]

  /-- Reflect a proof-erased **upcast** node (`arrToVec`/`natToFin`): reflect the operand, emit the
      cast.  `aTpOpt = some elemTp` for `array → vec` (result `vec elemTp n`), `none` for `nat → fin`
      (result `fin n`). -/
  partial def Env.reflectCast (env : Env) (ctor : Name) (aTpOpt : Option Expr) (nExpr operand : Expr)
      (k : Expr → MetaM Expr) : MetaM Expr :=
    env.reflectAtom operand fun oa => do
      let resTp := match aTpOpt with
        | some aTp => mkApp2 (.const ``Tp.vec []) aTp nExpr
        | none     => mkApp (.const ``Tp.fin []) nExpr
      withLocalDeclD `v (mkApp env.V resTp) fun vv => do
        let lam ← mkLambdaFVars #[vv] (← k vv)
        match aTpOpt with
        | some aTp => mkAppOptM ctor #[env.Op, env.SOp, env.F, env.V, none, aTp, nExpr, oa, lam]
        | none     => mkAppOptM ctor #[env.Op, env.SOp, env.F, env.V, none, nExpr, oa, lam]

  /-- Reflect a binary primitive: reflect both operands to atoms, emit a `bin` node. -/
  partial def Env.reflectBin (env : Env) (binOp cTp x y : Expr) (k : Expr → MetaM Expr) : MetaM Expr :=
    env.reflectAtom x fun ax =>
    env.reflectAtom y fun ay =>
    withLocalDeclD `v (mkApp env.V cTp) fun vc => do
      let lam ← mkLambdaFVars #[vc] (← k vc)
      mkAppOptM ``Code.bin #[env.Op, env.SOp, env.F, env.V, none, none, none, none, binOp, ax, ay, lam]

  /-- Reflect a unary primitive: reflect the operand to an atom, emit a `un` node. -/
  partial def Env.reflectUn (env : Env) (unOp cTp x : Expr) (k : Expr → MetaM Expr) : MetaM Expr :=
    env.reflectAtom x fun ax =>
    withLocalDeclD `v (mkApp env.V cTp) fun vc => do
      let lam ← mkLambdaFVars #[vc] (← k vc)
      mkAppOptM ``Code.un #[env.Op, env.SOp, env.F, env.V, none, none, none, unOp, ax, lam]

  /-- Reflect a proof-erased collection **get** (`vget`/`aget`): reflect collection + index to atoms,
      emit the node binding the element atom for the continuation.  `nExpr` is the vector length
      (`some`) or `none` for an array. -/
  partial def Env.reflectGet (env : Env) (ctor : Name) (aTp : Expr) (nExpr : Option Expr)
      (coll idx : Expr) (k : Expr → MetaM Expr) : MetaM Expr :=
    env.reflectAtom coll fun ac =>
    env.reflectAtom idx fun ai =>
    withLocalDeclD `v (mkApp env.V aTp) fun vc => do
      let lam ← mkLambdaFVars #[vc] (← k vc)
      match nExpr with
      | some n => mkAppOptM ctor #[env.Op, env.SOp, env.F, env.V, none, aTp, n, ac, ai, lam]
      | none   => mkAppOptM ctor #[env.Op, env.SOp, env.F, env.V, none, aTp, ac, ai, lam]

  /-- Reflect a proof-erased collection **set** (`vset`/`aset`): reflect collection, index and value
      to atoms, emit the node binding the *updated collection* atom for the continuation. -/
  partial def Env.reflectSet (env : Env) (ctor : Name) (aTp : Expr) (nExpr : Option Expr)
      (coll idx x : Expr) (k : Expr → MetaM Expr) : MetaM Expr :=
    env.reflectAtom coll fun ac =>
    env.reflectAtom idx fun ai =>
    env.reflectAtom x fun ax => do
      let collTp := match nExpr with
        | some n => mkApp2 (.const ``Tp.vec []) aTp n
        | none   => mkApp (.const ``Tp.array []) aTp
      withLocalDeclD `v (mkApp env.V collTp) fun vc => do
        let lam ← mkLambdaFVars #[vc] (← k vc)
        match nExpr with
        | some n => mkAppOptM ctor #[env.Op, env.SOp, env.F, env.V, none, aTp, n, ac, ai, ax, lam]
        | none   => mkAppOptM ctor #[env.Op, env.SOp, env.F, env.V, none, aTp, ac, ai, ax, lam]

  /-- Reflect a list of argument values into their atoms. -/
  partial def Env.reflectArgList (env : Env) : List Expr → (List Expr → MetaM Expr) → MetaM Expr
    | [],      k => k []
    | a :: as, k => env.reflectAtom a (fun atom => env.reflectArgList as (fun atoms => k (atom :: atoms)))

  /-- Reflect a `Free Op SOp _` computation into a `Code`; `k` consumes the result atom. -/
  partial def Env.walkProg (env : Env) (e : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
    let e := e.consumeMData.headBeta
    if let .letE _ _ v b _ := e then return ← env.walkProg (b.instantiate1 v) k
    match_expr e with
    | Free.pure _ _ _ a       => env.reflectAtom a k
    | Pure.pure _ _ _ a        => env.reflectAtom a k
    | Bind.bind _ _ _ _ x f    => env.walkBind x f k
    | Free.bind _ _ _ _ x f   => env.walkBind x f k
    | cond _ c t e             => env.walkIte c t e k
    | Free.op _ _ _ I R o i cont =>
        env.reflectAtom i (fun ia => env.walkOp I R o ia cont k)
    | Free.hop _ _ _ β s b cont => env.walkScope β s b cont k
    | _ =>
        match ← env.tryCall e k with
        | some prog => pure prog
        | none => match ← unfoldDefinition? e with
          | some e' =>
              if let some n := e.getAppFn.constName? then env.defsUsed.modify (·.push n)
              env.walkProg e' k
          | none    => throwError "reflect%: don't know how to reflect computation{indentExpr e}"

  /-- Reflect a `bind x f`; a pure `x` is inlined via left-identity. -/
  partial def Env.walkBind (env : Env) (x f : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
    match_expr x.consumeMData.headBeta with
    | Free.pure _ _ _ a => env.walkProg (f.beta #[a]) k
    | Pure.pure _ _ _ a  => env.walkProg (f.beta #[a]) k
    | _                  => env.walkProg x (fun xa => env.walkBindCont f xa k)

  /-- Continue a `bind`: apply the binder to a host placeholder rewritten to the bound atom. -/
  partial def Env.walkBindCont (env : Env) (f xa : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
    let .forallE _ X _ _ := (← whnf (← inferType f))
      | throwError "reflect%: expected a continuation function{indentExpr f}"
    withLocalDeclD `h X fun hx =>
      { env with subst := (hx.fvarId!, xa) :: env.subst }.walkProg (f.beta #[hx]) k

  /-- Emit an `op` node. -/
  partial def Env.walkOp (env : Env) (I R o ia cont : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
    let ITp ← reifyTpOrThrow I
    let RTp ← reifyTpOrThrow R
    let .forallE _ Rt _ _ := (← whnf (← inferType cont))
      | throwError "reflect%: expected an op continuation{indentExpr cont}"
    withLocalDeclD `v (mkApp env.V RTp) fun vx =>
    withLocalDeclD `h Rt fun hx => do
      let env' := { env with subst := (hx.fvarId!, vx) :: env.subst }
      let lam ← mkLambdaFVars #[vx] (← env'.walkProg (cont.beta #[hx]) k)
      mkAppOptM ``Code.op #[env.Op, env.SOp, env.F, env.V, none, ITp, RTp, o, ia, lam]

  /-- Emit a `scope` node: reflect the block into a `Code` (ending in `ret`), then the tail. -/
  partial def Env.walkScope (env : Env) (β s b cont : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
    let βTp ← reifyTpOrThrow β
    let blockCode ← env.walkProg b (env.mkRet ·)
    let .forallE _ Xt _ _ := (← whnf (← inferType cont))
      | throwError "reflect%: expected a scope continuation{indentExpr cont}"
    withLocalDeclD `v (mkApp env.V βTp) fun vx =>
    withLocalDeclD `h Xt fun hx => do
      let env' := { env with subst := (hx.fvarId!, vx) :: env.subst }
      let lam ← mkLambdaFVars #[vx] (← env'.walkProg (cont.beta #[hx]) k)
      mkAppOptM ``Code.scope #[env.Op, env.SOp, env.F, env.V, none, βTp, s, blockCode, lam]

  /-- Emit an `ite`: reflect the scrutinee atom, walk both branches with the same continuation. -/
  partial def Env.walkIte (env : Env) (c t e : Expr) (k : Expr → MetaM Expr) : MetaM Expr :=
    env.reflectAtom c fun ca => do
      let t' ← env.walkProg t k
      let e' ← env.walkProg e k
      mkAppOptM ``Code.ite #[env.Op, env.SOp, env.F, env.V, none, ca, t', e']

  /-- Try to reflect `e` as a **call** to a top-level helper function: classify binders into type
      parameters vs value arguments, monomorphise on `(name, arg-tps, ret-tp)`, spill the specialised
      body as a `def_` (discovery pass) or emit a `call` to its resolved name (build pass). -/
  partial def Env.tryCall (env : Env) (e : Expr) (k : Expr → MetaM Expr) : MetaM (Option Expr) := do
    if env.inBody then return none
    let fn := e.getAppFn
    let some cName := fn.constName? | return none
    let some ci := (← getEnv).find? cName | return none
    let some cVal := ci.value? | return none
    let fArgs := e.getAppArgs
    let cValInst := cVal.instantiateLevelParams ci.levelParams fn.constLevels!
    match_expr ← whnf (cValInst.beta fArgs) with
    | Free.op _ _ _ _ _ _ _ _ => return none      -- effect smart-constructors (→ `op`) inline
    | Free.hop _ _ _ _ _ _ _   => return none      -- scoped constructs (→ `scope`) inline
    | _ => pure ()
    let valuePos ← forallTelescope (← inferType fn) fun xs cod => do
      let mut vps : Array Nat := #[]
      for i in [0:xs.size] do
        let mut dep := cod.containsFVar xs[i]!.fvarId!
        for j in [i+1:xs.size] do
          if (← inferType xs[j]!).containsFVar xs[i]!.fvarId! then dep := true
        unless dep do vps := vps.push i
      pure vps
    if valuePos.size == 0 then return none
    env.defsUsed.modify (·.push cName)     -- the helper is `call`-spilled; unfold it on the source side
    let valueArgs := valuePos.toList.map (fArgs[·]!)
    let mut argTps : Array Expr := #[]
    for va in valueArgs do
      let some t ← reifyTp (← inferType va) | return none
      argTps := argTps.push t
    let asList ← mkListLit (.const ``Tp []) argTps.toList
    let some retTp ← (match_expr (← whnf (← inferType e)) with
                        | Free _ _ R => reifyTp R | _ => pure none) | return none
    let sigMatches (d : DefEntry) : MetaM Bool :=
      return d.name == cName && (← isDefEq d.asList asList) && (← isDefEq d.retTp retTp)
    let emit (cf : Expr) : MetaM Expr :=
      env.reflectArgList valueArgs (fun atoms => do
        env.emitCall cf asList retTp (← env.mkArgHList atoms) k)
    match env.resolved with
    | some resolved =>
        let some (_, cf) ← resolved.findM? (fun de => sigMatches de.1) | return none
        some <$> emit cf
    | none =>
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
              mkLambdaFVars #[hargs] (← env'.walkProg (cValInst.beta fullArgs) (env.mkRet ·))
          env.defs.modify (·.push { name := cName, asList, retTp, bodyLam })
        some <$> emit (← mkFreshExprMVar (mkApp2 env.F asList retTp))
end

/-! ## The compositional soundness proof (`pWalk`)

Instead of discharging soundness with a global `simp`, the reflector **builds the proof structurally**,
mirroring the source term.  `pWalk` walks the source again at the *concrete* representation
(`V := Tp.denote`, `F := KC Op`) and, at every node, emits the equation of the invariant

```
denote code = bind (ofFree e) Kf        -- (★)   Kf = the reflected continuation's denotation
```

by applying that node's congruence lemma (`sc_op`, `sc_bind`, …) to the equations of the sub-terms.
Every non-`get`/`set` atom step is *definitional* (`denote (Code.bin …) = denote (k …)` is `rfl`), so
a get/set contributes the only real step: `sc_vget … h_src` = `dif_pos h_src`, the **source's own**
in-bounds proof taken straight from the term.  No `simp`, no decidability, no hypothesis reachability
— the proof is a congruence tree over the source, valid at *any* depth.  The produced `code` is
definitionally the concrete specialisation of the abstract `g`, so the top-level (★) (`k = mkRet`,
`Kf = ret`) *is* `denoteProg (g KC Tp.denote) ⟨args⟩ = ofFree (foo args)`. -/

/-- `denote code` as an `Expr`. -/
private def denoteE (c : Expr) : MetaM Expr := mkAppM ``denote #[c]

/-- A `ret` continuation with the result `Tp` given **explicitly** — needed at `V := Tp.denote`,
    where `α` cannot be recovered from a raw-typed atom by unifying `Tp.denote ?α`. -/
def Env.mkRetT (env : Env) (resTp : Expr) : Expr → MetaM Expr := fun atom =>
  mkAppOptM ``Code.ret #[env.Op, env.SOp, env.F, env.V, resTp, atom]

/-- `Kf := fun (r : X) => denote (k r)` — the reflected continuation's denotation. -/
private def mkKf (_V : Expr) (X : Expr) (k : Expr → MetaM Expr) : MetaM Expr :=
  withLocalDeclD `r X fun r => do mkLambdaFVars #[r] (← denoteE (← k r))

/-- Lift a *code-only* continuation into the proof-carrying form, its step being `rfl`
    (`denote (k atom) = denote (k atom)`). -/
private def kRfl (k : Expr → MetaM Expr) : Expr → MetaM (Expr × Expr) := fun atom => do
  let c ← k atom; pure (c, ← mkEqRefl (← denoteE c))

/-- Build `HList V [tps]` from atoms with the `Tp` indices given **explicitly** — at `V := Tp.denote`
    the index can't be recovered from a raw-typed atom. -/
private def mkArgHListT (V : Expr) : List Expr → List Expr → MetaM Expr
  | [],      []      => mkAppOptM ``HList.nil #[none, V]
  | a :: as, t :: ts => do
      let tail ← mkArgHListT V as ts
      mkAppOptM ``HList.cons #[none, V, t, ← mkListLit (.const ``Tp []) ts, a, tail]
  | _, _ => throwError "reflect%: argument/type length mismatch"

/-- The result Lean type `X` of a source `e : Free Op SOp X`. -/
private def freeResult (e : Expr) : MetaM Expr := do
  let_expr Free _ _ X := (← whnf (← inferType e)) | throwError "reflect%: not a `Free`{indentExpr e}"
  pure X

/-- `Eq.trans` tolerant of a *definitional* mismatch at the shared point: the `denote`-of-a-node steps
    are only defeq (a `Code.bin`/`vget` node reduces to its continuation), so coerce `h2`'s LHS to
    `h1`'s RHS before chaining. -/
private def eqTransD (h1 h2 : Expr) : MetaM Expr := do
  let_expr Eq _ _ b := (← inferType h1) | throwError "reflect%: eqTransD h1 not an Eq"
  let_expr Eq _ _ c := (← inferType h2) | throwError "reflect%: eqTransD h2 not an Eq"
  mkAppM ``Eq.trans #[h1, ← mkExpectedTypeHint h2 (← mkEq b c)]

mutual
  /-- A *pure atom*, at `V := Tp.denote`: build its `Code` (as `reflectAtom`) with the proof
      `denote code = denote-of (k a)`.  The continuation `k` itself returns `(code, proof)`, so proofs
      thread through in one pass; every non-`get`/`set` step is definitional, and a get/set inserts
      exactly `sc_*` (= `dif_pos h_src`, the source's own in-bounds proof).  `resTp` is the overall
      result `Tp` (the sc-lemmas' `α`, unrecoverable through `Tp.denote`). -/
  partial def Env.pAtom (env : Env) (resTp a : Expr) (k : Expr → MetaM (Expr × Expr)) : MetaM (Expr × Expr) := do
    let a ← instantiateMVars a
    if let .fvar fid := a then
      if let some atom := env.subst.lookup fid then return ← k atom
    if !(a.hasAnyFVar fun fid => (env.subst.lookup fid).isSome) then
      -- a closed value: feed it *directly* (no `Code.lit` node — denotationally identical, and it
      -- keeps a literal index/collection literal so a get/set's source proof `h` still fits).
      return ← k a
    match_expr a with
    | HMul.hMul _ _ _ _ x y => let (o,c) ← arithOp ``Bin.mul ``Bin.mulZ (← inferType a); env.pBin resTp a o c x y k
    | HAdd.hAdd _ _ _ _ x y => let (o,c) ← arithOp ``Bin.add ``Bin.addZ (← inferType a); env.pBin resTp a o c x y k
    | HSub.hSub _ _ _ _ x y => let (o,c) ← arithOp ``Bin.sub ``Bin.subZ (← inferType a); env.pBin resTp a o c x y k
    | HPow.hPow _ _ _ _ x y => env.pBin resTp a (.const ``Bin.pow []) (.const ``Tp.nat []) x y k
    | BEq.beq _ _ x y       => env.pBin resTp a (.const ``Bin.eq []) (.const ``Tp.bool []) x y k
    | Bool.and x y          => env.pBin resTp a (.const ``Bin.and []) (.const ``Tp.bool []) x y k
    | Bool.or  x y          => env.pBin resTp a (.const ``Bin.or []) (.const ``Tp.bool []) x y k
    | Bool.not x            => env.pUn resTp a (.const ``Un.not []) (.const ``Tp.bool []) x k
    | Prod.mk _ _ x y =>
        let aTp ← reifyTpOrThrow (← inferType x); let bTp ← reifyTpOrThrow (← inferType y)
        env.pBin resTp a (mkApp2 (.const ``Bin.pair []) aTp bTp) (mkApp2 (.const ``Tp.prod []) aTp bTp) x y k
    | Prod.fst _ _ p => env.pUn resTp a (← prodUn ``Un.fst p) (← reifyTpOrThrow (← inferType a)) p k
    | Prod.snd _ _ p => env.pUn resTp a (← prodUn ``Un.snd p) (← reifyTpOrThrow (← inferType a)) p k
    | Sum.inl A B x =>
        let aTp ← reifyTpOrThrow A; let bTp ← reifyTpOrThrow B
        env.pUn resTp a (mkApp2 (.const ``Un.inl []) aTp bTp) (mkApp2 (.const ``Tp.sum []) aTp bTp) x k
    | Sum.inr A B x =>
        let aTp ← reifyTpOrThrow A; let bTp ← reifyTpOrThrow B
        env.pUn resTp a (mkApp2 (.const ``Un.inr []) aTp bTp) (mkApp2 (.const ``Tp.sum []) aTp bTp) x k
    | GetElem.getElem _ _ _ _ _ coll i h =>
        let (natIdx, finPf) ← finIndexToNat i        -- a `Fin` index becomes `i.val` with `i.isLt`
        let proof := finPf.getD h
        match_expr ← reifyTpOrThrow (← inferType coll) with
        | Tp.vec aTp nExpr => env.pGet resTp a ``Code.vget ``sc_vget aTp (some nExpr) coll natIdx proof k
        | Tp.array aTp     => env.pGet resTp a ``Code.aget ``sc_aget aTp none coll natIdx proof k
        | _ => throwError "reflect%: get on a non-collection value{indentExpr coll}"
    | Vector.ofFn nExpr elemTy f =>
        let some n := natLitOf nExpr <|> natLitOf (← whnf nExpr)
          | throwError "reflect%: `Vector.ofFn` non-literal length{indentExpr nExpr}"
        let aTp ← reifyTpOrThrow elemTy
        let elems ← (List.range n).mapM (fun kk => do pure (f.beta #[← mkFinLit nExpr kk]))
        env.pVec resTp aTp nExpr elems k
    | Vector.set _ _ coll i x h =>
        match_expr ← reifyTpOrThrow (← inferType coll) with
        | Tp.vec aTp nExpr => env.pSet resTp a ``Code.vset ``sc_vset aTp (some nExpr) coll i x h k
        | _ => throwError "reflect%: `Vector.set` on a non-vector{indentExpr coll}"
    | Array.set _ coll i x h =>
        match_expr ← reifyTpOrThrow (← inferType coll) with
        | Tp.array aTp => env.pSet resTp a ``Code.aset ``sc_aset aTp none coll i x h k
        | _ => throwError "reflect%: `Array.set` on a non-array{indentExpr coll}"
    | Vector.mk _ nExpr arr h =>
        match_expr ← reifyTpOrThrow (← inferType a) with
        | Tp.vec aTp _ =>
            match seqLitElems arr with
            | some elems => env.pVec resTp aTp nExpr elems k
            | none       => env.pCast resTp a ``Code.arrToVec ``sc_arrToVec (some aTp) nExpr arr h k
        | _ => throwError "reflect%: `Vector.mk` at a non-vector type{indentExpr a}"
    | List.toArray _ lst =>
        let some elems := seqLitElems lst | throwError "reflect%: array not a list literal{indentExpr a}"
        match_expr ← reifyTpOrThrow (← inferType a) with
        | Tp.array aTp => env.pArr resTp aTp elems k
        | _ => throwError "reflect%: array literal at a non-array type{indentExpr a}"
    | Fin.mk nExpr m h => env.pCast resTp a ``Code.natToFin ``sc_natToFin none nExpr m h k
    | Vector.toArray A nExpr v =>
        let aTp ← reifyTpOrThrow A
        env.pUn resTp a (mkApp2 (.const ``Un.toArray []) aTp nExpr) (mkApp (.const ``Tp.array []) aTp) v k
    | Fin.val nExpr i =>
        env.pUn resTp a (mkApp (.const ``Un.finVal []) nExpr) (.const ``Tp.nat []) i k
    | _ => throwError "reflect%: cannot reflect operand{indentExpr a}"

  /-- Binary primitive: reflect both operands, bind the result as a fresh var `vc` (so the
      continuation reflects against a *variable*, as the abstract walk does), emit the `bin` node, and
      instantiate `vc ↦ Bin.denote o x y` in the continuation's proof (the `bin` step is definitional). -/
  partial def Env.pBin (env : Env) (resTp _a binOp cTp x y : Expr) (k : Expr → MetaM (Expr × Expr)) : MetaM (Expr × Expr) :=
    env.pAtom resTp x fun ax =>
    env.pAtom resTp y fun ay =>
    withLocalDeclD `v (mkApp env.V cTp) fun vc => do
      let (kcode, kproof) ← k vc
      let klam ← mkLambdaFVars #[vc] kcode
      let node ← mkAppOptM ``Code.bin #[env.Op, env.SOp, env.F, env.V, none, none, none, none, binOp, ax, ay, klam]
      pure (node, kproof.replaceFVar vc (← mkAppM ``Bin.denote #[binOp, ax, ay]))

  /-- Unary primitive: as `pBin`, with `vc ↦ Un.denote o x`. -/
  partial def Env.pUn (env : Env) (resTp _a unOp cTp x : Expr) (k : Expr → MetaM (Expr × Expr)) : MetaM (Expr × Expr) :=
    env.pAtom resTp x fun ax =>
    withLocalDeclD `v (mkApp env.V cTp) fun vc => do
      let (kcode, kproof) ← k vc
      let klam ← mkLambdaFVars #[vc] kcode
      let node ← mkAppOptM ``Code.un #[env.Op, env.SOp, env.F, env.V, none, none, none, unOp, ax, klam]
      pure (node, kproof.replaceFVar vc (← mkAppM ``Un.denote #[unOp, ax]))

  /-- Proof-erased **get**: reflect collection + index, bind the element as a fresh var, emit the node,
      and close its `fail` branch with the *source's* proof `h` (`sc_vget`/`sc_aget` = `dif_pos h`),
      instantiating the element var with the source `coll[i]'h` (`elem`). -/
  partial def Env.pGet (env : Env) (resTp elem : Expr) (ctor scLemma : Name) (aTp : Expr) (nExpr : Option Expr)
      (coll idx h : Expr) (k : Expr → MetaM (Expr × Expr)) : MetaM (Expr × Expr) :=
    env.pAtom resTp coll fun ac =>
    env.pAtom resTp idx fun ai =>
    withLocalDeclD `v (mkApp env.V aTp) fun vc => do
      let (kcode, kproof) ← k vc
      let klam ← mkLambdaFVars #[vc] kcode
      let node ← match nExpr with
        | some n => mkAppOptM ctor #[env.Op, env.SOp, env.F, env.V, none, aTp, n, ac, ai, klam]
        | none   => mkAppOptM ctor #[env.Op, env.SOp, env.F, env.V, none, aTp, ac, ai, klam]
      -- the sc-lemma uses the *source* collection `coll` and index `idx` (concrete), not the reflected
      -- atoms `ac`/`ai` (fresh binders for a compound collection or computed index): the bound
      -- `idx < coll.size` then fits `h`, and the enclosing node ties each binder to its source.
      let scStep ← match nExpr with
        | some _ => mkAppOptM scLemma #[env.Op, env.SOp, resTp, aTp, none, coll, idx, klam, h]
        | none   => mkAppOptM scLemma #[env.Op, env.SOp, resTp, aTp, coll, idx, klam, h]
      pure (node, ← eqTransD scStep (kproof.replaceFVar vc elem))

  /-- Proof-erased **set**: as `pGet`, with the value operand and `sc_vset`/`sc_aset`. -/
  partial def Env.pSet (env : Env) (resTp elem : Expr) (ctor scLemma : Name) (aTp : Expr) (nExpr : Option Expr)
      (coll idx x h : Expr) (k : Expr → MetaM (Expr × Expr)) : MetaM (Expr × Expr) :=
    let collTp := match nExpr with
      | some n => mkApp2 (.const ``Tp.vec []) aTp n
      | none   => mkApp (.const ``Tp.array []) aTp
    env.pAtom resTp coll fun ac =>
    env.pAtom resTp idx fun ai =>
    env.pAtom resTp x fun ax =>
    withLocalDeclD `v (mkApp env.V collTp) fun vc => do
      let (kcode, kproof) ← k vc
      let klam ← mkLambdaFVars #[vc] kcode
      let node ← match nExpr with
        | some n => mkAppOptM ctor #[env.Op, env.SOp, env.F, env.V, none, aTp, n, ac, ai, ax, klam]
        | none   => mkAppOptM ctor #[env.Op, env.SOp, env.F, env.V, none, aTp, ac, ai, ax, klam]
      -- as `pGet`: the sc-lemma uses the *source* collection/index/value so the array bound fits `h`.
      let scStep ← match nExpr with
        | some _ => mkAppOptM scLemma #[env.Op, env.SOp, resTp, aTp, none, coll, idx, x, klam, h]
        | none   => mkAppOptM scLemma #[env.Op, env.SOp, resTp, aTp, coll, idx, x, klam, h]
      pure (node, ← eqTransD scStep (kproof.replaceFVar vc elem))

  /-- Proof-erased **upcast** (`arrToVec`/`natToFin`): reflect the operand, emit the cast, and close
      its `fail` branch with the source's proof `h` (`sc_arrToVec`/`sc_natToFin` = `dif_pos h`).
      `elem` is the source `⟨operand, h⟩`; `aTpOpt = some elemTp` for `array→vec`, `none` for `nat→fin`. -/
  partial def Env.pCast (env : Env) (resTp elem : Expr) (ctor scLemma : Name) (aTpOpt : Option Expr)
      (nExpr operand h : Expr) (k : Expr → MetaM (Expr × Expr)) : MetaM (Expr × Expr) :=
    let castTp := match aTpOpt with
      | some aTp => mkApp2 (.const ``Tp.vec []) aTp nExpr
      | none     => mkApp (.const ``Tp.fin []) nExpr
    env.pAtom resTp operand fun oa =>
    withLocalDeclD `v (mkApp env.V castTp) fun vc => do
      let (kcode, kproof) ← k vc
      let klam ← mkLambdaFVars #[vc] kcode
      let node ← match aTpOpt with
        | some aTp => mkAppOptM ctor #[env.Op, env.SOp, env.F, env.V, none, aTp, nExpr, oa, klam]
        | none     => mkAppOptM ctor #[env.Op, env.SOp, env.F, env.V, none, nExpr, oa, klam]
      -- the sc-lemma uses the *source* operand (concrete), not the reflected atom `oa`.
      let scStep ← match aTpOpt with
        | some aTp => mkAppOptM scLemma #[env.Op, env.SOp, resTp, aTp, nExpr, operand, klam, h]
        | none     => mkAppOptM scLemma #[env.Op, env.SOp, resTp, nExpr, operand, klam, h]
      pure (node, ← eqTransD scStep (kproof.replaceFVar vc elem))

  /-- **Vector construction**: reflect the elements, bind the result vector as a fresh var, emit the
      `vec` node, and instantiate the var with the atom-vector in the continuation's proof (the `vec`
      step `denote (Code.vec elems k) = denote (k elems)` is definitional). -/
  partial def Env.pVec (env : Env) (resTp aTp nExpr : Expr) (elems : List Expr)
      (k : Expr → MetaM (Expr × Expr)) : MetaM (Expr × Expr) :=
    env.pAtoms resTp elems fun atoms => do
      let vecVal ← mkVecOfAtoms env.V aTp nExpr atoms
      withLocalDeclD `v (mkApp env.V (mkApp2 (.const ``Tp.vec []) aTp nExpr)) fun vc => do
        let (kcode, kproof) ← k vc
        let klam ← mkLambdaFVars #[vc] kcode
        let node ← mkAppOptM ``Code.vec #[env.Op, env.SOp, env.F, env.V, none, aTp, nExpr, vecVal, klam]
        pure (node, kproof.replaceFVar vc vecVal)

  /-- **Array construction**: as `pVec`, instantiating with `(#[atoms])`. -/
  partial def Env.pArr (env : Env) (resTp aTp : Expr) (elems : List Expr)
      (k : Expr → MetaM (Expr × Expr)) : MetaM (Expr × Expr) :=
    env.pAtoms resTp elems fun atoms => do
      let lst ← mkListLit (mkApp env.V aTp) atoms
      let arrVal ← mkAppM ``List.toArray #[lst]
      withLocalDeclD `v (mkApp env.V (mkApp (.const ``Tp.array []) aTp)) fun vc => do
        let (kcode, kproof) ← k vc
        let klam ← mkLambdaFVars #[vc] kcode
        let node ← mkAppOptM ``Code.arr #[env.Op, env.SOp, env.F, env.V, none, aTp, lst, klam]
        pure (node, kproof.replaceFVar vc arrVal)

  /-- Reflect a list of pure argument values to atoms, threading the proof-carrying continuation. -/
  partial def Env.pAtoms (env : Env) (resTp : Expr) (vals : List Expr)
      (k : List Expr → MetaM (Expr × Expr)) : MetaM (Expr × Expr) := do
    match vals with
    | []      => k []
    | v :: vs => env.pAtom resTp v fun av => env.pAtoms resTp vs (fun atoms => k (av :: atoms))

  /-- Prove a **call** to a helper: build the (concrete) subroutine `cf` and its own (★)-proof, reflect
      the arguments, then `sc_call` — the helper's soundness `hcf : cf args = ofFree (helper args)`
      composes with the caller's continuation. -/
  partial def Env.pTryCall (env : Env) (resTp e : Expr) (k : Expr → MetaM Expr) :
      MetaM (Option (Expr × Expr)) := do
    if env.inBody then return none
    let fn := e.getAppFn
    let some cName := fn.constName? | return none
    let some ci := (← getEnv).find? cName | return none
    let some cVal := ci.value? | return none
    let fArgs := e.getAppArgs
    let cValInst := cVal.instantiateLevelParams ci.levelParams fn.constLevels!
    match_expr ← whnf (cValInst.beta fArgs) with
    | Free.op _ _ _ _ _ _ _ _ => return none
    | Free.hop _ _ _ _ _ _ _   => return none
    | _ => pure ()
    let valuePos ← forallTelescope (← inferType fn) fun xs cod => do
      let mut vps : Array Nat := #[]
      for i in [0:xs.size] do
        let mut dep := cod.containsFVar xs[i]!.fvarId!
        for j in [i+1:xs.size] do
          if (← inferType xs[j]!).containsFVar xs[i]!.fvarId! then dep := true
        unless dep do vps := vps.push i
      pure vps
    if valuePos.size == 0 then return none
    env.defsUsed.modify (·.push cName)
    let valueArgs := valuePos.toList.map (fArgs[·]!)
    let mut argTps : Array Expr := #[]
    for va in valueArgs do
      let some t ← reifyTp (← inferType va) | return none
      argTps := argTps.push t
    let asList ← mkListLit (.const ``Tp []) argTps.toList
    let some retTp ← (match_expr (← whnf (← inferType e)) with
                        | Free _ _ R => reifyTp R | _ => pure none) | return none
    let hlistTy ← mkAppM ``HList #[env.V, asList]
    -- the concrete subroutine `cf` and its parametric (★)-proof `bodyProof : ∀ hargs, cf hargs = ofFree …`.
    -- Walk the body with fresh *identity*-mapped value vars `pvs` (so `pAtom`'s `atom = value`), then
    -- substitute `pvs ↦ projHList hargs` — matching `g`'s spilled `def_` body (which projects `hargs`).
    let (cf, bodyProofLam) ← withLocalDeclD `args hlistTy fun hargs => do
      let decls : Array (Name × (Array Expr → MetaM Expr)) :=
        valueArgs.toArray.map (fun va => (`x, fun _ => inferType va))
      withLocalDeclsD decls fun pvs => do
        let subst := (pvs.toList.map (fun p => (p.fvarId!, p))) ++ env.subst
        let mut fullArgs := fArgs
        for j in [0:valuePos.size] do fullArgs := fullArgs.set! (valuePos[j]!) pvs[j]!
        let env' := { env with subst, inBody := true }
        let (bcode, bproof) ← env'.pTop (cValInst.beta fullArgs) retTp
        let mut projs : Array Expr := #[]
        for j in [0:pvs.size] do projs := projs.push (← projHList hargs j)
        let bcode' := bcode.replaceFVars pvs projs
        let bproof' := bproof.replaceFVars pvs projs
        pure (← mkLambdaFVars #[hargs] (← denoteE bcode'), ← mkLambdaFVars #[hargs] bproof')
    let kcont ← withLocalDeclD `r (mkApp env.V retTp) fun vr => do mkLambdaFVars #[vr] (← k vr)
    let (code, proof) ← env.pAtoms resTp valueArgs fun atoms => do
      let argHList ← mkArgHListT env.V atoms argTps.toList
      let callCode ← env.emitCall cf asList retTp argHList k
      let hcf := bodyProofLam.beta #[argHList]
      -- `m = ofFree (helper applied to *these* atoms)` — matches `hcf`'s RHS; a bin/get argument's
      -- atom is a bound var here, later instantiated to the source value (so `m` becomes `ofFree e`).
      let mut fullArgs := fArgs
      for j in [0:valuePos.size] do fullArgs := fullArgs.set! (valuePos[j]!) atoms.toArray[j]!
      let m ← mkAppM ``ofFree #[cValInst.beta fullArgs]
      let scStep ← mkAppOptM ``sc_call
        #[env.Op, env.SOp, asList, retTp, resTp, cf, argHList, kcont, m, hcf]
      pure (callCode, scStep)
    return some (code, proof)

  /-- Prove a `Free` computation: `(code, proof : denote code = bind (ofFree e) Kf)`.  `resTp` is the
      overall result `Tp` (the sc-lemmas' `α`). -/
  partial def Env.pWalk (env : Env) (resTp e : Expr) (k : Expr → MetaM Expr) : MetaM (Expr × Expr) := do
    let e := e.consumeMData.headBeta
    if let .letE _ _ v b _ := e then return ← env.pWalk resTp (b.instantiate1 v) k
    match_expr e with
    | Free.pure _ _ _ a       => env.pPure resTp a k
    | Pure.pure _ _ _ a       => env.pPure resTp a k
    | Bind.bind _ _ _ _ x f   => env.pBindD resTp x f k
    | Free.bind _ _ _ _ x f   => env.pBindD resTp x f k
    | cond _ c t el           => env.pIte resTp c t el k
    | Free.op _ _ _ I R o i cont => env.pOp resTp I R o i cont k
    | Free.hop _ _ _ β s b cont  => env.pScope resTp β s b cont k
    | _ =>
        match ← env.pTryCall resTp e k with
        | some r => pure r
        | none =>
        match ← unfoldDefinition? e with
        | some e' => env.pWalk resTp e' k
        | none    => throwError "reflect%: pWalk cannot handle{indentExpr e}"

  /-- `pure a`: `pAtom`, then `sc_pure`. -/
  partial def Env.pPure (env : Env) (resTp a : Expr) (k : Expr → MetaM Expr) : MetaM (Expr × Expr) := do
    let (code, pA) ← env.pAtom resTp a (kRfl k)
    let Kf ← mkKf env.V (← inferType a) k
    return (code, ← mkAppOptM ``sc_pure #[env.Op, env.SOp, none, resTp, a, ← denoteE code, Kf, pA])

  /-- `op o i cont`: reflect the input (`pAtom i`), then `sc_op` with the continuation's IH. -/
  partial def Env.pOp (env : Env) (resTp I R o i cont : Expr) (k : Expr → MetaM Expr) : MetaM (Expr × Expr) := do
    let ITp ← reifyTpOrThrow I; let RTp ← reifyTpOrThrow R
    let Xr ← forallTelescope (← inferType cont) fun _ cod => do
      let_expr Free _ _ X := (← whnf cod) | throwError "reflect%: op cont"
      pure X
    let Kf ← mkKf env.V Xr k
    let (kbody, ih) ← withLocalDeclD `r R fun vr => do
      let env' := { env with subst := (vr.fvarId!, vr) :: env.subst }
      let (rcode, rproof) ← env'.pWalk resTp (cont.beta #[vr]) k
      pure (← mkLambdaFVars #[vr] rcode, ← mkLambdaFVars #[vr] rproof)
    let (code, pI) ← env.pAtom resTp i (kRfl fun ia => do
      mkAppOptM ``Code.op #[env.Op, env.SOp, env.F, env.V, none, ITp, RTp, o, ia, kbody])
    let scStep ← mkAppOptM ``sc_op #[env.Op, env.SOp, ITp, RTp, resTp, none, o, i, cont, kbody, Kf, ih]
    return (code, ← eqTransD pI scStep)

  /-- `bind x f`: pure `x` inlines by left-identity; else `sc_bind` composing `x`'s and `f`'s IHs. -/
  partial def Env.pBindD (env : Env) (resTp x f : Expr) (k : Expr → MetaM Expr) : MetaM (Expr × Expr) := do
    match_expr x.consumeMData.headBeta with
    | Free.pure _ _ _ a => env.pWalk resTp (f.beta #[a]) k
    | Pure.pure _ _ _ a => env.pWalk resTp (f.beta #[a]) k
    | _ =>
      let Y ← freeResult x
      let X ← forallTelescope (← inferType f) fun _ cod => do
        let_expr Free _ _ X := (← whnf cod) | throwError "reflect%: bind cont"
        pure X
      let Kf ← mkKf env.V X k
      let (fproofLam) ← withLocalDeclD `r Y fun vr => do
        let env' := { env with subst := (vr.fvarId!, vr) :: env.subst }
        let (_, fp) ← env'.pWalk resTp (f.beta #[vr]) k
        mkLambdaFVars #[vr] fp
      let kInner : Expr → MetaM Expr := fun xa => do
        let env' := if let .fvar fid := xa then { env with subst := (fid, xa) :: env.subst } else env
        Prod.fst <$> env'.pWalk resTp (f.beta #[xa]) k
      let (xcode, xproof) ← env.pWalk resTp x kInner
      -- xproof : denote xcode = bind (ofFree x) (fun r => denote (kInner r))
      let ofx ← mkAppM ``ofFree #[x]
      let hEq ← mkAppM ``funext #[fproofLam]      -- (fun r => denote (kInner r)) = (fun r => bind (ofFree (f r)) Kf)
      let compTy ← inferType (← denoteE xcode)
      let fFun ← withLocalDeclD `kk (← mkArrow Y compTy) fun kk => do
        mkLambdaFVars #[kk] (← mkAppM ``ITree.bind #[ofx, kk])
      let congrStep ← mkAppM ``congrArg #[fFun, hEq]
      let hC ← eqTransD xproof congrStep
      return (xcode, ← mkAppOptM ``sc_bind #[env.Op, env.SOp, none, none, resTp, x, f, Kf, ← denoteE xcode, hC])

  /-- `cond c t e`: reflect the scrutinee, then `sc_cond` with both arms' IHs. -/
  partial def Env.pIte (env : Env) (resTp c t el : Expr) (k : Expr → MetaM Expr) : MetaM (Expr × Expr) := do
    let X ← freeResult t
    let Kf ← mkKf env.V X k
    let (tcode, tproof) ← env.pWalk resTp t k
    let (ecode, eproof) ← env.pWalk resTp el k
    let (code, pC) ← env.pAtom resTp c (kRfl fun ca =>
      mkAppOptM ``Code.ite #[env.Op, env.SOp, env.F, env.V, none, ca, tcode, ecode])
    let scStep ← mkAppOptM ``sc_cond #[env.Op, env.SOp, none, resTp, c, t, el, tcode, ecode, Kf, tproof, eproof]
    return (code, ← eqTransD pC scStep)

  /-- `hop s b cont`: the block runs inline (`sc_top` to `ofFree b`), tail by IH, then `sc_scope`. -/
  partial def Env.pScope (env : Env) (resTp β s b cont : Expr) (k : Expr → MetaM Expr) : MetaM (Expr × Expr) := do
    let βTp ← reifyTpOrThrow β
    let (Bcode, Bproof) ← env.pTop b βTp
    let X ← forallTelescope (← inferType cont) fun _ cod => do
      let_expr Free _ _ X := (← whnf cod) | throwError "reflect%: scope cont"
      pure X
    let Kf ← mkKf env.V X k
    let (kbody, ih) ← withLocalDeclD `r β fun vr => do
      let env' := { env with subst := (vr.fvarId!, vr) :: env.subst }
      let (rc, rp) ← env'.pWalk resTp (cont.beta #[vr]) k
      pure (← mkLambdaFVars #[vr] rc, ← mkLambdaFVars #[vr] rp)
    let code ← mkAppOptM ``Code.scope #[env.Op, env.SOp, env.F, env.V, none, βTp, s, Bcode, kbody]
    return (code, ← mkAppOptM ``sc_scope #[env.Op, env.SOp, βTp, resTp, none, s, b, cont, Bcode, kbody, Kf, Bproof, ih])

  /-- Top-level (`k = mkRet`, `Kf = ret`): `denote code = ofFree e`.  `resTp` is `e`'s result `Tp`. -/
  partial def Env.pTop (env : Env) (e resTp : Expr) : MetaM (Expr × Expr) := do
    let (code, proof) ← env.pWalk resTp e (env.mkRetT resTp)
    let brr ← mkAppM ``ITree.bind_ret_right #[← mkAppM ``ofFree #[e]]
    return (code, ← eqTransD proof brr)

end


/-- Reflect a program `foo : A₁ → … → Aₙ → Free Op SOp X` (`n ≥ 0`) into
    `{ g : Closed // ∀ args, denoteProg (g KC Tp.denote) ⟨value-args⟩ ≈ ofFree (foo args) }` — the
    `Prog` whose `main` is a function of the program's inputs (delivered as an `HList`), with a `def_`
    per monomorphised helper.  Each `Aᵢ` that reifies to a `Tp` is a program input; any that does not
    (e.g. an in-bounds proof `j < n` for a symbolic index) is **erased from the AST** and instead
    left quantifying the soundness statement, where it discharges the erased get/set's `fail` branch.
    The non-recursive arm of `reflect%`. -/
def reflectMain (foo : Expr) : TermElabM Expr := do
  forallTelescope (← inferType foo) fun args codom => do
    let_expr Free Op SOp X := (← whnf codom)
      | throwError "reflect%: the body must have type `Free Op SOp _`, got{indentExpr codom}"
    let _ ← reifyTpOrThrow X
    -- Classify each argument: those whose type reifies to a `Tp` are **program inputs**; the rest
    -- (e.g. an in-bounds proof `j < n` accompanying a symbolic index) are **erased** from the AST but
    -- kept as hypotheses scoping the soundness statement — that is how a proof-erased `vget`/`vset`'s
    -- `fail` branch is ruled out when the index is symbolic: the source still carries the proof.
    let argTpOpt ← args.mapM (fun a => do reifyTp (← inferType a))
    let mut mainArgTps : Array Expr := #[]
    let mut valueArgs : Array Expr := #[]
    for i in [0:args.size] do
      if let some t := argTpOpt[i]! then
        mainArgTps := mainArgTps.push t; valueArgs := valueArgs.push args[i]!
    -- program inputs must be monomorphic and non-dependent (no type-parameter arguments); a *hypothesis*
    -- argument may freely depend on earlier value arguments (it is a proof *about* them).
    for i in [0:args.size] do
      if X.containsFVar args[i]!.fvarId! then
        throwError "reflect%: `main`'s result type may not depend on its arguments"
      for j in [i+1:args.size] do
        if argTpOpt[j]!.isSome && (← inferType args[j]!).containsFVar args[i]!.fvarId! then
          throwError "reflect%: `main` may not take a type-parameter argument\
                      {indentExpr (← inferType args[i]!)}"
    let tpTy := (.const ``Tp [] : Expr)
    let mainArgsList ← mkListLit tpTy mainArgTps.toList
    let fTy ← mkArrow (← mkAppM ``List #[tpTy]) (← mkArrow tpTy (mkSort (.succ (.succ .zero))))
    let vTy ← mkArrow tpTy (mkSort (.succ .zero))
    let defs ← IO.mkRef (#[] : Array DefEntry)
    let defsUsed ← IO.mkRef (#[] : Array Name)
    let denoteV := Lean.mkConst ``Tp.denote []
    let topBody := (← unfoldDefinition? (foo.beta args)).getD (foo.beta args)
    let g ← withLocalDeclD `F fTy fun F => withLocalDeclD `V vTy fun V => do
      let hlistTy ← mkAppM ``HList #[V, mainArgsList]
      -- walk `main` under an argument tuple `hargs`, substituting each host argument for its atom
      let walkMain (resolved : Option (Array (DefEntry × Expr))) (hargs : Expr) : MetaM Expr := do
        let mut subst : List (FVarId × Expr) := []
        for i in [0:valueArgs.size] do subst := (valueArgs[i]!.fvarId!, ← projHList hargs i) :: subst
        let env : Env := { Op, SOp, F, V, subst, defs, defsUsed, resolved }
        env.walkProg topBody (env.mkRet ·)
      let _ ← withLocalDeclD `args hlistTy fun h => walkMain none h    -- pass 1: discovery
      let entries ← defs.get
      let prog ← withLocalDeclsD (entries.map fun d => (`f, fun _ => pure (mkApp2 F d.asList d.retTp)))
        fun cfs => do                                                  -- pass 2: build
          let resolved := entries.zip cfs
          let mainLam ← withLocalDeclD `args hlistTy fun h => do
            mkLambdaFVars #[h] (← walkMain (some resolved) h)
          let mut prog ← mkAppOptM ``Prog.main #[Op, SOp, F, V, mainArgsList, none, mainLam]
          for j in [0:entries.size] do
            let (d, cf) := resolved[entries.size - 1 - j]!
            prog ← mkAppOptM ``Prog.def_
              #[Op, SOp, F, V, mainArgsList, none, d.asList, d.retTp, d.bodyLam, ← mkLambdaFVars #[cf] prog]
          pure prog
      mkLambdaFVars #[F, V] prog
    let gTy ← inferType g
    let kc ← mkAppM ``KC #[Op]
    -- the actual (value) arguments as an `HList Tp.denote mainArgs`, for the soundness statement
    let mut argHList ← mkAppOptM ``HList.nil #[none, denoteV]
    for (a, t) in (valueArgs.zip mainArgTps).reverse do
      argHList ← mkAppOptM ``HList.cons #[none, denoteV, t, none, a, argHList]
    let ofFreeFn ← mkAppOptM ``ofFree #[Op, SOp, X]
    -- soundness  fun g => ∀ args, denoteProg (g KC Tp.denote) ⟨args⟩ ≈ ofFree (foo args)
    -- — `denoteProg` lands in `Comp` *directly*; `ofFree` only embeds the source `Free`.
    let pred ← withLocalDeclD `g gTy fun gv => do
      let lhs ← mkAppOptM ``denoteProg #[Op, SOp, none, none, mkAppN gv #[kc, denoteV], argHList]
      let eutt ← mkAppM ``ITree.Eutt #[lhs, mkApp ofFreeFn (foo.beta args)]
      mkLambdaFVars #[gv] (← mkForallFVars args eutt)
    -- proof: `denoteProg (g KC ⟨args⟩) = ofFree (foo args)` directly — `denote`/`denoteProg` and
    -- `ofFree` unfold to the same tree, the `call`-binds fusing via `bind_ret`/`bind_vis`.
    let dpC ← mkAppOptM ``denoteProg #[Op, SOp, none, none, mkAppN g #[kc, denoteV], argHList]
    let eqTy ← mkEq dpC (mkApp ofFreeFn (foo.beta args))
    -- compositional bisimulation: unfold `denoteProg`/`denote` and `ofFree`/`ofFree_bind` on *both*
    -- sides, plus every source definition the reflector touched, so scope- and call-binds fuse
    -- consistently and the two `Comp` trees converge.
    -- **The compositional soundness proof**: walk the source at the concrete representation and
    -- assemble the `sc_*` congruence lemmas — the source's own in-bounds proofs discharge each erased
    -- get/set `fail` branch (`dif_pos`), and helper calls compose via each helper's own (★)-proof.
    -- No `simp`: the proof term mirrors the source structure.
    let mut psubst : List (FVarId × Expr) := []
    for va in valueArgs do psubst := (va.fvarId!, va) :: psubst
    let penv : Env := { Op, SOp, F := kc, V := denoteV, subst := psubst, defs, defsUsed }
    let (_, proof) ← penv.pTop topBody (← reifyTpOrThrow X)
    let eqPrf ← mkExpectedTypeHint proof eqTy
    let prf ← mkLambdaFVars args (← mkAppM ``ITree.Eutt.of_eq #[eqPrf])
    mkAppOptM ``Subtype.mk #[gTy, pred, g, prf]

end Freigen
