import Freigen.F2Z.Defs

namespace Freigen.F2Z.WF

open Context

/-- The semantic environment for one representation context. -/
abbrev Valuation [ctx : Context] := Context.Valuations ctx

/-- Values in two representations agree when their respective valuations
give the same scalar. -/
def LCEq {F : Type u} [Semiring F]
    {leftW : Type v} [AddCommMonoid leftW] [ModuleWithOne F leftW]
    {rightW : Type w} [AddCommMonoid rightW] [ModuleWithOne F rightW]
    (leftVal : Freigen.F2Z.Valuation F leftW)
    (rightVal : Freigen.F2Z.Valuation F rightW)
    (left : leftW) (right : rightW) : Prop :=
  leftVal left = rightVal right

/-- Evaluate a heterogeneous list of hint arguments in its representation. -/
def evalArgs (ctx : Context) (valuation : @Valuation ctx) :
    {argTps : List Eff.WitnessSide} →
    HList (Eff.WitnessSide.denoteW ctx) argTps →
    HList Eff.WitnessSide.denoteF argTps
  | [], .nil => .nil
  | .z :: _, .cons x xs =>
      .cons (valuation.int (show ctx.Wℤ from
        (by simpa [Eff.WitnessSide.denoteW] using x)))
        (evalArgs ctx valuation xs)
  | .f₂ :: _, .cons x xs =>
      .cons (valuation.bool (show ctx.WBool from
        (by simpa [Eff.WitnessSide.denoteW] using x)))
        (evalArgs ctx valuation xs)

/-- Hint arguments agree when they evaluate to the same heterogeneous tuple. -/
def ArgsEq {leftCtx rightCtx : Context}
    (leftVal : @Valuation leftCtx) (rightVal : @Valuation rightCtx)
    {argTps : List Eff.WitnessSide}
    (left : HList (Eff.WitnessSide.denoteW leftCtx) argTps)
    (right : HList (Eff.WitnessSide.denoteW rightCtx) argTps) : Prop :=
  evalArgs leftCtx leftVal left = evalArgs rightCtx rightVal right

/-- A vector of abstract Boolean combinations realizes concrete values. -/
def RealizesBools {ctx : Context}
    (valuation : Freigen.F2Z.Valuation Bool ctx.WBool)
    (xs : Vector ctx.WBool n) (values : Vector Bool n) : Prop :=
  ∀ (i : Nat) (hi : i < n), valuation xs[i] = values[i]

/-- Stateless denotation of the hint language. -/
def interpHint {ctx : Context} (body : @Hint ctx α) : Option α :=
  Free.interp (fun _ _ => none) body

@[simp] theorem interpHint_pure {ctx : Context} (value : α) :
    interpHint (pure value : @Hint ctx α) = some value := rfl

@[simp] theorem interpHint_bind {ctx : Context}
    (body : @Hint ctx α) (k : α → @Hint ctx β) :
    interpHint (body >>= k) =
      (interpHint body >>= fun value => interpHint (k value)) := by
  simp [interpHint, Free.interp_bind]

@[simp] theorem interpHint_fail {ctx : Context} (msg : String) :
    interpHint (F2Z.fail (ctx := ctx) (α := α) msg) = none := by
  unfold interpHint F2Z.fail
  rw [Free.interp_op]

/-- Hint computations in different contexts either both fail or return
related values. -/
def HintRel {leftCtx rightCtx : Context} (R : α → β → Prop)
    (left : @Hint leftCtx α) (right : @Hint rightCtx β) : Prop :=
  Option.Rel R (interpHint left) (interpHint right)

def HintReturns {ctx : Context} (body : @Hint ctx α) (value : α) : Prop :=
  interpHint body = some value

theorem HintReturns.unique {ctx : Context} {body : @Hint ctx α} {left right : α}
    (hleft : HintReturns body left) (hright : HintReturns body right) :
    left = right := by
  unfold HintReturns at hleft hright
  rw [hleft] at hright
  exact Option.some.inj hright

attribute [grind →] HintReturns.unique

theorem HintRel.refl {ctx : Context} (body : @Hint ctx α) :
    HintRel Eq body body := by
  unfold HintRel
  cases interpHint body with
  | none => exact .none
  | some value => exact .some rfl

theorem HintRel.of_eq {leftCtx rightCtx : Context}
    {left : @Hint leftCtx α} {right : @Hint rightCtx α}
    (h : interpHint left = interpHint right) : HintRel Eq left right := by
  unfold HintRel
  rw [h]
  cases interpHint right <;> simp

theorem HintRel.of_argsEq {leftCtx rightCtx : Context}
    {argTps : List Eff.WitnessSide}
    {argsL : HList (Eff.WitnessSide.denoteW leftCtx) argTps}
    {argsR : HList (Eff.WitnessSide.denoteW rightCtx) argTps}
    (body : HList Eff.WitnessSide.denoteF argTps → @Hint leftCtx α)
    (bodyR : HList Eff.WitnessSide.denoteF argTps → @Hint rightCtx α)
    (hbody : ∀ values, interpHint (body values) = interpHint (bodyR values))
    {leftVal : @Valuation leftCtx} {rightVal : @Valuation rightCtx}
    (hargs : ArgsEq leftVal rightVal argsL argsR) :
    HintRel Eq (body (evalArgs leftCtx leftVal argsL))
      (bodyR (evalArgs rightCtx rightVal argsR)) := by
  unfold ArgsEq at hargs
  rw [hargs]
  exact HintRel.of_eq (hbody _)

abbrev Assumption (leftCtx rightCtx : Context) :=
  @Valuation leftCtx → @Valuation rightCtx → Prop

abbrev Post (leftCtx rightCtx : Context) (leftType rightType : Type) :=
  @Valuation leftCtx → @Valuation rightCtx → leftType → rightType → Prop

/-- Representation-parametric circuit semantics.

The two programs may use different carrier types. Every primitive is related
only through its scalar denotation, so a derivation cannot inspect or depend
on the concrete representation of a linear combination. -/
inductive Rel {leftCtx rightCtx : Context} {leftType rightType : Type}
    (Q : Post leftCtx rightCtx leftType rightType) :
    Assumption leftCtx rightCtx →
    @Circuit leftCtx leftType → @Circuit rightCtx rightType → Prop
  | pure {P} {left : leftType} {right : rightType} :
      (∀ leftVal rightVal, P leftVal rightVal →
        Q leftVal rightVal left right) →
      Rel Q P (pure left) (pure right)
  | assertR1C {P}
      {aL bL cL : leftCtx.Wℤ} {aR bR cR : rightCtx.Wℤ}
      {kL : Unit → @Circuit leftCtx leftType}
      {kR : Unit → @Circuit rightCtx rightType} :
      (∀ leftVal rightVal, P leftVal rightVal →
        LCEq leftVal.int rightVal.int aL aR) →
      (∀ leftVal rightVal, P leftVal rightVal →
        LCEq leftVal.int rightVal.int bL bR) →
      (∀ leftVal rightVal, P leftVal rightVal →
        LCEq leftVal.int rightVal.int cL cR) →
      Rel Q P (kL ()) (kR ()) →
      Rel Q P
        (F2Z.assertR1C (ctx := leftCtx) aL bL cL >>= kL)
        (F2Z.assertR1C (ctx := rightCtx) aR bR cR >>= kR)
  | f2z {P} {aL : leftCtx.WBool} {aR : rightCtx.WBool}
      {kL : leftCtx.Wℤ → @Circuit leftCtx leftType}
      {kR : rightCtx.Wℤ → @Circuit rightCtx rightType} :
      (∀ leftVal rightVal, P leftVal rightVal →
        LCEq leftVal.bool rightVal.bool aL aR) →
      (∀ outL outR,
        Rel Q
          (fun leftVal rightVal =>
            P leftVal rightVal ∧
            leftVal.int outL = (leftVal.bool aL).toInt ∧
            rightVal.int outR = (rightVal.bool aR).toInt)
          (kL outL) (kR outR)) →
      Rel Q P
        (F2Z.f2z (ctx := leftCtx) aL >>= kL)
        (F2Z.f2z (ctx := rightCtx) aR >>= kR)
  | hint {P} {n : Nat} {argTps : List Eff.WitnessSide}
      {argsL : HList (Eff.WitnessSide.denoteW leftCtx) argTps}
      {argsR : HList (Eff.WitnessSide.denoteW rightCtx) argTps}
      {bodyL : HList Eff.WitnessSide.denoteF argTps →
        @Hint leftCtx (Vector Bool n)}
      {bodyR : HList Eff.WitnessSide.denoteF argTps →
        @Hint rightCtx (Vector Bool n)}
      {kL : Vector leftCtx.WBool n → @Circuit leftCtx leftType}
      {kR : Vector rightCtx.WBool n → @Circuit rightCtx rightType} :
      (∀ leftVal rightVal, P leftVal rightVal →
        ArgsEq leftVal rightVal argsL argsR) →
      (∀ leftVal rightVal, P leftVal rightVal →
        HintRel Eq
          (bodyL (evalArgs leftCtx leftVal argsL))
          (bodyR (evalArgs rightCtx rightVal argsR))) →
      (∀ outL outR,
        Rel Q
          (fun leftVal rightVal =>
            P leftVal rightVal ∧ ∃ values,
              HintReturns (bodyL (evalArgs leftCtx leftVal argsL)) values ∧
              HintReturns (bodyR (evalArgs rightCtx rightVal argsR)) values ∧
              RealizesBools leftVal.bool outL values ∧
              RealizesBools rightVal.bool outR values)
          (kL outL) (kR outR)) →
      Rel Q P
        (F2Z.hint (ctx := leftCtx) argsL bodyL >>= kL)
        (F2Z.hint (ctx := rightCtx) argsR bodyR >>= kR)

theorem Rel.assertR1C_pure {Q : Post leftCtx rightCtx Unit Unit}
    {P : Assumption leftCtx rightCtx}
    {aL bL cL : leftCtx.Wℤ} {aR bR cR : rightCtx.Wℤ}
    (ha : ∀ lv rv, P lv rv → LCEq lv.int rv.int aL aR)
    (hb : ∀ lv rv, P lv rv → LCEq lv.int rv.int bL bR)
    (hc : ∀ lv rv, P lv rv → LCEq lv.int rv.int cL cR)
    (hpost : ∀ lv rv, P lv rv → Q lv rv () ()) :
    Rel Q P (F2Z.assertR1C (ctx := leftCtx) aL bL cL)
      (F2Z.assertR1C (ctx := rightCtx) aR bR cR) := by
  simpa only [bind_pure] using Rel.assertR1C ha hb hc (Rel.pure hpost)

theorem Rel.mono {P Q : Post leftCtx rightCtx α β}
    {R : Assumption leftCtx rightCtx}
    {left : @Circuit leftCtx α} {right : @Circuit rightCtx β}
    (h : Rel P R left right)
    (hpq : ∀ lv rv left right, P lv rv left right → Q lv rv left right) :
    Rel Q R left right := by
  induction h with
  | pure hpost => exact .pure fun l r hR => hpq _ _ _ _ (hpost l r hR)
  | assertR1C ha hb hc _ ih => exact .assertR1C ha hb hc ih
  | f2z ha _ ih => exact .f2z ha ih
  | hint hargs hbody _ ih => exact .hint hargs hbody ih

theorem Rel.bind
    {P : Post leftCtx rightCtx αL αR}
    {Q : Post leftCtx rightCtx βL βR}
    {R : Assumption leftCtx rightCtx}
    {left : @Circuit leftCtx αL} {right : @Circuit rightCtx αR}
    (h : Rel P R left right)
    (fL : αL → @Circuit leftCtx βL) (fR : αR → @Circuit rightCtx βR)
    (hcont : ∀ (S : Assumption leftCtx rightCtx) left right,
      (∀ lv rv, S lv rv → P lv rv left right) →
      Rel Q S (fL left) (fR right)) :
    Rel Q R (left >>= fL) (right >>= fR) := by
  induction h with
  | pure hpost => simpa using hcont _ _ _ hpost
  | assertR1C ha hb hc _ ih =>
      simpa only [bind_assoc] using Rel.assertR1C ha hb hc ih
  | f2z ha _ ih => simpa only [bind_assoc] using Rel.f2z ha ih
  | hint hargs hbody _ ih =>
      simpa only [bind_assoc] using Rel.hint hargs hbody ih

theorem Rel.frame {Q : Post leftCtx rightCtx α β}
    {P A : Assumption leftCtx rightCtx}
    {left : @Circuit leftCtx α} {right : @Circuit rightCtx β}
    (h : Rel Q P left right)
    (hpre : ∀ lv rv, A lv rv → P lv rv) :
    Rel (fun lv rv left right => A lv rv ∧ Q lv rv left right)
      A left right := by
  induction h generalizing A with
  | pure hpost => exact .pure fun lv rv hA => ⟨hA, hpost lv rv (hpre lv rv hA)⟩
  | assertR1C ha hb hc _ ih =>
      exact .assertR1C
        (fun lv rv hA => ha lv rv (hpre lv rv hA))
        (fun lv rv hA => hb lv rv (hpre lv rv hA))
        (fun lv rv hA => hc lv rv (hpre lv rv hA)) (ih hpre)
  | @f2z P₀ aL aR kL kR ha _ ih =>
      refine Rel.f2z (fun lv rv hA => ha lv rv (hpre lv rv hA)) ?_
      intro outL outR
      let A' := fun lv rv => A lv rv ∧
        lv.int outL = (lv.bool aL).toInt ∧
        rv.int outR = (rv.bool aR).toInt
      have framed := ih outL outR (A := A') fun lv rv hA =>
        ⟨hpre lv rv hA.1, hA.2⟩
      exact framed.mono fun _ _ _ _ hpost => ⟨hpost.1.1, hpost.2⟩
  | @hint P₀ n argTps argsL argsR bodyL bodyR kL kR hargs hbody _ ih =>
      refine Rel.hint
        (fun lv rv hA => hargs lv rv (hpre lv rv hA))
        (fun lv rv hA => hbody lv rv (hpre lv rv hA)) ?_
      intro outL outR
      let A' := fun lv rv => A lv rv ∧ ∃ values,
        HintReturns (bodyL (evalArgs leftCtx lv argsL)) values ∧
        HintReturns (bodyR (evalArgs rightCtx rv argsR)) values ∧
        RealizesBools lv.bool outL values ∧ RealizesBools rv.bool outR values
      have framed := ih outL outR (A := A') fun lv rv hA =>
        ⟨hpre lv rv hA.1, hA.2⟩
      exact framed.mono fun _ _ _ _ hpost => ⟨hpost.1.1, hpost.2⟩

/-- A relational Kleisli morphism between different representations. -/
def RelHom {leftCtx rightCtx : Context}
    (R : Post leftCtx rightCtx αL αR)
    (S : Post leftCtx rightCtx βL βR)
    (fL : αL → @Circuit leftCtx βL)
    (fR : αR → @Circuit rightCtx βR) : Prop :=
  ∀ (P : Assumption leftCtx rightCtx) left right,
    (∀ lv rv, P lv rv → R lv rv left right) →
    Rel (fun lv rv outL outR => P lv rv ∧ S lv rv outL outR)
      P (fL left) (fR right)

def VectorRel {leftCtx rightCtx : Context}
    (R : Post leftCtx rightCtx α β) :
    Post leftCtx rightCtx (Vector α n) (Vector β n) :=
  fun lv rv left right => ∀ i : Fin n, R lv rv left[i] right[i]

private theorem array_mapM_push [Monad m] [LawfulMonad m]
    (f : α → m β) (xs : Array α) (x : α) :
    (xs.push x).mapM f = (do
      let ys ← xs.mapM f; let y ← f x; pure (ys.push y)) := by
  simp only [Array.mapM_eq_mapM_toList, Array.toList_push,
    List.mapM_append, List.mapM_cons, List.mapM_nil]
  simp

private theorem vector_mapM_push [Monad m] [LawfulMonad m]
    (f : α → m β) (xs : Vector α n) (x : α) :
    (xs.push x).mapM f = (do
      let ys ← xs.mapM f; let y ← f x; pure (ys.push y)) := by
  apply Vector.map_toArray_inj.mp
  rw [Vector.toArray_mapM, Vector.toArray_push, array_mapM_push]
  rw [← Vector.toArray_mapM (f := f) (xs := xs), bind_map_left]
  simp only [← bind_pure_comp, bind_assoc, pure_bind, Vector.toArray_push]

private theorem vector_mapM_empty [Monad m] [LawfulMonad m] (f : α → m β) :
    Vector.mapM f (#v[] : Vector α 0) =
      (pure (#v[] : Vector β 0) : m (Vector β 0)) := by
  apply Vector.map_toArray_inj.mp
  rw [Vector.toArray_mapM]
  simp

theorem RelHom.vectorMapM
    {R : Post leftCtx rightCtx αL αR}
    {S : Post leftCtx rightCtx βL βR}
    {fL : αL → @Circuit leftCtx βL}
    {fR : αR → @Circuit rightCtx βR}
    (hf : RelHom R S fL fR) : ∀ {n},
    RelHom (VectorRel (n := n) R) (VectorRel (n := n) S)
      (fun xs => xs.mapM fL) (fun xs => xs.mapM fR) := by
  intro n
  induction n with
  | zero =>
      intro P left right hinput
      rw [show left = #v[] from Vector.eq_empty,
        show right = #v[] from Vector.eq_empty]
      dsimp only
      rw [vector_mapM_empty, vector_mapM_empty]
      exact Rel.pure fun _ _ hP => ⟨hP, fun i => Fin.elim0 i⟩
  | succ n ih =>
      intro P left right hinput
      obtain ⟨leftInit, leftLast, rfl⟩ := Vector.exists_push (xs := left)
      obtain ⟨rightInit, rightLast, rfl⟩ := Vector.exists_push (xs := right)
      dsimp only
      rw [vector_mapM_push, vector_mapM_push]
      have hinit := ih P leftInit rightInit fun lv rv hP i => by
        simpa [VectorRel] using hinput lv rv hP (Fin.castSucc i)
      apply hinit.bind
        (fun init => fL leftLast >>= fun last => pure (init.push last))
        (fun init => fR rightLast >>= fun last => pure (init.push last))
      intro A initL initR hA
      have hlast := hf A leftLast rightLast fun lv rv h => by
        simpa [VectorRel] using hinput lv rv (hA lv rv h).1 (Fin.last n)
      apply hlast.bind
        (fun last => pure (initL.push last))
        (fun last => pure (initR.push last))
      intro B lastL lastR hB
      exact Rel.pure fun lv rv h => by
        have hp := hA lv rv (hB lv rv h).1
        refine ⟨hp.1, ?_⟩
        intro i
        by_cases hi : i.val < n
        · change S lv rv (initL.push lastL)[i.val] (initR.push lastR)[i.val]
          rw [Vector.getElem_push_lt hi, Vector.getElem_push_lt hi]
          exact hp.2 ⟨i, hi⟩
        · have : i = Fin.last n := Fin.ext (by simp; omega)
          subst i
          simpa [VectorRel] using (hB lv rv h).2

/-- `Vector.ofFnM` lifts a relational specification for every index. -/
theorem Rel.vectorOfFnM
    {leftCtx rightCtx : Context} {n : Nat}
    {P : Assumption leftCtx rightCtx}
    {S : Fin n → Post leftCtx rightCtx αL αR}
    {fL : Fin n → @Circuit leftCtx αL}
    {fR : Fin n → @Circuit rightCtx αR}
    (hf : ∀ i, RelHom
      (fun lv rv (_ _ : Unit) => P lv rv) (S i)
      (fun _ => fL i) (fun _ => fR i)) :
    Rel (fun lv rv left right =>
        P lv rv ∧ ∀ i : Fin n, S i lv rv left[i] right[i])
      P (Vector.ofFnM fL) (Vector.ofFnM fR) := by
  induction n with
  | zero =>
      rw [Vector.ofFnM_zero, Vector.ofFnM_zero]
      exact Rel.pure fun lv rv hP => ⟨hP, fun i => Fin.elim0 i⟩
  | succ n ih =>
      rw [Vector.ofFnM_succ, Vector.ofFnM_succ]
      have hprefix := ih
        (S := fun i => S i.castSucc)
        (fL := fun i => fL i.castSucc)
        (fR := fun i => fR i.castSucc)
        (fun i => hf i.castSucc)
      apply hprefix.bind
        (fun xs => fL (Fin.last n) >>= fun x => Pure.pure (xs.push x))
        (fun xs => fR (Fin.last n) >>= fun x => Pure.pure (xs.push x))
      intro A leftPrefix rightPrefix hA
      have hlast := hf (Fin.last n) A () ()
        (fun lv rv ha => (hA lv rv ha).1)
      apply hlast.bind
        (fun x => Pure.pure (leftPrefix.push x))
        (fun x => Pure.pure (rightPrefix.push x))
      intro B leftLast rightLast hB
      exact Rel.pure fun lv rv hPre => by
        have hlastPost := hB lv rv hPre
        have hprefixPost := hA lv rv hlastPost.1
        refine ⟨hprefixPost.1, ?_⟩
        intro i
        by_cases hi : i.val < n
        · let j : Fin n := ⟨i.val, hi⟩
          have hieq : i = j.castSucc := Fin.ext rfl
          rw [hieq]
          simpa using hprefixPost.2 j
        · have hieq : i = Fin.last n := by
            apply Fin.ext
            simp
            omega
          subst i
          simpa using hlastPost.2

theorem RelHom.f2z {leftCtx rightCtx : Context} :
    RelHom
      (fun (lv : @Valuation leftCtx) (rv : @Valuation rightCtx)
          (left : leftCtx.WBool) (right : rightCtx.WBool) =>
        LCEq lv.bool rv.bool left right)
      (fun (lv : @Valuation leftCtx) (rv : @Valuation rightCtx)
          (left : leftCtx.Wℤ) (right : rightCtx.Wℤ) =>
        LCEq lv.int rv.int left right)
      (F2Z.f2z (ctx := leftCtx)) (F2Z.f2z (ctx := rightCtx)) := by
  intro P left right hinput
  rw [← bind_pure (x := F2Z.f2z (ctx := leftCtx) left),
    ← bind_pure (x := F2Z.f2z (ctx := rightCtx) right)]
  apply Rel.f2z hinput
  intro outL outR
  exact Rel.pure fun lv rv h => by
    refine ⟨h.1, ?_⟩
    unfold LCEq
    exact h.2.1.trans
      ((congrArg Bool.toInt (hinput _ _ h.1)).trans h.2.2.symm)

/-- A context-polymorphic gadget contract. -/
def GadgetSpec {Input Output : Context → Type}
    (P : ∀ {leftCtx rightCtx},
      @Valuation leftCtx → @Valuation rightCtx →
      Input leftCtx → Input rightCtx → Prop)
    (gadget : ∀ {ctx : Context}, Input ctx → @Circuit ctx (Output ctx))
    (Q : ∀ {leftCtx rightCtx},
      @Valuation leftCtx → @Valuation rightCtx →
      Output leftCtx → Output rightCtx → Prop) : Prop :=
  ∀ (leftCtx rightCtx : Context) (left : Input leftCtx) (right : Input rightCtx),
    Rel (Q (leftCtx := leftCtx) (rightCtx := rightCtx))
      (fun lv rv => P lv rv left right)
      (@gadget leftCtx left) (@gadget rightCtx right)

/-- A context-quantified closed circuit is independent of its representation. -/
def WellFormed {Output : Context → Type}
    (circ : ∀ ctx : Context, @Circuit ctx (Output ctx)) : Prop :=
  ∀ leftCtx rightCtx,
    Rel (fun _ _ _ _ => True) (fun _ _ => True)
      (circ leftCtx) (circ rightCtx)

def Valid {leftCtx rightCtx : Context}
    (P : Assumption leftCtx rightCtx)
    (left : @Circuit leftCtx α) (right : @Circuit rightCtx β)
    (Q : Post leftCtx rightCtx α β) : Prop := Rel Q P left right

theorem GadgetSpec.relHom {Input Output : Context → Type}
    {P Q} {gadget : ∀ {ctx}, Input ctx → @Circuit ctx (Output ctx)}
    (spec : GadgetSpec P gadget Q) (leftCtx rightCtx : Context) :
    RelHom (P (leftCtx := leftCtx) (rightCtx := rightCtx))
      (Q (leftCtx := leftCtx) (rightCtx := rightCtx))
      (@gadget leftCtx) (@gadget rightCtx) := by
  intro A left right hinput
  exact (spec leftCtx rightCtx left right).frame hinput

attribute [grind intro] Rel
attribute [grind ←] Rel.assertR1C_pure
attribute [grind =]
  Valuation.zero_apply Valuation.add_apply Valuation.smul_apply
  Valuation.one_apply interpHint_pure interpHint_bind interpHint_fail
attribute [grind unfold]
  WellFormed Valid GadgetSpec VectorRel LCEq ArgsEq evalArgs RealizesBools
  HintReturns

end Freigen.F2Z.WF
