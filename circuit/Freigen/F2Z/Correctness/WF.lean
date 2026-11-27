import Freigen.F2Z.Defs

namespace Freigen.F2Z.WF

/-- A total interpretation of every Boolean and integer witness identifier. -/
structure Valuation where
  bool : Nat → Bool
  int : Nat → ℤ

/-- Two linear combinations have the same value in their respective valuations. -/
def LCEq {F : Type u} [Semiring F] [DecidableEq F]
    (leftVal rightVal : Nat → F) (left right : LC F) : Prop :=
  left.eval leftVal = right.eval rightVal

/-- Evaluate a heterogeneous list of hint arguments. -/
def evalArgs (valuation : Valuation) :
    {argTps : List Eff.WitnessSide} →
    HList Eff.WitnessSide.denoteW argTps →
    HList Eff.WitnessSide.denoteF argTps
  | [], .nil => .nil
  | .z :: _, .cons x xs =>
      .cons (show ℤ from (show LC ℤ from x).eval valuation.int)
        (evalArgs valuation xs)
  | .f₂ :: _, .cons x xs =>
      .cons (show Bool from (show LC Bool from x).eval valuation.bool)
        (evalArgs valuation xs)

/-- Hint arguments are equivalent when they evaluate to the same heterogeneous tuple. -/
def ArgsEq (leftVal rightVal : Valuation)
    {argTps : List Eff.WitnessSide}
    (left right : HList Eff.WitnessSide.denoteW argTps) : Prop :=
  evalArgs leftVal left = evalArgs rightVal right

/-- A vector of Boolean LCs realizes a vector of values under a valuation. -/
def RealizesBools (valuation : Nat → Bool)
    (xs : Vector (LC Bool) n) (values : Vector Bool n) : Prop :=
  ∀ (i : Nat) (hi : i < n),
    LC.eval valuation xs[i] = values[i]

/-- Stateless denotation of the hint language. -/
def interpHint (body : Hint α) : Option α :=
  Free.interp (fun _ _ => none) body

@[simp]
theorem interpHint_pure (value : α) :
    interpHint (pure value : Hint α) = some value := by
  rfl

@[simp]
theorem interpHint_bind (body : Hint α) (k : α → Hint β) :
    interpHint (body >>= k) =
      (interpHint body >>= fun value => interpHint (k value)) := by
  simp [interpHint, Free.interp_bind]

@[simp]
theorem interpHint_fail (msg : String) :
    interpHint (F2Z.fail (α := α) msg) = none := by
  unfold interpHint F2Z.fail
  rw [Free.interp_op]

/-- Two hint computations either both fail, or return related values. -/
def HintRel (R : α → β → Prop) (left : Hint α) (right : Hint β) : Prop :=
  Option.Rel R (interpHint left) (interpHint right)

/-- A hint computation successfully returns `value`. -/
def HintReturns (body : Hint α) (value : α) : Prop :=
  interpHint body = some value

/-- A deterministic hint computation has at most one successful result. -/
theorem HintReturns.unique {body : Hint α} {left right : α}
    (hleft : HintReturns body left) (hright : HintReturns body right) :
    left = right := by
  unfold HintReturns at hleft hright
  rw [hleft] at hright
  exact Option.some.inj hright

attribute [grind →] HintReturns.unique

theorem HintRel.refl (body : Hint α) : HintRel Eq body body := by
  unfold HintRel
  cases interpHint body with
  | none => exact .none
  | some value => exact .some rfl

theorem HintRel.of_eq {left right : Hint α} (h : left = right) :
    HintRel Eq left right := by
  subst right
  exact HintRel.refl _

theorem HintRel.of_argsEq
    {argTps : List Eff.WitnessSide}
    {argsL argsR : HList Eff.WitnessSide.denoteW argTps}
    (body : HList Eff.WitnessSide.denoteF argTps → Hint α)
    (hargs : ArgsEq leftVal rightVal argsL argsR) :
    HintRel Eq (body (evalArgs leftVal argsL))
      (body (evalArgs rightVal argsR)) := by
  unfold ArgsEq at hargs
  rw [hargs]
  exact HintRel.refl _

/-- Assumptions describing which pairs of total valuations are currently related. -/
abbrev Assumption := Valuation → Valuation → Prop

/-- A postcondition over two results under two total valuations. -/
abbrev Post (alpha : Type) := Valuation → Valuation → alpha → alpha → Prop

/--
The representation-parametric semantics of circuits.

`P` describes the currently related pairs of total valuations. Effects strengthen `P`
with the semantic equations satisfied by their returned LCs. Nothing is allocated or
mutated in this semantics: the valuations are total from the beginning, and a circuit
must behave uniformly for every pair satisfying `P`.
-/
inductive Rel {alpha : Type} (Q : Post alpha) :
    Assumption → Circuit alpha → Circuit alpha → Prop
  | pure {P : Assumption} {left right : alpha} :
      (∀ leftVal rightVal, P leftVal rightVal →
        Q leftVal rightVal left right) →
      Rel Q P (pure left) (pure right)
  | assertR1C {P : Assumption}
      {aL bL cL aR bR cR : LC ℤ}
      {kL kR : Unit → Circuit alpha} :
      (∀ leftVal rightVal, P leftVal rightVal →
        LCEq leftVal.int rightVal.int aL aR) →
      (∀ leftVal rightVal, P leftVal rightVal →
        LCEq leftVal.int rightVal.int bL bR) →
      (∀ leftVal rightVal, P leftVal rightVal →
        LCEq leftVal.int rightVal.int cL cR) →
      Rel Q P (kL ()) (kR ()) →
      Rel Q P
        (F2Z.assertR1C aL bL cL >>= kL)
        (F2Z.assertR1C aR bR cR >>= kR)
  | f2z {P : Assumption} {aL aR : LC Bool}
      {kL kR : LC ℤ → Circuit alpha} :
      (∀ leftVal rightVal, P leftVal rightVal →
        LCEq leftVal.bool rightVal.bool aL aR) →
      (∀ outL outR,
        Rel Q
          (fun leftVal rightVal =>
            P leftVal rightVal ∧
            outL.eval leftVal.int = (aL.eval leftVal.bool).toInt ∧
            outR.eval rightVal.int = (aR.eval rightVal.bool).toInt)
          (kL outL) (kR outR)) →
      Rel Q P
        (F2Z.f2z aL >>= kL)
        (F2Z.f2z aR >>= kR)
  | hint {P : Assumption} {n : Nat} {argTps : List Eff.WitnessSide}
      {argsL argsR : HList Eff.WitnessSide.denoteW argTps}
      {bodyL bodyR : HList Eff.WitnessSide.denoteF argTps → Hint (Vector Bool n)}
      {kL kR : Vector (LC Bool) n → Circuit alpha} :
      (∀ leftVal rightVal, P leftVal rightVal →
        ArgsEq leftVal rightVal argsL argsR) →
      (∀ leftVal rightVal, P leftVal rightVal →
        HintRel Eq
          (bodyL (evalArgs leftVal argsL))
          (bodyR (evalArgs rightVal argsR))) →
      (∀ outL outR,
        Rel Q
          (fun leftVal rightVal =>
            P leftVal rightVal ∧ ∃ values,
              HintReturns
                (bodyL (evalArgs leftVal argsL)) values ∧
              HintReturns
                (bodyR (evalArgs rightVal argsR)) values ∧
              RealizesBools leftVal.bool outL values ∧
              RealizesBools rightVal.bool outR values)
          (kL outL) (kR outR)) →
      Rel Q P
        (F2Z.hint argsL bodyL >>= kL)
        (F2Z.hint argsR bodyR >>= kR)

theorem Rel.assertR1C_pure {Q : Post Unit} {P : Assumption}
    {aL bL cL aR bR cR : LC ℤ}
    (ha : ∀ leftVal rightVal, P leftVal rightVal →
      LCEq leftVal.int rightVal.int aL aR)
    (hb : ∀ leftVal rightVal, P leftVal rightVal →
      LCEq leftVal.int rightVal.int bL bR)
    (hc : ∀ leftVal rightVal, P leftVal rightVal →
      LCEq leftVal.int rightVal.int cL cR)
    (hpost : ∀ leftVal rightVal, P leftVal rightVal →
      Q leftVal rightVal () ()) :
    Rel Q P (F2Z.assertR1C aL bL cL) (F2Z.assertR1C aR bR cR) := by
  simpa only [bind_pure] using
    Rel.assertR1C ha hb hc (Rel.pure hpost)

theorem Rel.hint_pure {Q : Post (Vector (LC Bool) n)} {P : Assumption}
    {argTps : List Eff.WitnessSide}
    {argsL argsR : HList Eff.WitnessSide.denoteW argTps}
    {bodyL bodyR : HList Eff.WitnessSide.denoteF argTps →
      Hint (Vector Bool n)}
    (hargs : ∀ leftVal rightVal, P leftVal rightVal →
      ArgsEq leftVal rightVal argsL argsR)
    (hbody : ∀ leftVal rightVal, P leftVal rightVal →
      HintRel Eq (bodyL (evalArgs leftVal argsL))
        (bodyR (evalArgs rightVal argsR)))
    (hpost : ∀ outL outR leftVal rightVal,
      (P leftVal rightVal ∧ ∃ values,
        HintReturns (bodyL (evalArgs leftVal argsL)) values ∧
        HintReturns (bodyR (evalArgs rightVal argsR)) values ∧
        RealizesBools leftVal.bool outL values ∧
        RealizesBools rightVal.bool outR values) →
      Q leftVal rightVal outL outR) :
    Rel Q P (F2Z.hint argsL bodyL) (F2Z.hint argsR bodyR) := by
  rw [← bind_pure (x := F2Z.hint argsL bodyL),
    ← bind_pure (x := F2Z.hint argsR bodyR)]
  exact Rel.hint hargs hbody fun outL outR => Rel.pure (hpost outL outR)

theorem Rel.mono {P Q : Post alpha} {R : Assumption}
    {left right : Circuit alpha} (h : Rel P R left right)
    (hpq : ∀ leftVal rightVal left right,
      P leftVal rightVal left right → Q leftVal rightVal left right) :
    Rel Q R left right := by
  induction h with
  | pure hpost => exact .pure fun l r hR => hpq _ _ _ _ (hpost l r hR)
  | assertR1C ha hb hc _ ih => exact .assertR1C ha hb hc ih
  | f2z ha _ ih => exact .f2z ha ih
  | hint hargs hbody _ ih => exact .hint hargs hbody ih

theorem Rel.bind {P : Post alpha} {Q : Post beta} {R : Assumption}
    {left right : Circuit alpha} (h : Rel P R left right)
    (fL fR : alpha → Circuit beta)
    (hcont : ∀ (S : Assumption) left right,
      (∀ leftVal rightVal, S leftVal rightVal →
        P leftVal rightVal left right) →
      Rel Q S (fL left) (fR right)) :
    Rel Q R (left >>= fL) (right >>= fR) := by
  induction h with
  | pure hpost => simpa using hcont _ _ _ hpost
  | assertR1C ha hb hc _ ih =>
      simpa only [bind_assoc] using Rel.assertR1C ha hb hc ih
  | f2z ha _ ih =>
      simpa only [bind_assoc] using Rel.f2z ha ih
  | hint hargs hbody _ ih =>
      simpa only [bind_assoc] using Rel.hint hargs hbody ih

/-- An effectful function that preserves a logical relation in every ambient world. -/
def RelHom (R : Post α) (S : Post β)
    (fL fR : α → Circuit β) : Prop :=
  ∀ (P : Assumption) left right,
    (∀ leftVal rightVal, P leftVal rightVal →
      R leftVal rightVal left right) →
    Rel (fun leftVal rightVal outL outR =>
      P leftVal rightVal ∧ S leftVal rightVal outL outR)
      P (fL left) (fR right)

/-- Pointwise lifting of a relation to fixed-length vectors. -/
def VectorRel (R : Post α) : Post (Vector α n) :=
  fun leftVal rightVal left right =>
    ∀ i : Fin n, R leftVal rightVal left[i] right[i]

private theorem array_mapM_push [Monad m] [LawfulMonad m]
    (f : α → m β) (xs : Array α) (x : α) :
    (xs.push x).mapM f = (do
      let ys ← xs.mapM f
      let y ← f x
      pure (ys.push y)) := by
  simp only [Array.mapM_eq_mapM_toList, Array.toList_push,
    List.mapM_append, List.mapM_cons, List.mapM_nil]
  simp

private theorem vector_mapM_push [Monad m] [LawfulMonad m]
    (f : α → m β) (xs : Vector α n) (x : α) :
    (xs.push x).mapM f = (do
      let ys ← xs.mapM f
      let y ← f x
      pure (ys.push y)) := by
  apply Vector.map_toArray_inj.mp
  rw [Vector.toArray_mapM, Vector.toArray_push, array_mapM_push]
  rw [← Vector.toArray_mapM (f := f) (xs := xs)]
  rw [bind_map_left]
  simp only [← bind_pure_comp, bind_assoc, pure_bind,
    Vector.toArray_push]

private theorem vector_mapM_empty [Monad m] [LawfulMonad m]
    (f : α → m β) :
    Vector.mapM f (#v[] : Vector α 0) =
      (pure (#v[] : Vector β 0) : m (Vector β 0)) := by
  apply Vector.map_toArray_inj.mp
  rw [Vector.toArray_mapM]
  simp

/-- `Vector.mapM` lifts any relational Kleisli morphism pointwise. -/
theorem RelHom.vectorMapM {R : Post α} {S : Post β}
    {fL fR : α → Circuit β} (hf : RelHom R S fL fR) :
    ∀ {n}, RelHom (VectorRel (n := n) R) (VectorRel (n := n) S)
      (fun xs => xs.mapM fL) (fun xs => xs.mapM fR) := by
  intro n
  induction n with
  | zero =>
      intro P left right hinput
      rw [show left = #v[] from Vector.eq_empty,
        show right = #v[] from Vector.eq_empty]
      dsimp only
      rw [vector_mapM_empty, vector_mapM_empty]
      exact Rel.pure fun _ _ hP =>
        ⟨hP, fun i => Fin.elim0 i⟩
  | succ n ih =>
      intro P left right hinput
      obtain ⟨leftInit, leftLast, rfl⟩ :=
        Vector.exists_push (xs := left)
      obtain ⟨rightInit, rightLast, rfl⟩ :=
        Vector.exists_push (xs := right)
      dsimp only
      rw [vector_mapM_push, vector_mapM_push]
      have hinit := ih P leftInit rightInit fun leftVal rightVal hP i => by
        simpa [VectorRel] using
          hinput leftVal rightVal hP (Fin.castSucc i)
      apply hinit.bind
        (fun init => fL leftLast >>= fun last =>
          Pure.pure (init.push last))
        (fun init => fR rightLast >>= fun last =>
          Pure.pure (init.push last))
      intro ambient initL initR hambient
      have hlast := hf ambient leftLast rightLast fun leftVal rightVal hP => by
        have hp := hambient leftVal rightVal hP
        simpa [VectorRel] using
          hinput leftVal rightVal hp.1 (Fin.last n)
      apply hlast.bind
        (fun last => Pure.pure (initL.push last))
        (fun last => Pure.pure (initR.push last))
      intro final lastL lastR hfinal
      exact Rel.pure fun leftVal rightVal hP => by
        have hlastPost := hfinal leftVal rightVal hP
        have hinitPost := hambient leftVal rightVal hlastPost.1
        refine ⟨hinitPost.1, ?_⟩
        intro i
        by_cases hi : i.val < n
        · change S leftVal rightVal
            (initL.push lastL)[i.val] (initR.push lastR)[i.val]
          rw [Vector.getElem_push_lt hi, Vector.getElem_push_lt hi]
          exact hinitPost.2 ⟨i, hi⟩
        · have hieq : i = Fin.last n := by
            apply Fin.ext
            simp
            omega
          subst i
          simpa [VectorRel] using hlastPost.2

/-- `Vector.ofFnM` lifts a relational specification for each index. The
pointwise computations are nullary `RelHom`s so they remain usable in every
ambient relational context. -/
theorem Rel.vectorOfFnM
    {n : Nat} {P : Assumption} {S : Fin n → Post α}
    {fL fR : Fin n → Circuit α}
    (hf : ∀ i, RelHom
      (fun leftVal rightVal (_ _ : Unit) => P leftVal rightVal) (S i)
      (fun _ => fL i) (fun _ => fR i)) :
    Rel (fun leftVal rightVal left right =>
        P leftVal rightVal ∧
          ∀ i : Fin n, S i leftVal rightVal left[i] right[i])
      P (Vector.ofFnM fL) (Vector.ofFnM fR) := by
  induction n with
  | zero =>
      rw [Vector.ofFnM_zero, Vector.ofFnM_zero]
      exact Rel.pure fun leftVal rightVal hP =>
        ⟨hP, fun i => Fin.elim0 i⟩
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
        (fun leftVal rightVal ha => (hA leftVal rightVal ha).1)
      apply hlast.bind
        (fun x => Pure.pure (leftPrefix.push x))
        (fun x => Pure.pure (rightPrefix.push x))
      intro B leftLast rightLast hB
      exact Rel.pure fun leftVal rightVal hPre => by
        have hlastPost := hB leftVal rightVal hPre
        have hprefixPost := hA leftVal rightVal hlastPost.1
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

theorem RelHom.f2z :
    RelHom
      (fun leftVal rightVal left right =>
        LCEq leftVal.bool rightVal.bool left right)
      (fun leftVal rightVal left right =>
        LCEq leftVal.int rightVal.int left right)
      F2Z.f2z F2Z.f2z := by
  intro P left right hinput
  have hrel :
      Rel (fun leftVal rightVal outL outR =>
          P leftVal rightVal ∧
          LCEq leftVal.int rightVal.int outL outR)
        P
        (F2Z.f2z left >>= (Pure.pure : LC ℤ → Circuit (LC ℤ)))
        (F2Z.f2z right >>= (Pure.pure : LC ℤ → Circuit (LC ℤ))) := by
    apply Rel.f2z hinput
    intro outL outR
    exact Rel.pure fun leftVal rightVal hP => by
      refine ⟨hP.1, ?_⟩
      unfold LCEq
      exact hP.2.1.trans
        ((congrArg Bool.toInt (hinput _ _ hP.1)).trans hP.2.2.symm)
  simpa only [bind_pure] using hrel

/-- A relational specification under a predicate on global valuations. -/
def Valid (P : Assumption) (left right : Circuit alpha) (Q : Post alpha) : Prop :=
  Rel Q P left right

/-- A reusable relational contract for a gadget. -/
def GadgetSpec (P : Valuation → Valuation → input → input → Prop)
    (gadget : input → Circuit output) (Q : Post output) : Prop :=
  ∀ left right,
    Rel Q (fun leftVal rightVal => P leftVal rightVal left right)
      (gadget left) (gadget right)

/-- A closed circuit behaves uniformly for every pair of total valuations. -/
def WellFormed (circ : Circuit alpha) : Prop :=
  Rel (fun _ _ _ _ => True) (fun _ _ => True) circ circ

theorem wellFormed_iff {circ : Circuit alpha} :
    WellFormed circ ↔
      Rel (fun _ _ _ _ => True) (fun _ _ => True) circ circ :=
  Iff.rfl

attribute [grind intro] Rel
attribute [grind ←] Rel.assertR1C_pure
attribute [grind =]
  LC.eval_zero LC.eval_add LC.eval_nsmul LC.eval_smul
  LC.eval_one LC.eval_ofConst LC.eval_singleton Vector.getElem_map
  interpHint_pure interpHint_bind interpHint_fail
attribute [grind unfold]
  WellFormed Valid GadgetSpec VectorRel LCEq ArgsEq evalArgs RealizesBools
  HintReturns

end Freigen.F2Z.WF
