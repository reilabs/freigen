import Freigen.F2Z.Examples.Sha256.Full
import Freigen.F2Z.Examples.Sha256.FastWitgen
import Freigen.F2Z.Examples.Sha256.Proofs

namespace Freigen.F2Z.Examples

open Freigen.F2Z.Semantics

/- Everything in this module is a proof model or theorem.  Keeping the
definitions non-executable prevents Lake from generating C for large logical
trace objects; the optimized witgen itself remains fully executable in
`FastWitgen.lean`. -/
noncomputable section


theorem runAt_f2z (x : LC Bool) (s : Witgen.State) :
    StateT.run (Witgen.runAt (f2z x)) s =
      some (LC.ofConst (x.eval s.boolWitness).toInt, s) := by
  unfold Witgen.runAt f2z
  rw [Free.interp_op]
  simp only [Witgen.handler, StateT.run_get, Option.bind_some, StateT.run_pure]
  rfl

theorem Witgen.runAt_f2z_action (x : LC Bool) :
    Witgen.runAt (f2z x) =
      (do
        let s ← get
        pure (LC.ofConst (x.eval s.boolWitness).toInt) :
        StateT Witgen.State Option (LC Int)) := by
  apply StateT.ext
  intro s
  exact runAt_f2z x s

theorem runAt_assertR1C_of (a b c : LC Int) (s : Witgen.State)
    (h : a.eval Witgen.zeroWitness * b.eval Witgen.zeroWitness =
      c.eval Witgen.zeroWitness) :
    StateT.run (Witgen.runAt (assertR1C a b c)) s = some ((), s) := by
  unfold Witgen.runAt assertR1C
  rw [Free.interp_op]
  simp [Witgen.handler, h]

theorem runAt_hint {n : Nat} {argTps : List Eff.WitnessSide}
    (args : HList Eff.WitnessSide.denoteW argTps)
    (body : HList Eff.WitnessSide.denoteF argTps → Hint (Vector Bool n))
    (s : Witgen.State) (values : Vector Bool n)
    (hbody : Witgen.runAt (body (Witgen.evalArgs s args)) = some values) :
    StateT.run (Witgen.runAt (hint args body)) s = some
      (values.map LC.ofConst, { bools := s.bools ++ values.toArray }) := by
  unfold Witgen.runAt hint
  rw [Free.interp_op]
  unfold Witgen.runAt at hbody
  simp [Witgen.handler, hbody]

@[simp] theorem Witgen.runAt_bind (x : Circuit α)
    (f : α → Circuit β) :
    Witgen.runAt (x >>= f) =
      (Witgen.runAt x >>= fun a => Witgen.runAt (f a)) := by
  unfold Witgen.runAt
  rw [Free.interp_bind]

@[simp] theorem Witgen.runAt_pure (x : α) :
    Witgen.runAt (pure x : Circuit α) =
      (pure x : StateT Witgen.State Option α) := by
  rfl

theorem Witgen.runAt_forIn'_list
    (xs : List α) (init : β)
    (f : (a : α) → a ∈ xs → β → Circuit (ForInStep β)) :
    Witgen.runAt (forIn' xs init f) =
      forIn' xs init fun a h b => Witgen.runAt (f a h b) := by
  induction xs generalizing init with
  | nil => simp [Witgen.runAt]
  | cons x xs ih =>
      simp only [List.forIn'_cons, Witgen.runAt, Free.interp_bind]
      congr 1
      funext step
      cases step with
      | done b => simp [Witgen.runAt]
      | yield b =>
          unfold Witgen.runAt at ih
          exact ih b (fun a h b => f a (List.mem_cons_of_mem x h) b)

theorem Witgen.runAt_forIn'_range
    (xs : Std.Legacy.Range) (init : β)
    (f : (a : Nat) → a ∈ xs → β → Circuit (ForInStep β)) :
    Witgen.runAt (forIn' xs init f) =
      forIn' xs init fun a h b => Witgen.runAt (f a h b) := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range',
    Std.Legacy.Range.forIn'_eq_forIn'_range']
  simpa using Witgen.runAt_forIn'_list xs.toList init
    (fun a h b => f a (Std.Legacy.Range.mem_of_mem_range' h) b)

def fromWordResult (s : Witgen.State) (w : Word n) : U n where
  bits := w
  intBits := ([0:n].toList).foldl (fun res i => res.set! i
    (LC.ofConst (w.bitsLE[i]!.eval s.boolWitness).toInt)) default

theorem runFromWordStep (s : Witgen.State) (w : Word n)
    (i : Nat) (hi : i < n) (res : Vector (LC Int) n) :
    StateT.run (Witgen.runAt (do
      let b ← f2z (getElem w.bitsLE i hi)
      pure PUnit.unit
      pure (ForInStep.yield (res.set! i b)))) s =
    some (ForInStep.yield (res.set! i
      (LC.ofConst (w.bitsLE[i]!.eval s.boolWitness).toInt)), s) := by
  rw [getElem!_pos w.bitsLE i hi]
  rw [Witgen.runAt_bind]
  have htail (b : LC Int) : Witgen.runAt (γ := .constraint) (do
      pure PUnit.unit
      pure (ForInStep.yield (res.set! i b))) =
      (pure (ForInStep.yield (res.set! i b)) :
        StateT Witgen.State Option (ForInStep (Vector (LC Int) n))) := by
    rw [show (do
        pure PUnit.unit
        pure (ForInStep.yield (res.set! i b)) :
        Circuit (ForInStep (Vector (LC Int) n))) =
      pure (ForInStep.yield (res.set! i b)) by
        exact pure_bind PUnit.unit (fun _ =>
          pure (ForInStep.yield (res.set! i b)))]
    rfl
  have hfun : (fun b => Witgen.runAt (γ := .constraint) (do
      pure PUnit.unit
      pure (ForInStep.yield (res.set! i b)))) =
      (fun b => (pure (ForInStep.yield (res.set! i b)) :
        StateT Witgen.State Option (ForInStep (Vector (LC Int) n)))) := by
      funext b
      exact htail b
  have haction := congrArg
    (fun k => Witgen.runAt (f2z (getElem w.bitsLE i hi)) >>= k) hfun
  calc
    _ = StateT.run
        (Witgen.runAt (f2z (getElem w.bitsLE i hi)) >>= fun b =>
          pure (ForInStep.yield (res.set! i b))) s :=
      congrArg (fun action => StateT.run action s) haction
    _ = _ := by
      rw [Witgen.runAt_f2z_action]
      rfl

theorem runFromWordLoop (s : Witgen.State) (w : Word n)
    (xs : List Nat) (init : Vector (LC Int) n)
    (hxs : ∀ i ∈ xs, i < n) :
    StateT.run
      (forIn' xs init fun i hi res =>
        Witgen.runAt (do
          let b ← f2z (getElem w.bitsLE i (hxs i hi))
          pure PUnit.unit
          pure (ForInStep.yield (res.set! i b)))) s =
      some (xs.foldl (fun res i => res.set! i
        (LC.ofConst (w.bitsLE[i]!.eval s.boolWitness).toInt)) init, s) := by
  induction xs generalizing init with
  | nil => simp
  | cons i xs ih =>
      simp only [List.forIn'_cons, StateT.run_bind]
      rw [runFromWordStep s w i (hxs i (by simp)) init]
      rw [Option.bind_eq_bind, Option.bind_some]
      simp only [List.foldl]
      let next := init.set! i
        (LC.ofConst (w.bitsLE[i]!.eval s.boolWitness).toInt)
      calc
        _ = StateT.run
            (forIn' xs (init.set! i
              (LC.ofConst (w.bitsLE[i]!.eval s.boolWitness).toInt))
              fun j hj res => Witgen.runAt (do
              let b ← f2z (getElem w.bitsLE j (hxs j (by simp [hj])))
              pure PUnit.unit
              pure (ForInStep.yield (res.set! j b)))) s := rfl
        _ = some (xs.foldl (fun res j => res.set! j
              (LC.ofConst (w.bitsLE[j]!.eval s.boolWitness).toInt))
              (init.set! i (LC.ofConst
                (w.bitsLE[i]!.eval s.boolWitness).toInt)), s) :=
          ih (init.set! i (LC.ofConst
              (w.bitsLE[i]!.eval s.boolWitness).toInt))
            (fun j hj => hxs j (by simp [hj]))
        _ = _ := rfl

theorem runAt_fromWord (s : Witgen.State) (w : Word n) :
    StateT.run (Witgen.runAt (U.fromWord w)) s =
      some (fromWordResult s w, s) := by
  unfold U.fromWord
  rw [Witgen.runAt_bind]
  rw [Witgen.runAt_forIn'_range]
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  let indices := List.range' [:n].start [:n].size [:n].step
  have hindices : ∀ i ∈ indices, i < n := by
    intro i hi
    simpa [indices] using hi
  have hbody :
      (fun i (hi : i ∈ indices) (res : Vector (LC Int) n) => Witgen.runAt
        (have res := res
        do
          let b ← f2z (getElem w.bitsLE i (hindices i hi))
          let res := res.set! i b
          pure PUnit.unit
          pure (ForInStep.yield res))) =
      (fun i (hi : i ∈ indices) (res : Vector (LC Int) n) => Witgen.runAt (do
        let b ← f2z (getElem w.bitsLE i (hindices i hi))
        pure PUnit.unit
        pure (ForInStep.yield (res.set! i b)))) := by
    funext i hi res
    apply congrArg Witgen.runAt
    rfl
  have hloop := congrArg
    (fun body => forIn' indices (Vector.replicate n (0 : LC Int)) body)
    hbody
  have haction := congrArg
    (fun loop => loop >>= fun res =>
      Witgen.runAt (γ := .constraint)
        (pure ({ bits := w, intBits := res } : U n))) hloop
  calc
    _ = StateT.run
        ((forIn' indices (Vector.replicate n (0 : LC Int))
          fun i hi res => Witgen.runAt (do
            let b ← f2z (getElem w.bitsLE i (hindices i hi))
            pure PUnit.unit
            pure (ForInStep.yield (res.set! i b)))) >>= fun res =>
          Witgen.runAt (γ := .constraint)
            (pure ({ bits := w, intBits := res } : U n))) s :=
      congrArg (fun action => StateT.run action s) haction
    _ = _ := by
      rw [StateT.run_bind]
      rw [runFromWordLoop s w indices _ hindices]
      rw [Option.bind_eq_bind, Option.bind_some]
      simp only [Witgen.runAt, Free.interp_pure, StateT.run_pure]
      rfl

theorem foldl_set_get (xs : List Nat) (hxs : xs.Nodup)
    (hbound : ∀ j ∈ xs, j < n) (f : Nat → α)
    (init : Vector α n) (i : Nat) (hi : i < n) :
    (xs.foldl (fun acc j => acc.set! j (f j)) init)[i] =
      if i ∈ xs then f i else init[i] := by
  induction xs generalizing init with
  | nil => simp
  | cons j xs ih =>
      have hj : j < n := hbound j (by simp)
      have hnodup : xs.Nodup := hxs.tail
      have hjmem : j ∉ xs := (List.nodup_cons.mp hxs).1
      rw [List.foldl_cons, ih hnodup (fun k hk => hbound k (by simp [hk]))]
      by_cases himem : i ∈ xs
      · simp [himem]
      · by_cases hij : i = j
        · subst j
          simp only [List.mem_cons, true_or, ↓reduceIte]
          rw [if_neg himem]
          change (init.setIfInBounds i (f i))[i] = f i
          exact Vector.getElem_setIfInBounds_self hi
        · have hji : j ≠ i := Ne.symm hij
          simp only [List.mem_cons, hij, himem, or_false, ↓reduceIte]
          change (init.setIfInBounds j (f j))[i] = init[i]
          exact Vector.getElem_setIfInBounds_ne hi hji

theorem fromWordResult_intBits (s : Witgen.State) (w : Word n)
    (i : Fin n) :
    (fromWordResult s w).intBits[i] =
      LC.ofConst (w.bitsLE[i].eval s.boolWitness).toInt := by
  change (([0:n].toList).foldl (fun (res : Vector (LC Int) n) j => res.set! j
    (LC.ofConst (w.bitsLE[j]!.eval s.boolWitness).toInt)) default)[i.val]'i.isLt = _
  rw [foldl_set_get]
  · have himem : i.val ∈ [0:n].toList := by
      simpa [Std.Legacy.Range.toList] using i.isLt
    simp [himem, getElem!_pos w.bitsLE i.val i.isLt]
  · exact List.nodup_range' 1
  · intro j hj
    exact (Std.Legacy.Range.mem_of_mem_range' hj).2.1

def canonicalValuation (s : Witgen.State) : WF.Valuation where
  bool := s.boolWitness
  int := Witgen.zeroWitness

theorem fromWordResult_valid (s : Witgen.State) (w : Word n) :
    (fromWordResult s w).Valid (canonicalValuation s) := by
  intro i
  rw [fromWordResult_intBits]
  simp [canonicalValuation, fromWordResult]

@[simp] theorem fromWordResult_bits (s : Witgen.State) (w : Word n) :
    (fromWordResult s w).bits = w := rfl

def natBits (width value : Nat) : Vector Bool width :=
  Vector.ofFn fun i => value.testBit i

def appendNatBits (s : Witgen.State) (width value : Nat) : Witgen.State :=
  { bools := s.bools ++ (natBits width value).toArray }

theorem runAt_natBitsHint (s : Witgen.State) (x : LC Int)
    (width value : Nat) (hx : x.eval Witgen.zeroWitness = value) :
    StateT.run (Witgen.runAt (hint h![x] fun h![(x : Int)] => match x with
      | .ofNat value => pure (natBits width value)
      | _ => fail s!"negative integer {x} in U.fromInt")) s =
    some ((natBits width value).map LC.ofConst,
      appendNatBits s width value) := by
  apply runAt_hint
  change Witgen.runAt (match x.eval Witgen.zeroWitness with
    | .ofNat value => pure (natBits width value)
    | _ => fail s!"negative integer {x.eval Witgen.zeroWitness} in U.fromInt") =
    some (natBits width value)
  rw [hx]
  rfl

theorem runAt_fromIntHint (s : Witgen.State) (x : LC Int)
    (width value : Nat) (hx : x.eval Witgen.zeroWitness = value) :
    StateT.run (Witgen.runAt (hint h![x] fun h![(x : Int)] => match x with
      | .ofNat value => pure (Vector.ofFn fun i : Fin width => value.testBit i)
      | _ => fail s!"negative integer {x} in U.fromInt")) s =
    some ((natBits width value).map LC.ofConst,
      appendNatBits s width value) := by
  simpa [natBits] using runAt_natBitsHint s x width value hx

theorem runAt_fromIntHint_action (x : LC Int)
    (width value : Nat) (hx : x.eval Witgen.zeroWitness = value) :
    Witgen.runAt (hint h![x] fun h![(x : Int)] => match x with
      | .ofNat value => pure (Vector.ofFn fun i : Fin width => value.testBit i)
      | _ => fail s!"negative integer {x} in U.fromInt") =
    (do
      let s ← get
      set (appendNatBits s width value)
      pure ((natBits width value).map LC.ofConst) :
      StateT Witgen.State Option (Vector (LC Bool) width)) := by
  apply StateT.ext
  intro s
  exact runAt_fromIntHint s x width value hx

theorem fromWordResult_natBits_intVal (s : Witgen.State)
    (width value : Nat) (hvalue : value < 2 ^ width) :
    let word : Word width :=
      { bitsLE := (natBits width value).map LC.ofConst }
    (fromWordResult s word).intVal.eval Witgen.zeroWitness = value := by
  intro word
  change (fromWordResult s word).intVal.eval (canonicalValuation s).int = value
  rw [U.eval_intVal_eq_evalZ _ (fromWordResult_valid s word)]
  rw [fromWordResult_bits]
  unfold Word.evalZ
  dsimp [word, natBits, canonicalValuation]
  simp only [Vector.getElem_map, Vector.getElem_ofFn, LC.eval_ofConst]
  rw [Nat.ofBits_testBit, Nat.mod_eq_of_lt hvalue]

theorem runAt_fromInt (s : Witgen.State) (x : LC Int)
    (width value : Nat) (hx : x.eval Witgen.zeroWitness = value)
    (hvalue : value < 2 ^ width) :
    StateT.run (Witgen.runAt (U.fromInt width x)) s =
      some (fromWordResult (appendNatBits s width value)
        { bitsLE := (natBits width value).map LC.ofConst },
        appendNatBits s width value) := by
  unfold U.fromInt
  rw [Witgen.runAt_bind]
  let tail := fun bits : Vector (LC Bool) width => Witgen.runAt (do
    let r ← U.fromWord { bitsLE := bits }
    assertR1C 0 0 (x - r.intVal)
    pure r)
  have haction := congrArg (fun first => first >>= tail)
    (runAt_fromIntHint_action x width value hx)
  calc
    _ = StateT.run
        ((do
          let s ← get
          set (appendNatBits s width value)
          pure ((natBits width value).map LC.ofConst) :
          StateT Witgen.State Option (Vector (LC Bool) width)) >>= tail) s :=
      congrArg (fun action => StateT.run action s) haction
    _ = _ := by
      simp only [StateT.run_bind, StateT.run_get, StateT.run_set,
        StateT.run_pure]
      simp only [pure_bind]
      dsimp only [tail]
      rw [Witgen.runAt_bind, StateT.run_bind]
      rw [runAt_fromWord]
      rw [Option.bind_eq_bind, Option.bind_some]
      rw [Witgen.runAt_bind, StateT.run_bind]
      rw [runAt_assertR1C_of]
      · rw [Option.bind_eq_bind, Option.bind_some]
        simp [Witgen.runAt]
      · simp only [LC.eval_zero, zero_mul, LC.eval_sub]
        rw [fromWordResult_natBits_intVal _ _ _ hvalue, hx]
        simp

theorem runAt_fromDoubledHint (s : Witgen.State) (x : LC Int)
    (value : Nat) (hx : x.eval Witgen.zeroWitness = 2 * value) :
    StateT.run (Witgen.runAt (hint h![x] fun h![(x : Int)] => match x with
      | .ofNat n => pure (Vector.ofFn fun i : Fin 35 => (n / 2).testBit i)
      | _ => fail s!"negative integer {x} in U.fromDoubledInt35")) s =
    some ((natBits 35 value).map LC.ofConst,
      appendNatBits s 35 value) := by
  apply runAt_hint
  change Witgen.runAt (match x.eval Witgen.zeroWitness with
    | .ofNat n => pure (Vector.ofFn fun i : Fin 35 => (n / 2).testBit i)
    | _ => fail s!"negative integer {x.eval Witgen.zeroWitness} in U.fromDoubledInt35") =
    some (natBits 35 value)
  rw [hx]
  rw [show (2 * (value : Int)) = Int.ofNat (2 * value) by
    norm_num [Nat.cast_mul]]
  simp [natBits]
  rfl

theorem runAt_fromDoubledHint_action (x : LC Int)
    (value : Nat) (hx : x.eval Witgen.zeroWitness = 2 * value) :
    Witgen.runAt (hint h![x] fun h![(x : Int)] => match x with
      | .ofNat n => pure (Vector.ofFn fun i : Fin 35 => (n / 2).testBit i)
      | _ => fail s!"negative integer {x} in U.fromDoubledInt35") =
    (do
      let s ← get
      set (appendNatBits s 35 value)
      pure ((natBits 35 value).map LC.ofConst) :
      StateT Witgen.State Option (Vector (LC Bool) 35)) := by
  apply StateT.ext
  intro s
  exact runAt_fromDoubledHint s x value hx

theorem runAt_fromDoubledInt35 (s : Witgen.State) (x : LC Int)
    (value : Nat) (hx : x.eval Witgen.zeroWitness = 2 * value)
    (hvalue : value < 2 ^ 35) :
    StateT.run (Witgen.runAt (U.fromDoubledInt35 x)) s =
      some (fromWordResult (appendNatBits s 35 value)
        { bitsLE := (natBits 35 value).map LC.ofConst },
        appendNatBits s 35 value) := by
  unfold U.fromDoubledInt35
  rw [Witgen.runAt_bind]
  let tail := fun bits : Vector (LC Bool) 35 => Witgen.runAt (do
    let r ← U.fromWord { bitsLE := bits }
    assertR1C 0 0 (x - 2 • r.intVal)
    pure r)
  have haction := congrArg (fun first => first >>= tail)
    (runAt_fromDoubledHint_action x value hx)
  calc
    _ = StateT.run
        ((do
          let s ← get
          set (appendNatBits s 35 value)
          pure ((natBits 35 value).map LC.ofConst) :
          StateT Witgen.State Option (Vector (LC Bool) 35)) >>= tail) s :=
      congrArg (fun action => StateT.run action s) haction
    _ = _ := by
      simp only [StateT.run_bind, StateT.run_get, StateT.run_set,
        StateT.run_pure, pure_bind]
      dsimp only [tail]
      rw [Witgen.runAt_bind, StateT.run_bind]
      rw [runAt_fromWord]
      rw [Option.bind_eq_bind, Option.bind_some]
      rw [Witgen.runAt_bind, StateT.run_bind]
      rw [runAt_assertR1C_of]
      · rw [Option.bind_eq_bind, Option.bind_some]
        simp [Witgen.runAt]
      · simp only [LC.eval_zero, zero_mul, LC.eval_sub, LC.eval_nsmul,
          Nat.cast_ofNat]
        rw [fromWordResult_natBits_intVal _ _ _ hvalue, hx]
        simp [two_nsmul]

theorem fromWordResult_rel {ρ : WF.Valuation} (hρ : ρ.int = Witgen.zeroWitness)
    (s : Witgen.State) (w : Word n) (value : BitVec n)
    (hcurrent : Word.eval s.boolWitness w = value)
    (hfixed : Word.eval ρ.bool w = value) :
    U.Rel ρ (fromWordResult s w) value := by
  have hvalid : (fromWordResult s w).Valid ρ := by
    intro i
    rw [fromWordResult_intBits]
    simp only [LC.eval_ofConst]
    have hc := congrArg (fun x : BitVec n => x[i]) hcurrent
    have hf := congrArg (fun x : BitVec n => x[i]) hfixed
    have hc' : LC.eval s.boolWitness w.bitsLE[i] = value[i] := by
      simpa [Word.eval] using hc
    have hf' : LC.eval ρ.bool w.bitsLE[i] = value[i] := by
      simpa [Word.eval] using hf
    change (LC.eval s.boolWitness w.bitsLE[i]).toInt =
      (LC.eval ρ.bool w.bitsLE[i]).toInt
    exact congrArg Bool.toInt (hc'.trans hf'.symm)
  exact ⟨hvalid, U.eval_eq_word_eval _ w hvalid rfl |>.trans hfixed⟩

theorem constWord_eval (ρ : Nat → Bool) (value : Nat) :
    Word.eval ρ { bitsLE := (natBits n value).map LC.ofConst } =
      BitVec.ofNat n value := by
  unfold Word.eval
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_ofFnLE]
  rw [show ({ bitsLE := (natBits n value).map LC.ofConst } : Word n).bitsLE =
    (natBits n value).map LC.ofConst by rfl]
  change LC.eval ρ (getElem ((natBits n value).map LC.ofConst) i hi) = _
  rw [Vector.getElem_map LC.ofConst hi]
  rw [show getElem (natBits n value) i hi = value.testBit i by
    simp [natBits]]
  change LC.eval ρ (LC.ofConst (value.testBit i)) = (BitVec.ofNat n value)[i]
  simp [BitVec.getElem_eq_testBit_toNat, hi]

theorem fromWordResult_natBits_rel {ρ : WF.Valuation}
    (hρ : ρ.int = Witgen.zeroWitness) (s : Witgen.State)
    (width value : Nat) :
    U.Rel ρ (fromWordResult s
      { bitsLE := (natBits width value).map LC.ofConst })
      (BitVec.ofNat width value) := by
  apply fromWordResult_rel hρ
  · exact constWord_eval _ _
  · exact constWord_eval _ _

theorem runAt_sumFixed (s : Witgen.State) (us : Vector (U n) count)
    (value : Nat)
    (hx : (us.toArray.map (fun u : U n => u.intVal)).sum.eval
      Witgen.zeroWitness = value)
    (hvalue : value < 2 ^ (n + Nat.clog 2 count)) :
    StateT.run (Witgen.runAt (U.sumFixed us)) s =
      some ((fromWordResult
        (appendNatBits s (n + Nat.clog 2 count) value)
        { bitsLE := (natBits (n + Nat.clog 2 count) value).map LC.ofConst }
      ).takeLE n (by omega),
      appendNatBits s (n + Nat.clog 2 count) value) := by
  unfold U.sumFixed
  rw [Witgen.runAt_bind, StateT.run_bind]
  rw [runAt_fromInt _ _ _ value hx hvalue]
  rw [Option.bind_eq_bind, Option.bind_some]
  simp [Witgen.runAt]

theorem sumFixedResult_rel {ρ : WF.Valuation}
    (hρ : ρ.int = Witgen.zeroWitness) (s : Witgen.State)
    (n count value : Nat) (hvalue : value < 2 ^ (n + Nat.clog 2 count)) :
    U.Rel ρ ((fromWordResult
      (appendNatBits s (n + Nat.clog 2 count) value)
      { bitsLE := (natBits (n + Nat.clog 2 count) value).map LC.ofConst }
    ).takeLE n (by omega)) (BitVec.ofNat n value) := by
  let wide := fromWordResult
    (appendNatBits s (n + Nat.clog 2 count) value)
    { bitsLE := (natBits (n + Nat.clog 2 count) value).map LC.ofConst }
  have hwide : U.Rel ρ wide (BitVec.ofNat (n + Nat.clog 2 count) value) :=
    fromWordResult_natBits_rel hρ _ _ _
  refine ⟨U.takeLE_valid wide hwide.1 (by omega), ?_⟩
  rw [U.takeLE_eval wide hwide.1 (by omega)]
  have hint : wide.intVal.eval ρ.int = value := by
    rw [U.intVal_eval_eq_eval_toNat wide hwide.1, hwide.2,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvalue]
  rw [hint]
  simp

theorem runAt_sumDoubled32 (s : Witgen.State)
    (us : Array (U 32)) (doubled : Array (LC Int)) (value : Nat)
    (hx : (2 • (us.map (fun u : U 32 => u.intVal)).sum + doubled.sum).eval
      Witgen.zeroWitness = 2 * value)
    (hvalue : value < 2 ^ 35) :
    StateT.run (Witgen.runAt (U.sumDoubled32 us doubled)) s =
      some ((fromWordResult (appendNatBits s 35 value)
        { bitsLE := (natBits 35 value).map LC.ofConst }).takeLE 32 (by omega),
        appendNatBits s 35 value) := by
  unfold U.sumDoubled32
  rw [Witgen.runAt_bind, StateT.run_bind]
  rw [runAt_fromDoubledInt35 _ _ value hx hvalue]
  rw [Option.bind_eq_bind, Option.bind_some]
  simp [Witgen.runAt]

theorem sumDoubled32Result_rel {ρ : WF.Valuation}
    (hρ : ρ.int = Witgen.zeroWitness) (s : Witgen.State)
    (value : Nat) (hvalue : value < 2 ^ 35) :
    U.Rel ρ ((fromWordResult (appendNatBits s 35 value)
      { bitsLE := (natBits 35 value).map LC.ofConst }).takeLE 32 (by omega))
      (BitVec.ofNat 32 value) := by
  let wide := fromWordResult (appendNatBits s 35 value)
    { bitsLE := (natBits 35 value).map LC.ofConst }
  have hwide : U.Rel ρ wide (BitVec.ofNat 35 value) :=
    fromWordResult_natBits_rel hρ _ _ _
  refine ⟨U.takeLE_valid wide hwide.1 (by omega), ?_⟩
  rw [U.takeLE_eval wide hwide.1 (by omega)]
  have hint : wide.intVal.eval ρ.int = value := by
    rw [U.intVal_eval_eq_eval_toNat wide hwide.1, hwide.2,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvalue]
  rw [hint]
  simp

def appendBools (s : Witgen.State) (bits : Array Bool) : Witgen.State :=
  { bools := s.bools ++ bits }

def StableFrom (s : Witgen.State) (w : Word n) : Prop :=
  ∀ extra : Array Bool,
    Word.eval (appendBools s extra).boolWitness w = Word.eval s.boolWitness w

theorem appendBools_assoc (s : Witgen.State) (a b : Array Bool) :
    appendBools (appendBools s a) b = appendBools s (a ++ b) := by
  apply congrArg Witgen.State.mk
  simp [appendBools, Array.append_assoc]

theorem StableFrom.lift (h : StableFrom s w) (extra : Array Bool) :
    StableFrom (appendBools s extra) w := by
  intro later
  rw [appendBools_assoc, h, h]

theorem stable_const (s : Witgen.State) (value : Nat) :
    StableFrom s ({ bitsLE := (natBits n value).map LC.ofConst } : Word n) := by
  intro extra
  exact constWord_eval _ _ |>.trans (constWord_eval _ _).symm

theorem StableFrom.xor {n : Nat} {u v : Word n}
    (hu : StableFrom s u) (hv : StableFrom s v) :
    StableFrom s (u ^^^ v) := by
  intro extra
  simp only [Word.eval_xor]
  rw [hu, hv]

theorem StableFrom.rotateRight {n : Nat} {u : Word n} (hu : StableFrom s u)
    (k : Nat) (hk : k < n) : StableFrom s (u.rotateRight k) := by
  intro extra
  rw [Word.eval_rotateRight _ _ _ hk, Word.eval_rotateRight _ _ _ hk, hu]

theorem StableFrom.shiftRight {n : Nat} {u : Word n}
    (hu : StableFrom s u) (k : Nat) :
    StableFrom s (u >>> k) := by
  intro extra
  simp only [Word.eval_shiftRight]
  rw [hu]

theorem StableFrom.takeLE {m n : Nat} {w : Word n}
    (hw : StableFrom s w) (h : m ≤ n) :
    StableFrom s { bitsLE := Vector.ofFn fun i => w.bitsLE[i.castLE h] } := by
  intro extra
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hin : i < n := hi.trans_le h
  have hbit := congrArg (fun x : BitVec n => x[i]'hin) (hw extra)
  simpa [Word.eval] using hbit

def U.TraceRel (s : Witgen.State) (u : U n) (value : BitVec n) : Prop :=
  u.Valid (canonicalValuation s) ∧
    u.eval (canonicalValuation s) = value ∧
    StableFrom s u.bits

theorem U.TraceRel.lift {n : Nat} {u : U n} {value : BitVec n}
    (h : U.TraceRel s u value) (extra : Array Bool) :
    U.TraceRel (appendBools s extra) u value := by
  have hword := h.2.2 extra
  have hvalid : u.Valid (canonicalValuation (appendBools s extra)) := by
    intro i
    have hold := h.1 i
    change u.intBits[i].eval Witgen.zeroWitness = _ at hold ⊢
    have hbit :
        u.bits.bitsLE[i].eval (appendBools s extra).boolWitness =
          u.bits.bitsLE[i].eval s.boolWitness := by
      simpa [Word.eval] using congrArg (fun x : BitVec n => x[i]) hword
    change u.intBits[i].eval Witgen.zeroWitness =
      (u.bits.bitsLE[i].eval (appendBools s extra).boolWitness).toInt
    rw [hbit]
    change u.intBits[i].eval Witgen.zeroWitness =
      (u.bits.bitsLE[i].eval s.boolWitness).toInt at hold
    exact hold
  refine ⟨hvalid, ?_, h.2.2.lift extra⟩
  rw [U.eval_eq_word_eval u u.bits hvalid rfl]
  change Word.eval (appendBools s extra).boolWitness u.bits = value
  rw [hword]
  exact (U.eval_eq_word_eval u u.bits h.1 rfl).symm.trans h.2.1

theorem fromWordResult_traceRel (s : Witgen.State) (w : Word n)
    (hstable : StableFrom s w) :
    U.TraceRel s (fromWordResult s w) (Word.eval s.boolWitness w) := by
  refine ⟨fromWordResult_valid s w, ?_, hstable⟩
  exact U.eval_eq_word_eval _ w (fromWordResult_valid s w) rfl

theorem sumFixedResult_traceRel (s : Witgen.State) (n count value : Nat)
    (hvalue : value < 2 ^ (n + Nat.clog 2 count)) :
    U.TraceRel (appendNatBits s (n + Nat.clog 2 count) value)
      ((fromWordResult (appendNatBits s (n + Nat.clog 2 count) value)
        { bitsLE := (natBits (n + Nat.clog 2 count) value).map LC.ofConst }
      ).takeLE n (by omega)) (BitVec.ofNat n value) := by
  let state := appendNatBits s (n + Nat.clog 2 count) value
  let wide := fromWordResult state
    { bitsLE := (natBits (n + Nat.clog 2 count) value).map LC.ofConst }
  have hwide0 := fromWordResult_traceRel state
    ({ bitsLE := (natBits (n + Nat.clog 2 count) value).map LC.ofConst } :
      Word (n + Nat.clog 2 count)) (stable_const state value)
  have hwide : U.TraceRel state wide
      (BitVec.ofNat (n + Nat.clog 2 count) value) :=
    ⟨hwide0.1, hwide0.2.1.trans (constWord_eval _ _), hwide0.2.2⟩
  refine ⟨U.takeLE_valid wide hwide.1 (by omega), ?_, ?_⟩
  · rw [U.takeLE_eval wide hwide.1 (by omega)]
    have hint : wide.intVal.eval (canonicalValuation state).int = value := by
      rw [U.intVal_eval_eq_eval_toNat wide hwide.1, hwide.2.1,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvalue]
    rw [hint]
    simp
  · exact hwide.2.2.takeLE (by omega)

theorem U.TraceRel.intVal (h : U.TraceRel s u value) :
    u.intVal.eval Witgen.zeroWitness = value.toNat := by
  change u.intVal.eval (canonicalValuation s).int = value.toNat
  rw [U.intVal_eval_eq_eval_toNat u h.1, h.2.1]

def Vector.TraceRel (s : Witgen.State) (us : Vector (U n) count)
    (values : Vector (BitVec n) count) : Prop :=
  ∀ i : Fin count, U.TraceRel s us[i] values[i]

theorem Vector.TraceRel.lift (h : Vector.TraceRel s us values)
    (extra : Array Bool) : Vector.TraceRel (appendBools s extra) us values :=
  fun i => (h i).lift extra

theorem Vector.TraceRel.getElem! {n count : Nat}
    {us : Vector (U n) count} {values : Vector (BitVec n) count}
    (h : Vector.TraceRel s us values)
    (i : Nat) (hi : i < count) : U.TraceRel s us[i]! values[i]! := by
  simpa [getElem!_pos us i hi, getElem!_pos values i hi] using h ⟨i, hi⟩

theorem U.TraceRel.word_eval (h : U.TraceRel s u value) :
    Word.eval s.boolWitness u.bits = value := by
  exact (U.eval_eq_word_eval u u.bits h.1 rfl).symm.trans h.2.1

theorem runAt_ch2 (s : Witgen.State) {u v w : U n}
    {uv vv wv : BitVec n} (hu : U.TraceRel s u uv)
    (hv : U.TraceRel s v vv) (hw : U.TraceRel s w wv) :
    ∃ out : LC Int,
      StateT.run (Witgen.runAt (U.ch2 u v w)) s = some (out, s) ∧
      out.eval Witgen.zeroWitness =
        2 * ((chBV uv vv wv).toNat : Int) := by
  unfold U.ch2
  rw [Witgen.runAt_bind, StateT.run_bind, runAt_fromWord]
  rw [Option.bind_eq_bind, Option.bind_some]
  rw [Witgen.runAt_bind, StateT.run_bind, runAt_fromWord]
  rw [Option.bind_eq_bind, Option.bind_some]
  let ux := fromWordResult s (u.bits ^^^ v.bits)
  let wx := fromWordResult s (u.bits ^^^ w.bits)
  refine ⟨v.intVal + w.intVal - ux.intVal + wx.intVal, ?_, ?_⟩
  · simp [Witgen.runAt, ux, wx]
  · have hux : U.Rel (canonicalValuation s) ux
        (Word.eval (canonicalValuation s).bool (u.bits ^^^ v.bits)) := by
      apply fromWordResult_rel rfl
      · rfl
      · rfl
    have hwx : U.Rel (canonicalValuation s) wx
        (Word.eval (canonicalValuation s).bool (u.bits ^^^ w.bits)) := by
      apply fromWordResult_rel rfl
      · rfl
      · rfl
    have hresult := optimized_ch2_result hu.1 hv.1 hw.1 hux hwx
    rw [hu.2.1, hv.2.1, hw.2.1] at hresult
    exact hresult

theorem runAt_maj2 (s : Witgen.State) {u v w : U n}
    {uv vv wv : BitVec n} (hu : U.TraceRel s u uv)
    (hv : U.TraceRel s v vv) (hw : U.TraceRel s w wv) :
    ∃ out : LC Int,
      StateT.run (Witgen.runAt (U.maj2 u v w)) s = some (out, s) ∧
      out.eval Witgen.zeroWitness =
        2 * ((majBV uv vv wv).toNat : Int) := by
  unfold U.maj2
  rw [Witgen.runAt_bind, StateT.run_bind, runAt_fromWord]
  rw [Option.bind_eq_bind, Option.bind_some]
  let uvw := fromWordResult s (u.bits ^^^ v.bits ^^^ w.bits)
  refine ⟨u.intVal + v.intVal + w.intVal - uvw.intVal, ?_, ?_⟩
  · simp [Witgen.runAt, uvw]
  · have huv : U.Rel (canonicalValuation s) uvw
        (Word.eval (canonicalValuation s).bool
          (u.bits ^^^ v.bits ^^^ w.bits)) := by
      apply fromWordResult_rel rfl
      · rfl
      · rfl
    have hresult := optimized_maj2_result hu.1 hv.1 hw.1 huv
    rw [hu.2.1, hv.2.1, hw.2.1] at hresult
    exact hresult

def smallSigma0BV (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)

def smallSigma1BV (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)

def smallSigma0Word (x : Word 32) : Word 32 :=
  x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)

def smallSigma1Word (x : Word 32) : Word 32 :=
  x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)

theorem StableFrom.smallSigma0 (h : StableFrom s x) :
    StableFrom s (smallSigma0Word x) := by
  have h7 := h.rotateRight 7 (by decide)
  have h18 := h.rotateRight 18 (by decide)
  have h3 := h.shiftRight 3
  exact (h7.xor h18).xor h3

theorem StableFrom.smallSigma1 (h : StableFrom s x) :
    StableFrom s (smallSigma1Word x) := by
  have h17 := h.rotateRight 17 (by decide)
  have h19 := h.rotateRight 19 (by decide)
  have h10 := h.shiftRight 10
  exact (h17.xor h19).xor h10

theorem eval_smallSigma0Word (ρ : Nat → Bool) (x : Word 32) :
    Word.eval ρ (smallSigma0Word x) = smallSigma0BV (Word.eval ρ x) := by
  simp [smallSigma0Word, smallSigma0BV]

theorem eval_smallSigma1Word (ρ : Nat → Bool) (x : Word 32) :
    Word.eval ρ (smallSigma1Word x) = smallSigma1BV (Word.eval ρ x) := by
  simp [smallSigma1Word, smallSigma1BV]

def scheduleWide (i : Nat) (w : Vector (BitVec 32) 64) : Nat :=
  w[i - 16]!.toNat + (smallSigma0BV w[i - 15]!).toNat +
    w[i - 7]!.toNat + (smallSigma1BV w[i - 2]!).toNat

theorem scheduleWide_lt (i : Nat) (w : Vector (BitVec 32) 64) :
    scheduleWide i w < 2 ^ 34 := by
  have h0 := BitVec.isLt (w[i - 16]!)
  have h1 := BitVec.isLt (smallSigma0BV w[i - 15]!)
  have h2 := BitVec.isLt (w[i - 7]!)
  have h3 := BitVec.isLt (smallSigma1BV w[i - 2]!)
  unfold scheduleWide
  norm_num at h0 h1 h2 h3 ⊢
  omega

theorem scheduleStepBV_eq (i : Nat) (w : Vector (BitVec 32) 64) :
    scheduleStepBV i w = BitVec.ofNat 32 (scheduleWide i w) := by
  unfold scheduleStepBV scheduleWide
  simp only [← Array.sum_toList, List.sum_cons, List.sum_nil]
  change w[i - 16]! + (smallSigma0BV w[i - 15]! +
    (w[i - 7]! + (smallSigma1BV w[i - 2]! + 0))) = _
  calc
    _ = BitVec.ofNat 32 w[i - 16]!.toNat +
        (BitVec.ofNat 32 (smallSigma0BV w[i - 15]!).toNat +
          (BitVec.ofNat 32 w[i - 7]!.toNat +
            BitVec.ofNat 32 (smallSigma1BV w[i - 2]!).toNat)) := by
      simp
    _ = BitVec.ofNat 32 (w[i - 16]!.toNat +
        ((smallSigma0BV w[i - 15]!).toNat +
          (w[i - 7]!.toNat + (smallSigma1BV w[i - 2]!).toNat))) := by
      rw [← BitVec.ofNat_add]
      rw [← BitVec.ofNat_add]
      rw [← BitVec.ofNat_add]
    _ = _ := by congr 1 <;> omega

theorem runAt_scheduleStep (s : Witgen.State)
    {w : Vector (U 32) 64} {wv : Vector (BitVec 32) 64}
    (hw : Vector.TraceRel s w wv) (i : Nat) (hi : i ∈ [16:64]) :
    ∃ out : U 32,
      StateT.run (Witgen.runAt (scheduleStep i w)) s =
        some (out, appendNatBits s 34 (scheduleWide i wv)) ∧
      U.TraceRel (appendNatBits s 34 (scheduleWide i wv)) out
        (scheduleStepBV i wv) := by
  have hi16 : i - 16 < 64 := by grind
  have hi15 : i - 15 < 64 := by grind
  have hi7 : i - 7 < 64 := by grind
  have hi2 : i - 2 < 64 := by grind
  have hw16 := hw.getElem! (i - 16) hi16
  have hw15 := hw.getElem! (i - 15) hi15
  have hw7 := hw.getElem! (i - 7) hi7
  have hw2 := hw.getElem! (i - 2) hi2
  have hbase0 : StableFrom s w[i - 15]!.bits := hw15.2.2
  have hbase1 : StableFrom s w[i - 2]!.bits := hw2.2.2
  have hs0stable : StableFrom s (smallSigma0Word w[i - 15]!.bits) :=
    hbase0.smallSigma0
  have hs1stable : StableFrom s (smallSigma1Word w[i - 2]!.bits) :=
    hbase1.smallSigma1
  let s0 := fromWordResult s (smallSigma0Word w[i - 15]!.bits)
  let s1 := fromWordResult s (smallSigma1Word w[i - 2]!.bits)
  have hs0raw := fromWordResult_traceRel s
    (smallSigma0Word w[i - 15]!.bits) hs0stable
  have hs1raw := fromWordResult_traceRel s
    (smallSigma1Word w[i - 2]!.bits) hs1stable
  have hs0 : U.TraceRel s s0 (smallSigma0BV wv[i - 15]!) := by
    refine ⟨hs0raw.1, ?_, hs0raw.2.2⟩
    rw [hs0raw.2.1]
    rw [eval_smallSigma0Word, hw15.word_eval]
  have hs1 : U.TraceRel s s1 (smallSigma1BV wv[i - 2]!) := by
    refine ⟨hs1raw.1, ?_, hs1raw.2.2⟩
    rw [hs1raw.2.1]
    rw [eval_smallSigma1Word, hw2.word_eval]
  have hs0int : (fromWordResult s
      (Word.rotateRight 7 w[i - 15]!.bits ^^^
        Word.rotateRight 18 w[i - 15]!.bits ^^^
        w[i - 15]!.bits >>> 3)).intVal.eval Witgen.zeroWitness =
      (smallSigma0BV wv[i - 15]!).toNat := by
    change s0.intVal.eval Witgen.zeroWitness = _
    exact hs0.intVal
  have hs1int : (fromWordResult s
      (Word.rotateRight 17 w[i - 2]!.bits ^^^
        Word.rotateRight 19 w[i - 2]!.bits ^^^
        w[i - 2]!.bits >>> 10)).intVal.eval Witgen.zeroWitness =
      (smallSigma1BV wv[i - 2]!).toNat := by
    change s1.intVal.eval Witgen.zeroWitness = _
    exact hs1.intVal
  let out := (fromWordResult (appendNatBits s 34 (scheduleWide i wv))
    { bitsLE := (natBits 34 (scheduleWide i wv)).map LC.ofConst }
    ).takeLE 32 (by omega)
  refine ⟨out, ?_, ?_⟩
  · unfold scheduleStep
    rw [Witgen.runAt_bind, StateT.run_bind, runAt_fromWord]
    rw [Option.bind_eq_bind, Option.bind_some]
    rw [Witgen.runAt_bind, StateT.run_bind, runAt_fromWord]
    rw [Option.bind_eq_bind, Option.bind_some]
    simp only [U.sum4_eq_sumFixed]
    apply runAt_sumFixed
    · simp only [LC.eval_array_sum, Array.map_map]
      simp [scheduleWide, hs0int, hs1int, hw16.intVal, hw7.intVal]
      ring
    · exact scheduleWide_lt i wv
  · rw [scheduleStepBV_eq]
    exact sumFixedResult_traceRel s 32 4 (scheduleWide i wv)
      (scheduleWide_lt i wv)

def bigSigma0BV (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

def bigSigma1BV (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

def bigSigma0Word (x : Word 32) : Word 32 :=
  x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

def bigSigma1Word (x : Word 32) : Word 32 :=
  x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

theorem StableFrom.bigSigma0 (h : StableFrom s x) :
    StableFrom s (bigSigma0Word x) := by
  exact (h.rotateRight 2 (by decide) |>.xor
    (h.rotateRight 13 (by decide))).xor (h.rotateRight 22 (by decide))

theorem StableFrom.bigSigma1 (h : StableFrom s x) :
    StableFrom s (bigSigma1Word x) := by
  exact (h.rotateRight 6 (by decide) |>.xor
    (h.rotateRight 11 (by decide))).xor (h.rotateRight 25 (by decide))

theorem eval_bigSigma0Word (ρ : Nat → Bool) (x : Word 32) :
    Word.eval ρ (bigSigma0Word x) = bigSigma0BV (Word.eval ρ x) := by
  simp [bigSigma0Word, bigSigma0BV]

theorem eval_bigSigma1Word (ρ : Nat → Bool) (x : Word 32) :
    Word.eval ρ (bigSigma1Word x) = bigSigma1BV (Word.eval ρ x) := by
  simp [bigSigma1Word, bigSigma1BV]

theorem coe_bool_eq_ofConst (b : Bool) : (b : LC Bool) = LC.ofConst b := by
  rfl

theorem U.traceRel_bitVec (s : Witgen.State) (x : BitVec n) :
    U.TraceRel s (x : U n) x := by
  refine ⟨U.valid_bitVec x, U.eval_bitVec x, ?_⟩
  have hbits : (x : U n).bits =
      ({ bitsLE := (natBits n x.toNat).map LC.ofConst } : Word n) := by
    apply congrArg Word.mk
    apply Vector.ext
    intro i hi
    simp [natBits, BitVec.getElem_eq_testBit_toNat, coe_bool_eq_ofConst]
  rw [hbits]
  exact stable_const s x.toNat

def RoundState.TraceRel (s : Witgen.State) (r : RoundState (U 32))
    (rv : RoundState (BitVec 32)) : Prop :=
  U.TraceRel s r.1 rv.1 ∧ U.TraceRel s r.2.1 rv.2.1 ∧
  U.TraceRel s r.2.2.1 rv.2.2.1 ∧
  U.TraceRel s r.2.2.2.1 rv.2.2.2.1 ∧
  U.TraceRel s r.2.2.2.2.1 rv.2.2.2.2.1 ∧
  U.TraceRel s r.2.2.2.2.2.1 rv.2.2.2.2.2.1 ∧
  U.TraceRel s r.2.2.2.2.2.2.1 rv.2.2.2.2.2.2.1 ∧
  U.TraceRel s r.2.2.2.2.2.2.2 rv.2.2.2.2.2.2.2

theorem RoundState.TraceRel.lift (h : RoundState.TraceRel s r rv)
    (extra : Array Bool) : RoundState.TraceRel (appendBools s extra) r rv :=
  ⟨h.1.lift extra, h.2.1.lift extra, h.2.2.1.lift extra,
    h.2.2.2.1.lift extra, h.2.2.2.2.1.lift extra,
    h.2.2.2.2.2.1.lift extra, h.2.2.2.2.2.2.1.lift extra,
    h.2.2.2.2.2.2.2.lift extra⟩

def roundEWide (i : Nat) (w : Vector (BitVec 32) 64)
    (r : RoundState (BitVec 32)) : Nat :=
  r.2.2.2.1.toNat + r.2.2.2.2.2.2.2.toNat +
    (bigSigma1BV r.2.2.2.2.1).toNat + k[i]!.toNat + w[i]!.toNat +
    (chBV r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1).toNat

def roundAWide (i : Nat) (w : Vector (BitVec 32) 64)
    (r : RoundState (BitVec 32)) : Nat :=
  r.2.2.2.2.2.2.2.toNat + (bigSigma1BV r.2.2.2.2.1).toNat +
    k[i]!.toNat + w[i]!.toNat + (bigSigma0BV r.1).toNat +
    (chBV r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1).toNat +
    (majBV r.1 r.2.1 r.2.2.1).toNat

theorem roundEWide_lt (i : Nat) (w : Vector (BitVec 32) 64)
    (r : RoundState (BitVec 32)) : roundEWide i w r < 2 ^ 35 := by
  have h0 := BitVec.isLt r.2.2.2.1
  have h1 := BitVec.isLt r.2.2.2.2.2.2.2
  have h2 := BitVec.isLt (bigSigma1BV r.2.2.2.2.1)
  have h3 := BitVec.isLt k[i]!
  have h4 := BitVec.isLt w[i]!
  have h5 := BitVec.isLt
    (chBV r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1)
  unfold roundEWide
  norm_num at h0 h1 h2 h3 h4 h5 ⊢
  omega

theorem roundAWide_lt (i : Nat) (w : Vector (BitVec 32) 64)
    (r : RoundState (BitVec 32)) : roundAWide i w r < 2 ^ 35 := by
  have h0 := BitVec.isLt r.2.2.2.2.2.2.2
  have h1 := BitVec.isLt (bigSigma1BV r.2.2.2.2.1)
  have h2 := BitVec.isLt k[i]!
  have h3 := BitVec.isLt w[i]!
  have h4 := BitVec.isLt (bigSigma0BV r.1)
  have h5 := BitVec.isLt
    (chBV r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1)
  have h6 := BitVec.isLt (majBV r.1 r.2.1 r.2.2.1)
  unfold roundAWide
  norm_num at h0 h1 h2 h3 h4 h5 h6 ⊢
  omega

theorem listBitVec_sum_eq_ofNat (xs : List (BitVec n)) :
    xs.sum = BitVec.ofNat n (xs.map BitVec.toNat).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.sum_cons, List.map_cons]
      calc
        x + xs.sum = x + BitVec.ofNat n (xs.map BitVec.toNat).sum :=
          congrArg (x + ·) ih
        _ = BitVec.ofNat n x.toNat +
            BitVec.ofNat n (xs.map BitVec.toNat).sum := by simp
        _ = _ := (BitVec.ofNat_add _ _).symm

theorem roundStepBV_eq_wide (i : Nat) (w : Vector (BitVec 32) 64)
    (r : RoundState (BitVec 32)) :
    roundStepBV i w r =
      ⟨BitVec.ofNat 32 (roundAWide i w r), r.1, r.2.1, r.2.2.1,
        BitVec.ofNat 32 (roundEWide i w r), r.2.2.2.2.1,
        r.2.2.2.2.2.1, r.2.2.2.2.2.2.1⟩ := by
  unfold roundStepBV roundAWide roundEWide bigSigma0BV bigSigma1BV
  dsimp only
  congr 1
  · rw [← Array.sum_toList, listBitVec_sum_eq_ofNat]
    congr 1
    simp only [Array.toList_map, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    ac_rfl
  · rw [← Array.sum_toList, listBitVec_sum_eq_ofNat]
    congr 1
    simp only [Array.toList_map, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    ac_rfl

theorem runAt_roundStep (s : Witgen.State)
    {w : Vector (U 32) 64} {wv : Vector (BitVec 32) 64}
    (hw : Vector.TraceRel s w wv)
    {r : RoundState (U 32)} {rv : RoundState (BitVec 32)}
    (hr : RoundState.TraceRel s r rv) (i : Nat) (hi : i ∈ [0:64]) :
    ∃ out : RoundState (U 32),
      let stateE := appendNatBits s 35 (roundEWide i wv rv)
      let stateA := appendNatBits stateE 35 (roundAWide i wv rv)
      StateT.run (Witgen.runAt (roundStep i hi (w, r))) s =
          some (out, stateA) ∧
        RoundState.TraceRel stateA out (roundStepBV i wv rv) := by
  have hi64 : i < 64 := by grind
  have hwi := hw.getElem! i hi64
  have hki : U.TraceRel s (k[i] : U 32) k[i]! := by
    simpa [getElem!_pos k i hi64] using U.traceRel_bitVec s k[i]
  let S1word := bigSigma1Word r.2.2.2.2.1.bits
  let S0word := bigSigma0Word r.1.bits
  let S1 := fromWordResult s S1word
  let S0 := fromWordResult s S0word
  have hS1stable : StableFrom s S1word := hr.2.2.2.2.1.2.2.bigSigma1
  have hS0stable : StableFrom s S0word := hr.1.2.2.bigSigma0
  have hS1raw := fromWordResult_traceRel s S1word hS1stable
  have hS0raw := fromWordResult_traceRel s S0word hS0stable
  have hS1 : U.TraceRel s S1 (bigSigma1BV rv.2.2.2.2.1) := by
    refine ⟨hS1raw.1, ?_, hS1raw.2.2⟩
    rw [hS1raw.2.1, eval_bigSigma1Word, hr.2.2.2.2.1.word_eval]
  have hS0 : U.TraceRel s S0 (bigSigma0BV rv.1) := by
    refine ⟨hS0raw.1, ?_, hS0raw.2.2⟩
    rw [hS0raw.2.1, eval_bigSigma0Word, hr.1.word_eval]
  obtain ⟨ch2, hchrun, hchval⟩ :=
    runAt_ch2 s hr.2.2.2.2.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2.1
  obtain ⟨maj2, hmajrun, hmajval⟩ :=
    runAt_maj2 s hr.1 hr.2.1 hr.2.2.1
  let eWide := roundEWide i wv rv
  let aWide := roundAWide i wv rv
  let stateE := appendNatBits s 35 eWide
  let stateA := appendNatBits stateE 35 aWide
  let newE := (fromWordResult stateE
    { bitsLE := (natBits 35 eWide).map LC.ofConst }).takeLE 32 (by omega)
  let newA := (fromWordResult stateA
    { bitsLE := (natBits 35 aWide).map LC.ofConst }).takeLE 32 (by omega)
  have hkiInt : ((k[i] : U 32).intVal.eval Witgen.zeroWitness) =
      k[i]!.toNat := hki.intVal
  have hwiInt : w[i].intVal.eval Witgen.zeroWitness = wv[i]!.toNat := by
    simpa [getElem!_pos wv i hi64] using (hw ⟨i, hi64⟩).intVal
  have hErun : StateT.run (Witgen.runAt
      (U.sum5Doubled1 r.2.2.2.1 r.2.2.2.2.2.2.2 S1 k[i] w[i] ch2)) s =
      some (newE, stateE) := by
    unfold U.sum5Doubled1
    apply runAt_sumDoubled32
    · simp only [LC.eval_nsmul, LC.eval_add, LC.eval_array_sum,
        Array.map_map]
      rw [← Array.sum_toList, ← Array.sum_toList]
      simp only [Array.toList_map, List.map_map, Function.comp_apply,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [hr.2.2.2.1.intVal, hr.2.2.2.2.2.2.2.intVal, hS1.intVal,
        hkiInt, hwiInt, hchval]
      change _ = 2 * (eWide : Int)
      unfold eWide roundEWide
      push_cast
      ring
    · exact roundEWide_lt i wv rv
  have hArun : StateT.run (Witgen.runAt
      (U.sum5Doubled2 r.2.2.2.2.2.2.2 S1 k[i] w[i] S0 ch2 maj2)) stateE =
      some (newA, stateA) := by
    unfold U.sum5Doubled2
    apply runAt_sumDoubled32
    · simp only [LC.eval_nsmul, LC.eval_add, LC.eval_array_sum,
        Array.map_map]
      rw [← Array.sum_toList, ← Array.sum_toList]
      simp only [Array.toList_map, List.map_map, Function.comp_apply,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [hr.2.2.2.2.2.2.2.intVal, hS1.intVal, hkiInt, hwiInt,
        hS0.intVal, hchval, hmajval]
      change _ = 2 * (aWide : Int)
      unfold aWide roundAWide
      push_cast
      ring
    · exact roundAWide_lt i wv rv
  let out : RoundState (U 32) :=
    ⟨newA, r.1, r.2.1, r.2.2.1, newE,
      r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1⟩
  have hErun' : StateT.run (Witgen.runAt
      (U.sum5Doubled1 r.2.2.2.1 r.2.2.2.2.2.2.2
        (fromWordResult s
          (r.2.2.2.2.1.bits.rotateRight 6 ^^^
            r.2.2.2.2.1.bits.rotateRight 11 ^^^
            r.2.2.2.2.1.bits.rotateRight 25)) k[i] w[i] ch2)) s =
      some (newE, stateE) := hErun
  have hArun' : StateT.run (Witgen.runAt
      (U.sum5Doubled2 r.2.2.2.2.2.2.2
        (fromWordResult s
          (r.2.2.2.2.1.bits.rotateRight 6 ^^^
            r.2.2.2.2.1.bits.rotateRight 11 ^^^
            r.2.2.2.2.1.bits.rotateRight 25)) k[i] w[i]
        (fromWordResult s
          (r.1.bits.rotateRight 2 ^^^ r.1.bits.rotateRight 13 ^^^
            r.1.bits.rotateRight 22)) ch2 maj2)) stateE =
      some (newA, stateA) := hArun
  refine ⟨out, ?_, ?_⟩
  · unfold roundStep
    rw [Witgen.runAt_bind, StateT.run_bind, runAt_fromWord]
    rw [Option.bind_eq_bind, Option.bind_some]
    rw [Witgen.runAt_bind, StateT.run_bind, hchrun]
    rw [Option.bind_eq_bind, Option.bind_some]
    rw [Witgen.runAt_bind, StateT.run_bind, runAt_fromWord]
    rw [Option.bind_eq_bind, Option.bind_some]
    rw [Witgen.runAt_bind, StateT.run_bind, hmajrun]
    rw [Option.bind_eq_bind, Option.bind_some]
    simp only [Prod.fst, Prod.snd]
    rw [Witgen.runAt_bind, StateT.run_bind, hErun']
    rw [Option.bind_eq_bind, Option.bind_some]
    rw [Witgen.runAt_bind, StateT.run_bind, hArun']
    rw [Option.bind_eq_bind, Option.bind_some]
    simp [Witgen.runAt, out]
    rfl
  · rw [roundStepBV_eq_wide]
    have hE : U.TraceRel stateE newE (BitVec.ofNat 32 eWide) :=
      sumFixedResult_traceRel s 32 8 eWide (roundEWide_lt i wv rv)
    have hA : U.TraceRel stateA newA (BitVec.ofNat 32 aWide) :=
      sumFixedResult_traceRel stateE 32 8 aWide (roundAWide_lt i wv rv)
    have hrE : RoundState.TraceRel stateE r rv := by
      exact hr.lift (natBits 35 eWide).toArray
    have hrA : RoundState.TraceRel stateA r rv := by
      exact hrE.lift (natBits 35 aWide).toArray
    have hEA : U.TraceRel stateA newE (BitVec.ofNat 32 eWide) :=
      hE.lift (natBits 35 aWide).toArray
    exact ⟨hA, hrA.1, hrA.2.1, hrA.2.2.1, hEA,
      hrA.2.2.2.2.1, hrA.2.2.2.2.2.1, hrA.2.2.2.2.2.2.1⟩

theorem Vector.TraceRel.set! {us : Vector (U n) count}
    {values : Vector (BitVec n) count} (h : Vector.TraceRel s us values)
    {u : U n} {value : BitVec n} (hu : U.TraceRel s u value) (i : Nat) :
    Vector.TraceRel s (us.set! i u) (values.set! i value) := by
  intro j
  rw [show us.set! i u = us.setIfInBounds i u by rfl,
    show values.set! i value = values.setIfInBounds i value by rfl]
  simp only [Fin.getElem_fin, Vector.getElem_setIfInBounds j.isLt]
  split
  · exact hu
  · exact h j

structure ScheduleTrace where
  words : Vector (BitVec 32) 64
  state : Witgen.State

def scheduleTraceStep (i : Nat) (x : ScheduleTrace) : ScheduleTrace :=
  { words := x.words.set! i (scheduleStepBV i x.words)
    state := appendNatBits x.state 34 (scheduleWide i x.words) }

def scheduleTrace (xs : List Nat) (s : Witgen.State)
    (w : Vector (BitVec 32) 64) : ScheduleTrace :=
  xs.foldl (fun x i => scheduleTraceStep i x) { words := w, state := s }

theorem runScheduleLoop (xs : List Nat) (s : Witgen.State)
    {w : Vector (U 32) 64} {wv : Vector (BitVec 32) 64}
    (hw : Vector.TraceRel s w wv)
    (hxs : ∀ i ∈ xs, i ∈ [16:64]) :
    ∃ out : Vector (U 32) 64,
      StateT.run
          (forIn' xs w fun i hi acc => Witgen.runAt (do
            let next ← scheduleStep i acc
            pure PUnit.unit
            pure (ForInStep.yield (acc.set! i next)))) s =
        some (out, (scheduleTrace xs s wv).state) ∧
      Vector.TraceRel (scheduleTrace xs s wv).state out
        (scheduleTrace xs s wv).words := by
  induction xs generalizing s w wv with
  | nil =>
      refine ⟨w, ?_, hw⟩
      rfl
  | cons i xs ih =>
      have hi := hxs i (by simp)
      obtain ⟨next, hrun, hnext⟩ := runAt_scheduleStep s hw i hi
      let state1 := appendNatBits s 34 (scheduleWide i wv)
      let w1 := w.set! i next
      let wv1 := wv.set! i (scheduleStepBV i wv)
      have hw1 : Vector.TraceRel state1 w1 wv1 := by
        exact (hw.lift (natBits 34 (scheduleWide i wv)).toArray).set! hnext i
      obtain ⟨out, hloop, hout⟩ := ih state1 hw1 (fun j hj => hxs j (by simp [hj]))
      refine ⟨out, ?_, ?_⟩
      · simp only [List.forIn'_cons, StateT.run_bind]
        rw [Witgen.runAt_bind, StateT.run_bind, hrun]
        simp only [Option.bind_eq_bind, Option.bind_some, Witgen.runAt_pure,
          StateT.run_pure]
        change StateT.run
          (forIn' xs w1 fun j hj acc => Witgen.runAt (do
            let next ← scheduleStep j acc
            pure PUnit.unit
            pure (ForInStep.yield (acc.set! j next)))) state1 = _
        rw [hloop]
        rfl
      · exact hout

structure RoundsTrace where
  round : RoundState (BitVec 32)
  state : Witgen.State

def roundsTraceStep (i : Nat) (w : Vector (BitVec 32) 64)
    (x : RoundsTrace) : RoundsTrace :=
  let stateE := appendNatBits x.state 35 (roundEWide i w x.round)
  { round := roundStepBV i w x.round
    state := appendNatBits stateE 35 (roundAWide i w x.round) }

def roundsTrace (xs : List Nat) (s : Witgen.State)
    (w : Vector (BitVec 32) 64) (r : RoundState (BitVec 32)) : RoundsTrace :=
  xs.foldl (fun x i => roundsTraceStep i w x) { round := r, state := s }

theorem runRoundsLoop (xs : List Nat) (s : Witgen.State)
    {w : Vector (U 32) 64} {wv : Vector (BitVec 32) 64}
    (hw : Vector.TraceRel s w wv)
    {r : RoundState (U 32)} {rv : RoundState (BitVec 32)}
    (hr : RoundState.TraceRel s r rv)
    (hxs : ∀ i ∈ xs, i ∈ [0:64]) :
    ∃ out : RoundState (U 32),
      StateT.run
          (forIn' xs r fun i hi acc => Witgen.runAt (do
            let next ← roundStep i (hxs i (by simpa using hi)) (w, acc)
            pure PUnit.unit
            pure (ForInStep.yield next))) s =
        some (out, (roundsTrace xs s wv rv).state) ∧
      RoundState.TraceRel (roundsTrace xs s wv rv).state out
        (roundsTrace xs s wv rv).round := by
  induction xs generalizing s w wv r rv with
  | nil =>
      refine ⟨r, ?_, hr⟩
      rfl
  | cons i xs ih =>
      have hi := hxs i (by simp)
      obtain ⟨next, hrun, hnext⟩ := runAt_roundStep s hw hr i hi
      let state1 := appendNatBits
        (appendNatBits s 35 (roundEWide i wv rv)) 35 (roundAWide i wv rv)
      have hw1 : Vector.TraceRel state1 w wv := by
        exact (hw.lift (natBits 35 (roundEWide i wv rv)).toArray).lift
          (natBits 35 (roundAWide i wv rv)).toArray
      obtain ⟨out, hloop, hout⟩ := ih state1 hw1 hnext
        (fun j hj => hxs j (by simp [hj]))
      refine ⟨out, ?_, ?_⟩
      · simp only [List.forIn'_cons, StateT.run_bind]
        rw [Witgen.runAt_bind, StateT.run_bind, hrun]
        simp only [Option.bind_eq_bind, Option.bind_some, Witgen.runAt_pure,
          StateT.run_pure]
        change StateT.run
          (forIn' xs next fun j hj acc => Witgen.runAt (do
            let next ← roundStep j (hxs j (by simp [hj])) (w, acc)
            pure PUnit.unit
            pure (ForInStep.yield next))) state1 = _
        rw [hloop]
        rfl
      · exact hout

def Word.TraceRel (s : Witgen.State) (w : Word n) (value : BitVec n) : Prop :=
  StableFrom s w ∧ Word.eval s.boolWitness w = value

theorem Word.TraceRel.lift (h : Word.TraceRel s w value)
    (extra : Array Bool) : Word.TraceRel (appendBools s extra) w value := by
  refine ⟨h.1.lift extra, ?_⟩
  rw [h.1 extra, h.2]

def Word.VectorTraceRel (s : Witgen.State) (ws : Vector (Word n) count)
    (values : Vector (BitVec n) count) : Prop :=
  ∀ i : Fin count, Word.TraceRel s ws[i] values[i]

theorem runAt_ofFnM_fromWord (s : Witgen.State) (ws : Vector (Word n) count) :
    StateT.run (Witgen.runAt (Vector.ofFnM fun i => U.fromWord ws[i])) s =
      some (Vector.ofFn (fun i => fromWordResult s ws[i]), s) := by
  induction count with
  | zero =>
      simp [Vector.ofFnM_zero, Witgen.runAt]
  | succ count ih =>
      rw [Vector.ofFnM_succ, Witgen.runAt_bind, StateT.run_bind]
      let init : Vector (Word n) count := Vector.ofFn fun i => ws[i.castSucc]
      have hfun : (fun i => U.fromWord init[i]) =
          (fun i : Fin count => U.fromWord ws[i.castSucc]) := by
        funext i
        apply congrArg U.fromWord
        change init[i.val] = ws[i.castSucc]
        unfold init
        rw [Vector.getElem_ofFn]
      have hout : (Vector.ofFn fun i => fromWordResult s init[i]) =
          (Vector.ofFn fun i : Fin count => fromWordResult s ws[i.castSucc]) := by
        apply Vector.ext
        intro i hi
        rw [Vector.getElem_ofFn hi, Vector.getElem_ofFn hi]
        let j : Fin count := ⟨i, hi⟩
        change fromWordResult s init[j] = fromWordResult s ws[j.castSucc]
        congr 1
        change init[j.val] = ws[j.castSucc]
        unfold init
        rw [Vector.getElem_ofFn]
      have hih := ih init
      rw [hfun] at hih
      rw [hout] at hih
      rw [hih]
      rw [Option.bind_eq_bind, Option.bind_some]
      rw [Witgen.runAt_bind, StateT.run_bind, runAt_fromWord]
      rw [Option.bind_eq_bind, Option.bind_some]
      simp [Witgen.runAt, Vector.ofFn_succ]

theorem fromWordVector_traceRel (s : Witgen.State)
    {ws : Vector (Word n) count} {values : Vector (BitVec n) count}
    (h : Word.VectorTraceRel s ws values) :
    Vector.TraceRel s (Vector.ofFn fun i => fromWordResult s ws[i]) values := by
  intro i
  rw [show (Vector.ofFn fun i => fromWordResult s ws[i])[i] =
    fromWordResult s ws[i] by
      simp only [Fin.getElem_fin, Vector.getElem_ofFn]]
  have hi := h i
  refine ⟨fromWordResult_valid s ws[i], ?_, hi.1⟩
  exact (U.eval_eq_word_eval _ ws[i] (fromWordResult_valid s ws[i]) rfl).trans hi.2

theorem U.traceRel_default (s : Witgen.State) :
    U.TraceRel s (default : U n) (0 : BitVec n) := by
  refine ⟨U.valid_default, U.eval_default, ?_⟩
  intro extra
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [Word.eval, BitVec.getElem_ofFnLE]
  change LC.eval (appendBools s extra).boolWitness
      (Vector.replicate n (0 : LC Bool))[i] =
    LC.eval s.boolWitness (Vector.replicate n (0 : LC Bool))[i]
  simp

theorem Vector.traceRel_default (s : Witgen.State) :
    Vector.TraceRel s (default : Vector (U n) count)
      (default : Vector (BitVec n) count) := by
  intro i
  have hu : (default : Vector (U n) count)[i] = (default : U n) := by
    change (Vector.replicate count (default : U n))[i.val] = default
    rw [Vector.getElem_replicate]
  have hv : (default : Vector (BitVec n) count)[i] = (0 : BitVec n) := by
    change (Vector.replicate count (0 : BitVec n))[i.val] = 0
    rw [Vector.getElem_replicate]
  rw [hu, hv]
  exact U.traceRel_default s

theorem Word.VectorTraceRel.getElem! {n count : Nat}
    {ws : Vector (Word n) count} {values : Vector (BitVec n) count}
    (h : Word.VectorTraceRel s ws values)
    (i : Nat) (hi : i < count) : Word.TraceRel s ws[i]! values[i]! := by
  simpa [getElem!_pos ws i hi, getElem!_pos values i hi] using h ⟨i, hi⟩

def initialWordsTrace (xs : List Nat) (init : Vector (BitVec 32) 64)
    (values : Vector (BitVec 32) 16) :
    Vector (BitVec 32) 64 :=
  xs.foldl (fun w i => w.set! i values[i]!) init

theorem runInitialWordsLoop (xs : List Nat) (s : Witgen.State)
    {w : Vector (U 32) 64} {wv : Vector (BitVec 32) 64}
    (hw : Vector.TraceRel s w wv)
    {m : Vector (Word 32) 16} {mv : Vector (BitVec 32) 16}
    (hm : Word.VectorTraceRel s m mv)
    (hxs : ∀ i ∈ xs, i < 16) :
    ∃ out : Vector (U 32) 64,
      StateT.run
          (forIn' xs w fun i hi acc =>
            Witgen.runAt (do
              let next ← U.fromWord m[i]!
              pure PUnit.unit
              pure (ForInStep.yield (acc.set! i next)))) s =
        some (out, s) ∧
      Vector.TraceRel s out (initialWordsTrace xs wv mv) := by
  induction xs generalizing w wv with
  | nil =>
      exact ⟨w, rfl, hw⟩
  | cons i xs ih =>
      have hi16 := hxs i (by simp)
      have hmi := hm.getElem! i hi16
      let next := fromWordResult s m[i]!
      have hnext : U.TraceRel s next mv[i]! := by
        exact ⟨fromWordResult_valid s m[i]!,
          (U.eval_eq_word_eval _ m[i]! (fromWordResult_valid s m[i]!) rfl).trans hmi.2,
          hmi.1⟩
      have hw1 := hw.set! hnext i
      obtain ⟨out, hloop, hout⟩ := ih hw1 (fun j hj => hxs j (by simp [hj]))
      refine ⟨out, ?_, hout⟩
      simp only [List.forIn'_cons, StateT.run_bind]
      rw [Witgen.runAt_bind, StateT.run_bind, runAt_fromWord]
      simp only [Option.bind_eq_bind, Option.bind_some, Witgen.runAt_pure,
        StateT.run_pure]
      change StateT.run
        (forIn' xs (w.set! i next)
          fun j hj acc => Witgen.runAt (do
            let next ← U.fromWord m[j]!
            pure PUnit.unit
            pure (ForInStep.yield (acc.set! j next)))) s = _
      rw [hloop]

theorem RoundState.TraceRel.vector (h : RoundState.TraceRel s r rv) :
    Vector.TraceRel s (roundVector r) (roundVector rv) := by
  intro i
  fin_cases i <;>
    first | exact h.1 | exact h.2.1 | exact h.2.2.1 |
      exact h.2.2.2.1 | exact h.2.2.2.2.1 | exact h.2.2.2.2.2.1 |
      exact h.2.2.2.2.2.2.1 | exact h.2.2.2.2.2.2.2

theorem Vector.TraceRel.push {us : Vector (U n) count}
    {values : Vector (BitVec n) count} (h : Vector.TraceRel s us values)
    {u : U n} {value : BitVec n} (hu : U.TraceRel s u value) :
    Vector.TraceRel s (us.push u) (values.push value) := by
  intro i
  by_cases hi : i.val < count
  · have hieq : i = Fin.castSucc ⟨i.val, hi⟩ := Fin.ext rfl
    change U.TraceRel s ((us.push u).get i) ((values.push value).get i)
    rw [hieq]
    simp only [Vector.get_push_castSucc]
    exact h ⟨i.val, hi⟩
  · have hilast : i.val = count := by omega
    have hieq : i = Fin.last count := Fin.ext hilast
    subst i
    simpa using hu

def finishWide (i : Fin 8) (sv : Vector (BitVec 32) 8)
    (rv : RoundState (BitVec 32)) : Nat :=
  sv[i].toNat + (roundVector rv)[i].toNat

theorem finishWide_lt (i : Fin 8) (sv : Vector (BitVec 32) 8)
    (rv : RoundState (BitVec 32)) : finishWide i sv rv < 2 ^ 33 := by
  have h0 := BitVec.isLt sv[i]
  have h1 := BitVec.isLt (roundVector rv)[i]
  unfold finishWide
  norm_num at h0 h1 ⊢
  omega

def finishState : (count : Nat) → count ≤ 8 → Witgen.State →
    Vector (BitVec 32) 8 → RoundState (BitVec 32) → Witgen.State
  | 0, _, s, _, _ => s
  | count + 1, h, s, sv, rv =>
      let prior := finishState count (by omega) s sv rv
      appendNatBits prior 33 (finishWide ⟨count, by omega⟩ sv rv)

def finishValues (count : Nat) (h : count ≤ 8)
    (sv : Vector (BitVec 32) 8) (rv : RoundState (BitVec 32)) :
    Vector (BitVec 32) count :=
  Vector.ofFn fun i => BitVec.ofNat 32 (finishWide (i.castLE h) sv rv)

theorem runFinishPrefix (count : Nat) (hcount : count ≤ 8)
    (state : Witgen.State)
    {us : Vector (U 32) 8} {sv : Vector (BitVec 32) 8}
    (hus : Vector.TraceRel state us sv)
    {r : RoundState (U 32)} {rv : RoundState (BitVec 32)}
    (hr : RoundState.TraceRel state r rv) :
    ∃ out : Vector (U 32) count,
      StateT.run (Witgen.runAt (Vector.ofFnM fun i =>
        U.sumFixed #v[us[i.castLE hcount],
          (roundVector r)[i.castLE hcount]])) state =
        some (out, finishState count hcount state sv rv) ∧
      Vector.TraceRel (finishState count hcount state sv rv) out
          (finishValues count hcount sv rv) ∧
      Vector.TraceRel (finishState count hcount state sv rv) us sv ∧
      RoundState.TraceRel (finishState count hcount state sv rv) r rv := by
  induction count with
  | zero =>
      refine ⟨#v[], ?_, ?_, hus, hr⟩
      · simp [Vector.ofFnM_zero, Witgen.runAt, finishState]
      · intro i
        exact Fin.elim0 i
  | succ count ih =>
      have hc : count ≤ 8 := by omega
      obtain ⟨pref, hprefRun, hpref, husPrefix, hrPrefix⟩ :=
        ih hc
      have hidx : count < 8 := by omega
      let idx : Fin 8 := ⟨count, hidx⟩
      let wide := finishWide idx sv rv
      let prior := finishState count hc state sv rv
      let nextState := appendNatBits prior 33 wide
      let next := (fromWordResult nextState
        { bitsLE := (natBits 33 wide).map LC.ofConst }).takeLE 32 (by omega)
      have husi := husPrefix idx
      have hrvi := hrPrefix.vector idx
      have hnextRun : StateT.run (Witgen.runAt
          (U.sumFixed #v[us[idx], (roundVector r)[idx]])) prior =
          some (next, nextState) := by
        apply runAt_sumFixed
        · simp only [LC.eval_array_sum, Array.map_map]
          rw [← Array.sum_toList]
          simp only [Array.toList_map, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, Function.comp_apply]
          have huval := husi.intVal
          have hrval := hrvi.intVal
          simp only [huval, hrval]
          simp [finishWide, wide, idx]
        · exact finishWide_lt idx sv rv
      have hnext : U.TraceRel nextState next (BitVec.ofNat 32 wide) :=
        sumFixedResult_traceRel prior 32 2 wide (finishWide_lt idx sv rv)
      refine ⟨pref.push next, ?_, ?_, ?_, ?_⟩
      · rw [Vector.ofFnM_succ, Witgen.runAt_bind, StateT.run_bind]
        have hprefixCircuit :
            (Vector.ofFnM fun i : Fin count =>
              U.sumFixed #v[us[Fin.castLE hcount i.castSucc],
                (roundVector r)[Fin.castLE hcount i.castSucc]]) =
            (Vector.ofFnM fun i : Fin count =>
              U.sumFixed #v[us[Fin.castLE hc i],
                (roundVector r)[Fin.castLE hc i]]) := by
          rfl
        rw [hprefixCircuit]
        rw [hprefRun, Option.bind_eq_bind, Option.bind_some]
        rw [Witgen.runAt_bind, StateT.run_bind]
        change StateT.run (Witgen.runAt
          (U.sumFixed #v[us[idx], (roundVector r)[idx]])) prior >>= _ = _
        rw [hnextRun, Option.bind_eq_bind, Option.bind_some]
        simp [Witgen.runAt, finishState, nextState, prior, wide, idx]
      · have hp := hpref.lift (natBits 33 wide).toArray
        have hv : finishValues (count + 1) hcount sv rv =
            (finishValues count hc sv rv).push (BitVec.ofNat 32 wide) := by
          apply Vector.ext
          intro i hi
          by_cases hilast : i = count
          · subst i
            simp [finishValues, wide, idx]
          · have hilt : i < count := by omega
            rw [Vector.getElem_push_lt]
            simp only [finishValues, Vector.getElem_ofFn]
            congr 2
            exact hilt
        rw [hv]
        exact hp.push hnext
      · exact husPrefix.lift (natBits 33 wide).toArray
      · exact hrPrefix.lift (natBits 33 wide).toArray


end
end Freigen.F2Z.Examples
