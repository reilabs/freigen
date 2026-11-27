import Freigen.F2Z.Gadgets
import Freigen.F2Z.Correctness.WFGen

namespace Freigen.F2Z

open Std.Do
open scoped Std.Do

theorem Nat.intCast_ofBits_eq_sum (f : Fin n → Bool) :
    (Nat.ofBits f : Int) = ∑ k : Fin n, 2 ^ k.val * (f k).toInt := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.ofBits_succ, Nat.cast_add, Nat.cast_mul, Fin.sum_univ_succ]
      simp only [Nat.cast_ofNat, Fin.val_zero, pow_zero, one_mul,
        Fin.val_succ, pow_succ, ih, Finset.mul_sum]
      rw [show ((f 0).toNat : Int) = (f 0).toInt by cases f 0 <;> rfl,
        add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [Function.comp_apply]
      ring

theorem BitVec.intCast_toNat_eq_sum (x : BitVec n) :
    (x.toNat : Int) = ∑ k : Fin n, 2 ^ k.val * (x[k.val]).toInt := by
  rw [← Nat.intCast_ofBits_eq_sum]
  congr 1
  rw [show (fun i : Fin n => x[i.val]) =
      (fun i => x.toNat.testBit i.val) by
    funext i
    exact BitVec.getElem_eq_testBit_toNat x i.val i.isLt]
  exact (Nat.ofBits_testBit x.toNat n |>.trans
    (Nat.mod_eq_of_lt x.isLt)).symm

def U.Rel (valuation : WF.Valuation) (u : U n) (value : BitVec n) : Prop :=
  u.Valid valuation ∧ u.eval valuation = value

def Vector.Rel (valuation : WF.Valuation) (us : Vector (U n) m)
    (values : Vector (BitVec n) m) : Prop :=
  ∀ i : Fin m, U.Rel valuation us[i] values[i]

theorem U.valid_bitVec (w : BitVec n) : ((w : U n).Valid ρ) := by
  intro i
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  change LC.eval ρ.int (LC.ofConst w[i.val].toInt) =
    (LC.eval ρ.bool (LC.ofConst w[i.val])).toInt
  rw [LC.eval_ofConst, LC.eval_ofConst]

theorem U.eval_bitVec (w : BitVec n) : ((w : U n).eval ρ) = w := by
  rw [U.eval_eq_ofFnLE _ (U.valid_bitVec w)]
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_ofFnLE, Fin.getElem_fin, Vector.getElem_ofFn]
  change LC.eval ρ.bool (LC.ofConst w[i]) = w[i]
  rw [LC.eval_ofConst]

@[spec 2000] theorem U.fromWord_sound_rel {w : Word n} :
  ⦃⌜True⌝⦄ Sound.interp ρ (U.fromWord w)
    ⦃⇓ u => ⌜U.Rel ρ u (Word.eval ρ.bool w)⌝⦄ := by
  mvcgen
  intro hbits hvalid
  exact ⟨hvalid, U.eval_eq_word_eval _ _ hvalid hbits⟩

@[spec 2000] theorem U.fromWord_complete_rel {w : Word n} :
  ⦃⌜True⌝⦄ Complete.interp ρ (U.fromWord w)
    ⦃⇓ u => ⌜U.Rel ρ u (Word.eval ρ.bool w)⌝⦄ := by
  mvcgen
  intro hbits hvalid
  exact ⟨hvalid, U.eval_eq_word_eval _ _ hvalid hbits⟩

theorem Vector.Rel.eval_eq {n m : Nat} {valuation : WF.Valuation}
    {us : Vector (U n) m} {values : Vector (BitVec n) m}
    (h : Vector.Rel valuation us values) :
    us.map (·.eval valuation) = values := by
  apply Vector.ext
  intro i hi
  simpa using (h ⟨i, hi⟩).2

theorem Vector.Rel.valid {n m : Nat} {valuation : WF.Valuation}
    {us : Vector (U n) m} {values : Vector (BitVec n) m}
    (h : Vector.Rel valuation us values) :
    ∀ i : Fin m, us[i].Valid valuation := fun i => (h i).1

theorem U.Rel.word_eval (h : U.Rel ρ u value) :
    Word.eval ρ.bool u.bits = value :=
  (U.eval_eq_word_eval u u.bits h.1 rfl).symm.trans h.2

theorem U.Rel.rotateXorShift {n a b c : Nat}
    {u out : U n} {value : BitVec n}
    (ha : a < n) (hb : b < n) (hu : U.Rel ρ u value)
    (hout : U.Rel ρ out (Word.eval ρ.bool
      (u.bits.rotateRight a ^^^ u.bits.rotateRight b ^^^ (u.bits >>> c)))) :
    U.Rel ρ out (value.rotateRight a ^^^ value.rotateRight b ^^^
      (value >>> c : BitVec n)) := by
  refine ⟨hout.1, ?_⟩
  rw [hout.2]
  simp only [Word.eval_xor, Word.eval_shiftRight,
    Word.eval_rotateRight (n := n) _ _ a ha,
    Word.eval_rotateRight (n := n) _ _ b hb, hu.word_eval]

theorem U.Rel.rotateXor3 {n a b c : Nat}
    {u out : U n} {value : BitVec n}
    (ha : a < n) (hb : b < n) (hc : c < n) (hu : U.Rel ρ u value)
    (hout : U.Rel ρ out (Word.eval ρ.bool
      (u.bits.rotateRight a ^^^ u.bits.rotateRight b ^^^
        u.bits.rotateRight c))) :
    U.Rel ρ out (value.rotateRight a ^^^ value.rotateRight b ^^^
      value.rotateRight c) := by
  refine ⟨hout.1, ?_⟩
  rw [hout.2]
  simp only [Word.eval_xor,
    Word.eval_rotateRight (n := n) _ _ a ha,
    Word.eval_rotateRight (n := n) _ _ b hb,
    Word.eval_rotateRight (n := n) _ _ c hc, hu.word_eval]

theorem U.Rel.refl (h : u.Valid ρ) : U.Rel ρ u (u.eval ρ) :=
  ⟨h, rfl⟩

theorem U.Rel.intVal (h : U.Rel ρ u value) :
    u.intVal.eval ρ.int = value.toNat :=
  (U.intVal_eval_eq_eval_toNat u h.1).trans
    (congrArg (fun x => (x.toNat : Int)) h.2)

theorem U.Rel.ternary {u v w out : U n} {bits : Vector (LC Bool) n}
    (f : Bool → Bool → Bool → Bool)
    (hu : u.Valid ρ) (hv : v.Valid ρ) (hw : w.Valid ρ)
    (hbits : ∀ i : Fin n, bits[i].eval ρ.bool =
      f (u.bits[i].eval ρ.bool) (v.bits[i].eval ρ.bool)
        (w.bits[i].eval ρ.bool))
    (hout : U.Rel ρ out (Word.eval ρ.bool { bitsLE := bits })) :
    U.Rel ρ out (BitVec.ofFnLE fun i =>
      f (u.eval ρ)[i] (v.eval ρ)[i] (w.eval ρ)[i]) := by
  refine ⟨hout.1, hout.2.trans ?_⟩
  rw [U.eval_eq_ofFnLE u hu, U.eval_eq_ofFnLE v hv,
    U.eval_eq_ofFnLE w hw]
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hb := hbits ⟨i, hi⟩
  change LC.eval ρ.bool bits[i] = f
    (LC.eval ρ.bool u.bits.bitsLE[i])
    (LC.eval ρ.bool v.bits.bitsLE[i])
    (LC.eval ρ.bool w.bits.bitsLE[i]) at hb
  simpa [Word.eval] using hb

theorem Vector.Rel.getElem! {n m : Nat} {us : Vector (U n) m}
    {values : Vector (BitVec n) m} (h : Vector.Rel ρ us values)
    {i : Nat} (hi : i < m) : U.Rel ρ us[i]! values[i]! := by
  rw [getElem!_pos us i hi, getElem!_pos values i hi]
  exact h ⟨i, hi⟩

theorem Vector.Rel.refl {n m : Nat} {valuation : WF.Valuation}
    {us : Vector (U n) m} (h : ∀ i : Fin m, us[i].Valid valuation) :
    Vector.Rel valuation us (us.map (·.eval valuation)) :=
  fun i => ⟨h i, by simp⟩

theorem Vector.Rel.set! {n m : Nat} {valuation : WF.Valuation}
    {us : Vector (U n) m} {values : Vector (BitVec n) m}
    {u : U n} {value : BitVec n} (h : Vector.Rel valuation us values)
    (hx : U.Rel valuation u value) (i : Nat) :
    Vector.Rel valuation (us.set! i u) (values.set! i value) := by
  intro j
  rw [show us.set! i u = us.setIfInBounds i u by rfl,
    show values.set! i value = values.setIfInBounds i value by rfl]
  simp only [Fin.getElem_fin, Vector.getElem_setIfInBounds j.isLt]
  split
  · exact hx
  · exact h j

theorem U.eval_default : (default : U n).eval ρ = 0 := by
  rw [U.eval_eq_ofFnLE _ U.valid_default]
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_ofFnLE]
  change LC.eval ρ.bool (Vector.replicate n (0 : LC Bool))[i] =
    (0 : BitVec n)[i]
  simp only [Vector.getElem_replicate, LC.eval_zero]
  rw [show (0 : BitVec n) = BitVec.ofNat n 0 by rfl,
    BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.zero_mod]
  have hzero : (0 : Bool) = false := rfl
  rw [hzero]
  simp [Nat.testBit]

theorem U.valid_getElem! {xs : Vector (U n) m}
    (h : ∀ i : Fin m, xs[i].Valid ρ) {j : Nat} (hj : j < m) :
    xs[j]!.Valid ρ := by
  rw [getElem!_pos xs j hj]
  exact h ⟨j, hj⟩

theorem U.allValid_set! {xs : Vector (U n) m} {x : U n}
    (hxs : ∀ i : Fin m, xs[i].Valid valuation) (hx : x.Valid valuation)
    (i : Nat) : ∀ j : Fin m, (xs.set! i x)[j].Valid valuation := by
  intro j
  rw [show xs.set! i x = xs.setIfInBounds i x by rfl]
  simp only [Fin.getElem_fin, Vector.getElem_setIfInBounds j.isLt]
  split
  · exact hx
  · exact hxs j

theorem Array.mapM_push [Monad m] [LawfulMonad m]
    (f : α → m β) (xs : Array α) (x : α) :
    (xs.push x).mapM f = (do
      let ys ← xs.mapM f
      let y ← f x
      pure (ys.push y)) := by
  simp only [Array.mapM_eq_mapM_toList, Array.toList_push,
    List.mapM_append, List.mapM_cons, List.mapM_nil]
  simp

theorem Vector.mapM_push [Monad m] [LawfulMonad m]
    (f : α → m β) (xs : Vector α n) (x : α) :
    (xs.push x).mapM f = (do
      let ys ← xs.mapM f
      let y ← f x
      pure (ys.push y)) := by
  apply Vector.map_toArray_inj.mp
  rw [Vector.toArray_mapM, Vector.toArray_push, Array.mapM_push]
  rw [← Vector.toArray_mapM (f := f) (xs := xs)]
  rw [bind_map_left]
  simp only [← bind_pure_comp, bind_assoc, pure_bind,
    Vector.toArray_push]

theorem Vector.mapM_eq_ofFnM [Monad m] [LawfulMonad m]
    (xs : Vector α n) (f : α → m β) :
    xs.mapM f = Vector.ofFnM (fun i => f xs[i]) := by
  induction n with
  | zero =>
      rw [show xs = #v[] from Vector.eq_empty]
      simp
  | succ n ih =>
      obtain ⟨init, last, rfl⟩ := Vector.exists_push (xs := xs)
      rw [Vector.mapM_push, Vector.ofFnM_succ]
      have hinit : (fun i : Fin n => f (init.push last)[i.castSucc]) =
          (fun i : Fin n => f init[i]) := by funext i; simp
      rw [hinit, ← ih]
      simp

theorem Triple.vectorOfFnM [Monad m] [WPMonad m ps]
    {f : Fin n → m α} {R : Fin n → α → Prop}
    (hstep : ∀ i, ⦃⌜True⌝⦄ f i ⦃⇓ x => ⌜R i x⌝⦄) :
    ⦃⌜True⌝⦄ Vector.ofFnM f ⦃⇓ xs => ⌜∀ i, R i xs[i]⌝⦄ := by
  apply Triple.iff_conseq.mp (Std.Do.Spec.vector_ofFnM
    (E := ExceptConds.false) (inv := fun i hi xs =>
      ⌜∀ j : Fin i, R (j.castLE hi) xs[j]⌝) ?_) (by simp) (by simp)
  intro i hi xs
  mvcgen [hstep]
  case vc1 hxs x =>
    mframe
    rename_i hx
    mpure_intro
    intro j
    by_cases hj : j.val < i
    · let ji : Fin i := ⟨j, hj⟩
      have hcast : ji.castLE (Nat.le_of_lt hi) =
          j.castLE (Nat.succ_le_of_lt hi) := Fin.ext rfl
      rw [← hcast]
      simpa [Vector.getElem_push, hj, ji] using hxs ji
    · have hj' : j = Fin.last i := Fin.ext (by simp; omega)
      subst j
      have hlast : (Fin.last i).castLE (Nat.succ_le_of_lt hi) =
          ⟨i, hi⟩ := Fin.ext rfl
      rw [hlast]
      simpa using hx

theorem Sound.vectorOfFnM {f : Fin n → Circuit α}
    {R : Fin n → α → Prop}
    (hstep : ∀ i, ⦃⌜True⌝⦄ Sound.interp ρ (f i) ⦃⇓ x => ⌜R i x⌝⦄) :
    ⦃⌜True⌝⦄ Sound.interp ρ (Vector.ofFnM f)
      ⦃⇓ xs => ⌜∀ i, R i xs[i]⌝⦄ := by
  rw [Sound.interp_ofFnM]
  exact Triple.vectorOfFnM hstep

theorem Complete.vectorOfFnM {f : Fin n → Circuit α}
    {R : Fin n → α → Prop}
    (hstep : ∀ i, ⦃⌜True⌝⦄ Complete.interp ρ (f i) ⦃⇓ x => ⌜R i x⌝⦄) :
    ⦃⌜True⌝⦄ Complete.interp ρ (Vector.ofFnM f)
      ⦃⇓ xs => ⌜∀ i, R i xs[i]⌝⦄ := by
  rw [Complete.interp_ofFnM]
  exact Triple.vectorOfFnM hstep

theorem U.fromWord_wf_full :
    WF.GadgetSpec
      (fun lv rv (l r : Word n) => ∀ i : Fin n,
        WF.LCEq lv.bool rv.bool l.bitsLE[i] r.bitsLE[i])
      U.fromWord
      (fun lv rv l r =>
        (∀ i : Fin n, WF.LCEq lv.bool rv.bool
          l.bits.bitsLE[i] r.bits.bitsLE[i]) ∧
        (∀ i : Fin n, WF.LCEq lv.int rv.int l.intBits[i] r.intBits[i]) ∧
        WF.LCEq lv.int rv.int l.intVal r.intVal) := by
  unfold WF.GadgetSpec
  intro left right
  unfold U.fromWord
  apply WF.Rel.forIn'_range_f2z_set!_bind
  · intro lv rv h i
    simp [WF.LCEq]
  · intro i hi lv rv h
    exact h ⟨i, by grind⟩
  · grind
  · intro A leftInts rightInts hA
    apply WF.Rel.pure
    intro lv rv h
    have hp := hA lv rv h
    exact ⟨hp.1, hp.2, WF.LCEq.uIntVal hp.2⟩

theorem U.fromInt_wf_full :
    WF.GadgetSpec
      (fun lv rv (l r : LC ℤ) => WF.LCEq lv.int rv.int l r)
      (U.fromInt n)
      (fun lv rv l r =>
        (∀ i : Fin n, WF.LCEq lv.bool rv.bool
          l.bits.bitsLE[i] r.bits.bitsLE[i]) ∧
        (∀ i : Fin n, WF.LCEq lv.int rv.int l.intBits[i] r.intBits[i]) ∧
        WF.LCEq lv.int rv.int l.intVal r.intVal) := by
  wfgen' using [U.fromWord_wf_full] unfold [U.fromInt]
  case vc1 hrel =>
    rcases hrel with ⟨_, values, _, _, hleft, hright⟩
    exact (hleft i.val i.isLt).trans (hright i.val i.isLt).symm
  case vc2 h =>
    unfold WF.LCEq at h
    simp only [WF.evalArgs]
    rw [h]
  case vc3 h =>
    unfold WF.ArgsEq
    simp only [WF.evalArgs]
    exact congrArg (fun x => h![x]) h

def U.WFRel (lv rv : WF.Valuation) (l r : U n) : Prop :=
  WF.LCEq lv.int rv.int l.intVal r.intVal ∧
  ∀ i : Fin n, WF.LCEq lv.bool rv.bool l.bits.bitsLE[i] r.bits.bitsLE[i]

theorem U.wfRel_bitVec (lv rv : WF.Valuation) (x : BitVec n) :
    U.WFRel lv rv (x : U n) (x : U n) := by
  have hbit (v : Nat → Bool) (j : Fin n) :
      LC.eval v ((x : U n).bits.bitsLE[j]) = x[j] := by
    simp only [Vector.getElem_ofFn, Fin.getElem_fin, LC.eval_ofConst]
  have hint (v : Nat → ℤ) (j : Fin n) :
      LC.eval v ((x : U n).intBits[j]) = x[j].toInt := by
    simp only [Vector.getElem_ofFn, Fin.getElem_fin, LC.eval_ofConst]
  unfold U.WFRel WF.LCEq U.intVal
  constructor
  · rw [LC.eval_sum, LC.eval_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [LC.eval_nsmul, hint]
  · intro i
    rw [hbit, hbit]

theorem U.fromWord_wf_rel :
    WF.GadgetSpec
      (fun lv rv (l r : Word n) => ∀ i : Fin n,
        WF.LCEq lv.bool rv.bool l[i] r[i]) U.fromWord U.WFRel := by
  intro left right
  apply WF.Rel.mono (U.fromWord_wf_full left right)
  exact fun _ _ _ _ h => ⟨h.2.2, h.1⟩

theorem U.wfRel_default (lv rv : WF.Valuation) :
    U.WFRel lv rv (default : U n) default := by
  unfold U.WFRel WF.LCEq U.intVal
  constructor
  · rw [LC.eval_sum, LC.eval_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [LC.eval_nsmul, LC.eval_nsmul]
    have hz : (default : U n).intBits[i] = 0 := by
      change (Vector.replicate n (0 : LC ℤ))[i] = 0
      simp
    rw [hz, LC.eval_zero, LC.eval_zero]
  · intro i
    have hz : (default : U n).bits.bitsLE[i] = 0 := by
      change (Vector.replicate n (0 : LC Bool))[i] = 0
      simp
    rw [hz, LC.eval_zero, LC.eval_zero]

theorem U.vector_default_get (i : Fin m) :
    (default : Vector (U n) m)[i] = default := by
  change (Vector.replicate m (default : U n))[i] = default
  simp

theorem U.vector_default_wfRel (lv rv : WF.Valuation) :
    WF.VectorRel U.WFRel lv rv
      (default : Vector (U n) m) default := by
  intro i
  simpa only [U.vector_default_get] using U.wfRel_default lv rv

theorem Vector.Rel.default {n m : Nat} {valuation : WF.Valuation} :
    Vector.Rel valuation (Inhabited.default : Vector (U n) m)
      (Inhabited.default : Vector (BitVec n) m) := by
  intro i
  rw [U.vector_default_get]
  change U.Rel valuation (Inhabited.default : U n)
    ((Vector.replicate m (Inhabited.default : BitVec n)).get i)
  rw [Vector.get_replicate]
  exact ⟨U.valid_default, U.eval_default⟩

def U.ternaryHints (f : Bool → Bool → Bool → Bool)
    (u v w : U n) : Circuit (Vector (LC Bool) n) :=
  Vector.ofFnM fun i => do
    let out ← hint h![u.bits[i], v.bits[i], w.bits[i]]
      fun h![x, y, z] => pure #v[f x y z]
    pure out[0]

@[spec] theorem U.ternaryHints_complete
    (f : Bool → Bool → Bool → Bool) (u v w : U n) :
    ⦃⌜True⌝⦄ Complete.interp valuation (U.ternaryHints f u v w)
    ⦃⇓ out => ⌜∀ i : Fin n, out[i].eval valuation.bool =
      f (u.bits[i].eval valuation.bool) (v.bits[i].eval valuation.bool)
        (w.bits[i].eval valuation.bool)⌝⦄ := by
  unfold U.ternaryHints
  mvcgen invariants
  · fun i hi out => ⌜∀ j : Fin i, out[j].eval valuation.bool =
      f (u.bits[j.castLE hi].eval valuation.bool)
        (v.bits[j.castLE hi].eval valuation.bool)
        (w.bits[j.castLE hi].eval valuation.bool)⌝
  case vc1 =>
    rename_i i hi out
    simp only [WF.evalArgs, WF.interpHint, Free.interp_pure]
    intro hprefix
    let ix : Fin n := ⟨i, hi⟩
    refine ⟨#v[f (u.bits[ix].eval valuation.bool)
      (v.bits[ix].eval valuation.bool) (w.bits[ix].eval valuation.bool)],
      rfl, ?_⟩
    intro j
    by_cases hj : j.val < i
    · have hcast : (⟨j.val, hj⟩ : Fin i).castLE (Nat.le_of_lt hi) =
          j.castLE (Nat.succ_le_of_lt hi) := Fin.ext rfl
      simpa [Vector.getElem_push, hj, hcast] using hprefix ⟨j.val, hj⟩
    · have hjEq : j.val = i := by omega
      have hcast : j.castLE (Nat.succ_le_of_lt hi) = ix := Fin.ext hjEq
      rw [hcast]
      simp [hjEq, ix]
  case vc2 => simp
  case vc3 => simp

theorem WF.ArgsEq.three
    {xL xR yL yR zL zR : LC Bool}
    (hx : LCEq lv.bool rv.bool xL xR)
    (hy : LCEq lv.bool rv.bool yL yR)
    (hz : LCEq lv.bool rv.bool zL zR) :
    ArgsEq lv rv h![xL, yL, zL] h![xR, yR, zR] := by
  unfold ArgsEq
  simp only [evalArgs]
  unfold LCEq at hx hy hz
  rw [hx, hy, hz]

theorem U.ternaryHints_wf (f : Bool → Bool → Bool → Bool) :
    WF.GadgetSpec
      (fun lv rv (l r : U n × U n × U n) =>
        U.WFRel lv rv l.1 r.1 ∧ U.WFRel lv rv l.2.1 r.2.1 ∧
          U.WFRel lv rv l.2.2 r.2.2)
      (fun x => U.ternaryHints f x.1 x.2.1 x.2.2)
      (WF.VectorRel fun lv rv l r => WF.LCEq lv.bool rv.bool l r) := by
  unfold WF.GadgetSpec
  intro left right
  unfold U.ternaryHints
  apply WF.Rel.mono (WF.Rel.vectorOfFnM
    (S := fun _ lv rv l r => WF.LCEq lv.bool rv.bool l r) ?_)
  · exact fun _ _ _ _ h => h.2
  · intro i P _ _ hP
    wfgen'
    case vc1 hrel =>
      rcases hrel with ⟨_, values, _, _, hleft, hright⟩
      exact (hleft j.val j.isLt).trans (hright j.val j.isLt).symm
    case vc2 => exact ⟨Nat.le_refl 0, Nat.zero_lt_one, rfl⟩
    case vc3 h =>
      have hin := hP leftVal rightVal h
      have hu := hin.1.2 i
      have hv := hin.2.1.2 i
      have hw := hin.2.2.2 i
      change WF.LCEq _ _ left.1.bits[i] right.1.bits[i] at hu
      change WF.LCEq _ _ left.2.1.bits[i] right.2.1.bits[i] at hv
      change WF.LCEq _ _ left.2.2.bits[i] right.2.2.bits[i] at hw
      have heq := WF.ArgsEq.three hu hv hw
      unfold WF.ArgsEq at heq
      rw [heq]
    case vc4 h =>
      have hin := hP leftVal rightVal h
      have hu := hin.1.2 i
      have hv := hin.2.1.2 i
      have hw := hin.2.2.2 i
      change WF.LCEq _ _ left.1.bits[i] right.1.bits[i] at hu
      change WF.LCEq _ _ left.2.1.bits[i] right.2.1.bits[i] at hv
      change WF.LCEq _ _ left.2.2.bits[i] right.2.2.bits[i] at hw
      exact WF.ArgsEq.three hu hv hw

theorem WF.VectorRel.set! {R : WF.Post α}
    {left right : Vector α n} {xL xR : α}
    (h : WF.VectorRel R lv rv left right)
    (hx : R lv rv xL xR) (i : Nat) :
    WF.VectorRel R lv rv (left.set! i xL) (right.set! i xR) := by
  intro j
  rw [show left.set! i xL = left.setIfInBounds i xL by rfl,
    show right.set! i xR = right.setIfInBounds i xR by rfl]
  simp only [Fin.getElem_fin, Vector.getElem_setIfInBounds j.isLt]
  split
  · exact hx
  · exact h j

theorem WF.VectorRel.getElem! [Inhabited α] {R : WF.Post α}
    {left right : Vector α n}
    (h : WF.VectorRel R lv rv left right) {i : Nat} (hi : i < n) :
    R lv rv left[i]! right[i]! := by
  rw [getElem!_pos left i hi, getElem!_pos right i hi]
  exact h ⟨i, hi⟩

def Word.WFRel (lv rv : WF.Valuation) (l r : Word n) : Prop :=
  ∀ i : Fin n, WF.LCEq lv.bool rv.bool l.bitsLE[i] r.bitsLE[i]

theorem U.WFRel.bits (h : U.WFRel lv rv l r) :
    Word.WFRel lv rv l.bits r.bits :=
  h.2

attribute [grind =>] U.WFRel.bits

theorem Word.WFRel.xor {uL uR vL vR : Word n}
    (hu : Word.WFRel lv rv uL uR)
    (hv : Word.WFRel lv rv vL vR) :
    Word.WFRel lv rv (uL ^^^ vL) (uR ^^^ vR) := by
  intro i
  unfold Word.WFRel at hu hv
  unfold WF.LCEq at hu hv ⊢
  change LC.eval lv.bool (uL ^^^ vL).bitsLE[i.val] = _
  rw [show uL ^^^ vL =
      { bitsLE := Vector.zipWith (· + ·) uL.bitsLE vL.bitsLE } by rfl,
    show uR ^^^ vR =
      { bitsLE := Vector.zipWith (· + ·) uR.bitsLE vR.bitsLE } by rfl]
  change LC.eval lv.bool
      (Vector.zipWith (· + ·) uL.bitsLE vL.bitsLE)[i.val] =
    LC.eval rv.bool
      (Vector.zipWith (· + ·) uR.bitsLE vR.bitsLE)[i.val]
  simp only [Vector.getElem_zipWith i.isLt, LC.eval_add]
  have hui := hu i
  have hvi := hv i
  change LC.eval lv.bool uL.bitsLE[i.val] =
    LC.eval rv.bool uR.bitsLE[i.val] at hui
  change LC.eval lv.bool vL.bitsLE[i.val] =
    LC.eval rv.bool vR.bitsLE[i.val] at hvi
  rw [hui, hvi]

theorem Word.WFRel.rotateRight (h : Word.WFRel lv rv uL uR) (k : Nat) :
    Word.WFRel lv rv (uL.rotateRight k) (uR.rotateRight k) := by
  intro i
  unfold WF.LCEq
  change LC.eval lv.bool (uL.rotateRight k).bitsLE[i.val] =
    LC.eval rv.bool (uR.rotateRight k).bitsLE[i.val]
  rw [Word.rotateRight_getElem uL k i i.isLt,
    Word.rotateRight_getElem uR k i i.isLt]
  split
  · exact h ⟨_, by omega⟩
  · exact h ⟨_, by omega⟩

theorem Word.WFRel.shiftRight (h : Word.WFRel lv rv uL uR) (k : Nat) :
    Word.WFRel lv rv (uL >>> k) (uR >>> k) := by
  intro i
  unfold WF.LCEq
  change LC.eval lv.bool (uL >>> k).bitsLE[i.val] =
    LC.eval rv.bool (uR >>> k).bitsLE[i.val]
  rw [Word.shiftRight_getElem uL k i i.isLt,
    Word.shiftRight_getElem uR k i i.isLt]
  split
  · exact h ⟨_, by omega⟩
  · simp

def U.sumFixed (us : Vector (U n) m) : Circuit (U n) := do
  let wide ← U.fromInt (n + Nat.clog 2 m)
    (us.toArray.map (fun x => x.intVal)).sum
  pure (wide.takeLE n (by omega))

theorem U.sum_toArray_eq_sumFixed (us : Vector (U n) m) :
    U.sum us.toArray = U.sumFixed us := by
  cases us with
  | mk array hsize =>
    cases hsize
    unfold U.sum U.sumFixed
    apply bind_congr
    intro wide
    exact congrArg (fun x : U n => (pure x : Circuit (U n)))
      (U.takeLE_eq_truncate wide (by omega)).symm

@[simp] theorem U.sum2_eq_sumFixed (a b : U n) :
    U.sum #[a, b] = U.sumFixed #v[a, b] :=
  U.sum_toArray_eq_sumFixed #v[a, b]
@[simp] theorem U.sum4_eq_sumFixed (a b c d : U n) :
    U.sum #[a, b, c, d] = U.sumFixed #v[a, b, c, d] :=
  U.sum_toArray_eq_sumFixed #v[a, b, c, d]
@[simp] theorem U.sum6_eq_sumFixed (a b c d e f : U n) :
    U.sum #[a, b, c, d, e, f] = U.sumFixed #v[a, b, c, d, e, f] :=
  U.sum_toArray_eq_sumFixed #v[a, b, c, d, e, f]
@[simp] theorem U.sum7_eq_sumFixed (a b c d e f g : U n) :
    U.sum #[a, b, c, d, e, f, g] = U.sumFixed #v[a, b, c, d, e, f, g] :=
  U.sum_toArray_eq_sumFixed #v[a, b, c, d, e, f, g]

theorem U.sumFixed_sound {us : Vector (U n) m}
    (hvalid : ∀ i : Fin m, us[i].Valid ρ) :
    ⦃⌜True⌝⦄ Sound.interp ρ (U.sumFixed us)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      out.eval ρ = (us.toArray.map (·.eval ρ)).sum⌝⦄ := by
  rw [← U.sum_toArray_eq_sumFixed]
  exact U.sum_sound fun u hu => by
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hu
    exact hvalid ⟨i, by simpa using hi⟩

theorem U.sumFixed_complete {us : Vector (U n) m}
    (hvalid : ∀ i : Fin m, us[i].Valid ρ) :
    ⦃⌜True⌝⦄ Complete.interp ρ (U.sumFixed us)
    ⦃⇓ out => ⌜out.Valid ρ ∧
      out.eval ρ = (us.toArray.map (·.eval ρ)).sum⌝⦄ := by
  rw [← U.sum_toArray_eq_sumFixed]
  exact U.sum_complete fun u hu => by
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hu
    exact hvalid ⟨i, by simpa using hi⟩

private theorem U.sumPair_result {a b out : U n} {av bv : BitVec n}
    (ha : U.Rel ρ a av) (hb : U.Rel ρ b bv)
    (hout : out.Valid ρ ∧ out.eval ρ =
      (#v[a, b].toArray.map (·.eval ρ)).sum) :
    U.Rel ρ out (av + bv) := by
  refine ⟨hout.1, ?_⟩
  rw [hout.2]
  simp [ha.2, hb.2]

theorem U.sumPair_sound {a b : U n} {av bv : BitVec n}
    (ha : U.Rel ρ a av) (hb : U.Rel ρ b bv) :
    ⦃⌜True⌝⦄ Sound.interp ρ (U.sumFixed #v[a, b])
      ⦃⇓ out => ⌜U.Rel ρ out (av + bv)⌝⦄ := by
  apply Triple.iff_conseq.mp (U.sumFixed_sound fun i => by
    fin_cases i <;> first | exact ha.1 | exact hb.1) (by simp)
  simp only [PostCond.entails, SPred.entails_nil]
  exact ⟨fun _ h => U.sumPair_result ha hb h, ExceptConds.entails.refl _⟩

theorem U.sumPair_complete {a b : U n} {av bv : BitVec n}
    (ha : U.Rel ρ a av) (hb : U.Rel ρ b bv) :
    ⦃⌜True⌝⦄ Complete.interp ρ (U.sumFixed #v[a, b])
      ⦃⇓ out => ⌜U.Rel ρ out (av + bv)⌝⦄ := by
  apply Triple.iff_conseq.mp (U.sumFixed_complete fun i => by
    fin_cases i <;> first | exact ha.1 | exact hb.1) (by simp)
  simp only [PostCond.entails, SPred.entails_nil]
  exact ⟨fun _ h => U.sumPair_result ha hb h, ExceptConds.entails.refl _⟩

theorem U.lceq_intVal_sum {left right : Vector (U n) m}
    (h : WF.VectorRel U.WFRel lv rv left right) :
    WF.LCEq lv.int rv.int
      (left.toArray.map (fun x => x.intVal)).sum
      (right.toArray.map (fun x => x.intVal)).sum := by
  unfold WF.LCEq
  rw [LC.eval_array_sum, LC.eval_array_sum]
  apply congrArg Array.sum
  apply Array.ext
  · simp
  · intro i hiLeft hiRight
    simp only [Array.getElem_map]
    exact (h ⟨i, by simpa using hiLeft⟩).1

theorem U.sumFixed_wf :
    WF.GadgetSpec (WF.VectorRel (U.WFRel (n := n)))
      (U.sumFixed (n := n) (m := m)) U.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  unfold U.sumFixed
  apply WF.GadgetSpec.bind_rule U.fromInt_wf_full
  · exact fun _ _ h => U.lceq_intVal_sum h
  · intro A outL outR hout
    apply WF.Rel.pure
    intro lv rv hA
    have h := hout lv rv hA
    let hle : n ≤ n + Nat.clog 2 m := by omega
    constructor
    · apply WF.LCEq.uIntVal
      intro i
      simpa [U.takeLE, Fin.getElem_fin] using h.2.2.1 (i.castLE hle)
    · intro i
      simpa [U.takeLE, Fin.getElem_fin] using h.2.1 (i.castLE hle)

instance instInhabitedWord : Inhabited (Word n) :=
  ⟨{ bitsLE := Vector.replicate n (0 : LC Bool) }⟩

@[simp] theorem Vector.getElem!_map [Inhabited α] [Inhabited β]
    (xs : Vector α n) (f : α → β) (i : Nat) (hi : i < n) :
    (xs.map f)[i]! = f (xs[i]!) := by
  rw [getElem!_pos (xs.map f) i (by simpa), getElem!_pos xs i hi,
    Vector.getElem_map f hi]

theorem List.foldl_congr_of_mem {xs : List α} {f g : β → α → β}
    (h : ∀ x ∈ xs, ∀ acc, f acc x = g acc x) (init : β) :
    xs.foldl f init = xs.foldl g init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [h x (by simp) init]
      exact ih (fun y hy => h y (by simp [hy])) _

@[spec] theorem U.mapM_fromWord_sound {valuation : WF.Valuation}
    {words : Vector (Word width) n} :
    ⦃⌜True⌝⦄ Sound.interp valuation (words.mapM U.fromWord)
    ⦃⇓ out => ⌜Vector.Rel valuation out
      (words.map (Word.eval valuation.bool))⌝⦄ := by
  rw [Vector.mapM_eq_ofFnM]
  apply Sound.vectorOfFnM (R := fun i out =>
    U.Rel valuation out (words.map (Word.eval valuation.bool))[i])
  intro i
  simpa using (U.fromWord_sound_rel (w := words[i]))

@[spec] theorem U.mapM_fromWord_complete {valuation : WF.Valuation}
    {words : Vector (Word width) n} :
    ⦃⌜True⌝⦄ Complete.interp valuation (words.mapM U.fromWord)
    ⦃⇓ out => ⌜Vector.Rel valuation out
      (words.map (Word.eval valuation.bool))⌝⦄ := by
  rw [Vector.mapM_eq_ofFnM]
  apply Complete.vectorOfFnM (R := fun i out =>
    U.Rel valuation out (words.map (Word.eval valuation.bool))[i])
  intro i
  simpa using (U.fromWord_complete_rel (w := words[i]))

theorem U.mapM_fromWord_wf :
    WF.GadgetSpec (WF.VectorRel Word.WFRel)
      (fun xs : Vector (Word n) m => xs.mapM U.fromWord)
      (WF.VectorRel U.WFRel) := by
  intro left right
  apply WF.Rel.mono
    (U.fromWord_wf_rel.relHom.vectorMapM
      (fun lv rv => WF.VectorRel Word.WFRel lv rv left right)
      left right (fun _ _ h => h))
  exact fun _ _ _ _ h => h.2

theorem List.id_forIn'_yield (xs : List α) (init : β) (f : β → α → β) :
    (forIn' xs init fun x _ acc =>
      (pure (ForInStep.yield (f acc x)) : Id (ForInStep β))) =
    (pure (xs.foldl f init) : Id β) := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
      rw [List.forIn'_cons]
      exact ih (f init x)

theorem Std.Legacy.Range.id_forIn'_yield (xs : Std.Legacy.Range)
    (init : β) (f : β → Nat → β) :
    (forIn' xs init fun i _ acc =>
      (pure (ForInStep.yield (f acc i)) : Id (ForInStep β))) =
    (pure (xs.toList.foldl f init) : Id β) := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  exact List.id_forIn'_yield _ _ _

theorem Std.Legacy.Range.id_forIn'_yield_congr (xs : Std.Legacy.Range)
    (init : β) (f : (i : Nat) → i ∈ xs → β → β)
    (g : β → Nat → β) (
      h : ∀ i hi acc, f i hi acc = g acc i) :
    (forIn' xs init fun i hi acc =>
      (pure (ForInStep.yield (f i hi acc)) : Id (ForInStep β))) =
    (pure (xs.toList.foldl g init) : Id β) := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  calc
    (forIn' xs.toList init fun i hi acc =>
      (pure (ForInStep.yield (f i (xs.mem_of_mem_range' hi) acc)) :
        Id (ForInStep β))) =
        forIn' xs.toList init (fun i _ acc =>
          pure (ForInStep.yield (g acc i))) := by
            apply List.forIn'_congr rfl rfl
            intro i hi acc
            rw [h]
    _ = pure (xs.toList.foldl g init) := List.id_forIn'_yield _ _ _

end Freigen.F2Z
