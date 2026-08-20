import Freigen.F2Z.Examples.Keccak.Impl
import Freigen.F2Z.Correctness.U

namespace Freigen.F2Z.Examples.Keccak

open Std.Do
open scoped Std.Do

def Word.Rel (ρ : WF.Valuation) (word : Word n) (value : BitVec n) : Prop :=
  word.eval ρ.bool = value

def Word.VectorRel (ρ : WF.Valuation) (words : Vector (Word n) m)
    (values : Vector (BitVec n) m) : Prop :=
  ∀ i : Fin m, Word.Rel ρ words[i] values[i]

theorem Word.VectorRel.getElem! {n m : Nat}
    {words : Vector (Word n) m} {values : Vector (BitVec n) m}
    (h : Word.VectorRel ρ words values)
    {i : Nat} (hi : i < m) :
    Word.Rel ρ words[i]! values[i]! := by
  rw [getElem!_pos words i hi, getElem!_pos values i hi]
  exact h ⟨i, hi⟩

theorem Word.VectorRel.eval_eq {n m : Nat}
    {words : Vector (Word n) m} {values : Vector (BitVec n) m}
    (h : Word.VectorRel ρ words values) :
    words.map (Word.eval ρ.bool) = values := by
  apply Vector.ext
  intro i hi
  simpa [Word.Rel] using h ⟨i, hi⟩

@[spec] theorem andNotBit_sound (y z : LC Bool) :
    ⦃⌜True⌝⦄ Sound.interp ρ (andNotBit y z)
    ⦃⇓ out => ⌜out.eval ρ.bool =
      ((!(y.eval ρ.bool)) && z.eval ρ.bool)⌝⦄ := by
  mvcgen [andNotBit]
  intro out
  mvcgen
  rename_i yi hy zi hz oi ho hass
  simp only [LC.eval_one, LC.eval_sub] at hass
  generalize y.eval ρ.bool = yv at hy hass ⊢
  generalize z.eval ρ.bool = zv at hz hass ⊢
  generalize out[0].eval ρ.bool = ov at ho hass ⊢
  cases yv <;> cases zv <;> cases ov <;> norm_num at hy hz ho hass ⊢
  all_goals norm_num [← hy, ← hz, ← ho] at hass

@[spec] theorem andNotBit_complete (y z : LC Bool) :
    ⦃⌜True⌝⦄ Complete.interp ρ (andNotBit y z)
    ⦃⇓ out => ⌜out.eval ρ.bool =
      ((!(y.eval ρ.bool)) && z.eval ρ.bool)⌝⦄ := by
  mvcgen [andNotBit]
  refine ⟨#v[(!(y.eval ρ.bool)) && z.eval ρ.bool], ?_, ?_⟩
  · simp [WF.interpHint, WF.evalArgs]
  · mvcgen
    generalize y.eval ρ.bool = yv at *
    generalize z.eval ρ.bool = zv at *
    cases yv <;> cases zv <;> simp_all
    all_goals rfl

theorem eval_wordOfBitVec (x : BitVec n) :
    (wordOfBitVec x).eval valuation = x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [Word.eval, BitVec.getElem_ofFnLE, wordOfBitVec,
    Vector.getElem_ofFn, Fin.getElem_fin]
  change (LC.ofConst x[i]).eval valuation = x[i]
  exact LC.eval_ofConst valuation x[i]

@[spec] theorem andNotWord_sound (y z : Word n) :
    ⦃⌜True⌝⦄ Sound.interp ρ (andNotWord y z)
    ⦃⇓ out => ⌜Word.Rel ρ out ((~~~y.eval ρ.bool) &&& z.eval ρ.bool)⌝⦄ := by
  unfold andNotWord
  rw [Sound.interp_bind]
  apply Triple.bind (Q := fun bits => ⌜∀ i : Fin n,
    bits[i].eval ρ.bool = ((!(y.bitsLE[i].eval ρ.bool)) &&
      z.bitsLE[i].eval ρ.bool)⌝)
  case hx =>
    apply Triple.iff_conseq.mp (Sound.vectorOfFnM
      (fun i => andNotBit_sound y.bitsLE[i] z.bitsLE[i]))
    · simp
    · simp
  case hf =>
    intro bits
    apply Triple.pure
    simp only [SPred.entails_nil]
    intro hbits
    unfold Word.Rel
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp only [Word.eval, BitVec.getElem_ofFnLE, BitVec.getElem_and,
      BitVec.getElem_not]
    exact hbits ⟨i, hi⟩

@[spec] theorem andNotWord_complete (y z : Word n) :
    ⦃⌜True⌝⦄ Complete.interp ρ (andNotWord y z)
    ⦃⇓ out => ⌜Word.Rel ρ out ((~~~y.eval ρ.bool) &&& z.eval ρ.bool)⌝⦄ := by
  unfold andNotWord
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun bits => ⌜∀ i : Fin n,
    bits[i].eval ρ.bool = ((!(y.bitsLE[i].eval ρ.bool)) &&
      z.bitsLE[i].eval ρ.bool)⌝)
  case hx =>
    apply Triple.iff_conseq.mp (Complete.vectorOfFnM
      (fun i => andNotBit_complete y.bitsLE[i] z.bitsLE[i]))
    · simp
    · simp
  case hf =>
    intro bits
    apply Triple.pure
    simp only [SPred.entails_nil]
    intro hbits
    unfold Word.Rel
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp only [Word.eval, BitVec.getElem_ofFnLE, BitVec.getElem_and,
      BitVec.getElem_not]
    exact hbits ⟨i, hi⟩

theorem thetaCWords_rel (h : Word.VectorRel ρ words values) :
    Word.VectorRel ρ (thetaCWords words) (thetaC values) := by
  intro x
  unfold Word.Rel thetaCWords thetaC
  simp only [Vector.getElem_ofFn, Fin.getElem_fin, Word.eval_xor]
  rw [h.getElem! (by unfold laneIndex; omega),
    h.getElem! (by unfold laneIndex; omega),
    h.getElem! (by unfold laneIndex; omega),
    h.getElem! (by unfold laneIndex; omega),
    h.getElem! (by unfold laneIndex; omega)]

theorem thetaDWords_rel (h : Word.VectorRel ρ words values) :
    Word.VectorRel ρ (thetaDWords words) (thetaD values) := by
  intro x
  unfold Word.Rel thetaDWords thetaD rotl
  simp only [Vector.getElem_ofFn, Fin.getElem_fin, Word.eval_xor]
  rw [Word.eval_rotateRight _ _ 63 (by omega),
    h.getElem! (Nat.mod_lt _ (by omega)),
    h.getElem! (Nat.mod_lt _ (by omega))]

theorem thetaWords_rel (h : Word.VectorRel ρ words values) :
    Word.VectorRel ρ (thetaWords words) (theta values) := by
  have hd := thetaDWords_rel (thetaCWords_rel h)
  intro i
  have hi := h i
  unfold Word.Rel at hi
  simp only [Fin.getElem_fin] at hi
  unfold Word.Rel thetaWords theta
  simp only [Vector.getElem_ofFn, Fin.getElem_fin, Word.eval_xor]
  rw [hi, hd.getElem! (Nat.mod_lt _ (by omega))]

theorem rhoPiWords_rel (h : Word.VectorRel ρ words values) :
    Word.VectorRel ρ (rhoPiWords words) (rhoPi values) := by
  intro i
  have hindex : laneIndex ((i.val % 5 + 3 * (i.val / 5)) % 5)
      (i.val % 5) < 25 := by
    unfold laneIndex
    omega
  unfold Word.Rel rhoPiWords rhoPi rotl
  simp only [Vector.getElem_ofFn, Fin.getElem_fin]
  rw [Word.eval_rotateRight _ _ _ (Nat.mod_lt _ (by omega))]
  congr 1
  exact h.getElem! hindex

@[spec] theorem chiLaneCircuit_sound (h : Word.VectorRel ρ words values)
    (i : Fin 25) :
    ⦃⌜True⌝⦄ Sound.interp ρ (chiLaneCircuit words i)
    ⦃⇓ out => ⌜Word.Rel ρ out (chiLane values i)⌝⦄ := by
  let x := i.val % 5
  let y := i.val / 5
  have h0 : laneIndex x y < 25 := by unfold x y laneIndex; omega
  have h1 : laneIndex ((x + 1) % 5) y < 25 := by
    unfold x y laneIndex; omega
  have h2 : laneIndex ((x + 2) % 5) y < 25 := by
    unfold x y laneIndex; omega
  unfold chiLaneCircuit
  rw [Sound.interp_bind]
  apply Triple.bind (Q := fun nonlinear => ⌜Word.Rel ρ nonlinear
    ((~~~values[laneIndex ((x + 1) % 5) y]!) &&&
      values[laneIndex ((x + 2) % 5) y]!)⌝)
  case hx =>
    apply Triple.iff_conseq.mp
      (andNotWord_sound
        words[laneIndex ((x + 1) % 5) y]!
        words[laneIndex ((x + 2) % 5) y]!)
    · simp
    · simp only [PostCond.entails, SPred.entails_nil]
      constructor
      · intro _ hout
        unfold Word.Rel at hout ⊢
        rw [(h.getElem! h1), (h.getElem! h2)] at hout
        exact hout
      · exact ExceptConds.entails.refl _
  case hf =>
    intro nonlinear
    apply Triple.pure
    simp only [SPred.entails_nil]
    intro hn
    unfold Word.Rel chiLane
    simp only [Word.eval_xor]
    rw [h.getElem! h0, hn]
    rfl

@[spec] theorem chiLaneCircuit_complete (words : Vector (Word 64) 25)
    (i : Fin 25) :
    ⦃⌜True⌝⦄ Complete.interp ρ (chiLaneCircuit words i)
    ⦃⇓ _ => ⌜True⌝⦄ := by
  unfold chiLaneCircuit
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun _ : Word 64 => ⌜True⌝)
  case hx =>
    exact Triple.iff_conseq.mp
      (andNotWord_complete
        words[laneIndex ((i.val % 5 + 1) % 5) (i.val / 5)]!
        words[laneIndex ((i.val % 5 + 2) % 5) (i.val / 5)]!)
      (by simp) (by simp)
  case hf =>
    intro _
    apply Triple.pure
    simp

private theorem chiCircuit_sound_lanes (h : Word.VectorRel ρ words values) :
    ⦃⌜True⌝⦄ Sound.interp ρ (chiCircuit words)
    ⦃⇓ out => ⌜∀ i, Word.Rel ρ out[i] (chiLane values i)⌝⦄ := by
  unfold chiCircuit
  exact Sound.vectorOfFnM (chiLaneCircuit_sound h)

theorem chi_get (values : Vector (BitVec 64) 25) (i : Fin 25) :
    (chi values)[i] = chiLane values i := by
  unfold chi
  exact Vector.getElem_ofFn i.isLt

theorem chiLanes_vectorRel
    (h : ∀ i, Word.Rel ρ words[i] (chiLane values i)) :
    Word.VectorRel ρ words (chi values) := by
  intro i
  rw [chi_get]
  exact h i

@[spec] theorem chiCircuit_complete (words : Vector (Word 64) 25) :
    ⦃⌜True⌝⦄ Complete.interp ρ (chiCircuit words)
    ⦃⇓ _ => ⌜True⌝⦄ := by
  unfold chiCircuit
  apply Triple.iff_conseq.mp (Complete.vectorOfFnM
    (R := fun _ _ => True) (chiLaneCircuit_complete (ρ := ρ) words))
  · simp
  · simp

theorem iotaWords_rel (h : Word.VectorRel ρ words values) (rc : BitVec 64) :
    Word.VectorRel ρ (iotaWords rc words) (iota rc values) := by
  intro i
  unfold iotaWords iota
  rw [show words.set! 0 (words[0]! ^^^ wordOfBitVec rc) =
      words.setIfInBounds 0 (words[0]! ^^^ wordOfBitVec rc) by rfl,
    show values.set! 0 (values[0]! ^^^ rc) =
      values.setIfInBounds 0 (values[0]! ^^^ rc) by rfl]
  simp only [Fin.getElem_fin, Vector.getElem_setIfInBounds i.isLt]
  split
  · unfold Word.Rel
    rw [Word.eval_xor, h.getElem! (by decide), eval_wordOfBitVec]
  · exact h i

@[spec] theorem roundCircuit_sound (h : Word.VectorRel ρ words values)
    (rc : BitVec 64) :
    ⦃⌜True⌝⦄ Sound.interp ρ (roundCircuit rc words)
    ⦃⇓ out => ⌜Word.VectorRel ρ out (round rc values)⌝⦄ := by
  unfold roundCircuit round
  rw [Sound.interp_bind]
  have hb := rhoPiWords_rel (thetaWords_rel h)
  apply Triple.bind (Q := fun afterChi => ⌜∀ i,
    Word.Rel ρ afterChi[i] (chiLane (rhoPi (theta values)) i)⌝)
  case hx => exact chiCircuit_sound_lanes hb
  case hf =>
    intro afterChi
    apply Triple.pure
    simp only [SPred.entails_nil]
    intro hchi
    exact iotaWords_rel (chiLanes_vectorRel hchi) rc

@[spec] theorem roundCircuit_complete (rc : BitVec 64)
    (words : Vector (Word 64) 25) :
    ⦃⌜True⌝⦄ Complete.interp ρ (roundCircuit rc words)
    ⦃⇓ _ => ⌜True⌝⦄ := by
  unfold roundCircuit
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun _ : Vector (Word 64) 25 => ⌜True⌝)
  case hx => exact chiCircuit_complete (rhoPiWords (thetaWords words))
  case hf => intro _; apply Triple.pure; simp

@[spec] theorem permCircuit_sound (h : Word.VectorRel ρ words values) :
    ⦃⌜True⌝⦄ Sound.interp ρ (permCircuit words)
    ⦃⇓ out => ⌜Word.VectorRel ρ out (perm values)⌝⦄ := by
  unfold permCircuit perm
  rw [Sound.interp_bind]
  apply Triple.bind (Q := fun state => ⌜Word.VectorRel ρ state
    (([0:24].toList).foldl
      (fun state r => round roundConstants[r]! state) values)⌝)
  case hx =>
    apply Sound.interp_forIn'_range_spec
    mvcgen -trivial invariants
    · ⇓⟨cur, state⟩ => ⌜Word.VectorRel ρ state
        (cur.prefix.foldl
          (fun state r => round roundConstants[r]! state) values)⌝
    case vc1.values pref _ _ _ _ _ =>
      exact pref.foldl (fun state r => round roundConstants[r]! state) values
    case vc2.h _ _ _ _ _ hstate => exact hstate
    case vc3 _ _ _ _ _ _ _ hout =>
      simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using hout
    case vc4.pre => simpa using h
    case vc5.post.success => exact fun h => h
  case hf => intro _; apply Triple.pure; simp

@[spec] theorem permCircuit_complete (words : Vector (Word 64) 25) :
    ⦃⌜True⌝⦄ Complete.interp ρ (permCircuit words)
    ⦃⇓ _ => ⌜True⌝⦄ := by
  unfold permCircuit
  rw [Complete.interp_bind]
  apply Triple.bind (Q := fun _ : Vector (Word 64) 25 => ⌜True⌝)
  case hx =>
    apply Complete.interp_forIn'_range_spec
    mvcgen -trivial invariants
    · ⇓⟨_, _⟩ => ⌜True⌝
  case hf => intro _; apply Triple.pure; simp

theorem andNotBit_wf :
    WF.GadgetSpec
      (fun lv rv (l r : LC Bool × LC Bool) =>
        WF.LCEq lv.bool rv.bool l.1 r.1 ∧
          WF.LCEq lv.bool rv.bool l.2 r.2)
      (fun x => andNotBit x.1 x.2)
      (fun lv rv l r => WF.LCEq lv.bool rv.bool l r) := by
  unfold WF.GadgetSpec
  rintro ⟨yL, zL⟩ ⟨yR, zR⟩
  unfold andNotBit
  wfgen'
  case vc2 | vc7 =>
    apply Std.Legacy.Range.mem_of_mem_range'
    simp
  all_goals
    simp_all [WF.LCEq, WF.RealizesBools, WF.HintReturns,
      WF.ArgsEq, WF.evalArgs]
  all_goals grind

theorem andNotWord_wf :
    WF.GadgetSpec
      (fun lv rv (l r : Word n × Word n) =>
        Word.WFRel lv rv l.1 r.1 ∧ Word.WFRel lv rv l.2 r.2)
      (fun x => andNotWord x.1 x.2) Word.WFRel := by
  unfold WF.GadgetSpec
  rintro ⟨yL, zL⟩ ⟨yR, zR⟩
  unfold andNotWord
  let P : WF.Assumption := fun lv rv =>
    Word.WFRel lv rv yL yR ∧ Word.WFRel lv rv zL zR
  have hbits := WF.Rel.vectorOfFnM
    (P := P)
    (S := fun _ lv rv l r => WF.LCEq lv.bool rv.bool l r)
    (fL := fun i => andNotBit yL.bitsLE[i] zL.bitsLE[i])
    (fR := fun i => andNotBit yR.bitsLE[i] zR.bitsLE[i])
    (fun i A _ _ hA => andNotBit_wf.relHom A
      ⟨yL.bitsLE[i], zL.bitsLE[i]⟩
      ⟨yR.bitsLE[i], zR.bitsLE[i]⟩
      (fun lv rv h =>
        let hp := hA lv rv h
        ⟨hp.1 i, hp.2 i⟩))
  apply hbits.bind
  intro A bitsL bitsR hA
  apply WF.Rel.pure
  intro lv rv h
  exact (hA lv rv h).2

theorem thetaCWords_wfRel
    (h : WF.VectorRel Word.WFRel lv rv left right) :
    WF.VectorRel Word.WFRel lv rv
      (thetaCWords left) (thetaCWords right) := by
  intro x
  unfold thetaCWords
  simp only [Vector.getElem_ofFn, Fin.getElem_fin]
  exact ((((h.getElem! (by unfold laneIndex; omega)).xor
    (h.getElem! (by unfold laneIndex; omega))).xor
    (h.getElem! (by unfold laneIndex; omega))).xor
    (h.getElem! (by unfold laneIndex; omega))).xor
    (h.getElem! (by unfold laneIndex; omega))

theorem thetaDWords_wfRel
    (h : WF.VectorRel Word.WFRel lv rv left right) :
    WF.VectorRel Word.WFRel lv rv
      (thetaDWords left) (thetaDWords right) := by
  intro x
  unfold thetaDWords
  simp only [Vector.getElem_ofFn, Fin.getElem_fin]
  exact (h.getElem! (Nat.mod_lt _ (by omega))).xor
    ((h.getElem! (Nat.mod_lt _ (by omega))).rotateRight 63)

theorem thetaWords_wfRel
    (h : WF.VectorRel Word.WFRel lv rv left right) :
    WF.VectorRel Word.WFRel lv rv
      (thetaWords left) (thetaWords right) := by
  have hd := thetaDWords_wfRel (thetaCWords_wfRel h)
  intro i
  unfold thetaWords
  simp only [Vector.getElem_ofFn, Fin.getElem_fin]
  exact (h i).xor (hd.getElem! (Nat.mod_lt _ (by omega)))

theorem rhoPiWords_wfRel
    (h : WF.VectorRel Word.WFRel lv rv left right) :
    WF.VectorRel Word.WFRel lv rv
      (rhoPiWords left) (rhoPiWords right) := by
  intro i
  unfold rhoPiWords
  simp only [Vector.getElem_ofFn, Fin.getElem_fin]
  apply Word.WFRel.rotateRight
  apply h.getElem!
  unfold laneIndex
  omega

theorem iotaWords_wfRel
    (h : WF.VectorRel Word.WFRel lv rv left right) (rc : BitVec 64) :
    WF.VectorRel Word.WFRel lv rv
      (iotaWords rc left) (iotaWords rc right) := by
  unfold iotaWords
  apply WF.VectorRel.set!
  · exact h
  · apply Word.WFRel.xor (h.getElem! (by decide))
    intro i
    unfold WF.LCEq wordOfBitVec
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    change (LC.ofConst rc[i.val]).eval lv.bool =
      (LC.ofConst rc[i.val]).eval rv.bool
    rw [LC.eval_ofConst, LC.eval_ofConst]

theorem chiLaneCircuit_wf (i : Fin 25) :
    WF.GadgetSpec (WF.VectorRel Word.WFRel)
      (fun words => chiLaneCircuit words i) Word.WFRel := by
  unfold WF.GadgetSpec
  intro left right
  let x := i.val % 5
  let y := i.val / 5
  have h0 : laneIndex x y < 25 := by unfold x y laneIndex; omega
  have h1 : laneIndex ((x + 1) % 5) y < 25 := by
    unfold x y laneIndex; omega
  have h2 : laneIndex ((x + 2) % 5) y < 25 := by
    unfold x y laneIndex; omega
  unfold chiLaneCircuit
  apply WF.GadgetSpec.bind_rule
    (left := ⟨left[laneIndex ((x + 1) % 5) y]!,
      left[laneIndex ((x + 2) % 5) y]!⟩)
    (right := ⟨right[laneIndex ((x + 1) % 5) y]!,
      right[laneIndex ((x + 2) % 5) y]!⟩) andNotWord_wf
  · intro lv rv h
    exact ⟨h.getElem! h1, h.getElem! h2⟩
  · intro A nonlinearL nonlinearR hn
    apply WF.Rel.pure
    intro lv rv hA
    have hp := hn lv rv hA
    exact (hp.1.getElem! h0).xor hp.2

theorem chiCircuit_wf :
    WF.GadgetSpec (WF.VectorRel Word.WFRel)
      chiCircuit (WF.VectorRel Word.WFRel) := by
  unfold WF.GadgetSpec
  intro left right
  unfold chiCircuit
  let P : WF.Assumption := fun lv rv =>
    WF.VectorRel Word.WFRel lv rv left right
  have hlanes := WF.Rel.vectorOfFnM
    (P := P) (S := fun _ => Word.WFRel)
    (fL := chiLaneCircuit left) (fR := chiLaneCircuit right)
    (fun i A _ _ hA => (chiLaneCircuit_wf i).relHom A left right
      (fun lv rv h => hA lv rv h))
  apply WF.Rel.mono hlanes
  exact fun _ _ _ _ h => h.2

theorem roundCircuit_wf (rc : BitVec 64) :
    WF.GadgetSpec (WF.VectorRel Word.WFRel)
      (roundCircuit rc) (WF.VectorRel Word.WFRel) := by
  unfold WF.GadgetSpec
  intro left right
  unfold roundCircuit
  apply WF.GadgetSpec.bind_rule
    (left := rhoPiWords (thetaWords left))
    (right := rhoPiWords (thetaWords right)) chiCircuit_wf
  · intro lv rv h
    exact rhoPiWords_wfRel (thetaWords_wfRel h)
  · intro A afterL afterR hafter
    apply WF.Rel.pure
    intro lv rv hA
    exact iotaWords_wfRel (hafter lv rv hA).2 rc

theorem permCircuit_wf :
    WF.GadgetSpec (WF.VectorRel Word.WFRel)
      permCircuit (WF.VectorRel Word.WFRel) := by
  unfold WF.GadgetSpec
  intro left right
  unfold permCircuit
  apply WF.Rel.forIn'_range_yield_bind
  · exact fun lv rv h => h
  · intro r _
    exact (roundCircuit_wf roundConstants[r]!).relHom
  · intro A outL outR hout
    apply WF.Rel.pure
    exact fun lv rv h => hout lv rv h

end Freigen.F2Z.Examples.Keccak
