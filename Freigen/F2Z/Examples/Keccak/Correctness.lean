import Freigen.F2Z.Examples.Keccak.Proofs

namespace Freigen.F2Z.Examples.Keccak

open Std.Do
open scoped Std.Do

theorem permCirc_eq (input : Vector (LC Bool) 1600) :
    permCirc input = (do
      let output ← permCircuit (inputWords input)
      pure (flattenOutput output)) := rfl

theorem inputWords_wf
    (h : WF.VectorRel (fun lv rv (l r : LC Bool) =>
      WF.LCEq lv.bool rv.bool l r) lv rv left right) :
    WF.VectorRel Word.WFRel lv rv
      (inputWords left) (inputWords right) := by
  intro lane bit
  unfold inputWords
  simp only [Vector.getElem_ofFn, Fin.getElem_fin]
  exact h ⟨lane.val * 64 + bit.val, by omega⟩

theorem permCirc_wf :
    WF.GadgetSpec
      (WF.VectorRel fun lv rv (l r : LC Bool) =>
        WF.LCEq lv.bool rv.bool l r)
      permCirc
      (WF.VectorRel fun lv rv (l r : LC Bool) =>
        WF.LCEq lv.bool rv.bool l r) := by
  unfold WF.GadgetSpec
  intro left right
  rw [permCirc_eq, permCirc_eq]
  apply WF.GadgetSpec.bind_rule
    (left := inputWords left) (right := inputWords right) permCircuit_wf
  · exact fun _ _ h => inputWords_wf h
  · intro A outL outR hout
    apply WF.Rel.pure
    intro lv rv hA i
    unfold flattenOutput
    simp only [Vector.getElem_ofFn, Fin.getElem_fin]
    exact (hout lv rv hA).2
      ⟨i.val / 64, by omega⟩ ⟨i.val % 64, by omega⟩

theorem permCirc_complete_triple (input : Vector (LC Bool) 1600) :
    ⦃⌜True⌝⦄ Complete.interp ρ (permCirc input)
    ⦃⇓ _ => ⌜True⌝⦄ := by
  rw [permCirc_eq, Complete.interp_bind]
  apply Triple.bind (Q := fun _ : Vector (Word 64) 25 => ⌜True⌝)
  case hx => exact permCircuit_complete (inputWords input)
  case hf => intro _; apply Triple.pure; simp

theorem inputWords_eval (input : Vector Bool 1600) (valuation : Nat → Bool)
    (hinput : ∀ i : Fin 1600, valuation i.val = input[i]) :
    (inputWords (Vector.ofFn fun i => ({i.val} : LC Bool))).map
      (Word.eval valuation) =
    Vector.ofFn fun lane => BitVec.ofNat 64
      (Nat.ofBits fun (bit : Fin 64) => input[lane.val * 64 + bit.val]) := by
  apply Vector.ext
  intro lane hlane
  apply BitVec.eq_of_getElem_eq
  intro bit hbit
  simp only [inputWords, Vector.getElem_map, Vector.getElem_ofFn,
    Word.eval, BitVec.getElem_ofFnLE, Fin.getElem_fin, LC.eval_singleton]
  rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow _),
    Nat.testBit_ofBits_lt _ _ hbit]
  exact hinput ⟨lane * 64 + bit, by omega⟩

theorem flatten_eval {output : Vector (Word 64) 25}
    {value : Vector (BitVec 64) 25}
    (h : Word.VectorRel ρ output value) :
    (flattenOutput output).map (fun x => x.eval ρ.bool) =
      Vector.ofFn fun i : Fin 1600 =>
        value[i.val / 64].toNat.testBit (i.val % 64) := by
  apply Vector.ext
  intro i hi
  simp only [flattenOutput, Vector.getElem_map, Vector.getElem_ofFn]
  have hlane := h ⟨i / 64, by omega⟩
  unfold Word.Rel at hlane
  have hbit := congrArg (fun x : BitVec 64 => x[i % 64]'(by omega)) hlane
  simp only [Word.eval, BitVec.getElem_ofFnLE] at hbit
  rw [BitVec.getElem_eq_testBit_toNat] at hbit
  exact hbit

theorem permCirc_sound_triple (input : Vector Bool 1600)
    (wit : Nat → Bool)
    (hinput : ∀ i : Fin 1600, wit i.val = input[i])
    (cs : Semantics.CS) :
    ⦃⌜True⌝⦄ Sound.interp (Sound.csValuation cs wit)
      (permCirc (Vector.ofFn fun i => ({i.val} : LC Bool)))
    ⦃⇓ output => ⌜output.map (fun x => x.eval wit) = permBits input⌝⦄ := by
  rw [permCirc_eq, Sound.interp_bind]
  apply Triple.bind (Q := fun output => ⌜Word.VectorRel
    (Sound.csValuation cs wit) output
    (perm ((inputWords (Vector.ofFn fun i => ({i.val} : LC Bool))).map
      (Word.eval wit)))⌝)
  case hx =>
    have hin : Word.VectorRel (Sound.csValuation cs wit)
        (inputWords (Vector.ofFn fun i => ({i.val} : LC Bool)))
        ((inputWords (Vector.ofFn fun i => ({i.val} : LC Bool))).map
          (Word.eval wit)) := by
      intro i
      unfold Word.Rel Sound.csValuation
      simp
    apply Triple.iff_conseq.mp (permCircuit_sound hin)
    · simp
    · simp
  case hf =>
    intro output
    apply Triple.pure
    simp only [SPred.entails_nil]
    intro houtput
    unfold permBits
    have hflat := flatten_eval houtput
    simp only [Sound.csValuation] at hflat
    rw [hflat]
    have hperm := congrArg perm (inputWords_eval input wit hinput)
    rw [hperm]
    rfl

theorem permCirc_complete : ∀ input, ∃ witness,
    Semantics.Witgen.runWithInputs permCirc input = some witness ∧
    keccakCS.2.satisfies (witness[·]!) := by
  intro input
  apply Complete.adequate
  · exact permCirc_wf
  · exact permCirc_complete_triple _

theorem permCirc_sound (input : Vector Bool 1600) (witness : Nat → Bool)
    (hinput : ∀ i : Fin 1600, input[i] = witness i.val) :
    keccakCS.2.satisfies witness →
      keccakCS.1.map (fun i => i.eval witness) = permBits input := by
  intro hsatisfies
  apply Sound.adequate
    (circ := permCirc)
    (P := fun _ output => output.map (·.eval witness) = permBits input)
  · have ht := permCirc_sound_triple input witness
      (fun i => (hinput i).symm) keccakCS.2
    rw [Triple.iff] at ht ⊢
    simp only [SPred.entails_nil] at ht ⊢
    exact fun _ => ht True.intro
  · exact fun i => (hinput i).symm
  · exact hsatisfies

end Freigen.F2Z.Examples.Keccak
