import Freigen.F2Z.Examples.Sha256.Model
import Freigen.F2Z.Examples.Sha256.Proofs

namespace Freigen.F2Z.Examples

local instance : Context := lcContext

/-- https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA256.pdf -/
example : perm
    #v[
      0x61626380, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000018
    ]
    #v[
      0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
      0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
    ] =
    #v[
      0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223,
      0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad
    ] := by native_decide

example : perm
    #v[
      0x61626364, 0x62636465, 0x63646566, 0x64656667,
      0x65666768, 0x66676869, 0x6768696a, 0x68696a6b,
      0x696a6b6c, 0x6a6b6c6d, 0x6b6c6d6e, 0x6c6d6e6f,
      0x6d6e6f70, 0x6e6f7071, 0x80000000, 0x00000000
    ]
    #v[
      0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
      0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
    ] =
    #v[
      0x85e655d6, 0x417a1795, 0x3363376a, 0x624cde5c,
      0x76e09589, 0xcac5f811, 0xcc4b32c1, 0xf20e533a
    ] := by native_decide

example : perm
    #v[
      0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x000001c0
    ]
    #v[
      0x85e655d6, 0x417a1795, 0x3363376a, 0x624cde5c,
      0x76e09589, 0xcac5f811, 0xcc4b32c1, 0xf20e533a
    ] =
    #v[
      0x248d6a61, 0xd20638b8, 0xe5c02693, 0x0c3e6039,
      0xa33ce459, 0x64ff2167, 0xf6ecedd4, 0x19db06c1
    ] := by native_decide

/--
info: { mRows := 20457, mCols := 7145, r1csRows := 184 }
-/
#guard_msgs in
#eval sha256CS.2.stats

theorem permCirc'_complete : ∀ inputs, ∃ wit,
    Semantics.Witgen.runWithInputs (@permCirc' valueContext) inputs = some wit ∧
    sha256CS.2.satisfies (wit[·]!) := by
  intro inputs
  apply Complete.adequate
  · exact permCirc'_wf
  · exact permCirc'_complete_triple _

theorem permCirc'_sound (input : Vector Bool 768) (wit : Nat → Bool)
    (hWit : ∀ i : Fin 768, input[i] = wit i.val) :
    sha256CS.2.satisfies wit →
      sha256CS.1.map (fun i => i.eval wit) = perm' input := by
  intro hsatisfies
  apply Sound.adequate
    (circ := @permCirc' lcContext)
    (P := fun _ output => output.map (·.eval wit) = perm' input)
  · have ht :=
      permCirc'_sound_triple input wit (fun i => (hWit i).symm) sha256CS.2
    rw [Std.Do.Triple.iff] at ht ⊢
    simp only [Std.Do.SPred.entails_nil] at ht ⊢
    intro _
    exact ht True.intro
  · exact fun i => (hWit i).symm
  · exact hsatisfies

end Freigen.F2Z.Examples
