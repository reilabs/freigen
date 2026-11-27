import Freigen.F2Z.Serialization

namespace Freigen.F2Z.Semantics.SerializationTest

private def m0 : LC Bool :=
  (true : LC Bool) + {1}

private def m1 : LC Bool :=
  ({130} : LC Bool)

private def a0 : LC Int :=
  (3 : LC Int) + (2 : Int) • ({0} : LC Int) + (-1 : Int) • ({130} : LC Int)

private def sample : CS := {
  m := #[m0, m1]
  r1cs := #[{
    a := a0
    b := (-65 : Int)
    c := 0
  }]
}

private def readU32 (bytes : Array UInt8) (offset : Nat) : UInt32 :=
  (List.range 4).foldl (fun value i =>
    value ||| (bytes[offset + i]!.toUInt32 <<< (8 * i).toUInt32)) 0

/-- Covers the implicit `M` row and constant column, all four matrix row
counts, omitted Boolean coefficients, fixed-width `u32` counts and indices, and
negative integer coefficients. -/
example :
    let bytes := sample.serialize.data
    bytes.size = 77 ∧
    -- M
    readU32 bytes 0 = 3 ∧
    readU32 bytes 4 = 1 ∧ readU32 bytes 8 = 0 ∧
    readU32 bytes 12 = 2 ∧ readU32 bytes 16 = 0 ∧ readU32 bytes 20 = 2 ∧
    readU32 bytes 24 = 1 ∧ readU32 bytes 28 = 131 ∧
    -- A
    readU32 bytes 32 = 1 ∧
    readU32 bytes 36 = 3 ∧
    readU32 bytes 40 = 0 ∧ bytes[44]! = 6 ∧
    readU32 bytes 45 = 1 ∧ bytes[49]! = 4 ∧
    readU32 bytes 50 = 131 ∧ bytes[54]! = 1 ∧
    -- B
    readU32 bytes 55 = 1 ∧
    readU32 bytes 59 = 1 ∧
    readU32 bytes 63 = 0 ∧ bytes[67]! = 129 ∧ bytes[68]! = 1 ∧
    -- C
    readU32 bytes 69 = 1 ∧ readU32 bytes 73 = 0 := by
  native_decide

end Freigen.F2Z.Semantics.SerializationTest
