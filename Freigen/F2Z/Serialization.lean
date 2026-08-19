import Freigen.F2Z.Semantics

/-!
# Binary serialization of F2Z constraint systems

The binary stream contains the four sparse matrices `M`, `A`, `B`, and `C`, in
that order.  Every matrix is encoded as its row count followed by its rows.  A
row is its number of nonzero entries followed by `(column, coefficient)` pairs;
the coefficient is omitted for `M`, where every stored coefficient is `true`.

Row counts, nonzero counts, and column indices are fixed-width little-endian
`u32` values.  Integer coefficients are ZigZag-encoded and then written as
unsigned LEB128 values, so Lean's arbitrary-size integers are not truncated.

Linear combinations keep their constant separate from their indexed
coefficients.  In the matrices, column zero holds that constant and coefficient
`i` is therefore written in column `i + 1`.  `M` also starts with the implicit
constant-one row, so its number of rows is `cs.m.size + 1`.
-/

namespace Freigen.F2Z.Semantics

namespace CS.Binary

/-- Append a natural number as a fixed-width little-endian `u32`, panicking
if it does not fit. -/
private def appendU32 (out : ByteArray) (n : Nat) : ByteArray :=
  if n < UInt32.size then
    let n := UInt32.ofNat n
    out
      |>.push n.toUInt8
      |>.push (n >>> 8).toUInt8
      |>.push (n >>> 16).toUInt8
      |>.push (n >>> 24).toUInt8
  else
    panic! s!"value {n} does not fit in a u32"

/-- Append an arbitrary-size natural number as unsigned LEB128. -/
private partial def appendVarNat (out : ByteArray) (n : Nat) : ByteArray :=
  let byte := UInt8.ofNat (n % 128)
  let rest := n / 128
  if rest = 0 then
    out.push byte
  else
    appendVarNat (out.push (byte ||| 0x80)) rest

/-- ZigZag encoding, with `0, -1, 1, -2, 2, ...` mapped to naturals. -/
private def zigZag : Int → Nat
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

private def appendInt (out : ByteArray) (n : Int) : ByteArray :=
  appendVarNat out (zigZag n)

private def appendBoolRow (out : ByteArray) (row : LC Bool) : ByteArray :=
  let entryCount := row.coeffs.size + if row.constant then 1 else 0
  let out := appendU32 out entryCount
  let out := if row.constant then appendU32 out 0 else out
  row.coeffs.foldl (fun out column _ => appendU32 out (column + 1)) out

private def appendIntRow (out : ByteArray) (row : LC Int) : ByteArray :=
  let entryCount := row.coeffs.size + if row.constant = 0 then 0 else 1
  let out := appendU32 out entryCount
  let out := if row.constant = 0 then out else appendInt (appendU32 out 0) row.constant
  row.coeffs.foldl (fun out column coeff =>
    appendInt (appendU32 out (column + 1)) coeff) out

private def appendM (out : ByteArray) (rows : Array (LC Bool)) : ByteArray :=
  let out := appendU32 out (rows.size + 1)
  -- The first integer-witness entry is the constant one.
  let out := appendU32 (appendU32 out 1) 0
  rows.foldl appendBoolRow out

private def appendR1CMatrix (out : ByteArray) (rows : Array (R1C Int))
    (select : R1C Int → LC Int) : ByteArray :=
  let out := appendU32 out rows.size
  rows.foldl (fun out row => appendIntRow out (select row)) out

/-- Serialize an F2Z constraint system as sparse `M`, `A`, `B`, and `C` matrices. -/
def serialize (cs : CS) : ByteArray :=
  let out := appendM ByteArray.empty cs.m
  let out := appendR1CMatrix out cs.r1cs (·.a)
  let out := appendR1CMatrix out cs.r1cs (·.b)
  appendR1CMatrix out cs.r1cs (·.c)

end CS.Binary

/-- Serialize an F2Z constraint system as sparse `M`, `A`, `B`, and `C` matrices. -/
def CS.serialize (cs : CS) : ByteArray :=
  CS.Binary.serialize cs

/-- Serialize an F2Z constraint system and write it to `path`. -/
def CS.writeBinFile (cs : CS) (path : System.FilePath) : IO Unit :=
  IO.FS.writeBinFile path cs.serialize

end Freigen.F2Z.Semantics
