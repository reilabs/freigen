import Freigen.F2Z.Examples.Sha256.FastWitgen

open Freigen.F2Z.Examples

def sampleA : Vector Bool sha2562KBMessageBits :=
  Vector.ofFn fun i => (0x61 : Nat).testBit (7 - i.val % 8)

def sampleZero : Vector Bool sha2562KBMessageBits :=
  Vector.replicate _ false

def samplePattern : Vector Bool sha2562KBMessageBits :=
  Vector.ofFn fun i => ((i.val * 73 + i.val / 11) % 19) < 8

def packedWordsLoop (message : Sha2562KBPackedMessage) :
    (iterations : Nat) → (index : Nat) → (checksum : Nat) → Nat
  | 0, _, checksum => checksum
  | iterations + 1, index, checksum =>
    let witness := sha2562KBFastWitgen message
    let checksum := checksum + witness.words.size +
      if witness.get ((index * 7919) % Sha256FastWitgen.witnessBits) then 1 else 0
    packedWordsLoop message iterations (index + 1) checksum

def runPackedWordsBatch (message : Sha2562KBPackedMessage)
    (iterations : Nat) : IO (Nat × Nat) := do
  let result ← IO.mkRef 0
  let start ← IO.monoNanosNow
  result.set (packedWordsLoop message iterations 0 0)
  let checksum ← result.get
  let stop ← IO.monoNanosNow
  return (stop - start, checksum)

def boolInputLoop (message : Vector Bool sha2562KBMessageBits) :
    (iterations : Nat) → (index : Nat) → (checksum : Nat) → Nat
  | 0, _, checksum => checksum
  | iterations + 1, index, checksum =>
    let witness := sha2562KBFastWitgenFromBits message
    let checksum := checksum + witness.words.size +
      if witness.get ((index * 7919) % Sha256FastWitgen.witnessBits) then 1 else 0
    boolInputLoop message iterations (index + 1) checksum

def runBoolInputBatch (message : Vector Bool sha2562KBMessageBits)
    (iterations : Nat) : IO (Nat × Nat) := do
  let result ← IO.mkRef 0
  let start ← IO.monoNanosNow
  result.set (boolInputLoop message iterations 0 0)
  let checksum ← result.get
  let stop ← IO.monoNanosNow
  return (stop - start, checksum)

def boolArrayLoop (message : Vector Bool sha2562KBMessageBits) :
    (iterations : Nat) → (index : Nat) → (checksum : Nat) → Nat
  | 0, _, checksum => checksum
  | iterations + 1, index, checksum =>
    let witness := sha2562KBFastWitgenBoolArray message
    let checksum := checksum + witness.size +
      if witness[(index * 7919) % witness.size]! then 1 else 0
    boolArrayLoop message iterations (index + 1) checksum

def runBoolArrayBatch (message : Vector Bool sha2562KBMessageBits)
    (iterations : Nat) : IO (Nat × Nat) := do
  let result ← IO.mkRef 0
  let start ← IO.monoNanosNow
  result.set (boolArrayLoop message iterations 0 0)
  let checksum ← result.get
  let stop ← IO.monoNanosNow
  return (stop - start, checksum)

private def pad3 (n : Nat) : String :=
  if n < 10 then s!"00{n}"
  else if n < 100 then s!"0{n}"
  else toString n

private def fraction3 (n : Nat) : String :=
  if n = 0 then ""
  else if n % 100 = 0 then s!".{n / 100}"
  else if n % 10 = 0 then
    let n := n / 10
    if n < 10 then s!".0{n}" else s!".{n}"
  else s!".{pad3 n}"

private def formatScaled (nanoseconds scale : Nat) (unit : String) : String :=
  let whole := nanoseconds / scale
  let fraction := (nanoseconds % scale) * 1000 / scale
  s!"{whole}{fraction3 fraction} {unit}"

/-- Format a nanosecond count using its most readable unit. -/
def formatDuration (nanoseconds : Nat) : String :=
  if nanoseconds < 1000 then s!"{nanoseconds} ns"
  else if nanoseconds < 1000000 then formatScaled nanoseconds 1000 "µs"
  else if nanoseconds < 1000000000 then formatScaled nanoseconds 1000000 "ms"
  else formatScaled nanoseconds 1000000000 "s"

def benchmark {α : Type} (name : String)
    (batch : α → Nat → IO (Nat × Nat)) (input : α)
    (iterations trials : Nat) : IO Unit := do
  let _ ← batch input 20
  let mut elapsed := Array.mkEmpty trials
  let mut checksum := 0
  for _ in [0:trials] do
    let result ← batch input iterations
    elapsed := elapsed.push result.1
    checksum := checksum + result.2
  let perIteration := elapsed.map (· / iterations)
  let sorted := perIteration.qsort (· < ·)
  let total := perIteration.foldl (· + ·) 0
  IO.println s!"{name}: {trials} trials × {iterations} iterations"
  let samples := String.intercalate ", "
    (perIteration.toList.map formatDuration)
  IO.println s!"  samples: [{samples}]"
  IO.println s!"  min/median/mean/max: {formatDuration sorted[0]!} / {formatDuration sorted[trials / 2]!} / {formatDuration (total / trials)} / {formatDuration sorted[trials - 1]!}"
  IO.println s!"  checksum: {checksum}"

def main : IO Unit := do
  let packedA := packSha2562KBMessage sampleA
  let packedZero := packSha2562KBMessage sampleZero
  let packedPattern := packSha2562KBMessage samplePattern
  benchmark "packed 'a' input → packed witness" runPackedWordsBatch packedA 200 20
  benchmark "packed zero input → packed witness" runPackedWordsBatch packedZero 200 20
  benchmark "packed patterned input → packed witness" runPackedWordsBatch packedPattern 200 20
  benchmark "Bool input adapter → packed witness" runBoolInputBatch sampleA 200 20
  benchmark "Bool input → materialized Array Bool" runBoolArrayBatch sampleA 100 12
