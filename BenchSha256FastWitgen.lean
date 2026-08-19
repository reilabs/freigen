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

/-!
The large-message cases below deliberately do not define circuits. They are
benchmark-only mocks which run the same packed SHA-256 compression and emit
the same hints per block as the proved 2 KiB fast witgen.

Both mock sizes are multiples of a SHA-256 block, so each message is followed
by exactly one padding block.
-/

def sha2561MBMessageBytes : Nat := 1024 * 1024
def sha25610MBMessageBytes : Nat := 10 * 1024 * 1024
def sha25630MBMessageBytes : Nat := 30 * 1024 * 1024

structure Sha256LargeMockInput where
  messageBytes : Nat
  packedWords : Array UInt64

structure Sha256LargeMockWitness where
  words : Array UInt64
  bitCount : Nat

def makeSha256LargeMockInput (messageBytes : Nat) : Sha256LargeMockInput :=
  { messageBytes
    -- A packed all-zero message keeps setup cheap and outside the timed region.
    packedWords := Array.replicate ((messageBytes + 7) / 8) 0 }

/-- Benchmark-only model of a future large fixed-size fast witgen. -/
def sha256LargeFastWitgenMock
    (input : Sha256LargeMockInput) : Sha256LargeMockWitness :=
  let dataBlocks := input.messageBytes / 64
  let blockCount := dataBlocks + 1
  let messageBits := input.messageBytes * 8
  let bitCount := messageBits +
    blockCount * Sha256FastWitgen.witnessBitsPerBlock
  let witnessWords := (bitCount + 63) / 64
  let blocks := Array.ofFn fun i : Fin (blockCount * 16) =>
    if i.val < dataBlocks * 16 then
      let packed := input.packedWords[i.val / 2]!
      if i.val % 2 = 0 then Sha256FastWitgen.reverseBits32 packed.toUInt32
      else Sha256FastWitgen.reverseBits32 (packed >>> 32).toUInt32
    else if i.val = dataBlocks * 16 then
      (0x80000000 : UInt32)
    else if i.val = blockCount * 16 - 2 then
      UInt32.ofNat (messageBits / 4294967296)
    else if i.val = blockCount * 16 - 1 then
      UInt32.ofNat messageBits
    else
      0
  let builder : Sha256FastWitgen.WitnessBuilder :=
    { words := (Array.mkEmpty witnessWords).append input.packedWords
      pending := 0
      pendingBits := 0 }
  let result := Sha256FastWitgen.compressBlocksLoop blocks 0 blockCount
    Sha256FastWitgen.initialState builder
  let builder := result.2
  let words := if builder.pendingBits = 0 then builder.words
    else builder.words.push builder.pending
  { words, bitCount }

def sha2561MBFastWitgenMock
    (input : Sha256LargeMockInput) : Sha256LargeMockWitness :=
  sha256LargeFastWitgenMock input

def sha25610MBFastWitgenMock
    (input : Sha256LargeMockInput) : Sha256LargeMockWitness :=
  sha256LargeFastWitgenMock input

def sha25630MBFastWitgenMock
    (input : Sha256LargeMockInput) : Sha256LargeMockWitness :=
  sha256LargeFastWitgenMock input

@[inline] def Sha256LargeMockWitness.get
    (witness : Sha256LargeMockWitness) (i : Nat) : Bool :=
  if i < witness.bitCount then
    match witness.words[i / 64]? with
    | some word => ((word >>> UInt64.ofNat (i % 64)) &&& 1) != 0
    | none => false
  else
    false

def largeMockLoop
    (witgen : Sha256LargeMockInput → Sha256LargeMockWitness)
    (input : Sha256LargeMockInput) :
    (iterations : Nat) → (index : Nat) → (checksum : Nat) → Nat
  | 0, _, checksum => checksum
  | iterations + 1, index, checksum =>
    let witness := witgen input
    let checksum := checksum + witness.words.size +
      if witness.get ((index * 7919) % witness.bitCount) then 1 else 0
    largeMockLoop witgen input iterations (index + 1) checksum

def runLargeMockBatch
    (witgen : Sha256LargeMockInput → Sha256LargeMockWitness)
    (input : Sha256LargeMockInput) (iterations : Nat) : IO (Nat × Nat) := do
  let result ← IO.mkRef 0
  let start ← IO.monoNanosNow
  result.set (largeMockLoop witgen input iterations 0 0)
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
    (iterations trials : Nat) (warmupIterations : Nat := 20) : IO Unit := do
  let _ ← batch input warmupIterations
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
  let oneMB := makeSha256LargeMockInput sha2561MBMessageBytes
  let tenMB := makeSha256LargeMockInput sha25610MBMessageBytes
  let thirtyMB := makeSha256LargeMockInput sha25630MBMessageBytes
  benchmark "1 MB packed input → packed witness (mock; no circuit)"
    (runLargeMockBatch sha2561MBFastWitgenMock) oneMB 1 10 0
  benchmark "10 MB packed input → packed witness (mock; no circuit)"
    (runLargeMockBatch sha25610MBFastWitgenMock) tenMB 1 10 0
  benchmark "30 MB packed input → packed witness (mock; no circuit)"
    (runLargeMockBatch sha25630MBFastWitgenMock) thirtyMB 1 10 0
