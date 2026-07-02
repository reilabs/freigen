import Freigen

/-!
# Compiling a library-provided program

`#compile` works on *any* `Free` program in scope — here Freigen's own Poseidon hash (BN254 `Fr`,
reference constants).  The emitted artifact keeps the source's structure: named `def`s
(`ark`/`mix`/`sbox`/…), `fold`/`gen` loops, no inlining — and only exists because its
`≈`-soundness proof type-checks.  Together with `Program.lean` this exercises **multi-artifact**
emission: `lake build Client:prog` writes both files.
-/

namespace Client
open Freigen

#compile Freigen.Poseidon.poseidonF => "out/poseidon.prog"

end Client
