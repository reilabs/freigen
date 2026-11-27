import Lake

open Lake DSL

package freigen_circuit

require freigen from ".."
require "leanprover-community" / "mathlib"

@[default_target]
lean_lib FreigenCircuit where
  roots := #[]
  globs := #[.submodules `Freigen.Circuit, .submodules `Freigen.F2Z]

lean_exe sha256_fast_witgen_bench where
  root := `BenchSha256FastWitgen
