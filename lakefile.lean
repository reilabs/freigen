import Lake

open Lake DSL

package freigen

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib Freigen where
  -- Include every `Freigen.*` module, even when the umbrella does not import it.
  globs := #[.andSubmodules `Freigen]

@[default_target]
lean_exe freigen where
  root := `Main
