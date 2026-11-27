import Lake

open Lake DSL

package freigen

@[default_target]
lean_lib Freigen where
  -- Include every core module, even when the umbrella does not import it.
  roots := #[]
  globs := #[.one `Freigen, .one `Freigen.Basic, .one `Freigen.Iso, .one `Freigen.Wheels,
    .one `Freigen.Eff, .one `Freigen.ExactCodensity, .submodules `Freigen.IxPoly,
    .submodules `Freigen.ITree, .submodules `Freigen.Free, .submodules `Freigen.CompM,
    .submodules `Freigen.Ast]

@[default_target]
lean_exe freigen where
  root := `Main
