import Lake
open Lake DSL

package freigen where
  version := v!"0.1.0"

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib Freigen where
  -- build every `Freigen.*` module, imported by the umbrella or not — an orphan module must fail
  -- CI rather than silently go unchecked
  globs := #[.andSubmodules `Freigen]

@[default_target]
lean_exe freigen where
  root := `Main
  -- the emitter runs the pretty-printer over imported code via the interpreter
  supportInterpreter := true

/--
`lake build <lib>:prog` — flush every `#compile` artifact recorded by the modules of `<lib>` to disk.

Reflection + rendering happen at the library's *elaboration* time (each `#compile` records the
rendered string into a persistent env extension); this facet just builds the library, then runs the
`freigen` emitter over its modules with the workspace's augmented `LEAN_PATH` so the emitter can
import them and write the files out.  Works on any downstream library that depends on Freigen.
-/
library_facet prog (lib : LeanLib) : Unit := do
  let ws ← getWorkspace
  let some exe := ws.findLeanExe? `freigen
    | do logError "freigen: could not find the `freigen` executable in the workspace"; return .nil
  -- Build the emitter and the target library's oleans, and collect the library's modules.
  let exePath ← (← exe.exe.fetch).await
  let _ ← (← lib.leanArts.fetch).await
  let mods ← (← lib.modules.fetch).await
  let env ← getAugmentedEnv
  let args := mods.map (·.name.toString)
  let out ← IO.Process.output { cmd := exePath.toString, args, env }
  if out.exitCode == 0 then
    unless out.stdout.isEmpty do logInfo out.stdout
  else
    logError s!"freigen emit failed (exit {out.exitCode}):\n{out.stdout}{out.stderr}"
  return .nil
