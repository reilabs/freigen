import Freigen
import Lean

open Lean Meta

/-- Render one recorded artifact: evaluate `Freigen.render decl.1` (a `String`) and write it to
    `path`, creating parent directories.  Runs in `MetaM` so instance synthesis picks up the
    declaration's `[DSL]` instance; `evalExpr` runs the pretty-printer over the imported code. -/
unsafe def emitEntry (path : String) (decl : Name) : MetaM Unit := do
  let closed ← mkAppM ``Subtype.val #[mkConst decl]        -- decl.1 : the `Closed` program
  let e ← mkAppM ``Freigen.render #[closed]                -- render decl.1 : String
  let contents ← evalExpr String (mkConst ``String) e
  let p : System.FilePath := path
  if let some dir := p.parent then IO.FS.createDirAll dir
  IO.FS.writeFile p contents
  IO.println s!"freigen: emitted {path} ({contents.length} bytes)"

/-- Import the given modules (loading env extensions) and flush every `#compile` artifact to disk. -/
unsafe def runImpl (args : List String) : IO Unit := do
  if args.isEmpty then
    IO.eprintln "usage: freigen <Module.Name> [Module.Name …]"
    IO.Process.exit 1
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let targetMods := args.foldl (·.insert ·.toName) (∅ : NameSet)
  let imports := args.toArray.map fun m => { module := m.toName : Import }
  let env ← importModules imports {} (loadExts := true)
  -- Emit only artifacts declared *in the requested library's own modules*, not ones pulled in
  -- transitively from dependencies (e.g. Freigen's own examples).
  let arts := Freigen.compileExt.getState env |>.filter fun (_, decl) =>
    match env.getModuleIdxFor? decl with
    | some idx => targetMods.contains env.header.moduleNames[idx.toNat]!
    | none     => false
  if arts.isEmpty then
    IO.println "freigen: no `#compile` artifacts found in the given modules"
    return
  let act : MetaM Unit := arts.forM fun (path, decl) => emitEntry path decl
  let ctx : Core.Context := { fileName := "<freigen>", fileMap := default }
  discard <| (act.run').toIO ctx { env }

@[implemented_by runImpl]
def run (_args : List String) : IO Unit := pure ()

/-- The `freigen` emitter, invoked by the `lake build <lib>:prog` facet with the target library's
    modules and an augmented `LEAN_PATH`. -/
def main (args : List String) : IO Unit := run args
