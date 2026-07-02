import Freigen.Ast
import Freigen.Reflect
import Lean.Elab.Command
import Lean.Elab.SyntheticMVars

/-!
# Compilation front-end: from a `Free` program to a file on disk

`reflect%` produces a `Prog` (+ its `≈`-soundness); `pp` renders one to a `String`.  This module turns
that capability into a *devex*:

* a **`DSL`** type-class carrying the per-signature op/scope naming, so `render` needs no ad-hoc
  arguments (killing the hand-rolled `ppCirc`/`ppStore` wrappers);
* a persistent **environment extension** (`compileExt`) recording *which declarations* to emit and
  *where*;
* a **`#compile prog => "path"`** command that takes the **raw `Free` program** `prog` directly —
  it reflects it for you (`reflect% prog`) into a kernel-checked auxiliary definition and records
  `(path, that def)`.  No `reflect%` boilerplate, no file written and no pretty-printing here, so the
  editor never touches the disk while you type.

Rendering (running the pretty-printer) is deferred to the `freigen` executable, which — being a
compiled binary — evaluates `render foo.1` after importing the library, and also prints the
`≈`-soundness statement proved by the reflection for your inspection.  The `lake build <lib>:prog`
facet wires the two together.  Because `#compile prog` elaborates `reflect% prog` (a `{ Closed //
≈-soundness }` pair) into a real definition, the artifact only exists if its soundness proof
type-checks: **every emitted file is certified `≈` its source.**
-/

open Lean Elab Command Term Meta

namespace Freigen

/-- The per-DSL data `pp`/`render` need: how to name each first-order op and each scoped construct.
    One `instance` per signature replaces threading `name`/`sname` through every call site. -/
class DSL (Op : Type → Type → Type 1) (SOp : Type → Type) where
  /-- Print a first-order op (`Op I R`) as its surface name, e.g. `assert`. -/
  opName : {I R : Type} → Op I R → String
  /-- Print a scoped construct (`SOp β`) as its surface name, e.g. `hint`. -/
  scopeName : {β : Type} → SOp β → String

/-- Render a closed program using its DSL instance — the argument-free `pp`. -/
def render {Op SOp} [inst : DSL Op SOp] {mainArgs α} (c : Closed Op SOp mainArgs α) : String :=
  pp inst.opName inst.scopeName c

/-! ## The artifact registry -/

/-- One compilation artifact: an output path and the reflected declaration to render into it. -/
abbrev Artifact := String × Name

/-- Persistent env extension collecting every `#compile` artifact in a module.  The `freigen`
    executable reads this (with `loadExts := true`) after importing a library. -/
initialize compileExt : SimplePersistentEnvExtension Artifact (Array Artifact) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun ass => ass.foldl (· ++ ·) #[]
  }

/-- `#compile prog => "path"` reflects the raw `Free` program `prog` (`reflect% prog`) into a
    kernel-checked auxiliary definition and records it for `lake build <lib>:prog` to render and
    write to `path`.  `prog` is anything `reflect%` accepts — a value, a function of its inputs, or a
    structural recursion — whose signature has a `[DSL]` instance. -/
elab "#compile " prog:term " => " path:str : command => do
  -- Reflect `prog` and its soundness proof, fully elaborated and closed.
  let (value, type, levelParams) ← liftTermElabM do
    let e ← elabTermAndSynthesize (← `(reflect% $prog)) none
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let type ← instantiateMVars (← inferType e)
    let levelParams := (collectLevelParams (collectLevelParams {} e) type).params.toList
    pure (e, type, levelParams)
  -- Materialise it as a compiled definition (kernel-checks the ≈-soundness proof; lets the emitter
  -- evaluate `render`).  Name it after the source, uniquely per module.
  let base : Name := if prog.raw.isIdent then prog.raw.getId else `compiled
  let idx := (compileExt.getState (← getEnv)).size
  let auxName := (← getMainModule) ++ base ++ Name.mkSimple s!"reflected_{idx}"
  liftCoreM <| addAndCompile <| .defnDecl {
    name := auxName, levelParams, type, value
    hints := .opaque, safety := .safe, all := [auxName] }
  modifyEnv (compileExt.addEntry · (path.getString, auxName))

end Freigen
