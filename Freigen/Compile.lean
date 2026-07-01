import Freigen.Ast
import Lean.Elab.Command

/-!
# Compilation front-end: from a `Free` program to a file on disk

`reflect%` produces a `Prog` (+ its `≈`-soundness); `pp` renders one to a `String`.  This module turns
that capability into a *devex*:

* a **`DSL`** type-class carrying the per-signature op/scope naming, so `render` needs no ad-hoc
  arguments (killing the hand-rolled `ppCirc`/`ppStore` wrappers);
* a persistent **environment extension** (`compileExt`) recording *which declarations* to emit and
  *where*;
* a **`#compile foo => "path"`** command that records `(path, foo)` at elaboration time — **no file
  is written and nothing is evaluated here**, so the editor never touches the disk while you type,
  and elaboration stays cheap.

Rendering (running the pretty-printer) is deferred to the `freigen` executable, which — being a
compiled binary — can evaluate `render foo.1` after importing the library.  The `lake build
<lib>:prog` facet wires the two together.  Because `foo` must be a `reflect%` result (a `{ Closed //
≈-soundness }` pair), the recorded declaration only exists if its soundness proof type-checks:
**every emitted file is certified `≈` its source.**
-/

open Lean Elab Command

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

/-- `#compile foo => "path"` records the reflected program `foo` for `lake build <lib>:prog` to
    render and write to `path`.  `foo` is an identifier naming a `reflect%` result (a `{ Closed //
    ≈-soundness }` pair) whose signature has a `[DSL]` instance. -/
elab "#compile " id:ident " => " path:str : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverload id
  modifyEnv (compileExt.addEntry · (path.getString, name))

end Freigen
