import Lake
open Lake DSL

package mycircuits where

-- Depend on Freigen from the repo root.  In a real project this would be a git `require`, e.g.
--   require freigen from git "https://github.com/reilabs/freigen" @ "main"
require freigen from ".." / ".."

@[default_target]
lean_lib MyCircuits where
