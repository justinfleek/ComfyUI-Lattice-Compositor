import Lake
open Lake DSL

package «tensor-core» where
  preferReleaseBuild := true

-- Override transitive dependencies with our patched versions for Lean 4.27.0-rc1 compatibility
-- These are self-contained in patched-deps/ to ensure builds work for all users
--
-- WORKAROUND: requireDecl (require X from "path") is not implemented in Lean 4.27.0-rc1
-- Using git with file:// URLs as a workaround. The "./" prefix makes paths relative to the lakefile.
-- Note: `lake update` may fail with these local dependencies; use `lake build` instead.
-- TODO: Once requireDecl is implemented, change to: require Qq from "patched-deps/Qq"
require Qq from git "file:///./patched-deps/Qq"
require aesop from git "file:///./patched-deps/aesop"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

require scilean from git
  "https://github.com/lecopivo/SciLean"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.27.0-rc1"

lean_lib «TensorCore» where
  srcDir := "."

lean_lib «Color» where
  srcDir := "."

lean_lib «Interpolation» where
  srcDir := "Interpolation"

lean_lib «Determinism» where
  srcDir := "Determinism"

lean_lib «Lattice» where
  srcDir := "."

lean_lib «Compass» where
  srcDir := "."

@[default_target]
lean_exe «tensor-core» where
  root := `Main

-- Extraction executable - generates Elm/Python/C from proofs
lean_exe «extract» where
  root := `ExtractMain
