import Lake
open Lake DSL

package «tensor-core» where
  preferReleaseBuild := true

require Qq from "patched-deps/Qq"
require aesop from "patched-deps/aesop"
require mathlib from git "https://github.com/leanprover-community/mathlib4"
require scilean from git "https://github.com/lecopivo/SciLean"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.27.0-rc1"

@[default_target]
lean_lib TensorCore

lean_lib Color

lean_lib Interpolation where
  srcDir := "Interpolation"

lean_lib Determinism where
  srcDir := "Determinism"

lean_lib Lattice

lean_lib Compass

lean_exe «tensor-core» {
  root := `Main
}

lean_exe extract {
  root := `ExtractMain
}
