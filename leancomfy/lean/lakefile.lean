import Lake
open Lake DSL

package «tensor-core» where
  preferReleaseBuild := true

-- All dependencies fetched from git for reproducible Nix builds
-- Note: batteries, Qq, aesop are pulled transitively through mathlib
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.26.0"

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
