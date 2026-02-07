import Lake
open Lake DSL

package compass where
  preferReleaseBuild := true

-- Core mathematical foundations
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.26.0"

-- SciLean included locally for compatibility with current Lean version

-- Cryptographic primitives for security proofs
require aesop from git
  "https://github.com/JLimperg/aesop" @ "master"

@[default_target]
lean_lib Compass where
  srcDir := "."
  roots := #[`Compass]

lean_lib SciLean where
  srcDir := "SciLean"
  roots := #[`SciLean]

lean_exe «compass-extract» where
  root := `CompassExtractMain
  supportInterpreter := true
