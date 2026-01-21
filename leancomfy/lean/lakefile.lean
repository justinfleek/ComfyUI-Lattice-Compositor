import Lake
open Lake DSL

package «tensor-core» where
  preferReleaseBuild := true

lean_lib «TensorCore» where
  srcDir := "."

@[default_target]
lean_exe «tensor-core» where
  root := `Main

-- Extraction executable - generates Elm/Python/C from proofs
lean_exe «extract» where
  root := `ExtractMain
