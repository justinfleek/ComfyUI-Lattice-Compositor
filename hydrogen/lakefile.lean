import Lake
open Lake DSL

package hydrogen where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- PRISM color math is integrated directly into Hydrogen.Schema.Color.Real
-- Original source: https://github.com/justinfleek/PRISM/tree/main/core/lean4

@[default_target]
lean_lib Hydrogen where
  srcDir := "proofs"

lean_exe hue where
  root := `Hydrogen.Schema.Color.Hue

lean_exe conversions where
  root := `Hydrogen.Schema.Color.Conversions

lean_exe math where
  root := `Hydrogen.Math
