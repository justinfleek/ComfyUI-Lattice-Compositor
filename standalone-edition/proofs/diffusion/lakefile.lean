import Lake
open Lake DSL

package diffusion where
  -- Options for the Lean compiler
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.unicode.fun, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

@[default_target]
lean_lib Diffusion where
  roots := #[`Diffusion.Tensor, `Diffusion.Operations]
  globs := #[.submodules `Diffusion]
