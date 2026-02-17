import Lake
open Lake DSL

package compass where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib Compass where
  roots := #[
    `Compass.Lattice.Basic,
    `Compass.Merkle.Integrity,
    `Compass.Inference.TierProofs,
    `Compass.CAS.Correctness
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
