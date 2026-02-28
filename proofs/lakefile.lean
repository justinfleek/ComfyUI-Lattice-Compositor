-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // lattice // proofs // lake
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
--    "A pixel is not just a color. A pixel is a potential location for an
--     agent's body."
--
--                                                           — AGENT_EMBODIMENT
--
-- Lattice Lean4 Proofs: Formal verification for agent bounds and parameters.
-- These proofs define the immutable laws that AI agents operate within.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

import Lake
open Lake DSL

package lattice where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.7.0"

@[default_target]
lean_lib Lattice where
  roots := #[`Lattice]
  -- Only build modules explicitly imported in Lattice.lean
  -- globs := #[.submodules `Lattice]
