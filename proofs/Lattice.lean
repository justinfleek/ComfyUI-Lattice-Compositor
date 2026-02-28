/-
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // lattice // proofs
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  LATTICE LEAN4 PROOFS — AGENT BOUNDS AND PARAMETERS

  "We are LITERALLY creating the bounds and parameters that AI agents will
   live in."

  This module aggregates all Lattice proofs for:

  ┌─────────────────────────────────────────────────────────────────────────────┐
  │ Math         │ Bounded types, Vec3 — foundational math                     │
  │ Scale        │ CRDT convergence for distributed state                      │
  │ GPU          │ Diffusion bounds, NVFP4 precision proofs                    │
  │ Reset        │ Minimum viable safety specifications                        │
  └─────────────────────────────────────────────────────────────────────────────┘

  The Core Insight:
    At billion-agent scale, the infrastructure agents operate on CANNOT be
    "hopefully correct". It must be PROVABLY correct. These proofs ARE the
    bounds and parameters. If a proof doesn't exist, the property isn't
    guaranteed.

-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- MATH (Foundational Types with Proven Bounds)
-- ═══════════════════════════════════════════════════════════════════════════════

import Lattice.Math.Bounded
import Lattice.Math.Vec3

-- ═══════════════════════════════════════════════════════════════════════════════
-- SCALE (Billion-Agent Coordination Proofs)
-- ═══════════════════════════════════════════════════════════════════════════════

import Lattice.Scale.CRDT

-- ═══════════════════════════════════════════════════════════════════════════════
-- GPU (Diffusion Bounds, NVFP4 Precision)
-- ═══════════════════════════════════════════════════════════════════════════════

import Lattice.GPU.Diffusion
import Lattice.GPU.Precision

-- ═══════════════════════════════════════════════════════════════════════════════
-- RESET (Minimum Viable Safety for AI Systems)
-- ═══════════════════════════════════════════════════════════════════════════════

import Lattice.Reset
