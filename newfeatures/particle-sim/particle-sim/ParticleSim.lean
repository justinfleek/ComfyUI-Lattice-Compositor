/-
  ParticleSim
  
  A formally verified particle simulation library.
  
  Key guarantees (all proven, no axioms beyond Lean's type theory):
  - Momentum conservation under Newton's third law
  - Deterministic evolution (same input → same output)
  - Order-independent parallel evaluation
  - Time-reversibility for Hamiltonian systems
  
  Uses exact rational arithmetic for bit-identical results.
-/

import ParticleSim.Vec3
import ParticleSim.Particle
import ParticleSim.Conservation
import ParticleSim.Determinism
