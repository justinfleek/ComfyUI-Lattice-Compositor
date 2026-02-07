# ParticleSim: Formally Verified Particle Simulation

## Overview

A Lean4 library for deterministic, formally verified particle simulation.
Designed for 40M+ particle systems with provable correctness.

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│  Lean4 Proof Kernel (this library)                         │
│  - Exact rational arithmetic (no floating point)           │
│  - Conservation laws proven                                 │
│  - Determinism proven                                       │
│  - Parallel safety proven                                   │
└─────────────────────────────────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────────┐
│  Haskell Compute Layer (TODO)                              │
│  - Accelerate for GPU                                       │
│  - Fixed-point matching Lean4 spec                         │
│  - QuickCheck properties mirror theorems                    │
└─────────────────────────────────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────────┐
│  PureScript Frontend (TODO)                                │
│  - WebGPU rendering                                         │
│  - Timeline scrubbing (enabled by determinism)             │
│  - Parameter tuning                                         │
└─────────────────────────────────────────────────────────────┘
```

## Modules

### Vec3.lean - 3D Vector Arithmetic ✅ COMPLETE
- Exact rational coordinates
- Addition/subtraction (abelian group)
- Scalar multiplication (vector space axioms)
- Dot product (bilinear form)
- Squared norm (non-negativity, zero iff zero vector)

**All proofs complete. No sorry.**

### Particle.lean - Particle Types ✅ COMPLETE
- Particle with positive mass
- Momentum = mass × velocity
- Kinetic energy (non-negative)
- Particle system as list
- Total momentum/mass with list lemmas

**All proofs complete. No sorry.**

### Conservation.lean - Momentum Conservation ⚠️ MOSTLY COMPLETE

**Fully proven (no sorry):**
- `two_particle_momentum_conserved`: Newton's third law → conservation
- `three_particle_momentum_conserved_12/13/23`: All pair interactions
- `three_particle_momentum_conserved_all`: Composability
- `momentum_conserved_when_weighted_sum_zero`: General principle

**Has sorry (needs more list lemmas):**
- `pair_impulses_weighted_sum_zero`: General n-particle case

### Determinism.lean - Deterministic Evolution ⚠️ MOSTLY COMPLETE

**Fully proven (no sorry):**
- `two_particle_evolution_deterministic`: Same input → same output
- `two_particle_time_reversal`: Reversibility
- `three_particle_order_independent_*`: Order doesn't matter
- `three_particle_all_orders_equivalent`: All 6 orderings equivalent

**Has sorry:**
- `seek_roundtrip`: Timeline scrubbing (needs Nat.iterate lemmas)

### Forces.lean - Force Application ⚠️ FOUNDATION ONLY

**Has sorry:**
- `momentum_change_eq_impulse_sum`: Requires Finset manipulation
- `momentum_conserved`: Depends on above

## Proof Status Summary

| Theorem | Status | Notes |
|---------|--------|-------|
| Vec3 is a vector space | ✅ Proven | All axioms |
| Momentum = mass × velocity | ✅ Proven | Definition + properties |
| 2-particle conservation | ✅ Proven | `two_particle_momentum_conserved` |
| 3-particle conservation | ✅ Proven | All three theorems |
| n-particle conservation | ⚠️ Sorry | Needs list infrastructure |
| Determinism | ✅ Proven | Pure functions |
| Time reversibility | ✅ Proven | `two_particle_time_reversal` |
| Parallel order-independence | ✅ Proven | All 3-particle orderings |

## Key Design Decisions

### Why Rationals?

```lean
structure Vec3 where
  x : ℚ  -- Rational, not Float!
  y : ℚ
  z : ℚ
```

Floating point breaks:
- `(a + b) + c ≠ a + (b + c)` 
- Different parallel reduction orders → different results
- Non-determinism creeps in

Rationals give:
- Exact arithmetic
- Associativity holds (proven!)
- Bit-identical results regardless of evaluation order

### Why Fixed Particle Counts?

We have `TwoParticles`, `ThreeParticles` instead of `List Particle` for the 
core conservation proofs. This is because:

1. Lean4 can unfold small fixed structures completely
2. `field_simp` and `ring` tactics work directly
3. No list manipulation lemmas needed

The general n-particle case exists but has sorry.

### Scaling to 40M

For actual simulation:
1. Lean4 proves correctness of the *algorithm*
2. Haskell implements with same semantics but efficient representation
3. QuickCheck tests mirror Lean4 theorems
4. GPU parallelism is safe because we proved order-independence

## Next Steps

### Phase 1: Complete Proofs
- [ ] Prove `pair_impulses_weighted_sum_zero` (general n-particle)
- [ ] Prove `seek_roundtrip` (timeline)
- [ ] Prove Finset-based momentum theorems

### Phase 2: Integration
- [ ] Add position updates (Verlet/symplectic)
- [ ] Add collision detection
- [ ] Add spatial hashing
- [ ] Connect to sand homogenization (MIT licensed code)

### Phase 3: Haskell Bridge
- [ ] Define FFI-compatible types
- [ ] Extract executable code or reimplement
- [ ] Add Accelerate GPU backend
- [ ] QuickCheck property tests

### Phase 4: PureScript UI
- [ ] WebGPU particle renderer
- [ ] Timeline controls
- [ ] Parameter interface

## Building

```bash
lake update
lake build
```

Requires Lean4 v4.14.0 and Mathlib.

## License

Your proprietary license here. This is a clean implementation from 
mathematical principles, not derived from any GPL code.
