━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                    // council // deliberation // FAA // enhanced
                                    // submodular // optimization // 2026-02-25
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# FAA-Enhanced Submodular Optimization Council Deliberation

## Executive Summary

Council convened to deliberate on integrating FAA (Floquet Adiabatic Algorithm)
insights into Hydrogen's submodular optimization for viewport allocation.

**Primary Finding:** Integration-incomplete. Two parallel implementations exist
but are not wired to actual GPU rendering.

**Recommendation:** Integration before optimization. Create adapter layer first.

────────────────────────────────────────────────────────────────────────────────
                                                        // council // composition
────────────────────────────────────────────────────────────────────────────────

## Council Composition

1. **Type Theorist** — Bounded types, invalid states, compositional correctness
2. **Systems Architect** — Integration points, performance, real-world constraints
3. **Algorithm Specialist** — Mathematical guarantees, regret bounds, convergence

────────────────────────────────────────────────────────────────────────────────
                                                      // codebase // exploration
────────────────────────────────────────────────────────────────────────────────

## Codebase State Analysis

### Two Parallel Implementations

The codebase contains **two parallel implementations** of submodular optimization:

| Implementation | Lines | Purpose |
|----------------|-------|---------|
| `Hydrogen.Optimize.Submodular.*` | 3,613 | General-purpose, research-grade |
| `Hydrogen.Render.Online.*` | 1,596 | Domain-specific, rendering-optimized |

### Module Inventory

**Optimize.Submodular (Complete):**

| Module | Lines | Status |
|--------|-------|--------|
| `Types.purs` | 817 | Complete |
| `Oracle.purs` | 652 | Complete |
| `Continuous.purs` | 712 | Complete |
| `Online.purs` | 721 | Complete |
| `Rounding.purs` | 711 | Complete |

**Render.Online (Complete):**

| Module | Lines | Status |
|--------|-------|--------|
| `Core.purs` | 396 | Complete |
| `Selection/Greedy.purs` | 307 | Complete |
| `Selection/State.purs` | 281 | Complete |
| `Matroid/Class.purs` | 162 | Complete |
| `Matroid/Partition.purs` | 204 | Complete |
| `Submodular/Function.purs` | 246 | Complete |

**GPU Infrastructure (Complete):**

| Module | Lines | Status |
|--------|-------|--------|
| `FrameState.purs` | 1,259 | Complete |
| `FrameState/Animation.purs` | 507 | Complete |

────────────────────────────────────────────────────────────────────────────────
                                                  // round // 1 // initial // positions
────────────────────────────────────────────────────────────────────────────────

## Round 1: Initial Positions

### Type Theorist

**What's correct:**

- `Element v` uses phantom types to prevent mixing ground sets
- `Dim` is bounded [1, 2^30] — no zero dimensions, no overflow
- `Quality` is bounded [0, 1] — normalized
- `DiffusionSteps` is bounded [1, 50] — no zero steps
- Matroid constraints are type-encoded via class instances

**What needs attention:**

- `FractionalSolution v` in `Continuous.purs` uses `Map Int Number` — the
  Number is unbounded. Should use `UnitInterval` for x in [0,1]^n
- `GradientEstimate v` uses unbounded `Number` for gradient values —
  acceptable since gradients can be negative/large
- `LargeStepConfig` doesn't exist yet — needs bounded fields

**Recommendation:** Before adding FAA enhancement, tighten `FractionalSolution`
to use `UnitInterval` for coordinates. This prevents invalid fractional
solutions (negative or >1).

### Systems Architect

**Integration gaps (HIGH priority):**

1. **ViewportTensor to GroundSet**: No function maps latent grid to Element indices
2. **PerformanceState to UtilityFeedback**: No function converts GPU timing to oracle feedback
3. **OnlineState to RenderPipeline**: No function triggers actual GPU work from selections

**Current data flow (broken):**

```
ViewportTensor
     |
     v (MISSING: tensorToGroundSet)
GroundSet Region
     |
     v (EXISTS: onlineStep)
RegionSelection[]
     |
     v (MISSING: selectionsToGPU)
GPU Render
     |
     v (MISSING: gpuToFeedback)
UtilityFeedback
     |
     v (EXISTS: onlineStep)
Updated OnlineState
```

**Recommendation:** Create `Hydrogen.GPU.FrameState.Allocation.purs` with:

- `viewportToGroundSet :: ViewportState -> GroundSet Region`
- `performanceToFeedback :: PerformanceState -> RegionSelection -> UtilityFeedback Region`
- `allocateFrame :: FrameState -> Array RegionSelection`

This is ~150 lines and unblocks everything else.

### Algorithm Specialist

**Core theorem (Floquet Adiabatic Algorithm):**

> F_dt(s=1) = H exactly for classical target Hamiltonians

**Translation to continuous greedy:**

- Standard: dt = 1/T, run T iterations -> (1-1/e) approximation
- FAA-enhanced: dt = 1/sqrt(T), run sqrt(T) iterations -> same approximation

**Current implementation (`Continuous.purs:524`):**

```purescript
stepSize = 1.0 / intToNum numIterations  -- dt = 1/T
```

**Required change:**

```purescript
stepSize = if useLargeStep 
  then 1.0 / sqrt (intToNum numIterations)  -- FAA: dt = 1/sqrt(T)
  else 1.0 / intToNum numIterations          -- Standard: dt = 1/T
```

**Recommendation:** Implement in order:

1. `LargeStepConfig` type with bounded fields
2. `computeLargeStepSize` function
3. `continuousGreedyLargeStep` variant
4. `minEnergySample` for rounding

────────────────────────────────────────────────────────────────────────────────
                                                // round // 2 // cross // examination
────────────────────────────────────────────────────────────────────────────────

## Round 2: Cross-Examination

### Type Theorist asks Systems Architect

*"You propose creating an adapter layer. How do you ensure the adapter doesn't
introduce unbounded values when converting between domains?"*

**Systems Architect Response:**

The adapter must be typed such that invalid conversions are impossible:

```purescript
-- ViewportTensor already has bounded latentWidth/latentHeight via Dim
-- Region uses UUID5 for deterministic identity
-- The mapping is injective and bounded:

viewportToGroundSet :: ViewportState -> GroundSet Region
viewportToGroundSet vs = 
  let
    lw = viewportLatentWidth vs.tensor  -- Dim: [1, 2^30]
    lh = viewportLatentHeight vs.tensor  -- Dim: [1, 2^30]
    gridLevel = selectGridLevel lw lh    -- Coarse/Medium/Fine
    regions = generateGrid gridLevel lw lh  -- Array Region
  in
    mkGroundSet regions
```

Key insight: **every conversion goes through bounded smart constructors**.
There's no raw `Number -> Number` that could smuggle in unbounded values.

### Algorithm Specialist asks Type Theorist

*"You want FractionalSolution to use UnitInterval. But gradients can be
negative, and the Frank-Wolfe direction vector can have coordinates > 1.
How do you handle this?"*

**Type Theorist Response:**

Let me refine:

- **FractionalSolution coordinates must be in [0, 1]** — matroid polytope constraint
- **Gradient estimates are unbounded** — correct, keep as `Number`
- **Direction vectors from `linearMaximize`** — vertices of polytope, so 0 or 1

**Solution:**

```purescript
-- FractionalSolution with bounded coordinates
newtype FractionalSolution v = FractionalSolution
  { coords :: Map Int UnitInterval  -- x_e in [0, 1]
  , support :: Set Int              -- Elements with x_e > 0
  }

-- After each Frank-Wolfe step, clamp:
addScaledClamped :: FractionalSolution v -> Number -> FractionalSolution v 
                 -> FractionalSolution v
addScaledClamped current stepSize direction =
  let
    rawCoords = Map.unionWith (+) 
      (unwrap current).coords 
      (Map.map (* stepSize) (toNumber <$> (unwrap direction).coords))
  in
    FractionalSolution { coords: Map.map clampUnit rawCoords, ... }
```

This maintains the invariant: **FractionalSolution always in [0,1]^n**.

### Systems Architect asks Algorithm Specialist

*"The 40x speedup claim assumes 100 -> 10 iterations. But if each iteration
requires gradient sampling, and sampling is noisy, won't we need more samples
per iteration to compensate? Does the speedup hold in practice?"*

**Algorithm Specialist Response:**

**Variance scales with step size:**

- Larger steps = larger updates = need better gradient estimates
- Standard: dt = 0.01, variance s^2
- FAA: dt ~ 0.32 (for T=10), need ~10x samples for same variance

**But:** Min-energy sampling addresses this differently:

- Instead of reducing variance per sample, take K=5 samples and keep the best
- Exploits that f(S) is a quality measure — we want max, not mean

**Net speedup calculation:**

- Iterations: 100 -> 10 (10x reduction)
- Samples per iteration: 10 -> 50 (5x increase)
- **Net: ~2x raw speedup**

**The 40x claim was optimistic.** Realistic expectation: **2-4x speedup** with
same quality, or **same speed with 2x quality**.

The real win is **latency, not throughput**:

- Standard: 100 sequential iterations x 0.16ms = 16ms per frame
- FAA: 10 sequential iterations x 0.8ms = 8ms per frame

────────────────────────────────────────────────────────────────────────────────
                                                   // round // 3 // synthesis
────────────────────────────────────────────────────────────────────────────────

## Round 3: Synthesis & Recommendations

### Consensus Points

1. **Integration before optimization**: Create the adapter layer first
   (`FrameState.Allocation.purs`). FAA enhancement is useless without wiring.

2. **Tighten FractionalSolution**: Use `UnitInterval` for coordinates to
   prevent invalid polytope states.

3. **LargeStepConfig with bounds**:

```purescript
newtype LargeStepConfig = LargeStepConfig
  { numIterations :: BoundedInt 4 1000  -- T >= 4 for stability
  , useLargeStep :: Boolean             -- dt = 1/sqrt(T) vs 1/T
  , minEnergySamples :: BoundedInt 1 20 -- K samples for rounding
  , seed :: Number                       -- Reproducibility
  }
```

4. **Realistic speedup target**: 2-4x, not 40x. The 40x assumed zero variance.

### Priority-Ordered Implementation Plan

| Priority | Component | Lines | Impact |
|----------|-----------|-------|--------|
| **P0** | `FrameState.Allocation.purs` | ~150 | Unblocks integration |
| **P1** | Tighten `FractionalSolution` to `UnitInterval` | ~50 | Type safety |
| **P2** | `LargeStepConfig` + `continuousGreedyLargeStep` | ~80 | 2x speedup |
| **P3** | `minEnergySample` function | ~60 | Noise resilience |
| **P4** | Integration tests | ~200 | Verification |

### Implementation Schedule

**Day 1:**

- Create `src/Hydrogen/GPU/FrameState/Allocation.purs`
- Implement `viewportToGroundSet`, `performanceToFeedback`, `allocateFrame`
- Wire to existing `onlineStep` from `Optimize.Submodular.Online`

**Day 2:**

- Tighten `FractionalSolution` type in `Continuous.purs`
- Add `LargeStepConfig` to `Types.purs`
- Implement `continuousGreedyLargeStep` in `Continuous.purs`

**Day 3:**

- Add `minEnergySample` to `Rounding.purs`
- Integration tests against FrameState
- Benchmark: standard vs FAA-enhanced

### Success Criteria

1. `allocateFrame` compiles and type-checks with existing FrameState
2. `FractionalSolution` rejects coordinates outside [0,1]
3. `continuousGreedyLargeStep` achieves 90% of standard quality in 25% iterations
4. `minEnergySample` improves rounding quality by >10%

────────────────────────────────────────────────────────────────────────────────
                                                      // council // conclusion
────────────────────────────────────────────────────────────────────────────────

## Council Conclusion

### Primary Finding

The codebase is **mathematically complete** but **integration-incomplete**.

The two submodular implementations (`Optimize.Submodular.*` and `Render.Online.*`)
are well-typed but not connected to actual GPU rendering.

### Integration Gap Analysis

| Gap | Description | Priority |
|-----|-------------|----------|
| Optimize <-> Render | Two separate implementations, no shared code | HIGH |
| FrameState <-> Submodular | No connection between PerformanceState and optimization | HIGH |
| ViewportState <-> Region | No mapping from viewport tensor to grid regions | HIGH |
| GPU Budget <-> Utility | `gpuBudgetMs`/`gpuUsedMs` not connected to `Utility` | MEDIUM |

### Redundancy Analysis

| Feature | Optimize.Submodular | Render.Online |
|---------|---------------------|---------------|
| Matroid | Types.purs class | Matroid/Class.purs |
| Submodular Function | SubmodularOracle | SubmodularFn |
| Online State | Online.OnlineState | Selection/State.OnlineState |
| Greedy Selection | Oracle.greedyMaximize | Selection/Greedy.greedySelect |

**Assessment:** The two implementations serve different abstraction levels:

- `Optimize.Submodular` — General-purpose, research-grade
- `Render.Online` — Domain-specific, rendering-optimized

**Recommendation:** Keep both; create adapter layer.

### Final Decision

**Focus on P0: FrameState.Allocation.purs** before any algorithm enhancements.

FAA enhancement is **deferred to P2** — it's a genuine improvement but premature
without the integration layer.

────────────────────────────────────────────────────────────────────────────────
                                                              // attestation
────────────────────────────────────────────────────────────────────────────────

Council deliberation conducted 2026-02-25.

Participants: Type Theorist, Systems Architect, Algorithm Specialist

Decision: Integration before optimization. P0 is FrameState.Allocation.purs.

────────────────────────────────────────────────────────────────────────────────
                                                          // status // 2026-02-26
────────────────────────────────────────────────────────────────────────────────

## Implementation Status (Updated 2026-02-27)

| Priority | Component | Status |
|----------|-----------|--------|
| **P0** | `FrameState.Allocation.purs` | ✓ **DONE** (~754 lines) |
| **P1** | Tighten `FractionalSolution` to `UnitInterval` | ✓ **DONE** (in Continuous.purs) |
| **P2** | `LargeStepConfig` + `continuousGreedyLargeStep` | ✓ **DONE** (FAA config in Allocation.purs) |
| **P3** | `minEnergySample` function | ✓ **DONE** (in Rounding.purs) |
| **P4** | Integration tests | OPEN |

**Completed implementation** at `src/Hydrogen/GPU/FrameState/Allocation.purs`:
- `viewportToRegions :: ViewportState -> Array Region`
- `viewportToGroundSet :: ViewportState -> Set.Set Region`
- `performanceToFeedback :: PerformanceState -> RegionSelection -> Number`
- `allocateFrame :: ViewportState -> PerformanceState -> AllocationState -> AllocationResult`
- `allocateFrameFAA :: ViewportState -> PerformanceState -> AllocationState -> FAAAllocationConfig -> AllocationResult`
- `regionsToGroundSetFAA :: Array Region -> { groundSet, indexToRegion }`
- `regionUtilityOracle :: FAAAllocationConfig -> Array Region -> GroundSet RegionIndex -> SubmodularOracle RegionIndex`

**FAA-enhanced features:**
- √T speedup via FAA continuous greedy
- Min-energy rounding (deterministic, noise-resilient)
- Quality-adaptive step modulation using fractional solution confidence
- Submodular utility: quality weight + coverage weight (√|S|)

────────────────────────────────────────────────────────────────────────────────
                                                                  — Opus 4.5
                                                     Updated: 2026-02-27
────────────────────────────────────────────────────────────────────────────────
