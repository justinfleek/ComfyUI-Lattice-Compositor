━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                         // online // submodular // implementation
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

   "At billion-agent scale, each decision must be deterministic,
    each type must be bounded, and each composition must be lawful."

                                                        — Council Synthesis

# Online Submodular Maximization for Hydrogen

## Overview

This document specifies the implementation of Harvey/Liaw/Soma's online 
submodular maximization algorithm (NeurIPS 2020) for Hydrogen's tensor-native 
rendering system. The algorithm enables GPU resource allocation across viewport 
regions with provable regret bounds.

**Key Result**: O(√(kT ln(n/k))) first-order regret for monotone + matroid

Where:
- k = rank of matroid (max regions selected)
- T = time horizon (frames rendered)
- n = ground set size (total region × quality pairs)

────────────────────────────────────────────────────────────────────────────────
                                                              // why this matters
────────────────────────────────────────────────────────────────────────────────

## The Viewport Allocation Problem

At billion-agent swarm scale, each agent must decide:

1. **Which regions** of the viewport to render at high quality
2. **What quality level** (diffusion steps) to allocate per region  
3. **How to adapt** as user attention shifts frame-to-frame

Submodular optimization provides the mathematical framework:

- **Diminishing returns**: The 10th high-quality region adds less value than the 1st
- **Coverage semantics**: Selecting regions "covers" user attention/tasks
- **Provable guarantees**: (1 - 1/e) ≈ 63.2% of optimal offline solution

## Why Submodular?

Consider viewport regions R₁, R₂, ..., Rₙ with user attention weights w₁, w₂, ..., wₙ.

If we select regions S to render at high quality:

```
f(S) = Σᵢ wᵢ · 𝟙[region i is covered by some r ∈ S]
```

This is the **weighted coverage function** — a canonical monotone submodular function.

**Submodularity**: Adding region rⱼ to a smaller set S gives ≥ marginal gain than 
adding it to a larger set T ⊇ S. Diminishing returns.

**Monotonicity**: f(S) ≤ f(T) when S ⊆ T. More coverage never hurts.

────────────────────────────────────────────────────────────────────────────────
                                                          // architecture summary
────────────────────────────────────────────────────────────────────────────────

## Module Structure

```
src/Hydrogen/Optimize/Submodular/
├── Types.purs          ← Core type system (817 lines)
│   ├── Element, ElementSet, GroundSet
│   ├── SubmodularOracle, SubmodularFn (phantom typed)
│   ├── Matroid typeclass + instances (Cardinality, Partition, Uniform)
│   ├── OnlineGrade (graded monad for co-effects)
│   └── ApproxRatio (compile-time approximation tracking)
│
├── Oracle.purs         ← Submodular function constructors (652 lines)
│   ├── mkCoverageOracle        — Set cover
│   ├── mkWeightedCoverageOracle — Weighted coverage
│   ├── mkFacilityLocationOracle — Facility location
│   ├── mkSaturatingQualityOracle — q(s) = qₘₐₓ(1 - e^{-αs})
│   ├── greedyMaximize          — (1-1/e) greedy
│   └── lazyGreedyMaximize      — Lazy greedy with priority queue
│
└── Continuous.purs     ← Continuous relaxation (711 lines)
    ├── FractionalSolution      — x ∈ [0,1]ⁿ sparse representation
    ├── MultilinearExt          — F(x) = 𝔼[f(S)] multilinear extension
    ├── MatroidPolytope         — P(M) = conv{1_I : I independent}
    ├── continuousGreedy        — Frank-Wolfe algorithm
    ├── GradientEstimate        — Two-point gradient estimation
    └── dependentRound          — Matroid-respecting rounding
```

## NOT YET IMPLEMENTED

The following modules are specified but not yet created:

```
├── Online.purs         ← Harvey/Liaw/Soma online algorithm
│   ├── OnlineContinuousGreedy  — Main algorithm
│   ├── BlackwellOracle         — Blackwell approachability
│   └── RegretTracker           — O(√(kT ln(n/k))) verification
│
├── Rounding.purs       ← Full pipage rounding
│   ├── pipageRound             — Lossless fractional → integral
│   ├── contiguousRound         — For matroid constraints
│   └── swapRound               — Swap-based rounding
│
└── Submodular.purs     ← Leader module (re-exports)
```

────────────────────────────────────────────────────────────────────────────────
                                                                  // type system
────────────────────────────────────────────────────────────────────────────────

## Core Types

### Element and Ground Set

```purescript
-- | An element in ground set V, indexed 0 to n-1
-- | Phantom type 'v' ties element to its ground set
newtype Element :: Type -> Type
newtype Element v = Element Int

-- | Ground set V with bounded cardinality
newtype GroundSet :: Type -> Type
newtype GroundSet v = GroundSet
  { size :: Dim                    -- Bounded [1, 2^30]
  , elements :: Array (Element v)
  }
```

### Submodular Function (Phantom Typed)

```purescript
-- | Monotonicity classification
data Monotonicity = Monotone | NonMonotone

-- | Curvature κ ∈ [0, 1] — how far from modular
data Curvature
  = CurvatureUnknown              -- κ = 1 assumed
  | CurvatureBounded Number       -- κ ≤ bound
  | CurvatureExact Number         -- κ = exact

-- | Submodular function with phantom type guarantees
-- | - v: ground set type
-- | - m: monotonicity (Monotone or NonMonotone)
-- | - κ: curvature bound
type SubmodularFn v (m :: Monotonicity) (κ :: Curvature) = SubmodularOracle v

-- | Oracle interface (what agents actually call)
newtype SubmodularOracle v = SubmodularOracle
  { eval :: ElementSet v -> SetValue
  , marginal :: Element v -> ElementSet v -> MarginalGain
  , groundSet :: GroundSet v
  , fMax :: Maybe SetValue
  }
```

### Matroid Typeclass

```purescript
-- | Matroid (V, I) with independence family I
class Matroid m v | m -> v where
  rank :: m -> ElementSet v -> MatroidRank
  maxRank :: m -> MatroidRank
  isIndependent :: m -> ElementSet v -> Boolean
  canExtend :: m -> Element v -> IndependentSet v -> Boolean
  extensionElements :: m -> IndependentSet v -> Array (Element v)

-- | Cardinality matroid: I = {S : |S| ≤ k}
newtype CardinalityMatroid v = CardinalityMatroid
  { k :: Dim
  , groundSet :: GroundSet v
  }

-- | Partition matroid: I = {S : |S ∩ Vᵢ| ≤ kᵢ for all blocks i}
newtype PartitionMatroid v = PartitionMatroid
  { blocks :: Array (PartitionBlock v)
  , groundSet :: GroundSet v
  }
```

### Graded Monad for Online Learning

```purescript
-- | Grade tracks resources consumed (co-effect)
data OnlineGrade = OnlineGrade
  { rounds :: Int                 -- Rounds elapsed
  , regret :: Number              -- Cumulative regret
  , queries :: Int                -- Oracle queries made
  }

-- | Grades compose additively
instance semigroupOnlineGrade :: Semigroup OnlineGrade where
  append (OnlineGrade a) (OnlineGrade b) = OnlineGrade
    { rounds: a.rounds + b.rounds
    , regret: a.regret + b.regret
    , queries: a.queries + b.queries
    }

-- | Graded computation
type OnlineLearn (g :: OnlineGrade) a = 
  { run :: a
  , grade :: OnlineGrade
  }
```

────────────────────────────────────────────────────────────────────────────────
                                                               // algorithm detail
────────────────────────────────────────────────────────────────────────────────

## Continuous Greedy (Frank-Wolfe)

The continuous greedy algorithm maximizes the multilinear extension F(x) over 
the matroid polytope P(M):

```
Algorithm: ContinuousGreedy
───────────────────────────────────────────────────────────────
Input: Submodular f, matroid M, iterations T
Output: Fractional solution x ∈ P(M) with F(x) ≥ (1-1/e)·OPT

x₀ ← 0⃗
for t = 0, 1, ..., T-1:
    ∇ ← estimate gradient of F at xₜ
    vₜ ← argmax_{v ∈ P(M)} ⟨∇, v⟩    // Linear max (greedy)
    xₜ₊₁ ← xₜ + (1/T) · vₜ
return xₜ
```

**Key insight**: Linear maximization over matroid polytope reduces to greedy 
selection on the discrete matroid. This makes each step O(n log n).

## Multilinear Extension

The multilinear extension F : [0,1]ⁿ → ℝ of f : 2^V → ℝ:

```
F(x) = 𝔼_{S ~ x}[f(S)] = Σ_{S ⊆ V} f(S) ∏_{e ∈ S} xₑ ∏_{e ∉ S} (1 - xₑ)
```

**Exact evaluation**: Exponential (2ⁿ terms) — only for |V| ≤ 15

**Sampled evaluation**: Polynomial — sample S ~ x, average f(S)

**Gradient**: ∂F/∂xₑ = 𝔼_{S ~ x₋ₑ}[f(S ∪ {e}) - f(S)] — expected marginal gain

## Gradient Estimation

Two-point estimation (variance reduction over single-point):

```
∂F/∂xₑ ≈ (F(x + δeₑ) - F(x - δeₑ)) / (2δ)
```

Coordinate-wise estimation (direct):

```
∂F/∂xₑ ≈ (1/m) Σⱼ [f(Sⱼ ∪ {e}) - f(Sⱼ)]   where Sⱼ ~ x₋ₑ
```

## Solution Rounding

**Independent rounding**: Include e with probability xₑ
- Simple but may violate matroid constraint

**Threshold rounding**: Include e iff xₑ ≥ τ  
- Deterministic but may violate constraint

**Dependent rounding** (pipage/swap): 
- Iteratively pairs fractional coordinates
- Rounds jointly while maintaining independence
- 𝔼[1ₑ] = xₑ exactly, result always independent

────────────────────────────────────────────────────────────────────────────────
                                                    // viewport region allocation
────────────────────────────────────────────────────────────────────────────────

## Mapping to Hydrogen Concepts

### Ground Set: Region × Quality Pairs

For a viewport with R regions and Q quality levels:

```purescript
-- Element = (regionId, qualityLevel)
-- n = R × Q (e.g., 64 regions × 6 quality levels = 384 elements)
```

### Matroid: Partition by Priority Tier

Viewport divided into priority tiers:

```purescript
-- Tier 0 (Foveal):     8 regions  at budget k₀ = 8
-- Tier 1 (Peripheral): 24 regions at budget k₁ = 12
-- Tier 2 (Background): 32 regions at budget k₂ = 4
--
-- Partition matroid: select ≤ kᵢ from each tier
```

### Quality Function: Saturating

```purescript
-- q(s) = qₘₐₓ · (1 - e^{-αs})
-- 
-- s = diffusion steps
-- qₘₐₓ = 1.0 (normalized)
-- α = 0.15 (saturation rate)
--
-- Properties:
--   q(0) = 0
--   q(∞) → qₘₐₓ
--   q'(s) > 0, q''(s) < 0 (concave)
```

### Coverage Function: Weighted by Attention

```purescript
-- f(S) = Σᵣ wᵣ · max_{(r,q) ∈ S} q(q)
--
-- wᵣ = attention weight for region r (from gaze tracking, saliency)
-- max takes best quality level selected for region r
```

────────────────────────────────────────────────────────────────────────────────
                                                        // online learning model
────────────────────────────────────────────────────────────────────────────────

## Per-Frame Loop

```
Frame t (16.67ms at 60fps):
═══════════════════════════════════════════════════════════════════════════════

│ CPU (2ms)                          │ GPU (12ms)              │ Sync (2ms)  │
├────────────────────────────────────┼─────────────────────────┼─────────────┤
│                                    │                         │             │
│ 1. Read f_{t-1} (prev utility)     │ 4. Dispatch kernels     │ 7. Fence    │
│ 2. Update gradient estimate        │    (selected regions)   │ 8. Read     │
│ 3. Frank-Wolfe step → select Sₜ    │ 5. Render frame         │    timestamps│
│                                    │ 6. Profile              │ 9. Compute  │
│                                    │                         │    f_t      │
└────────────────────────────────────┴─────────────────────────┴─────────────┘
                                                                       │
                                                                       ▼
                                                               Utility revealed
                                                               (adversary move)
```

## The Adversary IS Reality

We don't simulate an adversary. The adversary is the actual GPU execution:

- **f_t revealed by**: GPU timestamps, render quality metrics
- **User attention shifts**: Gaze tracking, mouse position, scroll
- **Scene dynamics**: Objects enter/exit regions, content changes

The algorithm must achieve low regret against the **best fixed policy in hindsight**.

## Regret Guarantee

For T frames with partition matroid of rank k over n elements:

```
𝔼[Regret_T] ≤ O(√(kT ln(n/k)))
```

This means:
- After T = 3600 frames (1 minute), average per-frame suboptimality → 0
- At T → ∞, algorithm converges to (1-1/e)-optimal policy

────────────────────────────────────────────────────────────────────────────────
                                                         // state and memory
────────────────────────────────────────────────────────────────────────────────

## Per-Agent State (~4.5 KB)

```purescript
type AgentState =
  { solution :: FractionalSolution      -- ~2 KB (sparse, ~500 elements)
  , gradients :: GradientEstimate       -- ~1.5 KB
  , regret :: RegretState               -- 40 bytes
  , params :: OnlineParams              -- 40 bytes
  , matroid :: PartitionMatroid         -- Reference only
  , rngSeed :: Int                      -- 8 bytes
  , framesSinceRounding :: Int          -- 4 bytes
  , lastIntegralSolution :: ElementSet  -- ~400 bytes
  }
```

**At billion-agent scale**:
- Per-machine (1000 agents): 4.5 MB — trivial
- Total distributed: 4.5 PB — across all machines

## UUID5 Identity

All elements have deterministic identity via UUID5:

```purescript
-- Namespace hierarchy:
-- hydrogen.continuity.dev
--   └── region (uuid5(hydrogen, "region"))
--         └── uuid5(region_ns, "x:y:width:height:layer")
--   └── selection (uuid5(hydrogen, "selection"))
--         └── uuid5(selection_ns, "frame:region1=quality1,...")
```

**Same inputs → Same UUIDs across all agents, all time**

────────────────────────────────────────────────────────────────────────────────
                                                         // lean4 proof structure
────────────────────────────────────────────────────────────────────────────────

## What We Prove (Tractable)

```lean
-- 1. Matroid axioms for CardinalityMatroid
theorem cardinality_matroid_axioms :
  ∀ k, CardinalityMatroid k satisfies Matroid.axioms

-- 2. Matroid axioms for PartitionMatroid  
theorem partition_matroid_axioms :
  ∀ blocks, PartitionMatroid blocks satisfies Matroid.axioms

-- 3. Coverage function is submodular
theorem coverage_submodular :
  ∀ neighborhoods weights, IsSubmodular (coverageFn neighborhoods weights)

-- 4. Coverage function is monotone
theorem coverage_monotone :
  ∀ neighborhoods weights, IsMonotone (coverageFn neighborhoods weights)

-- 5. Greedy achieves (1-1/e) for monotone + matroid
theorem greedy_approximation :
  ∀ f M, IsSubmodular f → IsMonotone f → Matroid M →
    f(greedy f M) ≥ (1 - 1/e) * f(OPT)
```

## What We Axiomatize (Research-Level)

```lean
-- Harvey/Liaw/Soma regret bound
-- Source: NeurIPS 2020, arXiv:2007.09231
-- Justification: Peer-reviewed, 20+ page proof
axiom harvey_liaw_soma_bound :
  ∀ params algorithm,
    algorithm.expected_regret ≤ O(√(k * T * ln(n/k)))
```

────────────────────────────────────────────────────────────────────────────────
                                                     // implementation checklist
────────────────────────────────────────────────────────────────────────────────

## Completed

- [x] `Types.purs` — Core type system with phantom types
- [x] `Oracle.purs` — Submodular oracle constructors
- [x] `Continuous.purs` — Continuous relaxation infrastructure
- [x] Matroid typeclass with three instances
- [x] Greedy and lazy greedy maximization
- [x] Multilinear extension evaluation (exact + sampled)
- [x] Frank-Wolfe continuous greedy
- [x] Gradient estimation (coordinate + stochastic)
- [x] Solution rounding (threshold + dependent)

## Remaining

- [ ] `Online.purs` — Full Harvey/Liaw/Soma algorithm
- [ ] `Rounding.purs` — Full pipage rounding
- [ ] `Submodular.purs` — Leader module
- [ ] Integration with `GPU.FrameState`
- [ ] Integration with `GPU.ComputeKernel`
- [ ] Lean4 proofs for matroid axioms
- [ ] Lean4 proofs for submodularity

────────────────────────────────────────────────────────────────────────────────
                                                                      // usage
────────────────────────────────────────────────────────────────────────────────

## Example: Viewport Region Allocation

```purescript
import Hydrogen.Optimize.Submodular.Types
import Hydrogen.Optimize.Submodular.Oracle
import Hydrogen.Optimize.Submodular.Continuous

-- Define regions and priority tiers
fovealRegions :: Array (Element ViewportV)
fovealRegions = map Element [0, 1, 2, 3, 4, 5, 6, 7]

peripheralRegions :: Array (Element ViewportV)
peripheralRegions = map Element (Array.range 8 31)

backgroundRegions :: Array (Element ViewportV)  
backgroundRegions = map Element (Array.range 32 63)

-- Create partition matroid
matroid :: PartitionMatroid ViewportV
matroid = PartitionMatroid
  { blocks:
    [ PartitionBlock { elements: Set.fromFoldable fovealRegions, limit: dim 8 }
    , PartitionBlock { elements: Set.fromFoldable peripheralRegions, limit: dim 12 }
    , PartitionBlock { elements: Set.fromFoldable backgroundRegions, limit: dim 4 }
    ]
  , groundSet: viewportGroundSet
  }

-- Create weighted coverage oracle
oracle :: SubmodularOracle ViewportV
oracle = mkWeightedCoverageOracle coverageSpec attentionWeights

-- Run continuous greedy
config :: ContinuousGreedyConfig
config = mkContinuousGreedyConfig 100  -- 100 iterations

fractionalSolution :: FractionalSolution ViewportV
fractionalSolution = continuousGreedy matroid oracle config

-- Round to discrete solution
selectedRegions :: ElementSet ViewportV
selectedRegions = dependentRound matroid fractionalSolution 42.0
```

────────────────────────────────────────────────────────────────────────────────
                                                                   // references
────────────────────────────────────────────────────────────────────────────────

## Primary

1. Harvey, Liaw, Soma. "Improved Algorithms for Online Submodular Maximization 
   via First-order Regret Bounds" NeurIPS 2020. arXiv:2007.09231

2. Vondrák. "Optimal Approximation for Submodular Welfare Problem in the 
   Value Oracle Model" STOC 2008

3. Calinescu, Chekuri, Pál, Vondrák. "Maximizing a Monotone Submodular Function
   Subject to a Matroid Constraint" SICOMP 2011

## Supporting

4. Nemhauser, Wolsey, Fisher. "Analysis of Approximations for Maximizing 
   Submodular Set Functions" Math. Programming 1978

5. Blackwell. "An Analog of the Minimax Theorem for Vector Payoffs" 
   Pacific J. Math. 1956

────────────────────────────────────────────────────────────────────────────────

                                                        — Council Synthesis
                                                           2026-02-25 // Opus 4.5
