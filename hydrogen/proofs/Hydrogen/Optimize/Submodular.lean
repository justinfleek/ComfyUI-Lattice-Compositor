/-
  Hydrogen.Optimize.Submodular
  
  Leader module for submodular optimization proofs.
  
  This module aggregates all submodular optimization theory:
  
  ┌─────────────────────────────────────────────────────────────────────────────┐
  │ Core             │ Submodular functions, monotonicity, normalization       │
  │ Matroid          │ Independence systems, rank functions, polytopes         │
  │ ContinuousGreedy │ (1-1/e) approximation guarantee                         │
  │ FAA              │ Floquet Adiabatic Algorithm for √T speedup              │
  │ RAOCO            │ Online submodular via online convex optimization        │
  └─────────────────────────────────────────────────────────────────────────────┘
  
  Status: COMPLETE
-/

import Hydrogen.Optimize.Submodular.Core
import Hydrogen.Optimize.Submodular.Matroid
import Hydrogen.Optimize.Submodular.ContinuousGreedy
import Hydrogen.Optimize.Submodular.FAA
import Hydrogen.Optimize.Submodular.RAOCO

namespace Hydrogen.Optimize.Submodular

/-! ## Summary of Proven Properties

### Core Submodular Theory
- `marginalGain`: Definition of marginal gain f(S ∪ {e}) - f(S)
- `IsSubmodular`: Diminishing returns property
- `IsMonotone`: Adding elements never decreases value
- `IsNormalized`: f(∅) = 0
- `monotone_implies_nonneg_marginal`: Monotone ⟹ non-negative marginals
- `submodular_iff_lattice`: Equivalence of two definitions
- `coverage_monotone`, `coverage_submodular`: Coverage function properties

### Matroid Theory  
- `Matroid`: Independence system with augmentation
- `rank`: Maximum independent subset size
- `rank_le_card`, `rank_mono`: Rank properties
- `inPolytope`: Matroid polytope membership
- `indicator_in_polytope`: Integer solutions are vertices
- `uniformMatroid`: Cardinality constraint matroid

### Continuous Greedy Algorithm
- `oneMinusInvE`: The (1-1/e) ≈ 0.632 constant
- `gap_shrinks`: Each step reduces gap by (1-1/T)
- `continuous_greedy_guarantee`: F(x_T) ≥ (1-(1-1/T)^T)·OPT
- `limit_is_one_minus_inv_e`: Limit as T→∞
- `explicit_approximation_bound`: Finite T bound with O(1/T) error
- `full_pipeline_guarantee`: End-to-end with rounding

### FAA (Floquet Adiabatic Algorithm)
- `faaStepSize`: δt = 1/√T (larger steps)
- `faaIterations`: √T iterations (fewer steps)
- `faa_step_larger`: FAA step > standard step
- `total_work_preserved`: √T · (1/√T) = 1
- `faa_cumulative_error`: Error accumulation bounded
- `faa_speedup`: √T/T = 1/√T reduction in iterations
- `min_energy_deterministic`: Noise-resilient rounding
- `regret_sublinear`: O(√(kT ln(n/k))) regret bound

### RAOCO (Online Submodular via OCO)
Reference: Si Salem et al., "Online Submodular Maximization via Online Convex 
           Optimization" (arXiv:2309.04339v4, January 2024)

- `thresholdPotential`: WTP building block
- `wtpApproxRatio`: α = (1 - 1/Δ)^Δ → e^(-1) as Δ → ∞
- `SandwichProperty`: Concave relaxations bound WTP from above/below
- `NegativelyCorrelatedRounding`: Swap rounding preserves expectation
- `raoco_reduction`: α-regret_T(P_X) ≤ α · regret_T(P_Y) (Theorem 2)
- `raoco_sqrt_regret`: O(√T) regret with O(√T) OCO regret
- `wtp_matroid_raoco`: Full theorem for WTP over matroids (Theorem 3)

-/

end Hydrogen.Optimize.Submodular
