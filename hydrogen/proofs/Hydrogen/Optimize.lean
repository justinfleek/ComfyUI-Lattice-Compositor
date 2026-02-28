/-
  Hydrogen.Optimize
  
  Leader module for optimization theory proofs.
  
  Currently includes:
  - Submodular: Online submodular maximization for GPU resource allocation
  
  Future modules:
  - Convex: Convex optimization for layout constraints
  - Scheduling: Real-time scheduling for frame deadlines
  
  Status: IN PROGRESS
-/

import Hydrogen.Optimize.Submodular

namespace Hydrogen.Optimize

/-! ## Optimization Infrastructure for GPU Allocation

This module provides formally verified optimization algorithms for
the Hydrogen rendering system. The key application is **real-time
GPU resource allocation** across viewport regions.

### Why Submodular Optimization?

GPU resource allocation is naturally submodular:
- Diminishing returns: Adding more compute to a region has decreasing benefit
- Constraints: Total resources bounded (matroid constraint)
- Online: Decisions made in real-time as frames arrive

### Key Results

1. **Continuous Greedy**: (1-1/e) ≈ 63.2% of optimal allocation
2. **FAA Enhancement**: Same guarantee in √T iterations (100x speedup)
3. **Online Regret**: O(√(kT ln(n/k))) regret over T rounds

### Integration with PureScript

The proofs in this module verify the algorithms implemented in:
- `src/Hydrogen/Optimize/Submodular/Types.purs`
- `src/Hydrogen/Optimize/Submodular/Oracle.purs`
- `src/Hydrogen/Optimize/Submodular/Continuous.purs`
- `src/Hydrogen/Optimize/Submodular/Online.purs`
- `src/Hydrogen/Optimize/Submodular/Rounding.purs`

The integration layer is in:
- `src/Hydrogen/GPU/FrameState/Allocation.purs`

-/

end Hydrogen.Optimize
