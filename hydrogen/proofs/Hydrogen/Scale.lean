/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                          HYDROGEN // SCALE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Proven invariants for billion-agent scale coordination.
  
  This module contains proofs that Hydrogen's architecture scales to 10^9 agents
  while maintaining:
  
  1. O(n log n) communication complexity (not O(n²))
  2. O(log n) coordination latency
  3. 60fps rendering independent of coordination latency
  4. Convergent state under network partitions
  
  SUBMODULES:
  
  - HierarchicalAggregation: Tree-based aggregation proofs

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Scale.HierarchicalAggregation
