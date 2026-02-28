/-
  Hydrogen.Schema.Numeric
  
  Leader module for graded numeric types with error tracking.
  
  Based on NumFuzz/Bean (Kellison, 2025):
    - GradedMonad: Forward error tracking M[ε]
    - RelativePrecision: RP metric for error measurement  
    - NeighborhoodMonad: T^r construction for semantic model
  
  Status: FOUNDATIONAL
-/

import Hydrogen.Schema.Numeric.GradedMonad
import Hydrogen.Schema.Numeric.RelativePrecision
import Hydrogen.Schema.Numeric.NeighborhoodMonad
