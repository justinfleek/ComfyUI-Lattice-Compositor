-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // schema // numeric
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hydrogen.Schema.Numeric — Graded types for error tracking.
-- |
-- | ## Overview
-- |
-- | This module provides the foundational types for tracking numerical
-- | errors through computation. Based on NumFuzz (Kellison, 2025) graded
-- | monads and Bean backward error comonads.
-- |
-- | ## Core Insight
-- |
-- | Programs using finite-precision arithmetic are PRODUCERS of rounding error.
-- | The graded monad M[ε] tracks the maximum error bound ε as a type-level grade.
-- |
-- | ## Sub-modules
-- |
-- | - `Grade` — Non-negative error bounds with monoid structure
-- | - `ForwardError` — Graded monad for forward error tracking
-- |
-- | ## Lean Proofs
-- |
-- | All operations are proven correct in:
-- |   proofs/Hydrogen/Schema/Numeric/GradedMonad.lean
-- |   proofs/Hydrogen/Schema/Numeric/RelativePrecision.lean
-- |   proofs/Hydrogen/Schema/Numeric/NeighborhoodMonad.lean
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Numeric as N
-- |
-- | -- Create exact values
-- | x = N.exact 42.0
-- |
-- | -- Operations accumulate error
-- | y = N.exact 3.14
-- | z = N.addReal x y  -- bound = 0 + 0 = 0 (both exact)
-- |
-- | -- With approximations
-- | approxPi = N.fromApprox 3.14159265 3.14 N.machineEpsilon
-- | result = N.addReal x approxPi  -- bound = 0 + machineEpsilon
-- | ```

module Hydrogen.Schema.Numeric
  ( -- * Re-exports from Grade
    module Hydrogen.Schema.Numeric.Grade
    -- * Re-exports from ForwardError
  , module Hydrogen.Schema.Numeric.ForwardError
    -- * Re-exports from Sensitivity
  , module Hydrogen.Schema.Numeric.Sensitivity
    -- * Re-exports from Primitives
  , module Hydrogen.Schema.Numeric.Primitives
  ) where

import Hydrogen.Schema.Numeric.Grade
  ( Grade
  , unGrade
  , grade
  , zero
  , machineEpsilon
  , olverEpsilon
  , add
  , mul
  , max
  , isZero
  , isExact
  )

import Hydrogen.Schema.Numeric.ForwardError
  ( ForwardError
  , exact
  , fromApprox
  , fromApproxUnsafe
  , ideal
  , approx
  , bound
  , value
  , weaken
  , strengthen
  , addReal
  , negReal
  , subReal
  , scaleReal
  , mulReal
  , mapWithGrade
  , errorMagnitude
  )

import Hydrogen.Schema.Numeric.Sensitivity
  ( Sensitive
  , sensitive
  , identity
  , compose
  , applySensitive
  , scale
  , negate
  , constant
  , getSensitivity
  , isContraction
  , isExpansion
  , isIsometry
  )

import Hydrogen.Schema.Numeric.Primitives
  ( liftNumber
  , divReal
  )
