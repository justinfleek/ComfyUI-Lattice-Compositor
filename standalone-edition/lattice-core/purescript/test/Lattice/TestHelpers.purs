-- | Shared test helpers for Lattice PureScript test suite
-- |
-- | Provides:
-- |   - Floating-point comparison with tolerance
-- |   - QuickCheck generators for bounded numbers, vectors
-- |   - Common assertion patterns

module Test.Lattice.TestHelpers
  ( assertCloseTo
  , assertInRange
  , assertFinite
  , genBoundedNumber
  , genNormalized
  , genPositiveNumber
  , genAngle
  , genVec3
  , epsilon
  ) where

import Prelude

import Data.Number as Number
import Data.Number (abs) as Math
import Effect.Aff (Aff)
import Test.Spec.Assertions (fail)
import Test.QuickCheck.Gen (Gen, choose)
import Lattice.Services.Math3D.Vec3 (Vec3, vec3)

-- | Default tolerance for floating-point comparison
epsilon :: Number
epsilon = 1.0e-6

-- | Assert two numbers are within tolerance of each other
assertCloseTo :: Number -> Number -> Number -> Aff Unit
assertCloseTo tolerance expected actual =
  if Math.abs (actual - expected) <= tolerance
    then pure unit
    else fail
      ( "Expected " <> show actual
      <> " to be close to " <> show expected
      <> " (tolerance: " <> show tolerance <> ")"
      <> ", diff: " <> show (Math.abs (actual - expected))
      )

-- | Assert value is in range [min, max]
assertInRange :: Number -> Number -> Number -> Aff Unit
assertInRange lo hi actual =
  if actual >= lo && actual <= hi
    then pure unit
    else fail
      ( "Expected " <> show actual
      <> " to be in range [" <> show lo <> ", " <> show hi <> "]"
      )

-- | Assert value is finite (not NaN, not Infinity)
assertFinite :: Number -> Aff Unit
assertFinite n =
  if Number.isFinite n
    then pure unit
    else fail ("Expected finite number, got: " <> show n)

-- | Generate a number in [min, max] (no NaN, no Infinity)
genBoundedNumber :: Number -> Number -> Gen Number
genBoundedNumber lo hi = choose lo hi

-- | Generate a number in [0, 1]
genNormalized :: Gen Number
genNormalized = choose 0.0 1.0

-- | Generate a positive number in [0.001, 1000]
genPositiveNumber :: Gen Number
genPositiveNumber = choose 0.001 1000.0

-- | Generate an angle in [-2pi, 2pi]
genAngle :: Gen Number
genAngle = choose (-6.283185307) 6.283185307

-- | Generate a Vec3 with components in [-1000, 1000]
genVec3 :: Gen Vec3
genVec3 = do
  x <- choose (-1000.0) 1000.0
  y <- choose (-1000.0) 1000.0
  z <- choose (-1000.0) 1000.0
  pure (vec3 x y z)
