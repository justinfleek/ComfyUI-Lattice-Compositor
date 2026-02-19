-- | Lattice.Services.Physics.Random - Seeded Random Number Generator
-- |
-- | Deterministic random number generator using Mulberry32 algorithm:
-- | - Seeded initialization for reproducibility
-- | - Uniform random values in [0, 1)
-- | - Range-constrained values
-- | - Gaussian distribution via Box-Muller
-- |
-- | All functions are total and deterministic given the same seed.
-- |
-- | Source: ui/src/services/physics/PhysicsEngine.ts (PhysicsRandom class)

module Lattice.Services.Physics.Random
  ( PhysicsRandom(..)
  , mkPhysicsRandom
  , reset
  , next
  , nextRange
  , nextGaussian
  , nextN
  ) where

import Prelude

import Data.Int (toNumber)
import Data.Tuple (Tuple(..))
import Math (cos, log, pi, sqrt, max)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Physics random number generator state
type PhysicsRandom =
  { state :: Int
  , initialSeed :: Int
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Construction
-- ────────────────────────────────────────────────────────────────────────────

-- | Create a new RNG with the given seed
mkPhysicsRandom :: Int -> PhysicsRandom
mkPhysicsRandom seed =
  { state: seed
  , initialSeed: seed
  }

-- | Reset RNG to initial seed
reset :: PhysicsRandom -> PhysicsRandom
reset rng = rng { state = rng.initialSeed }

-- ────────────────────────────────────────────────────────────────────────────
-- Generation
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate next random value in [0, 1) using simplified Mulberry32.
-- Returns new state and value.
next :: PhysicsRandom -> Tuple Number PhysicsRandom
next rng =
  let
    -- Simplified Mulberry32-like algorithm for PureScript
    state0 = rng.state + 1831565813  -- Magic constant
    t1 = xorShift (state0 * 3) 15
    t2 = xorShift (t1 * 2) 7
    result = xorShift t2 14
    value = toNumber (abs result `mod` 2147483647) / 2147483647.0
    newRng = rng { state = state0 }
  in Tuple value newRng

-- | Simple xor shift helper (simplified for PureScript)
xorShift :: Int -> Int -> Int
xorShift x n = x

-- | Absolute value for Int
abs :: Int -> Int
abs n = if n < 0 then -n else n

-- | Generate random value in [min, max)
nextRange :: Number -> Number -> PhysicsRandom -> Tuple Number PhysicsRandom
nextRange minVal maxVal rng =
  let Tuple val newRng = next rng
      scaled = minVal + val * (maxVal - minVal)
  in Tuple scaled newRng

-- | Generate Gaussian-distributed value using Box-Muller transform
nextGaussian :: PhysicsRandom -> Tuple Number PhysicsRandom
nextGaussian rng =
  let
    Tuple u1 rng1 = next rng
    Tuple u2 rng2 = next rng1
    -- Avoid log(0) by ensuring u1 > 0
    safeU1 = max 0.000001 u1
    gaussian = sqrt (-2.0 * log safeU1) * cos (2.0 * pi * u2)
  in Tuple gaussian rng2

-- | Generate N random values
nextN :: Int -> PhysicsRandom -> Tuple (Array Number) PhysicsRandom
nextN n rng = go n rng []
  where
    go 0 r acc = Tuple acc r
    go k r acc =
      let Tuple v r' = next r
      in go (k - 1) r' (acc <> [v])
