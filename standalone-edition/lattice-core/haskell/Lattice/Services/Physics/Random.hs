{-|
Module      : Lattice.Services.Physics.Random
Description : Seeded Random Number Generator for Physics Simulation
Copyright   : (c) Lattice Team, 2026
License     : MIT

Deterministic random number generator using Mulberry32 algorithm:
- Seeded initialization for reproducibility
- Uniform random values in [0, 1)
- Range-constrained values
- Gaussian distribution via Box-Muller

All functions are total and deterministic given the same seed.

Source: ui/src/services/physics/PhysicsEngine.ts (PhysicsRandom class)
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Physics.Random
  ( -- * Types
    PhysicsRandom(..)
  , RngState
    -- * Construction
  , mkPhysicsRandom
  , reset
    -- * Generation
  , next
  , nextRange
  , nextGaussian
    -- * Batch Operations
  , nextN
  , nextRangeN
  ) where

import Data.Word (Word32)
import Data.Bits (xor, shiftR, (.|.))

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Internal RNG state (32-bit)
type RngState = Word32

-- | Physics random number generator state
data PhysicsRandom = PhysicsRandom
  { prState :: RngState      -- ^ Current state
  , prInitialSeed :: RngState -- ^ Initial seed for reset
  } deriving (Show, Eq)

-- ────────────────────────────────────────────────────────────────────────────
-- Construction
-- ────────────────────────────────────────────────────────────────────────────

-- | Create a new RNG with the given seed
mkPhysicsRandom :: Word32 -> PhysicsRandom
mkPhysicsRandom seed = PhysicsRandom
  { prState = seed
  , prInitialSeed = seed
  }

-- | Reset RNG to initial seed
reset :: PhysicsRandom -> PhysicsRandom
reset rng = rng { prState = prInitialSeed rng }

-- ────────────────────────────────────────────────────────────────────────────
-- Generation
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate next random value in [0, 1) using Mulberry32 algorithm.
-- Returns new state and value.
next :: PhysicsRandom -> (Double, PhysicsRandom)
next rng =
  let
    -- Mulberry32 algorithm
    state0 = prState rng + 0x6D2B79F5
    t1 = state0 `xor` (state0 `shiftR` 15)
    t2 = t1 * (t1 .|. 1)  -- imul approximation
    t3 = t2 `xor` (t2 + (t2 `xor` (t2 `shiftR` 7)) * (t2 .|. 61))
    result = t3 `xor` (t3 `shiftR` 14)
    value = fromIntegral result / 4294967296.0
    newRng = rng { prState = state0 }
  in (value, newRng)

-- | Generate random value in [min, max)
nextRange :: Double -> Double -> PhysicsRandom -> (Double, PhysicsRandom)
nextRange minVal maxVal rng =
  let (val, newRng) = next rng
      scaled = minVal + val * (maxVal - minVal)
  in (scaled, newRng)

-- | Generate Gaussian-distributed value using Box-Muller transform
nextGaussian :: PhysicsRandom -> (Double, PhysicsRandom)
nextGaussian rng =
  let
    (u1, rng1) = next rng
    (u2, rng2) = next rng1
    -- Avoid log(0) by ensuring u1 > 0
    safeU1 = max 0.000001 u1
    gaussian = sqrt (-2 * log safeU1) * cos (2 * pi * u2)
  in (gaussian, rng2)

-- ────────────────────────────────────────────────────────────────────────────
-- Batch Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate N random values
nextN :: Int -> PhysicsRandom -> ([Double], PhysicsRandom)
nextN n rng = go n rng []
  where
    go 0 r acc = (reverse acc, r)
    go k r acc =
      let (v, r') = next r
      in go (k - 1) r' (v : acc)

-- | Generate N random values in range
nextRangeN :: Int -> Double -> Double -> PhysicsRandom -> ([Double], PhysicsRandom)
nextRangeN n minVal maxVal rng = go n rng []
  where
    go 0 r acc = (reverse acc, r)
    go k r acc =
      let (v, r') = nextRange minVal maxVal r
      in go (k - 1) r' (v : acc)
