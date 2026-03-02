{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Services.Particles.SeededRandom
Description : Seeded Random Number Generator
Copyright   : (c) Lattice, 2026
License     : MIT

Uses mulberry32 algorithm for deterministic, reproducible randomness.
This is CRITICAL for particle system determinism - same seed always
produces the same sequence of numbers.

Source: ui/src/services/particles/SeededRandom.ts
-}

module Lattice.Services.Particles.SeededRandom
  ( -- * Types
    RngState(..)
  , Point2D(..)
  , Point3D(..)
    -- * Core Operations
  , create, reset, setSeed
  , getState, setState, getSeed
    -- * Random Generation
  , next, nextN
    -- * Range Operations
  , range, int, variance, bool
    -- * Angular Operations
  , angle
    -- * Geometric Distributions
  , inCircle, onSphere
    -- * Statistical Distributions
  , gaussian
  ) where

import GHC.Generics (Generic)
import Data.Word (Word32)
import Data.Bits (xor, (.|.), shiftR)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Random generator state
data RngState = RngState
  { rngState :: Word32
  , rngInitialSeed :: Word32
  } deriving stock (Eq, Show, Generic)

-- | 2D point
data Point2D = Point2D
  { p2x :: Double
  , p2y :: Double
  } deriving stock (Eq, Show, Generic)

-- | 3D point
data Point3D = Point3D
  { p3x :: Double
  , p3y :: Double
  , p3z :: Double
  } deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

-- | Mulberry32 magic constant
mulberry32Magic :: Word32
mulberry32Magic = 0x6D2B79F5

-- ────────────────────────────────────────────────────────────────────────────
-- Core Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Create new RNG with seed
create :: Word32 -> RngState
create seed = RngState seed seed

-- | Reset to initial seed
reset :: RngState -> RngState
reset rng = rng { rngState = rngInitialSeed rng }

-- | Set new seed
setSeed :: Word32 -> RngState -> RngState
setSeed seed _ = RngState seed seed

-- | Get current state for checkpointing
getState :: RngState -> Word32
getState = rngState

-- | Restore state from checkpoint
setState :: Word32 -> RngState -> RngState
setState s rng = rng { rngState = s }

-- | Get initial seed
getSeed :: RngState -> Word32
getSeed = rngInitialSeed

-- ────────────────────────────────────────────────────────────────────────────
-- Mulberry32 Algorithm
-- ────────────────────────────────────────────────────────────────────────────

-- | Integer multiply with 32-bit semantics (simulated)
imul :: Word32 -> Word32 -> Word32
imul a b = a * b

-- | Get next random number in [0, 1)
--   Returns (value, newState)
next :: RngState -> (Double, RngState)
next rng =
  let newState = rngState rng + mulberry32Magic
      t1 = newState `xor` (newState `shiftR` 15)
      t2 = imul t1 (t1 .|. 1)
      t3 = t2 `xor` (t2 + imul (t2 `xor` (t2 `shiftR` 7)) (t2 .|. 61))
      t4 = t3 `xor` (t3 `shiftR` 14)
      value = fromIntegral t4 / 4294967296.0
  in (value, rng { rngState = newState })

-- | Generate n random numbers in [0, 1)
nextN :: Int -> RngState -> ([Double], RngState)
nextN n rng = go n [] rng
  where
    go 0 acc r = (reverse acc, r)
    go k acc r =
      let (v, r') = next r
      in go (k - 1) (v : acc) r'

-- ────────────────────────────────────────────────────────────────────────────
-- Range Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Get random in range [min, max]
range :: Double -> Double -> RngState -> (Double, RngState)
range minV maxV rng =
  let (r, rng') = next rng
  in (minV + r * (maxV - minV), rng')

-- | Get random integer in range [min, max] inclusive
int :: Int -> Int -> RngState -> (Int, RngState)
int minV maxV rng =
  let (r, rng') = range (fromIntegral minV) (fromIntegral maxV + 1) rng
  in (floor r, rng')

-- | Get random value with variance: base + random(-variance, +variance)
variance :: Double -> Double -> RngState -> (Double, RngState)
variance base var rng =
  let (r, rng') = next rng
  in (base + (r - 0.5) * 2 * var, rng')

-- | Get random boolean with given probability of true
bool :: Double -> RngState -> (Bool, RngState)
bool probability rng =
  let (r, rng') = next rng
  in (r < probability, rng')

-- ────────────────────────────────────────────────────────────────────────────
-- Angular Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Get random angle in radians [0, 2*PI)
angle :: RngState -> (Double, RngState)
angle rng =
  let (r, rng') = next rng
  in (r * pi * 2, rng')

-- ────────────────────────────────────────────────────────────────────────────
-- Geometric Distributions
-- ────────────────────────────────────────────────────────────────────────────

-- | Get random point in unit circle
inCircle :: RngState -> (Point2D, RngState)
inCircle rng =
  let (a, rng1) = angle rng
      (r, rng2) = next rng1
      radius = sqrt r
  in (Point2D (radius * cos a) (radius * sin a), rng2)

-- | Get random point on unit sphere
onSphere :: RngState -> (Point3D, RngState)
onSphere rng =
  let (theta, rng1) = angle rng
      (u, rng2) = next rng1
      phi = acos (2 * u - 1)
      sinPhi = sin phi
  in (Point3D (sinPhi * cos theta) (sinPhi * sin theta) (cos phi), rng2)

-- ────────────────────────────────────────────────────────────────────────────
-- Statistical Distributions
-- ────────────────────────────────────────────────────────────────────────────

-- | Get random number from Gaussian/normal distribution
--   Uses Box-Muller transform
gaussian :: Double -> Double -> RngState -> (Double, RngState)
gaussian mean stdDev rng =
  let stdDev' = if stdDev == 0 then 1 else stdDev
      (u1, rng1) = next rng
      (u2, rng2) = next rng1
      -- Prevent log(0)
      u1' = if u1 == 0 then 1e-10 else u1
      -- Box-Muller transform
      z = sqrt (-2 * log u1') * cos (2 * pi * u2)
  in (mean + z * stdDev', rng2)
