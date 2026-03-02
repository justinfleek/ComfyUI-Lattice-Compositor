-- |
-- Module      : Lattice.Services.PhysicsRandom
-- Description : Deterministic random number generator for physics simulation
-- 
-- Migrated from ui/src/services/physics/PhysicsEngine.ts (PhysicsRandom class)
-- Uses Mulberry32 algorithm for deterministic, reproducible random sequences
-- Same algorithm as particle system for consistency
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Services.PhysicsRandom
  ( -- Random generation
    physicsRandomNext
  , physicsRandomRange
  , physicsRandomGaussian
  -- Seed management
  , PhysicsRandomState(..)
  , initialPhysicsRandomState
  ) where

import Data.Bits ((.&.), (.|.), shiftR, xor)
import Data.Word (Word32)
import Data.Int (Int32)
import Lattice.Utils.NumericSafety (isFinite)
import Lattice.Utils.NumericSafety (ensureFinite, safeSqrt, safeLog)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | State for deterministic random number generator
-- Uses Word32 for Mulberry32 algorithm compatibility
data PhysicsRandomState = PhysicsRandomState
  { randomState :: Word32
  , randomInitialSeed :: Word32
  }
  deriving (Eq, Show)

-- | Create initial random state from seed
initialPhysicsRandomState :: Word32 -> PhysicsRandomState
initialPhysicsRandomState seed = PhysicsRandomState seed seed

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // mulberry32 // algorithm
-- ════════════════════════════════════════════════════════════════════════════

-- | Mulberry32 hash function for deterministic random
-- Pure function: same inputs → same outputs
-- Matches JavaScript: let t = (state += 0x6d2b79f5); t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return (t ^ (t >>> 14)) >>> 0
mulberry32 :: Word32 -> Word32
mulberry32 state =
  let -- Mulberry32 constant
      mulberryConst = 0x6d2b79f5
      -- Update state: t = state + constant
      t1 = (state + mulberryConst) .&. 0xFFFFFFFF
      -- t = Math.imul(t ^ (t >>> 15), t | 1)
      -- Math.imul does 32-bit integer multiplication
      t2Xor = xor t1 (shiftR t1 15)
      t2Or = t1 .|. 1
      -- 32-bit multiplication: convert to Int32, multiply, convert back
      t2 = fromIntegral ((fromIntegral t2Xor :: Int32) * (fromIntegral t2Or :: Int32)) .&. 0xFFFFFFFF
      -- t ^= t + Math.imul(t ^ (t >>> 7), t | 61)
      t3Xor = xor t2 (shiftR t2 7)
      t3Or = t2 .|. 61
      t3Mul = fromIntegral ((fromIntegral t3Xor :: Int32) * (fromIntegral t3Or :: Int32)) .&. 0xFFFFFFFF
      t3 = xor t2 (t2 + t3Mul) .&. 0xFFFFFFFF
      -- return (t ^ (t >>> 14)) >>> 0
      result = xor t3 (shiftR t3 14) .&. 0xFFFFFFFF
  in result

-- | Generate next random number in range [0, 1)
-- Pure function: same inputs → same outputs
-- Returns: (random value, new state)
physicsRandomNext :: PhysicsRandomState -> (Double, PhysicsRandomState)
physicsRandomNext state =
  let newStateValue = mulberry32 (randomState state)
      -- Convert to Double in range [0, 1)
      -- JavaScript: ((t ^ (t >>> 14)) >>> 0) / 4294967296
      randomValue = fromIntegral newStateValue / 4294967296.0
      finiteValue = ensureFinite randomValue 0.0
      newState = state { randomState = newStateValue }
  in (finiteValue, newState)

-- | Generate random number in specified range [min, max)
-- Pure function: same inputs → same outputs
-- Returns: (random value, new state)
physicsRandomRange :: PhysicsRandomState -> Double -> Double -> (Double, PhysicsRandomState)
physicsRandomRange state minVal maxVal =
  let (random01, newState) = physicsRandomNext state
      finiteMin = ensureFinite minVal 0.0
      finiteMax = ensureFinite maxVal 1.0
      range = finiteMax - finiteMin
      result = finiteMin + random01 * range
      finiteResult = ensureFinite result 0.0
  in (finiteResult, newState)

-- | Generate Gaussian random number using Box-Muller transform
-- Pure function: same inputs → same outputs
-- Returns: (random value, new state)
physicsRandomGaussian :: PhysicsRandomState -> (Double, PhysicsRandomState)
physicsRandomGaussian state =
  let -- Get two uniform random numbers
      (u1Raw, state1) = physicsRandomNext state
      (u2Raw, state2) = physicsRandomNext state1
      -- Ensure u1 is in (0, 1] for log (avoid log(0))
      u1 = if u1Raw <= 0.0 then 0.0001 else if u1Raw >= 1.0 then 0.9999 else u1Raw
      u2 = if u2Raw <= 0.0 then 0.0 else if u2Raw >= 1.0 then 0.9999 else u2Raw
      -- Box-Muller transform
      -- z0 = sqrt(-2 * log(u1)) * cos(2 * pi * u2)
      logU1 = safeLog u1 0.0
      -- -2 * logU1 is always >= 0 (logU1 <= 0 since u1 <= 1), so sqrt is safe
      z0 = safeSqrt (-2 * logU1) * cos (2 * pi * u2)
      result = ensureFinite z0 0.0
  in (result, state2)
