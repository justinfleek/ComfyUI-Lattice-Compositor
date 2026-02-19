-- | Lattice.Services.Particles.Emitter - Particle Emission Logic
-- |
-- | Pure mathematical functions for particle emission:
-- | - Emission rate calculation with accumulator
-- | - Burst emission on enable
-- | - Audio-reactive rate modulation
-- |
-- | All functions are total and deterministic.
-- |
-- | Source: ui/src/services/particleSystem.ts (lines 481-507, 938-1054)

module Lattice.Services.Particles.Emitter
  ( EmitterState(..)
  , EmissionResult(..)
  , EmitMode(..)
  , initialEmitterState
  , effectiveEmissionRate
  , burstCount
  , calculateEmission
  , stepAccumulator
  , advanceSequentialT
  ) where

import Prelude

import Data.Int (floor, toNumber)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Math (max)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Emission mode for spline/sequential emission
data EmitMode
  = EmitRandom
  | EmitUniform
  | EmitSequential
  | EmitStart
  | EmitEnd

derive instance eqEmitMode :: Eq EmitMode

instance showEmitMode :: Show EmitMode where
  show EmitRandom = "EmitRandom"
  show EmitUniform = "EmitUniform"
  show EmitSequential = "EmitSequential"
  show EmitStart = "EmitStart"
  show EmitEnd = "EmitEnd"

-- | Per-emitter runtime state
type EmitterState =
  { accumulator :: Number     -- Fractional particle accumulator (0 <= acc < 1)
  , sequentialT :: Number     -- Current T for sequential emission (0-1)
  , burstTriggered :: Boolean -- Whether initial burst has fired
  , enabled :: Boolean        -- Current enabled state
  }

-- | Result of emission calculation
type EmissionResult =
  { particlesToSpawn :: Int
  , newAccumulator :: Number
  , newSequentialT :: Number
  , burstTriggered :: Boolean
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Initial State
-- ────────────────────────────────────────────────────────────────────────────

-- | Create initial emitter state
initialEmitterState :: EmitterState
initialEmitterState =
  { accumulator: 0.0
  , sequentialT: 0.0
  , burstTriggered: false
  , enabled: false
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Emission Rate
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate effective emission rate with optional audio modulation.
-- |
-- | If audioValue is provided and positive, it overrides the base rate.
effectiveEmissionRate :: Number -> Maybe Number -> Number
effectiveEmissionRate baseRate audioValue =
  case audioValue of
    Just v | isValidPositive v -> v
    _ -> max 0.0 baseRate
  where
    isValidPositive x = not (isNaN x) && isFinite x && x >= 0.0

-- | Foreign function check for NaN
foreign import isNaN :: Number -> Boolean

-- | Foreign function check for finite
foreign import isFinite :: Number -> Boolean

-- | Calculate burst particle count.
-- |
-- | Burst = emissionRate * burstMultiplier * 10
burstCount :: Number -> Number -> Int
burstCount emissionRate burstMultiplier =
  floor (emissionRate * max 0.0 burstMultiplier * 10.0)

-- ────────────────────────────────────────────────────────────────────────────
-- Accumulator Logic
-- ────────────────────────────────────────────────────────────────────────────

-- | Step the emission accumulator.
-- |
-- | Returns (particles to spawn, remaining accumulator)
stepAccumulator :: Number -> Int -> Tuple Int Number
stepAccumulator accumulated maxSpawn =
  let
    wholeParticles = min (floor accumulated) maxSpawn
    remaining = max 0.0 (accumulated - toNumber wholeParticles)
  in
    Tuple wholeParticles remaining

-- | Calculate particles to emit this frame.
calculateEmission
  :: Number  -- emissionRate
  -> Number  -- deltaTime
  -> Number  -- currentAccumulator
  -> Int     -- maxSpawn
  -> Tuple Int Number
calculateEmission emissionRate deltaTime currentAcc maxSpawn =
  let
    particlesToEmit = emissionRate * max 0.0 deltaTime
    accumulated = currentAcc + particlesToEmit
  in
    stepAccumulator accumulated maxSpawn

-- ────────────────────────────────────────────────────────────────────────────
-- Sequential Emission
-- ────────────────────────────────────────────────────────────────────────────

-- | Advance sequential T for next emission, wrapping at 1.0.
advanceSequentialT :: Number -> Number -> Number
advanceSequentialT currentT speed =
  let
    safeSpeed = max 0.001 speed
    newT = currentT + safeSpeed
  in
    if newT > 1.0 then newT - 1.0 else newT
