{-|
Module      : Lattice.Services.Particles.Emitter
Description : Particle Emission Logic
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for particle emission:
- Emission rate calculation with accumulator
- Burst emission on enable
- Audio-reactive rate modulation
- Sequential/random emission modes

All functions are total (no partial patterns) and deterministic.
Randomness is provided as input parameters from seeded RNG.

Source: ui/src/services/particleSystem.ts (lines 481-507, 938-1054)
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Particles.Emitter
  ( -- * Types
    EmitterState(..)
  , EmissionResult(..)
  , EmitterConfig(..)
  , EmitMode(..)
    -- * Emission Logic
  , initialEmitterState
  , calculateEmission
  , applyBurst
  , stepEmissionAccumulator
    -- * Rate Calculation
  , effectiveEmissionRate
  , burstCount
    -- * Sequential Emission
  , advanceSequentialT
  ) where

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Emission mode for spline/sequential emission
data EmitMode
  = EmitRandom      -- ^ Random position along emitter shape
  | EmitUniform     -- ^ Evenly spaced positions
  | EmitSequential  -- ^ Sequentially advancing position
  | EmitStart       -- ^ Near start of path
  | EmitEnd         -- ^ Near end of path
  deriving (Show, Eq)

-- | Per-emitter runtime state
data EmitterState = EmitterState
  { esAccumulator :: Double     -- ^ Fractional particle accumulator (0 <= acc < 1)
  , esSequentialT :: Double     -- ^ Current T for sequential emission (0-1)
  , esBurstTriggered :: Bool    -- ^ Whether initial burst has fired
  , esEnabled :: Bool           -- ^ Current enabled state
  } deriving (Show, Eq)

-- | Static emitter configuration
data EmitterConfig = EmitterConfig
  { ecEmissionRate :: Double    -- ^ Particles per second
  , ecInitialBurst :: Double    -- ^ Burst multiplier on enable (0-10)
  , ecEnabled :: Bool           -- ^ Whether emitter is active
  , ecSequentialSpeed :: Double -- ^ T advance per emission for sequential mode
  } deriving (Show, Eq)

-- | Result of emission calculation
data EmissionResult = EmissionResult
  { erParticlesToSpawn :: Int       -- ^ Number of particles to spawn this frame
  , erNewAccumulator :: Double      -- ^ Updated fractional accumulator
  , erNewSequentialT :: Double      -- ^ Updated sequential T
  , erBurstTriggered :: Bool        -- ^ Whether burst was consumed
  } deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Initial State
--------------------------------------------------------------------------------

-- | Create initial emitter state
initialEmitterState :: EmitterState
initialEmitterState = EmitterState
  { esAccumulator = 0
  , esSequentialT = 0
  , esBurstTriggered = False
  , esEnabled = False
  }

--------------------------------------------------------------------------------
-- Emission Rate
--------------------------------------------------------------------------------

-- | Calculate effective emission rate with optional audio modulation.
--
-- If audioValue is provided and finite, it overrides the base rate.
-- Otherwise, the base rate is used.
--
-- @param baseRate Base emission rate (particles/second)
-- @param audioValue Optional audio-reactive rate override
-- @return Effective rate (always >= 0)
effectiveEmissionRate :: Double -> Maybe Double -> Double
effectiveEmissionRate baseRate audioValue =
  case audioValue of
    Just v | isValidPositive v -> v
    _                          -> max 0 baseRate
  where
    isValidPositive x = not (isNaN x) && not (isInfinite x) && x >= 0

-- | Calculate burst particle count.
--
-- Burst = emissionRate * burstMultiplier * 10
--
-- @param emissionRate Base emission rate
-- @param burstMultiplier Burst intensity (0-10)
-- @return Number of burst particles
burstCount :: Double -> Double -> Int
burstCount emissionRate burstMultiplier =
  floor (emissionRate * max 0 burstMultiplier * 10)

--------------------------------------------------------------------------------
-- Emission Calculation
--------------------------------------------------------------------------------

-- | Calculate emission for a single frame.
--
-- Uses fractional accumulator to handle non-integer emission rates.
-- Example: rate=2.5 at dt=1 → accumulator cycles: 0.5, 0.0, 0.5, 0.0...
--
-- @param config Emitter configuration
-- @param state Current emitter state
-- @param deltaTime Frame delta time
-- @param maxParticles Maximum total particles allowed
-- @param currentParticleCount Current particle count
-- @param audioRateOverride Optional audio-reactive rate
-- @return Emission result with updated state
calculateEmission
  :: EmitterConfig
  -> EmitterState
  -> Double
  -> Int
  -> Int
  -> Maybe Double
  -> EmissionResult
calculateEmission config state deltaTime maxParticles currentCount audioRate =
  if not (ecEnabled config) || currentCount >= maxParticles
  then EmissionResult 0 (esAccumulator state) (esSequentialT state) (esBurstTriggered state)
  else
    let rate = effectiveEmissionRate (ecEmissionRate config) audioRate
        particlesToEmit = rate * max 0 deltaTime
        accumulated = esAccumulator state + particlesToEmit
        (spawnCount, newAcc) = stepEmissionAccumulator accumulated (maxParticles - currentCount)
    in EmissionResult
         { erParticlesToSpawn = spawnCount
         , erNewAccumulator = newAcc
         , erNewSequentialT = esSequentialT state
         , erBurstTriggered = esBurstTriggered state
         }

-- | Step the emission accumulator, extracting whole particles.
--
-- @param accumulated Current accumulated value
-- @param maxSpawn Maximum particles we can spawn
-- @return (particles to spawn, remaining accumulator)
stepEmissionAccumulator :: Double -> Int -> (Int, Double)
stepEmissionAccumulator accumulated maxSpawn =
  let wholeParticles = min (floor accumulated) maxSpawn
      remaining = accumulated - fromIntegral wholeParticles
  in (wholeParticles, max 0 remaining)

-- | Apply initial burst emission when emitter becomes enabled.
--
-- @param config Emitter configuration
-- @param state Current state
-- @param wasEnabled Previous enabled state
-- @param maxParticles Maximum particles allowed
-- @param currentCount Current particle count
-- @return Updated state and burst particle count
applyBurst
  :: EmitterConfig
  -> EmitterState
  -> Bool
  -> Int
  -> Int
  -> (EmitterState, Int)
applyBurst config state wasEnabled maxParticles currentCount =
  if ecEnabled config && not wasEnabled && not (esBurstTriggered state)
     && ecInitialBurst config > 0
  then
    let burst = min (burstCount (ecEmissionRate config) (ecInitialBurst config))
                    (maxParticles - currentCount)
        newState = state { esBurstTriggered = True }
    in (newState, burst)
  else
    (state, 0)

--------------------------------------------------------------------------------
-- Sequential Emission
--------------------------------------------------------------------------------

-- | Advance sequential T for the next emission.
--
-- Wraps around at 1.0 to create continuous cycling.
--
-- @param currentT Current T value (0-1)
-- @param speed Advance per emission
-- @return New T value (wrapped to 0-1)
advanceSequentialT :: Double -> Double -> Double
advanceSequentialT currentT speed =
  let newT = currentT + max 0.001 speed
  in if newT > 1 then newT - 1 else newT
