{-|
{-# LANGUAGE OverloadedStrings #-}
Module      : Lattice.Services.Particles.Turbulence
Description : Turbulence/Noise Force Fields
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for turbulence/noise-based force fields:
- Simplex noise sampling (noise value provided as input)
- Multi-octave turbulence
- Curl noise for divergence-free flow
- Time-evolving turbulence

All functions operate on pre-computed noise values for determinism.
Noise generation happens externally using seeded simplex noise.

Source: ui/src/services/particleSystem.ts (applyTurbulence, turbulenceFields)
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Particles.Turbulence
  ( -- * Types
    TurbulenceConfig(..)
  , TurbulenceType(..)
  , NoiseOctave(..)
    -- * Turbulence Calculation
  , turbulenceForce
  , sampleTurbulence
  , multiOctaveNoise
    -- * Curl Noise
  , curlNoiseForce
  , curlGradient
    -- * Field Configuration
  , defaultTurbulenceConfig
  , turbulenceInBounds
  ) where

import Lattice.Services.Particles.Forces (Vec2(..))

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Turbulence field type
data TurbulenceType
  = TurbulenceNormal    -- ^ Standard noise-based displacement
  | TurbulenceCurl      -- ^ Curl noise (divergence-free, swirly)
  | TurbulenceDirected  -- ^ Noise modulates a base direction
  deriving (Show, Eq)

-- | Single noise octave for multi-octave turbulence
data NoiseOctave = NoiseOctave
  { noFrequency :: Double    -- ^ Frequency multiplier
  , noAmplitude :: Double    -- ^ Amplitude multiplier
  } deriving (Show, Eq)

-- | Turbulence field configuration
data TurbulenceConfig = TurbulenceConfig
  { tcX :: Double              -- ^ Center X position
  , tcY :: Double              -- ^ Center Y position
  , tcRadius :: Double         -- ^ Effect radius
  , tcStrength :: Double       -- ^ Force strength
  , tcFrequency :: Double      -- ^ Base noise frequency
  , tcOctaves :: Int           -- ^ Number of noise octaves
  , tcPersistence :: Double    -- ^ Amplitude decay per octave
  , tcLacunarity :: Double     -- ^ Frequency increase per octave
  , tcTurbulenceType :: TurbulenceType
  , tcEvolutionSpeed :: Double -- ^ How fast noise evolves over time
  , tcEnabled :: Bool
  } deriving (Show, Eq)

-- ────────────────────────────────────────────────────────────────────────────
-- Default Configuration
-- ────────────────────────────────────────────────────────────────────────────

-- | Default turbulence configuration
defaultTurbulenceConfig :: TurbulenceConfig
defaultTurbulenceConfig = TurbulenceConfig
  { tcX = 0.5
  , tcY = 0.5
  , tcRadius = 0.5
  , tcStrength = 1.0
  , tcFrequency = 4.0
  , tcOctaves = 4
  , tcPersistence = 0.5
  , tcLacunarity = 2.0
  , tcTurbulenceType = TurbulenceNormal
  , tcEvolutionSpeed = 0.01
  , tcEnabled = True
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Turbulence Force
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate turbulence force on a particle.
--
-- @param px Particle X position
-- @param py Particle Y position
-- @param config Turbulence configuration
-- @param noiseValueX Pre-computed noise value for X force
-- @param noiseValueY Pre-computed noise value for Y force
-- @param deltaTime Frame delta time
-- @return Velocity delta
turbulenceForce
  :: Double -> Double
  -> TurbulenceConfig
  -> Double -> Double
  -> Double
  -> Vec2
turbulenceForce px py config noiseX noiseY deltaTime =
  if not (tcEnabled config) || not (turbulenceInBounds px py config)
  then Vec2 0 0
  else
    let dx = tcX config - px
        dy = tcY config - py
        dist = sqrt (dx * dx + dy * dy)
        influence = 1 - dist / max 0.001 (tcRadius config)
        strength = tcStrength config * 0.0001 * influence
    in case tcTurbulenceType config of
         TurbulenceNormal ->
           Vec2 (noiseX * strength * deltaTime)
                (noiseY * strength * deltaTime)
         TurbulenceCurl ->
           -- Curl noise: perpendicular to gradient
           let curl = curlGradient noiseX noiseY
           in Vec2 (fst curl * strength * deltaTime)
                   (snd curl * strength * deltaTime)
         TurbulenceDirected ->
           -- Modulate a base direction with noise
           Vec2 (noiseX * strength * deltaTime)
                (noiseY * strength * deltaTime)

-- | Check if particle is within turbulence field bounds.
turbulenceInBounds :: Double -> Double -> TurbulenceConfig -> Bool
turbulenceInBounds px py config =
  let dx = tcX config - px
      dy = tcY config - py
      dist = sqrt (dx * dx + dy * dy)
  in dist < tcRadius config

-- ────────────────────────────────────────────────────────────────────────────
-- Noise Sampling
-- ────────────────────────────────────────────────────────────────────────────

-- | Sample turbulence at a position.
--
-- This is a pure function that takes pre-computed noise values.
-- The actual noise generation happens externally.
--
-- @param baseNoiseX Base noise value for X
-- @param baseNoiseY Base noise value for Y
-- @param config Turbulence configuration
-- @param octaveNoise List of (noiseX, noiseY) for each octave
-- @return Combined noise values (x, y)
sampleTurbulence
  :: Double -> Double
  -> TurbulenceConfig
  -> [(Double, Double)]
  -> (Double, Double)
sampleTurbulence baseX baseY config octaveNoise =
  let numOctaves = min (tcOctaves config) (length octaveNoise)
      combined = multiOctaveNoise (tcPersistence config) (take numOctaves octaveNoise)
  in (fst combined + baseX, snd combined + baseY)

-- | Combine multiple octaves of noise with persistence falloff.
--
-- @param persistence Amplitude decay per octave (typically 0.5)
-- @param octaves List of (noiseX, noiseY) per octave
-- @return Combined noise value
multiOctaveNoise :: Double -> [(Double, Double)] -> (Double, Double)
multiOctaveNoise persistence octaves =
  let go _ [] = (0, 0)
      go amp ((nx, ny) : rest) =
        let (restX, restY) = go (amp * persistence) rest
        in (nx * amp + restX, ny * amp + restY)
  in go 1.0 octaves

-- ────────────────────────────────────────────────────────────────────────────
-- Curl Noise
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate curl noise force for divergence-free motion.
--
-- Curl noise creates swirling, smoke-like motion without
-- compression or expansion.
curlNoiseForce
  :: Double -> Double
  -> Double -> Double
  -> Vec2
curlNoiseForce noiseX noiseY strength deltaTime =
  let (curlX, curlY) = curlGradient noiseX noiseY
  in Vec2 (curlX * strength * deltaTime)
          (curlY * strength * deltaTime)

-- | Calculate curl gradient from noise values.
--
-- Curl = (-dN/dy, dN/dx) for 2D
-- We approximate this from neighboring noise samples.
--
-- @param noiseX Noise partial derivative in X
-- @param noiseY Noise partial derivative in Y
-- @return Curl vector (perpendicular to gradient)
curlGradient :: Double -> Double -> (Double, Double)
curlGradient gradX gradY =
  -- Rotate gradient 90 degrees for curl
  (-gradY, gradX)
