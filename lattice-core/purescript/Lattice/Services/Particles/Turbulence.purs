-- | Lattice.Services.Particles.Turbulence - Noise-Based Force Fields
-- |
-- | Pure mathematical functions for turbulence/noise force fields:
-- | - Simplex noise sampling (noise value provided as input)
-- | - Multi-octave turbulence
-- | - Curl noise for divergence-free flow
-- |
-- | All functions are total and deterministic.
-- | Noise generation happens externally using seeded simplex noise.
-- |
-- | Source: ui/src/services/particleSystem.ts (applyTurbulence)

module Lattice.Services.Particles.Turbulence
  ( TurbulenceConfig(..)
  , TurbulenceType(..)
  , Vec2(..)
  , defaultTurbulenceConfig
  , turbulenceForce
  , turbulenceInBounds
  , multiOctaveNoise
  , curlGradient
  ) where

import Prelude

import Data.Array (foldl, mapWithIndex)
import Data.Int (toNumber)
import Data.Tuple (Tuple(..), fst, snd)
import Math (max, pow, sqrt)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | 2D velocity vector
type Vec2 =
  { x :: Number
  , y :: Number
  }

-- | Turbulence field type
data TurbulenceType
  = TurbulenceNormal    -- Standard noise displacement
  | TurbulenceCurl      -- Curl noise (divergence-free)
  | TurbulenceDirected  -- Noise modulates base direction

derive instance eqTurbulenceType :: Eq TurbulenceType

instance showTurbulenceType :: Show TurbulenceType where
  show TurbulenceNormal = "TurbulenceNormal"
  show TurbulenceCurl = "TurbulenceCurl"
  show TurbulenceDirected = "TurbulenceDirected"

-- | Turbulence configuration
type TurbulenceConfig =
  { x :: Number               -- Center X
  , y :: Number               -- Center Y
  , radius :: Number          -- Effect radius
  , strength :: Number        -- Force strength
  , frequency :: Number       -- Base noise frequency
  , octaves :: Int            -- Number of noise octaves
  , persistence :: Number     -- Amplitude decay per octave
  , lacunarity :: Number      -- Frequency increase per octave
  , turbulenceType :: TurbulenceType
  , evolutionSpeed :: Number  -- Noise evolution speed
  , enabled :: Boolean
  }

--------------------------------------------------------------------------------
-- Default Configuration
--------------------------------------------------------------------------------

-- | Default turbulence configuration
defaultTurbulenceConfig :: TurbulenceConfig
defaultTurbulenceConfig =
  { x: 0.5
  , y: 0.5
  , radius: 0.5
  , strength: 1.0
  , frequency: 4.0
  , octaves: 4
  , persistence: 0.5
  , lacunarity: 2.0
  , turbulenceType: TurbulenceNormal
  , evolutionSpeed: 0.01
  , enabled: true
  }

--------------------------------------------------------------------------------
-- Turbulence Force
--------------------------------------------------------------------------------

-- | Calculate turbulence force on a particle.
-- |
-- | Takes pre-computed noise values for determinism.
turbulenceForce
  :: Number  -- px
  -> Number  -- py
  -> TurbulenceConfig
  -> Number  -- noiseX
  -> Number  -- noiseY
  -> Number  -- deltaTime
  -> Vec2
turbulenceForce px py config noiseX noiseY deltaTime =
  if not config.enabled || not (turbulenceInBounds px py config)
  then { x: 0.0, y: 0.0 }
  else
    let
      dx = config.x - px
      dy = config.y - py
      dist = sqrt (dx * dx + dy * dy)
      safeRadius = max 0.001 config.radius
      influence = 1.0 - dist / safeRadius
      strength = config.strength * 0.0001 * influence
    in
      case config.turbulenceType of
        TurbulenceNormal ->
          { x: noiseX * strength * deltaTime
          , y: noiseY * strength * deltaTime
          }
        TurbulenceCurl ->
          let curl = curlGradient noiseX noiseY
          in
            { x: fst curl * strength * deltaTime
            , y: snd curl * strength * deltaTime
            }
        TurbulenceDirected ->
          { x: noiseX * strength * deltaTime
          , y: noiseY * strength * deltaTime
          }

-- | Check if particle is within turbulence field bounds.
turbulenceInBounds :: Number -> Number -> TurbulenceConfig -> Boolean
turbulenceInBounds px py config =
  let
    dx = config.x - px
    dy = config.y - py
    dist = sqrt (dx * dx + dy * dy)
  in
    dist < config.radius

--------------------------------------------------------------------------------
-- Noise Utilities
--------------------------------------------------------------------------------

-- | Combine multiple octaves of noise with persistence falloff.
multiOctaveNoise :: Number -> Array (Tuple Number Number) -> Tuple Number Number
multiOctaveNoise persistence octaves =
  foldl combine (Tuple 0.0 0.0) (withAmplitude octaves)
  where
    withAmplitude :: Array (Tuple Number Number) -> Array { noise :: Tuple Number Number, amp :: Number }
    withAmplitude octaveArr =
      let indexed = mapWithIndex (\i n -> { noise: n, amp: pow persistence (toNumber i) }) octaveArr
      in indexed

    combine :: Tuple Number Number -> { noise :: Tuple Number Number, amp :: Number } -> Tuple Number Number
    combine (Tuple accX accY) { noise: Tuple nx ny, amp } =
      Tuple (accX + nx * amp) (accY + ny * amp)

-- | Calculate curl gradient from noise values.
-- |
-- | Curl = (-dN/dy, dN/dx) for 2D
curlGradient :: Number -> Number -> Tuple Number Number
curlGradient gradX gradY =
  -- Rotate gradient 90 degrees for curl
  Tuple (-gradY) gradX
