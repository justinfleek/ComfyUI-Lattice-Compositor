{-
  Lattice.Services.Distort.Ripple - Ripple Distortion Mathematics

  Pure mathematical functions for ripple/wave distortion:
  - Concentric wave calculation
  - Decay/falloff functions
  - Radial displacement

  Source: ui/src/services/effects/distortRenderer.ts (lines 1209-1324)
-}

module Lattice.Services.Distort.Ripple
  ( RippleConfig
  , RippleResult
  , rippleWave
  , decayFactor
  , linearFalloff
  , smoothFalloff
  , unitDirection
  , radialDisplace
  , calculateRipple
  , combineRipples
  , phaseToRadians
  , animatedPhase
  ) where

import Prelude

import Data.Array (foldl)
import Data.Int (toNumber) as Int
import Data.Tuple (Tuple(..))
import Math (pi, pow, sin, sqrt)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Ripple configuration
type RippleConfig =
  { centerX    :: Number  -- Center X (0-1 normalized)
  , centerY    :: Number  -- Center Y (0-1 normalized)
  , radius     :: Number  -- Maximum radius of effect (pixels)
  , wavelength :: Number  -- Distance between wave peaks (pixels)
  , amplitude  :: Number  -- Maximum displacement (pixels)
  , phase      :: Number  -- Phase offset (radians, for animation)
  , decay      :: Number  -- Falloff exponent (0-1)
  }

-- | Ripple displacement result
type RippleResult =
  { srcX     :: Number
  , srcY     :: Number
  , inEffect :: Boolean   -- Whether pixel is within ripple radius
  }

--------------------------------------------------------------------------------
-- Wave Calculation
--------------------------------------------------------------------------------

-- | Calculate ripple wave value at a distance.
--
--   Uses sine wave with phase offset.
--
--   @param dist Distance from center (pixels)
--   @param wavelength Distance between peaks (pixels)
--   @param phase Phase offset (radians)
--   @return Wave value in [-1, 1]
rippleWave :: Number -> Number -> Number -> Number
rippleWave dist wavelength phase
  | wavelength < 0.0001 = 0.0
  | otherwise = sin ((dist / wavelength) * 2.0 * pi + phase)

--------------------------------------------------------------------------------
-- Decay/Falloff
--------------------------------------------------------------------------------

-- | Calculate decay factor based on distance from center.
--
--   Uses power function for smooth falloff.
--
--   @param dist Distance from center
--   @param radius Maximum effect radius
--   @param decay Decay exponent (higher = faster falloff)
--   @return Falloff factor in [0, 1]
decayFactor :: Number -> Number -> Number -> Number
decayFactor dist radius decayExp
  | radius <= 0.0 = 0.0
  | dist >= radius = 0.0
  | otherwise = pow (1.0 - dist / radius) decayExp

-- | Linear falloff (simple version).
--
--   @param dist Distance from center
--   @param radius Maximum radius
--   @return Linear falloff in [0, 1]
linearFalloff :: Number -> Number -> Number
linearFalloff dist radius
  | radius <= 0.0 = 0.0
  | otherwise = max 0.0 (1.0 - dist / radius)

-- | Smooth falloff using smoothstep.
--
--   @param dist Distance from center
--   @param radius Maximum radius
--   @return Smooth falloff in [0, 1]
smoothFalloff :: Number -> Number -> Number
smoothFalloff dist radius
  | radius <= 0.0 = 0.0
  | otherwise =
      let t = max 0.0 (min 1.0 (1.0 - dist / radius))
      in t * t * (3.0 - 2.0 * t)

--------------------------------------------------------------------------------
-- Radial Displacement
--------------------------------------------------------------------------------

-- | Calculate unit direction vector from center to point.
--
--   @param dx X distance from center
--   @param dy Y distance from center
--   @param dist Total distance (pre-computed)
--   @return (nx, ny) unit direction vector
unitDirection :: Number -> Number -> Number -> Tuple Number Number
unitDirection dx dy dist
  | dist < 0.0001 = Tuple 0.0 0.0
  | otherwise = Tuple (dx / dist) (dy / dist)

-- | Apply radial displacement along direction from center.
--
--   @param x Current X
--   @param y Current Y
--   @param nx Unit direction X
--   @param ny Unit direction Y
--   @param displacement Displacement amount (signed)
--   @return (newX, newY) displaced position
radialDisplace :: Number -> Number -> Number -> Number -> Number -> Tuple Number Number
radialDisplace x y nx ny displacement =
  Tuple (x - nx * displacement) (y - ny * displacement)

--------------------------------------------------------------------------------
-- Ripple Effect
--------------------------------------------------------------------------------

-- | Calculate ripple displacement for a single pixel.
--
--   @param x Pixel X coordinate
--   @param y Pixel Y coordinate
--   @param config Ripple configuration
--   @param width Image width (for center conversion)
--   @param height Image height (for center conversion)
--   @return Displaced source coordinates
calculateRipple :: Number -> Number -> RippleConfig -> Number -> Number -> RippleResult
calculateRipple x y config width height =
  let centerXPixels = config.centerX * width
      centerYPixels = config.centerY * height
      dx = x - centerXPixels
      dy = y - centerYPixels
      dist = sqrt (dx * dx + dy * dy)
  in
    -- Check if within effect radius
    if dist <= 0.0 then
      { srcX: x, srcY: y, inEffect: false }
    else if dist >= config.radius then
      { srcX: x, srcY: y, inEffect: false }
    else
      -- Calculate ripple displacement
      let wave = rippleWave dist config.wavelength config.phase
          falloff = decayFactor dist config.radius config.decay
          displacement = wave * config.amplitude * falloff

          -- Get radial direction and displace
          Tuple nx ny = unitDirection dx dy dist
          Tuple srcX srcY = radialDisplace x y nx ny displacement

      in { srcX, srcY, inEffect: true }

--------------------------------------------------------------------------------
-- Multiple Ripple Sources
--------------------------------------------------------------------------------

-- | Combine displacement from multiple ripple sources.
--
--   Uses additive blending of displacements.
--
--   @param x Pixel X
--   @param y Pixel Y
--   @param configs Array of ripple configurations
--   @param width Image width
--   @param height Image height
--   @return Combined displaced coordinates
combineRipples :: Number -> Number -> Array RippleConfig -> Number -> Number -> Tuple Number Number
combineRipples x y configs width height =
  let accumDisplacement (Tuple accDx accDy) config =
        let result = calculateRipple x y config width height
        in if result.inEffect
           then Tuple (accDx + (x - result.srcX)) (accDy + (y - result.srcY))
           else Tuple accDx accDy

      Tuple totalDx totalDy = foldl accumDisplacement (Tuple 0.0 0.0) configs

  in Tuple (x - totalDx) (y - totalDy)

--------------------------------------------------------------------------------
-- Animation Helpers
--------------------------------------------------------------------------------

-- | Convert degrees to radians for phase.
--
--   @param degrees Phase in degrees
--   @return Phase in radians
phaseToRadians :: Number -> Number
phaseToRadians degrees = degrees * pi / 180.0

-- | Calculate animated phase for looping.
--
--   @param time Current time (0-1 normalized over loop period)
--   @param loops Number of complete wave cycles per period
--   @return Phase in radians
animatedPhase :: Number -> Int -> Number
animatedPhase time loops = time * Int.toNumber loops * 2.0 * pi
