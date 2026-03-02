{-|
Module      : Lattice.Services.ColorCorrection.Vignette
Description : Vignette Effect Math
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for vignette effect calculations:
- Distance from center
- Smoothstep interpolation
- Vignette falloff

All functions are total and deterministic.

Source: ui/src/services/effects/colorRenderer.ts (lines 1544-1628)
-}

module Lattice.Services.ColorCorrection.Vignette
  ( -- * Smoothstep
    smoothstep
  , smoothstepClamped
    -- * Distance
  , normalizedDistance
  , maxDistanceFromCenter
    -- * Vignette
  , aspectFromRoundness
  , vignetteFactor
  , applyVignette
  , vignetteMultiplier
  ) where

-- ────────────────────────────────────────────────────────────────────────────
-- Smoothstep
-- ────────────────────────────────────────────────────────────────────────────

-- | Smoothstep interpolation function.
--
-- Formula: smoothstep(t) = t² × (3 - 2t)
smoothstep :: Double -> Double
smoothstep t = t * t * (3 - 2 * t)

-- | Clamped smoothstep for values outside 0-1.
smoothstepClamped :: Double  -- ^ edge0
                  -> Double  -- ^ edge1
                  -> Double  -- ^ x
                  -> Double
smoothstepClamped edge0 edge1 x =
  let range = edge1 - edge0
      t = if range < 0.0001
          then 0
          else max 0 (min 1 ((x - edge0) / range))
  in smoothstep t

-- ────────────────────────────────────────────────────────────────────────────
-- Distance Calculations
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate normalized distance from center.
normalizedDistance :: Double  -- ^ x
                   -> Double  -- ^ y
                   -> Double  -- ^ centerX
                   -> Double  -- ^ centerY
                   -> Double  -- ^ maxDist
                   -> Double  -- ^ aspectX
                   -> Double  -- ^ aspectY
                   -> Double
normalizedDistance x y centerX centerY maxDist aspectX aspectY =
  let dx = (x - centerX) * aspectX
      dy = (y - centerY) * aspectY
      dist = sqrt (dx * dx + dy * dy)
  in if maxDist < 0.0001 then 0 else dist / maxDist

-- | Calculate max distance from center to corner.
maxDistanceFromCenter :: Double -> Double -> Double
maxDistanceFromCenter width height =
  let cx = width / 2
      cy = height / 2
  in sqrt (cx * cx + cy * cy)

-- ────────────────────────────────────────────────────────────────────────────
-- Vignette Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate aspect ratio adjustments from roundness.
aspectFromRoundness :: Double -> (Double, Double)
aspectFromRoundness roundness =
  let aspectX = 1 + (if roundness > 0 then roundness * 0.5 else 0)
      aspectY = 1 + (if roundness < 0 then (-roundness) * 0.5 else 0)
  in (aspectX, aspectY)

-- | Calculate vignette factor for a pixel.
vignetteFactor :: Double  -- ^ dist
               -> Double  -- ^ midpoint
               -> Double  -- ^ feather
               -> Double
vignetteFactor dist midpoint feather
  | dist <= midpoint = 0
  | otherwise =
      let range = 1 - midpoint + 0.001
          t = (dist - midpoint) / range
          smoothT = smoothstep t
          safeFeather = max 0.01 feather
      in smoothT ** (1 / safeFeather)

-- | Apply vignette to a pixel value.
applyVignette :: Double  -- ^ value (0-255)
              -> Double  -- ^ factor
              -> Double  -- ^ amount
              -> Double  -- ^ result (0-255)
applyVignette value factor amount =
  let multiplier = 1 - factor * amount
  in max 0 (min 255 (value * multiplier))

-- | Calculate complete vignette multiplier for a pixel.
vignetteMultiplier :: Double  -- ^ x
                   -> Double  -- ^ y
                   -> Double  -- ^ width
                   -> Double  -- ^ height
                   -> Double  -- ^ amount
                   -> Double  -- ^ midpoint
                   -> Double  -- ^ roundness
                   -> Double  -- ^ feather
                   -> Double
vignetteMultiplier x y width height amount midpoint roundness feather =
  let centerX = width / 2
      centerY = height / 2
      maxDist = maxDistanceFromCenter width height
      (aspectX, aspectY) = aspectFromRoundness roundness
      dist = normalizedDistance x y centerX centerY maxDist aspectX aspectY
      factor = vignetteFactor dist midpoint feather
  in 1 - factor * amount
