-- | Lattice.Services.ColorCorrection.Vignette - Vignette Effect Math
-- |
-- | Pure mathematical functions for vignette effect calculations:
-- | - Distance from center
-- | - Smoothstep interpolation
-- | - Vignette falloff
-- |
-- | All functions are total and deterministic.
-- |
-- | Source: ui/src/services/effects/colorRenderer.ts (lines 1544-1628)

module Lattice.Services.ColorCorrection.Vignette
  ( smoothstep
  , smoothstepClamped
  , normalizedDistance
  , maxDistanceFromCenter
  , aspectFromRoundness
  , vignetteFactor
  , applyVignette
  , vignetteMultiplier
  ) where

import Prelude

import Data.Tuple (Tuple(..))
import Math (max, min, pow, sqrt)

--------------------------------------------------------------------------------
-- Smoothstep
--------------------------------------------------------------------------------

-- | Smoothstep interpolation function.
-- |
-- | Formula: smoothstep(t) = t² × (3 - 2t)
smoothstep :: Number -> Number
smoothstep t = t * t * (3.0 - 2.0 * t)

-- | Clamped smoothstep for values outside 0-1.
smoothstepClamped :: Number -> Number -> Number -> Number
smoothstepClamped edge0 edge1 x =
  let range = edge1 - edge0
      t = if range < 0.0001
          then 0.0
          else max 0.0 (min 1.0 ((x - edge0) / range))
  in smoothstep t

--------------------------------------------------------------------------------
-- Distance Calculations
--------------------------------------------------------------------------------

-- | Calculate normalized distance from center.
normalizedDistance :: Number -> Number -> Number -> Number -> Number
                   -> Number -> Number -> Number
normalizedDistance x y centerX centerY maxDist aspectX aspectY =
  let dx = (x - centerX) * aspectX
      dy = (y - centerY) * aspectY
      dist = sqrt (dx * dx + dy * dy)
  in if maxDist < 0.0001 then 0.0 else dist / maxDist

-- | Calculate max distance from center to corner.
maxDistanceFromCenter :: Number -> Number -> Number
maxDistanceFromCenter width height =
  let cx = width / 2.0
      cy = height / 2.0
  in sqrt (cx * cx + cy * cy)

--------------------------------------------------------------------------------
-- Vignette Calculation
--------------------------------------------------------------------------------

-- | Calculate aspect ratio adjustments from roundness.
aspectFromRoundness :: Number -> Tuple Number Number
aspectFromRoundness roundness =
  let aspectX = 1.0 + (if roundness > 0.0 then roundness * 0.5 else 0.0)
      aspectY = 1.0 + (if roundness < 0.0 then (-roundness) * 0.5 else 0.0)
  in Tuple aspectX aspectY

-- | Calculate vignette factor for a pixel.
vignetteFactor :: Number -> Number -> Number -> Number
vignetteFactor dist midpoint feather =
  if dist <= midpoint then 0.0
  else
    let range = 1.0 - midpoint + 0.001
        t = (dist - midpoint) / range
        smoothT = smoothstep t
        safeFeather = max 0.01 feather
    in pow smoothT (1.0 / safeFeather)

-- | Apply vignette to a pixel value.
applyVignette :: Number -> Number -> Number -> Number
applyVignette value factor amount =
  let multiplier = 1.0 - factor * amount
  in max 0.0 (min 255.0 (value * multiplier))

-- | Calculate complete vignette multiplier for a pixel.
vignetteMultiplier :: Number -> Number -> Number -> Number -> Number
                   -> Number -> Number -> Number -> Number
vignetteMultiplier x y width height amount midpoint roundness feather =
  let centerX = width / 2.0
      centerY = height / 2.0
      maxDist = maxDistanceFromCenter width height
      Tuple aspectX aspectY = aspectFromRoundness roundness
      dist = normalizedDistance x y centerX centerY maxDist aspectX aspectY
      factor = vignetteFactor dist midpoint feather
  in 1.0 - factor * amount
