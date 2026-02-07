{-
  Lattice.Services.Blur.Radial - Radial Blur Mathematics

  Pure mathematical functions for radial blur calculations:
  - Spin blur (rotation around center)
  - Zoom blur (scaling from center)
  - Center-relative coordinates

  Source: ui/src/services/effects/blurRenderer.ts (lines 1166-1317)
-}

module Lattice.Services.Blur.Radial
  ( vectorFromCenter
  , distanceFromCenter
  , angleFromCenter
  , spinBlurPosition
  , spinSampleAngle
  , spinMaxAngle
  , zoomBlurPosition
  , zoomSampleScale
  , zoomMaxAmount
  , centerToPixels
  , normalizedCenterToPixels
  , qualitySampleCount
  ) where

import Prelude

import Data.Int (toNumber) as Int
import Data.Tuple (Tuple(..))
import Math (sqrt, atan2, cos, sin, pi)

--------------------------------------------------------------------------------
-- Center-Relative Coordinates
--------------------------------------------------------------------------------

-- | Calculate vector from center to pixel.
vectorFromCenter :: Number -> Number -> Number -> Number -> Tuple Number Number
vectorFromCenter x y centerX centerY = Tuple (x - centerX) (y - centerY)

-- | Calculate distance from center.
distanceFromCenter :: Number -> Number -> Number
distanceFromCenter dx dy = sqrt (dx * dx + dy * dy)

-- | Calculate angle from center (atan2).
angleFromCenter :: Number -> Number -> Number
angleFromCenter dx dy = atan2 dy dx

--------------------------------------------------------------------------------
-- Spin Blur
--------------------------------------------------------------------------------

-- | Calculate rotated position for spin blur.
spinBlurPosition :: Number -> Number -> Number -> Number -> Tuple Number Number
spinBlurPosition centerX centerY distance angle =
  Tuple (centerX + cos angle * distance) (centerY + sin angle * distance)

-- | Calculate sample angle for spin blur.
spinSampleAngle :: Number -> Number -> Int -> Int -> Number
spinSampleAngle baseAngle maxAngle sampleIndex sampleCount =
  let t = Int.toNumber sampleIndex / Int.toNumber (sampleCount - 1) - 0.5
  in baseAngle + t * maxAngle

-- | Calculate max angle from spin amount.
spinMaxAngle :: Number -> Number
spinMaxAngle amount = (amount / 100.0) * pi * 0.5

--------------------------------------------------------------------------------
-- Zoom Blur
--------------------------------------------------------------------------------

-- | Calculate scaled position for zoom blur.
zoomBlurPosition :: Number -> Number -> Number -> Number -> Number -> Tuple Number Number
zoomBlurPosition centerX centerY dx dy scale =
  Tuple (centerX + dx * scale) (centerY + dy * scale)

-- | Calculate scale factor for zoom blur sample.
zoomSampleScale :: Number -> Int -> Int -> Number
zoomSampleScale maxZoom sampleIndex sampleCount =
  let t = Int.toNumber sampleIndex / Int.toNumber (sampleCount - 1)
  in 1.0 - t * maxZoom

-- | Calculate max zoom from amount.
zoomMaxAmount :: Number -> Number
zoomMaxAmount amount = amount / 100.0

--------------------------------------------------------------------------------
-- Center Point Conversion
--------------------------------------------------------------------------------

-- | Convert center point from percentage to pixels.
centerToPixels :: Number -> Int -> Number
centerToPixels centerPercent dimension =
  (centerPercent / 100.0) * Int.toNumber dimension

-- | Convert normalized center (0-1) to pixels.
normalizedCenterToPixels :: Number -> Int -> Number
normalizedCenterToPixels centerNorm dimension =
  centerNorm * Int.toNumber dimension

--------------------------------------------------------------------------------
-- Quality Settings
--------------------------------------------------------------------------------

-- | Get sample count from quality setting.
qualitySampleCount :: String -> Int
qualitySampleCount quality
  | quality == "best" = 32
  | quality == "good" = 16
  | otherwise = 8
