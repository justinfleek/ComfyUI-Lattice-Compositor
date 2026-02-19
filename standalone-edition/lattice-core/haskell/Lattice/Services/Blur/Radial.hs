{-|
  Lattice.Services.Blur.Radial - Radial Blur Mathematics

  Pure mathematical functions for radial blur calculations:
  - Spin blur (rotation around center)
  - Zoom blur (scaling from center)
  - Center-relative coordinates

  Source: ui/src/services/effects/blurRenderer.ts (lines 1166-1317)
-}

module Lattice.Services.Blur.Radial
  ( -- * Center-Relative Coordinates
    vectorFromCenter
  , distanceFromCenter
  , angleFromCenter
    -- * Spin Blur
  , spinBlurPosition
  , spinSampleAngle
  , spinMaxAngle
    -- * Zoom Blur
  , zoomBlurPosition
  , zoomSampleScale
  , zoomMaxAmount
    -- * Center Point Conversion
  , centerToPixels
  , normalizedCenterToPixels
    -- * Quality Settings
  , qualitySampleCount
  ) where

-- ────────────────────────────────────────────────────────────────────────────
-- Center-Relative Coordinates
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate vector from center to pixel.
--
--   @param x Pixel X coordinate
--   @param y Pixel Y coordinate
--   @param centerX Center X coordinate
--   @param centerY Center Y coordinate
--   @return (dx, dy) vector from center
vectorFromCenter :: Double -> Double -> Double -> Double -> (Double, Double)
vectorFromCenter x y centerX centerY = (x - centerX, y - centerY)

-- | Calculate distance from center.
--
--   @param dx X distance from center
--   @param dy Y distance from center
--   @return Euclidean distance
distanceFromCenter :: Double -> Double -> Double
distanceFromCenter dx dy = sqrt (dx * dx + dy * dy)

-- | Calculate angle from center (atan2).
--
--   @param dx X distance from center
--   @param dy Y distance from center
--   @return Angle in radians
angleFromCenter :: Double -> Double -> Double
angleFromCenter dx dy = atan2 dy dx

-- ────────────────────────────────────────────────────────────────────────────
-- Spin Blur
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate rotated position for spin blur.
--
--   Spin blur rotates pixels around a center point.
--
--   @param centerX Center X coordinate
--   @param centerY Center Y coordinate
--   @param distance Distance from center
--   @param angle New angle (base angle + rotation offset)
--   @return (x, y) rotated position
spinBlurPosition :: Double -> Double -> Double -> Double -> (Double, Double)
spinBlurPosition centerX centerY distance angle =
  (centerX + cos angle * distance, centerY + sin angle * distance)

-- | Calculate sample angle for spin blur.
--
--   @param baseAngle Original angle of pixel
--   @param maxAngle Maximum rotation angle (at amount=1)
--   @param sampleIndex Index of sample (0 to sampleCount-1)
--   @param sampleCount Total number of samples
--   @return Angle for this sample
spinSampleAngle :: Double -> Double -> Int -> Int -> Double
spinSampleAngle baseAngle maxAngle sampleIndex sampleCount =
  let t = fromIntegral sampleIndex / fromIntegral (sampleCount - 1) - 0.5  -- -0.5 to 0.5
  in baseAngle + t * maxAngle

-- | Calculate max angle from spin amount.
--
--   At amount=100, max rotation is 90 degrees (π/2).
--
--   @param amount Spin amount (0-100)
--   @return Maximum angle in radians
spinMaxAngle :: Double -> Double
spinMaxAngle amount = (amount / 100.0) * pi * 0.5

-- ────────────────────────────────────────────────────────────────────────────
-- Zoom Blur
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate scaled position for zoom blur.
--
--   Zoom blur scales pixels toward or away from center.
--
--   @param centerX Center X coordinate
--   @param centerY Center Y coordinate
--   @param dx X distance from center
--   @param dy Y distance from center
--   @param scale Scale factor (1.0 = no zoom, <1 = toward center)
--   @return (x, y) scaled position
zoomBlurPosition :: Double -> Double -> Double -> Double -> Double -> (Double, Double)
zoomBlurPosition centerX centerY dx dy scale =
  (centerX + dx * scale, centerY + dy * scale)

-- | Calculate scale factor for zoom blur sample.
--
--   @param maxZoom Maximum zoom amount (0-1)
--   @param sampleIndex Index of sample
--   @param sampleCount Total number of samples
--   @return Scale factor for this sample
zoomSampleScale :: Double -> Int -> Int -> Double
zoomSampleScale maxZoom sampleIndex sampleCount =
  let t = fromIntegral sampleIndex / fromIntegral (sampleCount - 1)  -- 0 to 1
  in 1.0 - t * maxZoom

-- | Calculate max zoom from amount.
--
--   At amount=100, max zoom is 100% (scale down to 0).
--
--   @param amount Zoom amount (0-100)
--   @return Maximum zoom factor (0-1)
zoomMaxAmount :: Double -> Double
zoomMaxAmount amount = amount / 100.0

-- ────────────────────────────────────────────────────────────────────────────
-- Center Point Conversion
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert center point from percentage to pixels.
--
--   @param centerPercent Center as percentage (0-100)
--   @param dimension Image dimension (width or height)
--   @return Center in pixels
centerToPixels :: Double -> Int -> Double
centerToPixels centerPercent dimension =
  (centerPercent / 100.0) * fromIntegral dimension

-- | Convert normalized center (0-1) to pixels.
--
--   @param centerNorm Normalized center (0-1)
--   @param dimension Image dimension
--   @return Center in pixels
normalizedCenterToPixels :: Double -> Int -> Double
normalizedCenterToPixels centerNorm dimension =
  centerNorm * fromIntegral dimension

-- ────────────────────────────────────────────────────────────────────────────
-- Quality Settings
-- ────────────────────────────────────────────────────────────────────────────

-- | Get sample count from quality setting.
--
--   @param quality "draft" | "good" | "best"
--   @return Number of samples
qualitySampleCount :: String -> Int
qualitySampleCount quality
  | quality == "best" = 32
  | quality == "good" = 16
  | otherwise = 8
