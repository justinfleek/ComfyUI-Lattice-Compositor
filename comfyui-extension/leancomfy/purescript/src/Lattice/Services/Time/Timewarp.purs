{-
  Lattice.Services.Time.Timewarp - Frame Blending for Timewarp

  Pure functions for timewarp frame interpolation:
  - Interpolation method selection
  - Blend factor calculations
  - Motion blur adjustment

  Source: ui/src/services/effects/timeRenderer.ts (lines 724-807)
-}

module Lattice.Services.Time.Timewarp
  ( TimewarpMethod(..)
  , parseTimewarpMethod
  -- * Blend Calculations
  , isExactFrame
  , selectNearestFrame
  -- * Frame Mix (Cross-fade)
  , frameMixPixel
  -- * Motion Blur Adjustment
  , defaultMotionBlur
  , calculateAdjustedBlend
  ) where

import Prelude

import Data.Int (toNumber, round)
import Math (sqrt)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Timewarp interpolation methods.
data TimewarpMethod
  = WholeFrames    -- Nearest frame, no interpolation
  | FrameMix       -- Simple cross-fade between frames
  | PixelMotion    -- Optical flow-based interpolation

derive instance eqTimewarpMethod :: Eq TimewarpMethod

instance showTimewarpMethod :: Show TimewarpMethod where
  show WholeFrames = "whole-frames"
  show FrameMix = "frame-mix"
  show PixelMotion = "pixel-motion"

-- | Parse timewarp method from string.
parseTimewarpMethod :: String -> TimewarpMethod
parseTimewarpMethod s = case s of
  "whole-frames" -> WholeFrames
  "frame-mix" -> FrameMix
  "pixel-motion" -> PixelMotion
  _ -> WholeFrames  -- Default

--------------------------------------------------------------------------------
-- Blend Calculations
--------------------------------------------------------------------------------

-- | Check if blend factor indicates exact frame (no interpolation needed).
isExactFrame :: Number -> Boolean
isExactFrame blend = blend == 0.0 || blend == 1.0

-- | Select nearest frame for whole-frames mode.
--   Returns 1 if blend >= 0.5 (use frame2), 0 otherwise (use frame1).
selectNearestFrame :: Number -> Int
selectNearestFrame blend = if blend < 0.5 then 0 else 1

--------------------------------------------------------------------------------
-- Frame Mix (Cross-fade)
--------------------------------------------------------------------------------

-- | Mix single pixel channel between two frames.
--   result = src1 * (1 - blend) + src2 * blend
frameMixPixel :: Number -> Number -> Number -> Number
frameMixPixel src1 src2 blend = src1 * (1.0 - blend) + src2 * blend

--------------------------------------------------------------------------------
-- Motion Blur Adjustment
--------------------------------------------------------------------------------

-- | Default motion blur amount.
defaultMotionBlur :: Number
defaultMotionBlur = 0.5

-- | Calculate adjusted blend factor considering motion blur.
--   Reduces blend near motion vector areas.
calculateAdjustedBlend :: Number -> Number -> Number -> Number -> Number
calculateAdjustedBlend blend motionBlurAmount mvX mvY =
  let magnitude = sqrt (mvX * mvX + mvY * mvY)
      blurFactor = min 1.0 (motionBlurAmount * magnitude / 10.0)
  in blend * (1.0 - blurFactor * 0.5)
