{-
  Lattice.Services.Time.PosterizeTime - Frame Rate Reduction

  Pure functions for posterize time effect:
  - Target frame rate conversion
  - Posterized frame calculation
  - Frame holding logic

  Source: ui/src/services/effects/timeRenderer.ts (lines 390-449)
-}

module Lattice.Services.Time.PosterizeTime
  ( -- * Parameter Validation
    validateTargetFps
  , defaultTargetFps
    -- * Posterize Calculation
  , calculateFrameRatio
  , calculatePosterizedFrame
  , shouldUseCurrent
  , nearFrameThreshold
  ) where

import Prelude

import Data.Int (floor, toNumber)
import Math (abs, round)

--------------------------------------------------------------------------------
-- Parameter Validation
--------------------------------------------------------------------------------

-- | Default target frame rate for posterize effect.
defaultTargetFps :: Number
defaultTargetFps = 12.0

-- | Validate and clamp target fps to [1, 60].
validateTargetFps :: Number -> Number
validateTargetFps fps = max 1.0 (min 60.0 fps)

--------------------------------------------------------------------------------
-- Posterize Calculation
--------------------------------------------------------------------------------

-- | Calculate frame ratio: source fps / target fps.
calculateFrameRatio :: Number -> Number -> Number
calculateFrameRatio sourceFps targetFps = sourceFps / targetFps

-- | Calculate the "posterized" frame number.
--   Rounds down to nearest posterized frame boundary.
calculatePosterizedFrame :: Int -> Number -> Int
calculatePosterizedFrame currentFrame frameRatio =
  let current = toNumber currentFrame
      posterized = toNumber (floor (current / frameRatio)) * frameRatio
  in floor posterized

-- | Threshold for determining if current frame is "close enough" to posterized.
nearFrameThreshold :: Number
nearFrameThreshold = 0.5

-- | Check if current frame should be used (vs held frame).
--   Returns true if current frame is within threshold of posterized frame.
shouldUseCurrent :: Int -> Int -> Boolean
shouldUseCurrent currentFrame posterizedFrame =
  abs (toNumber currentFrame - toNumber posterizedFrame) < nearFrameThreshold
