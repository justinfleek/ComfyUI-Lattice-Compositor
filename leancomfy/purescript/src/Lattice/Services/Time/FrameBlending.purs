{-
  Lattice.Services.Time.FrameBlending - Frame Interpolation Math

  Pure mathematical functions for time-based frame blending:
  - Whole-frame selection (nearest)
  - Frame mix (cross-fade)
  - Echo intensity decay

  Source: ui/src/services/effects/timeRenderer.ts (lines 746-808, 313-316)
-}

module Lattice.Services.Time.FrameBlending
  ( TimewarpMethod(..)
  , selectWholeFrame
  , mixPixelValue
  , mixPixelRGBA
  , echoIntensity
  , isSignificantEcho
  , posterizedFrame
  , isNewPosterizedFrame
  , motionBlurFactor
  , adjustedBlendForMotion
  , needsBlending
  ) where

import Prelude

import Data.Int (round, toNumber)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Math (abs, floor, min, pow)

--------------------------------------------------------------------------------
-- Timewarp Methods
--------------------------------------------------------------------------------

-- | Timewarp interpolation method.
data TimewarpMethod
  = WholeFrames   -- Nearest frame
  | FrameMix      -- Cross-fade
  | PixelMotion   -- Optical flow

derive instance eqTimewarpMethod :: Eq TimewarpMethod

--------------------------------------------------------------------------------
-- Whole Frame Selection
--------------------------------------------------------------------------------

-- | Select which frame to use based on blend factor.
selectWholeFrame :: Number -> Boolean
selectWholeFrame blendFactor = blendFactor < 0.5

--------------------------------------------------------------------------------
-- Frame Mix (Cross-fade)
--------------------------------------------------------------------------------

-- | Calculate blended pixel value.
mixPixelValue :: Number -> Number -> Number -> Number
mixPixelValue frame1Value frame2Value blend =
  frame1Value * (1.0 - blend) + frame2Value * blend

-- | Blend RGBA pixel values.
mixPixelRGBA :: Number -> Number -> Number -> Number
            -> Number -> Number -> Number -> Number
            -> Number
            -> Tuple Number (Tuple Number (Tuple Number Number))
mixPixelRGBA r1 g1 b1 a1 r2 g2 b2 a2 blend =
  Tuple (mixPixelValue r1 r2 blend)
    (Tuple (mixPixelValue g1 g2 blend)
      (Tuple (mixPixelValue b1 b2 blend)
        (mixPixelValue a1 a2 blend)))

--------------------------------------------------------------------------------
-- Echo Intensity Decay
--------------------------------------------------------------------------------

-- | Calculate echo intensity at a given echo index.
echoIntensity :: Number -> Number -> Int -> Number
echoIntensity startingIntensity decay echoIndex =
  startingIntensity * pow (1.0 - decay) (toNumber echoIndex)

-- | Check if echo intensity is significant enough to render.
isSignificantEcho :: Number -> Boolean
isSignificantEcho intensity = intensity > 0.001

--------------------------------------------------------------------------------
-- Posterize Time
--------------------------------------------------------------------------------

-- | Calculate the posterized frame number.
posterizedFrame :: Int -> Number -> Number -> Int
posterizedFrame currentFrame sourceFps targetFps
  | targetFps <= 0.0 || sourceFps <= 0.0 = currentFrame
  | otherwise =
      let frameRatio = sourceFps / targetFps
          quantized = floor (toNumber currentFrame / frameRatio) * frameRatio
      in round quantized

-- | Check if current frame is a "new" posterized frame.
isNewPosterizedFrame :: Int -> Number -> Number -> Boolean
isNewPosterizedFrame currentFrame sourceFps targetFps =
  let posterized = posterizedFrame currentFrame sourceFps targetFps
      diff = abs (toNumber currentFrame - toNumber posterized)
  in diff < 0.5

--------------------------------------------------------------------------------
-- Motion Blur Adjustment
--------------------------------------------------------------------------------

-- | Calculate motion blur factor from motion vector magnitude.
motionBlurFactor :: Number -> Number -> Number
motionBlurFactor motionBlurAmount motionMagnitude =
  min 1.0 (motionBlurAmount * motionMagnitude / 10.0)

-- | Adjust blend factor for motion blur.
adjustedBlendForMotion :: Number -> Number -> Number
adjustedBlendForMotion blend blurFactor =
  blend * (1.0 - blurFactor * 0.5)

--------------------------------------------------------------------------------
-- Frame Blending Decision
--------------------------------------------------------------------------------

-- | Determine if blending is needed based on blend factor.
needsBlending :: Number -> Maybe Number
needsBlending blendFactor
  | blendFactor == 0.0 || blendFactor == 1.0 = Nothing
  | otherwise = Just blendFactor
