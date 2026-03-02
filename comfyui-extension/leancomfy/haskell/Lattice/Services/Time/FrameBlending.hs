{-|
{-# LANGUAGE OverloadedStrings #-}
  Lattice.Services.Time.FrameBlending - Frame Interpolation Math

  Pure mathematical functions for time-based frame blending:
  - Whole-frame selection (nearest)
  - Frame mix (cross-fade)
  - Echo intensity decay

  Source: ui/src/services/effects/timeRenderer.ts (lines 746-808, 313-316)
-}

module Lattice.Services.Time.FrameBlending
  ( -- * Timewarp Methods
    TimewarpMethod(..)
    -- * Whole Frame Selection
  , selectWholeFrame
    -- * Frame Mix
  , mixPixelValue
  , mixPixelRGBA
    -- * Echo Decay
  , echoIntensity
  , isSignificantEcho
    -- * Posterize Time
  , posterizedFrame
  , isNewPosterizedFrame
    -- * Motion Blur
  , motionBlurFactor
  , adjustedBlendForMotion
    -- * Blending Decision
  , needsBlending
  ) where

--------------------------------------------------------------------------------
-- Timewarp Methods
--------------------------------------------------------------------------------

-- | Timewarp interpolation method.
data TimewarpMethod
  = WholeFrames   -- ^ Nearest frame, no interpolation
  | FrameMix      -- ^ Cross-fade between frames
  | PixelMotion   -- ^ Optical flow-based
  deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Whole Frame Selection
--------------------------------------------------------------------------------

-- | Select which frame to use based on blend factor.
--   Returns True if frame1 should be used, False for frame2.
selectWholeFrame :: Double  -- ^ Blend factor (0-1)
                 -> Bool
selectWholeFrame blendFactor = blendFactor < 0.5

--------------------------------------------------------------------------------
-- Frame Mix (Cross-fade)
--------------------------------------------------------------------------------

-- | Calculate blended pixel value using linear interpolation.
--   frame1Value * (1 - blend) + frame2Value * blend
mixPixelValue :: Double  -- ^ Frame 1 value
              -> Double  -- ^ Frame 2 value
              -> Double  -- ^ Blend factor (0-1)
              -> Double
mixPixelValue frame1Value frame2Value blend =
  frame1Value * (1.0 - blend) + frame2Value * blend

-- | Blend RGBA pixel values.
--   Returns (r, g, b, a) blended result.
mixPixelRGBA :: Double -> Double -> Double -> Double  -- ^ RGBA 1
             -> Double -> Double -> Double -> Double  -- ^ RGBA 2
             -> Double                                -- ^ Blend
             -> (Double, Double, Double, Double)
mixPixelRGBA r1 g1 b1 a1 r2 g2 b2 a2 blend =
  ( mixPixelValue r1 r2 blend
  , mixPixelValue g1 g2 blend
  , mixPixelValue b1 b2 blend
  , mixPixelValue a1 a2 blend
  )

--------------------------------------------------------------------------------
-- Echo Intensity Decay
--------------------------------------------------------------------------------

-- | Calculate echo intensity at a given echo index.
--   Uses exponential decay: startingIntensity * (1 - decay)^echoIndex
echoIntensity :: Double  -- ^ Starting intensity (0-1)
              -> Double  -- ^ Decay rate (0-1)
              -> Int     -- ^ Echo index (0-based)
              -> Double
echoIntensity startingIntensity decay echoIndex =
  startingIntensity * ((1.0 - decay) ** fromIntegral echoIndex)

-- | Check if echo intensity is significant enough to render.
--   Returns True if intensity > 0.001
isSignificantEcho :: Double -> Bool
isSignificantEcho intensity = intensity > 0.001

--------------------------------------------------------------------------------
-- Posterize Time
--------------------------------------------------------------------------------

-- | Calculate the posterized frame number.
--   Quantizes time to target frame rate.
posterizedFrame :: Int     -- ^ Current frame
                -> Double  -- ^ Source FPS
                -> Double  -- ^ Target FPS
                -> Int
posterizedFrame currentFrame sourceFps targetFps
  | targetFps <= 0.0 || sourceFps <= 0.0 = currentFrame
  | otherwise =
      let frameRatio = sourceFps / targetFps
          quantized = fromIntegral (floor (fromIntegral currentFrame / frameRatio)) * frameRatio
      in round quantized

-- | Check if current frame is a "new" posterized frame.
--   Returns True if frame is close to its posterized value.
isNewPosterizedFrame :: Int -> Double -> Double -> Bool
isNewPosterizedFrame currentFrame sourceFps targetFps =
  let posterized = posterizedFrame currentFrame sourceFps targetFps
      diff = abs (currentFrame - posterized)
  in fromIntegral diff < 0.5

--------------------------------------------------------------------------------
-- Motion Blur Adjustment
--------------------------------------------------------------------------------

-- | Calculate motion blur factor from motion vector magnitude.
--   motionBlurAmount: base blur amount (0-1)
--   motionMagnitude: length of motion vector
motionBlurFactor :: Double  -- ^ Motion blur amount (0-1)
                 -> Double  -- ^ Motion magnitude
                 -> Double
motionBlurFactor motionBlurAmount motionMagnitude =
  min 1.0 (motionBlurAmount * motionMagnitude / 10.0)

-- | Adjust blend factor for motion blur.
--   Reduces blend when there's significant motion.
adjustedBlendForMotion :: Double  -- ^ Original blend
                       -> Double  -- ^ Blur factor
                       -> Double
adjustedBlendForMotion blend blurFactor =
  blend * (1.0 - blurFactor * 0.5)

--------------------------------------------------------------------------------
-- Frame Blending Decision
--------------------------------------------------------------------------------

-- | Determine if blending is needed based on blend factor.
--   Returns Nothing if exact frame (0 or 1), Just blend otherwise.
needsBlending :: Double -> Maybe Double
needsBlending blendFactor
  | blendFactor == 0.0 || blendFactor == 1.0 = Nothing
  | otherwise = Just blendFactor
