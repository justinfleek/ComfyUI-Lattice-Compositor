{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Services.LayerTime
Description : Layer time calculations
Copyright   : (c) Lattice, 2026
License     : MIT

Pure functions for time remapping:
- Time stretch (percentage-based speed)
- Reversed playback (negative stretch)
- Loop and ping-pong modes
- Source time from composition time

Source: ui/src/services/layerTime.ts
-}

module Lattice.Services.LayerTime
  ( -- * Types
    SourceTimeResult(..)
  , SourceTimeOptions(..)
  , defaultSourceTimeOptions
    -- * Constants
  , normalStretch, defaultFps
    -- * Stretch Functions
  , effectiveSpeedFromStretch
  , isStretchReversed, reverseStretch
  , getStretchedDuration, getSourceDuration
    -- * Loop/Clamp Functions
  , loopFrame, pingPongFrame, clampFrame
    -- * Source Time Calculation
  , getSourceTime, getSourceFrame
  , isLayerVisibleAtFrame
    -- * Stretch Anchor Calculations
  , stretchFromStart, stretchFromEnd
  , stretchFromCenter, stretchFromFrame
    -- * Helpers
  , safeTimeStretch, safeFps, safeMod
  ) where

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Result of source time calculation
data SourceTimeResult = SourceTimeResult
  { sourceTime      :: Double      -- ^ Source time in seconds
  , sourceFrame     :: Int         -- ^ Source frame number
  , effectiveSpeed  :: Double      -- ^ Effective playback speed
  , isReversed      :: Bool        -- ^ Whether playback is reversed
  , wasAdjusted     :: Bool        -- ^ Whether source time was clamped/looped
  } deriving (Show, Eq)

-- | Options for source time calculation
data SourceTimeOptions = SourceTimeOptions
  { optFps            :: Double        -- ^ Composition frame rate
  , optSourceDuration :: Maybe Double  -- ^ Source duration in frames
  , optLoop           :: Bool          -- ^ Loop playback
  , optPingPong       :: Bool          -- ^ Ping-pong loop
  } deriving (Show, Eq)

-- | Default source time options
defaultSourceTimeOptions :: SourceTimeOptions
defaultSourceTimeOptions = SourceTimeOptions
  { optFps = defaultFps
  , optSourceDuration = Nothing
  , optLoop = False
  , optPingPong = False
  }

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Normal time stretch (100%)
normalStretch :: Double
normalStretch = 100.0

-- | Default FPS
defaultFps :: Double
defaultFps = 30.0

--------------------------------------------------------------------------------
-- Helper Functions
--------------------------------------------------------------------------------

-- | Ensure time stretch is valid
safeTimeStretch :: Double -> Double
safeTimeStretch stretch
  | isNaN stretch || isInfinite stretch = normalStretch
  | otherwise = stretch

-- | Ensure FPS is valid
safeFps :: Double -> Double
safeFps fps
  | isNaN fps || isInfinite fps || fps <= 0 = defaultFps
  | otherwise = fps

-- | Safe modulo for floats
safeMod :: Double -> Double -> Double
safeMod a b
  | b == 0 = a
  | otherwise = a - b * fromIntegral (floor (a / b) :: Int)

--------------------------------------------------------------------------------
-- Core Functions
--------------------------------------------------------------------------------

-- | Calculate effective speed from time stretch percentage.
-- 100% = 1x speed, 200% = 0.5x speed (slower), 50% = 2x speed (faster)
effectiveSpeedFromStretch :: Double -> Double
effectiveSpeedFromStretch timeStretch =
  let safe = safeTimeStretch timeStretch
  in if safe == 0 then 0 else normalStretch / safe

-- | Check if time stretch indicates reversed playback
isStretchReversed :: Double -> Bool
isStretchReversed timeStretch = safeTimeStretch timeStretch < 0

-- | Reverse a time stretch value (toggle playback direction)
reverseStretch :: Double -> Double
reverseStretch timeStretch = negate (safeTimeStretch timeStretch)

-- | Calculate stretched duration from source duration and time stretch.
-- 100% stretch = same duration, 200% = 2x duration, 50% = 0.5x duration
getStretchedDuration :: Double -> Double -> Double
getStretchedDuration sourceDuration timeStretch =
  let safe = safeTimeStretch timeStretch
  in if safe == 0 then sourceDuration
     else (sourceDuration * abs safe) / normalStretch

-- | Calculate original source duration from stretched duration
getSourceDuration :: Double -> Double -> Double
getSourceDuration stretchedDuration timeStretch =
  let safe = safeTimeStretch timeStretch
  in if safe == 0 then stretchedDuration
     else (stretchedDuration * normalStretch) / abs safe

--------------------------------------------------------------------------------
-- Loop/Clamp Functions
--------------------------------------------------------------------------------

-- | Apply simple loop to source frame
loopFrame :: Double -> Double -> (Double, Bool)
loopFrame sourceFrameVal sourceDuration
  | sourceDuration <= 0 = (sourceFrameVal, False)
  | otherwise =
      let adjusted = safeMod (safeMod sourceFrameVal sourceDuration + sourceDuration) sourceDuration
      in (adjusted, adjusted /= sourceFrameVal)

-- | Apply ping-pong loop to source frame
pingPongFrame :: Double -> Double -> (Double, Bool)
pingPongFrame sourceFrameVal sourceDuration
  | sourceDuration <= 0 = (sourceFrameVal, False)
  | otherwise =
      let cycles = fromIntegral (floor (sourceFrameVal / sourceDuration) :: Int)
          phase = safeMod sourceFrameVal sourceDuration
          cyclesInt = floor (sourceFrameVal / sourceDuration) :: Int
          adjusted
            | phase < 0 = sourceDuration + phase
            | cyclesInt `mod` 2 == 1 = sourceDuration - 1 - phase
            | otherwise = phase
      in (adjusted, cycles /= 0)

-- | Clamp source frame to valid range
clampFrame :: Double -> Double -> (Double, Bool)
clampFrame sourceFrameVal sourceDuration
  | sourceDuration <= 0 = (sourceFrameVal, False)
  | otherwise =
      let adjusted = max 0 (min sourceFrameVal (sourceDuration - 1))
      in (adjusted, adjusted /= sourceFrameVal)

--------------------------------------------------------------------------------
-- Source Time Calculation
--------------------------------------------------------------------------------

-- | Calculate source time from composition frame.
getSourceTime :: Double             -- ^ compFrame
              -> Double             -- ^ layerStartFrame
              -> Double             -- ^ timeStretch
              -> SourceTimeOptions  -- ^ options
              -> SourceTimeResult
getSourceTime compFrame layerStartFrame timeStretch options =
  let fps = safeFps (optFps options)
      stretch = safeTimeStretch timeStretch
      effSpeed = effectiveSpeedFromStretch stretch
      reversed = stretch < 0
      absSpeed = abs effSpeed

      -- Calculate time relative to layer start
      layerFrame = compFrame - layerStartFrame

      -- Apply time stretch to get source frame
      sourceFrameBase = layerFrame * absSpeed

      -- Handle reversed playback
      sourceFrameReversed = case optSourceDuration options of
        Just dur | reversed -> dur - 1 - sourceFrameBase
        _ -> sourceFrameBase

      -- Handle looping/clamping
      (sourceFrameLooped, adjusted) = case optSourceDuration options of
        Just dur | dur > 0 ->
          if optLoop options
          then if optPingPong options
               then pingPongFrame sourceFrameReversed dur
               else loopFrame sourceFrameReversed dur
          else clampFrame sourceFrameReversed dur
        _ -> (sourceFrameReversed, False)

      -- Ensure non-negative
      finalFrame = max 0 sourceFrameLooped

  in SourceTimeResult
    { sourceTime = finalFrame / fps
    , sourceFrame = round finalFrame
    , effectiveSpeed = effSpeed
    , isReversed = reversed
    , wasAdjusted = adjusted
    }

-- | Check if layer is visible at a given composition frame
isLayerVisibleAtFrame :: Double -> Double -> Double -> Bool
isLayerVisibleAtFrame compFrame startFrame endFrame =
  compFrame >= startFrame && compFrame <= endFrame

-- | Get just the source frame number (convenience function)
getSourceFrame :: Double         -- ^ compFrame
               -> Double         -- ^ layerStartFrame
               -> Double         -- ^ timeStretch
               -> Double         -- ^ fps
               -> Maybe Double   -- ^ sourceDuration
               -> Int
getSourceFrame compFrame layerStartFrame timeStretch fps sourceDuration =
  let options = defaultSourceTimeOptions
        { optFps = fps
        , optSourceDuration = sourceDuration
        }
      result = getSourceTime compFrame layerStartFrame timeStretch options
  in sourceFrame result

--------------------------------------------------------------------------------
-- Stretch Anchor Calculations
--------------------------------------------------------------------------------

-- | Calculate new endpoints after time stretch, anchored at start
stretchFromStart :: Double -> Double -> Double -> Double -> (Double, Double)
stretchFromStart startFrame currentDuration currentStretch newStretch =
  let sourceDuration = getSourceDuration currentDuration currentStretch
      newDuration = getStretchedDuration sourceDuration newStretch
  in (startFrame, startFrame + newDuration)

-- | Calculate new endpoints after time stretch, anchored at end
stretchFromEnd :: Double -> Double -> Double -> Double -> (Double, Double)
stretchFromEnd endFrame currentDuration currentStretch newStretch =
  let sourceDuration = getSourceDuration currentDuration currentStretch
      newDuration = getStretchedDuration sourceDuration newStretch
  in (endFrame - newDuration, endFrame)

-- | Calculate new endpoints after time stretch, anchored at center
stretchFromCenter :: Double -> Double -> Double -> Double -> Double -> (Double, Double)
stretchFromCenter startFrame endFrame currentDuration currentStretch newStretch =
  let center = (startFrame + endFrame) / 2
      sourceDuration = getSourceDuration currentDuration currentStretch
      newDuration = getStretchedDuration sourceDuration newStretch
      newStart = fromIntegral (floor (center - newDuration / 2) :: Int)
  in (newStart, newStart + newDuration)

-- | Calculate new endpoints after time stretch, anchored at specific frame
stretchFromFrame :: Double -> Double -> Double -> Double -> Double -> (Double, Double)
stretchFromFrame startFrame currentDuration currentStretch newStretch anchorFrame =
  let sourceDuration = getSourceDuration currentDuration currentStretch
      newDuration = getStretchedDuration sourceDuration newStretch
      ratio = if currentDuration == 0 then 0 else (anchorFrame - startFrame) / currentDuration
      newStart = fromIntegral (floor (anchorFrame - ratio * newDuration) :: Int)
  in (newStart, newStart + newDuration)
