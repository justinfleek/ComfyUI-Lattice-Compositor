-- | Lattice.Services.LayerTime - Layer time calculations
-- |
-- | Pure functions for time remapping:
-- | - Time stretch (percentage-based speed)
-- | - Reversed playback (negative stretch)
-- | - Loop and ping-pong modes
-- | - Source time from composition time
-- |
-- | Source: ui/src/services/layerTime.ts

module Lattice.Services.LayerTime
  ( -- * Types
    SourceTimeResult
  , SourceTimeOptions
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

import Prelude
import Data.Int (floor, round, toNumber)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Global (isNaN, isFinite) as Global
import Math (abs) as Math

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Result of source time calculation
type SourceTimeResult =
  { sourceTime :: Number      -- ^ Source time in seconds
  , sourceFrame :: Int        -- ^ Source frame number
  , effectiveSpeed :: Number  -- ^ Effective playback speed
  , isReversed :: Boolean     -- ^ Whether playback is reversed
  , wasAdjusted :: Boolean    -- ^ Whether source time was clamped/looped
  }

-- | Options for source time calculation
type SourceTimeOptions =
  { fps :: Number               -- ^ Composition frame rate
  , sourceDuration :: Maybe Number  -- ^ Source duration in frames
  , loop :: Boolean             -- ^ Loop playback
  , pingPong :: Boolean         -- ^ Ping-pong loop
  }

-- | Default source time options
defaultSourceTimeOptions :: SourceTimeOptions
defaultSourceTimeOptions =
  { fps: defaultFps
  , sourceDuration: Nothing
  , loop: false
  , pingPong: false
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

-- | Normal time stretch (100%)
normalStretch :: Number
normalStretch = 100.0

-- | Default FPS
defaultFps :: Number
defaultFps = 30.0

-- ────────────────────────────────────────────────────────────────────────────
-- Helper Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if finite
isFiniteNum :: Number -> Boolean
isFiniteNum x = Global.isFinite x && not (Global.isNaN x)

-- | Ensure time stretch is valid
safeTimeStretch :: Number -> Number
safeTimeStretch stretch =
  if isFiniteNum stretch then stretch else normalStretch

-- | Ensure FPS is valid
safeFps :: Number -> Number
safeFps fps =
  if isFiniteNum fps && fps > 0.0 then fps else defaultFps

-- | Safe modulo for floats
safeMod :: Number -> Number -> Number
safeMod a b =
  if b == 0.0 then a
  else a - b * toNumber (floor (a / b))

-- ────────────────────────────────────────────────────────────────────────────
-- Core Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate effective speed from time stretch percentage.
-- | 100% = 1x speed, 200% = 0.5x speed (slower), 50% = 2x speed (faster)
effectiveSpeedFromStretch :: Number -> Number
effectiveSpeedFromStretch timeStretch =
  let safe = safeTimeStretch timeStretch
  in if safe == 0.0 then 0.0 else normalStretch / safe

-- | Check if time stretch indicates reversed playback
isStretchReversed :: Number -> Boolean
isStretchReversed timeStretch = safeTimeStretch timeStretch < 0.0

-- | Reverse a time stretch value (toggle playback direction)
reverseStretch :: Number -> Number
reverseStretch timeStretch = negate (safeTimeStretch timeStretch)

-- | Calculate stretched duration from source duration and time stretch.
-- | 100% stretch = same duration, 200% = 2x duration, 50% = 0.5x duration
getStretchedDuration :: Number -> Number -> Number
getStretchedDuration sourceDuration timeStretch =
  let safe = safeTimeStretch timeStretch
  in if safe == 0.0 then sourceDuration
     else (sourceDuration * Math.abs safe) / normalStretch

-- | Calculate original source duration from stretched duration
getSourceDuration :: Number -> Number -> Number
getSourceDuration stretchedDuration timeStretch =
  let safe = safeTimeStretch timeStretch
  in if safe == 0.0 then stretchedDuration
     else (stretchedDuration * normalStretch) / Math.abs safe

-- ────────────────────────────────────────────────────────────────────────────
-- Loop/Clamp Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Apply simple loop to source frame
loopFrame :: Number -> Number -> Tuple Number Boolean
loopFrame sourceFrameVal sourceDuration
  | sourceDuration <= 0.0 = Tuple sourceFrameVal false
  | otherwise =
      let adjusted = safeMod (safeMod sourceFrameVal sourceDuration + sourceDuration) sourceDuration
      in Tuple adjusted (adjusted /= sourceFrameVal)

-- | Apply ping-pong loop to source frame
pingPongFrame :: Number -> Number -> Tuple Number Boolean
pingPongFrame sourceFrameVal sourceDuration
  | sourceDuration <= 0.0 = Tuple sourceFrameVal false
  | otherwise =
      let cycles = toNumber (floor (sourceFrameVal / sourceDuration))
          phase = safeMod sourceFrameVal sourceDuration
          cyclesInt = floor (sourceFrameVal / sourceDuration)
          adjusted =
            if phase < 0.0 then sourceDuration + phase
            else if cyclesInt `mod` 2 == 1 then sourceDuration - 1.0 - phase
            else phase
      in Tuple adjusted (cycles /= 0.0)

-- | Clamp source frame to valid range
clampFrame :: Number -> Number -> Tuple Number Boolean
clampFrame sourceFrameVal sourceDuration
  | sourceDuration <= 0.0 = Tuple sourceFrameVal false
  | otherwise =
      let adjusted = max 0.0 (min sourceFrameVal (sourceDuration - 1.0))
      in Tuple adjusted (adjusted /= sourceFrameVal)

-- ────────────────────────────────────────────────────────────────────────────
-- Source Time Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate source time from composition frame.
getSourceTime :: Number             -- ^ compFrame
              -> Number             -- ^ layerStartFrame
              -> Number             -- ^ timeStretch
              -> SourceTimeOptions  -- ^ options
              -> SourceTimeResult
getSourceTime compFrame layerStartFrame timeStretch options =
  let fps = safeFps options.fps
      stretch = safeTimeStretch timeStretch
      effSpeed = effectiveSpeedFromStretch stretch
      reversed = stretch < 0.0
      absSpeed = Math.abs effSpeed

      -- Calculate time relative to layer start
      layerFrame = compFrame - layerStartFrame

      -- Apply time stretch to get source frame
      sourceFrameBase = layerFrame * absSpeed

      -- Handle reversed playback
      sourceFrameReversed = case options.sourceDuration of
        Just dur | reversed -> dur - 1.0 - sourceFrameBase
        _ -> sourceFrameBase

      -- Handle looping/clamping
      Tuple sourceFrameLooped adjusted = case options.sourceDuration of
        Just dur | dur > 0.0 ->
          if options.loop
          then if options.pingPong
               then pingPongFrame sourceFrameReversed dur
               else loopFrame sourceFrameReversed dur
          else clampFrame sourceFrameReversed dur
        _ -> Tuple sourceFrameReversed false

      -- Ensure non-negative
      finalFrame = max 0.0 sourceFrameLooped

  in { sourceTime: finalFrame / fps
     , sourceFrame: round finalFrame
     , effectiveSpeed: effSpeed
     , isReversed: reversed
     , wasAdjusted: adjusted
     }

-- | Check if layer is visible at a given composition frame
isLayerVisibleAtFrame :: Number -> Number -> Number -> Boolean
isLayerVisibleAtFrame compFrame startFrame endFrame =
  compFrame >= startFrame && compFrame <= endFrame

-- | Get just the source frame number (convenience function)
getSourceFrame :: Number         -- ^ compFrame
               -> Number         -- ^ layerStartFrame
               -> Number         -- ^ timeStretch
               -> Number         -- ^ fps
               -> Maybe Number   -- ^ sourceDuration
               -> Int
getSourceFrame compFrame layerStartFrame timeStretch fps sourceDuration =
  let options = defaultSourceTimeOptions
        { fps = fps
        , sourceDuration = sourceDuration
        }
      result = getSourceTime compFrame layerStartFrame timeStretch options
  in result.sourceFrame

-- ────────────────────────────────────────────────────────────────────────────
-- Stretch Anchor Calculations
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate new endpoints after time stretch, anchored at start
stretchFromStart :: Number -> Number -> Number -> Number -> Tuple Number Number
stretchFromStart startFrame currentDuration currentStretch newStretch =
  let sourceDuration = getSourceDuration currentDuration currentStretch
      newDuration = getStretchedDuration sourceDuration newStretch
  in Tuple startFrame (startFrame + newDuration)

-- | Calculate new endpoints after time stretch, anchored at end
stretchFromEnd :: Number -> Number -> Number -> Number -> Tuple Number Number
stretchFromEnd endFrame currentDuration currentStretch newStretch =
  let sourceDuration = getSourceDuration currentDuration currentStretch
      newDuration = getStretchedDuration sourceDuration newStretch
  in Tuple (endFrame - newDuration) endFrame

-- | Calculate new endpoints after time stretch, anchored at center
stretchFromCenter :: Number -> Number -> Number -> Number -> Number -> Tuple Number Number
stretchFromCenter startFrame endFrame currentDuration currentStretch newStretch =
  let center = (startFrame + endFrame) / 2.0
      sourceDuration = getSourceDuration currentDuration currentStretch
      newDuration = getStretchedDuration sourceDuration newStretch
      newStart = toNumber (floor (center - newDuration / 2.0))
  in Tuple newStart (newStart + newDuration)

-- | Calculate new endpoints after time stretch, anchored at specific frame
stretchFromFrame :: Number -> Number -> Number -> Number -> Number -> Tuple Number Number
stretchFromFrame startFrame currentDuration currentStretch newStretch anchorFrame =
  let sourceDuration = getSourceDuration currentDuration currentStretch
      newDuration = getStretchedDuration sourceDuration newStretch
      ratio = if currentDuration == 0.0 then 0.0 else (anchorFrame - startFrame) / currentDuration
      newStart = toNumber (floor (anchorFrame - ratio * newDuration))
  in Tuple newStart (newStart + newDuration)
