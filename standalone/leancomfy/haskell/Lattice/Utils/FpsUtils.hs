{-# LANGUAGE StrictData #-}

{-|
Module      : Lattice.Utils.FpsUtils
Description : Frame rate utilities
Copyright   : (c) Lattice, 2026
License     : MIT

Validation and helper functions for frame rate handling.
Ensures fps values are valid to prevent division by zero.

Source: leancomfy/lean/Lattice/Utils/FpsUtils.lean
-}

module Lattice.Utils.FpsUtils
  ( -- * Constants
    defaultFps
  , minFps
  , maxFps
    -- * FPS Type
  , Fps(..)
  , mkFps
  , fpsDefault
    -- * Validation
  , validateFps
  , validateFpsInt
    -- * Safe Operations
  , safeDivideByFps
  , frameToTime
  , timeToFrame
  , calculateDuration
  , calculateFrameCount
    -- * Assertions
  , assertValidFps
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Default fps for Lattice Compositor (WAN model standard)
defaultFps :: Int
defaultFps = 16

-- | Minimum allowed fps value
minFps :: Int
minFps = 1

-- | Maximum allowed fps value
maxFps :: Int
maxFps = 120

--------------------------------------------------------------------------------
-- FPS Type
--------------------------------------------------------------------------------

-- | Validated FPS value (positive, within range)
newtype Fps = Fps { unFps :: Int }
  deriving (Eq, Show)

-- | Create FPS from Int, clamping to valid range
mkFps :: Int -> Fps
mkFps n
  | n <= 0 = Fps defaultFps
  | otherwise = Fps (max minFps (min maxFps n))

-- | Default FPS instance
fpsDefault :: Fps
fpsDefault = Fps defaultFps

--------------------------------------------------------------------------------
-- Helper
--------------------------------------------------------------------------------

-- | Check if Double is finite
isFiniteDouble :: Double -> Bool
isFiniteDouble x = not (isNaN x) && not (isInfinite x)

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Validate fps value, returning fallback if invalid
validateFps :: Maybe Double -> Fps -> Fps
validateFps Nothing fallback = fallback
validateFps (Just f) fallback
  | not (isFiniteDouble f) || f <= 0 = fallback
  | otherwise = mkFps (round f)

-- | Validate fps from Int
validateFpsInt :: Int -> Fps -> Fps
validateFpsInt n fallback
  | n <= 0 = fallback
  | otherwise = mkFps n

--------------------------------------------------------------------------------
-- Safe Operations
--------------------------------------------------------------------------------

-- | Safely divide by fps
safeDivideByFps :: Double -> Fps -> Double
safeDivideByFps numerator (Fps fps) = numerator / fromIntegral fps

-- | Convert frame number to time in seconds
frameToTime :: FrameNumber -> Fps -> FiniteFloat
frameToTime (FrameNumber frame) (Fps fps) =
  let result = fromIntegral frame / fromIntegral fps
  in if isFiniteDouble result
     then FiniteFloat result
     else FiniteFloat 0

-- | Convert time in seconds to frame number
timeToFrame :: FiniteFloat -> Fps -> FrameNumber
timeToFrame (FiniteFloat time) (Fps fps) =
  let result = time * fromIntegral fps
  in if result < 0
     then FrameNumber 0
     else FrameNumber (max 0 (round result))

-- | Calculate duration in seconds from frame count
calculateDuration :: Int -> Fps -> FiniteFloat
calculateDuration frameCount (Fps fps) =
  let result = fromIntegral frameCount / fromIntegral fps
  in if isFiniteDouble result
     then FiniteFloat result
     else FiniteFloat 0

-- | Calculate frame count from duration (ceiling)
calculateFrameCount :: FiniteFloat -> Fps -> Int
calculateFrameCount (FiniteFloat duration) (Fps fps) =
  ceiling (duration * fromIntegral fps)

--------------------------------------------------------------------------------
-- Assertions
--------------------------------------------------------------------------------

-- | Assert fps is valid
assertValidFps :: Maybe Double -> Maybe Text -> Either Text Fps
assertValidFps Nothing context =
  let ctx = maybe "" (" in " <>) context
  in Left $ "Invalid fps value" <> ctx <> ": Nothing. FPS must be a positive number."
assertValidFps (Just f) context
  | not (isFiniteDouble f) || f <= 0 =
      let ctx = maybe "" (" in " <>) context
      in Left $ "Invalid fps value" <> ctx <> ": " <> T.pack (show f) <> ". FPS must be a positive number."
  | otherwise = Right $ validateFps (Just f) fpsDefault
