-- | Lattice.Utils.FpsUtils - Frame rate utilities
-- |
-- | Validation and helper functions for frame rate handling.
-- | Ensures fps values are valid to prevent division by zero.
-- |
-- | Source: leancomfy/lean/Lattice/Utils/FpsUtils.lean

module Lattice.Utils.FpsUtils
  ( defaultFps
  , minFps
  , maxFps
  , Fps
  , mkFps
  , unFps
  , fpsDefault
  , validateFps
  , validateFpsInt
  , safeDivideByFps
  , frameToTime
  , timeToFrame
  , calculateDuration
  , calculateFrameCount
  , assertValidFps
  ) where

import Prelude
import Data.Either (Either(..))
import Data.Int (ceil, round, toNumber)
import Data.Maybe (Maybe(..))
import Data.Number (isFinite) as Number
import Lattice.Primitives (FiniteFloat(..), FrameNumber(..), unFiniteFloat)

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
newtype Fps = Fps Int

derive instance Eq Fps

instance Show Fps where
  show (Fps n) = "Fps " <> show n

-- | Extract Int from Fps
unFps :: Fps -> Int
unFps (Fps n) = n

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

-- | Check if Number is finite
isFiniteNumber :: Number -> Boolean
isFiniteNumber = Number.isFinite

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Validate fps value, returning fallback if invalid
validateFps :: Maybe Number -> Fps -> Fps
validateFps Nothing fallback = fallback
validateFps (Just f) fallback
  | not (isFiniteNumber f) || f <= 0.0 = fallback
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
safeDivideByFps :: Number -> Fps -> Number
safeDivideByFps numerator (Fps fps) = numerator / toNumber fps

-- | Convert frame number to time in seconds
frameToTime :: FrameNumber -> Fps -> FiniteFloat
frameToTime (FrameNumber frame) (Fps fps) =
  let result = toNumber frame / toNumber fps
  in FiniteFloat (if isFiniteNumber result then result else 0.0)

-- | Convert time in seconds to frame number
timeToFrame :: FiniteFloat -> Fps -> FrameNumber
timeToFrame time (Fps fps) =
  let result = unFiniteFloat time * toNumber fps
  in FrameNumber (if result < 0.0 then 0 else max 0 (round result))

-- | Calculate duration in seconds from frame count
calculateDuration :: Int -> Fps -> FiniteFloat
calculateDuration frameCount (Fps fps) =
  let result = toNumber frameCount / toNumber fps
  in FiniteFloat (if isFiniteNumber result then result else 0.0)

-- | Calculate frame count from duration (ceiling)
calculateFrameCount :: FiniteFloat -> Fps -> Int
calculateFrameCount duration (Fps fps) =
  ceil (unFiniteFloat duration * toNumber fps)

--------------------------------------------------------------------------------
-- Assertions
--------------------------------------------------------------------------------

-- | Assert fps is valid
assertValidFps :: Maybe Number -> Maybe String -> Either String Fps
assertValidFps Nothing context =
  let ctx = case context of
        Nothing -> ""
        Just c -> " in " <> c
  in Left $ "Invalid fps value" <> ctx <> ": Nothing. FPS must be a positive number."
assertValidFps (Just f) context
  | not (isFiniteNumber f) || f <= 0.0 =
      let ctx = case context of
            Nothing -> ""
            Just c -> " in " <> c
      in Left $ "Invalid fps value" <> ctx <> ": " <> show f <> ". FPS must be a positive number."
  | otherwise = Right $ validateFps (Just f) fpsDefault
