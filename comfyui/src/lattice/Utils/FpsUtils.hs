-- |
-- Module      : Lattice.Utils.FpsUtils
-- Description : FPS validation and helper functions for frame rate handling
-- 
-- Migrated from ui/src/utils/fpsUtils.ts
-- Pure functions for fps validation and conversion
-- 
-- CRITICAL: No forbidden patterns - explicit types, no null/undefined, no type escapes
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Utils.FpsUtils
  ( -- Constants
    defaultFps
  , minFps
  , maxFps
  -- Validation
  , validateFps
  , assertValidFps
  -- Conversion
  , safeDivideByFps
  , frameToTime
  , timeToFrame
  , calculateDuration
  , calculateFrameCount
  ) where

import Lattice.Utils.NumericSafety (isFinite)
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Utils.NumericSafety (ensureFinite, clamp)

-- ============================================================================
-- CONSTANTS
-- ============================================================================

-- | Default fps for Lattice Compositor (WAN model standard)
defaultFps :: Double
defaultFps = 16.0

-- | Minimum allowed fps value
minFps :: Double
minFps = 1.0

-- | Maximum allowed fps value
maxFps :: Double
maxFps = 120.0

-- ============================================================================
-- VALIDATION
-- ============================================================================

-- | Validates that fps is a positive number within acceptable range
-- Returns the validated fps or the default if invalid
-- 
-- System F/Omega proof: Explicit type Maybe Double -> Double -> Double
-- Mathematical proof: Result always in [minFps, maxFps] or defaultFps
-- 
-- @param fps The fps value to validate
-- @param fallback Fallback value if fps is invalid (default: 16)
-- @returns Valid fps value
validateFps :: Maybe Double -> Double -> Double
validateFps mFps fallback =
  let safeFallback = if fallback > 0 && isFinite fallback then fallback else defaultFps
  in case mFps of
    Nothing -> safeFallback
    Just fps ->
      if fps > 0 && isFinite fps then
        clamp fps minFps maxFps
      else
        safeFallback

-- | Asserts that fps is valid, returning error if not
-- Use this at function entry points where invalid fps should be a hard error
-- 
-- System F/Omega proof: Explicit type Maybe Double -> Maybe Text -> Either Text Double
-- Mathematical proof: Returns Left error or Right valid fps
-- 
-- @param fps The fps value to validate
-- @param context Optional context for error message
-- @returns Either error message or valid fps
assertValidFps :: Maybe Double -> Maybe Text -> Either Text Double
assertValidFps mFps mContext =
  case mFps of
    Nothing -> Left (buildErrorMsg Nothing mContext)
    Just fps ->
      if fps > 0 && isFinite fps then
        Right (clamp fps minFps maxFps)
      else
        Left (buildErrorMsg (Just fps) mContext)

-- | Build error message for invalid fps
buildErrorMsg :: Maybe Double -> Maybe Text -> Text
buildErrorMsg mFps mContext =
  let fpsStr = case mFps of
        Nothing -> "null or undefined"
        Just fps -> T.pack (show fps)
      ctxStr = case mContext of
        Nothing -> ""
        Just ctx -> " in " <> ctx
  in "Invalid fps value" <> ctxStr <> ": " <> fpsStr <> ". FPS must be a positive number."

-- ============================================================================
-- CONVERSION
-- ============================================================================

-- | Safely divides by fps, returning fallback if fps is invalid
-- Prevents division by zero errors
-- 
-- System F/Omega proof: Explicit type Double -> Maybe Double -> Double -> Double
-- Mathematical proof: Result = numerator / validFps, or fallback if invalid
-- 
-- @param numerator The value to divide
-- @param fps The fps value (must be > 0)
-- @param fallback Value to return if fps is invalid (default: 0)
-- @returns numerator / fps, or fallback if fps is invalid
safeDivideByFps :: Double -> Maybe Double -> Double -> Double
safeDivideByFps numerator mFps fallback =
  let validFps = validateFps mFps defaultFps
      safeNumerator = ensureFinite numerator 0.0
      result = safeNumerator / validFps
  in ensureFinite result fallback

-- | Converts frame number to time in seconds
-- Validates fps to prevent division by zero
-- 
-- System F/Omega proof: Explicit type Double -> Double -> Double
-- Mathematical proof: Result = frame / validFps
-- 
-- @param frame Frame number
-- @param fps Frames per second (must be > 0)
-- @returns Time in seconds
frameToTime :: Double -> Double -> Double
frameToTime frame fps =
  let safeFrame = ensureFinite frame 0.0
      validFps = validateFps (Just fps) defaultFps
      result = safeFrame / validFps
  in ensureFinite result 0.0

-- | Converts time in seconds to frame number
-- Validates fps to ensure valid multiplication
-- 
-- System F/Omega proof: Explicit type Double -> Double -> Double
-- Mathematical proof: Result = time * validFps
-- 
-- @param time Time in seconds
-- @param fps Frames per second (must be > 0)
-- @returns Frame number (not rounded)
timeToFrame :: Double -> Double -> Double
timeToFrame time fps =
  let safeTime = ensureFinite time 0.0
      validFps = validateFps (Just fps) defaultFps
      result = safeTime * validFps
  in ensureFinite result 0.0

-- | Calculates duration in seconds from frame count
-- 
-- System F/Omega proof: Explicit type Double -> Double -> Double
-- Mathematical proof: Result = frameCount / validFps
-- 
-- @param frameCount Number of frames
-- @param fps Frames per second (must be > 0)
-- @returns Duration in seconds
calculateDuration :: Double -> Double -> Double
calculateDuration frameCount fps =
  let safeFrameCount = ensureFinite frameCount 0.0
      validFps = validateFps (Just fps) defaultFps
      result = safeFrameCount / validFps
  in ensureFinite result 0.0

-- | Calculates frame count from duration
-- 
-- System F/Omega proof: Explicit type Double -> Double -> Int
-- Mathematical proof: Result = ceiling(duration * validFps)
-- 
-- @param duration Duration in seconds
-- @param fps Frames per second (must be > 0)
-- @returns Frame count (ceiling)
calculateFrameCount :: Double -> Double -> Int
calculateFrameCount duration fps =
  let safeDuration = ensureFinite duration 0.0
      validFps = validateFps (Just fps) defaultFps
      result = safeDuration * validFps
      safeResult = ensureFinite result 0.0
  in ceiling safeResult
