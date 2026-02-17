-- |
-- Module      : Lattice.State.Animation.Evaluation
-- Description : Frame evaluation operations for animation store
-- 
-- Migrated from ui/src/stores/animationStore/index.ts (frame evaluation section)
-- Pure functions for frame evaluation and time calculations
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Animation.Evaluation
  ( getCurrentTime
  -- FFI helpers (pass-through / simple conversions)
  , getCurrentFrame
  , getFrameCount
  , getFps
  , getEffectiveEndFrame
  , getCurrentTimeFromFrameFps
  ) where

import Data.Maybe (Maybe)
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Types.Primitives (validateFinite, validateNonNegative)
import Lattice.Types.Project (Composition(..), CompositionSettings(..))

-- ============================================================================
-- FRAME EVALUATION OPERATIONS
-- ============================================================================

-- | Get current time in seconds
-- Pure function: takes composition, returns current time in seconds
getCurrentTime ::
  Composition -> -- Current composition
  Either Text Double -- Current time in seconds, or error
getCurrentTime comp =
  let
    settings = compositionSettings comp
    fps = compositionSettingsFps settings
    currentFrame = compositionCurrentFrame comp
  in
    if not (validateFinite fps) || fps <= 0
      then Left ("getCurrentTime: Invalid FPS (must be finite and > 0): " <> T.pack (show fps))
      else if not (validateFinite currentFrame) || not (validateNonNegative currentFrame)
        then Left ("getCurrentTime: Invalid currentFrame (must be finite and non-negative): " <> T.pack (show currentFrame))
        else Right (currentFrame / fps)

-- ============================================================================
-- FFI HELPERS (pass-through / simple conversions for FFI layer)
-- ============================================================================

getCurrentFrame :: Int -> Int
getCurrentFrame = id

getFrameCount :: Int -> Int
getFrameCount = id

getFps :: Double -> Double
getFps = id

getEffectiveEndFrame :: Maybe Int -> Int -> Double
getEffectiveEndFrame mEnd frameCount =
  case mEnd of
    Just end -> fromIntegral end
    Nothing -> fromIntegral frameCount - 1.0

getCurrentTimeFromFrameFps :: Int -> Double -> Double
getCurrentTimeFromFrameFps frame fps = fromIntegral frame / fps

-- ============================================================================
-- NOTE: getFrameState
-- ============================================================================
--
-- The getFrameState function requires MotionEngine.evaluate() which has not been
-- migrated yet. This function will be added when MotionEngine migration is complete.
--
-- TypeScript signature:
-- getFrameState(
--   store: FrameEvaluationAccess,
--   frame?: number,
-- ): FrameState
--
-- This is the CANONICAL way to get evaluated state for rendering.
-- Uses MotionEngine.evaluate() which is PURE and deterministic.
--
-- This will be implemented as:
-- getFrameState ::
--   LatticeProject -> -- Full project data
--   Maybe Text -> -- Active camera ID (optional)
--   Maybe Double -> -- Frame override (optional, defaults to composition currentFrame)
--   Maybe AudioAnalysis -> -- Audio analysis (optional)
--   Maybe AudioReactiveData -> -- Audio reactive mappings (optional)
--   Either Text FrameState -- Evaluated frame state or error
--
