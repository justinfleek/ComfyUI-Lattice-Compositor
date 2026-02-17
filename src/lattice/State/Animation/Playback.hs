-- |
-- Module      : Lattice.State.Animation.Playback
-- Description : Playback operations for animation store
-- 
-- Migrated from ui/src/stores/animationStore/playback.ts
-- Pure functions for frame operations - playback control (play/pause) handled at FFI boundary
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Animation.Playback
  ( setFrame
  , nextFrame
  , prevFrame
  , jumpFrames
  , shouldClearTemporalState
  ) where

import Data.Maybe (Maybe)
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Types.Primitives (validateFinite, validateNonNegative)
import Lattice.Types.Project (Composition(..), CompositionSettings(..))

-- ============================================================================
-- FRAME OPERATIONS
-- ============================================================================

-- | Set current frame in composition
-- Pure function: takes composition and frame, returns new composition with updated currentFrame
-- Clears temporal effect state when frame changes non-sequentially (indicated by return value)
setFrame ::
  Composition -> -- Current composition
  Double -> -- Target frame number
  Either Text (Composition, Bool) -- (Updated composition, should clear temporal state), or error
setFrame comp frame =
  if not (validateFinite frame)
    then Left ("setFrame: Invalid frame value (must be finite): " <> T.pack (show frame))
    else
      let
        settings = compositionSettings comp
        frameCount = compositionSettingsFrameCount settings
        currentFrame = compositionCurrentFrame comp
        
        -- Clamp frame to valid range [0, frameCount - 1]
        newFrame = max 0.0 (min frame (frameCount - 1))
        
        -- Check if frame change is non-sequential (delta > 1)
        frameDelta = abs (newFrame - currentFrame)
        shouldClear = frameDelta > 1.0
        
        -- Update composition
        updatedComp = comp {compositionCurrentFrame = newFrame}
      in
        Right (updatedComp, shouldClear)

-- | Advance to next frame
-- Pure function: takes composition, returns new composition with incremented currentFrame
nextFrame ::
  Composition -> -- Current composition
  Either Text Composition -- Updated composition, or error
nextFrame comp =
  let
    settings = compositionSettings comp
    frameCount = compositionSettingsFrameCount settings
    currentFrame = compositionCurrentFrame comp
  in
    if currentFrame < frameCount - 1
      then Right (comp {compositionCurrentFrame = currentFrame + 1})
      else Right comp  -- Already at last frame, no change

-- | Go to previous frame
-- Pure function: takes composition, returns new composition with decremented currentFrame
prevFrame ::
  Composition -> -- Current composition
  Either Text Composition -- Updated composition, or error
prevFrame comp =
  let
    currentFrame = compositionCurrentFrame comp
  in
    if currentFrame > 0
      then Right (comp {compositionCurrentFrame = currentFrame - 1})
      else Right comp  -- Already at first frame, no change

-- | Jump forward or backward by N frames
-- Pure function: takes composition and frame delta, returns new composition with updated currentFrame
-- Clears temporal effect state when |n| > 1 (indicated by return value)
jumpFrames ::
  Composition -> -- Current composition
  Double -> -- Frame delta (positive = forward, negative = backward)
  Either Text (Composition, Bool) -- (Updated composition, should clear temporal state), or error
jumpFrames comp n =
  if not (validateFinite n)
    then Left ("jumpFrames: Invalid frame delta (must be finite): " <> T.pack (show n))
    else
      let
        settings = compositionSettings comp
        frameCount = compositionSettingsFrameCount settings
        currentFrame = compositionCurrentFrame comp
        
        -- Calculate new frame and clamp to valid range [0, frameCount - 1]
        newFrame = max 0.0 (min (currentFrame + n) (frameCount - 1))
        
        -- Check if jump is non-sequential (|n| > 1)
        shouldClear = abs n > 1.0
        
        -- Update composition
        updatedComp = comp {compositionCurrentFrame = newFrame}
      in
        Right (updatedComp, shouldClear)

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- | Check if temporal state should be cleared based on frame delta
-- Pure function: takes old frame and new frame, returns True if delta > 1
shouldClearTemporalState ::
  Double -> -- Old frame
  Double -> -- New frame
  Bool -- True if temporal state should be cleared
shouldClearTemporalState oldFrame newFrame =
  abs (newFrame - oldFrame) > 1.0
