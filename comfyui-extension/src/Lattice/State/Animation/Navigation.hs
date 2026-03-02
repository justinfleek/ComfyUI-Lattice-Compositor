-- |
-- Module      : Lattice.State.Animation.Navigation
-- Description : Navigation operations for animation store
-- 
-- Migrated from ui/src/stores/animationStore/navigation.ts
-- Pure functions for frame navigation: goToStart, goToEnd, keyframe jumping
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Animation.Navigation
  ( goToStart
  , goToEnd
  , jumpToNextKeyframe
  , jumpToPrevKeyframe
  ) where

import Data.Maybe (Maybe)
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.State.Animation.Playback (setFrame)
import Lattice.State.Keyframe.Query (findNextKeyframeFrame, findPrevKeyframeFrame)
import Lattice.Types.Layer (Layer(..))
import Lattice.Types.Project (Composition(..), CompositionSettings(..))

-- ============================================================================
-- NAVIGATION OPERATIONS
-- ============================================================================

-- | Jump to first frame (frame 0)
-- Pure function: takes composition, returns new composition with currentFrame = 0
-- Returns True if temporal state should be cleared (frame changed)
goToStart ::
  Composition -> -- Current composition
  Either Text (Composition, Bool) -- (Updated composition, should clear temporal state), or error
goToStart comp =
  let
    currentFrame = compositionCurrentFrame comp
    shouldClear = currentFrame /= 0.0
    updatedComp = comp {compositionCurrentFrame = 0.0}
  in
    Right (updatedComp, shouldClear)

-- | Jump to last frame (frameCount - 1)
-- Pure function: takes composition, returns new composition with currentFrame = frameCount - 1
-- Returns True if temporal state should be cleared (frame changed)
goToEnd ::
  Composition -> -- Current composition
  Either Text (Composition, Bool) -- (Updated composition, should clear temporal state), or error
goToEnd comp =
  let
    settings = compositionSettings comp
    frameCount = compositionSettingsFrameCount settings
    lastFrame = frameCount - 1
    currentFrame = compositionCurrentFrame comp
    shouldClear = currentFrame /= lastFrame
    updatedComp = comp {compositionCurrentFrame = lastFrame}
  in
    Right (updatedComp, shouldClear)

-- | Jump to the next keyframe (K key behavior)
-- Pure function: takes composition, optional layer ID, selected layer IDs, and layers list
-- Returns new composition with currentFrame set to next keyframe, or unchanged if no next keyframe
-- NOTE: Keyframes use 1-indexed frames, Composition uses 0-indexed frames - conversion handled here
jumpToNextKeyframe ::
  Composition -> -- Current composition
  Maybe Text -> -- Optional layer ID (if provided, only search this layer)
  [Text] -> -- Selected layer IDs (if no layerId provided and this is non-empty, search only these)
  [Layer] -> -- All layers in composition
  Either Text (Composition, Bool) -- (Updated composition, should clear temporal state), or error
jumpToNextKeyframe comp mLayerId selectedLayerIds layers =
  let
    currentFrame = compositionCurrentFrame comp
    
    -- Convert 0-indexed composition frame to 1-indexed keyframe frame
    -- Keyframes are 1-indexed (>= 1), Composition is 0-indexed (>= 0)
    keyframeFrame = currentFrame + 1.0
    
    -- Determine which layers to search
    layerIds = case mLayerId of
      Just layerId -> [layerId]
      Nothing -> if length selectedLayerIds > 0 then selectedLayerIds else []
    
    -- Find next keyframe (returns 1-indexed frame)
    nextKeyframeResult = findNextKeyframeFrame keyframeFrame layerIds layers
  in
    case nextKeyframeResult of
      Left err -> Left ("jumpToNextKeyframe: " <> err)
      Right nextKeyframeFrame1Indexed ->
        -- Convert 1-indexed keyframe frame back to 0-indexed composition frame
        let
          nextFrame0Indexed = nextKeyframeFrame1Indexed - 1.0
          -- Use setFrame to update composition (handles validation and clamping)
          setFrameResult = setFrame comp nextFrame0Indexed
        in
          case setFrameResult of
            Left err -> Left err
            Right (updatedComp, shouldClear) -> Right (updatedComp, shouldClear || currentFrame /= nextFrame0Indexed)

-- | Jump to the previous keyframe (J key behavior)
-- Pure function: takes composition, optional layer ID, selected layer IDs, and layers list
-- Returns new composition with currentFrame set to previous keyframe, or unchanged if no previous keyframe
-- NOTE: Keyframes use 1-indexed frames, Composition uses 0-indexed frames - conversion handled here
jumpToPrevKeyframe ::
  Composition -> -- Current composition
  Maybe Text -> -- Optional layer ID (if provided, only search this layer)
  [Text] -> -- Selected layer IDs (if no layerId provided and this is non-empty, search only these)
  [Layer] -> -- All layers in composition
  Either Text (Composition, Bool) -- (Updated composition, should clear temporal state), or error
jumpToPrevKeyframe comp mLayerId selectedLayerIds layers =
  let
    currentFrame = compositionCurrentFrame comp
    
    -- Convert 0-indexed composition frame to 1-indexed keyframe frame
    -- Keyframes are 1-indexed (>= 1), Composition is 0-indexed (>= 0)
    keyframeFrame = currentFrame + 1.0
    
    -- Determine which layers to search
    layerIds = case mLayerId of
      Just layerId -> [layerId]
      Nothing -> if length selectedLayerIds > 0 then selectedLayerIds else []
    
    -- Find previous keyframe (returns 1-indexed frame)
    prevKeyframeResult = findPrevKeyframeFrame keyframeFrame layerIds layers
  in
    case prevKeyframeResult of
      Left err -> Left ("jumpToPrevKeyframe: " <> err)
      Right prevKeyframeFrame1Indexed ->
        -- Convert 1-indexed keyframe frame back to 0-indexed composition frame
        let
          prevFrame0Indexed = prevKeyframeFrame1Indexed - 1.0
          -- Use setFrame to update composition (handles validation and clamping)
          setFrameResult = setFrame comp prevFrame0Indexed
        in
          case setFrameResult of
            Left err -> Left err
            Right (updatedComp, shouldClear) -> Right (updatedComp, shouldClear || currentFrame /= prevFrame0Indexed)
