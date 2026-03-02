-- |
-- Module      : Lattice.State.Animation.Snap
-- Description : Snap configuration operations for animation store
-- 
-- Migrated from ui/src/stores/animationStore/index.ts (snap configuration section)
-- Pure functions for snap configuration management
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Animation.Snap
  ( setSnapConfig
  , toggleSnapping
  , toggleSnapType
  , SnapTypeToggle(..)
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Services.TimelineSnap (SnapConfig(..), SnapType(..))
import Lattice.State.Animation.Types (AnimationState(..))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // snap // type // toggle
-- ════════════════════════════════════════════════════════════════════════════

-- | Snap type for toggling
data SnapTypeToggle
  = SnapTypeToggleGrid
  | SnapTypeToggleKeyframes
  | SnapTypeToggleBeats
  | SnapTypeTogglePeaks
  | SnapTypeToggleLayerBounds
  | SnapTypeTogglePlayhead
  deriving (Eq, Show)

-- ════════════════════════════════════════════════════════════════════════════
--                                       // snap // configuration // operations
-- ════════════════════════════════════════════════════════════════════════════

-- | Set snap configuration (partial update)
-- Pure function: takes animation state and partial snap config, returns new state
setSnapConfig ::
  AnimationState -> -- Current animation state
  SnapConfig -> -- New snap configuration (replaces existing)
  AnimationState -- Updated animation state
setSnapConfig state newConfig =
  state {animationStateSnapConfig = newConfig}

-- | Toggle snapping on/off
-- Pure function: takes animation state, returns new state with snapping toggled
toggleSnapping ::
  AnimationState -> -- Current animation state
  AnimationState -- Updated animation state
toggleSnapping state =
  let
    currentConfig = animationStateSnapConfig state
    updatedConfig = currentConfig {snapConfigEnabled = not (snapConfigEnabled currentConfig)}
  in
    state {animationStateSnapConfig = updatedConfig}

-- | Toggle specific snap type
-- Pure function: takes animation state and snap type, returns new state with that type toggled
toggleSnapType ::
  AnimationState -> -- Current animation state
  SnapTypeToggle -> -- Snap type to toggle
  AnimationState -- Updated animation state
toggleSnapType state snapType =
  let
    currentConfig = animationStateSnapConfig state
    updatedConfig = case snapType of
      SnapTypeToggleGrid ->
        currentConfig {snapConfigSnapToGrid = not (snapConfigSnapToGrid currentConfig)}
      SnapTypeToggleKeyframes ->
        currentConfig {snapConfigSnapToKeyframes = not (snapConfigSnapToKeyframes currentConfig)}
      SnapTypeToggleBeats ->
        currentConfig {snapConfigSnapToBeats = not (snapConfigSnapToBeats currentConfig)}
      SnapTypeTogglePeaks ->
        currentConfig {snapConfigSnapToPeaks = not (snapConfigSnapToPeaks currentConfig)}
      SnapTypeToggleLayerBounds ->
        currentConfig {snapConfigSnapToLayerBounds = not (snapConfigSnapToLayerBounds currentConfig)}
      SnapTypeTogglePlayhead ->
        currentConfig {snapConfigSnapToPlayhead = not (snapConfigSnapToPlayhead currentConfig)}
  in
    state {animationStateSnapConfig = updatedConfig}

-- ════════════════════════════════════════════════════════════════════════════
--                                                                      // note
-- ════════════════════════════════════════════════════════════════════════════
--
-- The findSnapPoint function requires findNearestSnap from TimelineSnap service,
-- which has not been migrated yet. This function will be added when TimelineSnap
-- service migration is complete.
--
-- TypeScript signature:
-- findSnapPoint(
--   store: SnapPointAccess,
--   frame: number,
--   pixelsPerFrame: number,
--   selectedLayerId?: string | null,
-- ): SnapResult
--
-- This will be implemented as:
-- findSnapPoint ::
--   Double -> -- Frame to find snap point for
--   SnapConfig -> -- Snap configuration
--   Double -> -- Pixels per frame
--   [Layer] -> -- Layers list
--   Maybe Text -> -- Selected layer ID (optional)
--   Double -> -- Current frame
--   Maybe AudioAnalysis -> -- Audio analysis (optional)
--   Maybe PeakData -> -- Peak data (optional)
--   Either Text SnapResult -- Snap result or error
--
