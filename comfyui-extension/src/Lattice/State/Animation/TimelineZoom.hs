-- |
-- Module      : Lattice.State.Animation.TimelineZoom
-- Description : Timeline zoom operations for animation store
-- 
-- Migrated from ui/src/stores/animationStore/index.ts (timeline zoom section)
-- Pure functions for timeline zoom management
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Animation.TimelineZoom
  ( setTimelineZoom
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Lattice.State.Animation.Types (AnimationState(..))
import Lattice.Types.Primitives (validateFinite)

-- ============================================================================
-- TIMELINE ZOOM OPERATIONS
-- ============================================================================

-- | Set timeline zoom level
-- Pure function: takes animation state and zoom level, returns new state
-- Zoom level must be in range [0.1, 10] where 1.0 = 100%
setTimelineZoom ::
  AnimationState -> -- Current animation state
  Double -> -- Zoom level (0.1 to 10, where 1.0 = 100%)
  Either Text AnimationState -- Updated animation state, or error
setTimelineZoom state zoom =
  if not (validateFinite zoom)
    then Left ("setTimelineZoom: Invalid zoom value (must be finite): " <> T.pack (show zoom))
    else
      let
        -- Clamp zoom to valid range [0.1, 10]
        clampedZoom = max 0.1 (min zoom 10.0)
        updatedState = state {animationStateTimelineZoom = clampedZoom}
      in
        Right updatedState
