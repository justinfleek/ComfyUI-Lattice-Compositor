-- |
-- Module      : Lattice.State.Animation
-- Description : Pure state management functions for animation store
--
-- Migrated from ui/src/stores/animationStore/index.ts + submodules
-- Pure functions extracted from Pinia store - no state mutation, no IO
--
-- This module re-exports all functions from specialized sub-modules for convenience.
-- Individual sub-modules can be imported directly for more granular control.
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Animation
  ( -- Re-export from Types
    module Lattice.State.Animation.Types
  -- Re-export from Playback
  , module Lattice.State.Animation.Playback
  -- Re-export from Navigation
  , module Lattice.State.Animation.Navigation
  -- Re-export from WorkArea
  , module Lattice.State.Animation.WorkArea
  -- Re-export from Snap
  , module Lattice.State.Animation.Snap
  -- Re-export from TimelineZoom
  , module Lattice.State.Animation.TimelineZoom
  -- Re-export from Evaluation
  , module Lattice.State.Animation.Evaluation
  ) where

-- Re-export all functions from sub-modules
import Lattice.State.Animation.Types
import Lattice.State.Animation.Playback
import Lattice.State.Animation.Navigation
import Lattice.State.Animation.WorkArea
import Lattice.State.Animation.Snap
import Lattice.State.Animation.TimelineZoom
import Lattice.State.Animation.Evaluation
