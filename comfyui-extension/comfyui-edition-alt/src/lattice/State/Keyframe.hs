-- |
-- Module      : Lattice.State.Keyframe
-- Description : Pure state management functions for keyframe store
-- 
-- Migrated from ui/src/stores/keyframeStore/index.ts + submodules
-- Pure functions extracted from Pinia store - no state mutation, no IO
--
-- This module re-exports all functions from specialized sub-modules for convenience.
-- Individual sub-modules can be imported directly for more granular control.
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Keyframe
  ( -- Re-export from Types
    module Lattice.State.Keyframe.Types
  -- Re-export from Helpers
  , module Lattice.State.Keyframe.Helpers
  -- Re-export from PropertyUpdate
  , module Lattice.State.Keyframe.PropertyUpdate
  -- Re-export from CRUD
  , module Lattice.State.Keyframe.CRUD
  -- Re-export from Interpolation
  , module Lattice.State.Keyframe.Interpolation
  -- Re-export from Property
  , module Lattice.State.Keyframe.Property
  -- Re-export from Query
  , module Lattice.State.Keyframe.Query
  -- Re-export from Timing
  , module Lattice.State.Keyframe.Timing
  -- Re-export from Clipboard
  , module Lattice.State.Keyframe.Clipboard
  -- Re-export from Velocity
  , module Lattice.State.Keyframe.Velocity
  -- Re-export from Dimensions
  , module Lattice.State.Keyframe.Dimensions
  -- Re-export from Expression
  , module Lattice.State.Keyframe.Expression
  -- Re-export from AutoBezier
  , module Lattice.State.Keyframe.AutoBezier
  -- Re-export from Evaluation
  , module Lattice.State.Keyframe.Evaluation
  ) where

-- Re-export all functions from sub-modules
import Lattice.State.Keyframe.Types
import Lattice.State.Keyframe.Helpers
import Lattice.State.Keyframe.PropertyUpdate
import Lattice.State.Keyframe.CRUD
import Lattice.State.Keyframe.Interpolation
import Lattice.State.Keyframe.Property
import Lattice.State.Keyframe.Query
import Lattice.State.Keyframe.Timing
import Lattice.State.Keyframe.Clipboard
import Lattice.State.Keyframe.Velocity
import Lattice.State.Keyframe.Dimensions
import Lattice.State.Keyframe.Expression
import Lattice.State.Keyframe.AutoBezier
import Lattice.State.Keyframe.Evaluation
