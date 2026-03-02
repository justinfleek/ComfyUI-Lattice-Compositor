{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Exports.WorkflowParamsSchema
Description : WorkflowParams export format types
Copyright   : (c) Lattice, 2026
License     : MIT

WorkflowParams export format types.
These define the EXACT property names that workflow templates expect.

Source: ui/src/schemas/exports/workflow-params-schema.ts
-}

module Lattice.Schemas.Exports.WorkflowParamsSchema
  ( -- * Constants
    maxTracks
  , maxPointsPerTrack
  , atiFixedFrames
  , maxCoordinate
    -- * Structures
  , TrackPoint(..)
  , WanMoveMotionData(..)
  , ATIMotionData(..)
    -- * Validation
  , isValidTrackPoint
  , isValidWanMoveMotionData
  , isValidATIMotionData
  ) where

import GHC.Generics (Generic)
import Data.Vector (Vector)
import qualified Data.Vector as V

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxTracks :: Int
maxTracks = 10000

maxPointsPerTrack :: Int
maxPointsPerTrack = 100000

atiFixedFrames :: Int
atiFixedFrames = 121

maxCoordinate :: Double
maxCoordinate = 16384.0

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | Track point format used by WanMove and ATI exports
data TrackPoint = TrackPoint
  { tpX :: !Double
  , tpY :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | WanMove motionData structure
data WanMoveMotionData = WanMoveMotionData
  { wmmdTracks :: !(Vector (Vector TrackPoint))
  }
  deriving stock (Eq, Show, Generic)

-- | ATI motionData structure
data ATIMotionData = ATIMotionData
  { amdTrajectories :: !(Vector (Vector TrackPoint))
  }
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if track point is valid
isValidTrackPoint :: TrackPoint -> Bool
isValidTrackPoint p =
  tpX p >= 0 && tpX p <= maxCoordinate &&
  tpY p >= 0 && tpY p <= maxCoordinate

-- | Check if WanMove motion data is valid
isValidWanMoveMotionData :: WanMoveMotionData -> Bool
isValidWanMoveMotionData d =
  V.length (wmmdTracks d) <= maxTracks &&
  V.all (\track -> V.length track <= maxPointsPerTrack) (wmmdTracks d)

-- | Check if ATI motion data is valid
isValidATIMotionData :: ATIMotionData -> Bool
isValidATIMotionData d =
  V.length (amdTrajectories d) <= maxTracks &&
  V.all (\traj -> V.length traj == atiFixedFrames) (amdTrajectories d)
