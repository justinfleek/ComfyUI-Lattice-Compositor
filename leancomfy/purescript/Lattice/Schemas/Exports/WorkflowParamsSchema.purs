-- | Lattice.Schemas.Exports.WorkflowParamsSchema - WorkflowParams export format types
-- |
-- | WorkflowParams export format types.
-- | These define the EXACT property names that workflow templates expect.
-- |
-- | Source: ui/src/schemas/exports/workflow-params-schema.ts

module Lattice.Schemas.Exports.WorkflowParamsSchema
  ( -- Constants
    maxTracks
  , maxPointsPerTrack
  , atiFixedFrames
  , maxCoordinate
    -- Structures
  , TrackPoint
  , WanMoveMotionData
  , ATIMotionData
    -- Validation
  , isValidTrackPoint
  , isValidWanMoveMotionData
  , isValidATIMotionData
  ) where

import Prelude
import Data.Array (length, all)

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxTracks :: Int
maxTracks = 10000

maxPointsPerTrack :: Int
maxPointsPerTrack = 100000

atiFixedFrames :: Int
atiFixedFrames = 121

maxCoordinate :: Number
maxCoordinate = 16384.0

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

-- | Track point format used by WanMove and ATI exports
type TrackPoint =
  { x :: Number
  , y :: Number
  }

-- | WanMove motionData structure
type WanMoveMotionData =
  { tracks :: Array (Array TrackPoint)
  }

-- | ATI motionData structure
type ATIMotionData =
  { trajectories :: Array (Array TrackPoint)
  }

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Check if track point is valid
isValidTrackPoint :: TrackPoint -> Boolean
isValidTrackPoint p =
  p.x >= 0.0 && p.x <= maxCoordinate &&
  p.y >= 0.0 && p.y <= maxCoordinate

-- | Check if WanMove motion data is valid
isValidWanMoveMotionData :: WanMoveMotionData -> Boolean
isValidWanMoveMotionData d =
  length d.tracks <= maxTracks &&
  all (\track -> length track <= maxPointsPerTrack) d.tracks

-- | Check if ATI motion data is valid
isValidATIMotionData :: ATIMotionData -> Boolean
isValidATIMotionData d =
  length d.trajectories <= maxTracks &&
  all (\traj -> length traj == atiFixedFrames) d.trajectories
