-- | Lattice.Services.Export.Transform - Export data transformations
-- |
-- | Pure functions for transforming between export formats.
-- | Converts internal trajectory formats to workflow-compatible formats.
-- |
-- | Source: ui/src/services/export/exportToWorkflowParams.ts

module Lattice.Services.Export.Transform
  ( -- * WanMove Transformation
    transformWanMoveToMotionData
  , transformATIToMotionData
  , transformExportToMotionData
    -- * Track Conversion
  , tracksToPoints
  , pointsToTracks
  , normalizeTrajectory
  , denormalizeTrajectory
    -- * Coordinate Conversion
  , pixelToNormalized
  , normalizedToPixel
  , flipYCoordinate
    -- * Validation
  , validateTrajectoryBounds
  , validateFrameCount
  ) where

import Prelude
import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Traversable (traverse)

import Lattice.Services.Export.Types
  ( TrackPoint
  , WanMoveTrajectory
  , WanMoveTrajectoryExport
  , ATIExportResult
  , ATITrackPoint
  , ModelTarget(..)
  , UnifiedExportResult
  )

--------------------------------------------------------------------------------
-- Motion Data Types (for workflow params)
--------------------------------------------------------------------------------

-- | WanMove motion data format for workflow params
type WanMoveMotionData =
  { tracks :: Array (Array TrackPoint)
  }

-- | ATI motion data format for workflow params
type ATIMotionData =
  { trajectories :: Array (Array TrackPoint)
  }

--------------------------------------------------------------------------------
-- WanMove Transformation
--------------------------------------------------------------------------------

-- | Transform WanMove export result to workflow motion data
-- | Converts tracks: number[][][] to tracks: Array<Array<{x, y}>>
transformWanMoveToMotionData :: UnifiedExportResult -> Either String WanMoveMotionData
transformWanMoveToMotionData result =
  case result.data of
    Nothing -> Left "Cannot transform: no data in export result"
    Just trajectory ->
      let
        formattedTracks = map trackToPoints trajectory.tracks
      in
        Right { tracks: formattedTracks }

-- | Transform ATI export result to workflow motion data
-- | ATI uses same structure but property name is "trajectories"
transformATIToMotionData :: UnifiedExportResult -> Either String ATIMotionData
transformATIToMotionData result =
  case result.data of
    Nothing -> Left "Cannot transform: no data in export result"
    Just trajectory ->
      let
        formattedTrajectories = map trackToPoints trajectory.tracks
      in
        Right { trajectories: formattedTrajectories }

-- | Transform based on target type
transformExportToMotionData
  :: ModelTarget
  -> UnifiedExportResult
  -> Either String { tracks :: Maybe (Array (Array TrackPoint)), trajectories :: Maybe (Array (Array TrackPoint)) }
transformExportToMotionData target result = do
  case target of
    TargetWanMove -> do
      motionData <- transformWanMoveToMotionData result
      pure { tracks: Just motionData.tracks, trajectories: Nothing }
    TargetATI -> do
      motionData <- transformATIToMotionData result
      pure { tracks: Nothing, trajectories: Just motionData.trajectories }
    _ ->
      Left ("Unsupported target for motion data transformation: " <> show target)

--------------------------------------------------------------------------------
-- Track Conversion
--------------------------------------------------------------------------------

-- | Convert a single track from [frame][x,y] to Array<{x,y}>
trackToPoints :: Array (Array Number) -> Array TrackPoint
trackToPoints = map arrayToPoint

-- | Convert [x, y] array to TrackPoint
arrayToPoint :: Array Number -> TrackPoint
arrayToPoint arr =
  case Array.index arr 0, Array.index arr 1 of
    Just x, Just y -> { x, y }
    _, _ -> { x: 0.0, y: 0.0 }

-- | Convert tracks to points format
tracksToPoints :: Array (Array (Array Number)) -> Array (Array TrackPoint)
tracksToPoints = map trackToPoints

-- | Convert points format back to tracks
pointsToTracks :: Array (Array TrackPoint) -> Array (Array (Array Number))
pointsToTracks = map (map pointToArray)

-- | Convert TrackPoint to [x, y] array
pointToArray :: TrackPoint -> Array Number
pointToArray p = [p.x, p.y]

--------------------------------------------------------------------------------
-- Normalization
--------------------------------------------------------------------------------

-- | Normalize trajectory coordinates to [0, 1] range
normalizeTrajectory :: Int -> Int -> WanMoveTrajectory -> WanMoveTrajectory
normalizeTrajectory width height trajectory =
  let
    normalizedTracks = map (map (normalizePoint width height)) trajectory.tracks
  in
    trajectory { tracks = normalizedTracks }

-- | Normalize a single point
normalizePoint :: Int -> Int -> Array Number -> Array Number
normalizePoint width height arr =
  case Array.index arr 0, Array.index arr 1 of
    Just x, Just y ->
      [ pixelToNormalized (toNumber width) x
      , pixelToNormalized (toNumber height) y
      ]
    _, _ -> arr

-- | Denormalize trajectory coordinates from [0, 1] to pixel space
denormalizeTrajectory :: Int -> Int -> WanMoveTrajectory -> WanMoveTrajectory
denormalizeTrajectory width height trajectory =
  let
    denormalizedTracks = map (map (denormalizePoint width height)) trajectory.tracks
  in
    trajectory { tracks = denormalizedTracks }

-- | Denormalize a single point
denormalizePoint :: Int -> Int -> Array Number -> Array Number
denormalizePoint width height arr =
  case Array.index arr 0, Array.index arr 1 of
    Just x, Just y ->
      [ normalizedToPixel (toNumber width) x
      , normalizedToPixel (toNumber height) y
      ]
    _, _ -> arr

--------------------------------------------------------------------------------
-- Coordinate Conversion
--------------------------------------------------------------------------------

-- | Convert pixel coordinate to normalized [0, 1]
pixelToNormalized :: Number -> Number -> Number
pixelToNormalized dimension pixel
  | dimension <= 0.0 = 0.0
  | otherwise = pixel / dimension

-- | Convert normalized [0, 1] to pixel coordinate
normalizedToPixel :: Number -> Number -> Number
normalizedToPixel dimension normalized = normalized * dimension

-- | Flip Y coordinate (for different coordinate systems)
flipYCoordinate :: Number -> Number -> Number
flipYCoordinate height y = height - y

-- | Helper to convert Int to Number
toNumber :: Int -> Number
toNumber = Int.toNumber

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Validate that all trajectory points are within bounds
validateTrajectoryBounds :: Int -> Int -> WanMoveTrajectory -> Either String WanMoveTrajectory
validateTrajectoryBounds width height trajectory =
  let
    isInBounds :: Array Number -> Boolean
    isInBounds arr =
      case Array.index arr 0, Array.index arr 1 of
        Just x, Just y ->
          x >= 0.0 && x <= toNumber width &&
          y >= 0.0 && y <= toNumber height
        _, _ -> false

    allInBounds = Array.all (Array.all isInBounds) trajectory.tracks
  in
    if allInBounds
    then Right trajectory
    else Left "Trajectory contains points outside bounds"

-- | Validate frame count matches expected
validateFrameCount :: Int -> WanMoveTrajectory -> Either String WanMoveTrajectory
validateFrameCount expected trajectory =
  if trajectory.frameCount == expected
  then Right trajectory
  else Left ("Frame count mismatch: expected " <> show expected <> ", got " <> show trajectory.frameCount)
