-- | Lattice.Services.Export.WanMoveExport.Export - Export functions
-- |
-- | Functions for exporting trajectory data in various formats.
-- | Supports JSON, NPY-compatible, and WanVideoWrapper formats.
-- |
-- | Source: ui/src/services/export/wanMoveExport.ts

module Lattice.Services.Export.WanMoveExport.Export
  ( -- * JSON Export
    exportAsJSON
  , exportWanMoveTrackCoordsJSON
  , exportWanMoveVisibility
  , exportWanMoveTrackCoordsPackage
    -- * NPY Export
  , NPYData
  , exportAsNPYData
    -- * Types
  , WanMovePackage
  ) where

import Prelude
import Data.Array (length, (!!), foldl, range)
import Data.Maybe (Maybe(..), fromMaybe)
import Effect (Effect)

import Lattice.Services.Export.WanMoveExport.Types
  ( WanMoveTrajectory
  , TrajectoryMetadata
  , TrackPoint
  )

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | NPY-compatible data structure
type NPYData =
  { tracks :: Array Number  -- Flattened [N * T * 2]
  , visibility :: Array Int  -- Flattened [N * T] (0 or 1)
  , shape ::
      { tracks :: { n :: Int, t :: Int, coords :: Int }
      , visibility :: { n :: Int, t :: Int }
      }
  }

-- | WanMove package with metadata
type WanMovePackage =
  { trackCoords :: String  -- JSON string
  , metadata :: TrajectoryMetadata
  }

--------------------------------------------------------------------------------
-- JSON Export
--------------------------------------------------------------------------------

-- | Export trajectory data as JSON string
exportAsJSON :: WanMoveTrajectory -> String
exportAsJSON trajectory =
  toJSON trajectory

-- | Export as WanMove-compatible track_coords JSON
-- | Format: [[{x, y}, {x, y}, ...], [{x, y}, ...], ...]
exportWanMoveTrackCoordsJSON :: WanMoveTrajectory -> String
exportWanMoveTrackCoordsJSON trajectory =
  let
    tracks = trajectory.tracks
    formattedTracks = map (\track ->
      map (\point -> { x: point.x, y: point.y }) track
    ) tracks
    pointToJSON :: { x :: Number, y :: Number } -> String
    pointToJSON p = "[" <> show p.x <> "," <> show p.y <> "]"

    trackToJSON :: Array { x :: Number, y :: Number } -> String
    trackToJSON track = toJSONArray pointToJSON track
  in
    toJSONArray trackToJSON formattedTracks

-- | Export visibility as WanMove-compatible JSON
-- | Transposed from [N][T] to [T][N]
exportWanMoveVisibility :: WanMoveTrajectory -> String
exportWanMoveVisibility trajectory =
  let
    vis = trajectory.visibility
    numPoints = trajectory.metadata.numPoints
    numFrames = trajectory.metadata.numFrames

    -- Transpose visibility
    transposed = map (\f ->
      map (\n ->
        let
          visRow = fromMaybe [] (vis !! n)
          visVal = fromMaybe false (visRow !! f)
        in
          visVal
      ) (range 0 (numPoints - 1))
    ) (range 0 (numFrames - 1))
    boolToJSON :: Boolean -> String
    boolToJSON b = if b then "true" else "false"

    rowToJSON :: Array Boolean -> String
    rowToJSON row = toJSONArray boolToJSON row
  in
    toJSONArray rowToJSON transposed

-- | Export track_coords with metadata
exportWanMoveTrackCoordsPackage :: WanMoveTrajectory -> WanMovePackage
exportWanMoveTrackCoordsPackage trajectory =
  { trackCoords: exportWanMoveTrackCoordsJSON trajectory
  , metadata: trajectory.metadata
  }

--------------------------------------------------------------------------------
-- NPY Export
--------------------------------------------------------------------------------

-- | Export as NPY-compatible data structure
exportAsNPYData :: WanMoveTrajectory -> NPYData
exportAsNPYData trajectory =
  let
    tracks = trajectory.tracks
    vis = trajectory.visibility
    numPoints = trajectory.metadata.numPoints
    numFrames = trajectory.metadata.numFrames

    -- Flatten tracks to [N * T * 2]
    flatTracks = foldl (\acc i ->
      let
        track = fromMaybe [] (tracks !! i)
      in
        foldl (\acc' f ->
          let
            point = fromMaybe { x: 0.0, y: 0.0 } (track !! f)
          in
            acc' <> [point.x, point.y]
        ) acc (range 0 (numFrames - 1))
    ) [] (range 0 (numPoints - 1))

    -- Flatten visibility to [N * T]
    flatVis = foldl (\acc i ->
      let
        visRow = fromMaybe [] (vis !! i)
      in
        foldl (\acc' f ->
          let
            v = fromMaybe false (visRow !! f)
          in
            acc' <> [if v then 1 else 0]
        ) acc (range 0 (numFrames - 1))
    ) [] (range 0 (numPoints - 1))
  in
    { tracks: flatTracks
    , visibility: flatVis
    , shape:
        { tracks: { n: numPoints, t: numFrames, coords: 2 }
        , visibility: { n: numPoints, t: numFrames }
        }
    }

--------------------------------------------------------------------------------
-- JSON Helpers (Pure implementations)
--------------------------------------------------------------------------------

-- | Convert trajectory to JSON string
toJSON :: WanMoveTrajectory -> String
toJSON trajectory =
  "{"
  <> "\"tracks\":" <> tracksToJSON trajectory.tracks <> ","
  <> "\"visibility\":" <> visibilityToJSON trajectory.visibility <> ","
  <> "\"metadata\":" <> metadataToJSON trajectory.metadata
  <> "}"

-- | Convert tracks to JSON
tracksToJSON :: Array (Array { x :: Number, y :: Number }) -> String
tracksToJSON tracks =
  "[" <> intercalateWith "," trackToJSON tracks <> "]"
  where
    trackToJSON :: Array { x :: Number, y :: Number } -> String
    trackToJSON track =
      "[" <> intercalateWith "," pointToJSON track <> "]"

    pointToJSON :: { x :: Number, y :: Number } -> String
    pointToJSON p = "[" <> show p.x <> "," <> show p.y <> "]"

-- | Convert visibility to JSON
visibilityToJSON :: Array (Array Boolean) -> String
visibilityToJSON vis =
  "[" <> intercalateWith "," rowToJSON vis <> "]"
  where
    rowToJSON :: Array Boolean -> String
    rowToJSON row =
      "[" <> intercalateWith "," (\b -> if b then "true" else "false") row <> "]"

-- | Convert metadata to JSON
metadataToJSON :: TrajectoryMetadata -> String
metadataToJSON meta =
  "{"
  <> "\"numPoints\":" <> show meta.numPoints <> ","
  <> "\"numFrames\":" <> show meta.numFrames <> ","
  <> "\"width\":" <> show meta.width <> ","
  <> "\"height\":" <> show meta.height <> ","
  <> "\"fps\":" <> show meta.fps
  <> "}"

-- | Convert array of track points to JSON
toJSONArray :: forall a. (a -> String) -> Array a -> String
toJSONArray f arr =
  "[" <> intercalateWith "," f arr <> "]"

-- | Intercalate with separator
intercalateWith :: forall a. String -> (a -> String) -> Array a -> String
intercalateWith sep f arr =
  let
    n = length arr
  in
    foldl (\acc i ->
      let
        item = fromMaybe (f (unsafeHead arr)) (map f (arr !! i))
        prefix = if i > 0 then sep else ""
      in
        acc <> prefix <> item
    ) "" (range 0 (n - 1))
  where
    unsafeHead :: Array a -> a
    unsafeHead a = case a !! 0 of
      Just x -> x
      Nothing -> unsafeHead a  -- Will never happen if called correctly

