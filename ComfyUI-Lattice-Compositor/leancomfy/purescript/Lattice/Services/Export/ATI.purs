-- | Lattice.Services.Export.ATI - ATI trajectory export
-- |
-- | Exports trajectory data in ATI-compatible format for
-- | ComfyUI-WanVideoWrapper's WanVideoATITracks node.
-- |
-- | ATI Format Requirements:
-- | - JSON string input with tracks as `[[{x, y}, ...], ...]`
-- | - Fixed 121 frames (ATI_FIXED_FRAMES constant)
-- | - Coordinates centered around frame center
-- | - Normalized to [-1, 1] based on SHORT EDGE
-- |
-- | Source: ui/src/services/export/atiExport.ts

module Lattice.Services.Export.ATI
  ( -- * Constants
    atiFixedFrames
    -- * Types
  , ATITrackPointExport
  , ATIExportPackage
  , ATINormalizedTrack
  , ATINormalizedMetadata
  , ATINormalizedResult
  , ATIValidationResult
    -- * Export Functions
  , exportATITrackCoordsJSON
  , exportATIPackage
  , exportAsNormalizedATI
    -- * Validation
  , validateForATI
    -- * Helpers
  , createATITrajectory
  ) where

import Prelude
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Array as Array
import Data.Int (toNumber)
import Data.String as String
import Data.Foldable (foldl, all)

import Lattice.Services.Export.Types (WanMoveTrajectory, TrackPoint)

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Fixed frame count for ATI model
-- | Must match FIXED_LENGTH in ATI/nodes.py
atiFixedFrames :: Int
atiFixedFrames = 121

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | ATI track point for export (x, y only)
type ATITrackPointExport = { x :: Number, y :: Number }

-- | ATI export package with metadata
type ATIExportPackage =
  { tracks :: String  -- JSON string for track_coords input
  , width :: Int
  , height :: Int
  , numTracks :: Int
  , originalFrames :: Int
  }

-- | ATI normalized track point with visibility
type ATINormalizedTrack =
  { x :: Number
  , y :: Number
  , visible :: Number  -- 0.0 or 1.0
  }

-- | Metadata for normalized export
type ATINormalizedMetadata =
  { width :: Int
  , height :: Int
  , shortEdge :: Int
  , numTracks :: Int
  }

-- | Normalized ATI export result
type ATINormalizedResult =
  { tracks :: Array (Array ATINormalizedTrack)
  , timeRange :: Array Number  -- 121 values from -1 to 1
  , metadata :: ATINormalizedMetadata
  }

-- | Validation result
type ATIValidationResult =
  { valid :: Boolean
  , warnings :: Array String
  , errors :: Array String
  }

--------------------------------------------------------------------------------
-- Export Functions
--------------------------------------------------------------------------------

-- | Export trajectory as ATI-compatible JSON string
-- |
-- | This function:
-- | 1. Pads or truncates tracks to exactly 121 frames
-- | 2. Keeps coordinates in PIXEL space (normalization is done by ATI node)
-- | 3. Formats as `[[{x, y}, ...], ...]`
exportATITrackCoordsJSON :: WanMoveTrajectory -> String
exportATITrackCoordsJSON trajectory =
  let
    atiTracks = map (convertTrack trajectory.frameCount) trajectory.tracks
  in
    serializeATITracks atiTracks

-- | Convert a single track to ATI format with 121 frame padding
convertTrack :: Int -> Array (Array Number) -> Array ATITrackPointExport
convertTrack numFrames track =
  Array.range 0 (atiFixedFrames - 1) # map \f ->
    if f < numFrames && f < Array.length track then
      -- Use actual track data
      case Array.index track f of
        Just frame -> arrayToPoint frame
        Nothing -> { x: 0.0, y: 0.0 }
    else if Array.length track > 0 then
      -- Pad with last known position (hold last frame)
      case Array.last track of
        Just lastFrame -> arrayToPoint lastFrame
        Nothing -> { x: 0.0, y: 0.0 }
    else
      -- Empty track - use origin
      { x: 0.0, y: 0.0 }

-- | Convert [x, y] array to ATITrackPointExport
arrayToPoint :: Array Number -> ATITrackPointExport
arrayToPoint arr =
  case Array.index arr 0, Array.index arr 1 of
    Just x, Just y -> { x, y }
    _, _ -> { x: 0.0, y: 0.0 }

-- | Serialize tracks to JSON string
serializeATITracks :: Array (Array ATITrackPointExport) -> String
serializeATITracks tracks =
  "[" <> String.joinWith "," (map serializeTrack tracks) <> "]"

-- | Serialize a single track
serializeTrack :: Array ATITrackPointExport -> String
serializeTrack points =
  "[" <> String.joinWith "," (map serializePoint points) <> "]"

-- | Serialize a single point
serializePoint :: ATITrackPointExport -> String
serializePoint pt =
  "{\"x\":" <> show pt.x <> ",\"y\":" <> show pt.y <> "}"

-- | Export trajectory with full ATI metadata
exportATIPackage :: WanMoveTrajectory -> ATIExportPackage
exportATIPackage trajectory =
  { tracks: exportATITrackCoordsJSON trajectory
  , width: trajectory.width
  , height: trajectory.height
  , numTracks: Array.length trajectory.tracks
  , originalFrames: trajectory.frameCount
  }

-- | Export trajectory as normalized ATI format
-- |
-- | Pre-normalizes coordinates to [-1, 1] range.
-- | Normalization formula (from ATI motion.py):
-- | 1. Center: coords - [width/2, height/2]
-- | 2. Normalize: coords / short_edge * 2
exportAsNormalizedATI :: WanMoveTrajectory -> Maybe (Array (Array Boolean)) -> ATINormalizedResult
exportAsNormalizedATI trajectory visibility =
  let
    { tracks, width, height, frameCount } = trajectory
    shortEdge = min width height
    halfWidth = toNumber width / 2.0
    halfHeight = toNumber height / 2.0
    shortEdgeNum = toNumber shortEdge

    -- Generate time range: -1 to 1 across 121 frames
    halfFrames = toNumber atiFixedFrames / 2.0
    timeRange = Array.range 0 (atiFixedFrames - 1) # map \f ->
      (toNumber f - halfFrames) / halfFrames

    -- Normalize tracks
    normalizedTracks = Array.mapWithIndex (normalizeTrack halfWidth halfHeight shortEdgeNum frameCount visibility) tracks
  in
    { tracks: normalizedTracks
    , timeRange
    , metadata:
        { width
        , height
        , shortEdge
        , numTracks: Array.length tracks
        }
    }

-- | Normalize a single track
normalizeTrack
  :: Number -> Number -> Number -> Int
  -> Maybe (Array (Array Boolean))
  -> Int
  -> Array (Array Number)
  -> Array ATINormalizedTrack
normalizeTrack halfWidth halfHeight shortEdge numFrames visibility trackIdx track =
  Array.range 0 (atiFixedFrames - 1) # map \f ->
    let
      { x, y, vis } =
        if f < numFrames && f < Array.length track then
          case Array.index track f of
            Just frame ->
              let
                px = fromMaybe halfWidth (Array.index frame 0)
                py = fromMaybe halfHeight (Array.index frame 1)
                v = getVisibility visibility trackIdx f
              in
                { x: px, y: py, vis: v }
            Nothing ->
              { x: halfWidth, y: halfHeight, vis: false }
        else if Array.length track > 0 then
          let
            lastIdx = min (numFrames - 1) (Array.length track - 1)
          in
            case Array.index track lastIdx of
              Just lastFrame ->
                let
                  px = fromMaybe halfWidth (Array.index lastFrame 0)
                  py = fromMaybe halfHeight (Array.index lastFrame 1)
                  v = getVisibility visibility trackIdx lastIdx
                in
                  { x: px, y: py, vis: v }
              Nothing ->
                { x: halfWidth, y: halfHeight, vis: false }
        else
          { x: halfWidth, y: halfHeight, vis: false }

      -- Center around frame center
      centeredX = x - halfWidth
      centeredY = y - halfHeight

      -- Normalize by short edge to [-1, 1] range
      normX = if shortEdge > 0.0 then (centeredX / shortEdge) * 2.0 else 0.0
      normY = if shortEdge > 0.0 then (centeredY / shortEdge) * 2.0 else 0.0

      -- Visibility as float
      visFloat = if vis then 1.0 else 0.0
    in
      { x: normX, y: normY, visible: visFloat }

-- | Get visibility for a specific track and frame
getVisibility :: Maybe (Array (Array Boolean)) -> Int -> Int -> Boolean
getVisibility visibility trackIdx frameIdx =
  case visibility of
    Nothing -> true
    Just visArray ->
      case Array.index visArray trackIdx of
        Nothing -> true
        Just trackVis ->
          case Array.index trackVis frameIdx of
            Nothing -> true
            Just v -> v

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Validate trajectory for ATI compatibility
validateForATI :: WanMoveTrajectory -> ATIValidationResult
validateForATI trajectory =
  let
    { tracks, width, height, frameCount } = trajectory
    numPoints = Array.length tracks

    errors = Array.catMaybes
      [ if numPoints == 0 then Just "No tracks provided" else Nothing
      , if width <= 0 || height <= 0 then Just ("Invalid dimensions: " <> show width <> "x" <> show height) else Nothing
      ]

    frameWarning =
      if frameCount > atiFixedFrames then
        Just ("Trajectory has " <> show frameCount <> " frames but ATI uses " <> show atiFixedFrames <>
              ". Frames beyond " <> show atiFixedFrames <> " will be truncated.")
      else if frameCount < atiFixedFrames then
        Just ("Trajectory has " <> show frameCount <> " frames but ATI expects " <> show atiFixedFrames <>
              ". Last frame will be held to pad the remaining " <> show (atiFixedFrames - frameCount) <> " frames.")
      else
        Nothing

    outOfBoundsCount = countOutOfBounds tracks width height

    boundsWarning =
      if outOfBoundsCount > 0 then
        Just (show outOfBoundsCount <> " track points are outside the frame bounds (" <>
              show width <> "x" <> show height <> "). These will be normalized but may produce unexpected results.")
      else
        Nothing

    warnings = Array.catMaybes [frameWarning, boundsWarning]
  in
    { valid: Array.length errors == 0
    , warnings
    , errors
    }

-- | Count out-of-bounds points
countOutOfBounds :: Array (Array (Array Number)) -> Int -> Int -> Int
countOutOfBounds tracks width height =
  let
    widthNum = toNumber width
    heightNum = toNumber height
  in
    foldl (\acc track ->
      foldl (\count frame ->
        let
          x = fromMaybe 0.0 (Array.index frame 0)
          y = fromMaybe 0.0 (Array.index frame 1)
          isOut = x < 0.0 || x > widthNum || y < 0.0 || y > heightNum
        in
          if isOut then count + 1 else count
      ) acc track
    ) 0 tracks

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

-- | Create an ATI-compatible trajectory from raw point data
createATITrajectory
  :: Array (Array { x :: Number, y :: Number })
  -> Int
  -> Int
  -> Int
  -> WanMoveTrajectory
createATITrajectory points width height fps =
  let
    numPoints = Array.length points
    numFrames = case Array.head points of
      Just firstTrack -> Array.length firstTrack
      Nothing -> 0

    -- Convert to WanMove format
    tracks = map (map \pt -> [pt.x, pt.y]) points
  in
    { tracks
    , width
    , height
    , frameCount: numFrames
    }
