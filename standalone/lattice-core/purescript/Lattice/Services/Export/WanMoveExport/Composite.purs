-- | Lattice.Services.Export.WanMoveExport.Composite - Multi-layer composition
-- |
-- | Functions for compositing multiple flow layers into combined trajectories.
-- |
-- | Source: ui/src/services/export/wanMoveExport.ts

module Lattice.Services.Export.WanMoveExport.Composite
  ( -- * Composition
    compositeFlowLayers
  , compositeColoredLayers
  ) where

import Prelude
import Data.Array (length, concat, (!!))
import Data.Maybe (Maybe(..), fromMaybe)

import Lattice.Services.Export.WanMoveExport.Types
  ( WanMoveTrajectory
  , ColoredTrajectory
  , FlowLayer
  )

-- ────────────────────────────────────────────────────────────────────────────
-- Composition
-- ────────────────────────────────────────────────────────────────────────────

-- | Composite multiple flow layers into one trajectory
-- | Concatenates all tracks from all layers
compositeFlowLayers :: Array FlowLayer -> WanMoveTrajectory
compositeFlowLayers layers =
  case layers !! 0 of
    Nothing ->
      -- Empty layers - return empty trajectory
      { tracks: []
      , visibility: []
      , metadata: { numPoints: 0, numFrames: 0, width: 512, height: 512, fps: 16 }
      }
    Just firstLayer ->
      let
        firstMeta = firstLayer.trajectory.metadata

        -- Collect all tracks and visibility
        allTracks = concat (map (\l -> l.trajectory.tracks) layers)
        allVisibility = concat (map (\l -> l.trajectory.visibility) layers)
      in
        { tracks: allTracks
        , visibility: allVisibility
        , metadata:
            { numPoints: length allTracks
            , numFrames: firstMeta.numFrames
            , width: firstMeta.width
            , height: firstMeta.height
            , fps: firstMeta.fps
            }
        }

-- | Composite with color data preserved per layer
compositeColoredLayers :: Array FlowLayer -> ColoredTrajectory
compositeColoredLayers layers =
  let
    base = compositeFlowLayers layers

    -- Generate colors based on layer colors
    colors = concat (map (\layer ->
      let
        layerColor = fromMaybe { r: 255, g: 255, b: 255 } layer.color
      in
        map (\track ->
          map (\_ -> layerColor) track
        ) layer.trajectory.tracks
    ) layers)
  in
    { tracks: base.tracks
    , visibility: base.visibility
    , metadata: base.metadata
    , colors: Just colors
    , dataValues: Nothing
    , trailLength: Nothing
    }

