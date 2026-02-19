-- | Lattice.Services.Export.VACE.Exporter - VACE control exporter
-- |
-- | Pure request types for VACE control video rendering.
-- | All actual rendering is done by the Haskell backend via Bridge.
-- |
-- | Uses arc-length parameterization for consistent speed along paths.
-- |
-- | Source: ui/src/services/export/vaceControlExport.ts

module Lattice.Services.Export.VACE.Exporter
  ( -- * Request Types
    VACEExportRequest(..)
    -- * Request Builders
  , mkCreatePathFollowerRequest
  , mkCreateExporterRequest
  , mkRenderFrameRequest
  , mkRenderAllFramesRequest
  , mkExportToImageDataRequest
    -- * Pure Utility Functions
  , calculateDurationForSpeed
  , calculateSpeed
  , splineLayerToPathFollowerConfig
    -- * Easing Functions (Pure)
  , applyEasing
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Int (toNumber, floor, ceil) as Int
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Argonaut.Encode (class EncodeJson)
import Data.Argonaut.Encode.Generic (genericEncodeJson)

import Lattice.Services.Export.VACE.Types
  ( PathFollowerConfig
  , VACEExportConfig
  , PathFollowerState
  , VACEFrame
  , PathStats
  , PathFollowerEasing(..)
  , PathFollowerShape(..)
  , LoopMode(..)
  , SplineControlPoint
  )

-- ────────────────────────────────────────────────────────────────────────────
-- Request Types
-- ────────────────────────────────────────────────────────────────────────────

-- | VACE export request - sent to Haskell backend
data VACEExportRequest
  = CreatePathFollowerRequest PathFollowerConfig
  | GetStateAtFrameRequest
      { followerId :: String
      , frame :: Int
      }
  | GetPathLengthRequest
      { followerId :: String
      }
  | GetPathSpeedRequest
      { followerId :: String
      }
  | CreateExporterRequest VACEExportConfig
  | RenderFrameRequest
      { exporterId :: String
      , frameNumber :: Int
      }
  | RenderAllFramesRequest
      { exporterId :: String
      }
  | GetFrameCountRequest
      { exporterId :: String
      }
  | GetPathStatsRequest
      { exporterId :: String
      }
  | ExportToImageDataRequest
      { exporterId :: String
      }

derive instance Generic VACEExportRequest _
instance Show VACEExportRequest where show = genericShow
instance EncodeJson VACEExportRequest where
  encodeJson = genericEncodeJson

-- ────────────────────────────────────────────────────────────────────────────
-- Request Builders
-- ────────────────────────────────────────────────────────────────────────────

-- | Create path follower request
mkCreatePathFollowerRequest :: PathFollowerConfig -> VACEExportRequest
mkCreatePathFollowerRequest = CreatePathFollowerRequest

-- | Create exporter request
mkCreateExporterRequest :: VACEExportConfig -> VACEExportRequest
mkCreateExporterRequest = CreateExporterRequest

-- | Create render frame request
mkRenderFrameRequest :: String -> Int -> VACEExportRequest
mkRenderFrameRequest exporterId frameNumber =
  RenderFrameRequest { exporterId, frameNumber }

-- | Create render all frames request
mkRenderAllFramesRequest :: String -> VACEExportRequest
mkRenderAllFramesRequest exporterId =
  RenderAllFramesRequest { exporterId }

-- | Create export to image data request
mkExportToImageDataRequest :: String -> VACEExportRequest
mkExportToImageDataRequest exporterId =
  ExportToImageDataRequest { exporterId }

-- ────────────────────────────────────────────────────────────────────────────
-- Pure Utility Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate duration needed for a specific speed (pixels per frame)
calculateDurationForSpeed :: Number -> Number -> Int
calculateDurationForSpeed pathLength pixelsPerFrame =
  let
    raw = pathLength / pixelsPerFrame
  in
    -- Using ceil from Data.Int
    if raw > 0.0 then max 1 (Int.ceil raw) else 1

-- | Calculate speed given path length and duration
calculateSpeed :: Number -> Int -> Number
calculateSpeed pathLength durationFrames =
  if durationFrames > 0
  then pathLength / Int.toNumber durationFrames
  else 0.0

-- | Convert SplineLayer data to PathFollowerConfig
splineLayerToPathFollowerConfig
  :: String
  -> Array SplineControlPoint
  -> Boolean
  -> Int
  -> { shape :: String, size :: { width :: Number, height :: Number } }
  -> PathFollowerConfig
splineLayerToPathFollowerConfig layerId controlPoints closed totalFrames opts =
  { id: layerId
  , controlPoints
  , closed
  , shape: stringToShape opts.shape
  , size: opts.size
  , fillColor: "#FFFFFF"
  , strokeColor: Nothing
  , strokeWidth: Nothing
  , startFrame: 0
  , duration: totalFrames
  , easing: EaseInOut
  , alignToPath: true
  , rotationOffset: 0.0
  , loop: false
  , loopMode: LoopRestart
  , scaleStart: 1.0
  , scaleEnd: 1.0
  , opacityStart: 1.0
  , opacityEnd: 1.0
  }

-- | Convert string to shape (internal helper)
stringToShape :: String -> PathFollowerShape
stringToShape = case _ of
  "circle" -> ShapeCircle
  "square" -> ShapeSquare
  "triangle" -> ShapeTriangle
  "diamond" -> ShapeDiamond
  "arrow" -> ShapeArrow
  _ -> ShapeCircle

-- ────────────────────────────────────────────────────────────────────────────
-- Easing Functions (Pure)
-- ────────────────────────────────────────────────────────────────────────────

-- | Apply easing function to progress value
applyEasing :: PathFollowerEasing -> Number -> Number
applyEasing easing t = case easing of
  EaseLinear -> t
  EaseIn -> t * t
  EaseOut -> t * (2.0 - t)
  EaseInOut ->
    if t < 0.5
    then 2.0 * t * t
    else -1.0 + (4.0 - 2.0 * t) * t
  EaseInCubic -> t * t * t
  EaseOutCubic ->
    let t' = t - 1.0
    in t' * t' * t' + 1.0
