-- | Lattice.Services.Export.VACE.Exporter - VACE control exporter
-- |
-- | Renders control videos for VACE and similar motion-controllable systems.
-- | Uses arc-length parameterization for consistent speed along paths.
-- |
-- | Source: ui/src/services/export/vaceControlExport.ts

module Lattice.Services.Export.VACE.Exporter
  ( -- * Exporter Handle
    VACEExporterHandle
  , PathFollowerHandle
    -- * Canvas Handle
  , CanvasHandle
    -- * Path Follower Operations
  , createPathFollower
  , getStateAtFrame
  , getPathLength
  , getPathSpeed
    -- * Exporter Operations
  , createExporter
  , renderFrame
  , renderAllFrames
  , getFrameCount
  , getPathStats
  , exportToImageDataArray
    -- * Utility Functions
  , calculateDurationForSpeed
  , calculateSpeed
  , splineLayerToPathFollower
    -- * Easing Functions
  , applyEasing
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Data.Maybe (Maybe(..))
import Data.Int (toNumber, floor)
import Data.Number (ceil)

import Lattice.Services.Export.VACE.Types
  ( PathFollowerConfig
  , VACEExportConfig
  , PathFollowerState
  , VACEFrame
  , PathStats
  , PathFollowerEasing(..)
  , SplineControlPoint
  )

--------------------------------------------------------------------------------
-- FFI Types
--------------------------------------------------------------------------------

-- | Opaque path follower handle
foreign import data PathFollowerHandle :: Type

-- | Opaque VACE exporter handle
foreign import data VACEExporterHandle :: Type

-- | Opaque canvas handle
foreign import data CanvasHandle :: Type

-- | Opaque ImageData handle
foreign import data ImageDataHandle :: Type

--------------------------------------------------------------------------------
-- Path Follower Operations
--------------------------------------------------------------------------------

-- | Create a new path follower
foreign import createPathFollowerImpl :: PathFollowerConfig -> Effect PathFollowerHandle

createPathFollower :: PathFollowerConfig -> Effect PathFollowerHandle
createPathFollower = createPathFollowerImpl

-- | Get state at a specific frame
foreign import getStateAtFrameImpl :: PathFollowerHandle -> Int -> Effect PathFollowerState

getStateAtFrame :: PathFollowerHandle -> Int -> Effect PathFollowerState
getStateAtFrame = getStateAtFrameImpl

-- | Get path length
foreign import getPathLength :: PathFollowerHandle -> Effect Number

-- | Get path speed (pixels per frame)
foreign import getPathSpeed :: PathFollowerHandle -> Effect Number

--------------------------------------------------------------------------------
-- Exporter Operations
--------------------------------------------------------------------------------

-- | Create a new VACE exporter
foreign import createExporterImpl :: VACEExportConfig -> Effect VACEExporterHandle

createExporter :: VACEExportConfig -> Effect VACEExporterHandle
createExporter = createExporterImpl

-- | Render a single frame
foreign import renderFrameImpl :: VACEExporterHandle -> Int -> Effect { frameNumber :: Int, canvas :: CanvasHandle, states :: Array { id :: String, state :: PathFollowerState } }

renderFrame :: VACEExporterHandle -> Int -> Effect { frameNumber :: Int, canvas :: CanvasHandle, states :: Array { id :: String, state :: PathFollowerState } }
renderFrame = renderFrameImpl

-- | Render all frames (returns generator-like structure)
foreign import renderAllFramesImpl :: VACEExporterHandle -> EffectFnAff (Array { frameNumber :: Int, canvas :: CanvasHandle, states :: Array { id :: String, state :: PathFollowerState } })

renderAllFrames :: VACEExporterHandle -> Aff (Array { frameNumber :: Int, canvas :: CanvasHandle, states :: Array { id :: String, state :: PathFollowerState } })
renderAllFrames handle = fromEffectFnAff (renderAllFramesImpl handle)

-- | Get frame count
foreign import getFrameCount :: VACEExporterHandle -> Effect Int

-- | Get path statistics for all followers
foreign import getPathStats :: VACEExporterHandle -> Effect (Array PathStats)

-- | Export to ImageData array
foreign import exportToImageDataArrayImpl :: VACEExporterHandle -> EffectFnAff (Array ImageDataHandle)

exportToImageDataArray :: VACEExporterHandle -> Aff (Array ImageDataHandle)
exportToImageDataArray handle = fromEffectFnAff (exportToImageDataArrayImpl handle)

--------------------------------------------------------------------------------
-- Utility Functions
--------------------------------------------------------------------------------

-- | Calculate duration needed for a specific speed (pixels per frame)
calculateDurationForSpeed :: Number -> Number -> Int
calculateDurationForSpeed pathLength pixelsPerFrame =
  floor (ceil (pathLength / pixelsPerFrame))

-- | Calculate speed given path length and duration
calculateSpeed :: Number -> Int -> Number
calculateSpeed pathLength durationFrames =
  if durationFrames > 0
  then pathLength / toNumber durationFrames
  else 0.0

-- | Convert SplineLayer data to PathFollowerConfig (partial, needs additional fields)
splineLayerToPathFollower
  :: String
  -> Array SplineControlPoint
  -> Boolean
  -> Int
  -> { shape :: String, size :: { width :: Number, height :: Number } }
  -> PathFollowerConfig
splineLayerToPathFollower layerId controlPoints closed totalFrames opts =
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
  , loopMode: Lattice.Services.Export.VACE.Types.LoopRestart
  , scaleStart: 1.0
  , scaleEnd: 1.0
  , opacityStart: 1.0
  , opacityEnd: 1.0
  }

-- | Convert string to shape (internal helper)
stringToShape :: String -> Lattice.Services.Export.VACE.Types.PathFollowerShape
stringToShape = case _ of
  "circle" -> Lattice.Services.Export.VACE.Types.ShapeCircle
  "square" -> Lattice.Services.Export.VACE.Types.ShapeSquare
  "triangle" -> Lattice.Services.Export.VACE.Types.ShapeTriangle
  "diamond" -> Lattice.Services.Export.VACE.Types.ShapeDiamond
  "arrow" -> Lattice.Services.Export.VACE.Types.ShapeArrow
  _ -> Lattice.Services.Export.VACE.Types.ShapeCircle

--------------------------------------------------------------------------------
-- Easing Functions (Pure)
--------------------------------------------------------------------------------

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
