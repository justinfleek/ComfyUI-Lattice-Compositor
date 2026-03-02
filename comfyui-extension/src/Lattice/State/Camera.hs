-- |
-- Module      : Lattice.State.Camera
-- Description : Pure state management functions for camera store
-- 
-- Migrated from ui/src/stores/cameraStore.ts
-- Pure functions extracted from Pinia store - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Camera
  ( -- Helper functions
    framesEqual
  , safeFrame
  -- Query functions
  , allCameras
  , getCamera
  , getCameraKeyframes
  , activeCamera
  -- State types
  , CameraState(..)
  , CameraKeyframe(..)
  , ViewportState(..)
  , ViewOptions(..)
  ) where

import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , object
  , (.=)
  , (.:)
  , (.:?)
  )
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import GHC.Generics (Generic)
import Lattice.Types.LayerData3D (Camera3D(..))
import Lattice.Utils.NumericSafety (ensureFiniteD)

-- ============================================================================
-- CAMERA KEYFRAME (Minimal type for pure queries)
-- ============================================================================

-- | Camera keyframe for animation
-- Minimal type sufficient for pure query functions
-- Full type definition will be migrated in schema phase
data CameraKeyframe = CameraKeyframe
  { cameraKeyframeFrame :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON CameraKeyframe where
  toJSON (CameraKeyframe frame) =
    object ["frame" .= frame]

instance FromJSON CameraKeyframe where
  parseJSON = withObject "CameraKeyframe" $ \o -> do
    frame <- o .: "frame"
    return (CameraKeyframe frame)

-- ============================================================================
-- VIEWPORT STATE (Minimal type for pure queries)
-- ============================================================================

-- | Viewport state for 3D viewport management
-- Minimal type sufficient for pure query functions
-- Full type definition will be migrated in schema phase
data ViewportState = ViewportState
  { viewportStateLayout :: Text
  , viewportStateActiveViewIndex :: Int
  }
  deriving (Eq, Show, Generic)

instance ToJSON ViewportState where
  toJSON (ViewportState layout activeIndex) =
    object
      [ "layout" .= layout
      , "activeViewIndex" .= activeIndex
      ]

instance FromJSON ViewportState where
  parseJSON = withObject "ViewportState" $ \o -> do
    layout <- o .: "layout"
    activeIndex <- o .: "activeViewIndex"
    return (ViewportState layout activeIndex)

-- ============================================================================
-- VIEW OPTIONS (Minimal type for pure queries)
-- ============================================================================

-- | View options for 3D viewport display
-- Minimal type sufficient for pure query functions
-- Full type definition will be migrated in schema phase
data ViewOptions = ViewOptions
  { viewOptionsCameraWireframes :: Text
  , viewOptionsShowGrid :: Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON ViewOptions where
  toJSON (ViewOptions cameraWireframes showGrid) =
    object
      [ "cameraWireframes" .= cameraWireframes
      , "showGrid" .= showGrid
      ]

instance FromJSON ViewOptions where
  parseJSON = withObject "ViewOptions" $ \o -> do
    cameraWireframes <- o .: "cameraWireframes"
    showGrid <- o .: "showGrid"
    return (ViewOptions cameraWireframes showGrid)

-- ============================================================================
-- CAMERA STATE
-- ============================================================================

-- | Camera store state
data CameraState = CameraState
  { cameraStateCameras :: HashMap Text Camera3D
  , cameraStateCameraKeyframes :: HashMap Text [CameraKeyframe]
  , cameraStateActiveCameraId :: Maybe Text
  , cameraStateViewportState :: ViewportState
  , cameraStateViewOptions :: ViewOptions
  }
  deriving (Eq, Show, Generic)

instance ToJSON CameraState where
  toJSON (CameraState cameras keyframes activeId viewport viewOptions) =
    object
      [ "cameras" .= cameras
      , "cameraKeyframes" .= keyframes
      , "activeCameraId" .= activeId
      , "viewportState" .= viewport
      , "viewOptions" .= viewOptions
      ]

instance FromJSON CameraState where
  parseJSON = withObject "CameraState" $ \o -> do
    cameras <- o .: "cameras"
    keyframes <- o .: "cameraKeyframes"
    activeId <- o .:? "activeCameraId"
    viewport <- o .: "viewportState"
    viewOptions <- o .: "viewOptions"
    return (CameraState cameras keyframes activeId viewport viewOptions)

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- | Safely compare frame numbers, handling NaN values
-- Pure function: takes two frame numbers, returns boolean
framesEqual :: Double -> Double -> Bool
framesEqual a b =
  let finiteA = ensureFiniteD a 0.0
      finiteB = ensureFiniteD b 0.0
  in finiteA == finiteB && a == b

-- | Validate and sanitize frame number input
-- Pure function: takes optional frame and fallback, returns valid frame
safeFrame :: Maybe Double -> Double -> Double
safeFrame mFrame fallback =
  case mFrame of
    Nothing -> fallback
    Just frame -> ensureFiniteD frame fallback

-- ============================================================================
-- QUERY FUNCTIONS
-- ============================================================================

-- | Get all cameras as list
-- Pure function: takes camera map, returns list of cameras
allCameras :: HashMap Text Camera3D -> [Camera3D]
allCameras cameras = HM.elems cameras

-- | Get camera by ID
-- Pure function: takes camera ID and camera map, returns camera or Nothing
getCamera :: Text -> HashMap Text Camera3D -> Maybe Camera3D
getCamera cameraId cameras = HM.lookup cameraId cameras

-- | Get keyframes for camera
-- Pure function: takes camera ID and keyframe map, returns keyframes list
getCameraKeyframes :: Text -> HashMap Text [CameraKeyframe] -> [CameraKeyframe]
getCameraKeyframes cameraId keyframes =
  case HM.lookup cameraId keyframes of
    Nothing -> []
    Just kfs -> kfs

-- | Get active camera
-- Pure function: takes active camera ID and camera map, returns camera or Nothing
-- Note: TypeScript version throws error, but pure version returns Maybe
activeCamera :: Maybe Text -> HashMap Text Camera3D -> Maybe Camera3D
activeCamera mActiveId cameras =
  case mActiveId of
    Nothing -> Nothing
    Just activeId -> HM.lookup activeId cameras
