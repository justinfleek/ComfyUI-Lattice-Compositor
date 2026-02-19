-- | Lattice.Services.Export.CameraExport.Types - Camera export types
-- |
-- | Types for camera export including interpolated state, motion analysis,
-- | and various export format configurations.
-- |
-- | Source: ui/src/services/export/cameraExportFormats.ts

module Lattice.Services.Export.CameraExport.Types
  ( -- * Core Types
    InterpolatedCamera
  , Vec3
    -- * Motion Analysis
  , CameraMotionAnalysis
  , PanDirection(..)
  , ZoomDirection(..)
  , OrbitDirection(..)
    -- * Export Targets
  , ExportTarget(..)
    -- * MotionCtrl Types
  , MotionCtrlPose
  , MotionCtrlCameraData
  , MotionCtrlSVDPreset(..)
  , MotionCtrlSVDCameraData
    -- * Wan 2.2 Types
  , Wan22CameraMotion(..)
  , Wan22FunCameraData
    -- * Uni3C Types
  , Uni3CTrajType(..)
  , Uni3CCameraTrajectory
  , Uni3CCameraData
    -- * CameraCtrl Types
  , CameraCtrlMotionType(..)
  , CameraCtrlPoses
  , CameraCtrlPoseEntry
    -- * Full Export Types
  , FullCameraFrame
  , FullCameraExport
  , CameraExportMetadata
    -- * Defaults
  , defaultInterpolatedCamera
  , defaultMotionAnalysis
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Eq.Generic (genericEq)
import Data.Argonaut.Encode (class EncodeJson)
import Data.Argonaut.Encode.Generic (genericEncodeJson)

-- ────────────────────────────────────────────────────────────────────────────
-- Core Types
-- ────────────────────────────────────────────────────────────────────────────

-- | 3D vector type
type Vec3 = { x :: Number, y :: Number, z :: Number }

-- | Interpolated camera state at a specific frame
type InterpolatedCamera =
  { position :: Vec3
  , rotation :: Vec3
  , focalLength :: Number
  , zoom :: Number
  , focusDistance :: Number
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Motion Analysis Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Pan direction
data PanDirection = PanUp | PanDown | PanLeft | PanRight

derive instance Generic PanDirection _
instance Show PanDirection where show = genericShow
instance Eq PanDirection where eq = genericEq

-- | Zoom direction
data ZoomDirection = ZoomIn | ZoomOut

derive instance Generic ZoomDirection _
instance Show ZoomDirection where show = genericShow
instance Eq ZoomDirection where eq = genericEq

-- | Orbit direction
data OrbitDirection = OrbitLeft | OrbitRight

derive instance Generic OrbitDirection _
instance Show OrbitDirection where show = genericShow
instance Eq OrbitDirection where eq = genericEq

-- | Camera motion analysis result
type CameraMotionAnalysis =
  { hasPan :: Boolean
  , panDirection :: Maybe PanDirection
  , panMagnitude :: Number
  , hasZoom :: Boolean
  , zoomDirection :: Maybe ZoomDirection
  , zoomMagnitude :: Number
  , hasOrbit :: Boolean
  , orbitDirection :: Maybe OrbitDirection
  , orbitMagnitude :: Number
  , hasRotation :: Boolean
  , rotationMagnitude :: Number
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Export Target Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Camera export target format
data ExportTarget
  = TargetMotionCtrl
  | TargetMotionCtrlSVD
  | TargetWan22FunCamera
  | TargetUni3CCamera
  | TargetUni3CMotion
  | TargetAnimateDiffCameraCtrl
  | TargetFullMatrices
  | TargetControlNetDepth
  | TargetControlNetNormal
  | TargetWanMove
  | TargetWanCamera
  | TargetCogVideoX
  | TargetCustom String

derive instance Generic ExportTarget _
instance Show ExportTarget where show = genericShow
instance Eq ExportTarget where eq = genericEq
instance EncodeJson ExportTarget where encodeJson = genericEncodeJson

-- ────────────────────────────────────────────────────────────────────────────
-- MotionCtrl Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Single MotionCtrl pose (4x4 RT matrix)
type MotionCtrlPose =
  { rt :: Array (Array Number)  -- 4x4 matrix
  }

-- | MotionCtrl camera data
type MotionCtrlCameraData =
  { cameraPoses :: Array MotionCtrlPose
  }

-- | MotionCtrl-SVD preset
data MotionCtrlSVDPreset
  = SVDStatic
  | SVDZoomIn
  | SVDZoomOut
  | SVDRotateCW
  | SVDRotateCCW
  | SVDPanLeft
  | SVDPanRight
  | SVDPanUp
  | SVDPanDown

derive instance Generic MotionCtrlSVDPreset _
instance Show MotionCtrlSVDPreset where show = genericShow
instance Eq MotionCtrlSVDPreset where eq = genericEq

-- | MotionCtrl-SVD camera data
type MotionCtrlSVDCameraData =
  { motionCamera :: MotionCtrlSVDPreset
  , cameraPoses :: Maybe String  -- JSON string of poses
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Wan 2.2 Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Wan 2.2 Fun Camera motion presets
data Wan22CameraMotion
  = Wan22Static
  | Wan22PanUp
  | Wan22PanDown
  | Wan22PanLeft
  | Wan22PanRight
  | Wan22ZoomIn
  | Wan22ZoomOut
  | Wan22OrbitalLeft
  | Wan22OrbitalRight
  | Wan22PanUpZoomIn
  | Wan22PanUpZoomOut
  | Wan22PanDownZoomIn
  | Wan22PanDownZoomOut
  | Wan22PanLeftZoomIn
  | Wan22PanLeftZoomOut
  | Wan22PanRightZoomIn
  | Wan22PanRightZoomOut

derive instance Generic Wan22CameraMotion _
instance Show Wan22CameraMotion where show = genericShow
instance Eq Wan22CameraMotion where eq = genericEq

-- | Wan 2.2 Fun Camera data
type Wan22FunCameraData =
  { cameraMotion :: Wan22CameraMotion
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Uni3C Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Uni3C trajectory type
data Uni3CTrajType
  = Uni3COrbit
  | Uni3CFree1
  | Uni3CFree2
  | Uni3CCustom

derive instance Generic Uni3CTrajType _
instance Show Uni3CTrajType where show = genericShow
instance Eq Uni3CTrajType where eq = genericEq

-- | Uni3C camera trajectory point
type Uni3CCameraTrajectory =
  { zoom :: Number
  , xOffset :: Number
  , yOffset :: Number
  , zOffset :: Number
  , pitch :: Number
  , yaw :: Number
  , roll :: Number
  }

-- | Uni3C camera data
type Uni3CCameraData =
  { trajType :: Uni3CTrajType
  , customTrajectory :: Maybe (Array Uni3CCameraTrajectory)
  }

-- ────────────────────────────────────────────────────────────────────────────
-- CameraCtrl Types
-- ────────────────────────────────────────────────────────────────────────────

-- | AnimateDiff CameraCtrl motion type
data CameraCtrlMotionType
  = CameraCtrlStatic
  | CameraCtrlMoveForward
  | CameraCtrlMoveBackward
  | CameraCtrlMoveLeft
  | CameraCtrlMoveRight
  | CameraCtrlMoveUp
  | CameraCtrlMoveDown
  | CameraCtrlRotateLeft
  | CameraCtrlRotateRight
  | CameraCtrlRotateUp
  | CameraCtrlRotateDown
  | CameraCtrlRollLeft
  | CameraCtrlRollRight

derive instance Generic CameraCtrlMotionType _
instance Show CameraCtrlMotionType where show = genericShow
instance Eq CameraCtrlMotionType where eq = genericEq

-- | AnimateDiff CameraCtrl poses output
type CameraCtrlPoses =
  { motionType :: CameraCtrlMotionType
  , speed :: Int
  , frameLength :: Int
  }

-- | CameraCtrl pose entry
-- | Format: [time, fx, fy, cx, cy, aspect, 0, 0, w2c[0..11]]
type CameraCtrlPoseEntry = Array Number

-- ────────────────────────────────────────────────────────────────────────────
-- Full Export Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Full camera frame with matrices
type FullCameraFrame =
  { frame :: Int
  , timestamp :: Number
  , viewMatrix :: Array (Array Number)
  , projectionMatrix :: Array (Array Number)
  , position :: Array Number  -- [x, y, z]
  , rotation :: Array Number  -- [rx, ry, rz]
  , fov :: Number
  , focalLength :: Number
  , focusDistance :: Number
  }

-- | Camera export metadata
type CameraExportMetadata =
  { width :: Int
  , height :: Int
  , fps :: Number
  , totalFrames :: Int
  , cameraType :: String
  , filmSize :: Number
  }

-- | Full camera export
type FullCameraExport =
  { frames :: Array FullCameraFrame
  , metadata :: CameraExportMetadata
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Defaults
-- ────────────────────────────────────────────────────────────────────────────

-- | Default interpolated camera
defaultInterpolatedCamera :: InterpolatedCamera
defaultInterpolatedCamera =
  { position: { x: 0.0, y: 0.0, z: 0.0 }
  , rotation: { x: 0.0, y: 0.0, z: 0.0 }
  , focalLength: 50.0
  , zoom: 1.0
  , focusDistance: 1000.0
  }

-- | Default motion analysis (no motion detected)
defaultMotionAnalysis :: CameraMotionAnalysis
defaultMotionAnalysis =
  { hasPan: false
  , panDirection: Nothing
  , panMagnitude: 0.0
  , hasZoom: false
  , zoomDirection: Nothing
  , zoomMagnitude: 0.0
  , hasOrbit: false
  , orbitDirection: Nothing
  , orbitMagnitude: 0.0
  , hasRotation: false
  , rotationMagnitude: 0.0
  }
