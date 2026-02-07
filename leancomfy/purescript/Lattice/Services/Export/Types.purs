-- | Lattice.Services.Export.Types - Export service types
-- |
-- | Pure types for video/image export pipelines.
-- | Depth maps, pose data, motion trajectories, video encoding.
-- |
-- | Source: ui/src/services/export/

module Lattice.Services.Export.Types
  ( -- * Core Export Types
    ExportPipelineOptions
  , RenderedFrame
  , ExportProgress
  , ExportResult(..)
    -- * Depth Types
  , DepthFormat(..)
  , DepthGenerationOptions
  , DepthGenerationResult
  , DepthMetadata
    -- * Normal Types
  , NormalGenerationOptions
  , NormalGenerationResult
    -- * Pose Types
  , PoseExportConfig
  , PoseExportResult
  , PoseFrame
  , PoseSequence
  , OpenPoseJSON
    -- * Trajectory Types
  , TrackPoint
  , PointTrajectory
  , WanMoveTrajectory
  , WanMoveTrajectoryExport
  , ATIExportResult
  , ATITrackPoint
    -- * Flow Generation
  , GenerativeFlowConfig
  , GenerativeFlowParams
  , FlowLayer
  , ForceFieldConfig
  , ForcePoint
  , AttractorConfig
    -- * Color Mapping
  , ColoredTrajectory
  , ColorGradient
    -- * Video Encoding
  , VideoEncoderConfig
  , EncodedVideo
  , EncodingProgress
    -- * VACE Control
  , VACEExportConfig
  , VACEFrame
  , PathFollowerConfig
  , PathFollowerState
  , PathFollowerShape(..)
  , PathFollowerEasing(..)
    -- * Mesh Deform
  , CompositionInfo
  , MeshMaskExport
    -- * Camera Export
  , CameraMatrix4x4
  , CameraTrajectoryExport
  , CameraCtrlPoseEntry
  , Uni3CFrame
  , Uni3CTrack
    -- * Model Targets
  , ModelTarget(..)
  , UnifiedExportOptions
  , UnifiedExportResult
  ) where

import Prelude
import Data.Maybe (Maybe)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Eq.Generic (genericEq)

--------------------------------------------------------------------------------
-- Core Export Types
--------------------------------------------------------------------------------

-- | Pipeline export options
type ExportPipelineOptions =
  { width :: Int
  , height :: Int
  , frameRate :: Int
  , startFrame :: Int
  , endFrame :: Int
  , format :: String
  , quality :: Number
  , includeAudio :: Boolean
  }

-- | A single rendered frame
type RenderedFrame =
  { frameNumber :: Int
  , timestamp :: Number
  , imageData :: String  -- Base64 or URL
  , width :: Int
  , height :: Int
  }

-- | Export progress
type ExportProgress =
  { currentFrame :: Int
  , totalFrames :: Int
  , percentage :: Number
  , stage :: String
  , elapsedMs :: Number
  , estimatedRemainingMs :: Maybe Number
  }

-- | Export result
data ExportResult a
  = ExportSuccess a
  | ExportFailure String
  | ExportCancelled

derive instance Generic (ExportResult a) _
instance Show a => Show (ExportResult a) where show = genericShow
instance Eq a => Eq (ExportResult a) where eq = genericEq

--------------------------------------------------------------------------------
-- Depth Types
--------------------------------------------------------------------------------

-- | Depth output format
data DepthFormat
  = DepthGrayscale16
  | DepthGrayscale8
  | DepthNormalized
  | DepthRaw

derive instance Generic DepthFormat _
instance Show DepthFormat where show = genericShow
instance Eq DepthFormat where eq = genericEq

-- | Options for depth generation
type DepthGenerationOptions =
  { model :: String
  , precision :: String
  , normalize :: Boolean
  , invert :: Boolean
  , colormap :: Maybe String
  }

-- | Result of depth generation
type DepthGenerationResult =
  { success :: Boolean
  , depthMap :: Maybe String  -- Base64
  , width :: Int
  , height :: Int
  , minDepth :: Number
  , maxDepth :: Number
  , error :: Maybe String
  }

-- | Depth sequence metadata
type DepthMetadata =
  { frameCount :: Int
  , width :: Int
  , height :: Int
  , minDepth :: Number
  , maxDepth :: Number
  , format :: DepthFormat
  }

--------------------------------------------------------------------------------
-- Normal Types
--------------------------------------------------------------------------------

-- | Options for normal map generation
type NormalGenerationOptions =
  { model :: String
  , precision :: String
  , normalize :: Boolean
  }

-- | Result of normal generation
type NormalGenerationResult =
  { success :: Boolean
  , normalMap :: Maybe String  -- Base64
  , width :: Int
  , height :: Int
  , error :: Maybe String
  }

--------------------------------------------------------------------------------
-- Pose Types
--------------------------------------------------------------------------------

-- | Pose export configuration
type PoseExportConfig =
  { includeHands :: Boolean
  , includeFace :: Boolean
  , format :: String  -- "openpose" | "mediapipe" | "dwpose"
  , resolution :: { width :: Int, height :: Int }
  , confidence :: Number
  }

-- | Pose export result
type PoseExportResult =
  { success :: Boolean
  , frames :: Array PoseFrame
  , format :: String
  , error :: Maybe String
  }

-- | A single pose frame
type PoseFrame =
  { frameNumber :: Int
  , people :: Array OpenPoseJSON
  , canvas :: Maybe String  -- Base64 rendered pose
  }

-- | Pose sequence
type PoseSequence =
  { frames :: Array PoseFrame
  , width :: Int
  , height :: Int
  , frameRate :: Int
  }

-- | OpenPose JSON format
type OpenPoseJSON =
  { pose_keypoints_2d :: Array Number
  , face_keypoints_2d :: Maybe (Array Number)
  , hand_left_keypoints_2d :: Maybe (Array Number)
  , hand_right_keypoints_2d :: Maybe (Array Number)
  }

--------------------------------------------------------------------------------
-- Trajectory Types
--------------------------------------------------------------------------------

-- | A single track point
type TrackPoint = { x :: Number, y :: Number }

-- | A point trajectory over time
type PointTrajectory =
  { points :: Array TrackPoint
  , startFrame :: Int
  , endFrame :: Int
  }

-- | Wan-Move trajectory format
type WanMoveTrajectory =
  { tracks :: Array (Array (Array Number))  -- [track][frame][x,y]
  , width :: Int
  , height :: Int
  , frameCount :: Int
  }

-- | Wan-Move trajectory export
type WanMoveTrajectoryExport =
  { tracks :: Array (Array TrackPoint)
  , visibility :: Maybe (Array (Array Boolean))
  , metadata :: { width :: Int, height :: Int, frames :: Int }
  }

-- | ATI export result
type ATIExportResult =
  { trajectories :: Array (Array ATITrackPoint)
  , frameCount :: Int
  , normalized :: Boolean
  }

-- | ATI track point
type ATITrackPoint =
  { x :: Number
  , y :: Number
  , visible :: Boolean
  }

--------------------------------------------------------------------------------
-- Flow Generation Types
--------------------------------------------------------------------------------

-- | Configuration for generative flow
type GenerativeFlowConfig =
  { flowType :: String  -- "spiral" | "vortex" | "wave" | etc.
  , pointCount :: Int
  , frameCount :: Int
  , width :: Int
  , height :: Int
  , seed :: Maybe Int
  }

-- | Parameters for flow generation
type GenerativeFlowParams =
  { speed :: Number
  , scale :: Number
  , turbulence :: Number
  , decay :: Number
  }

-- | A flow layer for composition
type FlowLayer =
  { trajectory :: WanMoveTrajectory
  , blendMode :: String
  , opacity :: Number
  }

-- | Force field configuration
type ForceFieldConfig =
  { forces :: Array ForcePoint
  , strength :: Number
  , falloff :: Number
  }

-- | A single force point
type ForcePoint =
  { x :: Number
  , y :: Number
  , strength :: Number
  , radius :: Number
  }

-- | Strange attractor configuration
type AttractorConfig =
  { type :: String  -- "lorenz" | "rossler" | "aizawa"
  , sigma :: Number
  , rho :: Number
  , beta :: Number
  , scale :: Number
  }

--------------------------------------------------------------------------------
-- Color Mapping
--------------------------------------------------------------------------------

-- | Colored trajectory
type ColoredTrajectory =
  { trajectory :: WanMoveTrajectory
  , colors :: Array String  -- Hex colors per track
  }

-- | Color gradient for trajectory visualization
type ColorGradient =
  { name :: String
  , stops :: Array { position :: Number, color :: String }
  }

--------------------------------------------------------------------------------
-- Video Encoding Types
--------------------------------------------------------------------------------

-- | Video encoder configuration
type VideoEncoderConfig =
  { codec :: String
  , width :: Int
  , height :: Int
  , frameRate :: Int
  , bitrate :: Int
  , keyFrameInterval :: Int
  }

-- | Encoded video result
type EncodedVideo =
  { blob :: String  -- URL or Base64
  , duration :: Number
  , size :: Int
  , codec :: String
  }

-- | Encoding progress
type EncodingProgress =
  { framesEncoded :: Int
  , totalFrames :: Int
  , percentage :: Number
  , bytesWritten :: Int
  }

--------------------------------------------------------------------------------
-- VACE Control Types
--------------------------------------------------------------------------------

-- | VACE export configuration
type VACEExportConfig =
  { resolution :: { width :: Int, height :: Int }
  , frameRate :: Int
  , frameCount :: Int
  , backgroundColor :: String
  }

-- | A single VACE frame
type VACEFrame =
  { frameNumber :: Int
  , shapes :: Array
      { path :: String  -- SVG path
      , fill :: String
      , stroke :: Maybe String
      , transform :: String
      }
  }

-- | Path follower configuration
type PathFollowerConfig =
  { speed :: Number
  , easing :: PathFollowerEasing
  , loop :: Boolean
  , pingPong :: Boolean
  }

-- | Path follower state
type PathFollowerState =
  { progress :: Number
  , position :: { x :: Number, y :: Number }
  , rotation :: Number
  , scale :: Number
  }

-- | Path follower shape types
data PathFollowerShape
  = ShapeCircle Number
  | ShapeRectangle Number Number
  | ShapeTriangle Number
  | ShapeCustomSVG String

derive instance Generic PathFollowerShape _
instance Show PathFollowerShape where show = genericShow
instance Eq PathFollowerShape where eq = genericEq

-- | Path follower easing
data PathFollowerEasing
  = EaseLinear
  | EaseInOut
  | EaseIn
  | EaseOut
  | EaseBounce

derive instance Generic PathFollowerEasing _
instance Show PathFollowerEasing where show = genericShow
instance Eq PathFollowerEasing where eq = genericEq

--------------------------------------------------------------------------------
-- Mesh Deform Types
--------------------------------------------------------------------------------

-- | Composition info for mesh export
type CompositionInfo =
  { width :: Int
  , height :: Int
  , frameRate :: Int
  , duration :: Number
  }

-- | Mesh mask export
type MeshMaskExport =
  { mask :: String  -- Base64
  , width :: Int
  , height :: Int
  , frameNumber :: Int
  }

--------------------------------------------------------------------------------
-- Camera Export Types
--------------------------------------------------------------------------------

-- | 4x4 camera matrix
type CameraMatrix4x4 = Array (Array Number)

-- | Camera trajectory export
type CameraTrajectoryExport =
  { matrices :: Array CameraMatrix4x4
  , frameCount :: Int
  , intrinsics :: { fx :: Number, fy :: Number, cx :: Number, cy :: Number }
  }

-- | CameraCtrl pose entry
type CameraCtrlPoseEntry =
  { rotation :: Array Number  -- 3x3 or quaternion
  , translation :: Array Number  -- 3D position
  , frame :: Int
  }

-- | Uni3C frame
type Uni3CFrame =
  { timestamp :: Number
  , rotation :: Array Number
  , translation :: Array Number
  , fov :: Number
  }

-- | Uni3C track
type Uni3CTrack =
  { frames :: Array Uni3CFrame
  , intrinsics :: { fx :: Number, fy :: Number, cx :: Number, cy :: Number }
  }

--------------------------------------------------------------------------------
-- Model Target Types
--------------------------------------------------------------------------------

-- | Supported model targets
data ModelTarget
  = TargetWanMove
  | TargetATI
  | TargetLightX
  | TargetTTM
  | TargetSCAIL
  | TargetCameraComfyUI
  | TargetMotionCtrl
  | TargetUni3C

derive instance Generic ModelTarget _
instance Show ModelTarget where show = genericShow
instance Eq ModelTarget where eq = genericEq

-- | Unified export options
type UnifiedExportOptions =
  { target :: ModelTarget
  , width :: Int
  , height :: Int
  , frameCount :: Int
  , frameRate :: Int
  , layers :: Array String  -- Layer IDs
  , splines :: Array String  -- Spline IDs
  , includeCamera :: Boolean
  , includeDepth :: Boolean
  }

-- | Unified export result
type UnifiedExportResult =
  { success :: Boolean
  , target :: ModelTarget
  , data :: Maybe WanMoveTrajectory
  , camera :: Maybe CameraTrajectoryExport
  , depth :: Maybe (Array String)  -- Base64 depth frames
  , error :: Maybe String
  }
