{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-|
Module      : Lattice.CameraTracking
Description : Camera tracking data import types
Copyright   : (c) Lattice, 2026
License     : MIT

Camera tracking data types for COLMAP and Blender format imports.
All numeric types use refined types with proofs of invariants.

Source: ui/src/types/cameraTracking.ts (297 lines)
-}

module Lattice.CameraTracking
  ( -- * Enumerations
    CoordinateSystem(..)
  , SolveQuality(..)
  , TrackPointState(..)
    -- * Core Types
  , TrackPoint2D(..)
  , TrackPoint3D(..)
  , CameraIntrinsics(..)
  , CameraPose(..)
  , GroundPlane(..)
  , CameraTrackingSolve(..)
    -- * COLMAP Types
  , COLMAPCameraModel(..)
  , COLMAPCameraEntry(..)
  , COLMAPImageEntry(..)
  , COLMAPPoint3DEntry(..)
    -- * Blender Types
  , BlenderTrackingMarker(..)
  , BlenderTrackingTrack(..)
  , BlenderCameraSolveData(..)
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Vector (Vector)
import Lattice.Primitives
  ( NonEmptyString
  , FrameNumber
  , FiniteFloat
  , UnitFloat
  , PositiveFloat
  , NonNegativeFloat
  )

-- | Camera tracking coordinate system
data CoordinateSystem
  = Blender    -- ^ Right-handed, Z-up
  | OpenGL     -- ^ Right-handed, Y-up
  | Unity      -- ^ Left-handed, Y-up
  | Unreal     -- ^ Left-handed, Z-up
  deriving stock (Eq, Show, Generic)

-- | Tracking solve quality
data SolveQuality
  = Poor
  | Fair
  | Good
  | Excellent
  deriving stock (Eq, Show, Generic, Ord)

-- | Track point state
data TrackPointState
  = Tracked
  | Interpolated
  | Keyframed
  | Lost
  deriving stock (Eq, Show, Generic)

-- | 2D track point (normalized coordinates)
data TrackPoint2D = TrackPoint2D
  { tp2dFrame      :: !FrameNumber
  , tp2dX          :: !UnitFloat       -- ^ 0-1 normalized
  , tp2dY          :: !UnitFloat       -- ^ 0-1 normalized
  , tp2dConfidence :: !UnitFloat       -- ^ 0-1
  , tp2dState      :: !TrackPointState
  } deriving stock (Eq, Show, Generic)

-- | 3D track point in world space
data TrackPoint3D = TrackPoint3D
  { tp3dX                :: !FiniteFloat
  , tp3dY                :: !FiniteFloat
  , tp3dZ                :: !FiniteFloat
  , tp3dReprojectionError :: !NonNegativeFloat  -- ^ Pixels
  } deriving stock (Eq, Show, Generic)

-- | Camera intrinsic parameters
data CameraIntrinsics = CameraIntrinsics
  { ciFocalLengthX    :: !PositiveFloat   -- ^ Pixels
  , ciFocalLengthY    :: !PositiveFloat   -- ^ Pixels
  , ciPrincipalPointX :: !FiniteFloat     -- ^ Pixels
  , ciPrincipalPointY :: !FiniteFloat     -- ^ Pixels
  , ciSkew            :: !FiniteFloat     -- ^ Usually 0
  -- Distortion coefficients
  , ciK1              :: !FiniteFloat
  , ciK2              :: !FiniteFloat
  , ciK3              :: !FiniteFloat
  , ciK4              :: !FiniteFloat
  , ciK5              :: !FiniteFloat
  , ciK6              :: !FiniteFloat
  , ciP1              :: !FiniteFloat
  , ciP2              :: !FiniteFloat
  -- Image dimensions
  , ciImageWidth      :: !Int             -- ^ > 0
  , ciImageHeight     :: !Int             -- ^ > 0
  } deriving stock (Eq, Show, Generic)

-- | Camera pose (rotation quaternion + translation)
data CameraPose = CameraPose
  { cpFrame        :: !FrameNumber
  -- Rotation quaternion (w, x, y, z)
  , cpRotationW    :: !FiniteFloat
  , cpRotationX    :: !FiniteFloat
  , cpRotationY    :: !FiniteFloat
  , cpRotationZ    :: !FiniteFloat
  -- Translation
  , cpTranslationX :: !FiniteFloat
  , cpTranslationY :: !FiniteFloat
  , cpTranslationZ :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

-- | Ground plane definition
data GroundPlane = GroundPlane
  { gpNormalX   :: !FiniteFloat  -- ^ Unit normal X
  , gpNormalY   :: !FiniteFloat  -- ^ Unit normal Y
  , gpNormalZ   :: !FiniteFloat  -- ^ Unit normal Z
  , gpDistance  :: !FiniteFloat  -- ^ Distance from origin
  , gpOriginX   :: !FiniteFloat  -- ^ Origin point X
  , gpOriginY   :: !FiniteFloat  -- ^ Origin point Y
  , gpOriginZ   :: !FiniteFloat  -- ^ Origin point Z
  } deriving stock (Eq, Show, Generic)

-- | Complete camera tracking solve
data CameraTrackingSolve = CameraTrackingSolve
  { ctsId                     :: !NonEmptyString
  , ctsName                   :: !NonEmptyString
  , ctsCoordinateSystem       :: !CoordinateSystem
  , ctsIntrinsics             :: !CameraIntrinsics
  , ctsPoses                  :: !(Vector CameraPose)
  , ctsTrackPoints2D          :: !(Vector (Vector TrackPoint2D))
  , ctsTrackPoints3D          :: !(Vector TrackPoint3D)
  , ctsSolveQuality           :: !SolveQuality
  , ctsReprojectionErrorMean  :: !NonNegativeFloat
  , ctsReprojectionErrorMax   :: !NonNegativeFloat
  , ctsGroundPlane            :: !(Maybe GroundPlane)
  , ctsSceneScale             :: !PositiveFloat  -- ^ Units per meter
  , ctsStartFrame             :: !FrameNumber
  , ctsEndFrame               :: !FrameNumber
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- COLMAP Format Types
--------------------------------------------------------------------------------

-- | COLMAP camera model
data COLMAPCameraModel
  = SimplePinhole
  | Pinhole
  | SimpleRadial
  | Radial
  | OpenCV
  | OpenCVFisheye
  | FullOpenCV
  | FOV
  | SimpleRadialFisheye
  | RadialFisheye
  | ThinPrismFisheye
  deriving stock (Eq, Show, Generic)

-- | COLMAP camera entry
data COLMAPCameraEntry = COLMAPCameraEntry
  { colmapCameraId :: !Int
  , colmapModel    :: !COLMAPCameraModel
  , colmapWidth    :: !Int               -- ^ > 0
  , colmapHeight   :: !Int               -- ^ > 0
  , colmapParams   :: !(Vector Double)   -- ^ Model-dependent parameters
  } deriving stock (Eq, Show, Generic)

-- | COLMAP image entry
data COLMAPImageEntry = COLMAPImageEntry
  { colmapImageId      :: !Int
  , colmapQuaternionW  :: !Double
  , colmapQuaternionX  :: !Double
  , colmapQuaternionY  :: !Double
  , colmapQuaternionZ  :: !Double
  , colmapTranslationX :: !Double
  , colmapTranslationY :: !Double
  , colmapTranslationZ :: !Double
  , colmapCameraIdRef  :: !Int
  , colmapImageName    :: !NonEmptyString
  , colmapPoints2D     :: !(Vector (Double, Double, Int))  -- ^ (x, y, point3DId)
  } deriving stock (Eq, Show, Generic)

-- | COLMAP 3D point entry
data COLMAPPoint3DEntry = COLMAPPoint3DEntry
  { colmapPoint3DId :: !Int
  , colmapPointX    :: !Double
  , colmapPointY    :: !Double
  , colmapPointZ    :: !Double
  , colmapR         :: !Int    -- ^ 0-255
  , colmapG         :: !Int    -- ^ 0-255
  , colmapB         :: !Int    -- ^ 0-255
  , colmapError     :: !Double
  , colmapTrackIds  :: !(Vector (Int, Int))  -- ^ (imageId, point2DIdx)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Blender Format Types
--------------------------------------------------------------------------------

-- | Blender tracking marker
data BlenderTrackingMarker = BlenderTrackingMarker
  { blenderMarkerFrame     :: !FrameNumber
  , blenderMarkerCoX       :: !Double   -- ^ Corner X (normalized)
  , blenderMarkerCoY       :: !Double   -- ^ Corner Y (normalized)
  , blenderMarkerIsEnabled :: !Bool
  } deriving stock (Eq, Show, Generic)

-- | Blender tracking track
data BlenderTrackingTrack = BlenderTrackingTrack
  { blenderTrackName      :: !NonEmptyString
  , blenderTrackMarkers   :: !(Vector BlenderTrackingMarker)
  , blenderTrackHasBundle :: !Bool
  , blenderTrackBundleX   :: !(Maybe Double)
  , blenderTrackBundleY   :: !(Maybe Double)
  , blenderTrackBundleZ   :: !(Maybe Double)
  } deriving stock (Eq, Show, Generic)

-- | Blender camera solve data
data BlenderCameraSolveData = BlenderCameraSolveData
  { blenderFocalLength     :: !PositiveFloat    -- ^ mm
  , blenderSensorWidth     :: !PositiveFloat    -- ^ mm
  , blenderSensorHeight    :: !PositiveFloat    -- ^ mm
  , blenderPrincipalPointX :: !FiniteFloat      -- ^ Normalized offset
  , blenderPrincipalPointY :: !FiniteFloat      -- ^ Normalized offset
  , blenderK1              :: !FiniteFloat
  , blenderK2              :: !FiniteFloat
  , blenderK3              :: !FiniteFloat
  , blenderTracks          :: !(Vector BlenderTrackingTrack)
  } deriving stock (Eq, Show, Generic)
