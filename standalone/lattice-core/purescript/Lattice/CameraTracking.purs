-- | Lattice.CameraTracking - Camera tracking data import types
-- |
-- | Source: ui/src/types/cameraTracking.ts (297 lines)
-- |
-- | Camera tracking data types for COLMAP and Blender format imports.

module Lattice.CameraTracking
  ( CoordinateSystem(..)
  , SolveQuality(..)
  , TrackPointState(..)
  , TrackPoint2D
  , TrackPoint3D
  , CameraIntrinsics
  , CameraPose
  , GroundPlane
  , CameraTrackingSolve
  , COLMAPCameraModel(..)
  , COLMAPCameraEntry
  , COLMAPImageEntry
  , COLMAPPoint3DEntry
  , BlenderTrackingMarker
  , BlenderTrackingTrack
  , BlenderCameraSolveData
  ) where

import Prelude
import Data.Maybe (Maybe)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives (NonEmptyString, FrameNumber, FiniteFloat, UnitFloat, PositiveFloat, NonNegativeFloat)

-- | Camera tracking coordinate system
data CoordinateSystem
  = CSBlender    -- ^ Right-handed, Z-up
  | CSOpenGL     -- ^ Right-handed, Y-up
  | CSUnity      -- ^ Left-handed, Y-up
  | CSUnreal     -- ^ Left-handed, Z-up

derive instance Eq CoordinateSystem
derive instance Generic CoordinateSystem _
instance Show CoordinateSystem where show = genericShow

-- | Tracking solve quality
data SolveQuality
  = SQPoor
  | SQFair
  | SQGood
  | SQExcellent

derive instance Eq SolveQuality
derive instance Ord SolveQuality
derive instance Generic SolveQuality _
instance Show SolveQuality where show = genericShow

-- | Track point state
data TrackPointState
  = TPSTracked
  | TPSInterpolated
  | TPSKeyframed
  | TPSLost

derive instance Eq TrackPointState
derive instance Generic TrackPointState _
instance Show TrackPointState where show = genericShow

-- | 2D track point (normalized coordinates)
type TrackPoint2D =
  { frame      :: FrameNumber
  , x          :: UnitFloat       -- ^ 0-1 normalized
  , y          :: UnitFloat       -- ^ 0-1 normalized
  , confidence :: UnitFloat       -- ^ 0-1
  , state      :: TrackPointState
  }

-- | 3D track point in world space
type TrackPoint3D =
  { x                :: FiniteFloat
  , y                :: FiniteFloat
  , z                :: FiniteFloat
  , reprojectionError :: NonNegativeFloat  -- ^ Pixels
  }

-- | Camera intrinsic parameters
type CameraIntrinsics =
  { focalLengthX    :: PositiveFloat   -- ^ Pixels
  , focalLengthY    :: PositiveFloat   -- ^ Pixels
  , principalPointX :: FiniteFloat     -- ^ Pixels
  , principalPointY :: FiniteFloat     -- ^ Pixels
  , skew            :: FiniteFloat     -- ^ Usually 0
  -- Distortion coefficients
  , k1              :: FiniteFloat
  , k2              :: FiniteFloat
  , k3              :: FiniteFloat
  , k4              :: FiniteFloat
  , k5              :: FiniteFloat
  , k6              :: FiniteFloat
  , p1              :: FiniteFloat
  , p2              :: FiniteFloat
  -- Image dimensions
  , imageWidth      :: Int             -- ^ > 0
  , imageHeight     :: Int             -- ^ > 0
  }

-- | Camera pose (rotation quaternion + translation)
type CameraPose =
  { frame        :: FrameNumber
  -- Rotation quaternion (w, x, y, z)
  , rotationW    :: FiniteFloat
  , rotationX    :: FiniteFloat
  , rotationY    :: FiniteFloat
  , rotationZ    :: FiniteFloat
  -- Translation
  , translationX :: FiniteFloat
  , translationY :: FiniteFloat
  , translationZ :: FiniteFloat
  }

-- | Ground plane definition
type GroundPlane =
  { normalX   :: FiniteFloat  -- ^ Unit normal X
  , normalY   :: FiniteFloat  -- ^ Unit normal Y
  , normalZ   :: FiniteFloat  -- ^ Unit normal Z
  , distance  :: FiniteFloat  -- ^ Distance from origin
  , originX   :: FiniteFloat  -- ^ Origin point X
  , originY   :: FiniteFloat  -- ^ Origin point Y
  , originZ   :: FiniteFloat  -- ^ Origin point Z
  }

-- | Complete camera tracking solve
type CameraTrackingSolve =
  { id                     :: NonEmptyString
  , name                   :: NonEmptyString
  , coordinateSystem       :: CoordinateSystem
  , intrinsics             :: CameraIntrinsics
  , poses                  :: Array CameraPose
  , trackPoints2D          :: Array (Array TrackPoint2D)
  , trackPoints3D          :: Array TrackPoint3D
  , solveQuality           :: SolveQuality
  , reprojectionErrorMean  :: NonNegativeFloat
  , reprojectionErrorMax   :: NonNegativeFloat
  , groundPlane            :: Maybe GroundPlane
  , sceneScale             :: PositiveFloat  -- ^ Units per meter
  , startFrame             :: FrameNumber
  , endFrame               :: FrameNumber
  }

-- ────────────────────────────────────────────────────────────────────────────
--                                                               // colmap // f
-- ────────────────────────────────────────────────────────────────────────────

-- | COLMAP camera model
data COLMAPCameraModel
  = CMSimplePinhole
  | CMPinhole
  | CMSimpleRadial
  | CMRadial
  | CMOpenCV
  | CMOpenCVFisheye
  | CMFullOpenCV
  | CMFOV
  | CMSimpleRadialFisheye
  | CMRadialFisheye
  | CMThinPrismFisheye

derive instance Eq COLMAPCameraModel
derive instance Generic COLMAPCameraModel _
instance Show COLMAPCameraModel where show = genericShow

-- | COLMAP camera entry
type COLMAPCameraEntry =
  { cameraId :: Int
  , model    :: COLMAPCameraModel
  , width    :: Int               -- ^ > 0
  , height   :: Int               -- ^ > 0
  , params   :: Array Number      -- ^ Model-dependent parameters
  }

-- | COLMAP image entry
type COLMAPImageEntry =
  { imageId      :: Int
  , quaternionW  :: Number
  , quaternionX  :: Number
  , quaternionY  :: Number
  , quaternionZ  :: Number
  , translationX :: Number
  , translationY :: Number
  , translationZ :: Number
  , cameraIdRef  :: Int
  , imageName    :: NonEmptyString
  , points2D     :: Array { x :: Number, y :: Number, point3DId :: Int }
  }

-- | COLMAP 3D point entry
type COLMAPPoint3DEntry =
  { point3DId :: Int
  , x         :: Number
  , y         :: Number
  , z         :: Number
  , r         :: Int    -- ^ 0-255
  , g         :: Int    -- ^ 0-255
  , b         :: Int    -- ^ 0-255
  , error     :: Number
  , trackIds  :: Array { imageId :: Int, point2DIdx :: Int }
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Blender Format Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Blender tracking marker
type BlenderTrackingMarker =
  { frame     :: FrameNumber
  , coX       :: Number   -- ^ Corner X (normalized)
  , coY       :: Number   -- ^ Corner Y (normalized)
  , isEnabled :: Boolean
  }

-- | Blender tracking track
type BlenderTrackingTrack =
  { name      :: NonEmptyString
  , markers   :: Array BlenderTrackingMarker
  , hasBundle :: Boolean
  , bundleX   :: Maybe Number
  , bundleY   :: Maybe Number
  , bundleZ   :: Maybe Number
  }

-- | Blender camera solve data
type BlenderCameraSolveData =
  { focalLength     :: PositiveFloat    -- ^ mm
  , sensorWidth     :: PositiveFloat    -- ^ mm
  , sensorHeight    :: PositiveFloat    -- ^ mm
  , principalPointX :: FiniteFloat      -- ^ Normalized offset
  , principalPointY :: FiniteFloat      -- ^ Normalized offset
  , k1              :: FiniteFloat
  , k2              :: FiniteFloat
  , k3              :: FiniteFloat
  , tracks          :: Array BlenderTrackingTrack
  }
