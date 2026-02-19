-- | Lattice.Schemas.Exports.CameraSchema - Camera export format enums and types
-- |
-- | Camera export format enums and types.
-- |
-- | Source: ui/src/schemas/exports/camera-schema.ts

module Lattice.Schemas.Exports.CameraSchema
  ( -- Camera Format
    CameraFormat(..)
  , cameraFormatFromString
  , cameraFormatToString
    -- Coordinate System
  , CoordinateSystem(..)
  , coordinateSystemFromString
  , coordinateSystemToString
    -- Euler Order
  , EulerOrder(..)
  , eulerOrderFromString
  , eulerOrderToString
    -- Camera Interpolation
  , CameraInterpolation(..)
  , cameraInterpolationFromString
  , cameraInterpolationToString
    -- Structures
  , Position3D
  , CameraIntrinsics
    -- Constants
  , maxFocalLength
  , maxSensorSize
  , maxFOV
  , maxAspectRatio
  , maxRotationDegrees
  , maxTimestamp
  , quaternionNormalizationTolerance
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- ────────────────────────────────────────────────────────────────────────────
-- Camera Format
-- ────────────────────────────────────────────────────────────────────────────

-- | Camera export format options
data CameraFormat
  = CameraMotionCtrl
  | CameraWanMove
  | CameraUni3C
  | CameraCameraCtrl
  | CameraBlender
  | CameraFBX

derive instance Eq CameraFormat
derive instance Generic CameraFormat _

instance Show CameraFormat where
  show = genericShow

cameraFormatFromString :: String -> Maybe CameraFormat
cameraFormatFromString = case _ of
  "motionctrl" -> Just CameraMotionCtrl
  "wan-move" -> Just CameraWanMove
  "uni3c" -> Just CameraUni3C
  "cameractrl" -> Just CameraCameraCtrl
  "blender" -> Just CameraBlender
  "fbx" -> Just CameraFBX
  _ -> Nothing

cameraFormatToString :: CameraFormat -> String
cameraFormatToString = case _ of
  CameraMotionCtrl -> "motionctrl"
  CameraWanMove -> "wan-move"
  CameraUni3C -> "uni3c"
  CameraCameraCtrl -> "cameractrl"
  CameraBlender -> "blender"
  CameraFBX -> "fbx"

-- ────────────────────────────────────────────────────────────────────────────
-- Coordinate System
-- ────────────────────────────────────────────────────────────────────────────

-- | Coordinate system conventions
data CoordinateSystem
  = CoordOpenGL   -- Y-up, right-handed
  | CoordOpenCV   -- Y-down, right-handed
  | CoordBlender  -- Z-up, right-handed
  | CoordUnity    -- Y-up, left-handed

derive instance Eq CoordinateSystem
derive instance Generic CoordinateSystem _

instance Show CoordinateSystem where
  show = genericShow

coordinateSystemFromString :: String -> Maybe CoordinateSystem
coordinateSystemFromString = case _ of
  "opengl" -> Just CoordOpenGL
  "opencv" -> Just CoordOpenCV
  "blender" -> Just CoordBlender
  "unity" -> Just CoordUnity
  _ -> Nothing

coordinateSystemToString :: CoordinateSystem -> String
coordinateSystemToString = case _ of
  CoordOpenGL -> "opengl"
  CoordOpenCV -> "opencv"
  CoordBlender -> "blender"
  CoordUnity -> "unity"

-- ────────────────────────────────────────────────────────────────────────────
-- Euler Order
-- ────────────────────────────────────────────────────────────────────────────

-- | Euler rotation order options
data EulerOrder
  = EulerXYZ
  | EulerYXZ
  | EulerZXY
  | EulerZYX
  | EulerXZY
  | EulerYZX

derive instance Eq EulerOrder
derive instance Generic EulerOrder _

instance Show EulerOrder where
  show = genericShow

eulerOrderFromString :: String -> Maybe EulerOrder
eulerOrderFromString = case _ of
  "XYZ" -> Just EulerXYZ
  "YXZ" -> Just EulerYXZ
  "ZXY" -> Just EulerZXY
  "ZYX" -> Just EulerZYX
  "XZY" -> Just EulerXZY
  "YZX" -> Just EulerYZX
  _ -> Nothing

eulerOrderToString :: EulerOrder -> String
eulerOrderToString = case _ of
  EulerXYZ -> "XYZ"
  EulerYXZ -> "YXZ"
  EulerZXY -> "ZXY"
  EulerZYX -> "ZYX"
  EulerXZY -> "XZY"
  EulerYZX -> "YZX"

-- ────────────────────────────────────────────────────────────────────────────
-- Camera Interpolation
-- ────────────────────────────────────────────────────────────────────────────

-- | Camera interpolation options
data CameraInterpolation
  = InterpLinear
  | InterpBezier
  | InterpSpline

derive instance Eq CameraInterpolation
derive instance Generic CameraInterpolation _

instance Show CameraInterpolation where
  show = genericShow

cameraInterpolationFromString :: String -> Maybe CameraInterpolation
cameraInterpolationFromString = case _ of
  "linear" -> Just InterpLinear
  "bezier" -> Just InterpBezier
  "spline" -> Just InterpSpline
  _ -> Nothing

cameraInterpolationToString :: CameraInterpolation -> String
cameraInterpolationToString = case _ of
  InterpLinear -> "linear"
  InterpBezier -> "bezier"
  InterpSpline -> "spline"

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | 3D position
type Position3D =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | Camera intrinsic parameters
type CameraIntrinsics =
  { focalLength :: Number
  , sensorWidth :: Maybe Number
  , sensorHeight :: Maybe Number
  , fov :: Number
  , aspectRatio :: Number
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxFocalLength :: Number
maxFocalLength = 10000.0

maxSensorSize :: Number
maxSensorSize = 100.0

maxFOV :: Number
maxFOV = 180.0

maxAspectRatio :: Number
maxAspectRatio = 10.0

maxRotationDegrees :: Number
maxRotationDegrees = 360.0

maxTimestamp :: Number
maxTimestamp = 86400.0

quaternionNormalizationTolerance :: Number
quaternionNormalizationTolerance = 0.1
