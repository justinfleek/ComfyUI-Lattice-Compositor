{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Exports.CameraSchema
Description : Camera export format enums and types
Copyright   : (c) Lattice, 2026
License     : MIT

Camera export format enums and types.

Source: ui/src/schemas/exports/camera-schema.ts
-}

module Lattice.Schemas.Exports.CameraSchema
  ( -- * Camera Format
    CameraFormat(..)
  , cameraFormatFromText
  , cameraFormatToText
    -- * Coordinate System
  , CoordinateSystem(..)
  , coordinateSystemFromText
  , coordinateSystemToText
    -- * Euler Order
  , EulerOrder(..)
  , eulerOrderFromText
  , eulerOrderToText
    -- * Camera Interpolation
  , CameraInterpolation(..)
  , cameraInterpolationFromText
  , cameraInterpolationToText
    -- * Structures
  , Position3D(..)
  , CameraIntrinsics(..)
    -- * Constants
  , maxFocalLength
  , maxSensorSize
  , maxFOV
  , maxAspectRatio
  , maxRotationDegrees
  , maxTimestamp
  , quaternionNormalizationTolerance
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

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
  deriving stock (Eq, Show, Generic, Enum, Bounded)

cameraFormatFromText :: Text -> Maybe CameraFormat
cameraFormatFromText "motionctrl" = Just CameraMotionCtrl
cameraFormatFromText "wan-move" = Just CameraWanMove
cameraFormatFromText "uni3c" = Just CameraUni3C
cameraFormatFromText "cameractrl" = Just CameraCameraCtrl
cameraFormatFromText "blender" = Just CameraBlender
cameraFormatFromText "fbx" = Just CameraFBX
cameraFormatFromText _ = Nothing

cameraFormatToText :: CameraFormat -> Text
cameraFormatToText CameraMotionCtrl = "motionctrl"
cameraFormatToText CameraWanMove = "wan-move"
cameraFormatToText CameraUni3C = "uni3c"
cameraFormatToText CameraCameraCtrl = "cameractrl"
cameraFormatToText CameraBlender = "blender"
cameraFormatToText CameraFBX = "fbx"

-- ────────────────────────────────────────────────────────────────────────────
-- Coordinate System
-- ────────────────────────────────────────────────────────────────────────────

-- | Coordinate system conventions
data CoordinateSystem
  = CoordOpenGL   -- Y-up, right-handed
  | CoordOpenCV   -- Y-down, right-handed
  | CoordBlender  -- Z-up, right-handed
  | CoordUnity    -- Y-up, left-handed
  deriving stock (Eq, Show, Generic, Enum, Bounded)

coordinateSystemFromText :: Text -> Maybe CoordinateSystem
coordinateSystemFromText "opengl" = Just CoordOpenGL
coordinateSystemFromText "opencv" = Just CoordOpenCV
coordinateSystemFromText "blender" = Just CoordBlender
coordinateSystemFromText "unity" = Just CoordUnity
coordinateSystemFromText _ = Nothing

coordinateSystemToText :: CoordinateSystem -> Text
coordinateSystemToText CoordOpenGL = "opengl"
coordinateSystemToText CoordOpenCV = "opencv"
coordinateSystemToText CoordBlender = "blender"
coordinateSystemToText CoordUnity = "unity"

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
  deriving stock (Eq, Show, Generic, Enum, Bounded)

eulerOrderFromText :: Text -> Maybe EulerOrder
eulerOrderFromText "XYZ" = Just EulerXYZ
eulerOrderFromText "YXZ" = Just EulerYXZ
eulerOrderFromText "ZXY" = Just EulerZXY
eulerOrderFromText "ZYX" = Just EulerZYX
eulerOrderFromText "XZY" = Just EulerXZY
eulerOrderFromText "YZX" = Just EulerYZX
eulerOrderFromText _ = Nothing

eulerOrderToText :: EulerOrder -> Text
eulerOrderToText EulerXYZ = "XYZ"
eulerOrderToText EulerYXZ = "YXZ"
eulerOrderToText EulerZXY = "ZXY"
eulerOrderToText EulerZYX = "ZYX"
eulerOrderToText EulerXZY = "XZY"
eulerOrderToText EulerYZX = "YZX"

-- ────────────────────────────────────────────────────────────────────────────
-- Camera Interpolation
-- ────────────────────────────────────────────────────────────────────────────

-- | Camera interpolation options
data CameraInterpolation
  = InterpLinear
  | InterpBezier
  | InterpSpline
  deriving stock (Eq, Show, Generic, Enum, Bounded)

cameraInterpolationFromText :: Text -> Maybe CameraInterpolation
cameraInterpolationFromText "linear" = Just InterpLinear
cameraInterpolationFromText "bezier" = Just InterpBezier
cameraInterpolationFromText "spline" = Just InterpSpline
cameraInterpolationFromText _ = Nothing

cameraInterpolationToText :: CameraInterpolation -> Text
cameraInterpolationToText InterpLinear = "linear"
cameraInterpolationToText InterpBezier = "bezier"
cameraInterpolationToText InterpSpline = "spline"

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | 3D position
data Position3D = Position3D
  { pos3DX :: !Double
  , pos3DY :: !Double
  , pos3DZ :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | Camera intrinsic parameters
data CameraIntrinsics = CameraIntrinsics
  { ciFocalLength :: !Double
  , ciSensorWidth :: !(Maybe Double)
  , ciSensorHeight :: !(Maybe Double)
  , ciFOV :: !Double
  , ciAspectRatio :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxFocalLength :: Double
maxFocalLength = 10000.0

maxSensorSize :: Double
maxSensorSize = 100.0

maxFOV :: Double
maxFOV = 180.0

maxAspectRatio :: Double
maxAspectRatio = 10.0

maxRotationDegrees :: Double
maxRotationDegrees = 360.0

maxTimestamp :: Double
maxTimestamp = 86400.0

quaternionNormalizationTolerance :: Double
quaternionNormalizationTolerance = 0.1
