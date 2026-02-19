-- | Lattice.Schemas.Imports.CameraSchema - Camera import format enums and types
-- |
-- | Camera import format enums and types.
-- |
-- | Source: ui/src/schemas/imports/camera-schema.ts

module Lattice.Schemas.Imports.CameraSchema
  ( -- Camera Type
    CameraType(..)
  , cameraTypeFromString
  , cameraTypeToString
    -- Auto Orient Mode
  , AutoOrientMode(..)
  , autoOrientModeFromString
  , autoOrientModeToString
    -- Measure Film Size
  , MeasureFilmSize(..)
  , measureFilmSizeFromString
  , measureFilmSizeToString
    -- Spatial Interpolation
  , SpatialInterpolation(..)
  , spatialInterpolationFromString
  , spatialInterpolationToString
    -- Temporal Interpolation
  , TemporalInterpolation(..)
  , temporalInterpolationFromString
  , temporalInterpolationToString
    -- Constants
  , maxFocalLength
  , maxRotation
  , maxZoom
  , minZoom
  , maxFilmSize
  , maxFocusDistance
  , maxAperture
  , maxKeyframes
    -- Structures
  , Vector2
  , Vector3
  , DepthOfField
  , Iris
  , Highlight
    -- Validation
  , isValidVector2
  , isValidVector3
  , isValidDepthOfField
  , isValidIris
  , isValidHighlight
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Number (isFinite)

-- ────────────────────────────────────────────────────────────────────────────
-- Camera Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Camera type (one-node vs two-node)
data CameraType
  = CameraOneNode
  | CameraTwoNode

derive instance Eq CameraType
derive instance Generic CameraType _

instance Show CameraType where
  show = genericShow

cameraTypeFromString :: String -> Maybe CameraType
cameraTypeFromString = case _ of
  "one-node" -> Just CameraOneNode
  "two-node" -> Just CameraTwoNode
  _ -> Nothing

cameraTypeToString :: CameraType -> String
cameraTypeToString = case _ of
  CameraOneNode -> "one-node"
  CameraTwoNode -> "two-node"

-- ────────────────────────────────────────────────────────────────────────────
-- Auto Orient Mode
-- ────────────────────────────────────────────────────────────────────────────

-- | Auto-orient mode for cameras
data AutoOrientMode
  = AutoOrientOff
  | AutoOrientAlongPath
  | AutoOrientTowardsPoi

derive instance Eq AutoOrientMode
derive instance Generic AutoOrientMode _

instance Show AutoOrientMode where
  show = genericShow

autoOrientModeFromString :: String -> Maybe AutoOrientMode
autoOrientModeFromString = case _ of
  "off" -> Just AutoOrientOff
  "orient-along-path" -> Just AutoOrientAlongPath
  "orient-towards-poi" -> Just AutoOrientTowardsPoi
  _ -> Nothing

autoOrientModeToString :: AutoOrientMode -> String
autoOrientModeToString = case _ of
  AutoOrientOff -> "off"
  AutoOrientAlongPath -> "orient-along-path"
  AutoOrientTowardsPoi -> "orient-towards-poi"

-- ────────────────────────────────────────────────────────────────────────────
-- Measure Film Size
-- ────────────────────────────────────────────────────────────────────────────

-- | How to measure film size
data MeasureFilmSize
  = MeasureHorizontal
  | MeasureVertical
  | MeasureDiagonal

derive instance Eq MeasureFilmSize
derive instance Generic MeasureFilmSize _

instance Show MeasureFilmSize where
  show = genericShow

measureFilmSizeFromString :: String -> Maybe MeasureFilmSize
measureFilmSizeFromString = case _ of
  "horizontal" -> Just MeasureHorizontal
  "vertical" -> Just MeasureVertical
  "diagonal" -> Just MeasureDiagonal
  _ -> Nothing

measureFilmSizeToString :: MeasureFilmSize -> String
measureFilmSizeToString = case _ of
  MeasureHorizontal -> "horizontal"
  MeasureVertical -> "vertical"
  MeasureDiagonal -> "diagonal"

-- ────────────────────────────────────────────────────────────────────────────
-- Spatial Interpolation
-- ────────────────────────────────────────────────────────────────────────────

-- | Spatial interpolation types
data SpatialInterpolation
  = SpatialLinear
  | SpatialBezier
  | SpatialAutoBezier
  | SpatialContinuousBezier

derive instance Eq SpatialInterpolation
derive instance Generic SpatialInterpolation _

instance Show SpatialInterpolation where
  show = genericShow

spatialInterpolationFromString :: String -> Maybe SpatialInterpolation
spatialInterpolationFromString = case _ of
  "linear" -> Just SpatialLinear
  "bezier" -> Just SpatialBezier
  "auto-bezier" -> Just SpatialAutoBezier
  "continuous-bezier" -> Just SpatialContinuousBezier
  _ -> Nothing

spatialInterpolationToString :: SpatialInterpolation -> String
spatialInterpolationToString = case _ of
  SpatialLinear -> "linear"
  SpatialBezier -> "bezier"
  SpatialAutoBezier -> "auto-bezier"
  SpatialContinuousBezier -> "continuous-bezier"

-- ────────────────────────────────────────────────────────────────────────────
-- Temporal Interpolation
-- ────────────────────────────────────────────────────────────────────────────

-- | Temporal interpolation types
data TemporalInterpolation
  = TemporalLinear
  | TemporalBezier
  | TemporalHold

derive instance Eq TemporalInterpolation
derive instance Generic TemporalInterpolation _

instance Show TemporalInterpolation where
  show = genericShow

temporalInterpolationFromString :: String -> Maybe TemporalInterpolation
temporalInterpolationFromString = case _ of
  "linear" -> Just TemporalLinear
  "bezier" -> Just TemporalBezier
  "hold" -> Just TemporalHold
  _ -> Nothing

temporalInterpolationToString :: TemporalInterpolation -> String
temporalInterpolationToString = case _ of
  TemporalLinear -> "linear"
  TemporalBezier -> "bezier"
  TemporalHold -> "hold"

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxFocalLength :: Number
maxFocalLength = 10000.0

maxRotation :: Number
maxRotation = 360.0

maxZoom :: Number
maxZoom = 1000.0

minZoom :: Number
minZoom = 0.1

maxFilmSize :: Number
maxFilmSize = 100.0

maxFocusDistance :: Number
maxFocusDistance = 100000.0

maxAperture :: Number
maxAperture = 100.0

maxKeyframes :: Int
maxKeyframes = 100000

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | 2D vector
type Vector2 =
  { x :: Number
  , y :: Number
  }

-- | 3D vector
type Vector3 =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | Depth of field settings
type DepthOfField =
  { enabled :: Boolean
  , focusDistance :: Number
  , aperture :: Number
  , fStop :: Number
  , blurLevel :: Number
  , lockToZoom :: Boolean
  }

-- | Iris settings
type Iris =
  { shape :: Number
  , rotation :: Number
  , roundness :: Number
  , aspectRatio :: Number
  , diffractionFringe :: Number
  }

-- | Highlight settings
type Highlight =
  { gain :: Number
  , threshold :: Number
  , saturation :: Number
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if 2D vector has finite values
isValidVector2 :: Vector2 -> Boolean
isValidVector2 v = isFinite v.x && isFinite v.y

-- | Check if 3D vector has finite values
isValidVector3 :: Vector3 -> Boolean
isValidVector3 v = isFinite v.x && isFinite v.y && isFinite v.z

-- | Check if depth of field settings are valid
isValidDepthOfField :: DepthOfField -> Boolean
isValidDepthOfField dof =
  dof.focusDistance >= 0.0 && dof.focusDistance <= maxFocusDistance &&
  dof.aperture >= 0.0 && dof.aperture <= maxAperture &&
  dof.fStop > 0.0 && dof.fStop <= maxAperture &&
  dof.blurLevel >= 0.0 && dof.blurLevel <= 1.0

-- | Check if iris settings are valid
isValidIris :: Iris -> Boolean
isValidIris i =
  i.shape >= 0.0 && i.shape <= 10.0 &&
  i.rotation <= maxRotation &&
  i.roundness >= 0.0 && i.roundness <= 1.0 &&
  i.aspectRatio >= 0.5 && i.aspectRatio <= 2.0 &&
  i.diffractionFringe >= 0.0 && i.diffractionFringe <= 1.0

-- | Check if highlight settings are valid
isValidHighlight :: Highlight -> Boolean
isValidHighlight h =
  h.gain >= 0.0 && h.gain <= 1.0 &&
  h.threshold >= 0.0 && h.threshold <= 1.0 &&
  h.saturation >= 0.0 && h.saturation <= 1.0
