{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Imports.CameraSchema
Description : Camera import format enums and types
Copyright   : (c) Lattice, 2026
License     : MIT

Camera import format enums and types.

Source: ui/src/schemas/imports/camera-schema.ts
-}

module Lattice.Schemas.Imports.CameraSchema
  ( -- * Camera Type
    CameraType(..)
  , cameraTypeFromText
  , cameraTypeToText
    -- * Auto Orient Mode
  , AutoOrientMode(..)
  , autoOrientModeFromText
  , autoOrientModeToText
    -- * Measure Film Size
  , MeasureFilmSize(..)
  , measureFilmSizeFromText
  , measureFilmSizeToText
    -- * Spatial Interpolation
  , SpatialInterpolation(..)
  , spatialInterpolationFromText
  , spatialInterpolationToText
    -- * Temporal Interpolation
  , TemporalInterpolation(..)
  , temporalInterpolationFromText
  , temporalInterpolationToText
    -- * Constants
  , maxFocalLength
  , maxRotation
  , maxZoom
  , minZoom
  , maxFilmSize
  , maxFocusDistance
  , maxAperture
  , maxKeyframes
    -- * Structures
  , Vector2(..)
  , Vector3(..)
  , DepthOfField(..)
  , Iris(..)
  , Highlight(..)
    -- * Validation
  , isValidVector2
  , isValidVector3
  , isValidDepthOfField
  , isValidIris
  , isValidHighlight
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

-- ────────────────────────────────────────────────────────────────────────────
-- Camera Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Camera type (one-node vs two-node)
data CameraType
  = CameraOneNode
  | CameraTwoNode
  deriving stock (Eq, Show, Generic, Enum, Bounded)

cameraTypeFromText :: Text -> Maybe CameraType
cameraTypeFromText "one-node" = Just CameraOneNode
cameraTypeFromText "two-node" = Just CameraTwoNode
cameraTypeFromText _ = Nothing

cameraTypeToText :: CameraType -> Text
cameraTypeToText CameraOneNode = "one-node"
cameraTypeToText CameraTwoNode = "two-node"

-- ────────────────────────────────────────────────────────────────────────────
-- Auto Orient Mode
-- ────────────────────────────────────────────────────────────────────────────

-- | Auto-orient mode for cameras
data AutoOrientMode
  = AutoOrientOff
  | AutoOrientAlongPath
  | AutoOrientTowardsPoi
  deriving stock (Eq, Show, Generic, Enum, Bounded)

autoOrientModeFromText :: Text -> Maybe AutoOrientMode
autoOrientModeFromText "off" = Just AutoOrientOff
autoOrientModeFromText "orient-along-path" = Just AutoOrientAlongPath
autoOrientModeFromText "orient-towards-poi" = Just AutoOrientTowardsPoi
autoOrientModeFromText _ = Nothing

autoOrientModeToText :: AutoOrientMode -> Text
autoOrientModeToText AutoOrientOff = "off"
autoOrientModeToText AutoOrientAlongPath = "orient-along-path"
autoOrientModeToText AutoOrientTowardsPoi = "orient-towards-poi"

-- ────────────────────────────────────────────────────────────────────────────
-- Measure Film Size
-- ────────────────────────────────────────────────────────────────────────────

-- | How to measure film size
data MeasureFilmSize
  = MeasureHorizontal
  | MeasureVertical
  | MeasureDiagonal
  deriving stock (Eq, Show, Generic, Enum, Bounded)

measureFilmSizeFromText :: Text -> Maybe MeasureFilmSize
measureFilmSizeFromText "horizontal" = Just MeasureHorizontal
measureFilmSizeFromText "vertical" = Just MeasureVertical
measureFilmSizeFromText "diagonal" = Just MeasureDiagonal
measureFilmSizeFromText _ = Nothing

measureFilmSizeToText :: MeasureFilmSize -> Text
measureFilmSizeToText MeasureHorizontal = "horizontal"
measureFilmSizeToText MeasureVertical = "vertical"
measureFilmSizeToText MeasureDiagonal = "diagonal"

-- ────────────────────────────────────────────────────────────────────────────
-- Spatial Interpolation
-- ────────────────────────────────────────────────────────────────────────────

-- | Spatial interpolation types
data SpatialInterpolation
  = SpatialLinear
  | SpatialBezier
  | SpatialAutoBezier
  | SpatialContinuousBezier
  deriving stock (Eq, Show, Generic, Enum, Bounded)

spatialInterpolationFromText :: Text -> Maybe SpatialInterpolation
spatialInterpolationFromText "linear" = Just SpatialLinear
spatialInterpolationFromText "bezier" = Just SpatialBezier
spatialInterpolationFromText "auto-bezier" = Just SpatialAutoBezier
spatialInterpolationFromText "continuous-bezier" = Just SpatialContinuousBezier
spatialInterpolationFromText _ = Nothing

spatialInterpolationToText :: SpatialInterpolation -> Text
spatialInterpolationToText SpatialLinear = "linear"
spatialInterpolationToText SpatialBezier = "bezier"
spatialInterpolationToText SpatialAutoBezier = "auto-bezier"
spatialInterpolationToText SpatialContinuousBezier = "continuous-bezier"

-- ────────────────────────────────────────────────────────────────────────────
-- Temporal Interpolation
-- ────────────────────────────────────────────────────────────────────────────

-- | Temporal interpolation types
data TemporalInterpolation
  = TemporalLinear
  | TemporalBezier
  | TemporalHold
  deriving stock (Eq, Show, Generic, Enum, Bounded)

temporalInterpolationFromText :: Text -> Maybe TemporalInterpolation
temporalInterpolationFromText "linear" = Just TemporalLinear
temporalInterpolationFromText "bezier" = Just TemporalBezier
temporalInterpolationFromText "hold" = Just TemporalHold
temporalInterpolationFromText _ = Nothing

temporalInterpolationToText :: TemporalInterpolation -> Text
temporalInterpolationToText TemporalLinear = "linear"
temporalInterpolationToText TemporalBezier = "bezier"
temporalInterpolationToText TemporalHold = "hold"

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxFocalLength :: Double
maxFocalLength = 10000.0

maxRotation :: Double
maxRotation = 360.0

maxZoom :: Double
maxZoom = 1000.0

minZoom :: Double
minZoom = 0.1

maxFilmSize :: Double
maxFilmSize = 100.0

maxFocusDistance :: Double
maxFocusDistance = 100000.0

maxAperture :: Double
maxAperture = 100.0

maxKeyframes :: Int
maxKeyframes = 100000

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | 2D vector
data Vector2 = Vector2
  { v2X :: !Double
  , v2Y :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | 3D vector
data Vector3 = Vector3
  { v3X :: !Double
  , v3Y :: !Double
  , v3Z :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | Depth of field settings
data DepthOfField = DepthOfField
  { dofEnabled :: !Bool
  , dofFocusDistance :: !Double
  , dofAperture :: !Double
  , dofFStop :: !Double
  , dofBlurLevel :: !Double
  , dofLockToZoom :: !Bool
  }
  deriving stock (Eq, Show, Generic)

-- | Iris settings
data Iris = Iris
  { irisShape :: !Double
  , irisRotation :: !Double
  , irisRoundness :: !Double
  , irisAspectRatio :: !Double
  , irisDiffractionFringe :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | Highlight settings
data Highlight = Highlight
  { highlightGain :: !Double
  , highlightThreshold :: !Double
  , highlightSaturation :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if 2D vector has finite values
isValidVector2 :: Vector2 -> Bool
isValidVector2 v =
  not (isNaN (v2X v) || isInfinite (v2X v)) &&
  not (isNaN (v2Y v) || isInfinite (v2Y v))

-- | Check if 3D vector has finite values
isValidVector3 :: Vector3 -> Bool
isValidVector3 v =
  not (isNaN (v3X v) || isInfinite (v3X v)) &&
  not (isNaN (v3Y v) || isInfinite (v3Y v)) &&
  not (isNaN (v3Z v) || isInfinite (v3Z v))

-- | Check if depth of field settings are valid
isValidDepthOfField :: DepthOfField -> Bool
isValidDepthOfField dof =
  dofFocusDistance dof >= 0 && dofFocusDistance dof <= maxFocusDistance &&
  dofAperture dof >= 0 && dofAperture dof <= maxAperture &&
  dofFStop dof > 0 && dofFStop dof <= maxAperture &&
  dofBlurLevel dof >= 0 && dofBlurLevel dof <= 1

-- | Check if iris settings are valid
isValidIris :: Iris -> Bool
isValidIris i =
  irisShape i >= 0 && irisShape i <= 10 &&
  irisRotation i <= maxRotation &&
  irisRoundness i >= 0 && irisRoundness i <= 1 &&
  irisAspectRatio i >= 0.5 && irisAspectRatio i <= 2 &&
  irisDiffractionFringe i >= 0 && irisDiffractionFringe i <= 1

-- | Check if highlight settings are valid
isValidHighlight :: Highlight -> Bool
isValidHighlight h =
  highlightGain h >= 0 && highlightGain h <= 1 &&
  highlightThreshold h >= 0 && highlightThreshold h <= 1 &&
  highlightSaturation h >= 0 && highlightSaturation h <= 1
