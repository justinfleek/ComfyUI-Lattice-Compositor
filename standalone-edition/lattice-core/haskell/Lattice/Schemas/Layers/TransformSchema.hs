{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Layers.TransformSchema
Description : Layer transform enums and types
Copyright   : (c) Lattice, 2026
License     : MIT

Layer transform enums: motion blur, auto-orient, material options.

Source: ui/src/schemas/layers/transform-schema.ts
-}

module Lattice.Schemas.Layers.TransformSchema
  ( -- * Motion Blur Type
    MotionBlurType(..)
  , motionBlurTypeFromText
  , motionBlurTypeToText
    -- * Radial Mode
  , RadialMode(..)
  , radialModeFromText
  , radialModeToText
    -- * Auto Orient Mode
  , AutoOrientMode(..)
  , autoOrientModeFromText
  , autoOrientModeToText
    -- * Casts Shadows
  , CastsShadows(..)
  , castsShadowsFromText
  , castsShadowsToText
    -- * Stretch Anchor
  , StretchAnchor(..)
  , stretchAnchorFromText
  , stretchAnchorToText
    -- * Audio Feature
  , AudioFeature(..)
  , audioFeatureFromText
  , audioFeatureToText
    -- * Constants
  , maxShutterAngle
  , maxShutterPhase
  , minShutterPhase
  , minSamplesPerFrame
  , maxSamplesPerFrame
  , maxBlurLength
  , maxRadialAmount
  , maxMaterialValue
  , maxTimeStretch
  , minTimeStretch
    -- * Structures
  , SeparateDimensions(..)
  , MotionBlurSettings(..)
  , MaterialOptions(..)
    -- * Validation
  , isValidMotionBlurSettings
  , isValidMaterialOptions
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

-- ────────────────────────────────────────────────────────────────────────────
-- Motion Blur Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Motion blur types
data MotionBlurType
  = BlurStandard
  | BlurPixel
  | BlurDirectional
  | BlurRadial
  | BlurVector
  | BlurAdaptive
  deriving stock (Eq, Show, Generic, Enum, Bounded)

motionBlurTypeFromText :: Text -> Maybe MotionBlurType
motionBlurTypeFromText "standard" = Just BlurStandard
motionBlurTypeFromText "pixel" = Just BlurPixel
motionBlurTypeFromText "directional" = Just BlurDirectional
motionBlurTypeFromText "radial" = Just BlurRadial
motionBlurTypeFromText "vector" = Just BlurVector
motionBlurTypeFromText "adaptive" = Just BlurAdaptive
motionBlurTypeFromText _ = Nothing

motionBlurTypeToText :: MotionBlurType -> Text
motionBlurTypeToText BlurStandard = "standard"
motionBlurTypeToText BlurPixel = "pixel"
motionBlurTypeToText BlurDirectional = "directional"
motionBlurTypeToText BlurRadial = "radial"
motionBlurTypeToText BlurVector = "vector"
motionBlurTypeToText BlurAdaptive = "adaptive"

-- ────────────────────────────────────────────────────────────────────────────
-- Radial Mode
-- ────────────────────────────────────────────────────────────────────────────

-- | Radial motion blur modes
data RadialMode
  = RadialSpin
  | RadialZoom
  deriving stock (Eq, Show, Generic, Enum, Bounded)

radialModeFromText :: Text -> Maybe RadialMode
radialModeFromText "spin" = Just RadialSpin
radialModeFromText "zoom" = Just RadialZoom
radialModeFromText _ = Nothing

radialModeToText :: RadialMode -> Text
radialModeToText RadialSpin = "spin"
radialModeToText RadialZoom = "zoom"

-- ────────────────────────────────────────────────────────────────────────────
-- Auto Orient Mode
-- ────────────────────────────────────────────────────────────────────────────

-- | Auto-orient mode for layers
data AutoOrientMode
  = OrientOff
  | OrientToCamera
  | OrientAlongPath
  | OrientToPointOfInterest
  deriving stock (Eq, Show, Generic, Enum, Bounded)

autoOrientModeFromText :: Text -> Maybe AutoOrientMode
autoOrientModeFromText "off" = Just OrientOff
autoOrientModeFromText "toCamera" = Just OrientToCamera
autoOrientModeFromText "alongPath" = Just OrientAlongPath
autoOrientModeFromText "toPointOfInterest" = Just OrientToPointOfInterest
autoOrientModeFromText _ = Nothing

autoOrientModeToText :: AutoOrientMode -> Text
autoOrientModeToText OrientOff = "off"
autoOrientModeToText OrientToCamera = "toCamera"
autoOrientModeToText OrientAlongPath = "alongPath"
autoOrientModeToText OrientToPointOfInterest = "toPointOfInterest"

-- ────────────────────────────────────────────────────────────────────────────
-- Casts Shadows
-- ────────────────────────────────────────────────────────────────────────────

-- | Shadow casting modes
data CastsShadows
  = ShadowOff
  | ShadowOn
  | ShadowOnly
  deriving stock (Eq, Show, Generic, Enum, Bounded)

castsShadowsFromText :: Text -> Maybe CastsShadows
castsShadowsFromText "off" = Just ShadowOff
castsShadowsFromText "on" = Just ShadowOn
castsShadowsFromText "only" = Just ShadowOnly
castsShadowsFromText _ = Nothing

castsShadowsToText :: CastsShadows -> Text
castsShadowsToText ShadowOff = "off"
castsShadowsToText ShadowOn = "on"
castsShadowsToText ShadowOnly = "only"

-- ────────────────────────────────────────────────────────────────────────────
-- Stretch Anchor
-- ────────────────────────────────────────────────────────────────────────────

-- | Time stretch anchor points
data StretchAnchor
  = AnchorStartFrame
  | AnchorEndFrame
  | AnchorCurrentFrame
  deriving stock (Eq, Show, Generic, Enum, Bounded)

stretchAnchorFromText :: Text -> Maybe StretchAnchor
stretchAnchorFromText "startFrame" = Just AnchorStartFrame
stretchAnchorFromText "endFrame" = Just AnchorEndFrame
stretchAnchorFromText "currentFrame" = Just AnchorCurrentFrame
stretchAnchorFromText _ = Nothing

stretchAnchorToText :: StretchAnchor -> Text
stretchAnchorToText AnchorStartFrame = "startFrame"
stretchAnchorToText AnchorEndFrame = "endFrame"
stretchAnchorToText AnchorCurrentFrame = "currentFrame"

-- ────────────────────────────────────────────────────────────────────────────
-- Audio Feature
-- ────────────────────────────────────────────────────────────────────────────

-- | Audio features for audio-driven animation
data AudioFeature
  = FeatureAmplitude
  | FeatureBass
  | FeatureMid
  | FeatureTreble
  | FeatureSpectral
  deriving stock (Eq, Show, Generic, Enum, Bounded)

audioFeatureFromText :: Text -> Maybe AudioFeature
audioFeatureFromText "amplitude" = Just FeatureAmplitude
audioFeatureFromText "bass" = Just FeatureBass
audioFeatureFromText "mid" = Just FeatureMid
audioFeatureFromText "treble" = Just FeatureTreble
audioFeatureFromText "spectral" = Just FeatureSpectral
audioFeatureFromText _ = Nothing

audioFeatureToText :: AudioFeature -> Text
audioFeatureToText FeatureAmplitude = "amplitude"
audioFeatureToText FeatureBass = "bass"
audioFeatureToText FeatureMid = "mid"
audioFeatureToText FeatureTreble = "treble"
audioFeatureToText FeatureSpectral = "spectral"

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxShutterAngle :: Double
maxShutterAngle = 720.0

maxShutterPhase :: Double
maxShutterPhase = 180.0

minShutterPhase :: Double
minShutterPhase = -180.0

minSamplesPerFrame :: Int
minSamplesPerFrame = 2

maxSamplesPerFrame :: Int
maxSamplesPerFrame = 64

maxBlurLength :: Double
maxBlurLength = 1000.0

maxRadialAmount :: Double
maxRadialAmount = 100.0

maxMaterialValue :: Double
maxMaterialValue = 100.0

maxTimeStretch :: Double
maxTimeStretch = 100.0

minTimeStretch :: Double
minTimeStretch = 0.01

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | Separate dimensions flags
data SeparateDimensions = SeparateDimensions
  { sdPosition :: !Bool
  , sdScale :: !Bool
  }
  deriving stock (Eq, Show, Generic)

-- | Motion blur settings
data MotionBlurSettings = MotionBlurSettings
  { mbsType :: !MotionBlurType
  , mbsShutterAngle :: !Double
  , mbsShutterPhase :: !Double
  , mbsSamplesPerFrame :: !Int
  , mbsDirection :: !(Maybe Double)
  , mbsBlurLength :: !(Maybe Double)
  , mbsRadialMode :: !(Maybe RadialMode)
  , mbsRadialCenterX :: !(Maybe Double)
  , mbsRadialCenterY :: !(Maybe Double)
  , mbsRadialAmount :: !(Maybe Double)
  }
  deriving stock (Eq, Show, Generic)

-- | Material options for 3D layers
data MaterialOptions = MaterialOptions
  { moCastsShadows :: !CastsShadows
  , moLightTransmission :: !Double
  , moAcceptsShadows :: !Bool
  , moAcceptsLights :: !Bool
  , moAmbient :: !Double
  , moDiffuse :: !Double
  , moSpecularIntensity :: !Double
  , moSpecularShininess :: !Double
  , moMetal :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if motion blur settings are valid
isValidMotionBlurSettings :: MotionBlurSettings -> Bool
isValidMotionBlurSettings s =
  mbsShutterAngle s >= 0 && mbsShutterAngle s <= maxShutterAngle &&
  mbsShutterPhase s >= minShutterPhase && mbsShutterPhase s <= maxShutterPhase &&
  mbsSamplesPerFrame s >= minSamplesPerFrame && mbsSamplesPerFrame s <= maxSamplesPerFrame

-- | Check if material options are valid
isValidMaterialOptions :: MaterialOptions -> Bool
isValidMaterialOptions m =
  moLightTransmission m >= 0 && moLightTransmission m <= maxMaterialValue &&
  moAmbient m >= 0 && moAmbient m <= maxMaterialValue &&
  moDiffuse m >= 0 && moDiffuse m <= maxMaterialValue &&
  moSpecularIntensity m >= 0 && moSpecularIntensity m <= maxMaterialValue &&
  moSpecularShininess m >= 0 && moSpecularShininess m <= maxMaterialValue &&
  moMetal m >= 0 && moMetal m <= maxMaterialValue
