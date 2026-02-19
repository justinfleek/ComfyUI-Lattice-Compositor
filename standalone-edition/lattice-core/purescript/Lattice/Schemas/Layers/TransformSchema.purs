-- | Lattice.Schemas.Layers.TransformSchema - Layer transform enums and types
-- |
-- | Layer transform enums: motion blur, auto-orient, material options.
-- |
-- | Source: ui/src/schemas/layers/transform-schema.ts

module Lattice.Schemas.Layers.TransformSchema
  ( -- Motion Blur Type
    MotionBlurType(..)
  , motionBlurTypeFromString
  , motionBlurTypeToString
    -- Radial Mode
  , RadialMode(..)
  , radialModeFromString
  , radialModeToString
    -- Auto Orient Mode
  , AutoOrientMode(..)
  , autoOrientModeFromString
  , autoOrientModeToString
    -- Casts Shadows
  , CastsShadows(..)
  , castsShadowsFromString
  , castsShadowsToString
    -- Stretch Anchor
  , StretchAnchor(..)
  , stretchAnchorFromString
  , stretchAnchorToString
    -- Audio Feature
  , AudioFeature(..)
  , audioFeatureFromString
  , audioFeatureToString
    -- Constants
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
    -- Structures
  , SeparateDimensions
  , MotionBlurSettings
  , MaterialOptions
    -- Validation
  , isValidMotionBlurSettings
  , isValidMaterialOptions
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

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

derive instance Eq MotionBlurType
derive instance Generic MotionBlurType _

instance Show MotionBlurType where
  show = genericShow

motionBlurTypeFromString :: String -> Maybe MotionBlurType
motionBlurTypeFromString = case _ of
  "standard" -> Just BlurStandard
  "pixel" -> Just BlurPixel
  "directional" -> Just BlurDirectional
  "radial" -> Just BlurRadial
  "vector" -> Just BlurVector
  "adaptive" -> Just BlurAdaptive
  _ -> Nothing

motionBlurTypeToString :: MotionBlurType -> String
motionBlurTypeToString = case _ of
  BlurStandard -> "standard"
  BlurPixel -> "pixel"
  BlurDirectional -> "directional"
  BlurRadial -> "radial"
  BlurVector -> "vector"
  BlurAdaptive -> "adaptive"

-- ────────────────────────────────────────────────────────────────────────────
-- Radial Mode
-- ────────────────────────────────────────────────────────────────────────────

-- | Radial motion blur modes
data RadialMode
  = RadialSpin
  | RadialZoom

derive instance Eq RadialMode
derive instance Generic RadialMode _

instance Show RadialMode where
  show = genericShow

radialModeFromString :: String -> Maybe RadialMode
radialModeFromString = case _ of
  "spin" -> Just RadialSpin
  "zoom" -> Just RadialZoom
  _ -> Nothing

radialModeToString :: RadialMode -> String
radialModeToString = case _ of
  RadialSpin -> "spin"
  RadialZoom -> "zoom"

-- ────────────────────────────────────────────────────────────────────────────
-- Auto Orient Mode
-- ────────────────────────────────────────────────────────────────────────────

-- | Auto-orient mode for layers
data AutoOrientMode
  = OrientOff
  | OrientToCamera
  | OrientAlongPath
  | OrientToPointOfInterest

derive instance Eq AutoOrientMode
derive instance Generic AutoOrientMode _

instance Show AutoOrientMode where
  show = genericShow

autoOrientModeFromString :: String -> Maybe AutoOrientMode
autoOrientModeFromString = case _ of
  "off" -> Just OrientOff
  "toCamera" -> Just OrientToCamera
  "alongPath" -> Just OrientAlongPath
  "toPointOfInterest" -> Just OrientToPointOfInterest
  _ -> Nothing

autoOrientModeToString :: AutoOrientMode -> String
autoOrientModeToString = case _ of
  OrientOff -> "off"
  OrientToCamera -> "toCamera"
  OrientAlongPath -> "alongPath"
  OrientToPointOfInterest -> "toPointOfInterest"

-- ────────────────────────────────────────────────────────────────────────────
-- Casts Shadows
-- ────────────────────────────────────────────────────────────────────────────

-- | Shadow casting modes
data CastsShadows
  = ShadowOff
  | ShadowOn
  | ShadowOnly

derive instance Eq CastsShadows
derive instance Generic CastsShadows _

instance Show CastsShadows where
  show = genericShow

castsShadowsFromString :: String -> Maybe CastsShadows
castsShadowsFromString = case _ of
  "off" -> Just ShadowOff
  "on" -> Just ShadowOn
  "only" -> Just ShadowOnly
  _ -> Nothing

castsShadowsToString :: CastsShadows -> String
castsShadowsToString = case _ of
  ShadowOff -> "off"
  ShadowOn -> "on"
  ShadowOnly -> "only"

-- ────────────────────────────────────────────────────────────────────────────
-- Stretch Anchor
-- ────────────────────────────────────────────────────────────────────────────

-- | Time stretch anchor points
data StretchAnchor
  = AnchorStartFrame
  | AnchorEndFrame
  | AnchorCurrentFrame

derive instance Eq StretchAnchor
derive instance Generic StretchAnchor _

instance Show StretchAnchor where
  show = genericShow

stretchAnchorFromString :: String -> Maybe StretchAnchor
stretchAnchorFromString = case _ of
  "startFrame" -> Just AnchorStartFrame
  "endFrame" -> Just AnchorEndFrame
  "currentFrame" -> Just AnchorCurrentFrame
  _ -> Nothing

stretchAnchorToString :: StretchAnchor -> String
stretchAnchorToString = case _ of
  AnchorStartFrame -> "startFrame"
  AnchorEndFrame -> "endFrame"
  AnchorCurrentFrame -> "currentFrame"

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

derive instance Eq AudioFeature
derive instance Generic AudioFeature _

instance Show AudioFeature where
  show = genericShow

audioFeatureFromString :: String -> Maybe AudioFeature
audioFeatureFromString = case _ of
  "amplitude" -> Just FeatureAmplitude
  "bass" -> Just FeatureBass
  "mid" -> Just FeatureMid
  "treble" -> Just FeatureTreble
  "spectral" -> Just FeatureSpectral
  _ -> Nothing

audioFeatureToString :: AudioFeature -> String
audioFeatureToString = case _ of
  FeatureAmplitude -> "amplitude"
  FeatureBass -> "bass"
  FeatureMid -> "mid"
  FeatureTreble -> "treble"
  FeatureSpectral -> "spectral"

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxShutterAngle :: Number
maxShutterAngle = 720.0

maxShutterPhase :: Number
maxShutterPhase = 180.0

minShutterPhase :: Number
minShutterPhase = -180.0

minSamplesPerFrame :: Int
minSamplesPerFrame = 2

maxSamplesPerFrame :: Int
maxSamplesPerFrame = 64

maxBlurLength :: Number
maxBlurLength = 1000.0

maxRadialAmount :: Number
maxRadialAmount = 100.0

maxMaterialValue :: Number
maxMaterialValue = 100.0

maxTimeStretch :: Number
maxTimeStretch = 100.0

minTimeStretch :: Number
minTimeStretch = 0.01

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | Separate dimensions flags
type SeparateDimensions =
  { position :: Boolean
  , scale :: Boolean
  }

-- | Motion blur settings
type MotionBlurSettings =
  { type_ :: MotionBlurType
  , shutterAngle :: Number
  , shutterPhase :: Number
  , samplesPerFrame :: Int
  , direction :: Maybe Number
  , blurLength :: Maybe Number
  , radialMode :: Maybe RadialMode
  , radialCenterX :: Maybe Number
  , radialCenterY :: Maybe Number
  , radialAmount :: Maybe Number
  }

-- | Material options for 3D layers
type MaterialOptions =
  { castsShadows :: CastsShadows
  , lightTransmission :: Number
  , acceptsShadows :: Boolean
  , acceptsLights :: Boolean
  , ambient :: Number
  , diffuse :: Number
  , specularIntensity :: Number
  , specularShininess :: Number
  , metal :: Number
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if motion blur settings are valid
isValidMotionBlurSettings :: MotionBlurSettings -> Boolean
isValidMotionBlurSettings s =
  s.shutterAngle >= 0.0 && s.shutterAngle <= maxShutterAngle &&
  s.shutterPhase >= minShutterPhase && s.shutterPhase <= maxShutterPhase &&
  s.samplesPerFrame >= minSamplesPerFrame && s.samplesPerFrame <= maxSamplesPerFrame

-- | Check if material options are valid
isValidMaterialOptions :: MaterialOptions -> Boolean
isValidMaterialOptions m =
  m.lightTransmission >= 0.0 && m.lightTransmission <= maxMaterialValue &&
  m.ambient >= 0.0 && m.ambient <= maxMaterialValue &&
  m.diffuse >= 0.0 && m.diffuse <= maxMaterialValue &&
  m.specularIntensity >= 0.0 && m.specularIntensity <= maxMaterialValue &&
  m.specularShininess >= 0.0 && m.specularShininess <= maxMaterialValue &&
  m.metal >= 0.0 && m.metal <= maxMaterialValue
