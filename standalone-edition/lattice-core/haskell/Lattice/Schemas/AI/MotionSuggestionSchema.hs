{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.AI.MotionSuggestionSchema
Description : AI motion suggestion validation
Copyright   : (c) Lattice, 2026
License     : MIT

Validates AI motion suggestion responses for camera/layer/particle/spline intents.

Source: ui/src/schemas/ai/motion-suggestion-schema.ts
-}

module Lattice.Schemas.AI.MotionSuggestionSchema
  ( -- * Camera Motion Type
    CameraMotionType(..)
  , cameraMotionTypeFromText
  , cameraMotionTypeToText
    -- * Motion Intensity
  , MotionIntensity(..)
  , motionIntensityFromText
  , motionIntensityToText
    -- * Easing Type
  , EasingType(..)
  , easingTypeFromText
  , easingTypeToText
    -- * Spline Usage
  , SplineUsage(..)
  , splineUsageFromText
  , splineUsageToText
    -- * Particle Behavior
  , ParticleBehavior(..)
  , particleBehaviorFromText
  , particleBehaviorToText
    -- * Layer Motion Type
  , LayerMotionType(..)
  , layerMotionTypeFromText
  , layerMotionTypeToText
    -- * Color Scheme
  , ColorScheme(..)
  , colorSchemeFromText
  , colorSchemeToText
    -- * Control Point Type
  , ControlPointType(..)
  , controlPointTypeFromText
  , controlPointTypeToText
    -- * Axis
  , Axis(..)
  , axisFromText
  , axisToText
    -- * Motion Axis
  , MotionAxis(..)
  , motionAxisFromText
  , motionAxisToText
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

-- ────────────────────────────────────────────────────────────────────────────
-- Camera Motion Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Camera motion type options
data CameraMotionType
  = CamDolly
  | CamTruck
  | CamPedestal
  | CamPan
  | CamTilt
  | CamRoll
  | CamOrbit
  | CamDrift
  | CamHandheld
  | CamCrane
  | CamZoom
  | CamFollowPath
  deriving stock (Eq, Show, Generic, Enum, Bounded)

cameraMotionTypeFromText :: Text -> Maybe CameraMotionType
cameraMotionTypeFromText "dolly" = Just CamDolly
cameraMotionTypeFromText "truck" = Just CamTruck
cameraMotionTypeFromText "pedestal" = Just CamPedestal
cameraMotionTypeFromText "pan" = Just CamPan
cameraMotionTypeFromText "tilt" = Just CamTilt
cameraMotionTypeFromText "roll" = Just CamRoll
cameraMotionTypeFromText "orbit" = Just CamOrbit
cameraMotionTypeFromText "drift" = Just CamDrift
cameraMotionTypeFromText "handheld" = Just CamHandheld
cameraMotionTypeFromText "crane" = Just CamCrane
cameraMotionTypeFromText "zoom" = Just CamZoom
cameraMotionTypeFromText "follow_path" = Just CamFollowPath
cameraMotionTypeFromText _ = Nothing

cameraMotionTypeToText :: CameraMotionType -> Text
cameraMotionTypeToText CamDolly = "dolly"
cameraMotionTypeToText CamTruck = "truck"
cameraMotionTypeToText CamPedestal = "pedestal"
cameraMotionTypeToText CamPan = "pan"
cameraMotionTypeToText CamTilt = "tilt"
cameraMotionTypeToText CamRoll = "roll"
cameraMotionTypeToText CamOrbit = "orbit"
cameraMotionTypeToText CamDrift = "drift"
cameraMotionTypeToText CamHandheld = "handheld"
cameraMotionTypeToText CamCrane = "crane"
cameraMotionTypeToText CamZoom = "zoom"
cameraMotionTypeToText CamFollowPath = "follow_path"

-- ────────────────────────────────────────────────────────────────────────────
-- Motion Intensity
-- ────────────────────────────────────────────────────────────────────────────

-- | Motion intensity levels
data MotionIntensity
  = IntensityVerySubtle
  | IntensitySubtle
  | IntensityMedium
  | IntensityStrong
  | IntensityDramatic
  deriving stock (Eq, Show, Generic, Enum, Bounded)

motionIntensityFromText :: Text -> Maybe MotionIntensity
motionIntensityFromText "very_subtle" = Just IntensityVerySubtle
motionIntensityFromText "subtle" = Just IntensitySubtle
motionIntensityFromText "medium" = Just IntensityMedium
motionIntensityFromText "strong" = Just IntensityStrong
motionIntensityFromText "dramatic" = Just IntensityDramatic
motionIntensityFromText _ = Nothing

motionIntensityToText :: MotionIntensity -> Text
motionIntensityToText IntensityVerySubtle = "very_subtle"
motionIntensityToText IntensitySubtle = "subtle"
motionIntensityToText IntensityMedium = "medium"
motionIntensityToText IntensityStrong = "strong"
motionIntensityToText IntensityDramatic = "dramatic"

-- ────────────────────────────────────────────────────────────────────────────
-- Easing Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Easing type options
data EasingType
  = EaseLinear
  | EaseIn
  | EaseOut
  | EaseInOut
  | EaseBounce
  | EaseElastic
  deriving stock (Eq, Show, Generic, Enum, Bounded)

easingTypeFromText :: Text -> Maybe EasingType
easingTypeFromText "linear" = Just EaseLinear
easingTypeFromText "easeIn" = Just EaseIn
easingTypeFromText "easeOut" = Just EaseOut
easingTypeFromText "easeInOut" = Just EaseInOut
easingTypeFromText "bounce" = Just EaseBounce
easingTypeFromText "elastic" = Just EaseElastic
easingTypeFromText _ = Nothing

easingTypeToText :: EasingType -> Text
easingTypeToText EaseLinear = "linear"
easingTypeToText EaseIn = "easeIn"
easingTypeToText EaseOut = "easeOut"
easingTypeToText EaseInOut = "easeInOut"
easingTypeToText EaseBounce = "bounce"
easingTypeToText EaseElastic = "elastic"

-- ────────────────────────────────────────────────────────────────────────────
-- Spline Usage
-- ────────────────────────────────────────────────────────────────────────────

-- | Spline usage options
data SplineUsage
  = SplineCameraPath
  | SplineEmitterPath
  | SplineTextPath
  | SplineLayerPath
  deriving stock (Eq, Show, Generic, Enum, Bounded)

splineUsageFromText :: Text -> Maybe SplineUsage
splineUsageFromText "camera_path" = Just SplineCameraPath
splineUsageFromText "emitter_path" = Just SplineEmitterPath
splineUsageFromText "text_path" = Just SplineTextPath
splineUsageFromText "layer_path" = Just SplineLayerPath
splineUsageFromText _ = Nothing

splineUsageToText :: SplineUsage -> Text
splineUsageToText SplineCameraPath = "camera_path"
splineUsageToText SplineEmitterPath = "emitter_path"
splineUsageToText SplineTextPath = "text_path"
splineUsageToText SplineLayerPath = "layer_path"

-- ────────────────────────────────────────────────────────────────────────────
-- Particle Behavior
-- ────────────────────────────────────────────────────────────────────────────

-- | Particle behavior options
data ParticleBehavior
  = BehaviorFlow
  | BehaviorDrift
  | BehaviorSpray
  | BehaviorTurbulence
  | BehaviorExplosion
  | BehaviorVortex
  | BehaviorRain
  | BehaviorSnow
  | BehaviorFireflies
  | BehaviorDust
  | BehaviorAlongPath
  deriving stock (Eq, Show, Generic, Enum, Bounded)

particleBehaviorFromText :: Text -> Maybe ParticleBehavior
particleBehaviorFromText "flow" = Just BehaviorFlow
particleBehaviorFromText "drift" = Just BehaviorDrift
particleBehaviorFromText "spray" = Just BehaviorSpray
particleBehaviorFromText "turbulence" = Just BehaviorTurbulence
particleBehaviorFromText "explosion" = Just BehaviorExplosion
particleBehaviorFromText "vortex" = Just BehaviorVortex
particleBehaviorFromText "rain" = Just BehaviorRain
particleBehaviorFromText "snow" = Just BehaviorSnow
particleBehaviorFromText "fireflies" = Just BehaviorFireflies
particleBehaviorFromText "dust" = Just BehaviorDust
particleBehaviorFromText "along_path" = Just BehaviorAlongPath
particleBehaviorFromText _ = Nothing

particleBehaviorToText :: ParticleBehavior -> Text
particleBehaviorToText BehaviorFlow = "flow"
particleBehaviorToText BehaviorDrift = "drift"
particleBehaviorToText BehaviorSpray = "spray"
particleBehaviorToText BehaviorTurbulence = "turbulence"
particleBehaviorToText BehaviorExplosion = "explosion"
particleBehaviorToText BehaviorVortex = "vortex"
particleBehaviorToText BehaviorRain = "rain"
particleBehaviorToText BehaviorSnow = "snow"
particleBehaviorToText BehaviorFireflies = "fireflies"
particleBehaviorToText BehaviorDust = "dust"
particleBehaviorToText BehaviorAlongPath = "along_path"

-- ────────────────────────────────────────────────────────────────────────────
-- Layer Motion Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Layer motion type options
data LayerMotionType
  = LayerParallax
  | LayerFloat
  | LayerSway
  | LayerBreathe
  | LayerDrift
  | LayerNoise
  | LayerPulse
  | LayerRotate
  | LayerFollowPath
  deriving stock (Eq, Show, Generic, Enum, Bounded)

layerMotionTypeFromText :: Text -> Maybe LayerMotionType
layerMotionTypeFromText "parallax" = Just LayerParallax
layerMotionTypeFromText "float" = Just LayerFloat
layerMotionTypeFromText "sway" = Just LayerSway
layerMotionTypeFromText "breathe" = Just LayerBreathe
layerMotionTypeFromText "drift" = Just LayerDrift
layerMotionTypeFromText "noise" = Just LayerNoise
layerMotionTypeFromText "pulse" = Just LayerPulse
layerMotionTypeFromText "rotate" = Just LayerRotate
layerMotionTypeFromText "follow_path" = Just LayerFollowPath
layerMotionTypeFromText _ = Nothing

layerMotionTypeToText :: LayerMotionType -> Text
layerMotionTypeToText LayerParallax = "parallax"
layerMotionTypeToText LayerFloat = "float"
layerMotionTypeToText LayerSway = "sway"
layerMotionTypeToText LayerBreathe = "breathe"
layerMotionTypeToText LayerDrift = "drift"
layerMotionTypeToText LayerNoise = "noise"
layerMotionTypeToText LayerPulse = "pulse"
layerMotionTypeToText LayerRotate = "rotate"
layerMotionTypeToText LayerFollowPath = "follow_path"

-- ────────────────────────────────────────────────────────────────────────────
-- Color Scheme
-- ────────────────────────────────────────────────────────────────────────────

-- | Color scheme options
data ColorScheme = SchemeWarm | SchemeCool | SchemeNeutral | SchemeCustom
  deriving stock (Eq, Show, Generic, Enum, Bounded)

colorSchemeFromText :: Text -> Maybe ColorScheme
colorSchemeFromText "warm" = Just SchemeWarm
colorSchemeFromText "cool" = Just SchemeCool
colorSchemeFromText "neutral" = Just SchemeNeutral
colorSchemeFromText "custom" = Just SchemeCustom
colorSchemeFromText _ = Nothing

colorSchemeToText :: ColorScheme -> Text
colorSchemeToText SchemeWarm = "warm"
colorSchemeToText SchemeCool = "cool"
colorSchemeToText SchemeNeutral = "neutral"
colorSchemeToText SchemeCustom = "custom"

-- ────────────────────────────────────────────────────────────────────────────
-- Control Point Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Control point type options
data ControlPointType = PointCorner | PointSmooth | PointSymmetric
  deriving stock (Eq, Show, Generic, Enum, Bounded)

controlPointTypeFromText :: Text -> Maybe ControlPointType
controlPointTypeFromText "corner" = Just PointCorner
controlPointTypeFromText "smooth" = Just PointSmooth
controlPointTypeFromText "symmetric" = Just PointSymmetric
controlPointTypeFromText _ = Nothing

controlPointTypeToText :: ControlPointType -> Text
controlPointTypeToText PointCorner = "corner"
controlPointTypeToText PointSmooth = "smooth"
controlPointTypeToText PointSymmetric = "symmetric"

-- ────────────────────────────────────────────────────────────────────────────
-- Axis
-- ────────────────────────────────────────────────────────────────────────────

-- | Axis options
data Axis = AxisX | AxisY | AxisZ | AxisAll
  deriving stock (Eq, Show, Generic, Enum, Bounded)

axisFromText :: Text -> Maybe Axis
axisFromText "x" = Just AxisX
axisFromText "y" = Just AxisY
axisFromText "z" = Just AxisZ
axisFromText "all" = Just AxisAll
axisFromText _ = Nothing

axisToText :: Axis -> Text
axisToText AxisX = "x"
axisToText AxisY = "y"
axisToText AxisZ = "z"
axisToText AxisAll = "all"

-- ────────────────────────────────────────────────────────────────────────────
-- Motion Axis
-- ────────────────────────────────────────────────────────────────────────────

-- | Motion axis options
data MotionAxis = MAxisX | MAxisY | MAxisZ | MAxisScale | MAxisRotation
  deriving stock (Eq, Show, Generic, Enum, Bounded)

motionAxisFromText :: Text -> Maybe MotionAxis
motionAxisFromText "x" = Just MAxisX
motionAxisFromText "y" = Just MAxisY
motionAxisFromText "z" = Just MAxisZ
motionAxisFromText "scale" = Just MAxisScale
motionAxisFromText "rotation" = Just MAxisRotation
motionAxisFromText _ = Nothing

motionAxisToText :: MotionAxis -> Text
motionAxisToText MAxisX = "x"
motionAxisToText MAxisY = "y"
motionAxisToText MAxisZ = "z"
motionAxisToText MAxisScale = "scale"
motionAxisToText MAxisRotation = "rotation"
