-- | Lattice.Schemas.AI.MotionSuggestionSchema - AI motion suggestion validation
-- |
-- | Validates AI motion suggestion responses for camera/layer/particle/spline intents.
-- |
-- | Source: ui/src/schemas/ai/motion-suggestion-schema.ts

module Lattice.Schemas.AI.MotionSuggestionSchema
  ( -- Camera Motion Type
    CameraMotionType(..)
  , cameraMotionTypeFromString
  , cameraMotionTypeToString
    -- Motion Intensity
  , MotionIntensity(..)
  , motionIntensityFromString
  , motionIntensityToString
    -- Easing Type
  , EasingType(..)
  , easingTypeFromString
  , easingTypeToString
    -- Spline Usage
  , SplineUsage(..)
  , splineUsageFromString
  , splineUsageToString
    -- Particle Behavior
  , ParticleBehavior(..)
  , particleBehaviorFromString
  , particleBehaviorToString
    -- Layer Motion Type
  , LayerMotionType(..)
  , layerMotionTypeFromString
  , layerMotionTypeToString
    -- Color Scheme
  , ColorScheme(..)
  , colorSchemeFromString
  , colorSchemeToString
    -- Control Point Type
  , ControlPointType(..)
  , controlPointTypeFromString
  , controlPointTypeToString
    -- Axis
  , Axis(..)
  , axisFromString
  , axisToString
    -- Motion Axis
  , MotionAxis(..)
  , motionAxisFromString
  , motionAxisToString
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

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

derive instance Eq CameraMotionType
derive instance Generic CameraMotionType _

instance Show CameraMotionType where
  show = genericShow

cameraMotionTypeFromString :: String -> Maybe CameraMotionType
cameraMotionTypeFromString = case _ of
  "dolly" -> Just CamDolly
  "truck" -> Just CamTruck
  "pedestal" -> Just CamPedestal
  "pan" -> Just CamPan
  "tilt" -> Just CamTilt
  "roll" -> Just CamRoll
  "orbit" -> Just CamOrbit
  "drift" -> Just CamDrift
  "handheld" -> Just CamHandheld
  "crane" -> Just CamCrane
  "zoom" -> Just CamZoom
  "follow_path" -> Just CamFollowPath
  _ -> Nothing

cameraMotionTypeToString :: CameraMotionType -> String
cameraMotionTypeToString = case _ of
  CamDolly -> "dolly"
  CamTruck -> "truck"
  CamPedestal -> "pedestal"
  CamPan -> "pan"
  CamTilt -> "tilt"
  CamRoll -> "roll"
  CamOrbit -> "orbit"
  CamDrift -> "drift"
  CamHandheld -> "handheld"
  CamCrane -> "crane"
  CamZoom -> "zoom"
  CamFollowPath -> "follow_path"

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

derive instance Eq MotionIntensity
derive instance Generic MotionIntensity _

instance Show MotionIntensity where
  show = genericShow

motionIntensityFromString :: String -> Maybe MotionIntensity
motionIntensityFromString = case _ of
  "very_subtle" -> Just IntensityVerySubtle
  "subtle" -> Just IntensitySubtle
  "medium" -> Just IntensityMedium
  "strong" -> Just IntensityStrong
  "dramatic" -> Just IntensityDramatic
  _ -> Nothing

motionIntensityToString :: MotionIntensity -> String
motionIntensityToString = case _ of
  IntensityVerySubtle -> "very_subtle"
  IntensitySubtle -> "subtle"
  IntensityMedium -> "medium"
  IntensityStrong -> "strong"
  IntensityDramatic -> "dramatic"

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

derive instance Eq EasingType
derive instance Generic EasingType _

instance Show EasingType where
  show = genericShow

easingTypeFromString :: String -> Maybe EasingType
easingTypeFromString = case _ of
  "linear" -> Just EaseLinear
  "easeIn" -> Just EaseIn
  "easeOut" -> Just EaseOut
  "easeInOut" -> Just EaseInOut
  "bounce" -> Just EaseBounce
  "elastic" -> Just EaseElastic
  _ -> Nothing

easingTypeToString :: EasingType -> String
easingTypeToString = case _ of
  EaseLinear -> "linear"
  EaseIn -> "easeIn"
  EaseOut -> "easeOut"
  EaseInOut -> "easeInOut"
  EaseBounce -> "bounce"
  EaseElastic -> "elastic"

-- ────────────────────────────────────────────────────────────────────────────
-- Spline Usage
-- ────────────────────────────────────────────────────────────────────────────

-- | Spline usage options
data SplineUsage
  = SplineCameraPath
  | SplineEmitterPath
  | SplineTextPath
  | SplineLayerPath

derive instance Eq SplineUsage
derive instance Generic SplineUsage _

instance Show SplineUsage where
  show = genericShow

splineUsageFromString :: String -> Maybe SplineUsage
splineUsageFromString = case _ of
  "camera_path" -> Just SplineCameraPath
  "emitter_path" -> Just SplineEmitterPath
  "text_path" -> Just SplineTextPath
  "layer_path" -> Just SplineLayerPath
  _ -> Nothing

splineUsageToString :: SplineUsage -> String
splineUsageToString = case _ of
  SplineCameraPath -> "camera_path"
  SplineEmitterPath -> "emitter_path"
  SplineTextPath -> "text_path"
  SplineLayerPath -> "layer_path"

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

derive instance Eq ParticleBehavior
derive instance Generic ParticleBehavior _

instance Show ParticleBehavior where
  show = genericShow

particleBehaviorFromString :: String -> Maybe ParticleBehavior
particleBehaviorFromString = case _ of
  "flow" -> Just BehaviorFlow
  "drift" -> Just BehaviorDrift
  "spray" -> Just BehaviorSpray
  "turbulence" -> Just BehaviorTurbulence
  "explosion" -> Just BehaviorExplosion
  "vortex" -> Just BehaviorVortex
  "rain" -> Just BehaviorRain
  "snow" -> Just BehaviorSnow
  "fireflies" -> Just BehaviorFireflies
  "dust" -> Just BehaviorDust
  "along_path" -> Just BehaviorAlongPath
  _ -> Nothing

particleBehaviorToString :: ParticleBehavior -> String
particleBehaviorToString = case _ of
  BehaviorFlow -> "flow"
  BehaviorDrift -> "drift"
  BehaviorSpray -> "spray"
  BehaviorTurbulence -> "turbulence"
  BehaviorExplosion -> "explosion"
  BehaviorVortex -> "vortex"
  BehaviorRain -> "rain"
  BehaviorSnow -> "snow"
  BehaviorFireflies -> "fireflies"
  BehaviorDust -> "dust"
  BehaviorAlongPath -> "along_path"

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

derive instance Eq LayerMotionType
derive instance Generic LayerMotionType _

instance Show LayerMotionType where
  show = genericShow

layerMotionTypeFromString :: String -> Maybe LayerMotionType
layerMotionTypeFromString = case _ of
  "parallax" -> Just LayerParallax
  "float" -> Just LayerFloat
  "sway" -> Just LayerSway
  "breathe" -> Just LayerBreathe
  "drift" -> Just LayerDrift
  "noise" -> Just LayerNoise
  "pulse" -> Just LayerPulse
  "rotate" -> Just LayerRotate
  "follow_path" -> Just LayerFollowPath
  _ -> Nothing

layerMotionTypeToString :: LayerMotionType -> String
layerMotionTypeToString = case _ of
  LayerParallax -> "parallax"
  LayerFloat -> "float"
  LayerSway -> "sway"
  LayerBreathe -> "breathe"
  LayerDrift -> "drift"
  LayerNoise -> "noise"
  LayerPulse -> "pulse"
  LayerRotate -> "rotate"
  LayerFollowPath -> "follow_path"

-- ────────────────────────────────────────────────────────────────────────────
-- Color Scheme
-- ────────────────────────────────────────────────────────────────────────────

-- | Color scheme options
data ColorScheme = SchemeWarm | SchemeCool | SchemeNeutral | SchemeCustom

derive instance Eq ColorScheme
derive instance Generic ColorScheme _

instance Show ColorScheme where
  show = genericShow

colorSchemeFromString :: String -> Maybe ColorScheme
colorSchemeFromString = case _ of
  "warm" -> Just SchemeWarm
  "cool" -> Just SchemeCool
  "neutral" -> Just SchemeNeutral
  "custom" -> Just SchemeCustom
  _ -> Nothing

colorSchemeToString :: ColorScheme -> String
colorSchemeToString = case _ of
  SchemeWarm -> "warm"
  SchemeCool -> "cool"
  SchemeNeutral -> "neutral"
  SchemeCustom -> "custom"

-- ────────────────────────────────────────────────────────────────────────────
-- Control Point Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Control point type options
data ControlPointType = PointCorner | PointSmooth | PointSymmetric

derive instance Eq ControlPointType
derive instance Generic ControlPointType _

instance Show ControlPointType where
  show = genericShow

controlPointTypeFromString :: String -> Maybe ControlPointType
controlPointTypeFromString = case _ of
  "corner" -> Just PointCorner
  "smooth" -> Just PointSmooth
  "symmetric" -> Just PointSymmetric
  _ -> Nothing

controlPointTypeToString :: ControlPointType -> String
controlPointTypeToString = case _ of
  PointCorner -> "corner"
  PointSmooth -> "smooth"
  PointSymmetric -> "symmetric"

-- ────────────────────────────────────────────────────────────────────────────
-- Axis
-- ────────────────────────────────────────────────────────────────────────────

-- | Axis options
data Axis = AxisX | AxisY | AxisZ | AxisAll

derive instance Eq Axis
derive instance Generic Axis _

instance Show Axis where
  show = genericShow

axisFromString :: String -> Maybe Axis
axisFromString = case _ of
  "x" -> Just AxisX
  "y" -> Just AxisY
  "z" -> Just AxisZ
  "all" -> Just AxisAll
  _ -> Nothing

axisToString :: Axis -> String
axisToString = case _ of
  AxisX -> "x"
  AxisY -> "y"
  AxisZ -> "z"
  AxisAll -> "all"

-- ────────────────────────────────────────────────────────────────────────────
-- Motion Axis
-- ────────────────────────────────────────────────────────────────────────────

-- | Motion axis options
data MotionAxis = MAxisX | MAxisY | MAxisZ | MAxisScale | MAxisRotation

derive instance Eq MotionAxis
derive instance Generic MotionAxis _

instance Show MotionAxis where
  show = genericShow

motionAxisFromString :: String -> Maybe MotionAxis
motionAxisFromString = case _ of
  "x" -> Just MAxisX
  "y" -> Just MAxisY
  "z" -> Just MAxisZ
  "scale" -> Just MAxisScale
  "rotation" -> Just MAxisRotation
  _ -> Nothing

motionAxisToString :: MotionAxis -> String
motionAxisToString = case _ of
  MAxisX -> "x"
  MAxisY -> "y"
  MAxisZ -> "z"
  MAxisScale -> "scale"
  MAxisRotation -> "rotation"
