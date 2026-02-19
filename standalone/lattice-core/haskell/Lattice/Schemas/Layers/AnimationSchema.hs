{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Layers.AnimationSchema
Description : Animation keyframe and interpolation enums
Copyright   : (c) Lattice, 2026
License     : MIT

Animation keyframe and interpolation enums.

Source: ui/src/schemas/layers/animation-schema.ts
-}

module Lattice.Schemas.Layers.AnimationSchema
  ( -- * Base Interpolation Type
    BaseInterpolationType(..)
  , baseInterpolationTypeFromText
  , baseInterpolationTypeToText
    -- * Easing Type
  , EasingType(..)
  , easingTypeFromText
  , easingTypeToText
    -- * Control Mode
  , ControlMode(..)
  , controlModeFromText
  , controlModeToText
    -- * Property Type
  , PropertyType(..)
  , propertyTypeFromText
  , propertyTypeToText
    -- * Expression Type
  , ExpressionType(..)
  , expressionTypeFromText
  , expressionTypeToText
    -- * Constants
  , maxKeyframesPerProperty
  , maxNameLength
  , maxStringLength
  , maxExpressionParams
    -- * Structures
  , BezierHandle(..)
  , Vec3(..)
    -- * Validation
  , isValidBezierHandle
  , isValidVec3
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

-- ────────────────────────────────────────────────────────────────────────────
-- Base Interpolation Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Base interpolation types
data BaseInterpolationType
  = InterpLinear
  | InterpBezier
  | InterpHold
  deriving stock (Eq, Show, Generic, Enum, Bounded)

baseInterpolationTypeFromText :: Text -> Maybe BaseInterpolationType
baseInterpolationTypeFromText "linear" = Just InterpLinear
baseInterpolationTypeFromText "bezier" = Just InterpBezier
baseInterpolationTypeFromText "hold" = Just InterpHold
baseInterpolationTypeFromText _ = Nothing

baseInterpolationTypeToText :: BaseInterpolationType -> Text
baseInterpolationTypeToText InterpLinear = "linear"
baseInterpolationTypeToText InterpBezier = "bezier"
baseInterpolationTypeToText InterpHold = "hold"

-- ────────────────────────────────────────────────────────────────────────────
-- Easing Type
-- ────────────────────────────────────────────────────────────────────────────

-- | All easing function names
data EasingType
  = EaseInSine
  | EaseOutSine
  | EaseInOutSine
  | EaseInQuad
  | EaseOutQuad
  | EaseInOutQuad
  | EaseInCubic
  | EaseOutCubic
  | EaseInOutCubic
  | EaseInQuart
  | EaseOutQuart
  | EaseInOutQuart
  | EaseInQuint
  | EaseOutQuint
  | EaseInOutQuint
  | EaseInExpo
  | EaseOutExpo
  | EaseInOutExpo
  | EaseInCirc
  | EaseOutCirc
  | EaseInOutCirc
  | EaseInBack
  | EaseOutBack
  | EaseInOutBack
  | EaseInElastic
  | EaseOutElastic
  | EaseInOutElastic
  | EaseInBounce
  | EaseOutBounce
  | EaseInOutBounce
  deriving stock (Eq, Show, Generic, Enum, Bounded)

easingTypeFromText :: Text -> Maybe EasingType
easingTypeFromText "easeInSine" = Just EaseInSine
easingTypeFromText "easeOutSine" = Just EaseOutSine
easingTypeFromText "easeInOutSine" = Just EaseInOutSine
easingTypeFromText "easeInQuad" = Just EaseInQuad
easingTypeFromText "easeOutQuad" = Just EaseOutQuad
easingTypeFromText "easeInOutQuad" = Just EaseInOutQuad
easingTypeFromText "easeInCubic" = Just EaseInCubic
easingTypeFromText "easeOutCubic" = Just EaseOutCubic
easingTypeFromText "easeInOutCubic" = Just EaseInOutCubic
easingTypeFromText "easeInQuart" = Just EaseInQuart
easingTypeFromText "easeOutQuart" = Just EaseOutQuart
easingTypeFromText "easeInOutQuart" = Just EaseInOutQuart
easingTypeFromText "easeInQuint" = Just EaseInQuint
easingTypeFromText "easeOutQuint" = Just EaseOutQuint
easingTypeFromText "easeInOutQuint" = Just EaseInOutQuint
easingTypeFromText "easeInExpo" = Just EaseInExpo
easingTypeFromText "easeOutExpo" = Just EaseOutExpo
easingTypeFromText "easeInOutExpo" = Just EaseInOutExpo
easingTypeFromText "easeInCirc" = Just EaseInCirc
easingTypeFromText "easeOutCirc" = Just EaseOutCirc
easingTypeFromText "easeInOutCirc" = Just EaseInOutCirc
easingTypeFromText "easeInBack" = Just EaseInBack
easingTypeFromText "easeOutBack" = Just EaseOutBack
easingTypeFromText "easeInOutBack" = Just EaseInOutBack
easingTypeFromText "easeInElastic" = Just EaseInElastic
easingTypeFromText "easeOutElastic" = Just EaseOutElastic
easingTypeFromText "easeInOutElastic" = Just EaseInOutElastic
easingTypeFromText "easeInBounce" = Just EaseInBounce
easingTypeFromText "easeOutBounce" = Just EaseOutBounce
easingTypeFromText "easeInOutBounce" = Just EaseInOutBounce
easingTypeFromText _ = Nothing

easingTypeToText :: EasingType -> Text
easingTypeToText EaseInSine = "easeInSine"
easingTypeToText EaseOutSine = "easeOutSine"
easingTypeToText EaseInOutSine = "easeInOutSine"
easingTypeToText EaseInQuad = "easeInQuad"
easingTypeToText EaseOutQuad = "easeOutQuad"
easingTypeToText EaseInOutQuad = "easeInOutQuad"
easingTypeToText EaseInCubic = "easeInCubic"
easingTypeToText EaseOutCubic = "easeOutCubic"
easingTypeToText EaseInOutCubic = "easeInOutCubic"
easingTypeToText EaseInQuart = "easeInQuart"
easingTypeToText EaseOutQuart = "easeOutQuart"
easingTypeToText EaseInOutQuart = "easeInOutQuart"
easingTypeToText EaseInQuint = "easeInQuint"
easingTypeToText EaseOutQuint = "easeOutQuint"
easingTypeToText EaseInOutQuint = "easeInOutQuint"
easingTypeToText EaseInExpo = "easeInExpo"
easingTypeToText EaseOutExpo = "easeOutExpo"
easingTypeToText EaseInOutExpo = "easeInOutExpo"
easingTypeToText EaseInCirc = "easeInCirc"
easingTypeToText EaseOutCirc = "easeOutCirc"
easingTypeToText EaseInOutCirc = "easeInOutCirc"
easingTypeToText EaseInBack = "easeInBack"
easingTypeToText EaseOutBack = "easeOutBack"
easingTypeToText EaseInOutBack = "easeInOutBack"
easingTypeToText EaseInElastic = "easeInElastic"
easingTypeToText EaseOutElastic = "easeOutElastic"
easingTypeToText EaseInOutElastic = "easeInOutElastic"
easingTypeToText EaseInBounce = "easeInBounce"
easingTypeToText EaseOutBounce = "easeOutBounce"
easingTypeToText EaseInOutBounce = "easeInOutBounce"

-- ────────────────────────────────────────────────────────────────────────────
-- Control Mode
-- ────────────────────────────────────────────────────────────────────────────

-- | Control mode for bezier handles
data ControlMode
  = CtrlSymmetric
  | CtrlSmooth
  | CtrlCorner
  deriving stock (Eq, Show, Generic, Enum, Bounded)

controlModeFromText :: Text -> Maybe ControlMode
controlModeFromText "symmetric" = Just CtrlSymmetric
controlModeFromText "smooth" = Just CtrlSmooth
controlModeFromText "corner" = Just CtrlCorner
controlModeFromText _ = Nothing

controlModeToText :: ControlMode -> Text
controlModeToText CtrlSymmetric = "symmetric"
controlModeToText CtrlSmooth = "smooth"
controlModeToText CtrlCorner = "corner"

-- ────────────────────────────────────────────────────────────────────────────
-- Property Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Property type enum
data PropertyType
  = PropNumber
  | PropPosition
  | PropColor
  | PropEnum
  | PropVector3
  deriving stock (Eq, Show, Generic, Enum, Bounded)

propertyTypeFromText :: Text -> Maybe PropertyType
propertyTypeFromText "number" = Just PropNumber
propertyTypeFromText "position" = Just PropPosition
propertyTypeFromText "color" = Just PropColor
propertyTypeFromText "enum" = Just PropEnum
propertyTypeFromText "vector3" = Just PropVector3
propertyTypeFromText _ = Nothing

propertyTypeToText :: PropertyType -> Text
propertyTypeToText PropNumber = "number"
propertyTypeToText PropPosition = "position"
propertyTypeToText PropColor = "color"
propertyTypeToText PropEnum = "enum"
propertyTypeToText PropVector3 = "vector3"

-- ────────────────────────────────────────────────────────────────────────────
-- Expression Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Expression type (preset vs custom)
data ExpressionType
  = ExprPreset
  | ExprCustom
  deriving stock (Eq, Show, Generic, Enum, Bounded)

expressionTypeFromText :: Text -> Maybe ExpressionType
expressionTypeFromText "preset" = Just ExprPreset
expressionTypeFromText "custom" = Just ExprCustom
expressionTypeFromText _ = Nothing

expressionTypeToText :: ExpressionType -> Text
expressionTypeToText ExprPreset = "preset"
expressionTypeToText ExprCustom = "custom"

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxKeyframesPerProperty :: Int
maxKeyframesPerProperty = 10000

maxNameLength :: Int
maxNameLength = 200

maxStringLength :: Int
maxStringLength = 10000

maxExpressionParams :: Int
maxExpressionParams = 1000

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | Bezier handle for keyframe curves
data BezierHandle = BezierHandle
  { bhFrame :: !Double
  , bhValue :: !Double
  , bhEnabled :: !Bool
  }
  deriving stock (Eq, Show, Generic)

-- | 3D vector
data Vec3 = Vec3
  { vecX :: !Double
  , vecY :: !Double
  , vecZ :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if bezier handle has finite values
isValidBezierHandle :: BezierHandle -> Bool
isValidBezierHandle h =
  not (isNaN (bhFrame h) || isInfinite (bhFrame h)) &&
  not (isNaN (bhValue h) || isInfinite (bhValue h))

-- | Check if Vec3 has finite values
isValidVec3 :: Vec3 -> Bool
isValidVec3 v =
  not (isNaN (vecX v) || isInfinite (vecX v)) &&
  not (isNaN (vecY v) || isInfinite (vecY v)) &&
  not (isNaN (vecZ v) || isInfinite (vecZ v))
