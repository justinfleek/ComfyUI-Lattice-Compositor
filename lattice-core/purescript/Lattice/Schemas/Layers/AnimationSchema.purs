-- | Lattice.Schemas.Layers.AnimationSchema - Animation keyframe and interpolation enums
-- |
-- | Animation keyframe and interpolation enums.
-- |
-- | Source: ui/src/schemas/layers/animation-schema.ts

module Lattice.Schemas.Layers.AnimationSchema
  ( -- Base Interpolation Type
    BaseInterpolationType(..)
  , baseInterpolationTypeFromString
  , baseInterpolationTypeToString
    -- Easing Type
  , EasingType(..)
  , easingTypeFromString
  , easingTypeToString
    -- Control Mode
  , ControlMode(..)
  , controlModeFromString
  , controlModeToString
    -- Property Type
  , PropertyType(..)
  , propertyTypeFromString
  , propertyTypeToString
    -- Expression Type
  , ExpressionType(..)
  , expressionTypeFromString
  , expressionTypeToString
    -- Constants
  , maxKeyframesPerProperty
  , maxNameLength
  , maxStringLength
  , maxExpressionParams
    -- Structures
  , BezierHandle
  , Vec3
    -- Validation
  , isValidBezierHandle
  , isValidVec3
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Number (isFinite)

-- ────────────────────────────────────────────────────────────────────────────
-- Base Interpolation Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Base interpolation types
data BaseInterpolationType
  = InterpLinear
  | InterpBezier
  | InterpHold

derive instance Eq BaseInterpolationType
derive instance Generic BaseInterpolationType _

instance Show BaseInterpolationType where
  show = genericShow

baseInterpolationTypeFromString :: String -> Maybe BaseInterpolationType
baseInterpolationTypeFromString = case _ of
  "linear" -> Just InterpLinear
  "bezier" -> Just InterpBezier
  "hold" -> Just InterpHold
  _ -> Nothing

baseInterpolationTypeToString :: BaseInterpolationType -> String
baseInterpolationTypeToString = case _ of
  InterpLinear -> "linear"
  InterpBezier -> "bezier"
  InterpHold -> "hold"

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

derive instance Eq EasingType
derive instance Generic EasingType _

instance Show EasingType where
  show = genericShow

easingTypeFromString :: String -> Maybe EasingType
easingTypeFromString = case _ of
  "easeInSine" -> Just EaseInSine
  "easeOutSine" -> Just EaseOutSine
  "easeInOutSine" -> Just EaseInOutSine
  "easeInQuad" -> Just EaseInQuad
  "easeOutQuad" -> Just EaseOutQuad
  "easeInOutQuad" -> Just EaseInOutQuad
  "easeInCubic" -> Just EaseInCubic
  "easeOutCubic" -> Just EaseOutCubic
  "easeInOutCubic" -> Just EaseInOutCubic
  "easeInQuart" -> Just EaseInQuart
  "easeOutQuart" -> Just EaseOutQuart
  "easeInOutQuart" -> Just EaseInOutQuart
  "easeInQuint" -> Just EaseInQuint
  "easeOutQuint" -> Just EaseOutQuint
  "easeInOutQuint" -> Just EaseInOutQuint
  "easeInExpo" -> Just EaseInExpo
  "easeOutExpo" -> Just EaseOutExpo
  "easeInOutExpo" -> Just EaseInOutExpo
  "easeInCirc" -> Just EaseInCirc
  "easeOutCirc" -> Just EaseOutCirc
  "easeInOutCirc" -> Just EaseInOutCirc
  "easeInBack" -> Just EaseInBack
  "easeOutBack" -> Just EaseOutBack
  "easeInOutBack" -> Just EaseInOutBack
  "easeInElastic" -> Just EaseInElastic
  "easeOutElastic" -> Just EaseOutElastic
  "easeInOutElastic" -> Just EaseInOutElastic
  "easeInBounce" -> Just EaseInBounce
  "easeOutBounce" -> Just EaseOutBounce
  "easeInOutBounce" -> Just EaseInOutBounce
  _ -> Nothing

easingTypeToString :: EasingType -> String
easingTypeToString = case _ of
  EaseInSine -> "easeInSine"
  EaseOutSine -> "easeOutSine"
  EaseInOutSine -> "easeInOutSine"
  EaseInQuad -> "easeInQuad"
  EaseOutQuad -> "easeOutQuad"
  EaseInOutQuad -> "easeInOutQuad"
  EaseInCubic -> "easeInCubic"
  EaseOutCubic -> "easeOutCubic"
  EaseInOutCubic -> "easeInOutCubic"
  EaseInQuart -> "easeInQuart"
  EaseOutQuart -> "easeOutQuart"
  EaseInOutQuart -> "easeInOutQuart"
  EaseInQuint -> "easeInQuint"
  EaseOutQuint -> "easeOutQuint"
  EaseInOutQuint -> "easeInOutQuint"
  EaseInExpo -> "easeInExpo"
  EaseOutExpo -> "easeOutExpo"
  EaseInOutExpo -> "easeInOutExpo"
  EaseInCirc -> "easeInCirc"
  EaseOutCirc -> "easeOutCirc"
  EaseInOutCirc -> "easeInOutCirc"
  EaseInBack -> "easeInBack"
  EaseOutBack -> "easeOutBack"
  EaseInOutBack -> "easeInOutBack"
  EaseInElastic -> "easeInElastic"
  EaseOutElastic -> "easeOutElastic"
  EaseInOutElastic -> "easeInOutElastic"
  EaseInBounce -> "easeInBounce"
  EaseOutBounce -> "easeOutBounce"
  EaseInOutBounce -> "easeInOutBounce"

-- ────────────────────────────────────────────────────────────────────────────
-- Control Mode
-- ────────────────────────────────────────────────────────────────────────────

-- | Control mode for bezier handles
data ControlMode
  = CtrlSymmetric
  | CtrlSmooth
  | CtrlCorner

derive instance Eq ControlMode
derive instance Generic ControlMode _

instance Show ControlMode where
  show = genericShow

controlModeFromString :: String -> Maybe ControlMode
controlModeFromString = case _ of
  "symmetric" -> Just CtrlSymmetric
  "smooth" -> Just CtrlSmooth
  "corner" -> Just CtrlCorner
  _ -> Nothing

controlModeToString :: ControlMode -> String
controlModeToString = case _ of
  CtrlSymmetric -> "symmetric"
  CtrlSmooth -> "smooth"
  CtrlCorner -> "corner"

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

derive instance Eq PropertyType
derive instance Generic PropertyType _

instance Show PropertyType where
  show = genericShow

propertyTypeFromString :: String -> Maybe PropertyType
propertyTypeFromString = case _ of
  "number" -> Just PropNumber
  "position" -> Just PropPosition
  "color" -> Just PropColor
  "enum" -> Just PropEnum
  "vector3" -> Just PropVector3
  _ -> Nothing

propertyTypeToString :: PropertyType -> String
propertyTypeToString = case _ of
  PropNumber -> "number"
  PropPosition -> "position"
  PropColor -> "color"
  PropEnum -> "enum"
  PropVector3 -> "vector3"

-- ────────────────────────────────────────────────────────────────────────────
-- Expression Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Expression type (preset vs custom)
data ExpressionType
  = ExprPreset
  | ExprCustom

derive instance Eq ExpressionType
derive instance Generic ExpressionType _

instance Show ExpressionType where
  show = genericShow

expressionTypeFromString :: String -> Maybe ExpressionType
expressionTypeFromString = case _ of
  "preset" -> Just ExprPreset
  "custom" -> Just ExprCustom
  _ -> Nothing

expressionTypeToString :: ExpressionType -> String
expressionTypeToString = case _ of
  ExprPreset -> "preset"
  ExprCustom -> "custom"

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
type BezierHandle =
  { frame :: Number
  , value :: Number
  , enabled :: Boolean
  }

-- | 3D vector
type Vec3 =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if bezier handle has finite values
isValidBezierHandle :: BezierHandle -> Boolean
isValidBezierHandle h = isFinite h.frame && isFinite h.value

-- | Check if Vec3 has finite values
isValidVec3 :: Vec3 -> Boolean
isValidVec3 v = isFinite v.x && isFinite v.y && isFinite v.z
