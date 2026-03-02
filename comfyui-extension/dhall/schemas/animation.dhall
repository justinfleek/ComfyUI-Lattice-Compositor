-- |
-- Module      : Lattice.Schema.Animation
-- Description : Animation type definitions and validation constants
--
-- Migrated from ui/src/schemas/layers/animation-schema.ts
-- Defines animation types: interpolation, keyframes, properties, expressions

let Primitives = ./primitives.dhall

-- ============================================================================
-- Validation Constants
-- ============================================================================

let MAX_KEYFRAMES_PER_PROPERTY = 10000 : Natural

let MAX_EXPRESSION_PARAMS = 1000 : Natural

-- ============================================================================
-- Interpolation Types
-- ============================================================================

let BaseInterpolationType = < Linear | Bezier | Hold >

let EasingType =
      < EaseInSine
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
      >

let InterpolationType = < Base : BaseInterpolationType | Easing : EasingType >

-- ============================================================================
-- Bezier Handle
-- ============================================================================

let BezierHandle = { frame : Primitives.FiniteNumber, value : Primitives.FiniteNumber, enabled : Bool }

let ControlMode = < Symmetric | Smooth | Corner >

-- ============================================================================
-- Property Value Types
-- ============================================================================

let PropertyValue =
      < Number : Primitives.FiniteNumber
      | String : Text
      | Vec2 : Primitives.Vec2
      | Position2DOr3D : Primitives.Position2DOr3D
      | Vec3 : Primitives.Vec3
      | RGBA : Primitives.RGBAColor
      >

-- ============================================================================
-- Keyframe Schema
-- ============================================================================

let Keyframe = { id : Primitives.EntityId, frame : Primitives.FrameNumber, value : PropertyValue, interpolation : InterpolationType, inHandle : BezierHandle, outHandle : BezierHandle, controlMode : ControlMode, spatialInTangent : Optional Primitives.Vec3, spatialOutTangent : Optional Primitives.Vec3 }

-- ============================================================================
-- Property Expression
-- ============================================================================

let ExpressionType = < Preset | Custom >

let ExpressionParamValue = < Number : Primitives.FiniteNumber | String : Text | Bool : Bool >

let PropertyExpression = { enabled : Bool, type : ExpressionType, name : Text, params : { mapKey : Text, mapValue : ExpressionParamValue } }

-- ============================================================================
-- Property Type
-- ============================================================================

let PropertyType = < Number | Position | Color | Enum | Vector3 >

-- ============================================================================
-- Animatable Property
-- ============================================================================

let AnimatableProperty = { id : Primitives.EntityId, name : Text, type : PropertyType, value : PropertyValue, animated : Bool, keyframes : List Keyframe, group : Optional Text, expression : Optional PropertyExpression }

-- ============================================================================
-- Clipboard Keyframe
-- ============================================================================

let ClipboardKeyframe = { layerId : Primitives.EntityId, propertyPath : Text, keyframes : List Keyframe }

-- ============================================================================
-- Export
-- ============================================================================

in  { MAX_KEYFRAMES_PER_PROPERTY
    , MAX_EXPRESSION_PARAMS
    , BaseInterpolationType
    , EasingType
    , InterpolationType
    , BezierHandle
    , ControlMode
    , PropertyValue
    , Keyframe
    , ExpressionType
    , ExpressionParamValue
    , PropertyExpression
    , PropertyType
    , AnimatableProperty
    , ClipboardKeyframe
    }
