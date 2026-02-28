-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // motion // property
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Animatable properties for motion graphics layers.
-- |
-- | Properties are the individual values that can be animated on a layer.
-- | Each property has a type, can have keyframes, and may support expressions.
-- |
-- | ## Property Types
-- |
-- | - **Transform**: Position, Scale, Rotation, Anchor, Opacity
-- | - **Geometry**: Path, Mask, UV coordinates
-- | - **Appearance**: Fill color, Stroke, Effects
-- | - **Audio**: Volume, Pan, Tone
-- |
-- | ## Architecture
-- |
-- | This module mirrors `Lattice.Entities` from the Lattice Haskell backend.

module Hydrogen.Schema.Motion.Property
  ( -- * Property Value Type
    PropertyValueType(..)
  , propertyValueTypeToString
  , propertyValueTypeFromString
  , isPropertyValueNumeric
  , isPropertyValueVector
  
  -- * Property Expression
  , PropertyExpression(..)
  , defaultPropertyExpression
  , propertyExpressionEnabled
  
  -- * Expression Type
  , ExpressionType(..)
  , expressionTypeToString
  , expressionTypeFromString
  , isExpressionTypeMath
  , isExpressionTypeTime
  
  -- * Animatable Property Identifier
  , AnimatablePropertyId(..)
  , mkAnimatablePropertyId
  , unwrapAnimatablePropertyId
  
  -- * Animatable Property
  , AnimatableProperty(..)
  , defaultAnimatableProperty
  , propertyAnimated
  , propertyHasKeyframes
  , propertyHasExpression
  
  -- * Property Group
  , PropertyGroup(..)
  , propertyGroupName
  , propertyGroupProperties
  
  -- * Property Path
  , PropertyPath(..)
  , propertyPathToString
  , propertyPathFromString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , ($)
  , (<>)
  , (&&)
  , not
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Array (null, uncons) as Array
import Data.String (split) as String
import Data.String.Pattern (Pattern(Pattern))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // property // value // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of value a property can hold.
-- |
-- | Determines how the property is animated and what operations are valid.
data PropertyValueType
  = PVTNumber         -- Single numeric value
  | PVTPosition       -- 2D/3D position (x, y) or (x, y, z)
  | PVTColor          -- Color (r, g, b, a)
  | PVTEnum           -- Enumerated value (blend mode, etc.)
  | PVTVector3        -- 3D vector (for 3D transforms)

derive instance eqPropertyValueType :: Eq PropertyValueType
derive instance ordPropertyValueType :: Ord PropertyValueType

instance showPropertyValueType :: Show PropertyValueType where
  show = propertyValueTypeToString

-- | Convert property value type to string.
propertyValueTypeToString :: PropertyValueType -> String
propertyValueTypeToString PVTNumber = "number"
propertyValueTypeToString PVTPosition = "position"
propertyValueTypeToString PVTColor = "color"
propertyValueTypeToString PVTEnum = "enum"
propertyValueTypeToString PVTVector3 = "vector3"

-- | Parse property value type from string.
propertyValueTypeFromString :: String -> Maybe PropertyValueType
propertyValueTypeFromString "number" = Just PVTNumber
propertyValueTypeFromString "position" = Just PVTPosition
propertyValueTypeFromString "color" = Just PVTColor
propertyValueTypeFromString "enum" = Just PVTEnum
propertyValueTypeFromString "vector3" = Just PVTVector3
propertyValueTypeFromString _ = Nothing

-- | Check if property value type is numeric.
isPropertyValueNumeric :: PropertyValueType -> Boolean
isPropertyValueNumeric PVTNumber = true
isPropertyValueNumeric _ = false

-- | Check if property value type is a vector.
isPropertyValueVector :: PropertyValueType -> Boolean
isPropertyValueVector PVTPosition = true
isPropertyValueVector PVTVector3 = true
isPropertyValueVector _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // expression // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of expression that can be applied to a property.
-- |
-- | Expressions allow procedural animation based on time, other properties, etc.
data ExpressionType
  -- Math expressions
  = ETWiggle          -- Random wiggle
  | ETTime            -- Current time
  | ETLoop            -- Loop animation
  | ETLinear          -- Linear interpolation
  | ETHold            -- Hold value
  | ETSmooth          -- Smooth interpolation
  
  -- Property references
  | ETThisProperty    -- Reference to this property
  | ETComp            -- Reference to composition
  | ETLayer           -- Reference to layer
  | ETMarker          -- Reference to marker
  
  -- Math operations
  | ETAdd             -- Addition
  | ETSubtract        -- Subtraction
  | ETMultiply        -- Multiplication
  | ETDivide          -- Division
  | ETModulo          -- Modulo
  
  -- Vector operations
  | ETLength          -- Vector length
  | ETNormalize       -- Normalize vector
  | ETDistance        -- Distance between points
  | ETClamp           -- Clamp value to range
  | ETLerp            -- Linear interpolation
  
  -- Noise
  | ETNoise           -- Perlin noise
  | ETSimplexNoise    -- Simplex noise
  
  -- Audio reactive
  | ETAudioSpectrum   -- Audio spectrum data
  | ETAudioLevel      -- Audio level
  
  -- Custom
  | ETCustom String   -- Custom expression (parsed at runtime)

derive instance eqExpressionType :: Eq ExpressionType
derive instance ordExpressionType :: Ord ExpressionType

instance showExpressionType :: Show ExpressionType where
  show = expressionTypeToString

-- | Convert expression type to string.
expressionTypeToString :: ExpressionType -> String
expressionTypeToString ETWiggle = "wiggle"
expressionTypeToString ETTime = "time"
expressionTypeToString ETLoop = "loop"
expressionTypeToString ETLinear = "linear"
expressionTypeToString ETHold = "hold"
expressionTypeToString ETSmooth = "smooth"
expressionTypeToString ETThisProperty = "thisProperty"
expressionTypeToString ETComp = "comp"
expressionTypeToString ETLayer = "layer"
expressionTypeToString ETMarker = "marker"
expressionTypeToString ETAdd = "add"
expressionTypeToString ETSubtract = "subtract"
expressionTypeToString ETMultiply = "multiply"
expressionTypeToString ETDivide = "divide"
expressionTypeToString ETModulo = "modulo"
expressionTypeToString ETLength = "length"
expressionTypeToString ETNormalize = "normalize"
expressionTypeToString ETDistance = "distance"
expressionTypeToString ETClamp = "clamp"
expressionTypeToString ETLerp = "lerp"
expressionTypeToString ETNoise = "noise"
expressionTypeToString ETSimplexNoise = "simplexNoise"
expressionTypeToString ETAudioSpectrum = "audioSpectrum"
expressionTypeToString ETAudioLevel = "audioLevel"
expressionTypeToString (ETCustom s) = "custom:" <> s

-- | Parse expression type from string.
expressionTypeFromString :: String -> Maybe ExpressionType
expressionTypeFromString "wiggle" = Just ETWiggle
expressionTypeFromString "time" = Just ETTime
expressionTypeFromString "loop" = Just ETLoop
expressionTypeFromString "hold" = Just ETHold
expressionTypeFromString "smooth" = Just ETSmooth
expressionTypeFromString "thisProperty" = Just ETThisProperty
expressionTypeFromString "comp" = Just ETComp
expressionTypeFromString "layer" = Just ETLayer
expressionTypeFromString "marker" = Just ETMarker
expressionTypeFromString "add" = Just ETAdd
expressionTypeFromString "subtract" = Just ETSubtract
expressionTypeFromString "multiply" = Just ETMultiply
expressionTypeFromString "divide" = Just ETDivide
expressionTypeFromString "modulo" = Just ETModulo
expressionTypeFromString "length" = Just ETLength
expressionTypeFromString "normalize" = Just ETNormalize
expressionTypeFromString "distance" = Just ETDistance
expressionTypeFromString "lerp" = Just ETLerp
expressionTypeFromString "noise" = Just ETNoise
expressionTypeFromString "simplexNoise" = Just ETSimplexNoise
expressionTypeFromString "audioSpectrum" = Just ETAudioSpectrum
expressionTypeFromString "audioLevel" = Just ETAudioLevel
expressionTypeFromString s =
  case String.split (Pattern ":") s of
    ["custom", rest] -> Just (ETCustom rest)
    _ -> Nothing

-- | Check if expression type is a math operation.
isExpressionTypeMath :: ExpressionType -> Boolean
isExpressionTypeMath ETAdd = true
isExpressionTypeMath ETSubtract = true
isExpressionTypeMath ETMultiply = true
isExpressionTypeMath ETDivide = true
isExpressionTypeMath ETModulo = true
isExpressionTypeMath ETLength = true
isExpressionTypeMath ETNormalize = true
isExpressionTypeMath ETDistance = true
isExpressionTypeMath ETLerp = true
isExpressionTypeMath _ = false

-- | Check if expression type is time-based.
isExpressionTypeTime :: ExpressionType -> Boolean
isExpressionTypeTime ETTime = true
isExpressionTypeTime ETWiggle = true
isExpressionTypeTime ETLoop = true
isExpressionTypeTime ETSmooth = true
isExpressionTypeTime ETNoise = true
isExpressionTypeTime ETSimplexNoise = true
isExpressionTypeTime _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // property // expression
-- ═════════════════════════════════════════════════════════════════════════════

-- | Property expression for procedural animation.
-- |
-- | Expressions allow properties to be computed from other values
-- | rather than just keyframed.
newtype PropertyExpression = PropertyExpression
  { enabled :: Boolean
  , expressionType :: ExpressionType
  , expressionCode :: String      -- Raw expression code
  , parameters :: String          -- JSON-encoded parameters
  }

derive instance eqPropertyExpression :: Eq PropertyExpression

instance showPropertyExpression :: Show PropertyExpression where
  show (PropertyExpression e) = 
    "Expression(" <> expressionTypeToString e.expressionType <> ")"

-- | Default property expression (disabled).
defaultPropertyExpression :: PropertyExpression
defaultPropertyExpression = PropertyExpression
  { enabled: false
  , expressionType: ETHold
  , expressionCode: ""
  , parameters: "{}"
  }

-- | Check if expression is enabled.
propertyExpressionEnabled :: PropertyExpression -> Boolean
propertyExpressionEnabled (PropertyExpression e) = e.enabled

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // animatable // property // id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for an animatable property.
-- |
-- | Uses NonEmptyString semantics — must have at least one character.
newtype AnimatablePropertyId = AnimatablePropertyId String

derive instance eqAnimatablePropertyId :: Eq AnimatablePropertyId
derive instance ordAnimatablePropertyId :: Ord AnimatablePropertyId

instance showAnimatablePropertyId :: Show AnimatablePropertyId where
  show (AnimatablePropertyId s) = "(AnimatablePropertyId " <> s <> ")"

-- | Smart constructor for AnimatablePropertyId.
-- | Returns Nothing for empty strings.
mkAnimatablePropertyId :: String -> Maybe AnimatablePropertyId
mkAnimatablePropertyId "" = Nothing
mkAnimatablePropertyId s = Just (AnimatablePropertyId s)

-- | Unwrap property ID to String.
unwrapAnimatablePropertyId :: AnimatablePropertyId -> String
unwrapAnimatablePropertyId (AnimatablePropertyId s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // animatable // property
-- ═════════════════════════════════════════════════════════════════════════════

-- | An animatable property on a layer.
-- |
-- | Contains the property metadata, current value, keyframes, and optional
-- | expression for procedural animation.
newtype AnimatableProperty = AnimatableProperty
  { id :: String
  , name :: String
  , propertyType :: PropertyValueType
  , value :: String            -- JSON-encoded value
  , animated :: Boolean
  , keyframeIds :: Array String
  , group :: Maybe String
  , expression :: Maybe PropertyExpression
  , simplified :: Boolean     -- Use simplified UI
  , locked :: Boolean         -- Cannot be edited
  , elided :: Boolean         -- Hidden in UI
  }

derive instance eqAnimatableProperty :: Eq AnimatableProperty

instance showAnimatableProperty :: Show AnimatableProperty where
  show (AnimatableProperty p) = 
    "Property(" <> p.name <> 
    (if p.animated then " [animated]" else "") <>
    (case p.expression of
      Just _ -> " [expression]"
      Nothing -> "") <>
    ")"

-- | Default animatable property.
defaultAnimatableProperty :: String -> String -> PropertyValueType -> AnimatableProperty
defaultAnimatableProperty id name pvt = AnimatableProperty
  { id: id
  , name: name
  , propertyType: pvt
  , value: "null"
  , animated: false
  , keyframeIds: []
  , group: Nothing
  , expression: Nothing
  , simplified: false
  , locked: false
  , elided: false
  }

-- | Check if property is animated (has keyframes).
propertyAnimated :: AnimatableProperty -> Boolean
propertyAnimated (AnimatableProperty p) = p.animated

-- | Check if property has keyframes.
propertyHasKeyframes :: AnimatableProperty -> Boolean
propertyHasKeyframes (AnimatableProperty p) = 
  p.animated && (not (Array.null p.keyframeIds))

-- | Check if property has an expression.
propertyHasExpression :: AnimatableProperty -> Boolean
propertyHasExpression (AnimatableProperty p) =
  case p.expression of
    Just (PropertyExpression e) -> e.enabled
    Nothing -> false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // property // group
-- ═════════════════════════════════════════════════════════════════════════════

-- | Group of related properties.
-- |
-- | Properties are organized into groups for UI organization.
newtype PropertyGroup = PropertyGroup
  { id :: String
  , name :: String
  , properties :: Array AnimatableProperty
  , collapsed :: Boolean
  }

derive instance eqPropertyGroup :: Eq PropertyGroup

instance showPropertyGroup :: Show PropertyGroup where
  show (PropertyGroup g) = "Group(" <> g.name <> ")"

-- | Get property group name.
propertyGroupName :: PropertyGroup -> String
propertyGroupName (PropertyGroup g) = g.name

-- | Get properties in group.
propertyGroupProperties :: PropertyGroup -> Array AnimatableProperty
propertyGroupProperties (PropertyGroup g) = g.properties

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // property // path
-- ═════════════════════════════════════════════════════════════════════════════

-- | Path to a property in the property tree.
-- |
-- | Example: "Transform/Position/X" identifies the X component of position.
newtype PropertyPath = PropertyPath (Array String)

derive instance eqPropertyPath :: Eq PropertyPath
derive instance ordPropertyPath :: Ord PropertyPath

instance showPropertyPath :: Show PropertyPath where
  show = propertyPathToString

-- | Convert property path to string.
propertyPathToString :: PropertyPath -> String
propertyPathToString (PropertyPath segments) =
  case segments of
    [] -> ""
    [x] -> x
    xs -> foldSegments xs
  where
    foldSegments :: Array String -> String
    foldSegments arr = case Array.uncons arr of
      Nothing -> ""
      Just { head: x, tail: [] } -> x
      Just { head: x, tail: ys } -> x <> "/" <> foldSegments ys

-- | Parse property path from string.
propertyPathFromString :: String -> PropertyPath
propertyPathFromString s =
  PropertyPath $ parsePath s
  where
    parsePath :: String -> Array String
    parsePath str = 
      case str of
        "" -> []
        _ -> 
          let
            parts = String.split (Pattern "/") str
          in
            parts
