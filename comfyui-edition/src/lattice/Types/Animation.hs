-- |
-- Module      : Lattice.Types.Animation
-- Description : Animation types - keyframes, properties, interpolation
-- 
-- Migrated from ui/src/types/animation.ts
-- Depends on: Lattice.Types.Primitives
-- All numeric values must be finite (reject NaN/Infinity)
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Lattice.Types.Animation
  ( -- Core types
    AnimatableProperty(..)
  , PropertyExpression(..)
  , Keyframe(..)
  , BezierHandle(..)
  -- Interpolation types
  , ControlMode(..)
  , BaseInterpolationType(..)
  , EasingType(..)
  , InterpolationType(..)
  -- Property types
  , PropertyType(..)
  -- Property values
  , PropertyValue(..)
  , ClipboardKeyframe(..)
  -- Helper functions
  , createAnimatableProperty
  , createKeyframe  -- Returns Either Text (Keyframe a)
  -- Validation functions
  , validateKeyframesSorted
  , maxKeyframesPerProperty
  , maxExpressionParams
  -- Re-exports from Primitives
  , Vec2(..)
  , Vec3(..)
  , RGBAColor(..)
  ) where

import Control.Applicative ((<|>))
import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , object
  , (.=)
  , (.:)
  , (.:?)
  , Value(..)
  )
import Data.Aeson.Key (fromText, toText)
import Data.Aeson.KeyMap (toList)
import Data.Aeson.Types (Parser, Object)
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)
import Lattice.Types.Primitives
  ( Vec2(..)
  , Vec3(..)
  , RGBAColor(..)
  , validateFinite
  )
import Lattice.Schema.SharedValidation
  ( validateBoundedArray
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // interpolation // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Control mode for bezier handles (industry standard)
data ControlMode
  = ControlSymmetric
  | ControlSmooth
  | ControlCorner
  deriving (Eq, Show, Generic)

instance ToJSON ControlMode where
  toJSON ControlSymmetric = "symmetric"
  toJSON ControlSmooth = "smooth"
  toJSON ControlCorner = "corner"

instance FromJSON ControlMode where
  parseJSON (String "symmetric") = return ControlSymmetric
  parseJSON (String "smooth") = return ControlSmooth
  parseJSON (String "corner") = return ControlCorner
  parseJSON _ = fail "Invalid ControlMode (expected 'symmetric', 'smooth', or 'corner')"

-- | Base interpolation types
data BaseInterpolationType
  = InterpolationLinear
  | InterpolationBezier
  | InterpolationHold
  deriving (Eq, Show, Generic)

instance ToJSON BaseInterpolationType where
  toJSON InterpolationLinear = "linear"
  toJSON InterpolationBezier = "bezier"
  toJSON InterpolationHold = "hold"

instance FromJSON BaseInterpolationType where
  parseJSON (String "linear") = return InterpolationLinear
  parseJSON (String "bezier") = return InterpolationBezier
  parseJSON (String "hold") = return InterpolationHold
  parseJSON _ = fail "Invalid BaseInterpolationType"

-- | Easing function names
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
  deriving (Eq, Show, Generic)

instance ToJSON EasingType where
  toJSON EaseInSine = "easeInSine"
  toJSON EaseOutSine = "easeOutSine"
  toJSON EaseInOutSine = "easeInOutSine"
  toJSON EaseInQuad = "easeInQuad"
  toJSON EaseOutQuad = "easeOutQuad"
  toJSON EaseInOutQuad = "easeInOutQuad"
  toJSON EaseInCubic = "easeInCubic"
  toJSON EaseOutCubic = "easeOutCubic"
  toJSON EaseInOutCubic = "easeInOutCubic"
  toJSON EaseInQuart = "easeInQuart"
  toJSON EaseOutQuart = "easeOutQuart"
  toJSON EaseInOutQuart = "easeInOutQuart"
  toJSON EaseInQuint = "easeInQuint"
  toJSON EaseOutQuint = "easeOutQuint"
  toJSON EaseInOutQuint = "easeInOutQuint"
  toJSON EaseInExpo = "easeInExpo"
  toJSON EaseOutExpo = "easeOutExpo"
  toJSON EaseInOutExpo = "easeInOutExpo"
  toJSON EaseInCirc = "easeInCirc"
  toJSON EaseOutCirc = "easeOutCirc"
  toJSON EaseInOutCirc = "easeInOutCirc"
  toJSON EaseInBack = "easeInBack"
  toJSON EaseOutBack = "easeOutBack"
  toJSON EaseInOutBack = "easeInOutBack"
  toJSON EaseInElastic = "easeInElastic"
  toJSON EaseOutElastic = "easeOutElastic"
  toJSON EaseInOutElastic = "easeInOutElastic"
  toJSON EaseInBounce = "easeInBounce"
  toJSON EaseOutBounce = "easeOutBounce"
  toJSON EaseInOutBounce = "easeInOutBounce"

instance FromJSON EasingType where
  parseJSON (String "easeInSine") = return EaseInSine
  parseJSON (String "easeOutSine") = return EaseOutSine
  parseJSON (String "easeInOutSine") = return EaseInOutSine
  parseJSON (String "easeInQuad") = return EaseInQuad
  parseJSON (String "easeOutQuad") = return EaseOutQuad
  parseJSON (String "easeInOutQuad") = return EaseInOutQuad
  parseJSON (String "easeInCubic") = return EaseInCubic
  parseJSON (String "easeOutCubic") = return EaseOutCubic
  parseJSON (String "easeInOutCubic") = return EaseInOutCubic
  parseJSON (String "easeInQuart") = return EaseInQuart
  parseJSON (String "easeOutQuart") = return EaseOutQuart
  parseJSON (String "easeInOutQuart") = return EaseInOutQuart
  parseJSON (String "easeInQuint") = return EaseInQuint
  parseJSON (String "easeOutQuint") = return EaseOutQuint
  parseJSON (String "easeInOutQuint") = return EaseInOutQuint
  parseJSON (String "easeInExpo") = return EaseInExpo
  parseJSON (String "easeOutExpo") = return EaseOutExpo
  parseJSON (String "easeInOutExpo") = return EaseInOutExpo
  parseJSON (String "easeInCirc") = return EaseInCirc
  parseJSON (String "easeOutCirc") = return EaseOutCirc
  parseJSON (String "easeInOutCirc") = return EaseInOutCirc
  parseJSON (String "easeInBack") = return EaseInBack
  parseJSON (String "easeOutBack") = return EaseOutBack
  parseJSON (String "easeInOutBack") = return EaseInOutBack
  parseJSON (String "easeInElastic") = return EaseInElastic
  parseJSON (String "easeOutElastic") = return EaseOutElastic
  parseJSON (String "easeInOutElastic") = return EaseInOutElastic
  parseJSON (String "easeInBounce") = return EaseInBounce
  parseJSON (String "easeOutBounce") = return EaseOutBounce
  parseJSON (String "easeInOutBounce") = return EaseInOutBounce
  parseJSON _ = fail "Invalid EasingType"

-- | Combined interpolation type (base types + easing functions)
data InterpolationType
  = InterpolationBase BaseInterpolationType
  | InterpolationEasing EasingType
  deriving (Eq, Show, Generic)

instance ToJSON InterpolationType where
  toJSON (InterpolationBase b) = toJSON b
  toJSON (InterpolationEasing e) = toJSON e

instance FromJSON InterpolationType where
  parseJSON v =
    -- Try base type first
    (InterpolationBase <$> parseJSON v) <|>
    -- If not base, try easing
    (InterpolationEasing <$> parseJSON v)

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // bezier // handle
-- ════════════════════════════════════════════════════════════════════════════

-- | Bezier handle for keyframe curves
data BezierHandle = BezierHandle
  { bezierHandleFrame :: Double  -- Frame offset from keyframe (negative for inHandle, positive for outHandle)
  , bezierHandleValue :: Double  -- Value offset from keyframe (can be positive or negative)
  , bezierHandleEnabled :: Bool  -- Whether this handle is active (for graph editor)
  }
  deriving (Eq, Show, Generic)

instance ToJSON BezierHandle where
  toJSON (BezierHandle f v e) = object
    [ "frame" .= f
    , "value" .= v
    , "enabled" .= e
    ]

instance FromJSON BezierHandle where
  parseJSON = withObject "BezierHandle" $ \o -> do
    f <- o .: "frame"
    v <- o .: "value"
    e <- o .: "enabled"
    -- Validate finite
    if validateFinite f && validateFinite v
      then return (BezierHandle f v e)
      else fail "BezierHandle frame and value must be finite numbers"

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // property // value
-- ════════════════════════════════════════════════════════════════════════════

-- | All possible values that can be stored in keyframes.
-- Used for type-safe clipboard operations and generic property handling.
data PropertyValue
  = PropertyValueNumber Double
  | PropertyValueString Text
  | PropertyValueBool Bool
  | PropertyValueVec2 Vec2
  | PropertyValuePosition2DOr3D Vec2 (Maybe Double)  -- {x, y, z?}
  | PropertyValueVec3 Vec3
  | PropertyValueRGBA RGBAColor
  deriving (Eq, Show, Generic)

instance ToJSON PropertyValue where
  toJSON (PropertyValueNumber n) = toJSON n
  toJSON (PropertyValueString s) = toJSON s
  toJSON (PropertyValueBool b) = toJSON b
  toJSON (PropertyValueVec2 v) = toJSON v
  toJSON (PropertyValuePosition2DOr3D v mz) =
    case mz of
      Nothing -> toJSON v
      Just z -> object ["x" .= vec2X v, "y" .= vec2Y v, "z" .= z]
  toJSON (PropertyValueVec3 v) = toJSON v
  toJSON (PropertyValueRGBA c) = toJSON c

instance FromJSON PropertyValue where
  parseJSON v@(Number _) = PropertyValueNumber <$> parseJSON v
  parseJSON v@(String _) = PropertyValueString <$> parseJSON v
  parseJSON v@(Bool _) = PropertyValueBool <$> parseJSON v
  parseJSON v@(Object o) =
    (do rgba <- parseJSON v :: Parser RGBAColor
        return (PropertyValueRGBA rgba)) <|>
    (do vec3 <- parseJSON v :: Parser Vec3
        return (PropertyValueVec3 vec3)) <|>
    (do x <- o .: "x"
        y <- o .: "y"
        mz <- o .:? "z"
        if validateFinite x && validateFinite y && maybe True validateFinite mz
          then case mz of
            Nothing -> return (PropertyValueVec2 (Vec2 x y))
            Just z -> return (PropertyValuePosition2DOr3D (Vec2 x y) (Just z))
          else fail "PropertyValue position components must be finite") <|>
    (do vec2 <- parseJSON v :: Parser Vec2
        return (PropertyValueVec2 vec2))
  parseJSON _ = fail "Invalid PropertyValue"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // keyframe
-- ════════════════════════════════════════════════════════════════════════════

-- | Keyframe with bezier handles for smooth interpolation
data Keyframe a = Keyframe
  { keyframeId :: Text
  , keyframeFrame :: Double  -- Frame number (>= 1, 1-indexed)
  , keyframeValue :: a
  , keyframeInterpolation :: InterpolationType
  , keyframeInHandle :: BezierHandle
  , keyframeOutHandle :: BezierHandle
  , keyframeControlMode :: ControlMode
  , keyframeSpatialInTangent :: Maybe Vec3  -- Spatial tangents for position keyframes (motion path curves)
  , keyframeSpatialOutTangent :: Maybe Vec3
  }
  deriving (Eq, Show, Generic)

instance ToJSON a => ToJSON (Keyframe a) where
  toJSON (Keyframe id_ frame val interp inH outH ctrlMode mSpatialIn mSpatialOut) =
    let
      baseFields = ["id" .= id_, "frame" .= frame, "value" .= val, "interpolation" .= interp, "inHandle" .= inH, "outHandle" .= outH, "controlMode" .= ctrlMode]
      withSpatialIn = case mSpatialIn of
        Just t -> ("spatialInTangent" .= t) : baseFields
        Nothing -> baseFields
      withSpatialOut = case mSpatialOut of
        Just t -> ("spatialOutTangent" .= t) : withSpatialIn
        Nothing -> withSpatialIn
    in object withSpatialOut

instance FromJSON a => FromJSON (Keyframe a) where
  parseJSON = withObject "Keyframe" $ \o -> do
    id_ <- o .: "id"
    frame <- o .: "frame"
    val <- o .: "value"
    interp <- o .: "interpolation"
    inH <- o .: "inHandle"
    outH <- o .: "outHandle"
    ctrlMode <- o .: "controlMode"
    mSpatialIn <- o .:? "spatialInTangent"
    mSpatialOut <- o .:? "spatialOutTangent"
    -- Validate frame is finite
    if validateFinite frame
      then return (Keyframe id_ frame val interp inH outH ctrlMode mSpatialIn mSpatialOut)
      else fail "Keyframe frame must be finite number"

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // property // expression
-- ════════════════════════════════════════════════════════════════════════════

-- | Expression attached to a property
-- Evaluated after keyframe interpolation to add dynamic behavior
data PropertyExpression = PropertyExpression
  { propertyExpressionEnabled :: Bool  -- Whether the expression is active
  , propertyExpressionType :: ExpressionType  -- 'preset' for named expressions, 'custom' for user scripts
  , propertyExpressionName :: Text  -- Expression name (for presets: 'jitter', 'repeatAfter', 'inertia', etc.)
  , propertyExpressionParams :: [(Text, ExpressionParamValue)]  -- Expression parameters
  }
  deriving (Eq, Show, Generic)

-- | Expression type
data ExpressionType
  = ExpressionPreset
  | ExpressionCustom
  deriving (Eq, Show, Generic)

instance ToJSON ExpressionType where
  toJSON ExpressionPreset = "preset"
  toJSON ExpressionCustom = "custom"

instance FromJSON ExpressionType where
  parseJSON (String "preset") = return ExpressionPreset
  parseJSON (String "custom") = return ExpressionCustom
  parseJSON _ = fail "Invalid ExpressionType (expected 'preset' or 'custom')"

-- | Expression parameter value (number, string, or boolean)
data ExpressionParamValue
  = ExpressionParamNumber Double
  | ExpressionParamString Text
  | ExpressionParamBool Bool
  deriving (Eq, Show, Generic)

instance ToJSON ExpressionParamValue where
  toJSON (ExpressionParamNumber n) = toJSON n
  toJSON (ExpressionParamString s) = toJSON s
  toJSON (ExpressionParamBool b) = toJSON b

instance FromJSON ExpressionParamValue where
  parseJSON v@(Number _) = ExpressionParamNumber <$> parseJSON v
  parseJSON v@(String _) = ExpressionParamString <$> parseJSON v
  parseJSON v@(Bool _) = ExpressionParamBool <$> parseJSON v
  parseJSON _ = fail "ExpressionParamValue must be number, string, or boolean"

instance ToJSON PropertyExpression where
  toJSON (PropertyExpression enabled typ name params) =
    object
      [ "enabled" .= enabled
      , "type" .= typ
      , "name" .= name
      , "params" .= object (map (\(k, v) -> fromText k .= v) params)
      ]

instance FromJSON PropertyExpression where
  parseJSON = withObject "PropertyExpression" $ \o -> do
    enabled <- o .: "enabled"
    typ <- o .: "type"
    name <- o .: "name"
    paramsObj <- o .: "params"
    -- Parse params object as key-value pairs
    params <- withObject "params" (\paramsO -> do
      let pairs = toList paramsO
      if length pairs > maxExpressionParams
        then fail ("Maximum " <> show maxExpressionParams <> " expression parameters allowed")
        else mapM (\(k, v) -> do
          paramVal <- parseJSON v :: Parser ExpressionParamValue
          return (toText k, paramVal)) pairs) paramsObj
    return (PropertyExpression enabled typ name params)

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // animatable // property
-- ════════════════════════════════════════════════════════════════════════════

-- | Property type for animatable properties
data PropertyType
  = PropertyTypeNumber
  | PropertyTypePosition
  | PropertyTypeColor
  | PropertyTypeEnum
  | PropertyTypeVector3
  deriving (Eq, Show, Generic)

instance ToJSON PropertyType where
  toJSON PropertyTypeNumber = "number"
  toJSON PropertyTypePosition = "position"
  toJSON PropertyTypeColor = "color"
  toJSON PropertyTypeEnum = "enum"
  toJSON PropertyTypeVector3 = "vector3"

instance FromJSON PropertyType where
  parseJSON (String "number") = return PropertyTypeNumber
  parseJSON (String "position") = return PropertyTypePosition
  parseJSON (String "color") = return PropertyTypeColor
  parseJSON (String "enum") = return PropertyTypeEnum
  parseJSON (String "vector3") = return PropertyTypeVector3
  parseJSON _ = fail "Invalid PropertyType"

-- | Animatable property with optional keyframes and expressions
data AnimatableProperty a = AnimatableProperty
  { animatablePropertyId :: Text
  , animatablePropertyName :: Text
  , animatablePropertyType :: PropertyType
  , animatablePropertyValue :: a  -- Default/current value
  , animatablePropertyAnimated :: Bool
  , animatablePropertyKeyframes :: [Keyframe a]
  , animatablePropertyGroup :: Maybe Text  -- Property group for timeline organization (e.g., "Transform", "Text", "More Options")
  , animatablePropertyExpression :: Maybe PropertyExpression  -- Expression system - applies post-interpolation modifications
  }
  deriving (Eq, Show, Generic)

instance ToJSON a => ToJSON (AnimatableProperty a) where
  toJSON (AnimatableProperty id_ name typ val animated keyframes mGroup mExpr) =
    let
      baseFields = ["id" .= id_, "name" .= name, "type" .= typ, "value" .= val, "animated" .= animated, "keyframes" .= keyframes]
      withGroup = case mGroup of
        Just g -> ("group" .= g) : baseFields
        Nothing -> baseFields
      withExpr = case mExpr of
        Just e -> ("expression" .= e) : withGroup
        Nothing -> withGroup
    in object withExpr

instance FromJSON a => FromJSON (AnimatableProperty a) where
  parseJSON = withObject "AnimatableProperty" $ \o -> do
    id_ <- o .: "id"
    name <- o .: "name"
    typ <- o .: "type"
    val <- o .: "value"
    animated <- o .: "animated"
    keyframesRaw <- o .: "keyframes"
    mGroup <- o .:? "group"
    mExpr <- o .:? "expression"
    -- Validate max 10,000 keyframes per property (matches Zod schema)
    keyframes <- case validateBoundedArray maxKeyframesPerProperty keyframesRaw of
      Left err -> fail (T.unpack err)
      Right kfs ->
        -- If animated is true, validate keyframes are sorted by frame
        if animated
          then case validateKeyframesSorted kfs of
            Left err -> fail (T.unpack err)
            Right sorted -> return sorted
          else return kfs
    return (AnimatableProperty id_ name typ val animated keyframes mGroup mExpr)

-- ════════════════════════════════════════════════════════════════════════════
--                                                     // clipboard // keyframe
-- ════════════════════════════════════════════════════════════════════════════

-- | Clipboard keyframe entry with property path context
data ClipboardKeyframe = ClipboardKeyframe
  { clipboardKeyframeLayerId :: Text
  , clipboardKeyframePropertyPath :: Text
  , clipboardKeyframeKeyframes :: [Keyframe PropertyValue]
  }
  deriving (Eq, Show, Generic)

instance ToJSON ClipboardKeyframe where
  toJSON (ClipboardKeyframe layerId propPath keyframes) =
    object
      [ "layerId" .= layerId
      , "propertyPath" .= propPath
      , "keyframes" .= keyframes
      ]

instance FromJSON ClipboardKeyframe where
  parseJSON = withObject "ClipboardKeyframe" $ \o -> do
    layerId <- o .: "layerId"
    propPath <- o .: "propertyPath"
    keyframesRaw <- o .: "keyframes"
    -- Validate max 10,000 keyframes in clipboard (matches Zod schema)
    keyframes <- case validateBoundedArray maxKeyframesPerProperty keyframesRaw of
      Left err -> fail (T.unpack err)
      Right kfs -> return kfs
    return (ClipboardKeyframe layerId propPath keyframes)

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // validation // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Maximum keyframes per property (matches Zod schema)
maxKeyframesPerProperty :: Int
maxKeyframesPerProperty = 10000

-- | Maximum expression parameters (matches Zod schema)
maxExpressionParams :: Int
maxExpressionParams = 1000

-- | Validate that keyframes are sorted by frame (non-decreasing)
-- Matches Zod schema refinement: "Keyframes must be sorted by frame when animated"
validateKeyframesSorted :: [Keyframe a] -> Either Text [Keyframe a]
validateKeyframesSorted [] = Right []
validateKeyframesSorted [k] = Right [k]
validateKeyframesSorted (k1:k2:ks) =
  if keyframeFrame k2 >= keyframeFrame k1
    then do
      rest <- validateKeyframesSorted (k2:ks)
      return (k1:rest)
    else Left "Keyframes must be sorted by frame when animated"

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // helper // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Create a new animatable property with default values
-- Note: ID generation should be done by the caller or use a proper ID generator
createAnimatableProperty
  :: Text  -- id (must be provided - no auto-generation to avoid IO)
  -> Text  -- name
  -> a  -- value
  -> PropertyType  -- type
  -> Maybe Text  -- group (optional)
  -> AnimatableProperty a
createAnimatableProperty id_ name val typ mGroup =
  AnimatableProperty
    { animatablePropertyId = id_
    , animatablePropertyName = name
    , animatablePropertyType = typ
    , animatablePropertyValue = val
    , animatablePropertyAnimated = False
    , animatablePropertyKeyframes = []
    , animatablePropertyGroup = mGroup
    , animatablePropertyExpression = Nothing
    }

-- | Create a default keyframe
-- 
--                                              // bezier // handle // defaults
-- - inHandle: { frame: -5, value: 0, enabled: True }
-- - outHandle: { frame: 5, value: 0, enabled: True }
-- 
-- The ±5 frame offset creates a gentle ease curve by default.
-- At 30fps: 5 frames = ~0.167 seconds of influence
-- At 16fps: 5 frames = ~0.313 seconds of influence
-- 
-- A value of 0 means flat tangent (no acceleration at the keyframe).
-- 
-- These defaults were chosen to provide reasonable ease-in/ease-out
-- behavior without requiring manual handle adjustment for most animations.
-- | Create a default keyframe
-- Note: ID generation should be done by the caller or use a proper ID generator
-- Returns Either error message or valid Keyframe
createKeyframe
  :: Text  -- id (must be provided - no auto-generation to avoid IO)
  -> Double  -- frame (must be finite and >= 1)
  -> a  -- value
  -> InterpolationType  -- interpolation
  -> Either Text (Keyframe a)
createKeyframe id_ frame val interp =
  if validateFinite frame && frame >= 1
    then Right $ Keyframe
      { keyframeId = id_
      , keyframeFrame = frame
      , keyframeValue = val
      , keyframeInterpolation = interp
      , keyframeInHandle = BezierHandle (-5) 0 True
      , keyframeOutHandle = BezierHandle 5 0 True
      , keyframeControlMode = ControlSmooth
      , keyframeSpatialInTangent = Nothing
      , keyframeSpatialOutTangent = Nothing
      }
    else Left ("Invalid keyframe frame: frame must be finite and >= 1")
