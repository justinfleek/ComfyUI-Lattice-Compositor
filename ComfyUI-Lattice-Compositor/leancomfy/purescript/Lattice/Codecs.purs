-- | Lattice.Codecs - JSON encode/decode functions for Lattice types
-- |
-- | Explicit encode/decode functions (no orphan instances).
-- | Used by serialization tests and persistence layer.

module Lattice.Codecs
  ( encodeFiniteFloat
  , decodeFiniteFloat
  , encodeNonEmptyString
  , decodeNonEmptyString
  , encodeControlMode
  , decodeControlMode
  , encodeInterpolationType
  , decodeInterpolationType
  , encodeExpressionType
  , decodeExpressionType
  , encodePropertyValueType
  , decodePropertyValueType
  , encodeAutoOrientMode
  , decodeAutoOrientMode
  , encodeBezierHandle
  , decodeBezierHandle
  , encodeKeyframe
  , decodeKeyframe
  , encodeExpression
  , decodeExpression
  , encodeAnimatableProperty
  , decodeAnimatableProperty
  , encodeLayerTransform
  , decodeLayerTransform
  , encodeMaybe
  , decodeUnitFloat
  ) where

import Prelude

import Data.Argonaut.Core (Json, jsonNull, isNull, caseJsonNumber, caseJsonString, caseJsonBoolean, caseJsonObject, caseJsonArray, fromNumber, fromString, fromBoolean, fromObject, fromArray)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Int (toNumber, floor) as Int
import Data.Traversable (traverse)
import Foreign.Object as FO
import Lattice.Primitives
  ( FiniteFloat(..), mkFiniteFloat
  , NonEmptyString(..), mkNonEmptyString
  , FrameNumber(..)
  , UnitFloat(..)
  )
import Lattice.Enums (InterpolationType(..), ExpressionType(..))
import Lattice.Entities
  ( BezierHandle, ControlMode(..), Keyframe
  , PropertyValueType(..), PropertyExpression
  , AnimatableProperty, LayerTransform
  , AutoOrientMode(..)
  )

--------------------------------------------------------------------------------
-- Primitive Codecs
--------------------------------------------------------------------------------

encodeFiniteFloat :: FiniteFloat -> Json
encodeFiniteFloat (FiniteFloat n) = fromNumber n

decodeFiniteFloat :: Json -> Either String FiniteFloat
decodeFiniteFloat json =
  caseJsonNumber (Left "Expected number") (\n ->
    case mkFiniteFloat n of
      Just ff -> Right ff
      Nothing -> Left "Number is not finite"
  ) json

encodeNonEmptyString :: NonEmptyString -> Json
encodeNonEmptyString (NonEmptyString s) = fromString s

decodeNonEmptyString :: Json -> Either String NonEmptyString
decodeNonEmptyString json =
  caseJsonString (Left "Expected string") (\s ->
    case mkNonEmptyString s of
      Just nes -> Right nes
      Nothing -> Left "String is empty"
  ) json

encodeFrameNumber :: FrameNumber -> Json
encodeFrameNumber (FrameNumber n) = fromNumber (Int.toNumber n)

decodeFrameNumber :: Json -> Either String FrameNumber
decodeFrameNumber json =
  caseJsonNumber (Left "Expected number") (\n ->
    let i = Int.floor n
    in if Int.toNumber i == n && i >= 0
       then Right (FrameNumber i)
       else Left "Expected non-negative integer"
  ) json

encodeUnitFloat :: UnitFloat -> Json
encodeUnitFloat (UnitFloat n) = fromNumber n

decodeUnitFloat :: Json -> Either String UnitFloat
decodeUnitFloat json =
  caseJsonNumber (Left "Expected number") (\n ->
    if n >= 0.0 && n <= 1.0
    then Right (UnitFloat n)
    else Left "Expected unit float [0,1]"
  ) json

--------------------------------------------------------------------------------
-- Simple Codecs
--------------------------------------------------------------------------------

encodeBoolean :: Boolean -> Json
encodeBoolean = fromBoolean

decodeBoolean :: Json -> Either String Boolean
decodeBoolean json = caseJsonBoolean (Left "Expected boolean") Right json

encodeString :: String -> Json
encodeString = fromString

decodeString :: Json -> Either String String
decodeString json = caseJsonString (Left "Expected string") Right json

--------------------------------------------------------------------------------
-- Enum Codecs
--------------------------------------------------------------------------------

encodeControlMode :: ControlMode -> Json
encodeControlMode CMSymmetric = fromString "symmetric"
encodeControlMode CMSmooth = fromString "smooth"
encodeControlMode CMCorner = fromString "corner"

decodeControlMode :: Json -> Either String ControlMode
decodeControlMode json =
  caseJsonString (Left "Expected string") (\s -> case s of
    "symmetric" -> Right CMSymmetric
    "smooth" -> Right CMSmooth
    "corner" -> Right CMCorner
    _ -> Left ("Unknown ControlMode: " <> s)
  ) json

encodeInterpolationType :: InterpolationType -> Json
encodeInterpolationType ITLinear = fromString "linear"
encodeInterpolationType ITBezier = fromString "bezier"
encodeInterpolationType ITHold = fromString "hold"
encodeInterpolationType ITEaseIn = fromString "easeIn"
encodeInterpolationType ITEaseOut = fromString "easeOut"
encodeInterpolationType ITEaseInOut = fromString "easeInOut"
encodeInterpolationType ITCustom = fromString "custom"

decodeInterpolationType :: Json -> Either String InterpolationType
decodeInterpolationType json =
  caseJsonString (Left "Expected string") (\s -> case s of
    "linear" -> Right ITLinear
    "bezier" -> Right ITBezier
    "hold" -> Right ITHold
    "easeIn" -> Right ITEaseIn
    "easeOut" -> Right ITEaseOut
    "easeInOut" -> Right ITEaseInOut
    "custom" -> Right ITCustom
    _ -> Left ("Unknown InterpolationType: " <> s)
  ) json

encodeExpressionType :: ExpressionType -> Json
encodeExpressionType EXPreset = fromString "preset"
encodeExpressionType EXCustom = fromString "custom"

decodeExpressionType :: Json -> Either String ExpressionType
decodeExpressionType json =
  caseJsonString (Left "Expected string") (\s -> case s of
    "preset" -> Right EXPreset
    "custom" -> Right EXCustom
    _ -> Left ("Unknown ExpressionType: " <> s)
  ) json

encodePropertyValueType :: PropertyValueType -> Json
encodePropertyValueType PVTNumber = fromString "number"
encodePropertyValueType PVTPosition = fromString "position"
encodePropertyValueType PVTColor = fromString "color"
encodePropertyValueType PVTEnum = fromString "enum"
encodePropertyValueType PVTVector3 = fromString "vector3"

decodePropertyValueType :: Json -> Either String PropertyValueType
decodePropertyValueType json =
  caseJsonString (Left "Expected string") (\s -> case s of
    "number" -> Right PVTNumber
    "position" -> Right PVTPosition
    "color" -> Right PVTColor
    "enum" -> Right PVTEnum
    "vector3" -> Right PVTVector3
    _ -> Left ("Unknown PropertyValueType: " <> s)
  ) json

encodeAutoOrientMode :: AutoOrientMode -> Json
encodeAutoOrientMode AOMOff = fromString "off"
encodeAutoOrientMode AOMOrientAlongPath = fromString "alongPath"
encodeAutoOrientMode AOMOrientTowardsPoi = fromString "toPointOfInterest"

decodeAutoOrientMode :: Json -> Either String AutoOrientMode
decodeAutoOrientMode json =
  caseJsonString (Left "Expected string") (\s -> case s of
    "off" -> Right AOMOff
    "alongPath" -> Right AOMOrientAlongPath
    "toPointOfInterest" -> Right AOMOrientTowardsPoi
    _ -> Left ("Unknown AutoOrientMode: " <> s)
  ) json

--------------------------------------------------------------------------------
-- Object Helpers
--------------------------------------------------------------------------------

obj :: Array (Tuple String Json) -> Json
obj pairs = fromObject (FO.fromFoldable pairs)

getField :: forall a. String -> (Json -> Either String a) -> FO.Object Json -> Either String a
getField key decoder o = case FO.lookup key o of
  Nothing -> Left ("Missing field: " <> key)
  Just json -> decoder json

getOptionalField :: forall a. String -> (Json -> Either String a) -> FO.Object Json -> Either String (Maybe a)
getOptionalField key decoder o = case FO.lookup key o of
  Nothing -> Right Nothing
  Just json ->
    if isNull json
    then Right Nothing
    else map Just (decoder json)

asObject :: Json -> Either String (FO.Object Json)
asObject json = caseJsonObject (Left "Expected object") Right json

encodeMaybe :: forall a. (a -> Json) -> Maybe a -> Json
encodeMaybe _ Nothing = jsonNull
encodeMaybe f (Just a) = f a

decodeNesArray :: Json -> Either String (Array NonEmptyString)
decodeNesArray json =
  caseJsonArray (Left "Expected array")
    (\arr -> traverse decodeNonEmptyString arr)
    json

--------------------------------------------------------------------------------
-- Entity Codecs
--------------------------------------------------------------------------------

encodeBezierHandle :: BezierHandle -> Json
encodeBezierHandle h = obj
  [ Tuple "frame" (encodeFiniteFloat h.frame)
  , Tuple "value" (encodeFiniteFloat h.value)
  , Tuple "enabled" (encodeBoolean h.enabled)
  ]

decodeBezierHandle :: Json -> Either String BezierHandle
decodeBezierHandle json = do
  o <- asObject json
  frame <- getField "frame" decodeFiniteFloat o
  value <- getField "value" decodeFiniteFloat o
  enabled <- getField "enabled" decodeBoolean o
  Right { frame, value, enabled }

encodeKeyframe :: Keyframe -> Json
encodeKeyframe k = obj
  [ Tuple "id" (encodeNonEmptyString k.id)
  , Tuple "frame" (encodeFrameNumber k.frame)
  , Tuple "value" (encodeString k.value)
  , Tuple "interpolation" (encodeInterpolationType k.interpolation)
  , Tuple "inHandle" (encodeBezierHandle k.inHandle)
  , Tuple "outHandle" (encodeBezierHandle k.outHandle)
  , Tuple "controlMode" (encodeControlMode k.controlMode)
  ]

decodeKeyframe :: Json -> Either String Keyframe
decodeKeyframe json = do
  o <- asObject json
  id <- getField "id" decodeNonEmptyString o
  frame <- getField "frame" decodeFrameNumber o
  value <- getField "value" decodeString o
  interpolation <- getField "interpolation" decodeInterpolationType o
  inHandle <- getField "inHandle" decodeBezierHandle o
  outHandle <- getField "outHandle" decodeBezierHandle o
  controlMode <- getField "controlMode" decodeControlMode o
  Right { id, frame, value, interpolation, inHandle, outHandle, controlMode }

encodeExpression :: PropertyExpression -> Json
encodeExpression e = obj
  [ Tuple "enabled" (encodeBoolean e.enabled)
  , Tuple "expressionType" (encodeExpressionType e.expressionType)
  , Tuple "name" (encodeNonEmptyString e.name)
  , Tuple "params" (encodeString e.params)
  ]

decodeExpression :: Json -> Either String PropertyExpression
decodeExpression json = do
  o <- asObject json
  enabled <- getField "enabled" decodeBoolean o
  expressionType <- getField "expressionType" decodeExpressionType o
  name <- getField "name" decodeNonEmptyString o
  params <- getField "params" decodeString o
  Right { enabled, expressionType, name, params }

encodeAnimatableProperty :: AnimatableProperty -> Json
encodeAnimatableProperty p = obj
  [ Tuple "id" (encodeNonEmptyString p.id)
  , Tuple "name" (encodeNonEmptyString p.name)
  , Tuple "propertyType" (encodePropertyValueType p.propertyType)
  , Tuple "value" (encodeString p.value)
  , Tuple "animated" (encodeBoolean p.animated)
  , Tuple "keyframes" (fromArray (map encodeNonEmptyString p.keyframes))
  , Tuple "group" (encodeMaybe encodeNonEmptyString p.group)
  , Tuple "expression" (encodeMaybe encodeExpression p.expression)
  ]

decodeAnimatableProperty :: Json -> Either String AnimatableProperty
decodeAnimatableProperty json = do
  o <- asObject json
  id <- getField "id" decodeNonEmptyString o
  name <- getField "name" decodeNonEmptyString o
  propertyType <- getField "propertyType" decodePropertyValueType o
  value <- getField "value" decodeString o
  animated <- getField "animated" decodeBoolean o
  keyframes <- getField "keyframes" decodeNesArray o
  group <- getOptionalField "group" decodeNonEmptyString o
  expression <- getOptionalField "expression" decodeExpression o
  Right { id, name, propertyType, value, animated, keyframes, group, expression }

encodeVec2 :: { x :: FiniteFloat, y :: FiniteFloat } -> Json
encodeVec2 v = obj
  [ Tuple "x" (encodeFiniteFloat v.x)
  , Tuple "y" (encodeFiniteFloat v.y)
  ]

decodeVec2 :: Json -> Either String { x :: FiniteFloat, y :: FiniteFloat }
decodeVec2 json = do
  o <- asObject json
  x <- getField "x" decodeFiniteFloat o
  y <- getField "y" decodeFiniteFloat o
  Right { x, y }

encodeLayerTransform :: LayerTransform -> Json
encodeLayerTransform t = obj
  [ Tuple "position" (encodeVec2 t.position)
  , Tuple "rotation" (encodeFiniteFloat t.rotation)
  , Tuple "scale" (encodeVec2 t.scale)
  , Tuple "anchor" (encodeVec2 t.anchor)
  , Tuple "opacity" (encodeUnitFloat t.opacity)
  ]

decodeLayerTransform :: Json -> Either String LayerTransform
decodeLayerTransform json = do
  o <- asObject json
  position <- getField "position" decodeVec2 o
  rotation <- getField "rotation" decodeFiniteFloat o
  scale <- getField "scale" decodeVec2 o
  anchor <- getField "anchor" decodeVec2 o
  opacity <- getField "opacity" decodeUnitFloat o
  Right { position, rotation, scale, anchor, opacity }
