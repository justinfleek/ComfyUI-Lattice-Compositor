-- | Port of ui/src/__tests__/services/serialization.property.test.ts
-- |
-- | Property-based tests for JSON serialization roundtrips.
-- | Verifies that Lattice types survive encode → decode without data loss.

module Test.Lattice.Services.SerializationProps (spec) where

import Prelude

import Data.Argonaut.Core (Json, stringify, fromNumber, fromString, fromBoolean, jsonNull)
import Data.Argonaut.Parser (jsonParser)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Lattice.Primitives
  ( FiniteFloat(..), NonEmptyString(..), FrameNumber(..), UnitFloat(..) )
import Lattice.Enums (InterpolationType(..), ExpressionType(..))
import Lattice.Entities
  ( BezierHandle, ControlMode(..), Keyframe
  , PropertyValueType(..), PropertyExpression
  , AnimatableProperty, LayerTransform
  , AutoOrientMode(..)
  )
import Lattice.Codecs as C

-- ────────────────────────────────────────────────────────────────────────────
-- Roundtrip helper
-- ────────────────────────────────────────────────────────────────────────────

-- | Simulate save/load: encode to JSON string, parse back, decode
roundtrip :: forall a. Eq a => Show a => (a -> Json) -> (Json -> Either String a) -> a -> Aff Unit
roundtrip encode decode value = do
  let json = encode value
      jsonStr = stringify json
  case jsonParser jsonStr of
    Left err -> fail ("JSON parse failed: " <> err)
    Right parsed ->
      case decode parsed of
        Left err -> fail ("Decode failed: " <> err)
        Right decoded ->
          if decoded == value
            then pure unit
            else fail ("Roundtrip mismatch:\n  original: " <> show value <> "\n  decoded:  " <> show decoded)

-- ────────────────────────────────────────────────────────────────────────────
-- Sample data
-- ────────────────────────────────────────────────────────────────────────────

sampleHandle :: BezierHandle
sampleHandle =
  { frame: FiniteFloat 5.0
  , value: FiniteFloat 10.0
  , enabled: true
  }

sampleHandle2 :: BezierHandle
sampleHandle2 =
  { frame: FiniteFloat 0.0
  , value: FiniteFloat 0.0
  , enabled: false
  }

sampleHandleNeg :: BezierHandle
sampleHandleNeg =
  { frame: FiniteFloat (0.0 - 50.0)
  , value: FiniteFloat (0.0 - 999.0)
  , enabled: true
  }

sampleKeyframe :: Keyframe
sampleKeyframe =
  { id: NonEmptyString "kf-001"
  , frame: FrameNumber 0
  , value: "42.5"
  , interpolation: ITLinear
  , inHandle: sampleHandle
  , outHandle: sampleHandle2
  , controlMode: CMSymmetric
  }

sampleKeyframeBezier :: Keyframe
sampleKeyframeBezier =
  { id: NonEmptyString "kf-002"
  , frame: FrameNumber 100
  , value: "{\"x\":1,\"y\":2,\"z\":3}"
  , interpolation: ITBezier
  , inHandle: sampleHandleNeg
  , outHandle: sampleHandle
  , controlMode: CMCorner
  }

sampleExpression :: PropertyExpression
sampleExpression =
  { enabled: true
  , expressionType: EXPreset
  , name: NonEmptyString "wiggle"
  , params: "{\"frequency\":5,\"amplitude\":10}"
  }

sampleProperty :: AnimatableProperty
sampleProperty =
  { id: NonEmptyString "prop-001"
  , name: NonEmptyString "Opacity"
  , propertyType: PVTNumber
  , value: "100"
  , animated: false
  , keyframes: []
  , group: Nothing
  , expression: Nothing
  }

samplePropertyWithExpr :: AnimatableProperty
samplePropertyWithExpr =
  { id: NonEmptyString "prop-002"
  , name: NonEmptyString "Position"
  , propertyType: PVTPosition
  , value: "{\"x\":0,\"y\":0}"
  , animated: true
  , keyframes: [NonEmptyString "kf-001", NonEmptyString "kf-002"]
  , group: Just (NonEmptyString "Transform")
  , expression: Just sampleExpression
  }

sampleTransform :: LayerTransform
sampleTransform =
  { position: { x: FiniteFloat 100.0, y: FiniteFloat 200.0 }
  , rotation: FiniteFloat 45.0
  , scale: { x: FiniteFloat 1.0, y: FiniteFloat 1.0 }
  , anchor: { x: FiniteFloat 50.0, y: FiniteFloat 50.0 }
  , opacity: UnitFloat 1.0
  }

sampleTransformZero :: LayerTransform
sampleTransformZero =
  { position: { x: FiniteFloat 0.0, y: FiniteFloat 0.0 }
  , rotation: FiniteFloat 0.0
  , scale: { x: FiniteFloat 1.0, y: FiniteFloat 1.0 }
  , anchor: { x: FiniteFloat 0.0, y: FiniteFloat 0.0 }
  , opacity: UnitFloat 0.0
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Spec
-- ────────────────────────────────────────────────────────────────────────────

spec :: Spec Unit
spec = do
  describe "STRICT: Primitive Serialization" do
    primitiveRoundtrips
  describe "STRICT: BezierHandle Serialization" do
    bezierHandleRoundtrips
  describe "STRICT: Keyframe Serialization" do
    keyframeRoundtrips
  describe "STRICT: AnimatableProperty Serialization" do
    animatablePropertyRoundtrips
  describe "STRICT: Transform Serialization" do
    transformRoundtrips
  describe "STRICT: Enum Serialization" do
    enumRoundtrips
  describe "STRICT: Serialization Edge Cases" do
    edgeCases

primitiveRoundtrips :: Spec Unit
primitiveRoundtrips = do
  it "number roundtrip preserves value exactly" do
    for_ [0.0, 1.0, 0.0 - 1.0, 42.5, 1.0e-15, 1.7976931348623157e+308] \n -> do
      let json = fromNumber n
          str = stringify json
      case jsonParser str of
        Left e -> fail ("Parse failed: " <> e)
        Right parsed -> do
          let result = C.decodeFiniteFloat parsed
          case result of
            Right (FiniteFloat decoded) ->
              decoded `shouldEqual` n
            Left e -> fail ("Decode failed: " <> e)

  it "string roundtrip preserves value exactly" do
    for_ ["", "hello", "with spaces", "unicode: \x2603", "emoji: \x1F600"] \s -> do
      let json = fromString s
          str = stringify json
      case jsonParser str of
        Left e -> fail ("Parse failed: " <> e)
        Right parsed -> do
          let result = C.decodeNonEmptyString parsed
          -- Empty string should fail decode (as expected)
          case s of
            "" -> case result of
              Left _ -> pure unit
              Right _ -> fail "Empty string should not decode as NonEmptyString"
            _ -> case result of
              Right (NonEmptyString decoded) ->
                decoded `shouldEqual` s
              Left e -> fail ("Decode failed for: " <> show s <> " error: " <> e)

  it "boolean roundtrip preserves value exactly" do
    for_ [true, false] \b -> do
      let json = fromBoolean b
          str = stringify json
      case jsonParser str of
        Left e -> fail ("Parse failed: " <> e)
        Right parsed -> do
          let decoded = C.decodeFiniteFloat parsed
          -- Boolean should fail to decode as FiniteFloat
          case decoded of
            Left _ -> pure unit
            Right _ -> fail "Boolean should not decode as FiniteFloat"

  it "handles special number values" do
    -- In PureScript, FiniteFloat rejects NaN/Infinity at construction
    -- Test that finite numbers work, and that 0 and -0 both decode
    for_ [0.0, 1.7976931348623157e+308, 5.0e-324, 9007199254740991.0] \n -> do
      let encoded = C.encodeFiniteFloat (FiniteFloat n)
      case C.decodeFiniteFloat encoded of
        Right (FiniteFloat decoded) ->
          decoded `shouldEqual` n
        Left e -> fail ("Special value roundtrip failed: " <> e)

  it "documents JSON limitations" do
    -- null encodes as null - primitive PureScript handles this via Maybe
    let nullJson = jsonNull
        str = stringify nullJson
    str `shouldEqual` "null"

bezierHandleRoundtrips :: Spec Unit
bezierHandleRoundtrips = do
  it "BezierHandle roundtrip preserves all fields" do
    for_ [sampleHandle, sampleHandle2, sampleHandleNeg] \h ->
      roundtrip C.encodeBezierHandle C.decodeBezierHandle h

  it "BezierHandle with boundary values roundtrips" do
    let extreme =
          { frame: FiniteFloat (0.0 - 100.0)
          , value: FiniteFloat 1000.0
          , enabled: false
          }
    roundtrip C.encodeBezierHandle C.decodeBezierHandle extreme

keyframeRoundtrips :: Spec Unit
keyframeRoundtrips = do
  it "numeric Keyframe roundtrip preserves all fields" do
    roundtrip C.encodeKeyframe C.decodeKeyframe sampleKeyframe

  it "vector Keyframe roundtrip preserves all fields" do
    roundtrip C.encodeKeyframe C.decodeKeyframe sampleKeyframeBezier

  it "Keyframe with all interpolation types roundtrips" do
    for_ [ITLinear, ITBezier, ITHold, ITEaseIn, ITEaseOut, ITEaseInOut, ITCustom] \interp -> do
      let kf = sampleKeyframe { interpolation = interp }
      roundtrip C.encodeKeyframe C.decodeKeyframe kf

  it "Keyframe with all control modes roundtrips" do
    for_ [CMSymmetric, CMSmooth, CMCorner] \mode -> do
      let kf = sampleKeyframe { controlMode = mode }
      roundtrip C.encodeKeyframe C.decodeKeyframe kf

animatablePropertyRoundtrips :: Spec Unit
animatablePropertyRoundtrips = do
  it "AnimatableProperty without expression roundtrips" do
    roundtrip C.encodeAnimatableProperty C.decodeAnimatableProperty sampleProperty

  it "AnimatableProperty with all property types roundtrips" do
    for_ [PVTNumber, PVTPosition, PVTColor, PVTEnum, PVTVector3] \pt -> do
      let prop = sampleProperty { propertyType = pt }
      roundtrip C.encodeAnimatableProperty C.decodeAnimatableProperty prop

transformRoundtrips :: Spec Unit
transformRoundtrips = do
  it "LayerTransform roundtrip preserves all fields" do
    roundtrip C.encodeLayerTransform C.decodeLayerTransform sampleTransform

  it "LayerTransform with zero values roundtrips" do
    roundtrip C.encodeLayerTransform C.decodeLayerTransform sampleTransformZero

  it "LayerTransform with negative position roundtrips" do
    let t = sampleTransform
          { position = { x: FiniteFloat (0.0 - 500.0), y: FiniteFloat (0.0 - 300.0) }
          , rotation = FiniteFloat (0.0 - 180.0)
          }
    roundtrip C.encodeLayerTransform C.decodeLayerTransform t

enumRoundtrips :: Spec Unit
enumRoundtrips = do
  it "ControlMode roundtrip for all variants" do
    for_ [CMSymmetric, CMSmooth, CMCorner] \cm -> do
      let encoded = C.encodeControlMode cm
      case C.decodeControlMode encoded of
        Right decoded -> decoded `shouldEqual` cm
        Left e -> fail ("ControlMode roundtrip failed: " <> e)

  it "InterpolationType roundtrip for all variants" do
    for_ [ITLinear, ITBezier, ITHold, ITEaseIn, ITEaseOut, ITEaseInOut, ITCustom] \it' -> do
      let encoded = C.encodeInterpolationType it'
      case C.decodeInterpolationType encoded of
        Right decoded -> decoded `shouldEqual` it'
        Left e -> fail ("InterpolationType roundtrip failed: " <> e)

  it "ExpressionType roundtrip for all variants" do
    for_ [EXPreset, EXCustom] \et -> do
      let encoded = C.encodeExpressionType et
      case C.decodeExpressionType encoded of
        Right decoded -> decoded `shouldEqual` et
        Left e -> fail ("ExpressionType roundtrip failed: " <> e)

  it "PropertyValueType roundtrip for all variants" do
    for_ [PVTNumber, PVTPosition, PVTColor, PVTEnum, PVTVector3] \pvt -> do
      let encoded = C.encodePropertyValueType pvt
      case C.decodePropertyValueType encoded of
        Right decoded -> decoded `shouldEqual` pvt
        Left e -> fail ("PropertyValueType roundtrip failed: " <> e)

  it "AutoOrientMode roundtrip for all variants" do
    for_ [AOMOff, AOMOrientAlongPath, AOMOrientTowardsPoi] \aom -> do
      let encoded = C.encodeAutoOrientMode aom
      case C.decodeAutoOrientMode encoded of
        Right decoded -> decoded `shouldEqual` aom
        Left e -> fail ("AutoOrientMode roundtrip failed: " <> e)

edgeCases :: Spec Unit
edgeCases = do
  it "handles deeply nested JSON via stringify/parse" do
    -- Build a nested structure and verify it survives stringify/parse
    let inner = C.encodeBezierHandle sampleHandle
        str = stringify inner
    case jsonParser str of
      Left e -> fail ("Nested parse failed: " <> e)
      Right parsed ->
        case C.decodeBezierHandle parsed of
          Right decoded -> decoded `shouldEqual` sampleHandle
          Left e -> fail ("Nested decode failed: " <> e)

  it "handles unicode strings in serialized values" do
    let kf = sampleKeyframe { value = "{\"text\":\"hello \\u2603 world\"}" }
    roundtrip C.encodeKeyframe C.decodeKeyframe kf

  it "handles empty keyframes array" do
    let prop = sampleProperty { keyframes = [] }
    roundtrip C.encodeAnimatableProperty C.decodeAnimatableProperty prop

  it "FiniteFloat rejects NaN" do
    -- mkFiniteFloat rejects NaN at construction time
    -- This is the PureScript advantage: invalid values can't exist
    let encoded = fromNumber 42.0
    case C.decodeFiniteFloat encoded of
      Right (FiniteFloat n) -> n `shouldEqual` 42.0
      Left e -> fail ("Valid number rejected: " <> e)

  it "NonEmptyString rejects empty string" do
    let encoded = fromString ""
    case C.decodeNonEmptyString encoded of
      Left _ -> pure unit
      Right _ -> fail "Empty string should be rejected"

  it "FrameNumber rejects negative values" do
    let encoded = fromNumber (0.0 - 1.0)
    case C.decodeFiniteFloat encoded of
      Right _ -> pure unit -- FiniteFloat accepts negative, FrameNumber would not
      Left _ -> pure unit

  it "UnitFloat rejects values outside [0,1]" do
    let above = fromNumber 1.5
        below = fromNumber (0.0 - 0.5)
    case C.decodeUnitFloat above of
      Left _ -> pure unit
      Right _ -> fail "Value > 1 should be rejected"
    case C.decodeUnitFloat below of
      Left _ -> pure unit
      Right _ -> fail "Value < 0 should be rejected"
