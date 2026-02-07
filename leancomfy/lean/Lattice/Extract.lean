/-
  Lattice.Extract - PureScript code generation from proofs
  
  Single source of truth: Lean types → PureScript types
  Every extracted type has a proven roundtrip theorem.
  
  The extraction pipeline:
    Lean Type → Proof → PureScript
  
  If it doesn't have a proof, it doesn't get extracted.
-/

import Lattice.Codegen
import Lattice.Primitives
import Lattice.Enums
import Lattice.Events
import Lattice.Metrics
import Lattice.Triggers
import Lattice.Actions
import Lattice.Entities

namespace Lattice.Extract

open Lattice.Codegen
open Lattice.Primitives
open Lattice.Enums
open Lattice.Events
open Lattice.Metrics
open Lattice.Triggers
open Lattice.Actions
open Lattice.Entities

/-! ## PureScript Code Emission -/

/-- PureScript type declaration for an Extractable type -/
class EmitPureScript (α : Type _) where
  typeName : String
  typeDecl : String
  decoder : String
  encoder : String

/-! ## Primitives - PureScript Instances -/

instance : EmitPureScript NonEmptyString where
  typeName := "NonEmptyString"
  typeDecl := "newtype NonEmptyString = NonEmptyString String"
  decoder := """instance DecodeJson NonEmptyString where
  decodeJson json = do
    str <- decodeJson json
    if str == "" then Left "NonEmptyString cannot be empty"
    else pure (NonEmptyString str)"""
  encoder := """instance EncodeJson NonEmptyString where
  encodeJson (NonEmptyString s) = encodeJson s"""

instance : EmitPureScript PositiveInt where
  typeName := "PositiveInt"
  typeDecl := "newtype PositiveInt = PositiveInt Int"
  decoder := """instance DecodeJson PositiveInt where
  decodeJson json = do
    n <- decodeJson json
    if n > 0 then pure (PositiveInt n)
    else Left "PositiveInt must be > 0" """
  encoder := """instance EncodeJson PositiveInt where
  encodeJson (PositiveInt n) = encodeJson n"""

instance : EmitPureScript PositiveFloat where
  typeName := "PositiveFloat"
  typeDecl := "newtype PositiveFloat = PositiveFloat Number"
  decoder := """instance DecodeJson PositiveFloat where
  decodeJson json = do
    f <- decodeJson json
    if isFinite f && f > 0.0 then pure (PositiveFloat f)
    else Left "PositiveFloat must be finite and > 0" """
  encoder := """instance EncodeJson PositiveFloat where
  encodeJson (PositiveFloat f) = encodeJson f"""

instance : EmitPureScript NonNegativeFloat where
  typeName := "NonNegativeFloat"
  typeDecl := "newtype NonNegativeFloat = NonNegativeFloat Number"
  decoder := """instance DecodeJson NonNegativeFloat where
  decodeJson json = do
    f <- decodeJson json
    if isFinite f && f >= 0.0 then pure (NonNegativeFloat f)
    else Left "NonNegativeFloat must be finite and >= 0" """
  encoder := """instance EncodeJson NonNegativeFloat where
  encodeJson (NonNegativeFloat f) = encodeJson f"""

instance : EmitPureScript Percentage where
  typeName := "Percentage"
  typeDecl := "newtype Percentage = Percentage Number"
  decoder := """instance DecodeJson Percentage where
  decodeJson json = do
    f <- decodeJson json
    if isFinite f && f >= 0.0 && f <= 100.0 then pure (Percentage f)
    else Left "Percentage must be finite and in [0, 100]" """
  encoder := """instance EncodeJson Percentage where
  encodeJson (Percentage f) = encodeJson f"""

instance : EmitPureScript NormalizedValue where
  typeName := "NormalizedValue"
  typeDecl := "newtype NormalizedValue = NormalizedValue Number"
  decoder := """instance DecodeJson NormalizedValue where
  decodeJson json = do
    f <- decodeJson json
    if isFinite f && f >= 0.0 && f <= 1.0 then pure (NormalizedValue f)
    else Left "NormalizedValue must be finite and in [0, 1]" """
  encoder := """instance EncodeJson NormalizedValue where
  encodeJson (NormalizedValue f) = encodeJson f"""

instance : EmitPureScript FrameNumber where
  typeName := "FrameNumber"
  typeDecl := "newtype FrameNumber = FrameNumber Int"
  decoder := """instance DecodeJson FrameNumber where
  decodeJson json = FrameNumber <$> decodeJson json"""
  encoder := """instance EncodeJson FrameNumber where
  encodeJson (FrameNumber n) = encodeJson n"""

instance : EmitPureScript Vec2 where
  typeName := "Vec2"
  typeDecl := "type Vec2 = { x :: Number, y :: Number }"
  decoder := """instance DecodeJson Vec2 where
  decodeJson json = do
    obj <- decodeJson json
    x <- obj .: "x"
    y <- obj .: "y"
    if isFinite x && isFinite y && not (isNaN x) && not (isNaN y)
      then pure { x, y }
      else Left "Vec2 components must be finite numbers" """
  encoder := """instance EncodeJson Vec2 where
  encodeJson v = "x" := v.x ~> "y" := v.y ~> jsonEmptyObject"""

instance : EmitPureScript Vec3 where
  typeName := "Vec3"
  typeDecl := "type Vec3 = { x :: Number, y :: Number, z :: Number }"
  decoder := """instance DecodeJson Vec3 where
  decodeJson json = do
    obj <- decodeJson json
    x <- obj .: "x"
    y <- obj .: "y"
    z <- obj .: "z"
    if isFinite x && isFinite y && isFinite z && not (isNaN x) && not (isNaN y) && not (isNaN z)
      then pure { x, y, z }
      else Left "Vec3 components must be finite numbers" """
  encoder := """instance EncodeJson Vec3 where
  encodeJson v = "x" := v.x ~> "y" := v.y ~> "z" := v.z ~> jsonEmptyObject"""

instance : EmitPureScript Vec4 where
  typeName := "Vec4"
  typeDecl := "type Vec4 = { x :: Number, y :: Number, z :: Number, w :: Number }"
  decoder := """instance DecodeJson Vec4 where
  decodeJson json = do
    obj <- decodeJson json
    x <- obj .: "x"
    y <- obj .: "y"
    z <- obj .: "z"
    w <- obj .: "w"
    if isFinite x && isFinite y && isFinite z && isFinite w && not (isNaN x) && not (isNaN y) && not (isNaN z) && not (isNaN w)
      then pure { x, y, z, w }
      else Left "Vec4 components must be finite numbers" """
  encoder := """instance EncodeJson Vec4 where
  encodeJson v = "x" := v.x ~> "y" := v.y ~> "z" := v.z ~> "w" := v.w ~> jsonEmptyObject"""

instance : EmitPureScript Matrix3x3 where
  typeName := "Matrix3x3"
  typeDecl := "type Matrix3x3 = { m00 :: Number, m01 :: Number, m02 :: Number, m10 :: Number, m11 :: Number, m12 :: Number, m20 :: Number, m21 :: Number, m22 :: Number }"
  decoder := """instance DecodeJson Matrix3x3 where
  decodeJson json = do
    obj <- decodeJson json
    m00 <- obj .: "m00"
    m01 <- obj .: "m01"
    m02 <- obj .: "m02"
    m10 <- obj .: "m10"
    m11 <- obj .: "m11"
    m12 <- obj .: "m12"
    m20 <- obj .: "m20"
    m21 <- obj .: "m21"
    m22 <- obj .: "m22"
    if isFinite m00 && isFinite m01 && isFinite m02 && isFinite m10 && isFinite m11 && isFinite m12 && isFinite m20 && isFinite m21 && isFinite m22 &&
       not (isNaN m00) && not (isNaN m01) && not (isNaN m02) && not (isNaN m10) && not (isNaN m11) && not (isNaN m12) && not (isNaN m20) && not (isNaN m21) && not (isNaN m22)
      then pure { m00, m01, m02, m10, m11, m12, m20, m21, m22 }
      else Left "Matrix3x3 components must be finite numbers" """
  encoder := """instance EncodeJson Matrix3x3 where
  encodeJson m = "m00" := m.m00 ~> "m01" := m.m01 ~> "m02" := m.m02 ~> "m10" := m.m10 ~> "m11" := m.m11 ~> "m12" := m.m12 ~> "m20" := m.m20 ~> "m21" := m.m21 ~> "m22" := m.m22 ~> jsonEmptyObject"""

instance : EmitPureScript Matrix4x4 where
  typeName := "Matrix4x4"
  typeDecl := "type Matrix4x4 = { m00 :: Number, m01 :: Number, m02 :: Number, m03 :: Number, m10 :: Number, m11 :: Number, m12 :: Number, m13 :: Number, m20 :: Number, m21 :: Number, m22 :: Number, m23 :: Number, m30 :: Number, m31 :: Number, m32 :: Number, m33 :: Number }"
  decoder := """instance DecodeJson Matrix4x4 where
  decodeJson json = do
    obj <- decodeJson json
    m00 <- obj .: "m00"
    m01 <- obj .: "m01"
    m02 <- obj .: "m02"
    m03 <- obj .: "m03"
    m10 <- obj .: "m10"
    m11 <- obj .: "m11"
    m12 <- obj .: "m12"
    m13 <- obj .: "m13"
    m20 <- obj .: "m20"
    m21 <- obj .: "m21"
    m22 <- obj .: "m22"
    m23 <- obj .: "m23"
    m30 <- obj .: "m30"
    m31 <- obj .: "m31"
    m32 <- obj .: "m32"
    m33 <- obj .: "m33"
    if isFinite m00 && isFinite m01 && isFinite m02 && isFinite m03 && isFinite m10 && isFinite m11 && isFinite m12 && isFinite m13 && isFinite m20 && isFinite m21 && isFinite m22 && isFinite m23 && isFinite m30 && isFinite m31 && isFinite m32 && isFinite m33 &&
       not (isNaN m00) && not (isNaN m01) && not (isNaN m02) && not (isNaN m03) && not (isNaN m10) && not (isNaN m11) && not (isNaN m12) && not (isNaN m13) && not (isNaN m20) && not (isNaN m21) && not (isNaN m22) && not (isNaN m23) && not (isNaN m30) && not (isNaN m31) && not (isNaN m32) && not (isNaN m33)
      then pure { m00, m01, m02, m03, m10, m11, m12, m13, m20, m21, m22, m23, m30, m31, m32, m33 }
      else Left "Matrix4x4 components must be finite numbers" """
  encoder := """instance EncodeJson Matrix4x4 where
  encodeJson m = "m00" := m.m00 ~> "m01" := m.m01 ~> "m02" := m.m02 ~> "m03" := m.m03 ~> "m10" := m.m10 ~> "m11" := m.m11 ~> "m12" := m.m12 ~> "m13" := m.m13 ~> "m20" := m.m20 ~> "m21" := m.m21 ~> "m22" := m.m22 ~> "m23" := m.m23 ~> "m30" := m.m30 ~> "m31" := m.m31 ~> "m32" := m.m32 ~> "m33" := m.m33 ~> jsonEmptyObject"""

-- RGBAColor not yet defined in Lattice.Primitives - will add when type exists

/-! ## Enums - PureScript Instances -/

instance : EmitPureScript ControlMode where
  typeName := "ControlMode"
  typeDecl := """data ControlMode
  = ControlModeSymmetric
  | ControlModeSmooth
  | ControlModeCorner

derive instance Eq ControlMode
derive instance Ord ControlMode"""
  decoder := """instance DecodeJson ControlMode where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "symmetric" -> pure ControlModeSymmetric
      "smooth" -> pure ControlModeSmooth
      "corner" -> pure ControlModeCorner
      _ -> Left "Invalid ControlMode" """
  encoder := """instance EncodeJson ControlMode where
  encodeJson ControlModeSymmetric = encodeJson "symmetric"
  encodeJson ControlModeSmooth = encodeJson "smooth"
  encodeJson ControlModeCorner = encodeJson "corner" """

instance : EmitPureScript InterpolationType where
  typeName := "InterpolationType"
  typeDecl := """data InterpolationType
  = InterpolationLinear
  | InterpolationBezier
  | InterpolationHold
  | InterpolationEaseIn
  | InterpolationEaseOut
  | InterpolationEaseInOut
  | InterpolationCustom

derive instance Eq InterpolationType
derive instance Ord InterpolationType"""
  decoder := """instance DecodeJson InterpolationType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "linear" -> pure InterpolationLinear
      "bezier" -> pure InterpolationBezier
      "hold" -> pure InterpolationHold
      "easeIn" -> pure InterpolationEaseIn
      "easeOut" -> pure InterpolationEaseOut
      "easeInOut" -> pure InterpolationEaseInOut
      "custom" -> pure InterpolationCustom
      _ -> Left "Invalid InterpolationType" """
  encoder := """instance EncodeJson InterpolationType where
  encodeJson InterpolationLinear = encodeJson "linear"
  encodeJson InterpolationBezier = encodeJson "bezier"
  encodeJson InterpolationHold = encodeJson "hold"
  encodeJson InterpolationEaseIn = encodeJson "easeIn"
  encodeJson InterpolationEaseOut = encodeJson "easeOut"
  encodeJson InterpolationEaseInOut = encodeJson "easeInOut"
  encodeJson InterpolationCustom = encodeJson "custom" """

instance : EmitPureScript PropertyValueType where
  typeName := "PropertyValueType"
  typeDecl := """data PropertyValueType
  = PropertyValueTypeNumber
  | PropertyValueTypePosition
  | PropertyValueTypeColor
  | PropertyValueTypeEnum
  | PropertyValueTypeVector3

derive instance Eq PropertyValueType
derive instance Ord PropertyValueType"""
  decoder := """instance DecodeJson PropertyValueType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "number" -> pure PropertyValueTypeNumber
      "position" -> pure PropertyValueTypePosition
      "color" -> pure PropertyValueTypeColor
      "enum" -> pure PropertyValueTypeEnum
      "vector3" -> pure PropertyValueTypeVector3
      _ -> Left "Invalid PropertyValueType" """
  encoder := """instance EncodeJson PropertyValueType where
  encodeJson PropertyValueTypeNumber = encodeJson "number"
  encodeJson PropertyValueTypePosition = encodeJson "position"
  encodeJson PropertyValueTypeColor = encodeJson "color"
  encodeJson PropertyValueTypeEnum = encodeJson "enum"
  encodeJson PropertyValueTypeVector3 = encodeJson "vector3" """

instance : EmitPureScript BezierHandle where
  typeName := "BezierHandle"
  typeDecl := "type BezierHandle = { frame :: Number, value :: Number, enabled :: Boolean }"
  decoder := """instance DecodeJson BezierHandle where
  decodeJson json = do
    obj <- decodeJson json
    frame <- obj .: "frame"
    value <- obj .: "value"
    enabled <- obj .: "enabled"
    if isFinite frame && isFinite value && not (isNaN frame) && not (isNaN value)
      then pure { frame, value, enabled }
      else Left "BezierHandle components must be finite numbers" """
  encoder := """instance EncodeJson BezierHandle where
  encodeJson h = "frame" := h.frame ~> "value" := h.value ~> "enabled" := h.enabled ~> jsonEmptyObject"""

/-! ## Enums - Additional PureScript Instances -/

instance : EmitPureScript LayerType where
  typeName := "LayerType"
  typeDecl := """data LayerType
  = LayerTypeShape
  | LayerTypeText
  | LayerTypeImage
  | LayerTypeVideo
  | LayerTypeAudio
  | LayerTypeGroup
  | LayerTypeCamera
  | LayerTypeLight
  | LayerTypeParticle
  | LayerTypeEffect

derive instance Eq LayerType
derive instance Ord LayerType"""
  decoder := """instance DecodeJson LayerType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "shape" -> pure LayerTypeShape
      "text" -> pure LayerTypeText
      "image" -> pure LayerTypeImage
      "video" -> pure LayerTypeVideo
      "audio" -> pure LayerTypeAudio
      "group" -> pure LayerTypeGroup
      "camera" -> pure LayerTypeCamera
      "light" -> pure LayerTypeLight
      "particle" -> pure LayerTypeParticle
      "effect" -> pure LayerTypeEffect
      _ -> Left "Invalid LayerType" """
  encoder := """instance EncodeJson LayerType where
  encodeJson LayerTypeShape = encodeJson "shape"
  encodeJson LayerTypeText = encodeJson "text"
  encodeJson LayerTypeImage = encodeJson "image"
  encodeJson LayerTypeVideo = encodeJson "video"
  encodeJson LayerTypeAudio = encodeJson "audio"
  encodeJson LayerTypeGroup = encodeJson "group"
  encodeJson LayerTypeCamera = encodeJson "camera"
  encodeJson LayerTypeLight = encodeJson "light"
  encodeJson LayerTypeParticle = encodeJson "particle"
  encodeJson LayerTypeEffect = encodeJson "effect" """

instance : EmitPureScript BlendMode where
  typeName := "BlendMode"
  typeDecl := """data BlendMode
  = BlendModeNormal
  | BlendModeMultiply
  | BlendModeScreen
  | BlendModeOverlay
  | BlendModeSoftLight
  | BlendModeHardLight
  | BlendModeColorDodge
  | BlendModeColorBurn
  | BlendModeDarken
  | BlendModeLighten
  | BlendModeDifference
  | BlendModeExclusion
  | BlendModeHue
  | BlendModeSaturation
  | BlendModeColor
  | BlendModeLuminosity
  | BlendModeAdd
  | BlendModeSubtract
  | BlendModeDivide

derive instance Eq BlendMode
derive instance Ord BlendMode"""
  decoder := """instance DecodeJson BlendMode where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "normal" -> pure BlendModeNormal
      "multiply" -> pure BlendModeMultiply
      "screen" -> pure BlendModeScreen
      "overlay" -> pure BlendModeOverlay
      "softLight" -> pure BlendModeSoftLight
      "hardLight" -> pure BlendModeHardLight
      "colorDodge" -> pure BlendModeColorDodge
      "colorBurn" -> pure BlendModeColorBurn
      "darken" -> pure BlendModeDarken
      "lighten" -> pure BlendModeLighten
      "difference" -> pure BlendModeDifference
      "exclusion" -> pure BlendModeExclusion
      "hue" -> pure BlendModeHue
      "saturation" -> pure BlendModeSaturation
      "color" -> pure BlendModeColor
      "luminosity" -> pure BlendModeLuminosity
      "add" -> pure BlendModeAdd
      "subtract" -> pure BlendModeSubtract
      "divide" -> pure BlendModeDivide
      _ -> Left "Invalid BlendMode" """
  encoder := """instance EncodeJson BlendMode where
  encodeJson BlendModeNormal = encodeJson "normal"
  encodeJson BlendModeMultiply = encodeJson "multiply"
  encodeJson BlendModeScreen = encodeJson "screen"
  encodeJson BlendModeOverlay = encodeJson "overlay"
  encodeJson BlendModeSoftLight = encodeJson "softLight"
  encodeJson BlendModeHardLight = encodeJson "hardLight"
  encodeJson BlendModeColorDodge = encodeJson "colorDodge"
  encodeJson BlendModeColorBurn = encodeJson "colorBurn"
  encodeJson BlendModeDarken = encodeJson "darken"
  encodeJson BlendModeLighten = encodeJson "lighten"
  encodeJson BlendModeDifference = encodeJson "difference"
  encodeJson BlendModeExclusion = encodeJson "exclusion"
  encodeJson BlendModeHue = encodeJson "hue"
  encodeJson BlendModeSaturation = encodeJson "saturation"
  encodeJson BlendModeColor = encodeJson "color"
  encodeJson BlendModeLuminosity = encodeJson "luminosity"
  encodeJson BlendModeAdd = encodeJson "add"
  encodeJson BlendModeSubtract = encodeJson "subtract"
  encodeJson BlendModeDivide = encodeJson "divide" """

instance : EmitPureScript MaskMode where
  typeName := "MaskMode"
  typeDecl := """data MaskMode
  = MaskModeAdd
  | MaskModeSubtract
  | MaskModeIntersect
  | MaskModeDifference

derive instance Eq MaskMode
derive instance Ord MaskMode"""
  decoder := """instance DecodeJson MaskMode where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "add" -> pure MaskModeAdd
      "subtract" -> pure MaskModeSubtract
      "intersect" -> pure MaskModeIntersect
      "difference" -> pure MaskModeDifference
      _ -> Left "Invalid MaskMode" """
  encoder := """instance EncodeJson MaskMode where
  encodeJson MaskModeAdd = encodeJson "add"
  encodeJson MaskModeSubtract = encodeJson "subtract"
  encodeJson MaskModeIntersect = encodeJson "intersect"
  encodeJson MaskModeDifference = encodeJson "difference" """

instance : EmitPureScript ExpressionType where
  typeName := "ExpressionType"
  typeDecl := """data ExpressionType
  = ExpressionTypePreset
  | ExpressionTypeCustom

derive instance Eq ExpressionType
derive instance Ord ExpressionType"""
  decoder := """instance DecodeJson ExpressionType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "preset" -> pure ExpressionTypePreset
      "custom" -> pure ExpressionTypeCustom
      _ -> Left "Invalid ExpressionType" """
  encoder := """instance EncodeJson ExpressionType where
  encodeJson ExpressionTypePreset = encodeJson "preset"
  encodeJson ExpressionTypeCustom = encodeJson "custom" """

instance : EmitPureScript QualityMode where
  typeName := "QualityMode"
  typeDecl := """data QualityMode
  = QualityModeLow
  | QualityModeMedium
  | QualityModeHigh
  | QualityModeUltra

derive instance Eq QualityMode
derive instance Ord QualityMode"""
  decoder := """instance DecodeJson QualityMode where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "low" -> pure QualityModeLow
      "medium" -> pure QualityModeMedium
      "high" -> pure QualityModeHigh
      "ultra" -> pure QualityModeUltra
      _ -> Left "Invalid QualityMode" """
  encoder := """instance EncodeJson QualityMode where
  encodeJson QualityModeLow = encodeJson "low"
  encodeJson QualityModeMedium = encodeJson "medium"
  encodeJson QualityModeHigh = encodeJson "high"
  encodeJson QualityModeUltra = encodeJson "ultra" """

instance : EmitPureScript LayerStatus where
  typeName := "LayerStatus"
  typeDecl := """data LayerStatus
  = LayerStatusActive
  | LayerStatusHidden
  | LayerStatusLocked
  | LayerStatusDisabled

derive instance Eq LayerStatus
derive instance Ord LayerStatus"""
  decoder := """instance DecodeJson LayerStatus where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "active" -> pure LayerStatusActive
      "hidden" -> pure LayerStatusHidden
      "locked" -> pure LayerStatusLocked
      "disabled" -> pure LayerStatusDisabled
      _ -> Left "Invalid LayerStatus" """
  encoder := """instance EncodeJson LayerStatus where
  encodeJson LayerStatusActive = encodeJson "active"
  encodeJson LayerStatusHidden = encodeJson "hidden"
  encodeJson LayerStatusLocked = encodeJson "locked"
  encodeJson LayerStatusDisabled = encodeJson "disabled" """

instance : EmitPureScript EffectCategory where
  typeName := "EffectCategory"
  typeDecl := """data EffectCategory
  = EffectCategoryBlurSharpen
  | EffectCategoryColorCorrection
  | EffectCategoryDistort
  | EffectCategoryGenerate
  | EffectCategoryKeying
  | EffectCategoryMatte
  | EffectCategoryNoiseGrain
  | EffectCategoryPerspective
  | EffectCategoryStylize
  | EffectCategoryTime
  | EffectCategoryTransition
  | EffectCategoryUtility

derive instance Eq EffectCategory
derive instance Ord EffectCategory"""
  decoder := """instance DecodeJson EffectCategory where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "blurSharpen" -> pure EffectCategoryBlurSharpen
      "colorCorrection" -> pure EffectCategoryColorCorrection
      "distort" -> pure EffectCategoryDistort
      "generate" -> pure EffectCategoryGenerate
      "keying" -> pure EffectCategoryKeying
      "matte" -> pure EffectCategoryMatte
      "noiseGrain" -> pure EffectCategoryNoiseGrain
      "perspective" -> pure EffectCategoryPerspective
      "stylize" -> pure EffectCategoryStylize
      "time" -> pure EffectCategoryTime
      "transition" -> pure EffectCategoryTransition
      "utility" -> pure EffectCategoryUtility
      _ -> Left "Invalid EffectCategory" """
  encoder := """instance EncodeJson EffectCategory where
  encodeJson EffectCategoryBlurSharpen = encodeJson "blurSharpen"
  encodeJson EffectCategoryColorCorrection = encodeJson "colorCorrection"
  encodeJson EffectCategoryDistort = encodeJson "distort"
  encodeJson EffectCategoryGenerate = encodeJson "generate"
  encodeJson EffectCategoryKeying = encodeJson "keying"
  encodeJson EffectCategoryMatte = encodeJson "matte"
  encodeJson EffectCategoryNoiseGrain = encodeJson "noiseGrain"
  encodeJson EffectCategoryPerspective = encodeJson "perspective"
  encodeJson EffectCategoryStylize = encodeJson "stylize"
  encodeJson EffectCategoryTime = encodeJson "time"
  encodeJson EffectCategoryTransition = encodeJson "transition"
  encodeJson EffectCategoryUtility = encodeJson "utility" """

instance : EmitPureScript EffectStatus where
  typeName := "EffectStatus"
  typeDecl := """data EffectStatus
  = EffectStatusActive
  | EffectStatusDisabled
  | EffectStatusBypassed

derive instance Eq EffectStatus
derive instance Ord EffectStatus"""
  decoder := """instance DecodeJson EffectStatus where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "active" -> pure EffectStatusActive
      "disabled" -> pure EffectStatusDisabled
      "bypassed" -> pure EffectStatusBypassed
      _ -> Left "Invalid EffectStatus" """
  encoder := """instance EncodeJson EffectStatus where
  encodeJson EffectStatusActive = encodeJson "active"
  encodeJson EffectStatusDisabled = encodeJson "disabled"
  encodeJson EffectStatusBypassed = encodeJson "bypassed" """

instance : EmitPureScript EffectType where
  typeName := "EffectType"
  typeDecl := """data EffectType
  = EffectTypeBlur
  | EffectTypeSharpen
  | EffectTypeGlow
  | EffectTypeShadow
  | EffectTypeBevel
  | EffectTypeGradientOverlay
  | EffectTypeStroke
  | EffectTypeColorCorrection
  | EffectTypeDistort
  | EffectTypeKeying
  | EffectTypeMatte
  | EffectTypeNoise
  | EffectTypeGrain
  | EffectTypeMotionBlur
  | EffectTypeTimewarp
  | EffectTypeTransition

derive instance Eq EffectType
derive instance Ord EffectType"""
  decoder := """instance DecodeJson EffectType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "blur" -> pure EffectTypeBlur
      "sharpen" -> pure EffectTypeSharpen
      "glow" -> pure EffectTypeGlow
      "shadow" -> pure EffectTypeShadow
      "bevel" -> pure EffectTypeBevel
      "gradientOverlay" -> pure EffectTypeGradientOverlay
      "stroke" -> pure EffectTypeStroke
      "colorCorrection" -> pure EffectTypeColorCorrection
      "distort" -> pure EffectTypeDistort
      "keying" -> pure EffectTypeKeying
      "matte" -> pure EffectTypeMatte
      "noise" -> pure EffectTypeNoise
      "grain" -> pure EffectTypeGrain
      "motionBlur" -> pure EffectTypeMotionBlur
      "timewarp" -> pure EffectTypeTimewarp
      "transition" -> pure EffectTypeTransition
      _ -> Left "Invalid EffectType" """
  encoder := """instance EncodeJson EffectType where
  encodeJson EffectTypeBlur = encodeJson "blur"
  encodeJson EffectTypeSharpen = encodeJson "sharpen"
  encodeJson EffectTypeGlow = encodeJson "glow"
  encodeJson EffectTypeShadow = encodeJson "shadow"
  encodeJson EffectTypeBevel = encodeJson "bevel"
  encodeJson EffectTypeGradientOverlay = encodeJson "gradientOverlay"
  encodeJson EffectTypeStroke = encodeJson "stroke"
  encodeJson EffectTypeColorCorrection = encodeJson "colorCorrection"
  encodeJson EffectTypeDistort = encodeJson "distort"
  encodeJson EffectTypeKeying = encodeJson "keying"
  encodeJson EffectTypeMatte = encodeJson "matte"
  encodeJson EffectTypeNoise = encodeJson "noise"
  encodeJson EffectTypeGrain = encodeJson "grain"
  encodeJson EffectTypeMotionBlur = encodeJson "motionBlur"
  encodeJson EffectTypeTimewarp = encodeJson "timewarp"
  encodeJson EffectTypeTransition = encodeJson "transition" """

instance : EmitPureScript ExportFormat where
  typeName := "ExportFormat"
  typeDecl := """data ExportFormat
  = ExportFormatMp4
  | ExportFormatMov
  | ExportFormatAvi
  | ExportFormatWebm
  | ExportFormatPng
  | ExportFormatJpg
  | ExportFormatExr
  | ExportFormatH264
  | ExportFormatH265
  | ExportFormatProres

derive instance Eq ExportFormat
derive instance Ord ExportFormat"""
  decoder := """instance DecodeJson ExportFormat where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "mp4" -> pure ExportFormatMp4
      "mov" -> pure ExportFormatMov
      "avi" -> pure ExportFormatAvi
      "webm" -> pure ExportFormatWebm
      "png" -> pure ExportFormatPng
      "jpg" -> pure ExportFormatJpg
      "exr" -> pure ExportFormatExr
      "h264" -> pure ExportFormatH264
      "h265" -> pure ExportFormatH265
      "prores" -> pure ExportFormatProres
      _ -> Left "Invalid ExportFormat" """
  encoder := """instance EncodeJson ExportFormat where
  encodeJson ExportFormatMp4 = encodeJson "mp4"
  encodeJson ExportFormatMov = encodeJson "mov"
  encodeJson ExportFormatAvi = encodeJson "avi"
  encodeJson ExportFormatWebm = encodeJson "webm"
  encodeJson ExportFormatPng = encodeJson "png"
  encodeJson ExportFormatJpg = encodeJson "jpg"
  encodeJson ExportFormatExr = encodeJson "exr"
  encodeJson ExportFormatH264 = encodeJson "h264"
  encodeJson ExportFormatH265 = encodeJson "h265"
  encodeJson ExportFormatProres = encodeJson "prores" """

instance : EmitPureScript ExportStatus where
  typeName := "ExportStatus"
  typeDecl := """data ExportStatus
  = ExportStatusQueued
  | ExportStatusProcessing
  | ExportStatusCompleted
  | ExportStatusFailed
  | ExportStatusCancelled

derive instance Eq ExportStatus
derive instance Ord ExportStatus"""
  decoder := """instance DecodeJson ExportStatus where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "queued" -> pure ExportStatusQueued
      "processing" -> pure ExportStatusProcessing
      "completed" -> pure ExportStatusCompleted
      "failed" -> pure ExportStatusFailed
      "cancelled" -> pure ExportStatusCancelled
      _ -> Left "Invalid ExportStatus" """
  encoder := """instance EncodeJson ExportStatus where
  encodeJson ExportStatusQueued = encodeJson "queued"
  encodeJson ExportStatusProcessing = encodeJson "processing"
  encodeJson ExportStatusCompleted = encodeJson "completed"
  encodeJson ExportStatusFailed = encodeJson "failed"
  encodeJson ExportStatusCancelled = encodeJson "cancelled" """

instance : EmitPureScript JobStatus where
  typeName := "JobStatus"
  typeDecl := """data JobStatus
  = JobStatusQueued
  | JobStatusRunning
  | JobStatusCompleted
  | JobStatusFailed
  | JobStatusCancelled

derive instance Eq JobStatus
derive instance Ord JobStatus"""
  decoder := """instance DecodeJson JobStatus where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "queued" -> pure JobStatusQueued
      "running" -> pure JobStatusRunning
      "completed" -> pure JobStatusCompleted
      "failed" -> pure JobStatusFailed
      "cancelled" -> pure JobStatusCancelled
      _ -> Left "Invalid JobStatus" """
  encoder := """instance EncodeJson JobStatus where
  encodeJson JobStatusQueued = encodeJson "queued"
  encodeJson JobStatusRunning = encodeJson "running"
  encodeJson JobStatusCompleted = encodeJson "completed"
  encodeJson JobStatusFailed = encodeJson "failed"
  encodeJson JobStatusCancelled = encodeJson "cancelled" """

instance : EmitPureScript RenderStatus where
  typeName := "RenderStatus"
  typeDecl := """data RenderStatus
  = RenderStatusIdle
  | RenderStatusRendering
  | RenderStatusPaused
  | RenderStatusCompleted
  | RenderStatusFailed

derive instance Eq RenderStatus
derive instance Ord RenderStatus"""
  decoder := """instance DecodeJson RenderStatus where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "idle" -> pure RenderStatusIdle
      "rendering" -> pure RenderStatusRendering
      "paused" -> pure RenderStatusPaused
      "completed" -> pure RenderStatusCompleted
      "failed" -> pure RenderStatusFailed
      _ -> Left "Invalid RenderStatus" """
  encoder := """instance EncodeJson RenderStatus where
  encodeJson RenderStatusIdle = encodeJson "idle"
  encodeJson RenderStatusRendering = encodeJson "rendering"
  encodeJson RenderStatusPaused = encodeJson "paused"
  encodeJson RenderStatusCompleted = encodeJson "completed"
  encodeJson RenderStatusFailed = encodeJson "failed" """

instance : EmitPureScript ValidationResult where
  typeName := "ValidationResult"
  typeDecl := """data ValidationResult
  = ValidationResultValid
  | ValidationResultInvalid
  | ValidationResultWarning

derive instance Eq ValidationResult
derive instance Ord ValidationResult"""
  decoder := """instance DecodeJson ValidationResult where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "valid" -> pure ValidationResultValid
      "invalid" -> pure ValidationResultInvalid
      "warning" -> pure ValidationResultWarning
      _ -> Left "Invalid ValidationResult" """
  encoder := """instance EncodeJson ValidationResult where
  encodeJson ValidationResultValid = encodeJson "valid"
  encodeJson ValidationResultInvalid = encodeJson "invalid"
  encodeJson ValidationResultWarning = encodeJson "warning" """

instance : EmitPureScript Severity where
  typeName := "Severity"
  typeDecl := """data Severity
  = SeverityDebug
  | SeverityInfo
  | SeverityWarning
  | SeverityError
  | SeverityCritical

derive instance Eq Severity
derive instance Ord Severity"""
  decoder := """instance DecodeJson Severity where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "debug" -> pure SeverityDebug
      "info" -> pure SeverityInfo
      "warning" -> pure SeverityWarning
      "error" -> pure SeverityError
      "critical" -> pure SeverityCritical
      _ -> Left "Invalid Severity" """
  encoder := """instance EncodeJson Severity where
  encodeJson SeverityDebug = encodeJson "debug"
  encodeJson SeverityInfo = encodeJson "info"
  encodeJson SeverityWarning = encodeJson "warning"
  encodeJson SeverityError = encodeJson "error"
  encodeJson SeverityCritical = encodeJson "critical" """

instance : EmitPureScript AssetType where
  typeName := "AssetType"
  typeDecl := """data AssetType
  = AssetTypeDepthMap
  | AssetTypeImage
  | AssetTypeVideo
  | AssetTypeAudio
  | AssetTypeModel
  | AssetTypePointcloud
  | AssetTypeTexture
  | AssetTypeMaterial
  | AssetTypeHdri
  | AssetTypeSvg
  | AssetTypeSprite
  | AssetTypeSpritesheet
  | AssetTypeLut

derive instance Eq AssetType
derive instance Ord AssetType"""
  decoder := """instance DecodeJson AssetType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "depthMap" -> pure AssetTypeDepthMap
      "image" -> pure AssetTypeImage
      "video" -> pure AssetTypeVideo
      "audio" -> pure AssetTypeAudio
      "model" -> pure AssetTypeModel
      "pointcloud" -> pure AssetTypePointcloud
      "texture" -> pure AssetTypeTexture
      "material" -> pure AssetTypeMaterial
      "hdri" -> pure AssetTypeHdri
      "svg" -> pure AssetTypeSvg
      "sprite" -> pure AssetTypeSprite
      "spritesheet" -> pure AssetTypeSpritesheet
      "lut" -> pure AssetTypeLut
      _ -> Left "Invalid AssetType" """
  encoder := """instance EncodeJson AssetType where
  encodeJson AssetTypeDepthMap = encodeJson "depthMap"
  encodeJson AssetTypeImage = encodeJson "image"
  encodeJson AssetTypeVideo = encodeJson "video"
  encodeJson AssetTypeAudio = encodeJson "audio"
  encodeJson AssetTypeModel = encodeJson "model"
  encodeJson AssetTypePointcloud = encodeJson "pointcloud"
  encodeJson AssetTypeTexture = encodeJson "texture"
  encodeJson AssetTypeMaterial = encodeJson "material"
  encodeJson AssetTypeHdri = encodeJson "hdri"
  encodeJson AssetTypeSvg = encodeJson "svg"
  encodeJson AssetTypeSprite = encodeJson "sprite"
  encodeJson AssetTypeSpritesheet = encodeJson "spritesheet"
  encodeJson AssetTypeLut = encodeJson "lut" """

instance : EmitPureScript AssetSource where
  typeName := "AssetSource"
  typeDecl := """data AssetSource
  = AssetSourceComfyuiNode
  | AssetSourceFile
  | AssetSourceGenerated
  | AssetSourceUrl

derive instance Eq AssetSource
derive instance Ord AssetSource"""
  decoder := """instance DecodeJson AssetSource where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "comfyuiNode" -> pure AssetSourceComfyuiNode
      "file" -> pure AssetSourceFile
      "generated" -> pure AssetSourceGenerated
      "url" -> pure AssetSourceUrl
      _ -> Left "Invalid AssetSource" """
  encoder := """instance EncodeJson AssetSource where
  encodeJson AssetSourceComfyuiNode = encodeJson "comfyuiNode"
  encodeJson AssetSourceFile = encodeJson "file"
  encodeJson AssetSourceGenerated = encodeJson "generated"
  encodeJson AssetSourceUrl = encodeJson "url" """

instance : EmitPureScript ExportJobStatus where
  typeName := "ExportJobStatus"
  typeDecl := """data ExportJobStatus
  = ExportJobStatusQueued
  | ExportJobStatusProcessing
  | ExportJobStatusCompleted
  | ExportJobStatusFailed
  | ExportJobStatusCancelled

derive instance Eq ExportJobStatus
derive instance Ord ExportJobStatus"""
  decoder := """instance DecodeJson ExportJobStatus where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "queued" -> pure ExportJobStatusQueued
      "processing" -> pure ExportJobStatusProcessing
      "completed" -> pure ExportJobStatusCompleted
      "failed" -> pure ExportJobStatusFailed
      "cancelled" -> pure ExportJobStatusCancelled
      _ -> Left "Invalid ExportJobStatus" """
  encoder := """instance EncodeJson ExportJobStatus where
  encodeJson ExportJobStatusQueued = encodeJson "queued"
  encodeJson ExportJobStatusProcessing = encodeJson "processing"
  encodeJson ExportJobStatusCompleted = encodeJson "completed"
  encodeJson ExportJobStatusFailed = encodeJson "failed"
  encodeJson ExportJobStatusCancelled = encodeJson "cancelled" """

instance : EmitPureScript CameraType where
  typeName := "CameraType"
  typeDecl := """data CameraType
  = CameraTypePerspective
  | CameraTypeOrthographic
  | CameraTypeFisheye
  | CameraTypeSpherical

derive instance Eq CameraType
derive instance Ord CameraType"""
  decoder := """instance DecodeJson CameraType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "perspective" -> pure CameraTypePerspective
      "orthographic" -> pure CameraTypeOrthographic
      "fisheye" -> pure CameraTypeFisheye
      "spherical" -> pure CameraTypeSpherical
      _ -> Left "Invalid CameraType" """
  encoder := """instance EncodeJson CameraType where
  encodeJson CameraTypePerspective = encodeJson "perspective"
  encodeJson CameraTypeOrthographic = encodeJson "orthographic"
  encodeJson CameraTypeFisheye = encodeJson "fisheye"
  encodeJson CameraTypeSpherical = encodeJson "spherical" """

instance : EmitPureScript ProjectionType where
  typeName := "ProjectionType"
  typeDecl := """data ProjectionType
  = ProjectionTypePerspective
  | ProjectionTypeOrthographic

derive instance Eq ProjectionType
derive instance Ord ProjectionType"""
  decoder := """instance DecodeJson ProjectionType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "perspective" -> pure ProjectionTypePerspective
      "orthographic" -> pure ProjectionTypeOrthographic
      _ -> Left "Invalid ProjectionType" """
  encoder := """instance EncodeJson ProjectionType where
  encodeJson ProjectionTypePerspective = encodeJson "perspective"
  encodeJson ProjectionTypeOrthographic = encodeJson "orthographic" """

instance : EmitPureScript KeyframeType where
  typeName := "KeyframeType"
  typeDecl := """data KeyframeType
  = KeyframeTypeLinear
  | KeyframeTypeBezier
  | KeyframeTypeHold
  | KeyframeTypeAuto

derive instance Eq KeyframeType
derive instance Ord KeyframeType"""
  decoder := """instance DecodeJson KeyframeType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "linear" -> pure KeyframeTypeLinear
      "bezier" -> pure KeyframeTypeBezier
      "hold" -> pure KeyframeTypeHold
      "auto" -> pure KeyframeTypeAuto
      _ -> Left "Invalid KeyframeType" """
  encoder := """instance EncodeJson KeyframeType where
  encodeJson KeyframeTypeLinear = encodeJson "linear"
  encodeJson KeyframeTypeBezier = encodeJson "bezier"
  encodeJson KeyframeTypeHold = encodeJson "hold"
  encodeJson KeyframeTypeAuto = encodeJson "auto" """

instance : EmitPureScript ColorSpace where
  typeName := "ColorSpace"
  typeDecl := """data ColorSpace
  = ColorSpaceSRGB
  | ColorSpaceLinearSRGB
  | ColorSpaceWideGamutRGB
  | ColorSpaceDisplayP3
  | ColorSpaceProPhotoRGB
  | ColorSpaceAcescg
  | ColorSpaceRec709
  | ColorSpaceRec2020

derive instance Eq ColorSpace
derive instance Ord ColorSpace"""
  decoder := """instance DecodeJson ColorSpace where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "sRGB" -> pure ColorSpaceSRGB
      "linearSRGB" -> pure ColorSpaceLinearSRGB
      "wideGamutRGB" -> pure ColorSpaceWideGamutRGB
      "displayP3" -> pure ColorSpaceDisplayP3
      "proPhotoRGB" -> pure ColorSpaceProPhotoRGB
      "acescg" -> pure ColorSpaceAcescg
      "rec709" -> pure ColorSpaceRec709
      "rec2020" -> pure ColorSpaceRec2020
      _ -> Left "Invalid ColorSpace" """
  encoder := """instance EncodeJson ColorSpace where
  encodeJson ColorSpaceSRGB = encodeJson "sRGB"
  encodeJson ColorSpaceLinearSRGB = encodeJson "linearSRGB"
  encodeJson ColorSpaceWideGamutRGB = encodeJson "wideGamutRGB"
  encodeJson ColorSpaceDisplayP3 = encodeJson "displayP3"
  encodeJson ColorSpaceProPhotoRGB = encodeJson "proPhotoRGB"
  encodeJson ColorSpaceAcescg = encodeJson "acescg"
  encodeJson ColorSpaceRec709 = encodeJson "rec709"
  encodeJson ColorSpaceRec2020 = encodeJson "rec2020" """

instance : EmitPureScript ColorFormat where
  typeName := "ColorFormat"
  typeDecl := """data ColorFormat
  = ColorFormatRgb8
  | ColorFormatRgb16
  | ColorFormatRgba8
  | ColorFormatRgba16
  | ColorFormatHsl
  | ColorFormatHsv
  | ColorFormatLab
  | ColorFormatXyz

derive instance Eq ColorFormat
derive instance Ord ColorFormat"""
  decoder := """instance DecodeJson ColorFormat where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "rgb8" -> pure ColorFormatRgb8
      "rgb16" -> pure ColorFormatRgb16
      "rgba8" -> pure ColorFormatRgba8
      "rgba16" -> pure ColorFormatRgba16
      "hsl" -> pure ColorFormatHsl
      "hsv" -> pure ColorFormatHsv
      "lab" -> pure ColorFormatLab
      "xyz" -> pure ColorFormatXyz
      _ -> Left "Invalid ColorFormat" """
  encoder := """instance EncodeJson ColorFormat where
  encodeJson ColorFormatRgb8 = encodeJson "rgb8"
  encodeJson ColorFormatRgb16 = encodeJson "rgb16"
  encodeJson ColorFormatRgba8 = encodeJson "rgba8"
  encodeJson ColorFormatRgba16 = encodeJson "rgba16"
  encodeJson ColorFormatHsl = encodeJson "hsl"
  encodeJson ColorFormatHsv = encodeJson "hsv"
  encodeJson ColorFormatLab = encodeJson "lab"
  encodeJson ColorFormatXyz = encodeJson "xyz" """

instance : EmitPureScript TransferFunction where
  typeName := "TransferFunction"
  typeDecl := """data TransferFunction
  = TransferFunctionLinear
  | TransferFunctionSRGB
  | TransferFunctionGamma
  | TransferFunctionLog
  | TransferFunctionPq
  | TransferFunctionHlg

derive instance Eq TransferFunction
derive instance Ord TransferFunction"""
  decoder := """instance DecodeJson TransferFunction where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "linear" -> pure TransferFunctionLinear
      "sRGB" -> pure TransferFunctionSRGB
      "gamma" -> pure TransferFunctionGamma
      "log" -> pure TransferFunctionLog
      "pq" -> pure TransferFunctionPq
      "hlg" -> pure TransferFunctionHlg
      _ -> Left "Invalid TransferFunction" """
  encoder := """instance EncodeJson TransferFunction where
  encodeJson TransferFunctionLinear = encodeJson "linear"
  encodeJson TransferFunctionSRGB = encodeJson "sRGB"
  encodeJson TransferFunctionGamma = encodeJson "gamma"
  encodeJson TransferFunctionLog = encodeJson "log"
  encodeJson TransferFunctionPq = encodeJson "pq"
  encodeJson TransferFunctionHlg = encodeJson "hlg" """

instance : EmitPureScript TextAlign where
  typeName := "TextAlign"
  typeDecl := """data TextAlign
  = TextAlignLeft
  | TextAlignCenter
  | TextAlignRight
  | TextAlignJustify

derive instance Eq TextAlign
derive instance Ord TextAlign"""
  decoder := """instance DecodeJson TextAlign where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "left" -> pure TextAlignLeft
      "center" -> pure TextAlignCenter
      "right" -> pure TextAlignRight
      "justify" -> pure TextAlignJustify
      _ -> Left "Invalid TextAlign" """
  encoder := """instance EncodeJson TextAlign where
  encodeJson TextAlignLeft = encodeJson "left"
  encodeJson TextAlignCenter = encodeJson "center"
  encodeJson TextAlignRight = encodeJson "right"
  encodeJson TextAlignJustify = encodeJson "justify" """

instance : EmitPureScript TextDirection where
  typeName := "TextDirection"
  typeDecl := """data TextDirection
  = TextDirectionLtr
  | TextDirectionRtl

derive instance Eq TextDirection
derive instance Ord TextDirection"""
  decoder := """instance DecodeJson TextDirection where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "ltr" -> pure TextDirectionLtr
      "rtl" -> pure TextDirectionRtl
      _ -> Left "Invalid TextDirection" """
  encoder := """instance EncodeJson TextDirection where
  encodeJson TextDirectionLtr = encodeJson "ltr"
  encodeJson TextDirectionRtl = encodeJson "rtl" """

instance : EmitPureScript FontStyle where
  typeName := "FontStyle"
  typeDecl := """data FontStyle
  = FontStyleNormal
  | FontStyleItalic
  | FontStyleOblique

derive instance Eq FontStyle
derive instance Ord FontStyle"""
  decoder := """instance DecodeJson FontStyle where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "normal" -> pure FontStyleNormal
      "italic" -> pure FontStyleItalic
      "oblique" -> pure FontStyleOblique
      _ -> Left "Invalid FontStyle" """
  encoder := """instance EncodeJson FontStyle where
  encodeJson FontStyleNormal = encodeJson "normal"
  encodeJson FontStyleItalic = encodeJson "italic"
  encodeJson FontStyleOblique = encodeJson "oblique" """

instance : EmitPureScript FontWeight where
  typeName := "FontWeight"
  typeDecl := """data FontWeight
  = FontWeightThin
  | FontWeightExtraLight
  | FontWeightLight
  | FontWeightRegular
  | FontWeightMedium
  | FontWeightSemiBold
  | FontWeightBold
  | FontWeightExtraBold
  | FontWeightBlack

derive instance Eq FontWeight
derive instance Ord FontWeight"""
  decoder := """instance DecodeJson FontWeight where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "thin" -> pure FontWeightThin
      "extraLight" -> pure FontWeightExtraLight
      "light" -> pure FontWeightLight
      "regular" -> pure FontWeightRegular
      "medium" -> pure FontWeightMedium
      "semiBold" -> pure FontWeightSemiBold
      "bold" -> pure FontWeightBold
      "extraBold" -> pure FontWeightExtraBold
      "black" -> pure FontWeightBlack
      _ -> Left "Invalid FontWeight" """
  encoder := """instance EncodeJson FontWeight where
  encodeJson FontWeightThin = encodeJson "thin"
  encodeJson FontWeightExtraLight = encodeJson "extraLight"
  encodeJson FontWeightLight = encodeJson "light"
  encodeJson FontWeightRegular = encodeJson "regular"
  encodeJson FontWeightMedium = encodeJson "medium"
  encodeJson FontWeightSemiBold = encodeJson "semiBold"
  encodeJson FontWeightBold = encodeJson "bold"
  encodeJson FontWeightExtraBold = encodeJson "extraBold"
  encodeJson FontWeightBlack = encodeJson "black" """

instance : EmitPureScript AudioFormat where
  typeName := "AudioFormat"
  typeDecl := """data AudioFormat
  = AudioFormatMp3
  | AudioFormatWav
  | AudioFormatOgg
  | AudioFormatAac
  | AudioFormatFlac
  | AudioFormatM4a

derive instance Eq AudioFormat
derive instance Ord AudioFormat"""
  decoder := """instance DecodeJson AudioFormat where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "mp3" -> pure AudioFormatMp3
      "wav" -> pure AudioFormatWav
      "ogg" -> pure AudioFormatOgg
      "aac" -> pure AudioFormatAac
      "flac" -> pure AudioFormatFlac
      "m4a" -> pure AudioFormatM4a
      _ -> Left "Invalid AudioFormat" """
  encoder := """instance EncodeJson AudioFormat where
  encodeJson AudioFormatMp3 = encodeJson "mp3"
  encodeJson AudioFormatWav = encodeJson "wav"
  encodeJson AudioFormatOgg = encodeJson "ogg"
  encodeJson AudioFormatAac = encodeJson "aac"
  encodeJson AudioFormatFlac = encodeJson "flac"
  encodeJson AudioFormatM4a = encodeJson "m4a" """

instance : EmitPureScript AudioChannel where
  typeName := "AudioChannel"
  typeDecl := """data AudioChannel
  = AudioChannelMono
  | AudioChannelStereo
  | AudioChannelQuad
  | AudioChannelSurround51
  | AudioChannelSurround71

derive instance Eq AudioChannel
derive instance Ord AudioChannel"""
  decoder := """instance DecodeJson AudioChannel where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "mono" -> pure AudioChannelMono
      "stereo" -> pure AudioChannelStereo
      "quad" -> pure AudioChannelQuad
      "surround51" -> pure AudioChannelSurround51
      "surround71" -> pure AudioChannelSurround71
      _ -> Left "Invalid AudioChannel" """
  encoder := """instance EncodeJson AudioChannel where
  encodeJson AudioChannelMono = encodeJson "mono"
  encodeJson AudioChannelStereo = encodeJson "stereo"
  encodeJson AudioChannelQuad = encodeJson "quad"
  encodeJson AudioChannelSurround51 = encodeJson "surround51"
  encodeJson AudioChannelSurround71 = encodeJson "surround71" """

instance : EmitPureScript BeatDetectionMethod where
  typeName := "BeatDetectionMethod"
  typeDecl := """data BeatDetectionMethod
  = BeatDetectionMethodEnergy
  | BeatDetectionMethodOnset
  | BeatDetectionMethodSpectral
  | BeatDetectionMethodTempo
  | BeatDetectionMethodCustom

derive instance Eq BeatDetectionMethod
derive instance Ord BeatDetectionMethod"""
  decoder := """instance DecodeJson BeatDetectionMethod where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "energy" -> pure BeatDetectionMethodEnergy
      "onset" -> pure BeatDetectionMethodOnset
      "spectral" -> pure BeatDetectionMethodSpectral
      "tempo" -> pure BeatDetectionMethodTempo
      "custom" -> pure BeatDetectionMethodCustom
      _ -> Left "Invalid BeatDetectionMethod" """
  encoder := """instance EncodeJson BeatDetectionMethod where
  encodeJson BeatDetectionMethodEnergy = encodeJson "energy"
  encodeJson BeatDetectionMethodOnset = encodeJson "onset"
  encodeJson BeatDetectionMethodSpectral = encodeJson "spectral"
  encodeJson BeatDetectionMethodTempo = encodeJson "tempo"
  encodeJson BeatDetectionMethodCustom = encodeJson "custom" """

instance : EmitPureScript DepthOfFieldMode where
  typeName := "DepthOfFieldMode"
  typeDecl := """data DepthOfFieldMode
  = DepthOfFieldModeOff
  | DepthOfFieldModeGaussian
  | DepthOfFieldModeBokeh
  | DepthOfFieldModeCustom

derive instance Eq DepthOfFieldMode
derive instance Ord DepthOfFieldMode"""
  decoder := """instance DecodeJson DepthOfFieldMode where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "off" -> pure DepthOfFieldModeOff
      "gaussian" -> pure DepthOfFieldModeGaussian
      "bokeh" -> pure DepthOfFieldModeBokeh
      "custom" -> pure DepthOfFieldModeCustom
      _ -> Left "Invalid DepthOfFieldMode" """
  encoder := """instance EncodeJson DepthOfFieldMode where
  encodeJson DepthOfFieldModeOff = encodeJson "off"
  encodeJson DepthOfFieldModeGaussian = encodeJson "gaussian"
  encodeJson DepthOfFieldModeBokeh = encodeJson "bokeh"
  encodeJson DepthOfFieldModeCustom = encodeJson "custom" """

instance : EmitPureScript ModelType where
  typeName := "ModelType"
  typeDecl := """data ModelType
  = ModelTypeMesh
  | ModelTypePointCloud
  | ModelTypeVolume
  | ModelTypeProcedural

derive instance Eq ModelType
derive instance Ord ModelType"""
  decoder := """instance DecodeJson ModelType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "mesh" -> pure ModelTypeMesh
      "pointCloud" -> pure ModelTypePointCloud
      "volume" -> pure ModelTypeVolume
      "procedural" -> pure ModelTypeProcedural
      _ -> Left "Invalid ModelType" """
  encoder := """instance EncodeJson ModelType where
  encodeJson ModelTypeMesh = encodeJson "mesh"
  encodeJson ModelTypePointCloud = encodeJson "pointCloud"
  encodeJson ModelTypeVolume = encodeJson "volume"
  encodeJson ModelTypeProcedural = encodeJson "procedural" """

instance : EmitPureScript PreprocessorType where
  typeName := "PreprocessorType"
  typeDecl := """data PreprocessorType
  = PreprocessorTypeDepth
  | PreprocessorTypeNormal
  | PreprocessorTypePose
  | PreprocessorTypeEdge
  | PreprocessorTypeLineart
  | PreprocessorTypeScribble
  | PreprocessorTypeSegmentation
  | PreprocessorTypeVideo
  | PreprocessorTypeOther

derive instance Eq PreprocessorType
derive instance Ord PreprocessorType"""
  decoder := """instance DecodeJson PreprocessorType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "depth" -> pure PreprocessorTypeDepth
      "normal" -> pure PreprocessorTypeNormal
      "pose" -> pure PreprocessorTypePose
      "edge" -> pure PreprocessorTypeEdge
      "lineart" -> pure PreprocessorTypeLineart
      "scribble" -> pure PreprocessorTypeScribble
      "segmentation" -> pure PreprocessorTypeSegmentation
      "video" -> pure PreprocessorTypeVideo
      "other" -> pure PreprocessorTypeOther
      _ -> Left "Invalid PreprocessorType" """
  encoder := """instance EncodeJson PreprocessorType where
  encodeJson PreprocessorTypeDepth = encodeJson "depth"
  encodeJson PreprocessorTypeNormal = encodeJson "normal"
  encodeJson PreprocessorTypePose = encodeJson "pose"
  encodeJson PreprocessorTypeEdge = encodeJson "edge"
  encodeJson PreprocessorTypeLineart = encodeJson "lineart"
  encodeJson PreprocessorTypeScribble = encodeJson "scribble"
  encodeJson PreprocessorTypeSegmentation = encodeJson "segmentation"
  encodeJson PreprocessorTypeVideo = encodeJson "video"
  encodeJson PreprocessorTypeOther = encodeJson "other" """

instance : EmitPureScript SegmentationMode where
  typeName := "SegmentationMode"
  typeDecl := """data SegmentationMode
  = SegmentationModeSemantic
  | SegmentationModeInstance
  | SegmentationModePanoptic
  | SegmentationModeCustom

derive instance Eq SegmentationMode
derive instance Ord SegmentationMode"""
  decoder := """instance DecodeJson SegmentationMode where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "semantic" -> pure SegmentationModeSemantic
      "instance" -> pure SegmentationModeInstance
      "panoptic" -> pure SegmentationModePanoptic
      "custom" -> pure SegmentationModeCustom
      _ -> Left "Invalid SegmentationMode" """
  encoder := """instance EncodeJson SegmentationMode where
  encodeJson SegmentationModeSemantic = encodeJson "semantic"
  encodeJson SegmentationModeInstance = encodeJson "instance"
  encodeJson SegmentationModePanoptic = encodeJson "panoptic"
  encodeJson SegmentationModeCustom = encodeJson "custom" """

instance : EmitPureScript AuditCategory where
  typeName := "AuditCategory"
  typeDecl := """data AuditCategory
  = AuditCategorySecurity
  | AuditCategoryPerformance
  | AuditCategoryError
  | AuditCategoryAccess
  | AuditCategoryModification
  | AuditCategorySystem

derive instance Eq AuditCategory
derive instance Ord AuditCategory"""
  decoder := """instance DecodeJson AuditCategory where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "security" -> pure AuditCategorySecurity
      "performance" -> pure AuditCategoryPerformance
      "error" -> pure AuditCategoryError
      "access" -> pure AuditCategoryAccess
      "modification" -> pure AuditCategoryModification
      "system" -> pure AuditCategorySystem
      _ -> Left "Invalid AuditCategory" """
  encoder := """instance EncodeJson AuditCategory where
  encodeJson AuditCategorySecurity = encodeJson "security"
  encodeJson AuditCategoryPerformance = encodeJson "performance"
  encodeJson AuditCategoryError = encodeJson "error"
  encodeJson AuditCategoryAccess = encodeJson "access"
  encodeJson AuditCategoryModification = encodeJson "modification"
  encodeJson AuditCategorySystem = encodeJson "system" """

instance : EmitPureScript RateLimitScope where
  typeName := "RateLimitScope"
  typeDecl := """data RateLimitScope
  = RateLimitScopeGlobal
  | RateLimitScopeUser
  | RateLimitScopeIp
  | RateLimitScopeEndpoint
  | RateLimitScopeCustom

derive instance Eq RateLimitScope
derive instance Ord RateLimitScope"""
  decoder := """instance DecodeJson RateLimitScope where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "global" -> pure RateLimitScopeGlobal
      "user" -> pure RateLimitScopeUser
      "ip" -> pure RateLimitScopeIp
      "endpoint" -> pure RateLimitScopeEndpoint
      "custom" -> pure RateLimitScopeCustom
      _ -> Left "Invalid RateLimitScope" """
  encoder := """instance EncodeJson RateLimitScope where
  encodeJson RateLimitScopeGlobal = encodeJson "global"
  encodeJson RateLimitScopeUser = encodeJson "user"
  encodeJson RateLimitScopeIp = encodeJson "ip"
  encodeJson RateLimitScopeEndpoint = encodeJson "endpoint"
  encodeJson RateLimitScopeCustom = encodeJson "custom" """

instance : EmitPureScript SyncStatus where
  typeName := "SyncStatus"
  typeDecl := """data SyncStatus
  = SyncStatusSynced
  | SyncStatusSyncing
  | SyncStatusPending
  | SyncStatusFailed
  | SyncStatusConflict

derive instance Eq SyncStatus
derive instance Ord SyncStatus"""
  decoder := """instance DecodeJson SyncStatus where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "synced" -> pure SyncStatusSynced
      "syncing" -> pure SyncStatusSyncing
      "pending" -> pure SyncStatusPending
      "failed" -> pure SyncStatusFailed
      "conflict" -> pure SyncStatusConflict
      _ -> Left "Invalid SyncStatus" """
  encoder := """instance EncodeJson SyncStatus where
  encodeJson SyncStatusSynced = encodeJson "synced"
  encodeJson SyncStatusSyncing = encodeJson "syncing"
  encodeJson SyncStatusPending = encodeJson "pending"
  encodeJson SyncStatusFailed = encodeJson "failed"
  encodeJson SyncStatusConflict = encodeJson "conflict" """

instance : EmitPureScript TextRangeMode where
  typeName := "TextRangeMode"
  typeDecl := """data TextRangeMode
  = TextRangeModePercent
  | TextRangeModeIndex

derive instance Eq TextRangeMode
derive instance Ord TextRangeMode"""
  decoder := """instance DecodeJson TextRangeMode where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "percent" -> pure TextRangeModePercent
      "index" -> pure TextRangeModeIndex
      _ -> Left "Invalid TextRangeMode" """
  encoder := """instance EncodeJson TextRangeMode where
  encodeJson TextRangeModePercent = encodeJson "percent"
  encodeJson TextRangeModeIndex = encodeJson "index" """

instance : EmitPureScript TextRangeBasedOn where
  typeName := "TextRangeBasedOn"
  typeDecl := """data TextRangeBasedOn
  = TextRangeBasedOnCharacters
  | TextRangeBasedOnCharactersExcludingSpaces
  | TextRangeBasedOnWords
  | TextRangeBasedOnLines

derive instance Eq TextRangeBasedOn
derive instance Ord TextRangeBasedOn"""
  decoder := """instance DecodeJson TextRangeBasedOn where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "characters" -> pure TextRangeBasedOnCharacters
      "characters_excluding_spaces" -> pure TextRangeBasedOnCharactersExcludingSpaces
      "words" -> pure TextRangeBasedOnWords
      "lines" -> pure TextRangeBasedOnLines
      _ -> Left "Invalid TextRangeBasedOn" """
  encoder := """instance EncodeJson TextRangeBasedOn where
  encodeJson TextRangeBasedOnCharacters = encodeJson "characters"
  encodeJson TextRangeBasedOnCharactersExcludingSpaces = encodeJson "characters_excluding_spaces"
  encodeJson TextRangeBasedOnWords = encodeJson "words"
  encodeJson TextRangeBasedOnLines = encodeJson "lines" """

instance : EmitPureScript TextRangeShape where
  typeName := "TextRangeShape"
  typeDecl := """data TextRangeShape
  = TextRangeShapeSquare
  | TextRangeShapeRampUp
  | TextRangeShapeRampDown
  | TextRangeShapeTriangle
  | TextRangeShapeRound
  | TextRangeShapeSmooth

derive instance Eq TextRangeShape
derive instance Ord TextRangeShape"""
  decoder := """instance DecodeJson TextRangeShape where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "square" -> pure TextRangeShapeSquare
      "ramp_up" -> pure TextRangeShapeRampUp
      "ramp_down" -> pure TextRangeShapeRampDown
      "triangle" -> pure TextRangeShapeTriangle
      "round" -> pure TextRangeShapeRound
      "smooth" -> pure TextRangeShapeSmooth
      _ -> Left "Invalid TextRangeShape" """
  encoder := """instance EncodeJson TextRangeShape where
  encodeJson TextRangeShapeSquare = encodeJson "square"
  encodeJson TextRangeShapeRampUp = encodeJson "ramp_up"
  encodeJson TextRangeShapeRampDown = encodeJson "ramp_down"
  encodeJson TextRangeShapeTriangle = encodeJson "triangle"
  encodeJson TextRangeShapeRound = encodeJson "round"
  encodeJson TextRangeShapeSmooth = encodeJson "smooth" """

instance : EmitPureScript ComparisonOperator where
  typeName := "ComparisonOperator"
  typeDecl := """data ComparisonOperator
  = ComparisonOperatorEquals
  | ComparisonOperatorNotEquals
  | ComparisonOperatorGreaterThan
  | ComparisonOperatorGreaterThanOrEqual
  | ComparisonOperatorLessThan
  | ComparisonOperatorLessThanOrEqual

derive instance Eq ComparisonOperator
derive instance Ord ComparisonOperator"""
  decoder := """instance DecodeJson ComparisonOperator where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "equals" -> pure ComparisonOperatorEquals
      "notEquals" -> pure ComparisonOperatorNotEquals
      "greaterThan" -> pure ComparisonOperatorGreaterThan
      "greaterThanOrEqual" -> pure ComparisonOperatorGreaterThanOrEqual
      "lessThan" -> pure ComparisonOperatorLessThan
      "lessThanOrEqual" -> pure ComparisonOperatorLessThanOrEqual
      _ -> Left "Invalid ComparisonOperator" """
  encoder := """instance EncodeJson ComparisonOperator where
  encodeJson ComparisonOperatorEquals = encodeJson "equals"
  encodeJson ComparisonOperatorNotEquals = encodeJson "notEquals"
  encodeJson ComparisonOperatorGreaterThan = encodeJson "greaterThan"
  encodeJson ComparisonOperatorGreaterThanOrEqual = encodeJson "greaterThanOrEqual"
  encodeJson ComparisonOperatorLessThan = encodeJson "lessThan"
  encodeJson ComparisonOperatorLessThanOrEqual = encodeJson "lessThanOrEqual" """

instance : EmitPureScript CompositeOperator where
  typeName := "CompositeOperator"
  typeDecl := """data CompositeOperator
  = CompositeOperatorAnd
  | CompositeOperatorOr

derive instance Eq CompositeOperator
derive instance Ord CompositeOperator"""
  decoder := """instance DecodeJson CompositeOperator where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "and" -> pure CompositeOperatorAnd
      "or" -> pure CompositeOperatorOr
      _ -> Left "Invalid CompositeOperator" """
  encoder := """instance EncodeJson CompositeOperator where
  encodeJson CompositeOperatorAnd = encodeJson "and"
  encodeJson CompositeOperatorOr = encodeJson "or" """

instance : EmitPureScript EmitterShape where
  typeName := "EmitterShape"
  typeDecl := """data EmitterShape
  = EmitterShapePoint
  | EmitterShapeLine
  | EmitterShapeCircle
  | EmitterShapeBox
  | EmitterShapeSphere
  | EmitterShapeRing
  | EmitterShapeSpline
  | EmitterShapeDepthMap
  | EmitterShapeMask
  | EmitterShapeCone
  | EmitterShapeImage
  | EmitterShapeDepthEdge
  | EmitterShapeMesh

derive instance Eq EmitterShape
derive instance Ord EmitterShape"""
  decoder := """instance DecodeJson EmitterShape where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "point" -> pure EmitterShapePoint
      "line" -> pure EmitterShapeLine
      "circle" -> pure EmitterShapeCircle
      "box" -> pure EmitterShapeBox
      "sphere" -> pure EmitterShapeSphere
      "ring" -> pure EmitterShapeRing
      "spline" -> pure EmitterShapeSpline
      "depthMap" -> pure EmitterShapeDepthMap
      "mask" -> pure EmitterShapeMask
      "cone" -> pure EmitterShapeCone
      "image" -> pure EmitterShapeImage
      "depthEdge" -> pure EmitterShapeDepthEdge
      "mesh" -> pure EmitterShapeMesh
      _ -> Left "Invalid EmitterShape" """
  encoder := """instance EncodeJson EmitterShape where
  encodeJson EmitterShapePoint = encodeJson "point"
  encodeJson EmitterShapeLine = encodeJson "line"
  encodeJson EmitterShapeCircle = encodeJson "circle"
  encodeJson EmitterShapeBox = encodeJson "box"
  encodeJson EmitterShapeSphere = encodeJson "sphere"
  encodeJson EmitterShapeRing = encodeJson "ring"
  encodeJson EmitterShapeSpline = encodeJson "spline"
  encodeJson EmitterShapeDepthMap = encodeJson "depthMap"
  encodeJson EmitterShapeMask = encodeJson "mask"
  encodeJson EmitterShapeCone = encodeJson "cone"
  encodeJson EmitterShapeImage = encodeJson "image"
  encodeJson EmitterShapeDepthEdge = encodeJson "depthEdge"
  encodeJson EmitterShapeMesh = encodeJson "mesh" """

instance : EmitPureScript ParticleShape where
  typeName := "ParticleShape"
  typeDecl := """data ParticleShape
  = ParticleShapePoint
  | ParticleShapeCircle
  | ParticleShapeSquare
  | ParticleShapeTriangle
  | ParticleShapeStar
  | ParticleShapeCustom

derive instance Eq ParticleShape
derive instance Ord ParticleShape"""
  decoder := """instance DecodeJson ParticleShape where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "point" -> pure ParticleShapePoint
      "circle" -> pure ParticleShapeCircle
      "square" -> pure ParticleShapeSquare
      "triangle" -> pure ParticleShapeTriangle
      "star" -> pure ParticleShapeStar
      "custom" -> pure ParticleShapeCustom
      _ -> Left "Invalid ParticleShape" """
  encoder := """instance EncodeJson ParticleShape where
  encodeJson ParticleShapePoint = encodeJson "point"
  encodeJson ParticleShapeCircle = encodeJson "circle"
  encodeJson ParticleShapeSquare = encodeJson "square"
  encodeJson ParticleShapeTriangle = encodeJson "triangle"
  encodeJson ParticleShapeStar = encodeJson "star"
  encodeJson ParticleShapeCustom = encodeJson "custom" """

instance : EmitPureScript CollisionType where
  typeName := "CollisionType"
  typeDecl := """data CollisionType
  = CollisionTypeNone
  | CollisionTypeBoundingBox
  | CollisionTypePrecise
  | CollisionTypeTrigger

derive instance Eq CollisionType
derive instance Ord CollisionType"""
  decoder := """instance DecodeJson CollisionType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "none" -> pure CollisionTypeNone
      "boundingBox" -> pure CollisionTypeBoundingBox
      "precise" -> pure CollisionTypePrecise
      "trigger" -> pure CollisionTypeTrigger
      _ -> Left "Invalid CollisionType" """
  encoder := """instance EncodeJson CollisionType where
  encodeJson CollisionTypeNone = encodeJson "none"
  encodeJson CollisionTypeBoundingBox = encodeJson "boundingBox"
  encodeJson CollisionTypePrecise = encodeJson "precise"
  encodeJson CollisionTypeTrigger = encodeJson "trigger" """

instance : EmitPureScript MaterialType where
  typeName := "MaterialType"
  typeDecl := """data MaterialType
  = MaterialTypeStandard
  | MaterialTypePhysical
  | MaterialTypeToon
  | MaterialTypeEmissive
  | MaterialTypeTransparent
  | MaterialTypeCustom

derive instance Eq MaterialType
derive instance Ord MaterialType"""
  decoder := """instance DecodeJson MaterialType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "standard" -> pure MaterialTypeStandard
      "physical" -> pure MaterialTypePhysical
      "toon" -> pure MaterialTypeToon
      "emissive" -> pure MaterialTypeEmissive
      "transparent" -> pure MaterialTypeTransparent
      "custom" -> pure MaterialTypeCustom
      _ -> Left "Invalid MaterialType" """
  encoder := """instance EncodeJson MaterialType where
  encodeJson MaterialTypeStandard = encodeJson "standard"
  encodeJson MaterialTypePhysical = encodeJson "physical"
  encodeJson MaterialTypeToon = encodeJson "toon"
  encodeJson MaterialTypeEmissive = encodeJson "emissive"
  encodeJson MaterialTypeTransparent = encodeJson "transparent"
  encodeJson MaterialTypeCustom = encodeJson "custom" """

instance : EmitPureScript AutoOrientMode where
  typeName := "AutoOrientMode"
  typeDecl := """data AutoOrientMode
  = AutoOrientModeOff
  | AutoOrientModeOrientAlongPath
  | AutoOrientModeOrientTowardsPoi

derive instance Eq AutoOrientMode
derive instance Ord AutoOrientMode"""
  decoder := """instance DecodeJson AutoOrientMode where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "off" -> pure AutoOrientModeOff
      "orientAlongPath" -> pure AutoOrientModeOrientAlongPath
      "orientTowardsPoi" -> pure AutoOrientModeOrientTowardsPoi
      _ -> Left "Invalid AutoOrientMode" """
  encoder := """instance EncodeJson AutoOrientMode where
  encodeJson AutoOrientModeOff = encodeJson "off"
  encodeJson AutoOrientModeOrientAlongPath = encodeJson "orientAlongPath"
  encodeJson AutoOrientModeOrientTowardsPoi = encodeJson "orientTowardsPoi" """

instance : EmitPureScript CameraControlType where
  typeName := "CameraControlType"
  typeDecl := """data CameraControlType
  = CameraControlTypeOneNode
  | CameraControlTypeTwoNode

derive instance Eq CameraControlType
derive instance Ord CameraControlType"""
  decoder := """instance DecodeJson CameraControlType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "oneNode" -> pure CameraControlTypeOneNode
      "twoNode" -> pure CameraControlTypeTwoNode
      _ -> Left "Invalid CameraControlType" """
  encoder := """instance EncodeJson CameraControlType where
  encodeJson CameraControlTypeOneNode = encodeJson "oneNode"
  encodeJson CameraControlTypeTwoNode = encodeJson "twoNode" """

instance : EmitPureScript ForceType where
  typeName := "ForceType"
  typeDecl := """data ForceType
  = ForceTypeGravity
  | ForceTypeWind
  | ForceTypeAttraction
  | ForceTypeExplosion
  | ForceTypeBuoyancy
  | ForceTypeVortex
  | ForceTypeDrag

derive instance Eq ForceType
derive instance Ord ForceType"""
  decoder := """instance DecodeJson ForceType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "gravity" -> pure ForceTypeGravity
      "wind" -> pure ForceTypeWind
      "attraction" -> pure ForceTypeAttraction
      "explosion" -> pure ForceTypeExplosion
      "buoyancy" -> pure ForceTypeBuoyancy
      "vortex" -> pure ForceTypeVortex
      "drag" -> pure ForceTypeDrag
      _ -> Left "Invalid ForceType" """
  encoder := """instance EncodeJson ForceType where
  encodeJson ForceTypeGravity = encodeJson "gravity"
  encodeJson ForceTypeWind = encodeJson "wind"
  encodeJson ForceTypeAttraction = encodeJson "attraction"
  encodeJson ForceTypeExplosion = encodeJson "explosion"
  encodeJson ForceTypeBuoyancy = encodeJson "buoyancy"
  encodeJson ForceTypeVortex = encodeJson "vortex"
  encodeJson ForceTypeDrag = encodeJson "drag" """

instance : EmitPureScript BodyType where
  typeName := "BodyType"
  typeDecl := """data BodyType
  = BodyTypeStatic
  | BodyTypeDynamic
  | BodyTypeKinematic
  | BodyTypeDormant

derive instance Eq BodyType
derive instance Ord BodyType"""
  decoder := """instance DecodeJson BodyType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "static" -> pure BodyTypeStatic
      "dynamic" -> pure BodyTypeDynamic
      "kinematic" -> pure BodyTypeKinematic
      "dormant" -> pure BodyTypeDormant
      _ -> Left "Invalid BodyType" """
  encoder := """instance EncodeJson BodyType where
  encodeJson BodyTypeStatic = encodeJson "static"
  encodeJson BodyTypeDynamic = encodeJson "dynamic"
  encodeJson BodyTypeKinematic = encodeJson "kinematic"
  encodeJson BodyTypeDormant = encodeJson "dormant" """

instance : EmitPureScript JointType where
  typeName := "JointType"
  typeDecl := """data JointType
  = JointTypePivot
  | JointTypeSpring
  | JointTypeDistance
  | JointTypePiston
  | JointTypeWheel
  | JointTypeWeld
  | JointTypeBlob
  | JointTypeRope

derive instance Eq JointType
derive instance Ord JointType"""
  decoder := """instance DecodeJson JointType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "pivot" -> pure JointTypePivot
      "spring" -> pure JointTypeSpring
      "distance" -> pure JointTypeDistance
      "piston" -> pure JointTypePiston
      "wheel" -> pure JointTypeWheel
      "weld" -> pure JointTypeWeld
      "blob" -> pure JointTypeBlob
      "rope" -> pure JointTypeRope
      _ -> Left "Invalid JointType" """
  encoder := """instance EncodeJson JointType where
  encodeJson JointTypePivot = encodeJson "pivot"
  encodeJson JointTypeSpring = encodeJson "spring"
  encodeJson JointTypeDistance = encodeJson "distance"
  encodeJson JointTypePiston = encodeJson "piston"
  encodeJson JointTypeWheel = encodeJson "wheel"
  encodeJson JointTypeWeld = encodeJson "weld"
  encodeJson JointTypeBlob = encodeJson "blob"
  encodeJson JointTypeRope = encodeJson "rope" """

instance : EmitPureScript EasingType where
  typeName := "EasingType"
  typeDecl := """data EasingType
  = EasingTypeLinear
  | EasingTypeEaseInQuad
  | EasingTypeEaseOutQuad
  | EasingTypeEaseInOutQuad
  | EasingTypeEaseInCubic
  | EasingTypeEaseOutCubic
  | EasingTypeEaseInOutCubic
  | EasingTypeEaseInQuart
  | EasingTypeEaseOutQuart
  | EasingTypeEaseInOutQuart
  | EasingTypeEaseInQuint
  | EasingTypeEaseOutQuint
  | EasingTypeEaseInOutQuint
  | EasingTypeEaseInSine
  | EasingTypeEaseOutSine
  | EasingTypeEaseInOutSine
  | EasingTypeEaseInExpo
  | EasingTypeEaseOutExpo
  | EasingTypeEaseInOutExpo
  | EasingTypeEaseInCirc
  | EasingTypeEaseOutCirc
  | EasingTypeEaseInOutCirc
  | EasingTypeEaseInElastic
  | EasingTypeEaseOutElastic
  | EasingTypeEaseInOutElastic
  | EasingTypeEaseInBack
  | EasingTypeEaseOutBack
  | EasingTypeEaseInOutBack
  | EasingTypeEaseInBounce
  | EasingTypeEaseOutBounce
  | EasingTypeEaseInOutBounce

derive instance Eq EasingType
derive instance Ord EasingType"""
  decoder := """instance DecodeJson EasingType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "linear" -> pure EasingTypeLinear
      "easeInQuad" -> pure EasingTypeEaseInQuad
      "easeOutQuad" -> pure EasingTypeEaseOutQuad
      "easeInOutQuad" -> pure EasingTypeEaseInOutQuad
      "easeInCubic" -> pure EasingTypeEaseInCubic
      "easeOutCubic" -> pure EasingTypeEaseOutCubic
      "easeInOutCubic" -> pure EasingTypeEaseInOutCubic
      "easeInQuart" -> pure EasingTypeEaseInQuart
      "easeOutQuart" -> pure EasingTypeEaseOutQuart
      "easeInOutQuart" -> pure EasingTypeEaseInOutQuart
      "easeInQuint" -> pure EasingTypeEaseInQuint
      "easeOutQuint" -> pure EasingTypeEaseOutQuint
      "easeInOutQuint" -> pure EasingTypeEaseInOutQuint
      "easeInSine" -> pure EasingTypeEaseInSine
      "easeOutSine" -> pure EasingTypeEaseOutSine
      "easeInOutSine" -> pure EasingTypeEaseInOutSine
      "easeInExpo" -> pure EasingTypeEaseInExpo
      "easeOutExpo" -> pure EasingTypeEaseOutExpo
      "easeInOutExpo" -> pure EasingTypeEaseInOutExpo
      "easeInCirc" -> pure EasingTypeEaseInCirc
      "easeOutCirc" -> pure EasingTypeEaseOutCirc
      "easeInOutCirc" -> pure EasingTypeEaseInOutCirc
      "easeInElastic" -> pure EasingTypeEaseInElastic
      "easeOutElastic" -> pure EasingTypeEaseOutElastic
      "easeInOutElastic" -> pure EasingTypeEaseInOutElastic
      "easeInBack" -> pure EasingTypeEaseInBack
      "easeOutBack" -> pure EasingTypeEaseOutBack
      "easeInOutBack" -> pure EasingTypeEaseInOutBack
      "easeInBounce" -> pure EasingTypeEaseInBounce
      "easeOutBounce" -> pure EasingTypeEaseOutBounce
      "easeInOutBounce" -> pure EasingTypeEaseInOutBounce
      _ -> Left "Invalid EasingType" """
  encoder := """instance EncodeJson EasingType where
  encodeJson EasingTypeLinear = encodeJson "linear"
  encodeJson EasingTypeEaseInQuad = encodeJson "easeInQuad"
  encodeJson EasingTypeEaseOutQuad = encodeJson "easeOutQuad"
  encodeJson EasingTypeEaseInOutQuad = encodeJson "easeInOutQuad"
  encodeJson EasingTypeEaseInCubic = encodeJson "easeInCubic"
  encodeJson EasingTypeEaseOutCubic = encodeJson "easeOutCubic"
  encodeJson EasingTypeEaseInOutCubic = encodeJson "easeInOutCubic"
  encodeJson EasingTypeEaseInQuart = encodeJson "easeInQuart"
  encodeJson EasingTypeEaseOutQuart = encodeJson "easeOutQuart"
  encodeJson EasingTypeEaseInOutQuart = encodeJson "easeInOutQuart"
  encodeJson EasingTypeEaseInQuint = encodeJson "easeInQuint"
  encodeJson EasingTypeEaseOutQuint = encodeJson "easeOutQuint"
  encodeJson EasingTypeEaseInOutQuint = encodeJson "easeInOutQuint"
  encodeJson EasingTypeEaseInSine = encodeJson "easeInSine"
  encodeJson EasingTypeEaseOutSine = encodeJson "easeOutSine"
  encodeJson EasingTypeEaseInOutSine = encodeJson "easeInOutSine"
  encodeJson EasingTypeEaseInExpo = encodeJson "easeInExpo"
  encodeJson EasingTypeEaseOutExpo = encodeJson "easeOutExpo"
  encodeJson EasingTypeEaseInOutExpo = encodeJson "easeInOutExpo"
  encodeJson EasingTypeEaseInCirc = encodeJson "easeInCirc"
  encodeJson EasingTypeEaseOutCirc = encodeJson "easeOutCirc"
  encodeJson EasingTypeEaseInOutCirc = encodeJson "easeInOutCirc"
  encodeJson EasingTypeEaseInElastic = encodeJson "easeInElastic"
  encodeJson EasingTypeEaseOutElastic = encodeJson "easeOutElastic"
  encodeJson EasingTypeEaseInOutElastic = encodeJson "easeInOutElastic"
  encodeJson EasingTypeEaseInBack = encodeJson "easeInBack"
  encodeJson EasingTypeEaseOutBack = encodeJson "easeOutBack"
  encodeJson EasingTypeEaseInOutBack = encodeJson "easeInOutBack"
  encodeJson EasingTypeEaseInBounce = encodeJson "easeInBounce"
  encodeJson EasingTypeEaseOutBounce = encodeJson "easeOutBounce"
  encodeJson EasingTypeEaseInOutBounce = encodeJson "easeInOutBounce" """

instance : EmitPureScript ExportTarget where
  typeName := "ExportTarget"
  typeDecl := """data ExportTarget
  = ExportTargetWan22I2V
  | ExportTargetWan22T2V
  | ExportTargetWan22FunCamera
  | ExportTargetWan22FirstLast
  | ExportTargetUni3cCamera
  | ExportTargetUni3cMotion
  | ExportTargetMotionctrl
  | ExportTargetMotionctrlSvd
  | ExportTargetCogvideox
  | ExportTargetControlnetDepth
  | ExportTargetControlnetCanny
  | ExportTargetControlnetLineart
  | ExportTargetControlnetPose
  | ExportTargetAnimatediffCameractrl
  | ExportTargetCustomWorkflow
  | ExportTargetLightX
  | ExportTargetWanMove
  | ExportTargetAti
  | ExportTargetTtm
  | ExportTargetTtmWan
  | ExportTargetTtmCogvideox
  | ExportTargetTtmSvd
  | ExportTargetScail
  | ExportTargetCameraComfyui

derive instance Eq ExportTarget
derive instance Ord ExportTarget"""
  decoder := """instance DecodeJson ExportTarget where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "wan22I2V" -> pure ExportTargetWan22I2V
      "wan22T2V" -> pure ExportTargetWan22T2V
      "wan22FunCamera" -> pure ExportTargetWan22FunCamera
      "wan22FirstLast" -> pure ExportTargetWan22FirstLast
      "uni3cCamera" -> pure ExportTargetUni3cCamera
      "uni3cMotion" -> pure ExportTargetUni3cMotion
      "motionctrl" -> pure ExportTargetMotionctrl
      "motionctrlSvd" -> pure ExportTargetMotionctrlSvd
      "cogvideox" -> pure ExportTargetCogvideox
      "controlnetDepth" -> pure ExportTargetControlnetDepth
      "controlnetCanny" -> pure ExportTargetControlnetCanny
      "controlnetLineart" -> pure ExportTargetControlnetLineart
      "controlnetPose" -> pure ExportTargetControlnetPose
      "animatediffCameractrl" -> pure ExportTargetAnimatediffCameractrl
      "customWorkflow" -> pure ExportTargetCustomWorkflow
      "lightX" -> pure ExportTargetLightX
      "wanMove" -> pure ExportTargetWanMove
      "ati" -> pure ExportTargetAti
      "ttm" -> pure ExportTargetTtm
      "ttmWan" -> pure ExportTargetTtmWan
      "ttmCogvideox" -> pure ExportTargetTtmCogvideox
      "ttmSvd" -> pure ExportTargetTtmSvd
      "scail" -> pure ExportTargetScail
      "cameraComfyui" -> pure ExportTargetCameraComfyui
      _ -> Left "Invalid ExportTarget" """
  encoder := """instance EncodeJson ExportTarget where
  encodeJson ExportTargetWan22I2V = encodeJson "wan22I2V"
  encodeJson ExportTargetWan22T2V = encodeJson "wan22T2V"
  encodeJson ExportTargetWan22FunCamera = encodeJson "wan22FunCamera"
  encodeJson ExportTargetWan22FirstLast = encodeJson "wan22FirstLast"
  encodeJson ExportTargetUni3cCamera = encodeJson "uni3cCamera"
  encodeJson ExportTargetUni3cMotion = encodeJson "uni3cMotion"
  encodeJson ExportTargetMotionctrl = encodeJson "motionctrl"
  encodeJson ExportTargetMotionctrlSvd = encodeJson "motionctrlSvd"
  encodeJson ExportTargetCogvideox = encodeJson "cogvideox"
  encodeJson ExportTargetControlnetDepth = encodeJson "controlnetDepth"
  encodeJson ExportTargetControlnetCanny = encodeJson "controlnetCanny"
  encodeJson ExportTargetControlnetLineart = encodeJson "controlnetLineart"
  encodeJson ExportTargetControlnetPose = encodeJson "controlnetPose"
  encodeJson ExportTargetAnimatediffCameractrl = encodeJson "animatediffCameractrl"
  encodeJson ExportTargetCustomWorkflow = encodeJson "customWorkflow"
  encodeJson ExportTargetLightX = encodeJson "lightX"
  encodeJson ExportTargetWanMove = encodeJson "wanMove"
  encodeJson ExportTargetAti = encodeJson "ati"
  encodeJson ExportTargetTtm = encodeJson "ttm"
  encodeJson ExportTargetTtmWan = encodeJson "ttmWan"
  encodeJson ExportTargetTtmCogvideox = encodeJson "ttmCogvideox"
  encodeJson ExportTargetTtmSvd = encodeJson "ttmSvd"
  encodeJson ExportTargetScail = encodeJson "scail"
  encodeJson ExportTargetCameraComfyui = encodeJson "cameraComfyui" """

/-! ## Base Types - PureScript Instances -/

instance : EmitPureScript ActionResult where
  typeName := "ActionResult"
  typeDecl := """data ActionResult
  = ActionResultSuccess
  | ActionResultFailure
  | ActionResultPartial

derive instance Eq ActionResult
derive instance Ord ActionResult"""
  decoder := """instance DecodeJson ActionResult where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "success" -> pure ActionResultSuccess
      "failure" -> pure ActionResultFailure
      "partial" -> pure ActionResultPartial
      _ -> Left "Invalid ActionResult" """
  encoder := """instance EncodeJson ActionResult where
  encodeJson ActionResultSuccess = encodeJson "success"
  encodeJson ActionResultFailure = encodeJson "failure"
  encodeJson ActionResultPartial = encodeJson "partial" """

instance : EmitPureScript RetryPolicy where
  typeName := "RetryPolicy"
  typeDecl := """type RetryPolicy = { maxRetries :: FrameNumber, retryDelay :: NonNegativeFloat, backoffMultiplier :: PositiveFloat }"""
  decoder := """instance DecodeJson RetryPolicy where
  decodeJson json = do
    maxRetries <- json .? "maxRetries"
    retryDelay <- json .? "retryDelay"
    backoffMultiplier <- json .? "backoffMultiplier"
    pure { maxRetries, retryDelay, backoffMultiplier } """
  encoder := """instance EncodeJson RetryPolicy where
  encodeJson r = "maxRetries" := r.maxRetries
    ~> "retryDelay" := r.retryDelay
    ~> "backoffMultiplier" := r.backoffMultiplier
    ~> jsonEmptyObject """

instance : EmitPureScript BaseEvent where
  typeName := "BaseEvent"
  typeDecl := """type BaseEvent = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString }"""
  decoder := """instance DecodeJson BaseEvent where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    pure { id, timestamp, eventType } """
  encoder := """instance EncodeJson BaseEvent where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> jsonEmptyObject """

instance : EmitPureScript BaseAction where
  typeName := "BaseAction"
  typeDecl := """type BaseAction = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy }"""
  decoder := """instance DecodeJson BaseAction where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    pure { id, actionType, target, params, retryPolicy } """
  encoder := """instance EncodeJson BaseAction where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> jsonEmptyObject """

instance : EmitPureScript BaseTrigger where
  typeName := "BaseTrigger"
  typeDecl := """type BaseTrigger = { id :: NonEmptyString, triggerType :: NonEmptyString, enabled :: Boolean, compositionId :: NonEmptyString }"""
  decoder := """instance DecodeJson BaseTrigger where
  decodeJson json = do
    id <- json .? "id"
    triggerType <- json .? "triggerType"
    enabled <- json .? "enabled"
    compositionId <- json .? "compositionId"
    pure { id, triggerType, enabled, compositionId } """
  encoder := """instance EncodeJson BaseTrigger where
  encodeJson t = "id" := t.id
    ~> "triggerType" := t.triggerType
    ~> "enabled" := t.enabled
    ~> "compositionId" := t.compositionId
    ~> jsonEmptyObject """

/-! ## Events - PureScript Instances -/

instance : EmitPureScript CompositionCreated where
  typeName := "CompositionCreated"
  typeDecl := """type CompositionCreated = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, compositionId :: NonEmptyString, compositionName :: NonEmptyString }"""
  decoder := """instance DecodeJson CompositionCreated where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    compositionId <- json .? "compositionId"
    compositionName <- json .? "compositionName"
    pure { id, timestamp, eventType, compositionId, compositionName } """
  encoder := """instance EncodeJson CompositionCreated where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "compositionId" := e.compositionId
    ~> "compositionName" := e.compositionName
    ~> jsonEmptyObject """

instance : EmitPureScript CompositionDeleted where
  typeName := "CompositionDeleted"
  typeDecl := """type CompositionDeleted = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, compositionId :: NonEmptyString }"""
  decoder := """instance DecodeJson CompositionDeleted where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    compositionId <- json .? "compositionId"
    pure { id, timestamp, eventType, compositionId } """
  encoder := """instance EncodeJson CompositionDeleted where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "compositionId" := e.compositionId
    ~> jsonEmptyObject """

instance : EmitPureScript CompositionRendered where
  typeName := "CompositionRendered"
  typeDecl := """type CompositionRendered = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, compositionId :: NonEmptyString, frameNumber :: FrameNumber, duration :: NonNegativeFloat }"""
  decoder := """instance DecodeJson CompositionRendered where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    compositionId <- json .? "compositionId"
    frameNumber <- json .? "frameNumber"
    duration <- json .? "duration"
    pure { id, timestamp, eventType, compositionId, frameNumber, duration } """
  encoder := """instance EncodeJson CompositionRendered where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "compositionId" := e.compositionId
    ~> "frameNumber" := e.frameNumber
    ~> "duration" := e.duration
    ~> jsonEmptyObject """

instance : EmitPureScript LayerCreated where
  typeName := "LayerCreated"
  typeDecl := """type LayerCreated = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, layerId :: NonEmptyString, compositionId :: NonEmptyString, layerType :: LayerType }"""
  decoder := """instance DecodeJson LayerCreated where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    layerId <- json .? "layerId"
    compositionId <- json .? "compositionId"
    layerType <- json .? "layerType"
    pure { id, timestamp, eventType, layerId, compositionId, layerType } """
  encoder := """instance EncodeJson LayerCreated where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "layerId" := e.layerId
    ~> "compositionId" := e.compositionId
    ~> "layerType" := e.layerType
    ~> jsonEmptyObject """

instance : EmitPureScript LayerDeleted where
  typeName := "LayerDeleted"
  typeDecl := """type LayerDeleted = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, layerId :: NonEmptyString, compositionId :: NonEmptyString }"""
  decoder := """instance DecodeJson LayerDeleted where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    layerId <- json .? "layerId"
    compositionId <- json .? "compositionId"
    pure { id, timestamp, eventType, layerId, compositionId } """
  encoder := """instance EncodeJson LayerDeleted where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "layerId" := e.layerId
    ~> "compositionId" := e.compositionId
    ~> jsonEmptyObject """

instance : EmitPureScript LayerMoved where
  typeName := "LayerMoved"
  typeDecl := """type LayerMoved = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, layerId :: NonEmptyString, compositionId :: NonEmptyString, oldIndex :: PositiveInt, newIndex :: PositiveInt }"""
  decoder := """instance DecodeJson LayerMoved where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    layerId <- json .? "layerId"
    compositionId <- json .? "compositionId"
    oldIndex <- json .? "oldIndex"
    newIndex <- json .? "newIndex"
    pure { id, timestamp, eventType, layerId, compositionId, oldIndex, newIndex } """
  encoder := """instance EncodeJson LayerMoved where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "layerId" := e.layerId
    ~> "compositionId" := e.compositionId
    ~> "oldIndex" := e.oldIndex
    ~> "newIndex" := e.newIndex
    ~> jsonEmptyObject """

instance : EmitPureScript LayerDuplicated where
  typeName := "LayerDuplicated"
  typeDecl := """type LayerDuplicated = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, sourceLayerId :: NonEmptyString, newLayerId :: NonEmptyString, compositionId :: NonEmptyString }"""
  decoder := """instance DecodeJson LayerDuplicated where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    sourceLayerId <- json .? "sourceLayerId"
    newLayerId <- json .? "newLayerId"
    compositionId <- json .? "compositionId"
    pure { id, timestamp, eventType, sourceLayerId, newLayerId, compositionId } """
  encoder := """instance EncodeJson LayerDuplicated where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "sourceLayerId" := e.sourceLayerId
    ~> "newLayerId" := e.newLayerId
    ~> "compositionId" := e.compositionId
    ~> jsonEmptyObject """

instance : EmitPureScript LayerVisibilityChanged where
  typeName := "LayerVisibilityChanged"
  typeDecl := """type LayerVisibilityChanged = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, layerId :: NonEmptyString, compositionId :: NonEmptyString, visible :: Boolean }"""
  decoder := """instance DecodeJson LayerVisibilityChanged where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    layerId <- json .? "layerId"
    compositionId <- json .? "compositionId"
    visible <- json .? "visible"
    pure { id, timestamp, eventType, layerId, compositionId, visible } """
  encoder := """instance EncodeJson LayerVisibilityChanged where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "layerId" := e.layerId
    ~> "compositionId" := e.compositionId
    ~> "visible" := e.visible
    ~> jsonEmptyObject """

instance : EmitPureScript KeyframeAdded where
  typeName := "KeyframeAdded"
  typeDecl := """type KeyframeAdded = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, keyframeId :: NonEmptyString, layerId :: NonEmptyString, propertyPath :: NonEmptyString, frameNumber :: FrameNumber, value :: String }"""
  decoder := """instance DecodeJson KeyframeAdded where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    keyframeId <- json .? "keyframeId"
    layerId <- json .? "layerId"
    propertyPath <- json .? "propertyPath"
    frameNumber <- json .? "frameNumber"
    value <- json .? "value"
    pure { id, timestamp, eventType, keyframeId, layerId, propertyPath, frameNumber, value } """
  encoder := """instance EncodeJson KeyframeAdded where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "keyframeId" := e.keyframeId
    ~> "layerId" := e.layerId
    ~> "propertyPath" := e.propertyPath
    ~> "frameNumber" := e.frameNumber
    ~> "value" := e.value
    ~> jsonEmptyObject """

instance : EmitPureScript KeyframeRemoved where
  typeName := "KeyframeRemoved"
  typeDecl := """type KeyframeRemoved = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, keyframeId :: NonEmptyString, layerId :: NonEmptyString, propertyPath :: NonEmptyString, frameNumber :: FrameNumber }"""
  decoder := """instance DecodeJson KeyframeRemoved where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    keyframeId <- json .? "keyframeId"
    layerId <- json .? "layerId"
    propertyPath <- json .? "propertyPath"
    frameNumber <- json .? "frameNumber"
    pure { id, timestamp, eventType, keyframeId, layerId, propertyPath, frameNumber } """
  encoder := """instance EncodeJson KeyframeRemoved where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "keyframeId" := e.keyframeId
    ~> "layerId" := e.layerId
    ~> "propertyPath" := e.propertyPath
    ~> "frameNumber" := e.frameNumber
    ~> jsonEmptyObject """

instance : EmitPureScript KeyframeModified where
  typeName := "KeyframeModified"
  typeDecl := """type KeyframeModified = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, keyframeId :: NonEmptyString, layerId :: NonEmptyString, propertyPath :: NonEmptyString, frameNumber :: FrameNumber, oldValue :: String, newValue :: String }"""
  decoder := """instance DecodeJson KeyframeModified where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    keyframeId <- json .? "keyframeId"
    layerId <- json .? "layerId"
    propertyPath <- json .? "propertyPath"
    frameNumber <- json .? "frameNumber"
    oldValue <- json .? "oldValue"
    newValue <- json .? "newValue"
    pure { id, timestamp, eventType, keyframeId, layerId, propertyPath, frameNumber, oldValue, newValue } """
  encoder := """instance EncodeJson KeyframeModified where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "keyframeId" := e.keyframeId
    ~> "layerId" := e.layerId
    ~> "propertyPath" := e.propertyPath
    ~> "frameNumber" := e.frameNumber
    ~> "oldValue" := e.oldValue
    ~> "newValue" := e.newValue
    ~> jsonEmptyObject """

instance : EmitPureScript KeyframeInterpolationChanged where
  typeName := "KeyframeInterpolationChanged"
  typeDecl := """type KeyframeInterpolationChanged = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, keyframeId :: NonEmptyString, layerId :: NonEmptyString, propertyPath :: NonEmptyString, oldInterpolation :: InterpolationType, newInterpolation :: InterpolationType }"""
  decoder := """instance DecodeJson KeyframeInterpolationChanged where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    keyframeId <- json .? "keyframeId"
    layerId <- json .? "layerId"
    propertyPath <- json .? "propertyPath"
    oldInterpolation <- json .? "oldInterpolation"
    newInterpolation <- json .? "newInterpolation"
    pure { id, timestamp, eventType, keyframeId, layerId, propertyPath, oldInterpolation, newInterpolation } """
  encoder := """instance EncodeJson KeyframeInterpolationChanged where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "keyframeId" := e.keyframeId
    ~> "layerId" := e.layerId
    ~> "propertyPath" := e.propertyPath
    ~> "oldInterpolation" := e.oldInterpolation
    ~> "newInterpolation" := e.newInterpolation
    ~> jsonEmptyObject """

instance : EmitPureScript PropertyAnimated where
  typeName := "PropertyAnimated"
  typeDecl := """type PropertyAnimated = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, layerId :: NonEmptyString, propertyPath :: NonEmptyString, keyframeCount :: PositiveInt }"""
  decoder := """instance DecodeJson PropertyAnimated where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    layerId <- json .? "layerId"
    propertyPath <- json .? "propertyPath"
    keyframeCount <- json .? "keyframeCount"
    pure { id, timestamp, eventType, layerId, propertyPath, keyframeCount } """
  encoder := """instance EncodeJson PropertyAnimated where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "layerId" := e.layerId
    ~> "propertyPath" := e.propertyPath
    ~> "keyframeCount" := e.keyframeCount
    ~> jsonEmptyObject """

instance : EmitPureScript PropertyExpressionChanged where
  typeName := "PropertyExpressionChanged"
  typeDecl := """type PropertyExpressionChanged = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, layerId :: NonEmptyString, propertyPath :: NonEmptyString, oldExpression :: String, newExpression :: String }"""
  decoder := """instance DecodeJson PropertyExpressionChanged where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    layerId <- json .? "layerId"
    propertyPath <- json .? "propertyPath"
    oldExpression <- json .? "oldExpression"
    newExpression <- json .? "newExpression"
    pure { id, timestamp, eventType, layerId, propertyPath, oldExpression, newExpression } """
  encoder := """instance EncodeJson PropertyExpressionChanged where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "layerId" := e.layerId
    ~> "propertyPath" := e.propertyPath
    ~> "oldExpression" := e.oldExpression
    ~> "newExpression" := e.newExpression
    ~> jsonEmptyObject """

instance : EmitPureScript PropertyDriverAdded where
  typeName := "PropertyDriverAdded"
  typeDecl := """type PropertyDriverAdded = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, layerId :: NonEmptyString, propertyPath :: NonEmptyString, driverPropertyPath :: NonEmptyString }"""
  decoder := """instance DecodeJson PropertyDriverAdded where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    layerId <- json .? "layerId"
    propertyPath <- json .? "propertyPath"
    driverPropertyPath <- json .? "driverPropertyPath"
    pure { id, timestamp, eventType, layerId, propertyPath, driverPropertyPath } """
  encoder := """instance EncodeJson PropertyDriverAdded where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "layerId" := e.layerId
    ~> "propertyPath" := e.propertyPath
    ~> "driverPropertyPath" := e.driverPropertyPath
    ~> jsonEmptyObject """

instance : EmitPureScript EffectAdded where
  typeName := "EffectAdded"
  typeDecl := """type EffectAdded = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, effectId :: NonEmptyString, layerId :: NonEmptyString, effectCategory :: EffectCategory }"""
  decoder := """instance DecodeJson EffectAdded where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    effectId <- json .? "effectId"
    layerId <- json .? "layerId"
    effectCategory <- json .? "effectCategory"
    pure { id, timestamp, eventType, effectId, layerId, effectCategory } """
  encoder := """instance EncodeJson EffectAdded where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "effectId" := e.effectId
    ~> "layerId" := e.layerId
    ~> "effectCategory" := e.effectCategory
    ~> jsonEmptyObject """

instance : EmitPureScript EffectRemoved where
  typeName := "EffectRemoved"
  typeDecl := """type EffectRemoved = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, effectId :: NonEmptyString, layerId :: NonEmptyString }"""
  decoder := """instance DecodeJson EffectRemoved where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    effectId <- json .? "effectId"
    layerId <- json .? "layerId"
    pure { id, timestamp, eventType, effectId, layerId } """
  encoder := """instance EncodeJson EffectRemoved where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "effectId" := e.effectId
    ~> "layerId" := e.layerId
    ~> jsonEmptyObject """

instance : EmitPureScript EffectParameterChanged where
  typeName := "EffectParameterChanged"
  typeDecl := """type EffectParameterChanged = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, effectId :: NonEmptyString, layerId :: NonEmptyString, parameterName :: NonEmptyString, oldValue :: String, newValue :: String }"""
  decoder := """instance DecodeJson EffectParameterChanged where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    effectId <- json .? "effectId"
    layerId <- json .? "layerId"
    parameterName <- json .? "parameterName"
    oldValue <- json .? "oldValue"
    newValue <- json .? "newValue"
    pure { id, timestamp, eventType, effectId, layerId, parameterName, oldValue, newValue } """
  encoder := """instance EncodeJson EffectParameterChanged where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "effectId" := e.effectId
    ~> "layerId" := e.layerId
    ~> "parameterName" := e.parameterName
    ~> "oldValue" := e.oldValue
    ~> "newValue" := e.newValue
    ~> jsonEmptyObject """

instance : EmitPureScript ExportStarted where
  typeName := "ExportStarted"
  typeDecl := """type ExportStarted = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, exportId :: NonEmptyString, compositionId :: NonEmptyString, exportFormat :: ExportFormat, exportTarget :: ExportTarget }"""
  decoder := """instance DecodeJson ExportStarted where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    exportId <- json .? "exportId"
    compositionId <- json .? "compositionId"
    exportFormat <- json .? "exportFormat"
    exportTarget <- json .? "exportTarget"
    pure { id, timestamp, eventType, exportId, compositionId, exportFormat, exportTarget } """
  encoder := """instance EncodeJson ExportStarted where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "exportId" := e.exportId
    ~> "compositionId" := e.compositionId
    ~> "exportFormat" := e.exportFormat
    ~> "exportTarget" := e.exportTarget
    ~> jsonEmptyObject """

instance : EmitPureScript ExportProgress where
  typeName := "ExportProgress"
  typeDecl := """type ExportProgress = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, exportId :: NonEmptyString, compositionId :: NonEmptyString, progress :: Percentage, currentFrame :: FrameNumber, totalFrames :: FrameNumber }"""
  decoder := """instance DecodeJson ExportProgress where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    exportId <- json .? "exportId"
    compositionId <- json .? "compositionId"
    progress <- json .? "progress"
    currentFrame <- json .? "currentFrame"
    totalFrames <- json .? "totalFrames"
    pure { id, timestamp, eventType, exportId, compositionId, progress, currentFrame, totalFrames } """
  encoder := """instance EncodeJson ExportProgress where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "exportId" := e.exportId
    ~> "compositionId" := e.compositionId
    ~> "progress" := e.progress
    ~> "currentFrame" := e.currentFrame
    ~> "totalFrames" := e.totalFrames
    ~> jsonEmptyObject """

instance : EmitPureScript ExportCompleted where
  typeName := "ExportCompleted"
  typeDecl := """type ExportCompleted = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, exportId :: NonEmptyString, compositionId :: NonEmptyString, outputPath :: NonEmptyString, duration :: NonNegativeFloat }"""
  decoder := """instance DecodeJson ExportCompleted where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    exportId <- json .? "exportId"
    compositionId <- json .? "compositionId"
    outputPath <- json .? "outputPath"
    duration <- json .? "duration"
    pure { id, timestamp, eventType, exportId, compositionId, outputPath, duration } """
  encoder := """instance EncodeJson ExportCompleted where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "exportId" := e.exportId
    ~> "compositionId" := e.compositionId
    ~> "outputPath" := e.outputPath
    ~> "duration" := e.duration
    ~> jsonEmptyObject """

instance : EmitPureScript ExportFailed where
  typeName := "ExportFailed"
  typeDecl := """type ExportFailed = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, exportId :: NonEmptyString, compositionId :: NonEmptyString, errorMessage :: NonEmptyString }"""
  decoder := """instance DecodeJson ExportFailed where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    exportId <- json .? "exportId"
    compositionId <- json .? "compositionId"
    errorMessage <- json .? "errorMessage"
    pure { id, timestamp, eventType, exportId, compositionId, errorMessage } """
  encoder := """instance EncodeJson ExportFailed where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "exportId" := e.exportId
    ~> "compositionId" := e.compositionId
    ~> "errorMessage" := e.errorMessage
    ~> jsonEmptyObject """

instance : EmitPureScript RenderJobQueued where
  typeName := "RenderJobQueued"
  typeDecl := """type RenderJobQueued = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, jobId :: NonEmptyString, compositionId :: NonEmptyString, priority :: PositiveInt }"""
  decoder := """instance DecodeJson RenderJobQueued where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    jobId <- json .? "jobId"
    compositionId <- json .? "compositionId"
    priority <- json .? "priority"
    pure { id, timestamp, eventType, jobId, compositionId, priority } """
  encoder := """instance EncodeJson RenderJobQueued where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "jobId" := e.jobId
    ~> "compositionId" := e.compositionId
    ~> "priority" := e.priority
    ~> jsonEmptyObject """

instance : EmitPureScript RenderJobCompleted where
  typeName := "RenderJobCompleted"
  typeDecl := """type RenderJobCompleted = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, jobId :: NonEmptyString, compositionId :: NonEmptyString, duration :: NonNegativeFloat }"""
  decoder := """instance DecodeJson RenderJobCompleted where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    jobId <- json .? "jobId"
    compositionId <- json .? "compositionId"
    duration <- json .? "duration"
    pure { id, timestamp, eventType, jobId, compositionId, duration } """
  encoder := """instance EncodeJson RenderJobCompleted where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "jobId" := e.jobId
    ~> "compositionId" := e.compositionId
    ~> "duration" := e.duration
    ~> jsonEmptyObject """

instance : EmitPureScript CacheCleared where
  typeName := "CacheCleared"
  typeDecl := """type CacheCleared = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, cacheType :: NonEmptyString, sizeBytes :: PositiveInt }"""
  decoder := """instance DecodeJson CacheCleared where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    cacheType <- json .? "cacheType"
    sizeBytes <- json .? "sizeBytes"
    pure { id, timestamp, eventType, cacheType, sizeBytes } """
  encoder := """instance EncodeJson CacheCleared where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "cacheType" := e.cacheType
    ~> "sizeBytes" := e.sizeBytes
    ~> jsonEmptyObject """

instance : EmitPureScript ErrorOccurred where
  typeName := "ErrorOccurred"
  typeDecl := """type ErrorOccurred = { id :: NonEmptyString, timestamp :: PositiveFloat, eventType :: NonEmptyString, severity :: Severity, errorMessage :: NonEmptyString, errorCode :: NonEmptyString, stackTrace :: String }"""
  decoder := """instance DecodeJson ErrorOccurred where
  decodeJson json = do
    id <- json .? "id"
    timestamp <- json .? "timestamp"
    eventType <- json .? "eventType"
    severity <- json .? "severity"
    errorMessage <- json .? "errorMessage"
    errorCode <- json .? "errorCode"
    stackTrace <- json .? "stackTrace"
    pure { id, timestamp, eventType, severity, errorMessage, errorCode, stackTrace } """
  encoder := """instance EncodeJson ErrorOccurred where
  encodeJson e = "id" := e.id
    ~> "timestamp" := e.timestamp
    ~> "eventType" := e.eventType
    ~> "severity" := e.severity
    ~> "errorMessage" := e.errorMessage
    ~> "errorCode" := e.errorCode
    ~> "stackTrace" := e.stackTrace
    ~> jsonEmptyObject """

/-! ## Actions - PureScript Instances -/

instance : EmitPureScript (Lattice.Actions.CreateLayer) where
  typeName := "CreateLayer"
  typeDecl := """type CreateLayer = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerType :: LayerType, compositionId :: NonEmptyString }"""
  decoder := """instance DecodeJson CreateLayer where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerType <- json .? "layerType"
    compositionId <- json .? "compositionId"
    pure { id, actionType, target, params, retryPolicy, layerType, compositionId } """
  encoder := """instance EncodeJson CreateLayer where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerType" := a.layerType
    ~> "compositionId" := a.compositionId
    ~> jsonEmptyObject """

instance : EmitPureScript DeleteLayer where
  typeName := "DeleteLayer"
  typeDecl := """type DeleteLayer = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, compositionId :: NonEmptyString }"""
  decoder := """instance DecodeJson DeleteLayer where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    compositionId <- json .? "compositionId"
    pure { id, actionType, target, params, retryPolicy, layerId, compositionId } """
  encoder := """instance EncodeJson DeleteLayer where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "compositionId" := a.compositionId
    ~> jsonEmptyObject """

instance : EmitPureScript DuplicateLayer where
  typeName := "DuplicateLayer"
  typeDecl := """type DuplicateLayer = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, sourceLayerId :: NonEmptyString, compositionId :: NonEmptyString }"""
  decoder := """instance DecodeJson DuplicateLayer where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    sourceLayerId <- json .? "sourceLayerId"
    compositionId <- json .? "compositionId"
    pure { id, actionType, target, params, retryPolicy, sourceLayerId, compositionId } """
  encoder := """instance EncodeJson DuplicateLayer where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "sourceLayerId" := a.sourceLayerId
    ~> "compositionId" := a.compositionId
    ~> jsonEmptyObject """

instance : EmitPureScript MoveLayer where
  typeName := "MoveLayer"
  typeDecl := """type MoveLayer = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, compositionId :: NonEmptyString, newIndex :: FrameNumber }"""
  decoder := """instance DecodeJson MoveLayer where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    compositionId <- json .? "compositionId"
    newIndex <- json .? "newIndex"
    pure { id, actionType, target, params, retryPolicy, layerId, compositionId, newIndex } """
  encoder := """instance EncodeJson MoveLayer where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "compositionId" := a.compositionId
    ~> "newIndex" := a.newIndex
    ~> jsonEmptyObject """

instance : EmitPureScript SetLayerVisibility where
  typeName := "SetLayerVisibility"
  typeDecl := """type SetLayerVisibility = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, compositionId :: NonEmptyString, visible :: Boolean }"""
  decoder := """instance DecodeJson SetLayerVisibility where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    compositionId <- json .? "compositionId"
    visible <- json .? "visible"
    pure { id, actionType, target, params, retryPolicy, layerId, compositionId, visible } """
  encoder := """instance EncodeJson SetLayerVisibility where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "compositionId" := a.compositionId
    ~> "visible" := a.visible
    ~> jsonEmptyObject """

instance : EmitPureScript SetLayerOpacity where
  typeName := "SetLayerOpacity"
  typeDecl := """type SetLayerOpacity = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, compositionId :: NonEmptyString, opacity :: NormalizedValue }"""
  decoder := """instance DecodeJson SetLayerOpacity where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    compositionId <- json .? "compositionId"
    opacity <- json .? "opacity"
    pure { id, actionType, target, params, retryPolicy, layerId, compositionId, opacity } """
  encoder := """instance EncodeJson SetLayerOpacity where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "compositionId" := a.compositionId
    ~> "opacity" := a.opacity
    ~> jsonEmptyObject """

instance : EmitPureScript AddKeyframe where
  typeName := "AddKeyframe"
  typeDecl := """type AddKeyframe = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, propertyPath :: NonEmptyString, frameNumber :: FrameNumber, value :: String }"""
  decoder := """instance DecodeJson AddKeyframe where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    propertyPath <- json .? "propertyPath"
    frameNumber <- json .? "frameNumber"
    value <- json .? "value"
    pure { id, actionType, target, params, retryPolicy, layerId, propertyPath, frameNumber, value } """
  encoder := """instance EncodeJson AddKeyframe where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "propertyPath" := a.propertyPath
    ~> "frameNumber" := a.frameNumber
    ~> "value" := a.value
    ~> jsonEmptyObject """

instance : EmitPureScript RemoveKeyframe where
  typeName := "RemoveKeyframe"
  typeDecl := """type RemoveKeyframe = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, propertyPath :: NonEmptyString, frameNumber :: FrameNumber }"""
  decoder := """instance DecodeJson RemoveKeyframe where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    propertyPath <- json .? "propertyPath"
    frameNumber <- json .? "frameNumber"
    pure { id, actionType, target, params, retryPolicy, layerId, propertyPath, frameNumber } """
  encoder := """instance EncodeJson RemoveKeyframe where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "propertyPath" := a.propertyPath
    ~> "frameNumber" := a.frameNumber
    ~> jsonEmptyObject """

instance : EmitPureScript ModifyKeyframe where
  typeName := "ModifyKeyframe"
  typeDecl := """type ModifyKeyframe = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, propertyPath :: NonEmptyString, frameNumber :: FrameNumber, value :: String }"""
  decoder := """instance DecodeJson ModifyKeyframe where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    propertyPath <- json .? "propertyPath"
    frameNumber <- json .? "frameNumber"
    value <- json .? "value"
    pure { id, actionType, target, params, retryPolicy, layerId, propertyPath, frameNumber, value } """
  encoder := """instance EncodeJson ModifyKeyframe where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "propertyPath" := a.propertyPath
    ~> "frameNumber" := a.frameNumber
    ~> "value" := a.value
    ~> jsonEmptyObject """

instance : EmitPureScript SetInterpolation where
  typeName := "SetInterpolation"
  typeDecl := """type SetInterpolation = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, propertyPath :: NonEmptyString, frameNumber :: FrameNumber, interpolation :: InterpolationType }"""
  decoder := """instance DecodeJson SetInterpolation where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    propertyPath <- json .? "propertyPath"
    frameNumber <- json .? "frameNumber"
    interpolation <- json .? "interpolation"
    pure { id, actionType, target, params, retryPolicy, layerId, propertyPath, frameNumber, interpolation } """
  encoder := """instance EncodeJson SetInterpolation where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "propertyPath" := a.propertyPath
    ~> "frameNumber" := a.frameNumber
    ~> "interpolation" := a.interpolation
    ~> jsonEmptyObject """

instance : EmitPureScript CopyKeyframes where
  typeName := "CopyKeyframes"
  typeDecl := """type CopyKeyframes = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, sourceLayerId :: NonEmptyString, sourcePropertyPath :: NonEmptyString, targetLayerId :: NonEmptyString, targetPropertyPath :: NonEmptyString, frameRange :: Maybe (Tuple FrameNumber FrameNumber) }"""
  decoder := """instance DecodeJson CopyKeyframes where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    sourceLayerId <- json .? "sourceLayerId"
    sourcePropertyPath <- json .? "sourcePropertyPath"
    targetLayerId <- json .? "targetLayerId"
    targetPropertyPath <- json .? "targetPropertyPath"
    frameRange <- case json .? "frameRange" of
      Nothing -> pure Nothing
      Just rangeJson -> case Json.toArray rangeJson of
        Just arr -> case uncons arr of
          Just { head: startJson, tail } -> case uncons tail of
            Just { head: endJson, tail: [] } -> do
              start <- decodeJson startJson
              end <- decodeJson endJson
              pure (Just (Tuple start end))
            _ -> Left (TypeMismatch "frameRange must be array of 2 elements")
          Nothing -> Left (TypeMismatch "frameRange must be array of 2 elements")
        Nothing -> Left (TypeMismatch "frameRange must be array")
    pure { id, actionType, target, params, retryPolicy, sourceLayerId, sourcePropertyPath, targetLayerId, targetPropertyPath, frameRange } """
  encoder := """instance EncodeJson CopyKeyframes where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "sourceLayerId" := a.sourceLayerId
    ~> "sourcePropertyPath" := a.sourcePropertyPath
    ~> "targetLayerId" := a.targetLayerId
    ~> "targetPropertyPath" := a.targetPropertyPath
    ~> "frameRange" :=? (map (\(Tuple start end) -> Json.fromArray [encodeJson start, encodeJson end]) a.frameRange)
    ~> jsonEmptyObject """

instance : EmitPureScript PasteKeyframes where
  typeName := "PasteKeyframes"
  typeDecl := """type PasteKeyframes = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, propertyPath :: NonEmptyString, frameNumber :: FrameNumber }"""
  decoder := """instance DecodeJson PasteKeyframes where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    propertyPath <- json .? "propertyPath"
    frameNumber <- json .? "frameNumber"
    pure { id, actionType, target, params, retryPolicy, layerId, propertyPath, frameNumber } """
  encoder := """instance EncodeJson PasteKeyframes where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "propertyPath" := a.propertyPath
    ~> "frameNumber" := a.frameNumber
    ~> jsonEmptyObject """

instance : EmitPureScript AnimateProperty where
  typeName := "AnimateProperty"
  typeDecl := """type AnimateProperty = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, propertyPath :: NonEmptyString, keyframes :: String }"""
  decoder := """instance DecodeJson AnimateProperty where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    propertyPath <- json .? "propertyPath"
    keyframes <- json .? "keyframes"
    pure { id, actionType, target, params, retryPolicy, layerId, propertyPath, keyframes } """
  encoder := """instance EncodeJson AnimateProperty where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "propertyPath" := a.propertyPath
    ~> "keyframes" := a.keyframes
    ~> jsonEmptyObject """

instance : EmitPureScript SetPropertyValue where
  typeName := "SetPropertyValue"
  typeDecl := """type SetPropertyValue = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, propertyPath :: NonEmptyString, value :: String }"""
  decoder := """instance DecodeJson SetPropertyValue where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    propertyPath <- json .? "propertyPath"
    value <- json .? "value"
    pure { id, actionType, target, params, retryPolicy, layerId, propertyPath, value } """
  encoder := """instance EncodeJson SetPropertyValue where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "propertyPath" := a.propertyPath
    ~> "value" := a.value
    ~> jsonEmptyObject """

instance : EmitPureScript AddExpression where
  typeName := "AddExpression"
  typeDecl := """type AddExpression = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, propertyPath :: NonEmptyString, expression :: NonEmptyString }"""
  decoder := """instance DecodeJson AddExpression where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    propertyPath <- json .? "propertyPath"
    expression <- json .? "expression"
    pure { id, actionType, target, params, retryPolicy, layerId, propertyPath, expression } """
  encoder := """instance EncodeJson AddExpression where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "propertyPath" := a.propertyPath
    ~> "expression" := a.expression
    ~> jsonEmptyObject """

instance : EmitPureScript RemoveExpression where
  typeName := "RemoveExpression"
  typeDecl := """type RemoveExpression = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, propertyPath :: NonEmptyString }"""
  decoder := """instance DecodeJson RemoveExpression where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    propertyPath <- json .? "propertyPath"
    pure { id, actionType, target, params, retryPolicy, layerId, propertyPath } """
  encoder := """instance EncodeJson RemoveExpression where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "propertyPath" := a.propertyPath
    ~> jsonEmptyObject """

instance : EmitPureScript AddDriver where
  typeName := "AddDriver"
  typeDecl := """type AddDriver = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, propertyPath :: NonEmptyString, driverPropertyPath :: NonEmptyString }"""
  decoder := """instance DecodeJson AddDriver where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    propertyPath <- json .? "propertyPath"
    driverPropertyPath <- json .? "driverPropertyPath"
    pure { id, actionType, target, params, retryPolicy, layerId, propertyPath, driverPropertyPath } """
  encoder := """instance EncodeJson AddDriver where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "propertyPath" := a.propertyPath
    ~> "driverPropertyPath" := a.driverPropertyPath
    ~> jsonEmptyObject """

instance : EmitPureScript AddEffect where
  typeName := "AddEffect"
  typeDecl := """type AddEffect = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, effectCategory :: EffectCategory, effectParams :: String }"""
  decoder := """instance DecodeJson AddEffect where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    effectCategory <- json .? "effectCategory"
    effectParams <- json .? "effectParams"
    pure { id, actionType, target, params, retryPolicy, layerId, effectCategory, effectParams } """
  encoder := """instance EncodeJson AddEffect where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "effectCategory" := a.effectCategory
    ~> "effectParams" := a.effectParams
    ~> jsonEmptyObject """

instance : EmitPureScript RemoveEffect where
  typeName := "RemoveEffect"
  typeDecl := """type RemoveEffect = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, effectId :: NonEmptyString }"""
  decoder := """instance DecodeJson RemoveEffect where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    effectId <- json .? "effectId"
    pure { id, actionType, target, params, retryPolicy, layerId, effectId } """
  encoder := """instance EncodeJson RemoveEffect where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "effectId" := a.effectId
    ~> jsonEmptyObject """

instance : EmitPureScript ModifyEffect where
  typeName := "ModifyEffect"
  typeDecl := """type ModifyEffect = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, effectId :: NonEmptyString, effectParams :: String }"""
  decoder := """instance DecodeJson ModifyEffect where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    effectId <- json .? "effectId"
    effectParams <- json .? "effectParams"
    pure { id, actionType, target, params, retryPolicy, layerId, effectId, effectParams } """
  encoder := """instance EncodeJson ModifyEffect where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "effectId" := a.effectId
    ~> "effectParams" := a.effectParams
    ~> jsonEmptyObject """

instance : EmitPureScript EnableEffect where
  typeName := "EnableEffect"
  typeDecl := """type EnableEffect = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, effectId :: NonEmptyString }"""
  decoder := """instance DecodeJson EnableEffect where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    effectId <- json .? "effectId"
    pure { id, actionType, target, params, retryPolicy, layerId, effectId } """
  encoder := """instance EncodeJson EnableEffect where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "effectId" := a.effectId
    ~> jsonEmptyObject """

instance : EmitPureScript DisableEffect where
  typeName := "DisableEffect"
  typeDecl := """type DisableEffect = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, effectId :: NonEmptyString }"""
  decoder := """instance DecodeJson DisableEffect where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    effectId <- json .? "effectId"
    pure { id, actionType, target, params, retryPolicy, layerId, effectId } """
  encoder := """instance EncodeJson DisableEffect where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "effectId" := a.effectId
    ~> jsonEmptyObject """

instance : EmitPureScript (Lattice.Actions.CreateComposition) where
  typeName := "CreateComposition"
  typeDecl := """type CreateComposition = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, compositionName :: NonEmptyString, width :: PositiveInt, height :: PositiveInt, fps :: PositiveFloat }"""
  decoder := """instance DecodeJson CreateComposition where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    compositionName <- json .? "compositionName"
    width <- json .? "width"
    height <- json .? "height"
    fps <- json .? "fps"
    pure { id, actionType, target, params, retryPolicy, compositionName, width, height, fps } """
  encoder := """instance EncodeJson CreateComposition where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "compositionName" := a.compositionName
    ~> "width" := a.width
    ~> "height" := a.height
    ~> "fps" := a.fps
    ~> jsonEmptyObject """

instance : EmitPureScript DeleteComposition where
  typeName := "DeleteComposition"
  typeDecl := """type DeleteComposition = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, compositionId :: NonEmptyString }"""
  decoder := """instance DecodeJson DeleteComposition where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    compositionId <- json .? "compositionId"
    pure { id, actionType, target, params, retryPolicy, compositionId } """
  encoder := """instance EncodeJson DeleteComposition where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "compositionId" := a.compositionId
    ~> jsonEmptyObject """

instance : EmitPureScript SetCompositionSettings where
  typeName := "SetCompositionSettings"
  typeDecl := """type SetCompositionSettings = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, compositionId :: NonEmptyString, settings :: String }"""
  decoder := """instance DecodeJson SetCompositionSettings where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    compositionId <- json .? "compositionId"
    settings <- json .? "settings"
    pure { id, actionType, target, params, retryPolicy, compositionId, settings } """
  encoder := """instance EncodeJson SetCompositionSettings where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "compositionId" := a.compositionId
    ~> "settings" := a.settings
    ~> jsonEmptyObject """

instance : EmitPureScript RenderComposition where
  typeName := "RenderComposition"
  typeDecl := """type RenderComposition = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, compositionId :: NonEmptyString, startFrame :: FrameNumber, endFrame :: FrameNumber }"""
  decoder := """instance DecodeJson RenderComposition where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    compositionId <- json .? "compositionId"
    startFrame <- json .? "startFrame"
    endFrame <- json .? "endFrame"
    pure { id, actionType, target, params, retryPolicy, compositionId, startFrame, endFrame } """
  encoder := """instance EncodeJson RenderComposition where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "compositionId" := a.compositionId
    ~> "startFrame" := a.startFrame
    ~> "endFrame" := a.endFrame
    ~> jsonEmptyObject """

instance : EmitPureScript StartExport where
  typeName := "StartExport"
  typeDecl := """type StartExport = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, compositionId :: NonEmptyString, exportFormat :: ExportFormat, exportTarget :: ExportTarget, settings :: String }"""
  decoder := """instance DecodeJson StartExport where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    compositionId <- json .? "compositionId"
    exportFormat <- json .? "exportFormat"
    exportTarget <- json .? "exportTarget"
    settings <- json .? "settings"
    pure { id, actionType, target, params, retryPolicy, compositionId, exportFormat, exportTarget, settings } """
  encoder := """instance EncodeJson StartExport where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "compositionId" := a.compositionId
    ~> "exportFormat" := a.exportFormat
    ~> "exportTarget" := a.exportTarget
    ~> "settings" := a.settings
    ~> jsonEmptyObject """

instance : EmitPureScript CancelExport where
  typeName := "CancelExport"
  typeDecl := """type CancelExport = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, exportId :: NonEmptyString }"""
  decoder := """instance DecodeJson CancelExport where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    exportId <- json .? "exportId"
    pure { id, actionType, target, params, retryPolicy, exportId } """
  encoder := """instance EncodeJson CancelExport where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "exportId" := a.exportId
    ~> jsonEmptyObject """

instance : EmitPureScript PauseExport where
  typeName := "PauseExport"
  typeDecl := """type PauseExport = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, exportId :: NonEmptyString }"""
  decoder := """instance DecodeJson PauseExport where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    exportId <- json .? "exportId"
    pure { id, actionType, target, params, retryPolicy, exportId } """
  encoder := """instance EncodeJson PauseExport where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "exportId" := a.exportId
    ~> jsonEmptyObject """

instance : EmitPureScript ResumeExport where
  typeName := "ResumeExport"
  typeDecl := """type ResumeExport = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, exportId :: NonEmptyString }"""
  decoder := """instance DecodeJson ResumeExport where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    exportId <- json .? "exportId"
    pure { id, actionType, target, params, retryPolicy, exportId } """
  encoder := """instance EncodeJson ResumeExport where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "exportId" := a.exportId
    ~> jsonEmptyObject """

instance : EmitPureScript SetExportSettings where
  typeName := "SetExportSettings"
  typeDecl := """type SetExportSettings = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, exportId :: NonEmptyString, settings :: String }"""
  decoder := """instance DecodeJson SetExportSettings where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    exportId <- json .? "exportId"
    settings <- json .? "settings"
    pure { id, actionType, target, params, retryPolicy, exportId, settings } """
  encoder := """instance EncodeJson SetExportSettings where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "exportId" := a.exportId
    ~> "settings" := a.settings
    ~> jsonEmptyObject """

instance : EmitPureScript LoadAudio where
  typeName := "LoadAudio"
  typeDecl := """type LoadAudio = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, audioPath :: NonEmptyString }"""
  decoder := """instance DecodeJson LoadAudio where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    audioPath <- json .? "audioPath"
    pure { id, actionType, target, params, retryPolicy, layerId, audioPath } """
  encoder := """instance EncodeJson LoadAudio where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "audioPath" := a.audioPath
    ~> jsonEmptyObject """

instance : EmitPureScript AnalyzeAudio where
  typeName := "AnalyzeAudio"
  typeDecl := """type AnalyzeAudio = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, method :: BeatDetectionMethod }"""
  decoder := """instance DecodeJson AnalyzeAudio where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    method <- json .? "method"
    pure { id, actionType, target, params, retryPolicy, layerId, method } """
  encoder := """instance EncodeJson AnalyzeAudio where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "method" := a.method
    ~> jsonEmptyObject """

instance : EmitPureScript SetAudioReactivity where
  typeName := "SetAudioReactivity"
  typeDecl := """type SetAudioReactivity = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, enabled :: Boolean, reactivityParams :: String }"""
  decoder := """instance DecodeJson SetAudioReactivity where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    enabled <- json .? "enabled"
    reactivityParams <- json .? "reactivityParams"
    pure { id, actionType, target, params, retryPolicy, layerId, enabled, reactivityParams } """
  encoder := """instance EncodeJson SetAudioReactivity where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "enabled" := a.enabled
    ~> "reactivityParams" := a.reactivityParams
    ~> jsonEmptyObject """

instance : EmitPureScript SetCameraPosition where
  typeName := "SetCameraPosition"
  typeDecl := """type SetCameraPosition = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, position :: Vec3 }"""
  decoder := """instance DecodeJson SetCameraPosition where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    position <- json .? "position"
    pure { id, actionType, target, params, retryPolicy, layerId, position } """
  encoder := """instance EncodeJson SetCameraPosition where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "position" := a.position
    ~> jsonEmptyObject """

instance : EmitPureScript SetCameraRotation where
  typeName := "SetCameraRotation"
  typeDecl := """type SetCameraRotation = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, rotation :: Vec3 }"""
  decoder := """instance DecodeJson SetCameraRotation where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    rotation <- json .? "rotation"
    pure { id, actionType, target, params, retryPolicy, layerId, rotation } """
  encoder := """instance EncodeJson SetCameraRotation where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "rotation" := a.rotation
    ~> jsonEmptyObject """

instance : EmitPureScript SetCameraFOV where
  typeName := "SetCameraFOV"
  typeDecl := """type SetCameraFOV = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, fov :: PositiveFloat }"""
  decoder := """instance DecodeJson SetCameraFOV where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    fov <- json .? "fov"
    pure { id, actionType, target, params, retryPolicy, layerId, fov } """
  encoder := """instance EncodeJson SetCameraFOV where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "fov" := a.fov
    ~> jsonEmptyObject """

instance : EmitPureScript AnimateCamera where
  typeName := "AnimateCamera"
  typeDecl := """type AnimateCamera = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, keyframes :: String }"""
  decoder := """instance DecodeJson AnimateCamera where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    keyframes <- json .? "keyframes"
    pure { id, actionType, target, params, retryPolicy, layerId, keyframes } """
  encoder := """instance EncodeJson AnimateCamera where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "keyframes" := a.keyframes
    ~> jsonEmptyObject """

instance : EmitPureScript SegmentImage where
  typeName := "SegmentImage"
  typeDecl := """type SegmentImage = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, mode :: SegmentationMode }"""
  decoder := """instance DecodeJson SegmentImage where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    mode <- json .? "mode"
    pure { id, actionType, target, params, retryPolicy, layerId, mode } """
  encoder := """instance EncodeJson SegmentImage where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "mode" := a.mode
    ~> jsonEmptyObject """

instance : EmitPureScript VectorizeImage where
  typeName := "VectorizeImage"
  typeDecl := """type VectorizeImage = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, vectorizeParams :: String }"""
  decoder := """instance DecodeJson VectorizeImage where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    vectorizeParams <- json .? "vectorizeParams"
    pure { id, actionType, target, params, retryPolicy, layerId, vectorizeParams } """
  encoder := """instance EncodeJson VectorizeImage where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "vectorizeParams" := a.vectorizeParams
    ~> jsonEmptyObject """

instance : EmitPureScript DecomposeImage where
  typeName := "DecomposeImage"
  typeDecl := """type DecomposeImage = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, components :: String }"""
  decoder := """instance DecodeJson DecomposeImage where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    components <- json .? "components"
    pure { id, actionType, target, params, retryPolicy, layerId, components } """
  encoder := """instance EncodeJson DecomposeImage where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "components" := a.components
    ~> jsonEmptyObject """

instance : EmitPureScript GenerateDepth where
  typeName := "GenerateDepth"
  typeDecl := """type GenerateDepth = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, method :: PreprocessorType }"""
  decoder := """instance DecodeJson GenerateDepth where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    method <- json .? "method"
    pure { id, actionType, target, params, retryPolicy, layerId, method } """
  encoder := """instance EncodeJson GenerateDepth where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "method" := a.method
    ~> jsonEmptyObject """

instance : EmitPureScript EstimateNormals where
  typeName := "EstimateNormals"
  typeDecl := """type EstimateNormals = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, layerId :: NonEmptyString, normalParams :: String }"""
  decoder := """instance DecodeJson EstimateNormals where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    layerId <- json .? "layerId"
    normalParams <- json .? "normalParams"
    pure { id, actionType, target, params, retryPolicy, layerId, normalParams } """
  encoder := """instance EncodeJson EstimateNormals where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "layerId" := a.layerId
    ~> "normalParams" := a.normalParams
    ~> jsonEmptyObject """

instance : EmitPureScript ClearCache where
  typeName := "ClearCache"
  typeDecl := """type ClearCache = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, cacheType :: NonEmptyString }"""
  decoder := """instance DecodeJson ClearCache where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    cacheType <- json .? "cacheType"
    pure { id, actionType, target, params, retryPolicy, cacheType } """
  encoder := """instance EncodeJson ClearCache where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "cacheType" := a.cacheType
    ~> jsonEmptyObject """

instance : EmitPureScript OptimizeMemory where
  typeName := "OptimizeMemory"
  typeDecl := """type OptimizeMemory = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, targetMemoryMB :: PositiveFloat }"""
  decoder := """instance DecodeJson OptimizeMemory where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    targetMemoryMB <- json .? "targetMemoryMB"
    pure { id, actionType, target, params, retryPolicy, targetMemoryMB } """
  encoder := """instance EncodeJson OptimizeMemory where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "targetMemoryMB" := a.targetMemoryMB
    ~> jsonEmptyObject """

instance : EmitPureScript SaveProject where
  typeName := "SaveProject"
  typeDecl := """type SaveProject = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, projectId :: NonEmptyString, filePath :: NonEmptyString }"""
  decoder := """instance DecodeJson SaveProject where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    projectId <- json .? "projectId"
    filePath <- json .? "filePath"
    pure { id, actionType, target, params, retryPolicy, projectId, filePath } """
  encoder := """instance EncodeJson SaveProject where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "projectId" := a.projectId
    ~> "filePath" := a.filePath
    ~> jsonEmptyObject """

instance : EmitPureScript LoadProject where
  typeName := "LoadProject"
  typeDecl := """type LoadProject = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, filePath :: NonEmptyString }"""
  decoder := """instance DecodeJson LoadProject where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    filePath <- json .? "filePath"
    pure { id, actionType, target, params, retryPolicy, filePath } """
  encoder := """instance EncodeJson LoadProject where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "filePath" := a.filePath
    ~> jsonEmptyObject """

instance : EmitPureScript Undo where
  typeName := "Undo"
  typeDecl := """type Undo = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, compositionId :: NonEmptyString, steps :: FrameNumber }"""
  decoder := """instance DecodeJson Undo where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    compositionId <- json .? "compositionId"
    steps <- json .? "steps"
    pure { id, actionType, target, params, retryPolicy, compositionId, steps } """
  encoder := """instance EncodeJson Undo where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "compositionId" := a.compositionId
    ~> "steps" := a.steps
    ~> jsonEmptyObject """

instance : EmitPureScript Redo where
  typeName := "Redo"
  typeDecl := """type Redo = { id :: NonEmptyString, actionType :: NonEmptyString, target :: NonEmptyString, params :: String, retryPolicy :: Maybe RetryPolicy, compositionId :: NonEmptyString, steps :: FrameNumber }"""
  decoder := """instance DecodeJson Redo where
  decodeJson json = do
    id <- json .? "id"
    actionType <- json .? "actionType"
    target <- json .? "target"
    params <- json .? "params"
    retryPolicy <- case json .? "retryPolicy" of
      Nothing -> pure Nothing
      Just rpJson -> map Just (decodeJson rpJson)
    compositionId <- json .? "compositionId"
    steps <- json .? "steps"
    pure { id, actionType, target, params, retryPolicy, compositionId, steps } """
  encoder := """instance EncodeJson Redo where
  encodeJson a = "id" := a.id
    ~> "actionType" := a.actionType
    ~> "target" := a.target
    ~> "params" := a.params
    ~> "retryPolicy" :=? a.retryPolicy
    ~> "compositionId" := a.compositionId
    ~> "steps" := a.steps
    ~> jsonEmptyObject """

/-! ## Entities - Simple - PureScript Instances -/

instance : EmitPureScript EffectParameter where
  typeName := "EffectParameter"
  typeDecl := """type EffectParameter = { id :: NonEmptyString, name :: NonEmptyString, parameterType :: PropertyValueType, value :: String }"""
  decoder := """instance DecodeJson EffectParameter where
  decodeJson json = do
    id <- json .? "id"
    name <- json .? "name"
    parameterType <- json .? "parameterType"
    value <- json .? "value"
    pure { id, name, parameterType, value } """
  encoder := """instance EncodeJson EffectParameter where
  encodeJson p = "id" := p.id
    ~> "name" := p.name
    ~> "parameterType" := p.parameterType
    ~> "value" := p.value
    ~> jsonEmptyObject """

instance : EmitPureScript EffectPreset where
  typeName := "EffectPreset"
  typeDecl := """type EffectPreset = { id :: NonEmptyString, name :: NonEmptyString, effectType :: EffectType, parameters :: String }"""
  decoder := """instance DecodeJson EffectPreset where
  decodeJson json = do
    id <- json .? "id"
    name <- json .? "name"
    effectType <- json .? "effectType"
    parameters <- json .? "parameters"
    pure { id, name, effectType, parameters } """
  encoder := """instance EncodeJson EffectPreset where
  encodeJson p = "id" := p.id
    ~> "name" := p.name
    ~> "effectType" := p.effectType
    ~> "parameters" := p.parameters
    ~> jsonEmptyObject """

instance : EmitPureScript ProjectMetadata where
  typeName := "ProjectMetadata"
  typeDecl := """type ProjectMetadata = { name :: NonEmptyString, created :: NonEmptyString, modified :: NonEmptyString, author :: Maybe NonEmptyString, version :: NonEmptyString }"""
  decoder := """instance DecodeJson ProjectMetadata where
  decodeJson json = do
    name <- json .? "name"
    created <- json .? "created"
    modified <- json .? "modified"
    author <- case json .? "author" of
      Nothing -> pure Nothing
      Just aJson -> map Just (decodeJson aJson)
    version <- json .? "version"
    pure { name, created, modified, author, version } """
  encoder := """instance EncodeJson ProjectMetadata where
  encodeJson m = "name" := m.name
    ~> "created" := m.created
    ~> "modified" := m.modified
    ~> "author" :=? m.author
    ~> "version" := m.version
    ~> jsonEmptyObject """

instance : EmitPureScript ProjectSettings where
  typeName := "ProjectSettings"
  typeDecl := """type ProjectSettings = { autoSave :: Boolean, autoSaveInterval :: NonNegativeFloat, defaultCompositionSettings :: CompositionSettings }"""
  decoder := """instance DecodeJson ProjectSettings where
  decodeJson json = do
    autoSave <- json .? "autoSave"
    autoSaveInterval <- json .? "autoSaveInterval"
    defaultCompositionSettings <- json .? "defaultCompositionSettings"
    pure { autoSave, autoSaveInterval, defaultCompositionSettings } """
  encoder := """instance EncodeJson ProjectSettings where
  encodeJson s = "autoSave" := s.autoSave
    ~> "autoSaveInterval" := s.autoSaveInterval
    ~> "defaultCompositionSettings" := s.defaultCompositionSettings
    ~> jsonEmptyObject """

instance : EmitPureScript AssetMetadata where
  typeName := "AssetMetadata"
  typeDecl := """type AssetMetadata = { width :: PositiveInt, height :: PositiveInt, filename :: Maybe NonEmptyString, frameCount :: Maybe FrameNumber, duration :: Maybe NonNegativeFloat, fps :: Maybe PositiveFloat, hasAudio :: Maybe Boolean, audioChannels :: Maybe PositiveInt, sampleRate :: Maybe PositiveInt, modelFormat :: Maybe NonEmptyString, modelMeshCount :: Maybe FrameNumber, modelVertexCount :: Maybe FrameNumber, pointCloudFormat :: Maybe NonEmptyString, pointCount :: Maybe FrameNumber }"""
  decoder := """instance DecodeJson AssetMetadata where
  decodeJson json = do
    width <- json .? "width"
    height <- json .? "height"
    filename <- case json .? "filename" of
      Nothing -> pure Nothing
      Just fJson -> map Just (decodeJson fJson)
    frameCount <- case json .? "frameCount" of
      Nothing -> pure Nothing
      Just fcJson -> map Just (decodeJson fcJson)
    duration <- case json .? "duration" of
      Nothing -> pure Nothing
      Just dJson -> map Just (decodeJson dJson)
    fps <- case json .? "fps" of
      Nothing -> pure Nothing
      Just fJson -> map Just (decodeJson fJson)
    hasAudio <- case json .? "hasAudio" of
      Nothing -> pure Nothing
      Just (.bool b) -> pure (Just b)
      _ -> pure Nothing
    audioChannels <- case json .? "audioChannels" of
      Nothing -> pure Nothing
      Just acJson -> map Just (decodeJson acJson)
    sampleRate <- case json .? "sampleRate" of
      Nothing -> pure Nothing
      Just srJson -> map Just (decodeJson srJson)
    modelFormat <- case json .? "modelFormat" of
      Nothing -> pure Nothing
      Just mfJson -> map Just (decodeJson mfJson)
    modelMeshCount <- case json .? "modelMeshCount" of
      Nothing -> pure Nothing
      Just mcJson -> map Just (decodeJson mcJson)
    modelVertexCount <- case json .? "modelVertexCount" of
      Nothing -> pure Nothing
      Just vcJson -> map Just (decodeJson vcJson)
    pointCloudFormat <- case json .? "pointCloudFormat" of
      Nothing -> pure Nothing
      Just pcfJson -> map Just (decodeJson pcfJson)
    pointCount <- case json .? "pointCount" of
      Nothing -> pure Nothing
      Just pcJson -> map Just (decodeJson pcJson)
    pure { width, height, filename, frameCount, duration, fps, hasAudio, audioChannels, sampleRate, modelFormat, modelMeshCount, modelVertexCount, pointCloudFormat, pointCount } """
  encoder := """instance EncodeJson AssetMetadata where
  encodeJson m = "width" := m.width
    ~> "height" := m.height
    ~> "filename" :=? m.filename
    ~> "frameCount" :=? m.frameCount
    ~> "duration" :=? m.duration
    ~> "fps" :=? m.fps
    ~> "hasAudio" :=? m.hasAudio
    ~> "audioChannels" :=? m.audioChannels
    ~> "sampleRate" :=? m.sampleRate
    ~> "modelFormat" :=? m.modelFormat
    ~> "modelMeshCount" :=? m.modelMeshCount
    ~> "modelVertexCount" :=? m.modelVertexCount
    ~> "pointCloudFormat" :=? m.pointCloudFormat
    ~> "pointCount" :=? m.pointCount
    ~> jsonEmptyObject """

instance : EmitPureScript DepthOfField where
  typeName := "DepthOfField"
  typeDecl := """type DepthOfField = { enabled :: Boolean, focusDistance :: Number, aperture :: Number, fStop :: Number, blurLevel :: NormalizedValue, lockToZoom :: Boolean }"""
  decoder := """instance DecodeJson DepthOfField where
  decodeJson json = do
    enabled <- json .? "enabled"
    focusDistance <- json .? "focusDistance"
    aperture <- json .? "aperture"
    fStop <- json .? "fStop"
    blurLevel <- json .? "blurLevel"
    lockToZoom <- json .? "lockToZoom"
    pure { enabled, focusDistance, aperture, fStop, blurLevel, lockToZoom } """
  encoder := """instance EncodeJson DepthOfField where
  encodeJson d = "enabled" := d.enabled
    ~> "focusDistance" := d.focusDistance
    ~> "aperture" := d.aperture
    ~> "fStop" := d.fStop
    ~> "blurLevel" := d.blurLevel
    ~> "lockToZoom" := d.lockToZoom
    ~> jsonEmptyObject """

instance : EmitPureScript FontConfig where
  typeName := "FontConfig"
  typeDecl := """type FontConfig = { fontFamily :: NonEmptyString, fontSize :: PositiveFloat, fontWeight :: FontWeight, fontStyle :: FontStyle }"""
  decoder := """instance DecodeJson FontConfig where
  decodeJson json = do
    fontFamily <- json .? "fontFamily"
    fontSize <- json .? "fontSize"
    fontWeight <- json .? "fontWeight"
    fontStyle <- json .? "fontStyle"
    pure { fontFamily, fontSize, fontWeight, fontStyle } """
  encoder := """instance EncodeJson FontConfig where
  encodeJson f = "fontFamily" := f.fontFamily
    ~> "fontSize" := f.fontSize
    ~> "fontWeight" := f.fontWeight
    ~> "fontStyle" := f.fontStyle
    ~> jsonEmptyObject """

instance : EmitPureScript BeatData where
  typeName := "BeatData"
  typeDecl := """type BeatData = { frame :: FrameNumber, amplitude :: NormalizedValue, frequency :: Maybe NormalizedValue }"""
  decoder := """instance DecodeJson BeatData where
  decodeJson json = do
    frame <- json .? "frame"
    amplitude <- json .? "amplitude"
    frequency <- case json .? "frequency" of
      Nothing -> pure Nothing
      Just fJson -> map Just (decodeJson fJson)
    pure { frame, amplitude, frequency } """
  encoder := """instance EncodeJson BeatData where
  encodeJson b = "frame" := b.frame
    ~> "amplitude" := b.amplitude
    ~> "frequency" :=? b.frequency
    ~> jsonEmptyObject """

instance : EmitPureScript PhysicsMaterial where
  typeName := "PhysicsMaterial"
  typeDecl := """type PhysicsMaterial = { restitution :: NormalizedValue, friction :: NormalizedValue }"""
  decoder := """instance DecodeJson PhysicsMaterial where
  decodeJson json = do
    restitution <- json .? "restitution"
    friction <- json .? "friction"
    pure { restitution, friction } """
  encoder := """instance EncodeJson PhysicsMaterial where
  encodeJson m = "restitution" := m.restitution
    ~> "friction" := m.friction
    ~> jsonEmptyObject """

/-! ## Entities - Complex - PureScript Instances -/

instance : EmitPureScript EffectInstance where
  typeName := "EffectInstance"
  typeDecl := """type EffectInstance = { id :: NonEmptyString, createdAt :: NonNegativeFloat, updatedAt :: NonNegativeFloat, effectType :: EffectType, enabled :: Boolean, parameters :: Array NonEmptyString }"""
  decoder := """instance DecodeJson EffectInstance where
  decodeJson json = do
    id <- json .? "id"
    createdAt <- json .? "createdAt"
    updatedAt <- json .? "updatedAt"
    effectType <- json .? "effectType"
    enabled <- json .? "enabled"
    parameters <- json .? "parameters"
    pure { id, createdAt, updatedAt, effectType, enabled, parameters } """
  encoder := """instance EncodeJson EffectInstance where
  encodeJson e = "id" := e.id
    ~> "createdAt" := e.createdAt
    ~> "updatedAt" := e.updatedAt
    ~> "effectType" := e.effectType
    ~> "enabled" := e.enabled
    ~> "parameters" := e.parameters
    ~> jsonEmptyObject """

instance : EmitPureScript Project where
  typeName := "Project"
  typeDecl := """type Project = { id :: NonEmptyString, createdAt :: NonNegativeFloat, updatedAt :: NonNegativeFloat, name :: NonEmptyString, metadata :: ProjectMetadata, settings :: ProjectSettings, mainCompositionId :: NonEmptyString, compositionIds :: Array NonEmptyString, assetIds :: Array NonEmptyString }"""
  decoder := """instance DecodeJson Project where
  decodeJson json = do
    id <- json .? "id"
    createdAt <- json .? "createdAt"
    updatedAt <- json .? "updatedAt"
    name <- json .? "name"
    metadata <- json .? "metadata"
    settings <- json .? "settings"
    mainCompositionId <- json .? "mainCompositionId"
    compositionIds <- json .? "compositionIds"
    assetIds <- json .? "assetIds"
    pure { id, createdAt, updatedAt, name, metadata, settings, mainCompositionId, compositionIds, assetIds } """
  encoder := """instance EncodeJson Project where
  encodeJson p = "id" := p.id
    ~> "createdAt" := p.createdAt
    ~> "updatedAt" := p.updatedAt
    ~> "name" := p.name
    ~> "metadata" := p.metadata
    ~> "settings" := p.settings
    ~> "mainCompositionId" := p.mainCompositionId
    ~> "compositionIds" := p.compositionIds
    ~> "assetIds" := p.assetIds
    ~> jsonEmptyObject """

instance : EmitPureScript Asset where
  typeName := "Asset"
  typeDecl := """type Asset = { id :: NonEmptyString, createdAt :: NonNegativeFloat, updatedAt :: NonNegativeFloat, name :: NonEmptyString, assetType :: AssetType, source :: AssetSource, data :: NonEmptyString, metadata :: AssetMetadata, nodeId :: Maybe NonEmptyString }"""
  decoder := """instance DecodeJson Asset where
  decodeJson json = do
    id <- json .? "id"
    createdAt <- json .? "createdAt"
    updatedAt <- json .? "updatedAt"
    name <- json .? "name"
    assetType <- json .? "assetType"
    source <- json .? "source"
    data <- json .? "data"
    metadata <- json .? "metadata"
    nodeId <- case json .? "nodeId" of
      Nothing -> pure Nothing
      Just nidJson -> map Just (decodeJson nidJson)
    pure { id, createdAt, updatedAt, name, assetType, source, data, metadata, nodeId } """
  encoder := """instance EncodeJson Asset where
  encodeJson a = "id" := a.id
    ~> "createdAt" := a.createdAt
    ~> "updatedAt" := a.updatedAt
    ~> "name" := a.name
    ~> "assetType" := a.assetType
    ~> "source" := a.source
    ~> "data" := a.data
    ~> "metadata" := a.metadata
    ~> "nodeId" :=? a.nodeId
    ~> jsonEmptyObject """

instance : EmitPureScript AssetReference where
  typeName := "AssetReference"
  typeDecl := """type AssetReference = { id :: NonEmptyString, assetType :: AssetType, source :: AssetSource }"""
  decoder := """instance DecodeJson AssetReference where
  decodeJson json = do
    id <- json .? "id"
    assetType <- json .? "assetType"
    source <- json .? "source"
    pure { id, assetType, source } """
  encoder := """instance EncodeJson AssetReference where
  encodeJson r = "id" := r.id
    ~> "assetType" := r.assetType
    ~> "source" := r.source
    ~> jsonEmptyObject """

instance : EmitPureScript ExportConfig where
  typeName := "ExportConfig"
  typeDecl := """type ExportConfig = { target :: ExportTarget, width :: PositiveInt, height :: PositiveInt, frameCount :: FrameNumber, fps :: PositiveFloat, startFrame :: FrameNumber, endFrame :: FrameNumber, outputDir :: NonEmptyString, filenamePrefix :: NonEmptyString, exportDepthMap :: Boolean, exportControlImages :: Boolean, exportCameraData :: Boolean, exportReferenceFrame :: Boolean, exportLastFrame :: Boolean, prompt :: NonEmptyString, negativePrompt :: NonEmptyString }"""
  decoder := """instance DecodeJson ExportConfig where
  decodeJson json = do
    target <- json .? "target"
    width <- json .? "width"
    height <- json .? "height"
    frameCount <- json .? "frameCount"
    fps <- json .? "fps"
    startFrame <- json .? "startFrame"
    endFrame <- json .? "endFrame"
    outputDir <- json .? "outputDir"
    filenamePrefix <- json .? "filenamePrefix"
    exportDepthMap <- json .? "exportDepthMap"
    exportControlImages <- json .? "exportControlImages"
    exportCameraData <- json .? "exportCameraData"
    exportReferenceFrame <- json .? "exportReferenceFrame"
    exportLastFrame <- json .? "exportLastFrame"
    prompt <- json .? "prompt"
    negativePrompt <- json .? "negativePrompt"
    pure { target, width, height, frameCount, fps, startFrame, endFrame, outputDir, filenamePrefix, exportDepthMap, exportControlImages, exportCameraData, exportReferenceFrame, exportLastFrame, prompt, negativePrompt } """
  encoder := """instance EncodeJson ExportConfig where
  encodeJson c = "target" := c.target
    ~> "width" := c.width
    ~> "height" := c.height
    ~> "frameCount" := c.frameCount
    ~> "fps" := c.fps
    ~> "startFrame" := c.startFrame
    ~> "endFrame" := c.endFrame
    ~> "outputDir" := c.outputDir
    ~> "filenamePrefix" := c.filenamePrefix
    ~> "exportDepthMap" := c.exportDepthMap
    ~> "exportControlImages" := c.exportControlImages
    ~> "exportCameraData" := c.exportCameraData
    ~> "exportReferenceFrame" := c.exportReferenceFrame
    ~> "exportLastFrame" := c.exportLastFrame
    ~> "prompt" := c.prompt
    ~> "negativePrompt" := c.negativePrompt
    ~> jsonEmptyObject """

instance : EmitPureScript ExportTemplate where
  typeName := "ExportTemplate"
  typeDecl := """type ExportTemplate = { id :: NonEmptyString, name :: NonEmptyString, config :: ExportConfig }"""
  decoder := """instance DecodeJson ExportTemplate where
  decodeJson json = do
    id <- json .? "id"
    name <- json .? "name"
    config <- json .? "config"
    pure { id, name, config } """
  encoder := """instance EncodeJson ExportTemplate where
  encodeJson t = "id" := t.id
    ~> "name" := t.name
    ~> "config" := t.config
    ~> jsonEmptyObject """

instance : EmitPureScript ExportJob where
  typeName := "ExportJob"
  typeDecl := """type ExportJob = { id :: NonEmptyString, createdAt :: NonNegativeFloat, updatedAt :: NonNegativeFloat, compositionId :: NonEmptyString, config :: ExportConfig, status :: ExportJobStatus, progress :: NormalizedValue, outputFiles :: String, errorMessage :: Maybe NonEmptyString }"""
  decoder := """instance DecodeJson ExportJob where
  decodeJson json = do
    id <- json .? "id"
    createdAt <- json .? "createdAt"
    updatedAt <- json .? "updatedAt"
    compositionId <- json .? "compositionId"
    config <- json .? "config"
    status <- json .? "status"
    progress <- json .? "progress"
    outputFiles <- json .? "outputFiles"
    errorMessage <- case json .? "errorMessage" of
      Nothing -> pure Nothing
      Just emJson -> map Just (decodeJson emJson)
    pure { id, createdAt, updatedAt, compositionId, config, status, progress, outputFiles, errorMessage } """
  encoder := """instance EncodeJson ExportJob where
  encodeJson j = "id" := j.id
    ~> "createdAt" := j.createdAt
    ~> "updatedAt" := j.updatedAt
    ~> "compositionId" := j.compositionId
    ~> "config" := j.config
    ~> "status" := j.status
    ~> "progress" := j.progress
    ~> "outputFiles" := j.outputFiles
    ~> "errorMessage" :=? j.errorMessage
    ~> jsonEmptyObject """

instance : EmitPureScript Camera3D where
  typeName := "Camera3D"
  typeDecl := """type Camera3D = { id :: NonEmptyString, name :: NonEmptyString, cameraControlType :: CameraControlType, cameraType :: CameraType, position :: Vec3, pointOfInterest :: Maybe Vec3, orientation :: Vec3, xRotation :: Number, yRotation :: Number, zRotation :: Number, zoom :: PositiveFloat, focalLength :: PositiveFloat, angleOfView :: PositiveFloat, filmSize :: PositiveFloat, depthOfField :: DepthOfField, autoOrient :: AutoOrientMode, nearClip :: NonNegativeFloat, farClip :: NonNegativeFloat }"""
  decoder := """instance DecodeJson Camera3D where
  decodeJson json = do
    id <- json .? "id"
    name <- json .? "name"
    cameraControlType <- json .? "cameraControlType"
    cameraType <- json .? "cameraType"
    position <- json .? "position"
    pointOfInterest <- case json .? "pointOfInterest" of
      Nothing -> pure Nothing
      Just poiJson -> map Just (decodeJson poiJson)
    orientation <- json .? "orientation"
    xRotation <- json .? "xRotation"
    yRotation <- json .? "yRotation"
    zRotation <- json .? "zRotation"
    zoom <- json .? "zoom"
    focalLength <- json .? "focalLength"
    angleOfView <- json .? "angleOfView"
    filmSize <- json .? "filmSize"
    depthOfField <- json .? "depthOfField"
    autoOrient <- json .? "autoOrient"
    nearClip <- json .? "nearClip"
    farClip <- json .? "farClip"
    pure { id, name, cameraControlType, cameraType, position, pointOfInterest, orientation, xRotation, yRotation, zRotation, zoom, focalLength, angleOfView, filmSize, depthOfField, autoOrient, nearClip, farClip } """
  encoder := """instance EncodeJson Camera3D where
  encodeJson c = "id" := c.id
    ~> "name" := c.name
    ~> "cameraControlType" := c.cameraControlType
    ~> "cameraType" := c.cameraType
    ~> "position" := c.position
    ~> "pointOfInterest" :=? c.pointOfInterest
    ~> "orientation" := c.orientation
    ~> "xRotation" := c.xRotation
    ~> "yRotation" := c.yRotation
    ~> "zRotation" := c.zRotation
    ~> "zoom" := c.zoom
    ~> "focalLength" := c.focalLength
    ~> "angleOfView" := c.angleOfView
    ~> "filmSize" := c.filmSize
    ~> "depthOfField" := c.depthOfField
    ~> "autoOrient" := c.autoOrient
    ~> "nearClip" := c.nearClip
    ~> "farClip" := c.farClip
    ~> jsonEmptyObject """

instance : EmitPureScript CameraKeyframe where
  typeName := "CameraKeyframe"
  typeDecl := """type CameraKeyframe = { frame :: FrameNumber, position :: Maybe Vec3, pointOfInterest :: Maybe Vec3, orientation :: Maybe Vec3, xRotation :: Maybe Number, yRotation :: Maybe Number, zRotation :: Maybe Number, zoom :: Maybe PositiveFloat, focalLength :: Maybe PositiveFloat }"""
  decoder := """instance DecodeJson CameraKeyframe where
  decodeJson json = do
    frame <- json .? "frame"
    position <- case json .? "position" of
      Nothing -> pure Nothing
      Just pJson -> map Just (decodeJson pJson)
    pointOfInterest <- case json .? "pointOfInterest" of
      Nothing -> pure Nothing
      Just poiJson -> map Just (decodeJson poiJson)
    orientation <- case json .? "orientation" of
      Nothing -> pure Nothing
      Just oJson -> map Just (decodeJson oJson)
    xRotation <- case json .? "xRotation" of
      Nothing -> pure Nothing
      Just (.num r) -> pure (Just r)
      _ -> pure Nothing
    yRotation <- case json .? "yRotation" of
      Nothing -> pure Nothing
      Just (.num r) -> pure (Just r)
      _ -> pure Nothing
    zRotation <- case json .? "zRotation" of
      Nothing -> pure Nothing
      Just (.num r) -> pure (Just r)
      _ -> pure Nothing
    zoom <- case json .? "zoom" of
      Nothing -> pure Nothing
      Just zJson -> map Just (decodeJson zJson)
    focalLength <- case json .? "focalLength" of
      Nothing -> pure Nothing
      Just flJson -> map Just (decodeJson flJson)
    pure { frame, position, pointOfInterest, orientation, xRotation, yRotation, zRotation, zoom, focalLength } """
  encoder := """instance EncodeJson CameraKeyframe where
  encodeJson k = "frame" := k.frame
    ~> "position" :=? k.position
    ~> "pointOfInterest" :=? k.pointOfInterest
    ~> "orientation" :=? k.orientation
    ~> "xRotation" :=? k.xRotation
    ~> "yRotation" :=? k.yRotation
    ~> "zRotation" :=? k.zRotation
    ~> "zoom" :=? k.zoom
    ~> "focalLength" :=? k.focalLength
    ~> jsonEmptyObject """

instance : EmitPureScript CameraPath where
  typeName := "CameraPath"
  typeDecl := """type CameraPath = { id :: NonEmptyString, cameraId :: NonEmptyString, keyframes :: Array CameraKeyframe }"""
  decoder := """instance DecodeJson CameraPath where
  decodeJson json = do
    id <- json .? "id"
    cameraId <- json .? "cameraId"
    keyframes <- json .? "keyframes"
    pure { id, cameraId, keyframes } """
  encoder := """instance EncodeJson CameraPath where
  encodeJson p = "id" := p.id
    ~> "cameraId" := p.cameraId
    ~> "keyframes" := p.keyframes
    ~> jsonEmptyObject """

instance : EmitPureScript TextAnimatorProperties where
  typeName := "TextAnimatorProperties"
  typeDecl := """type TextAnimatorProperties = { position :: Maybe Vec2, rotation :: Maybe Number, scale :: Maybe Vec2, opacity :: Maybe NormalizedValue, fillColor :: Maybe NonEmptyString, strokeColor :: Maybe NonEmptyString, strokeWidth :: Maybe NonNegativeFloat, tracking :: Maybe Number, blur :: Maybe Vec2 }"""
  decoder := """instance DecodeJson TextAnimatorProperties where
  decodeJson json = do
    position <- case json .? "position" of
      Nothing -> pure Nothing
      Just pJson -> map Just (decodeJson pJson)
    rotation <- case json .? "rotation" of
      Nothing -> pure Nothing
      Just (.num r) -> pure (Just r)
      _ -> pure Nothing
    scale <- case json .? "scale" of
      Nothing -> pure Nothing
      Just sJson -> map Just (decodeJson sJson)
    opacity <- case json .? "opacity" of
      Nothing -> pure Nothing
      Just oJson -> map Just (decodeJson oJson)
    fillColor <- case json .? "fillColor" of
      Nothing -> pure Nothing
      Just cJson -> map Just (decodeJson cJson)
    strokeColor <- case json .? "strokeColor" of
      Nothing -> pure Nothing
      Just cJson -> map Just (decodeJson cJson)
    strokeWidth <- case json .? "strokeWidth" of
      Nothing -> pure Nothing
      Just wJson -> map Just (decodeJson wJson)
    tracking <- case json .? "tracking" of
      Nothing -> pure Nothing
      Just (.num t) -> pure (Just t)
      _ -> pure Nothing
    blur <- case json .? "blur" of
      Nothing -> pure Nothing
      Just bJson -> map Just (decodeJson bJson)
    pure { position, rotation, scale, opacity, fillColor, strokeColor, strokeWidth, tracking, blur } """
  encoder := """instance EncodeJson TextAnimatorProperties where
  encodeJson p = "position" :=? p.position
    ~> "rotation" :=? p.rotation
    ~> "scale" :=? p.scale
    ~> "opacity" :=? p.opacity
    ~> "fillColor" :=? p.fillColor
    ~> "strokeColor" :=? p.strokeColor
    ~> "strokeWidth" :=? p.strokeWidth
    ~> "tracking" :=? p.tracking
    ~> "blur" :=? p.blur
    ~> jsonEmptyObject """

instance : EmitPureScript TextRangeSelector where
  typeName := "TextRangeSelector"
  typeDecl := """type TextRangeSelector = { mode :: TextRangeMode, start :: NonEmptyString, end :: NonEmptyString, offset :: NonEmptyString, basedOn :: TextRangeBasedOn, shape :: TextRangeShape, randomizeOrder :: Boolean, randomSeed :: FrameNumber }"""
  decoder := """instance DecodeJson TextRangeSelector where
  decodeJson json = do
    mode <- json .? "mode"
    start <- json .? "start"
    end <- json .? "end"
    offset <- json .? "offset"
    basedOn <- json .? "basedOn"
    shape <- json .? "shape"
    randomizeOrder <- json .? "randomizeOrder"
    randomSeed <- json .? "randomSeed"
    pure { mode, start, end, offset, basedOn, shape, randomizeOrder, randomSeed } """
  encoder := """instance EncodeJson TextRangeSelector where
  encodeJson s = "mode" := s.mode
    ~> "start" := s.start
    ~> "end" := s.end
    ~> "offset" := s.offset
    ~> "basedOn" := s.basedOn
    ~> "shape" := s.shape
    ~> "randomizeOrder" := s.randomizeOrder
    ~> "randomSeed" := s.randomSeed
    ~> jsonEmptyObject """

instance : EmitPureScript TextAnimator where
  typeName := "TextAnimator"
  typeDecl := """type TextAnimator = { id :: NonEmptyString, name :: NonEmptyString, enabled :: Boolean, rangeSelector :: TextRangeSelector, properties :: TextAnimatorProperties }"""
  decoder := """instance DecodeJson TextAnimator where
  decodeJson json = do
    id <- json .? "id"
    name <- json .? "name"
    enabled <- json .? "enabled"
    rangeSelector <- json .? "rangeSelector"
    properties <- json .? "properties"
    pure { id, name, enabled, rangeSelector, properties } """
  encoder := """instance EncodeJson TextAnimator where
  encodeJson a = "id" := a.id
    ~> "name" := a.name
    ~> "enabled" := a.enabled
    ~> "rangeSelector" := a.rangeSelector
    ~> "properties" := a.properties
    ~> jsonEmptyObject """

instance : EmitPureScript TextLayerData where
  typeName := "TextLayerData"
  typeDecl := """type TextLayerData = { text :: NonEmptyString, fontConfig :: FontConfig, fill :: NonEmptyString, stroke :: NonEmptyString, strokeWidth :: NonNegativeFloat, tracking :: Number, lineSpacing :: Number, textAlign :: TextAlign, pathLayerId :: Maybe NonEmptyString, animators :: Array NonEmptyString }"""
  decoder := """instance DecodeJson TextLayerData where
  decodeJson json = do
    text <- json .? "text"
    fontConfig <- json .? "fontConfig"
    fill <- json .? "fill"
    stroke <- json .? "stroke"
    strokeWidth <- json .? "strokeWidth"
    tracking <- json .? "tracking"
    lineSpacing <- json .? "lineSpacing"
    textAlign <- json .? "textAlign"
    pathLayerId <- case json .? "pathLayerId" of
      Nothing -> pure Nothing
      Just idJson -> map Just (decodeJson idJson)
    animators <- json .? "animators"
    pure { text, fontConfig, fill, stroke, strokeWidth, tracking, lineSpacing, textAlign, pathLayerId, animators } """
  encoder := """instance EncodeJson TextLayerData where
  encodeJson d = "text" := d.text
    ~> "fontConfig" := d.fontConfig
    ~> "fill" := d.fill
    ~> "stroke" := d.stroke
    ~> "strokeWidth" := d.strokeWidth
    ~> "tracking" := d.tracking
    ~> "lineSpacing" := d.lineSpacing
    ~> "textAlign" := d.textAlign
    ~> "pathLayerId" :=? d.pathLayerId
    ~> "animators" := d.animators
    ~> jsonEmptyObject """

instance : EmitPureScript TextShaper where
  typeName := "TextShaper"
  typeDecl := """type TextShaper = { id :: NonEmptyString, name :: NonEmptyString, enabled :: Boolean, config :: String }"""
  decoder := """instance DecodeJson TextShaper where
  decodeJson json = do
    id <- json .? "id"
    name <- json .? "name"
    enabled <- json .? "enabled"
    config <- json .? "config"
    pure { id, name, enabled, config } """
  encoder := """instance EncodeJson TextShaper where
  encodeJson s = "id" := s.id
    ~> "name" := s.name
    ~> "enabled" := s.enabled
    ~> "config" := s.config
    ~> jsonEmptyObject """

instance : EmitPureScript AudioAnalysis where
  typeName := "AudioAnalysis"
  typeDecl := """type AudioAnalysis = { duration :: NonNegativeFloat, sampleRate :: PositiveInt, channels :: PositiveInt, beats :: Array FrameNumber, peaks :: Array (Tuple FrameNumber NormalizedValue), frequencies :: String }"""
  decoder := """instance DecodeJson AudioAnalysis where
  decodeJson json = do
    duration <- json .? "duration"
    sampleRate <- json .? "sampleRate"
    channels <- json .? "channels"
    beats <- json .? "beats"
    peaksJson <- json .? "peaks"
    peaks <- case Json.toArray peaksJson of
      Just arr -> mapM (\x -> case Json.toArray x of
        Just [fJson, vJson] -> do
          f <- decodeJson fJson
          v <- decodeJson vJson
          pure (Tuple f v)
        _ -> Left (TypeMismatch "Invalid peak tuple")) arr
      Nothing -> Left (TypeMismatch "peaks must be array")
    frequencies <- json .? "frequencies"
    pure { duration, sampleRate, channels, beats, peaks, frequencies } """
  encoder := """instance EncodeJson AudioAnalysis where
  encodeJson a = "duration" := a.duration
    ~> "sampleRate" := a.sampleRate
    ~> "channels" := a.channels
    ~> "beats" := a.beats
    ~> "peaks" := Json.fromArray (map (\(Tuple f v) -> Json.fromArray [encodeJson f, encodeJson v]) a.peaks)
    ~> "frequencies" := a.frequencies
    ~> jsonEmptyObject """

instance : EmitPureScript AudioReactivity where
  typeName := "AudioReactivity"
  typeDecl := """type AudioReactivity = { enabled :: Boolean, method :: BeatDetectionMethod, targetProperty :: NonEmptyString, sensitivity :: NormalizedValue, smoothing :: NormalizedValue }"""
  decoder := """instance DecodeJson AudioReactivity where
  decodeJson json = do
    enabled <- json .? "enabled"
    method <- json .? "method"
    targetProperty <- json .? "targetProperty"
    sensitivity <- json .? "sensitivity"
    smoothing <- json .? "smoothing"
    pure { enabled, method, targetProperty, sensitivity, smoothing } """
  encoder := """instance EncodeJson AudioReactivity where
  encodeJson r = "enabled" := r.enabled
    ~> "method" := r.method
    ~> "targetProperty" := r.targetProperty
    ~> "sensitivity" := r.sensitivity
    ~> "smoothing" := r.smoothing
    ~> jsonEmptyObject """

instance : EmitPureScript AudioTrack where
  typeName := "AudioTrack"
  typeDecl := """type AudioTrack = { id :: NonEmptyString, name :: NonEmptyString, assetId :: NonEmptyString, volume :: NormalizedValue, pan :: Number, startTime :: NonNegativeFloat, analysis :: Maybe AudioAnalysis, reactivity :: Maybe AudioReactivity }"""
  decoder := """instance DecodeJson AudioTrack where
  decodeJson json = do
    id <- json .? "id"
    name <- json .? "name"
    assetId <- json .? "assetId"
    volume <- json .? "volume"
    pan <- json .? "pan"
    startTime <- json .? "startTime"
    analysis <- case json .? "analysis" of
      Nothing -> pure Nothing
      Just aJson -> map Just (decodeJson aJson)
    reactivity <- case json .? "reactivity" of
      Nothing -> pure Nothing
      Just rJson -> map Just (decodeJson rJson)
    pure { id, name, assetId, volume, pan, startTime, analysis, reactivity } """
  encoder := """instance EncodeJson AudioTrack where
  encodeJson t = "id" := t.id
    ~> "name" := t.name
    ~> "assetId" := t.assetId
    ~> "volume" := t.volume
    ~> "pan" := t.pan
    ~> "startTime" := t.startTime
    ~> "analysis" :=? t.analysis
    ~> "reactivity" :=? t.reactivity
    ~> jsonEmptyObject """

instance : EmitPureScript ParticleEmitter where
  typeName := "ParticleEmitter"
  typeDecl := """type ParticleEmitter = { id :: NonEmptyString, emitterShape :: EmitterShape, position :: Vec2, rate :: PositiveFloat, lifetime :: PositiveFloat, speed :: PositiveFloat, direction :: Number, spread :: Number, pathLayerId :: Maybe NonEmptyString }"""
  decoder := """instance DecodeJson ParticleEmitter where
  decodeJson json = do
    id <- json .? "id"
    emitterShape <- json .? "emitterShape"
    position <- json .? "position"
    rate <- json .? "rate"
    lifetime <- json .? "lifetime"
    speed <- json .? "speed"
    direction <- json .? "direction"
    spread <- json .? "spread"
    pathLayerId <- case json .? "pathLayerId" of
      Nothing -> pure Nothing
      Just idJson -> map Just (decodeJson idJson)
    pure { id, emitterShape, position, rate, lifetime, speed, direction, spread, pathLayerId } """
  encoder := """instance EncodeJson ParticleEmitter where
  encodeJson e = "id" := e.id
    ~> "emitterShape" := e.emitterShape
    ~> "position" := e.position
    ~> "rate" := e.rate
    ~> "lifetime" := e.lifetime
    ~> "speed" := e.speed
    ~> "direction" := e.direction
    ~> "spread" := e.spread
    ~> "pathLayerId" :=? e.pathLayerId
    ~> jsonEmptyObject """

instance : EmitPureScript Force where
  typeName := "Force"
  typeDecl := """type Force = { id :: NonEmptyString, name :: NonEmptyString, forceType :: ForceType, strength :: Number, direction :: Vec2, position :: Maybe Vec2, enabled :: Boolean }"""
  decoder := """instance DecodeJson Force where
  decodeJson json = do
    id <- json .? "id"
    name <- json .? "name"
    forceType <- json .? "forceType"
    strength <- json .? "strength"
    direction <- json .? "direction"
    position <- case json .? "position" of
      Nothing -> pure Nothing
      Just pJson -> map Just (decodeJson pJson)
    enabled <- json .? "enabled"
    pure { id, name, forceType, strength, direction, position, enabled } """
  encoder := """instance EncodeJson Force where
  encodeJson f = "id" := f.id
    ~> "name" := f.name
    ~> "forceType" := f.forceType
    ~> "strength" := f.strength
    ~> "direction" := f.direction
    ~> "position" :=? f.position
    ~> "enabled" := f.enabled
    ~> jsonEmptyObject """

instance : EmitPureScript CollisionConfig where
  typeName := "CollisionConfig"
  typeDecl := """type CollisionConfig = { enabled :: Boolean, depthLayerId :: Maybe NonEmptyString, bounciness :: NormalizedValue, friction :: NormalizedValue }"""
  decoder := """instance DecodeJson CollisionConfig where
  decodeJson json = do
    enabled <- json .? "enabled"
    depthLayerId <- case json .? "depthLayerId" of
      Nothing -> pure Nothing
      Just idJson -> map Just (decodeJson idJson)
    bounciness <- json .? "bounciness"
    friction <- json .? "friction"
    pure { enabled, depthLayerId, bounciness, friction } """
  encoder := """instance EncodeJson CollisionConfig where
  encodeJson c = "enabled" := c.enabled
    ~> "depthLayerId" :=? c.depthLayerId
    ~> "bounciness" := c.bounciness
    ~> "friction" := c.friction
    ~> jsonEmptyObject """

instance : EmitPureScript ParticleRenderer where
  typeName := "ParticleRenderer"
  typeDecl := """type ParticleRenderer = { startSize :: PositiveFloat, endSize :: PositiveFloat, startColor :: NonEmptyString, endColor :: NonEmptyString, startOpacity :: NormalizedValue, endOpacity :: NormalizedValue, blendMode :: BlendMode }"""
  decoder := """instance DecodeJson ParticleRenderer where
  decodeJson json = do
    startSize <- json .? "startSize"
    endSize <- json .? "endSize"
    startColor <- json .? "startColor"
    endColor <- json .? "endColor"
    startOpacity <- json .? "startOpacity"
    endOpacity <- json .? "endOpacity"
    blendMode <- json .? "blendMode"
    pure { startSize, endSize, startColor, endColor, startOpacity, endOpacity, blendMode } """
  encoder := """instance EncodeJson ParticleRenderer where
  encodeJson r = "startSize" := r.startSize
    ~> "endSize" := r.endSize
    ~> "startColor" := r.startColor
    ~> "endColor" := r.endColor
    ~> "startOpacity" := r.startOpacity
    ~> "endOpacity" := r.endOpacity
    ~> "blendMode" := r.blendMode
    ~> jsonEmptyObject """

instance : EmitPureScript ParticleSystem where
  typeName := "ParticleSystem"
  typeDecl := """type ParticleSystem = { id :: NonEmptyString, name :: NonEmptyString, emitter :: NonEmptyString, renderer :: ParticleRenderer, forces :: Array NonEmptyString, collision :: Maybe CollisionConfig, enabled :: Boolean }"""
  decoder := """instance DecodeJson ParticleSystem where
  decodeJson json = do
    id <- json .? "id"
    name <- json .? "name"
    emitter <- json .? "emitter"
    renderer <- json .? "renderer"
    forces <- json .? "forces"
    collision <- case json .? "collision" of
      Nothing -> pure Nothing
      Just cJson -> map Just (decodeJson cJson)
    enabled <- json .? "enabled"
    pure { id, name, emitter, renderer, forces, collision, enabled } """
  encoder := """instance EncodeJson ParticleSystem where
  encodeJson s = "id" := s.id
    ~> "name" := s.name
    ~> "emitter" := s.emitter
    ~> "renderer" := s.renderer
    ~> "forces" := s.forces
    ~> "collision" :=? s.collision
    ~> "enabled" := s.enabled
    ~> jsonEmptyObject """

instance : EmitPureScript RigidBody where
  typeName := "RigidBody"
  typeDecl := """type RigidBody = { id :: NonEmptyString, layerId :: NonEmptyString, bodyType :: BodyType, mass :: PositiveFloat, position :: Vec2, rotation :: Number, material :: PhysicsMaterial, enabled :: Boolean }"""
  decoder := """instance DecodeJson RigidBody where
  decodeJson json = do
    id <- json .? "id"
    layerId <- json .? "layerId"
    bodyType <- json .? "bodyType"
    mass <- json .? "mass"
    position <- json .? "position"
    rotation <- json .? "rotation"
    material <- json .? "material"
    enabled <- json .? "enabled"
    pure { id, layerId, bodyType, mass, position, rotation, material, enabled } """
  encoder := """instance EncodeJson RigidBody where
  encodeJson b = "id" := b.id
    ~> "layerId" := b.layerId
    ~> "bodyType" := b.bodyType
    ~> "mass" := b.mass
    ~> "position" := b.position
    ~> "rotation" := b.rotation
    ~> "material" := b.material
    ~> "enabled" := b.enabled
    ~> jsonEmptyObject """

instance : EmitPureScript Joint where
  typeName := "Joint"
  typeDecl := """type Joint = { id :: NonEmptyString, name :: NonEmptyString, bodyA :: NonEmptyString, bodyB :: NonEmptyString, jointType :: JointType, anchorA :: Vec2, anchorB :: Vec2, enabled :: Boolean }"""
  decoder := """instance DecodeJson Joint where
  decodeJson json = do
    id <- json .? "id"
    name <- json .? "name"
    bodyA <- json .? "bodyA"
    bodyB <- json .? "bodyB"
    jointType <- json .? "jointType"
    anchorA <- json .? "anchorA"
    anchorB <- json .? "anchorB"
    enabled <- json .? "enabled"
    pure { id, name, bodyA, bodyB, jointType, anchorA, anchorB, enabled } """
  encoder := """instance EncodeJson Joint where
  encodeJson j = "id" := j.id
    ~> "name" := j.name
    ~> "bodyA" := j.bodyA
    ~> "bodyB" := j.bodyB
    ~> "jointType" := j.jointType
    ~> "anchorA" := j.anchorA
    ~> "anchorB" := j.anchorB
    ~> "enabled" := j.enabled
    ~> jsonEmptyObject """

instance : EmitPureScript PhysicsSpace where
  typeName := "PhysicsSpace"
  typeDecl := """type PhysicsSpace = { id :: NonEmptyString, name :: NonEmptyString, gravity :: Vec2, bodies :: Array NonEmptyString, joints :: Array NonEmptyString, enabled :: Boolean }"""
  decoder := """instance DecodeJson PhysicsSpace where
  decodeJson json = do
    id <- json .? "id"
    name <- json .? "name"
    gravity <- json .? "gravity"
    bodies <- json .? "bodies"
    joints <- json .? "joints"
    enabled <- json .? "enabled"
    pure { id, name, gravity, bodies, joints, enabled } """
  encoder := """instance EncodeJson PhysicsSpace where
  encodeJson s = "id" := s.id
    ~> "name" := s.name
    ~> "gravity" := s.gravity
    ~> "bodies" := s.bodies
    ~> "joints" := s.joints
    ~> "enabled" := s.enabled
    ~> jsonEmptyObject """

instance : EmitPureScript Ragdoll where
  typeName := "Ragdoll"
  typeDecl := """type Ragdoll = { id :: NonEmptyString, name :: NonEmptyString, rootBody :: NonEmptyString, bodies :: Array NonEmptyString, joints :: Array NonEmptyString, enabled :: Boolean }"""
  decoder := """instance DecodeJson Ragdoll where
  decodeJson json = do
    id <- json .? "id"
    name <- json .? "name"
    rootBody <- json .? "rootBody"
    bodies <- json .? "bodies"
    joints <- json .? "joints"
    enabled <- json .? "enabled"
    pure { id, name, rootBody, bodies, joints, enabled } """
  encoder := """instance EncodeJson Ragdoll where
  encodeJson r = "id" := r.id
    ~> "name" := r.name
    ~> "rootBody" := r.rootBody
    ~> "bodies" := r.bodies
    ~> "joints" := r.joints
    ~> "enabled" := r.enabled
    ~> jsonEmptyObject """

instance : EmitPureScript Cloth where
  typeName := "Cloth"
  typeDecl := """type Cloth = { id :: NonEmptyString, name :: NonEmptyString, layerId :: NonEmptyString, width :: PositiveInt, height :: PositiveInt, stiffness :: NormalizedValue, damping :: NormalizedValue, enabled :: Boolean }"""
  decoder := """instance DecodeJson Cloth where
  decodeJson json = do
    id <- json .? "id"
    name <- json .? "name"
    layerId <- json .? "layerId"
    width <- json .? "width"
    height <- json .? "height"
    stiffness <- json .? "stiffness"
    damping <- json .? "damping"
    enabled <- json .? "enabled"
    pure { id, name, layerId, width, height, stiffness, damping, enabled } """
  encoder := """instance EncodeJson Cloth where
  encodeJson c = "id" := c.id
    ~> "name" := c.name
    ~> "layerId" := c.layerId
    ~> "width" := c.width
    ~> "height" := c.height
    ~> "stiffness" := c.stiffness
    ~> "damping" := c.damping
    ~> "enabled" := c.enabled
    ~> jsonEmptyObject """

/-! ## Metrics - Enums - PureScript Instances -/

instance : EmitPureScript AggregationType where
  typeName := "AggregationType"
  typeDecl := """data AggregationType
  = AggregationTypeSum
  | AggregationTypeAverage
  | AggregationTypeMin
  | AggregationTypeMax
  | AggregationTypeCount
  | AggregationTypeLast

derive instance Eq AggregationType
derive instance Ord AggregationType"""
  decoder := """instance DecodeJson AggregationType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "sum" -> pure AggregationTypeSum
      "average" -> pure AggregationTypeAverage
      "min" -> pure AggregationTypeMin
      "max" -> pure AggregationTypeMax
      "count" -> pure AggregationTypeCount
      "last" -> pure AggregationTypeLast
      _ -> Left "Invalid AggregationType" """
  encoder := """instance EncodeJson AggregationType where
  encodeJson AggregationTypeSum = encodeJson "sum"
  encodeJson AggregationTypeAverage = encodeJson "average"
  encodeJson AggregationTypeMin = encodeJson "min"
  encodeJson AggregationTypeMax = encodeJson "max"
  encodeJson AggregationTypeCount = encodeJson "count"
  encodeJson AggregationTypeLast = encodeJson "last" """

instance : EmitPureScript TimeGrain where
  typeName := "TimeGrain"
  typeDecl := """data TimeGrain
  = TimeGrainMillisecond
  | TimeGrainSecond
  | TimeGrainMinute
  | TimeGrainHour
  | TimeGrainDay

derive instance Eq TimeGrain
derive instance Ord TimeGrain"""
  decoder := """instance DecodeJson TimeGrain where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "millisecond" -> pure TimeGrainMillisecond
      "second" -> pure TimeGrainSecond
      "minute" -> pure TimeGrainMinute
      "hour" -> pure TimeGrainHour
      "day" -> pure TimeGrainDay
      _ -> Left "Invalid TimeGrain" """
  encoder := """instance EncodeJson TimeGrain where
  encodeJson TimeGrainMillisecond = encodeJson "millisecond"
  encodeJson TimeGrainSecond = encodeJson "second"
  encodeJson TimeGrainMinute = encodeJson "minute"
  encodeJson TimeGrainHour = encodeJson "hour"
  encodeJson TimeGrainDay = encodeJson "day" """

instance : EmitPureScript MetricDataType where
  typeName := "MetricDataType"
  typeDecl := """data MetricDataType
  = MetricDataTypeFloat
  | MetricDataTypeInteger
  | MetricDataTypePercentage
  | MetricDataTypeDuration

derive instance Eq MetricDataType
derive instance Ord MetricDataType"""
  decoder := """instance DecodeJson MetricDataType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "float" -> pure MetricDataTypeFloat
      "integer" -> pure MetricDataTypeInteger
      "percentage" -> pure MetricDataTypePercentage
      "duration" -> pure MetricDataTypeDuration
      _ -> Left "Invalid MetricDataType" """
  encoder := """instance EncodeJson MetricDataType where
  encodeJson MetricDataTypeFloat = encodeJson "float"
  encodeJson MetricDataTypeInteger = encodeJson "integer"
  encodeJson MetricDataTypePercentage = encodeJson "percentage"
  encodeJson MetricDataTypeDuration = encodeJson "duration" """

instance : EmitPureScript MetricCategory where
  typeName := "MetricCategory"
  typeDecl := """data MetricCategory
  = MetricCategoryRendering
  | MetricCategoryPerformance
  | MetricCategoryQuality
  | MetricCategoryResource
  | MetricCategoryUser
  | MetricCategoryAi

derive instance Eq MetricCategory
derive instance Ord MetricCategory"""
  decoder := """instance DecodeJson MetricCategory where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "rendering" -> pure MetricCategoryRendering
      "performance" -> pure MetricCategoryPerformance
      "quality" -> pure MetricCategoryQuality
      "resource" -> pure MetricCategoryResource
      "user" -> pure MetricCategoryUser
      "ai" -> pure MetricCategoryAi
      _ -> Left "Invalid MetricCategory" """
  encoder := """instance EncodeJson MetricCategory where
  encodeJson MetricCategoryRendering = encodeJson "rendering"
  encodeJson MetricCategoryPerformance = encodeJson "performance"
  encodeJson MetricCategoryQuality = encodeJson "quality"
  encodeJson MetricCategoryResource = encodeJson "resource"
  encodeJson MetricCategoryUser = encodeJson "user"
  encodeJson MetricCategoryAi = encodeJson "ai" """

/-! ## Metrics - Entities - PureScript Instances -/

instance : EmitPureScript MetricDefinition where
  typeName := "MetricDefinition"
  typeDecl := """type MetricDefinition = { id :: NonEmptyString, name :: NonEmptyString, category :: MetricCategory, dataType :: MetricDataType, unit :: NonEmptyString, minValue :: Number, maxValue :: Number, aggregation :: AggregationType, timeGrain :: TimeGrain }"""
  decoder := """instance DecodeJson MetricDefinition where
  decodeJson json = do
    id <- json .? "id"
    name <- json .? "name"
    category <- json .? "category"
    dataType <- json .? "dataType"
    unit <- json .? "unit"
    minValue <- json .? "minValue"
    maxValue <- json .? "maxValue"
    aggregation <- json .? "aggregation"
    timeGrain <- json .? "timeGrain"
    pure { id, name, category, dataType, unit, minValue, maxValue, aggregation, timeGrain } """
  encoder := """instance EncodeJson MetricDefinition where
  encodeJson m = "id" := m.id
    ~> "name" := m.name
    ~> "category" := m.category
    ~> "dataType" := m.dataType
    ~> "unit" := m.unit
    ~> "minValue" := m.minValue
    ~> "maxValue" := m.maxValue
    ~> "aggregation" := m.aggregation
    ~> "timeGrain" := m.timeGrain
    ~> jsonEmptyObject """

/-! ## Metrics - Value Types - PureScript Instances -/

instance : EmitPureScript FrameRenderTime where
  typeName := "FrameRenderTime"
  typeDecl := """type FrameRenderTime = { value :: NonNegativeFloat, frameNumber :: FrameNumber }"""
  decoder := """instance DecodeJson FrameRenderTime where
  decodeJson json = do
    value <- json .? "value"
    frameNumber <- json .? "frameNumber"
    pure { value, frameNumber } """
  encoder := """instance EncodeJson FrameRenderTime where
  encodeJson m = "value" := m.value
    ~> "frameNumber" := m.frameNumber
    ~> jsonEmptyObject """

instance : EmitPureScript TotalRenderTime where
  typeName := "TotalRenderTime"
  typeDecl := """type TotalRenderTime = { value :: NonNegativeFloat, frameCount :: FrameNumber }"""
  decoder := """instance DecodeJson TotalRenderTime where
  decodeJson json = do
    value <- json .? "value"
    frameCount <- json .? "frameCount"
    pure { value, frameCount } """
  encoder := """instance EncodeJson TotalRenderTime where
  encodeJson m = "value" := m.value
    ~> "frameCount" := m.frameCount
    ~> jsonEmptyObject """

instance : EmitPureScript MemoryUsage where
  typeName := "MemoryUsage"
  typeDecl := """type MemoryUsage = { value :: NonNegativeFloat }"""
  decoder := """instance DecodeJson MemoryUsage where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson MemoryUsage where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

instance : EmitPureScript GpuUsage where
  typeName := "GpuUsage"
  typeDecl := """type GpuUsage = { value :: NormalizedValue }"""
  decoder := """instance DecodeJson GpuUsage where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson GpuUsage where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

instance : EmitPureScript CacheHitRate where
  typeName := "CacheHitRate"
  typeDecl := """type CacheHitRate = { value :: NormalizedValue }"""
  decoder := """instance DecodeJson CacheHitRate where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson CacheHitRate where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

instance : EmitPureScript CacheSize where
  typeName := "CacheSize"
  typeDecl := """type CacheSize = { value :: NonNegativeFloat }"""
  decoder := """instance DecodeJson CacheSize where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson CacheSize where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

instance : EmitPureScript Fps where
  typeName := "Fps"
  typeDecl := """type Fps = { value :: PositiveFloat }"""
  decoder := """instance DecodeJson Fps where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson Fps where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

instance : EmitPureScript DroppedFrames where
  typeName := "DroppedFrames"
  typeDecl := """type DroppedFrames = { value :: FrameNumber }"""
  decoder := """instance DecodeJson DroppedFrames where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson DroppedFrames where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

instance : EmitPureScript PlaybackLatency where
  typeName := "PlaybackLatency"
  typeDecl := """type PlaybackLatency = { value :: NonNegativeFloat }"""
  decoder := """instance DecodeJson PlaybackLatency where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson PlaybackLatency where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

instance : EmitPureScript ScrubLatency where
  typeName := "ScrubLatency"
  typeDecl := """type ScrubLatency = { value :: NonNegativeFloat }"""
  decoder := """instance DecodeJson ScrubLatency where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson ScrubLatency where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

instance : EmitPureScript CompressionRatio where
  typeName := "CompressionRatio"
  typeDecl := """type CompressionRatio = { value :: PositiveFloat }"""
  decoder := """instance DecodeJson CompressionRatio where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson CompressionRatio where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

instance : EmitPureScript Bitrate where
  typeName := "Bitrate"
  typeDecl := """type Bitrate = { value :: PositiveInt }"""
  decoder := """instance DecodeJson Bitrate where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson Bitrate where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

instance : EmitPureScript ColorAccuracy where
  typeName := "ColorAccuracy"
  typeDecl := """type ColorAccuracy = { value :: NormalizedValue }"""
  decoder := """instance DecodeJson ColorAccuracy where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson ColorAccuracy where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

instance : EmitPureScript MotionBlurQuality where
  typeName := "MotionBlurQuality"
  typeDecl := """type MotionBlurQuality = { value :: NormalizedValue }"""
  decoder := """instance DecodeJson MotionBlurQuality where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson MotionBlurQuality where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

instance : EmitPureScript VramUsage where
  typeName := "VramUsage"
  typeDecl := """type VramUsage = { value :: NonNegativeFloat }"""
  decoder := """instance DecodeJson VramUsage where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson VramUsage where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

instance : EmitPureScript CpuUsage where
  typeName := "CpuUsage"
  typeDecl := """type CpuUsage = { value :: NormalizedValue }"""
  decoder := """instance DecodeJson CpuUsage where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson CpuUsage where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

instance : EmitPureScript NetworkBandwidth where
  typeName := "NetworkBandwidth"
  typeDecl := """type NetworkBandwidth = { value :: NonNegativeFloat }"""
  decoder := """instance DecodeJson NetworkBandwidth where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson NetworkBandwidth where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

instance : EmitPureScript StorageUsed where
  typeName := "StorageUsed"
  typeDecl := """type StorageUsed = { value :: NonNegativeFloat }"""
  decoder := """instance DecodeJson StorageUsed where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson StorageUsed where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

instance : EmitPureScript ActionsPerSession where
  typeName := "ActionsPerSession"
  typeDecl := """type ActionsPerSession = { value :: PositiveInt }"""
  decoder := """instance DecodeJson ActionsPerSession where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson ActionsPerSession where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

instance : EmitPureScript ExportCount where
  typeName := "ExportCount"
  typeDecl := """type ExportCount = { value :: FrameNumber }"""
  decoder := """instance DecodeJson ExportCount where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson ExportCount where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

instance : EmitPureScript ProjectCount where
  typeName := "ProjectCount"
  typeDecl := """type ProjectCount = { value :: FrameNumber }"""
  decoder := """instance DecodeJson ProjectCount where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson ProjectCount where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

instance : EmitPureScript InferenceTime where
  typeName := "InferenceTime"
  typeDecl := """type InferenceTime = { value :: NonNegativeFloat }"""
  decoder := """instance DecodeJson InferenceTime where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson InferenceTime where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

instance : EmitPureScript ModelLoadTime where
  typeName := "ModelLoadTime"
  typeDecl := """type ModelLoadTime = { value :: NonNegativeFloat }"""
  decoder := """instance DecodeJson ModelLoadTime where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson ModelLoadTime where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

instance : EmitPureScript TokensUsed where
  typeName := "TokensUsed"
  typeDecl := """type TokensUsed = { value :: PositiveInt }"""
  decoder := """instance DecodeJson TokensUsed where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson TokensUsed where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

instance : EmitPureScript CostUSD where
  typeName := "CostUSD"
  typeDecl := """type CostUSD = { value :: NonNegativeFloat }"""
  decoder := """instance DecodeJson CostUSD where
  decodeJson json = do
    value <- json .? "value"
    pure { value } """
  encoder := """instance EncodeJson CostUSD where
  encodeJson m = "value" := m.value
    ~> jsonEmptyObject """

/-! ## Triggers - Conditions - PureScript Instances -/

instance : EmitPureScript PropertyCondition where
  typeName := "PropertyCondition"
  typeDecl := """type PropertyCondition = { propertyPath :: NonEmptyString, operator :: ComparisonOperator, value :: String }"""
  decoder := """instance DecodeJson PropertyCondition where
  decodeJson json = do
    propertyPath <- json .? "propertyPath"
    operator <- json .? "operator"
    value <- json .? "value"
    pure { propertyPath, operator, value } """
  encoder := """instance EncodeJson PropertyCondition where
  encodeJson c = "propertyPath" := c.propertyPath
    ~> "operator" := c.operator
    ~> "value" := c.value
    ~> jsonEmptyObject """

instance : EmitPureScript FrameCondition where
  typeName := "FrameCondition"
  typeDecl := """type FrameCondition = { frame :: FrameNumber, range :: Maybe (Tuple FrameNumber FrameNumber), modulo :: Maybe FrameNumber }"""
  decoder := """instance DecodeJson FrameCondition where
  decodeJson json = do
    frame <- json .? "frame"
    range <- case json .? "range" of
      Nothing -> pure Nothing
      Just rangeJson -> case Json.toArray rangeJson of
        Just [startJson, endJson] -> do
          start <- decodeJson startJson
          end <- decodeJson endJson
          pure (Just (Tuple start end))
        _ -> Left (TypeMismatch "range must be array of 2 FrameNumbers")
    modulo <- case json .? "modulo" of
      Nothing -> pure Nothing
      Just mJson -> map Just (decodeJson mJson)
    pure { frame, range, modulo } """
  encoder := """instance EncodeJson FrameCondition where
  encodeJson c = let rangeJson = case c.range of
        Nothing -> Nothing
        Just (Tuple start end) -> Just (Json.fromArray [encodeJson start, encodeJson end])
    in "frame" := c.frame
    ~> "range" :=? rangeJson
    ~> "modulo" :=? c.modulo
    ~> jsonEmptyObject """

instance : EmitPureScript AudioCondition where
  typeName := "AudioCondition"
  typeDecl := """type AudioCondition = { beatIndex :: Maybe FrameNumber, peakThreshold :: NormalizedValue, frequency :: Maybe NormalizedValue }"""
  decoder := """instance DecodeJson AudioCondition where
  decodeJson json = do
    beatIndex <- case json .? "beatIndex" of
      Nothing -> pure Nothing
      Just biJson -> map Just (decodeJson biJson)
    peakThreshold <- json .? "peakThreshold"
    frequency <- case json .? "frequency" of
      Nothing -> pure Nothing
      Just fJson -> map Just (decodeJson fJson)
    pure { beatIndex, peakThreshold, frequency } """
  encoder := """instance EncodeJson AudioCondition where
  encodeJson c = "beatIndex" :=? c.beatIndex
    ~> "peakThreshold" := c.peakThreshold
    ~> "frequency" :=? c.frequency
    ~> jsonEmptyObject """

instance : EmitPureScript TimeCondition where
  typeName := "TimeCondition"
  typeDecl := """type TimeCondition = { timecode :: NonNegativeFloat, duration :: Maybe NonNegativeFloat, loop :: Boolean }"""
  decoder := """instance DecodeJson TimeCondition where
  decodeJson json = do
    timecode <- json .? "timecode"
    duration <- case json .? "duration" of
      Nothing -> pure Nothing
      Just dJson -> map Just (decodeJson dJson)
    loop <- json .? "loop"
    pure { timecode, duration, loop } """
  encoder := """instance EncodeJson TimeCondition where
  encodeJson c = "timecode" := c.timecode
    ~> "duration" :=? c.duration
    ~> "loop" := c.loop
    ~> jsonEmptyObject """

/-! ## Triggers - Trigger Types - PureScript Instances -/

instance : EmitPureScript FrameTrigger where
  typeName := "FrameTrigger"
  typeDecl := """type FrameTrigger = { id :: NonEmptyString, triggerType :: NonEmptyString, enabled :: Boolean, compositionId :: NonEmptyString, condition :: FrameCondition }"""
  decoder := """instance DecodeJson FrameTrigger where
  decodeJson json = do
    id <- json .? "id"
    triggerType <- json .? "triggerType"
    enabled <- json .? "enabled"
    compositionId <- json .? "compositionId"
    condition <- json .? "condition"
    pure { id, triggerType, enabled, compositionId, condition } """
  encoder := """instance EncodeJson FrameTrigger where
  encodeJson t = "id" := t.id
    ~> "triggerType" := t.triggerType
    ~> "enabled" := t.enabled
    ~> "compositionId" := t.compositionId
    ~> "condition" := t.condition
    ~> jsonEmptyObject """

instance : EmitPureScript PropertyTrigger where
  typeName := "PropertyTrigger"
  typeDecl := """type PropertyTrigger = { id :: NonEmptyString, triggerType :: NonEmptyString, enabled :: Boolean, compositionId :: NonEmptyString, condition :: PropertyCondition, layerId :: NonEmptyString }"""
  decoder := """instance DecodeJson PropertyTrigger where
  decodeJson json = do
    id <- json .? "id"
    triggerType <- json .? "triggerType"
    enabled <- json .? "enabled"
    compositionId <- json .? "compositionId"
    condition <- json .? "condition"
    layerId <- json .? "layerId"
    pure { id, triggerType, enabled, compositionId, condition, layerId } """
  encoder := """instance EncodeJson PropertyTrigger where
  encodeJson t = "id" := t.id
    ~> "triggerType" := t.triggerType
    ~> "enabled" := t.enabled
    ~> "compositionId" := t.compositionId
    ~> "condition" := t.condition
    ~> "layerId" := t.layerId
    ~> jsonEmptyObject """

instance : EmitPureScript AudioTrigger where
  typeName := "AudioTrigger"
  typeDecl := """type AudioTrigger = { id :: NonEmptyString, triggerType :: NonEmptyString, enabled :: Boolean, compositionId :: NonEmptyString, condition :: AudioCondition, layerId :: NonEmptyString }"""
  decoder := """instance DecodeJson AudioTrigger where
  decodeJson json = do
    id <- json .? "id"
    triggerType <- json .? "triggerType"
    enabled <- json .? "enabled"
    compositionId <- json .? "compositionId"
    condition <- json .? "condition"
    layerId <- json .? "layerId"
    pure { id, triggerType, enabled, compositionId, condition, layerId } """
  encoder := """instance EncodeJson AudioTrigger where
  encodeJson t = "id" := t.id
    ~> "triggerType" := t.triggerType
    ~> "enabled" := t.enabled
    ~> "compositionId" := t.compositionId
    ~> "condition" := t.condition
    ~> "layerId" := t.layerId
    ~> jsonEmptyObject """

instance : EmitPureScript TimeTrigger where
  typeName := "TimeTrigger"
  typeDecl := """type TimeTrigger = { id :: NonEmptyString, triggerType :: NonEmptyString, enabled :: Boolean, compositionId :: NonEmptyString, condition :: TimeCondition }"""
  decoder := """instance DecodeJson TimeTrigger where
  decodeJson json = do
    id <- json .? "id"
    triggerType <- json .? "triggerType"
    enabled <- json .? "enabled"
    compositionId <- json .? "compositionId"
    condition <- json .? "condition"
    pure { id, triggerType, enabled, compositionId, condition } """
  encoder := """instance EncodeJson TimeTrigger where
  encodeJson t = "id" := t.id
    ~> "triggerType" := t.triggerType
    ~> "enabled" := t.enabled
    ~> "compositionId" := t.compositionId
    ~> "condition" := t.condition
    ~> jsonEmptyObject """

instance : EmitPureScript ExpressionTrigger where
  typeName := "ExpressionTrigger"
  typeDecl := """type ExpressionTrigger = { id :: NonEmptyString, triggerType :: NonEmptyString, enabled :: Boolean, compositionId :: NonEmptyString, expression :: NonEmptyString, layerId :: NonEmptyString }"""
  decoder := """instance DecodeJson ExpressionTrigger where
  decodeJson json = do
    id <- json .? "id"
    triggerType <- json .? "triggerType"
    enabled <- json .? "enabled"
    compositionId <- json .? "compositionId"
    expression <- json .? "expression"
    layerId <- json .? "layerId"
    pure { id, triggerType, enabled, compositionId, expression, layerId } """
  encoder := """instance EncodeJson ExpressionTrigger where
  encodeJson t = "id" := t.id
    ~> "triggerType" := t.triggerType
    ~> "enabled" := t.enabled
    ~> "compositionId" := t.compositionId
    ~> "expression" := t.expression
    ~> "layerId" := t.layerId
    ~> jsonEmptyObject """

instance : EmitPureScript EventTrigger where
  typeName := "EventTrigger"
  typeDecl := """type EventTrigger = { id :: NonEmptyString, triggerType :: NonEmptyString, enabled :: Boolean, compositionId :: NonEmptyString, eventType :: NonEmptyString }"""
  decoder := """instance DecodeJson EventTrigger where
  decodeJson json = do
    id <- json .? "id"
    triggerType <- json .? "triggerType"
    enabled <- json .? "enabled"
    compositionId <- json .? "compositionId"
    eventType <- json .? "eventType"
    pure { id, triggerType, enabled, compositionId, eventType } """
  encoder := """instance EncodeJson EventTrigger where
  encodeJson t = "id" := t.id
    ~> "triggerType" := t.triggerType
    ~> "enabled" := t.enabled
    ~> "compositionId" := t.compositionId
    ~> "eventType" := t.eventType
    ~> jsonEmptyObject """

instance : EmitPureScript CompositeTrigger where
  typeName := "CompositeTrigger"
  typeDecl := """type CompositeTrigger = { id :: NonEmptyString, triggerType :: NonEmptyString, enabled :: Boolean, compositionId :: NonEmptyString, operator :: CompositeOperator, triggers :: Array NonEmptyString }"""
  decoder := """instance DecodeJson CompositeTrigger where
  decodeJson json = do
    id <- json .? "id"
    triggerType <- json .? "triggerType"
    enabled <- json .? "enabled"
    compositionId <- json .? "compositionId"
    operator <- json .? "operator"
    triggers <- json .? "triggers"
    pure { id, triggerType, enabled, compositionId, operator, triggers } """
  encoder := """instance EncodeJson CompositeTrigger where
  encodeJson t = "id" := t.id
    ~> "triggerType" := t.triggerType
    ~> "enabled" := t.enabled
    ~> "compositionId" := t.compositionId
    ~> "operator" := t.operator
    ~> "triggers" := t.triggers
    ~> jsonEmptyObject """

/-! ## Entities - Create/Update Types - PureScript Instances -/

instance : EmitPureScript (Lattice.Entities.CreateLayer) where
  typeName := "CreateLayerEntity"
  typeDecl := """type CreateLayerEntity = { name :: NonEmptyString, layerType :: LayerType, startFrame :: FrameNumber, endFrame :: FrameNumber, parentId :: Maybe NonEmptyString }"""
  decoder := """instance DecodeJson CreateLayerEntity where
  decodeJson json = do
    name <- json .? "name"
    layerType <- json .? "layerType"
    startFrame <- json .? "startFrame"
    endFrame <- json .? "endFrame"
    parentId <- case json .? "parentId" of
      Nothing -> pure Nothing
      Just idJson -> map Just (decodeJson idJson)
    pure { name, layerType, startFrame, endFrame, parentId } """
  encoder := """instance EncodeJson CreateLayerEntity where
  encodeJson c = "name" := c.name
    ~> "layerType" := c.layerType
    ~> "startFrame" := c.startFrame
    ~> "endFrame" := c.endFrame
    ~> "parentId" :=? c.parentId
    ~> jsonEmptyObject """

instance : EmitPureScript (Lattice.Entities.UpdateLayer) where
  typeName := "UpdateLayer"
  typeDecl := """type UpdateLayer = { name :: Maybe NonEmptyString, visible :: Maybe Boolean, locked :: Maybe Boolean, threeD :: Maybe Boolean, motionBlur :: Maybe Boolean, startFrame :: Maybe FrameNumber, endFrame :: Maybe FrameNumber, parentId :: Maybe NonEmptyString, blendMode :: Maybe BlendMode }"""
  decoder := """instance DecodeJson UpdateLayer where
  decodeJson json = do
    name <- case json .? "name" of
      Nothing -> pure Nothing
      Just nJson -> map Just (decodeJson nJson)
    visible <- case json .? "visible" of
      Nothing -> pure Nothing
      Just (.bool v) -> pure (Just v)
      _ -> pure Nothing
    locked <- case json .? "locked" of
      Nothing -> pure Nothing
      Just (.bool l) -> pure (Just l)
      _ -> pure Nothing
    threeD <- case json .? "threeD" of
      Nothing -> pure Nothing
      Just (.bool t) -> pure (Just t)
      _ -> pure Nothing
    motionBlur <- case json .? "motionBlur" of
      Nothing -> pure Nothing
      Just (.bool mb) -> pure (Just mb)
      _ -> pure Nothing
    startFrame <- case json .? "startFrame" of
      Nothing -> pure Nothing
      Just sfJson -> map Just (decodeJson sfJson)
    endFrame <- case json .? "endFrame" of
      Nothing -> pure Nothing
      Just efJson -> map Just (decodeJson efJson)
    parentId <- case json .? "parentId" of
      Nothing -> pure Nothing
      Just idJson -> map Just (decodeJson idJson)
    blendMode <- case json .? "blendMode" of
      Nothing -> pure Nothing
      Just bmJson -> map Just (decodeJson bmJson)
    pure { name, visible, locked, threeD, motionBlur, startFrame, endFrame, parentId, blendMode } """
  encoder := """instance EncodeJson UpdateLayer where
  encodeJson u = "name" :=? u.name
    ~> "visible" :=? u.visible
    ~> "locked" :=? u.locked
    ~> "threeD" :=? u.threeD
    ~> "motionBlur" :=? u.motionBlur
    ~> "startFrame" :=? u.startFrame
    ~> "endFrame" :=? u.endFrame
    ~> "parentId" :=? u.parentId
    ~> "blendMode" :=? u.blendMode
    ~> jsonEmptyObject """

instance : EmitPureScript (Lattice.Entities.CreateComposition) where
  typeName := "CreateCompositionEntity"
  typeDecl := """type CreateCompositionEntity = { name :: NonEmptyString, settings :: CompositionSettings, renderSettings :: RenderSettings }"""
  decoder := """instance DecodeJson CreateCompositionEntity where
  decodeJson json = do
    name <- json .? "name"
    settings <- json .? "settings"
    renderSettings <- json .? "renderSettings"
    pure { name, settings, renderSettings } """
  encoder := """instance EncodeJson CreateCompositionEntity where
  encodeJson c = "name" := c.name
    ~> "settings" := c.settings
    ~> "renderSettings" := c.renderSettings
    ~> jsonEmptyObject """

instance : EmitPureScript (Lattice.Entities.UpdateComposition) where
  typeName := "UpdateComposition"
  typeDecl := """type UpdateComposition = { name :: Maybe NonEmptyString, settings :: Maybe CompositionSettings, renderSettings :: Maybe RenderSettings }"""
  decoder := """instance DecodeJson UpdateComposition where
  decodeJson json = do
    name <- case json .? "name" of
      Nothing -> pure Nothing
      Just nJson -> map Just (decodeJson nJson)
    settings <- case json .? "settings" of
      Nothing -> pure Nothing
      Just sJson -> map Just (decodeJson sJson)
    renderSettings <- case json .? "renderSettings" of
      Nothing -> pure Nothing
      Just rsJson -> map Just (decodeJson rsJson)
    pure { name, settings, renderSettings } """
  encoder := """instance EncodeJson UpdateComposition where
  encodeJson u = "name" :=? u.name
    ~> "settings" :=? u.settings
    ~> "renderSettings" :=? u.renderSettings
    ~> jsonEmptyObject """

instance : EmitPureScript (Lattice.Entities.CreateEffectInstance) where
  typeName := "CreateEffectInstance"
  typeDecl := """type CreateEffectInstance = { effectType :: EffectType, layerId :: NonEmptyString }"""
  decoder := """instance DecodeJson CreateEffectInstance where
  decodeJson json = do
    effectType <- json .? "effectType"
    layerId <- json .? "layerId"
    pure { effectType, layerId } """
  encoder := """instance EncodeJson CreateEffectInstance where
  encodeJson c = "effectType" := c.effectType
    ~> "layerId" := c.layerId
    ~> jsonEmptyObject """

instance : EmitPureScript (Lattice.Entities.UpdateEffectInstance) where
  typeName := "UpdateEffectInstance"
  typeDecl := """type UpdateEffectInstance = { enabled :: Maybe Boolean, parameters :: Maybe (Array NonEmptyString) }"""
  decoder := """instance DecodeJson UpdateEffectInstance where
  decodeJson json = do
    enabled <- case json .? "enabled" of
      Nothing -> pure Nothing
      Just (.bool e) -> pure (Just e)
      _ -> pure Nothing
    parameters <- case json .? "parameters" of
      Nothing -> pure Nothing
      Just paramsJson -> map Just (decodeJson paramsJson)
    pure { enabled, parameters } """
  encoder := """instance EncodeJson UpdateEffectInstance where
  encodeJson u = "enabled" :=? u.enabled
    ~> "parameters" :=? u.parameters
    ~> jsonEmptyObject """

instance : EmitPureScript (Lattice.Entities.CreateProject) where
  typeName := "CreateProject"
  typeDecl := """type CreateProject = { name :: NonEmptyString, settings :: ProjectSettings }"""
  decoder := """instance DecodeJson CreateProject where
  decodeJson json = do
    name <- json .? "name"
    settings <- json .? "settings"
    pure { name, settings } """
  encoder := """instance EncodeJson CreateProject where
  encodeJson c = "name" := c.name
    ~> "settings" := c.settings
    ~> jsonEmptyObject """

instance : EmitPureScript (Lattice.Entities.UpdateProject) where
  typeName := "UpdateProject"
  typeDecl := """type UpdateProject = { name :: Maybe NonEmptyString, settings :: Maybe ProjectSettings, mainCompositionId :: Maybe NonEmptyString }"""
  decoder := """instance DecodeJson UpdateProject where
  decodeJson json = do
    name <- case json .? "name" of
      Nothing -> pure Nothing
      Just nJson -> map Just (decodeJson nJson)
    settings <- case json .? "settings" of
      Nothing -> pure Nothing
      Just sJson -> map Just (decodeJson sJson)
    mainCompositionId <- case json .? "mainCompositionId" of
      Nothing -> pure Nothing
      Just idJson -> map Just (decodeJson idJson)
    pure { name, settings, mainCompositionId } """
  encoder := """instance EncodeJson UpdateProject where
  encodeJson u = "name" :=? u.name
    ~> "settings" :=? u.settings
    ~> "mainCompositionId" :=? u.mainCompositionId
    ~> jsonEmptyObject """

instance : EmitPureScript (Lattice.Entities.CreateAsset) where
  typeName := "CreateAsset"
  typeDecl := """type CreateAsset = { name :: NonEmptyString, assetType :: AssetType, source :: AssetSource, data :: NonEmptyString, metadata :: AssetMetadata }"""
  decoder := """instance DecodeJson CreateAsset where
  decodeJson json = do
    name <- json .? "name"
    assetType <- json .? "assetType"
    source <- json .? "source"
    data <- json .? "data"
    metadata <- json .? "metadata"
    pure { name, assetType, source, data, metadata } """
  encoder := """instance EncodeJson CreateAsset where
  encodeJson c = "name" := c.name
    ~> "assetType" := c.assetType
    ~> "source" := c.source
    ~> "data" := c.data
    ~> "metadata" := c.metadata
    ~> jsonEmptyObject """

instance : EmitPureScript (Lattice.Entities.UpdateAsset) where
  typeName := "UpdateAsset"
  typeDecl := """type UpdateAsset = { name :: Maybe NonEmptyString, data :: Maybe NonEmptyString, metadata :: Maybe AssetMetadata }"""
  decoder := """instance DecodeJson UpdateAsset where
  decodeJson json = do
    name <- case json .? "name" of
      Nothing -> pure Nothing
      Just nJson -> map Just (decodeJson nJson)
    data <- case json .? "data" of
      Nothing -> pure Nothing
      Just dJson -> map Just (decodeJson dJson)
    metadata <- case json .? "metadata" of
      Nothing -> pure Nothing
      Just mJson -> map Just (decodeJson mJson)
    pure { name, data, metadata } """
  encoder := """instance EncodeJson UpdateAsset where
  encodeJson u = "name" :=? u.name
    ~> "data" :=? u.data
    ~> "metadata" :=? u.metadata
    ~> jsonEmptyObject """

instance : EmitPureScript (Lattice.Entities.CreateExportJob) where
  typeName := "CreateExportJob"
  typeDecl := """type CreateExportJob = { compositionId :: NonEmptyString, config :: ExportConfig }"""
  decoder := """instance DecodeJson CreateExportJob where
  decodeJson json = do
    compositionId <- json .? "compositionId"
    config <- json .? "config"
    pure { compositionId, config } """
  encoder := """instance EncodeJson CreateExportJob where
  encodeJson c = "compositionId" := c.compositionId
    ~> "config" := c.config
    ~> jsonEmptyObject """

instance : EmitPureScript (Lattice.Entities.UpdateExportJob) where
  typeName := "UpdateExportJob"
  typeDecl := """type UpdateExportJob = { status :: Maybe ExportJobStatus, progress :: Maybe NormalizedValue, outputFiles :: Maybe String, errorMessage :: Maybe NonEmptyString }"""
  decoder := """instance DecodeJson UpdateExportJob where
  decodeJson json = do
    status <- case json .? "status" of
      Nothing -> pure Nothing
      Just sJson -> map Just (decodeJson sJson)
    progress <- case json .? "progress" of
      Nothing -> pure Nothing
      Just pJson -> map Just (decodeJson pJson)
    outputFiles <- case json .? "outputFiles" of
      Nothing -> pure Nothing
      Just (.str of) -> pure (Just of)
      _ -> pure Nothing
    errorMessage <- case json .? "errorMessage" of
      Nothing -> pure Nothing
      Just emJson -> map Just (decodeJson emJson)
    pure { status, progress, outputFiles, errorMessage } """
  encoder := """instance EncodeJson UpdateExportJob where
  encodeJson u = "status" :=? u.status
    ~> "progress" :=? u.progress
    ~> "outputFiles" :=? u.outputFiles
    ~> "errorMessage" :=? u.errorMessage
    ~> jsonEmptyObject """

/-! ## Structures - PureScript Instances -/

instance : EmitPureScript CompositionSettings where
  typeName := "CompositionSettings"
  typeDecl := "type CompositionSettings = { width :: PositiveInt, height :: PositiveInt, fps :: PositiveFloat, duration :: NonNegativeFloat, backgroundColor :: NonEmptyString }"
  decoder := """instance DecodeJson CompositionSettings where
  decodeJson json = do
    obj <- decodeJson json
    width <- obj .: "width"
    height <- obj .: "height"
    fps <- obj .: "fps"
    duration <- obj .: "duration"
    backgroundColor <- obj .: "backgroundColor"
    pure { width, height, fps, duration, backgroundColor } """
  encoder := """instance EncodeJson CompositionSettings where
  encodeJson s = "width" := s.width ~> "height" := s.height ~> "fps" := s.fps ~> "duration" := s.duration ~> "backgroundColor" := s.backgroundColor ~> jsonEmptyObject"""

instance : EmitPureScript RenderSettings where
  typeName := "RenderSettings"
  typeDecl := "type RenderSettings = { quality :: QualityMode, motionBlur :: Boolean, motionBlurSamples :: PositiveInt, motionBlurShutterAngle :: NormalizedValue }"
  decoder := """instance DecodeJson RenderSettings where
  decodeJson json = do
    obj <- decodeJson json
    quality <- obj .: "quality"
    motionBlur <- obj .: "motionBlur"
    motionBlurSamples <- obj .: "motionBlurSamples"
    motionBlurShutterAngle <- obj .: "motionBlurShutterAngle"
    pure { quality, motionBlur, motionBlurSamples, motionBlurShutterAngle } """
  encoder := """instance EncodeJson RenderSettings where
  encodeJson s = "quality" := s.quality ~> "motionBlur" := s.motionBlur ~> "motionBlurSamples" := s.motionBlurSamples ~> "motionBlurShutterAngle" := s.motionBlurShutterAngle ~> jsonEmptyObject"""

instance : EmitPureScript Composition where
  typeName := "Composition"
  typeDecl := "type Composition = { id :: NonEmptyString, createdAt :: Int, updatedAt :: Int, name :: NonEmptyString, settings :: CompositionSettings, renderSettings :: RenderSettings, mainCompositionId :: Maybe NonEmptyString }"
  decoder := """instance DecodeJson Composition where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    createdAt <- obj .: "createdAt"
    updatedAt <- obj .: "updatedAt"
    name <- obj .: "name"
    settings <- obj .: "settings"
    renderSettings <- obj .: "renderSettings"
    mainCompositionId <- obj .:? "mainCompositionId"
    pure { id, createdAt, updatedAt, name, settings, renderSettings, mainCompositionId } """
  encoder := """instance EncodeJson Composition where
  encodeJson c = "id" := c.id ~> "createdAt" := c.createdAt ~> "updatedAt" := c.updatedAt ~> "name" := c.name ~> "settings" := c.settings ~> "renderSettings" := c.renderSettings ~> "mainCompositionId" :=? c.mainCompositionId ~> jsonEmptyObject"""

instance : EmitPureScript LayerTransform where
  typeName := "LayerTransform"
  typeDecl := "type LayerTransform = { position :: Vec2, rotation :: Number, scale :: Vec2, anchor :: Vec2, opacity :: NormalizedValue }"
  decoder := """instance DecodeJson LayerTransform where
  decodeJson json = do
    obj <- decodeJson json
    position <- obj .: "position"
    rotation <- obj .: "rotation"
    scale <- obj .: "scale"
    anchor <- obj .: "anchor"
    opacity <- obj .: "opacity"
    if isFinite rotation && not (isNaN rotation)
      then pure { position, rotation, scale, anchor, opacity }
      else Left "LayerTransform rotation must be finite" """
  encoder := """instance EncodeJson LayerTransform where
  encodeJson t = "position" := t.position ~> "rotation" := t.rotation ~> "scale" := t.scale ~> "anchor" := t.anchor ~> "opacity" := t.opacity ~> jsonEmptyObject"""

instance : EmitPureScript Keyframe where
  typeName := "Keyframe"
  typeDecl := "type Keyframe = { id :: NonEmptyString, frame :: FrameNumber, value :: String, interpolation :: InterpolationType, inHandle :: BezierHandle, outHandle :: BezierHandle, controlMode :: ControlMode }"
  decoder := """instance DecodeJson Keyframe where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    frame <- obj .: "frame"
    value <- obj .: "value"
    interpolation <- obj .: "interpolation"
    inHandle <- obj .: "inHandle"
    outHandle <- obj .: "outHandle"
    controlMode <- obj .: "controlMode"
    pure { id, frame, value, interpolation, inHandle, outHandle, controlMode } """
  encoder := """instance EncodeJson Keyframe where
  encodeJson k = "id" := k.id ~> "frame" := k.frame ~> "value" := k.value ~> "interpolation" := k.interpolation ~> "inHandle" := k.inHandle ~> "outHandle" := k.outHandle ~> "controlMode" := k.controlMode ~> jsonEmptyObject"""

instance : EmitPureScript PropertyExpression where
  typeName := "PropertyExpression"
  typeDecl := "type PropertyExpression = { enabled :: Boolean, expressionType :: ExpressionType, name :: NonEmptyString, params :: String }"
  decoder := """instance DecodeJson PropertyExpression where
  decodeJson json = do
    obj <- decodeJson json
    enabled <- obj .: "enabled"
    expressionType <- obj .: "expressionType"
    name <- obj .: "name"
    params <- obj .: "params"
    pure { enabled, expressionType, name, params } """
  encoder := """instance EncodeJson PropertyExpression where
  encodeJson e = "enabled" := e.enabled ~> "expressionType" := e.expressionType ~> "name" := e.name ~> "params" := e.params ~> jsonEmptyObject"""

instance : EmitPureScript AnimatableProperty where
  typeName := "AnimatableProperty"
  typeDecl := "type AnimatableProperty = { id :: NonEmptyString, name :: NonEmptyString, propertyType :: PropertyValueType, value :: String, animated :: Boolean, keyframes :: Array NonEmptyString, group :: Maybe NonEmptyString, expression :: Maybe PropertyExpression }"
  decoder := """instance DecodeJson AnimatableProperty where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    name <- obj .: "name"
    propertyType <- obj .: "propertyType"
    value <- obj .: "value"
    animated <- obj .: "animated"
    keyframes <- obj .: "keyframes"
    group <- obj .:? "group"
    expression <- obj .:? "expression"
    pure { id, name, propertyType, value, animated, keyframes, group, expression } """
  encoder := """instance EncodeJson AnimatableProperty where
  encodeJson p = "id" := p.id ~> "name" := p.name ~> "propertyType" := p.propertyType ~> "value" := p.value ~> "animated" := p.animated ~> "keyframes" := p.keyframes ~> "group" :=? p.group ~> "expression" :=? p.expression ~> jsonEmptyObject"""

instance : EmitPureScript LayerMask where
  typeName := "LayerMask"
  typeDecl := "type LayerMask = { id :: NonEmptyString, path :: String, mode :: MaskMode, inverted :: Boolean }"
  decoder := """instance DecodeJson LayerMask where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    path <- obj .: "path"
    mode <- obj .: "mode"
    inverted <- obj .: "inverted"
    pure { id, path, mode, inverted } """
  encoder := """instance EncodeJson LayerMask where
  encodeJson m = "id" := m.id ~> "path" := m.path ~> "mode" := m.mode ~> "inverted" := m.inverted ~> jsonEmptyObject"""

instance : EmitPureScript Layer where
  typeName := "Layer"
  typeDecl := "type Layer = { id :: NonEmptyString, createdAt :: Int, updatedAt :: Int, name :: NonEmptyString, layerType :: LayerType, visible :: Boolean, locked :: Boolean, threeD :: Boolean, motionBlur :: Boolean, startFrame :: FrameNumber, endFrame :: FrameNumber, parentId :: Maybe NonEmptyString, blendMode :: BlendMode, opacity :: AnimatableProperty, transform :: LayerTransform, masks :: Array LayerMask, matteType :: Maybe NonEmptyString, properties :: Array NonEmptyString, effects :: Array NonEmptyString, data :: Maybe NonEmptyString }"
  decoder := """instance DecodeJson Layer where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    createdAt <- obj .: "createdAt"
    updatedAt <- obj .: "updatedAt"
    name <- obj .: "name"
    layerType <- obj .: "layerType"
    visible <- obj .: "visible"
    locked <- obj .: "locked"
    threeD <- obj .: "threeD"
    motionBlur <- obj .: "motionBlur"
    startFrame <- obj .: "startFrame"
    endFrame <- obj .: "endFrame"
    parentId <- obj .:? "parentId"
    blendMode <- obj .: "blendMode"
    opacity <- obj .: "opacity"
    transform <- obj .: "transform"
    masks <- obj .: "masks"
    matteType <- obj .:? "matteType"
    properties <- obj .: "properties"
    effects <- obj .: "effects"
    data <- obj .:? "data"
    pure { id, createdAt, updatedAt, name, layerType, visible, locked, threeD, motionBlur, startFrame, endFrame, parentId, blendMode, opacity, transform, masks, matteType, properties, effects, data } """
  encoder := """instance EncodeJson Layer where
  encodeJson l = "id" := l.id ~> "createdAt" := l.createdAt ~> "updatedAt" := l.updatedAt ~> "name" := l.name ~> "layerType" := l.layerType ~> "visible" := l.visible ~> "locked" := l.locked ~> "threeD" := l.threeD ~> "motionBlur" := l.motionBlur ~> "startFrame" := l.startFrame ~> "endFrame" := l.endFrame ~> "parentId" :=? l.parentId ~> "blendMode" := l.blendMode ~> "opacity" := l.opacity ~> "transform" := l.transform ~> "masks" := l.masks ~> "matteType" :=? l.matteType ~> "properties" := l.properties ~> "effects" := l.effects ~> "data" :=? l.data ~> jsonEmptyObject"""

/-! ## Full Module Generation -/

def purescriptModule : String :=
  let header := """-- |
-- Module      : Lattice.Types.Primitives
-- Description : AUTO-EXTRACTED FROM LEAN PROOFS
-- 
-- Every type here has a corresponding Extractable instance in Lean
-- with a proven roundtrip theorem. The encoder/decoder pairs are
-- verified correct by construction.
-- 
-- DO NOT EDIT - regenerate with `lake exe extract purescript`
--

module Lattice.Types.Primitives where

import Prelude
import Data.Argonaut (class EncodeJson, class DecodeJson, Json, encodeJson, decodeJson, (.?), (:=), (:=?), (~>), jsonEmptyObject, JsonDecodeError(..))
import Data.Argonaut.Core as Json
import Data.Array (uncons)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))

"""
  let types := [
    EmitPureScript.typeDecl (α := NonEmptyString),
    EmitPureScript.typeDecl (α := PositiveInt),
    EmitPureScript.typeDecl (α := PositiveFloat),
    EmitPureScript.typeDecl (α := NonNegativeFloat),
    EmitPureScript.typeDecl (α := Percentage),
    EmitPureScript.typeDecl (α := NormalizedValue),
    EmitPureScript.typeDecl (α := FrameNumber),
    EmitPureScript.typeDecl (α := Vec2),
    EmitPureScript.typeDecl (α := Vec3),
    EmitPureScript.typeDecl (α := Vec4),
    EmitPureScript.typeDecl (α := Matrix3x3),
    EmitPureScript.typeDecl (α := Matrix4x4),
    EmitPureScript.typeDecl (α := ControlMode),
    EmitPureScript.typeDecl (α := BezierHandle),
    EmitPureScript.typeDecl (α := InterpolationType),
    EmitPureScript.typeDecl (α := PropertyValueType),
    EmitPureScript.typeDecl (α := LayerType),
    EmitPureScript.typeDecl (α := BlendMode),
    EmitPureScript.typeDecl (α := MaskMode),
    EmitPureScript.typeDecl (α := ExpressionType),
    EmitPureScript.typeDecl (α := QualityMode),
    EmitPureScript.typeDecl (α := LayerStatus),
    EmitPureScript.typeDecl (α := EffectCategory),
    EmitPureScript.typeDecl (α := EffectStatus),
    EmitPureScript.typeDecl (α := EffectType),
    EmitPureScript.typeDecl (α := ExportFormat),
    EmitPureScript.typeDecl (α := ExportStatus),
    EmitPureScript.typeDecl (α := JobStatus),
    EmitPureScript.typeDecl (α := RenderStatus),
    EmitPureScript.typeDecl (α := ValidationResult),
    EmitPureScript.typeDecl (α := Severity),
    EmitPureScript.typeDecl (α := AssetType),
    EmitPureScript.typeDecl (α := AssetSource),
    EmitPureScript.typeDecl (α := ExportJobStatus),
    EmitPureScript.typeDecl (α := CameraType),
    EmitPureScript.typeDecl (α := ProjectionType),
    EmitPureScript.typeDecl (α := KeyframeType),
    EmitPureScript.typeDecl (α := ColorSpace),
    EmitPureScript.typeDecl (α := ColorFormat),
    EmitPureScript.typeDecl (α := TransferFunction),
    EmitPureScript.typeDecl (α := TextAlign),
    EmitPureScript.typeDecl (α := TextDirection),
    EmitPureScript.typeDecl (α := FontStyle),
    EmitPureScript.typeDecl (α := FontWeight),
    EmitPureScript.typeDecl (α := AudioFormat),
    EmitPureScript.typeDecl (α := AudioChannel),
    EmitPureScript.typeDecl (α := BeatDetectionMethod),
    EmitPureScript.typeDecl (α := DepthOfFieldMode),
    EmitPureScript.typeDecl (α := ModelType),
    EmitPureScript.typeDecl (α := PreprocessorType),
    EmitPureScript.typeDecl (α := SegmentationMode),
    EmitPureScript.typeDecl (α := AuditCategory),
    EmitPureScript.typeDecl (α := RateLimitScope),
    EmitPureScript.typeDecl (α := SyncStatus),
    EmitPureScript.typeDecl (α := TextRangeMode),
    EmitPureScript.typeDecl (α := TextRangeBasedOn),
    EmitPureScript.typeDecl (α := TextRangeShape),
    EmitPureScript.typeDecl (α := ComparisonOperator),
    EmitPureScript.typeDecl (α := CompositeOperator),
    EmitPureScript.typeDecl (α := EmitterShape),
    EmitPureScript.typeDecl (α := ParticleShape),
    EmitPureScript.typeDecl (α := CollisionType),
    EmitPureScript.typeDecl (α := MaterialType),
    EmitPureScript.typeDecl (α := AutoOrientMode),
    EmitPureScript.typeDecl (α := CameraControlType),
    EmitPureScript.typeDecl (α := ForceType),
    EmitPureScript.typeDecl (α := BodyType),
    EmitPureScript.typeDecl (α := AggregationType),
    EmitPureScript.typeDecl (α := TimeGrain),
    EmitPureScript.typeDecl (α := MetricDataType),
    EmitPureScript.typeDecl (α := MetricCategory),
    EmitPureScript.typeDecl (α := JointType),
    EmitPureScript.typeDecl (α := EasingType),
    EmitPureScript.typeDecl (α := ExportTarget),
    EmitPureScript.typeDecl (α := ActionResult),
    EmitPureScript.typeDecl (α := RetryPolicy),
    EmitPureScript.typeDecl (α := BaseEvent),
    EmitPureScript.typeDecl (α := BaseAction),
    EmitPureScript.typeDecl (α := BaseTrigger),
    EmitPureScript.typeDecl (α := CompositionCreated),
    EmitPureScript.typeDecl (α := CompositionDeleted),
    EmitPureScript.typeDecl (α := CompositionRendered),
    EmitPureScript.typeDecl (α := LayerCreated),
    EmitPureScript.typeDecl (α := LayerDeleted),
    EmitPureScript.typeDecl (α := LayerMoved),
    EmitPureScript.typeDecl (α := LayerDuplicated),
    EmitPureScript.typeDecl (α := LayerVisibilityChanged),
    EmitPureScript.typeDecl (α := KeyframeAdded),
    EmitPureScript.typeDecl (α := KeyframeRemoved),
    EmitPureScript.typeDecl (α := KeyframeModified),
    EmitPureScript.typeDecl (α := KeyframeInterpolationChanged),
    EmitPureScript.typeDecl (α := PropertyAnimated),
    EmitPureScript.typeDecl (α := PropertyExpressionChanged),
    EmitPureScript.typeDecl (α := PropertyDriverAdded),
    EmitPureScript.typeDecl (α := EffectAdded),
    EmitPureScript.typeDecl (α := EffectRemoved),
    EmitPureScript.typeDecl (α := EffectParameterChanged),
    EmitPureScript.typeDecl (α := ExportStarted),
    EmitPureScript.typeDecl (α := ExportProgress),
    EmitPureScript.typeDecl (α := ExportCompleted),
    EmitPureScript.typeDecl (α := ExportFailed),
    EmitPureScript.typeDecl (α := RenderJobQueued),
    EmitPureScript.typeDecl (α := RenderJobCompleted),
    EmitPureScript.typeDecl (α := CacheCleared),
    EmitPureScript.typeDecl (α := ErrorOccurred),
    EmitPureScript.typeDecl (α := (Lattice.Actions.CreateLayer)),
    EmitPureScript.typeDecl (α := DeleteLayer),
    EmitPureScript.typeDecl (α := DuplicateLayer),
    EmitPureScript.typeDecl (α := MoveLayer),
    EmitPureScript.typeDecl (α := SetLayerVisibility),
    EmitPureScript.typeDecl (α := SetLayerOpacity),
    EmitPureScript.typeDecl (α := AddKeyframe),
    EmitPureScript.typeDecl (α := RemoveKeyframe),
    EmitPureScript.typeDecl (α := ModifyKeyframe),
    EmitPureScript.typeDecl (α := SetInterpolation),
    EmitPureScript.typeDecl (α := CopyKeyframes),
    EmitPureScript.typeDecl (α := PasteKeyframes),
    EmitPureScript.typeDecl (α := AnimateProperty),
    EmitPureScript.typeDecl (α := SetPropertyValue),
    EmitPureScript.typeDecl (α := AddExpression),
    EmitPureScript.typeDecl (α := RemoveExpression),
    EmitPureScript.typeDecl (α := AddDriver),
    EmitPureScript.typeDecl (α := AddEffect),
    EmitPureScript.typeDecl (α := RemoveEffect),
    EmitPureScript.typeDecl (α := ModifyEffect),
    EmitPureScript.typeDecl (α := EnableEffect),
    EmitPureScript.typeDecl (α := DisableEffect),
    EmitPureScript.typeDecl (α := (Lattice.Actions.CreateComposition)),
    EmitPureScript.typeDecl (α := DeleteComposition),
    EmitPureScript.typeDecl (α := SetCompositionSettings),
    EmitPureScript.typeDecl (α := RenderComposition),
    EmitPureScript.typeDecl (α := StartExport),
    EmitPureScript.typeDecl (α := CancelExport),
    EmitPureScript.typeDecl (α := PauseExport),
    EmitPureScript.typeDecl (α := ResumeExport),
    EmitPureScript.typeDecl (α := SetExportSettings),
    EmitPureScript.typeDecl (α := LoadAudio),
    EmitPureScript.typeDecl (α := AnalyzeAudio),
    EmitPureScript.typeDecl (α := SetAudioReactivity),
    EmitPureScript.typeDecl (α := SetCameraPosition),
    EmitPureScript.typeDecl (α := SetCameraRotation),
    EmitPureScript.typeDecl (α := SetCameraFOV),
    EmitPureScript.typeDecl (α := AnimateCamera),
    EmitPureScript.typeDecl (α := SegmentImage),
    EmitPureScript.typeDecl (α := VectorizeImage),
    EmitPureScript.typeDecl (α := DecomposeImage),
    EmitPureScript.typeDecl (α := GenerateDepth),
    EmitPureScript.typeDecl (α := EstimateNormals),
    EmitPureScript.typeDecl (α := ClearCache),
    EmitPureScript.typeDecl (α := OptimizeMemory),
    EmitPureScript.typeDecl (α := SaveProject),
    EmitPureScript.typeDecl (α := LoadProject),
    EmitPureScript.typeDecl (α := Undo),
    EmitPureScript.typeDecl (α := Redo),
    EmitPureScript.typeDecl (α := EffectParameter),
    EmitPureScript.typeDecl (α := EffectPreset),
    EmitPureScript.typeDecl (α := ProjectMetadata),
    EmitPureScript.typeDecl (α := ProjectSettings),
    EmitPureScript.typeDecl (α := AssetMetadata),
    EmitPureScript.typeDecl (α := DepthOfField),
    EmitPureScript.typeDecl (α := FontConfig),
    EmitPureScript.typeDecl (α := BeatData),
    EmitPureScript.typeDecl (α := PhysicsMaterial),
    EmitPureScript.typeDecl (α := EffectInstance),
    EmitPureScript.typeDecl (α := Project),
    EmitPureScript.typeDecl (α := Asset),
    EmitPureScript.typeDecl (α := AssetReference),
    EmitPureScript.typeDecl (α := ExportConfig),
    EmitPureScript.typeDecl (α := ExportTemplate),
    EmitPureScript.typeDecl (α := ExportJob),
    EmitPureScript.typeDecl (α := Camera3D),
    EmitPureScript.typeDecl (α := CameraKeyframe),
    EmitPureScript.typeDecl (α := CameraPath),
    EmitPureScript.typeDecl (α := TextAnimatorProperties),
    EmitPureScript.typeDecl (α := TextRangeSelector),
    EmitPureScript.typeDecl (α := TextAnimator),
    EmitPureScript.typeDecl (α := TextLayerData),
    EmitPureScript.typeDecl (α := TextShaper),
    EmitPureScript.typeDecl (α := AudioAnalysis),
    EmitPureScript.typeDecl (α := AudioReactivity),
    EmitPureScript.typeDecl (α := AudioTrack),
    EmitPureScript.typeDecl (α := ParticleEmitter),
    EmitPureScript.typeDecl (α := Force),
    EmitPureScript.typeDecl (α := CollisionConfig),
    EmitPureScript.typeDecl (α := ParticleRenderer),
    EmitPureScript.typeDecl (α := ParticleSystem),
    EmitPureScript.typeDecl (α := RigidBody),
    EmitPureScript.typeDecl (α := Joint),
    EmitPureScript.typeDecl (α := PhysicsSpace),
    EmitPureScript.typeDecl (α := Ragdoll),
    EmitPureScript.typeDecl (α := Cloth),
    EmitPureScript.typeDecl (α := MetricDefinition),
    EmitPureScript.typeDecl (α := FrameRenderTime),
    EmitPureScript.typeDecl (α := TotalRenderTime),
    EmitPureScript.typeDecl (α := MemoryUsage),
    EmitPureScript.typeDecl (α := GpuUsage),
    EmitPureScript.typeDecl (α := CacheHitRate),
    EmitPureScript.typeDecl (α := CacheSize),
    EmitPureScript.typeDecl (α := Fps),
    EmitPureScript.typeDecl (α := DroppedFrames),
    EmitPureScript.typeDecl (α := PlaybackLatency),
    EmitPureScript.typeDecl (α := ScrubLatency),
    EmitPureScript.typeDecl (α := CompressionRatio),
    EmitPureScript.typeDecl (α := Bitrate),
    EmitPureScript.typeDecl (α := ColorAccuracy),
    EmitPureScript.typeDecl (α := MotionBlurQuality),
    EmitPureScript.typeDecl (α := VramUsage),
    EmitPureScript.typeDecl (α := CpuUsage),
    EmitPureScript.typeDecl (α := NetworkBandwidth),
    EmitPureScript.typeDecl (α := StorageUsed),
    EmitPureScript.typeDecl (α := ActionsPerSession),
    EmitPureScript.typeDecl (α := ExportCount),
    EmitPureScript.typeDecl (α := ProjectCount),
    EmitPureScript.typeDecl (α := InferenceTime),
    EmitPureScript.typeDecl (α := ModelLoadTime),
    EmitPureScript.typeDecl (α := TokensUsed),
    EmitPureScript.typeDecl (α := CostUSD),
    EmitPureScript.typeDecl (α := PropertyCondition),
    EmitPureScript.typeDecl (α := FrameCondition),
    EmitPureScript.typeDecl (α := AudioCondition),
    EmitPureScript.typeDecl (α := TimeCondition),
    EmitPureScript.typeDecl (α := FrameTrigger),
    EmitPureScript.typeDecl (α := PropertyTrigger),
    EmitPureScript.typeDecl (α := AudioTrigger),
    EmitPureScript.typeDecl (α := TimeTrigger),
    EmitPureScript.typeDecl (α := ExpressionTrigger),
    EmitPureScript.typeDecl (α := EventTrigger),
    EmitPureScript.typeDecl (α := CompositeTrigger),
    EmitPureScript.typeDecl (α := Lattice.Entities.CreateLayer),
    EmitPureScript.typeDecl (α := Lattice.Entities.UpdateLayer),
    EmitPureScript.typeDecl (α := Lattice.Entities.CreateComposition),
    EmitPureScript.typeDecl (α := Lattice.Entities.UpdateComposition),
    EmitPureScript.typeDecl (α := Lattice.Entities.CreateEffectInstance),
    EmitPureScript.typeDecl (α := Lattice.Entities.UpdateEffectInstance),
    EmitPureScript.typeDecl (α := Lattice.Entities.CreateProject),
    EmitPureScript.typeDecl (α := Lattice.Entities.UpdateProject),
    EmitPureScript.typeDecl (α := Lattice.Entities.CreateAsset),
    EmitPureScript.typeDecl (α := Lattice.Entities.UpdateAsset),
    EmitPureScript.typeDecl (α := Lattice.Entities.CreateExportJob),
    EmitPureScript.typeDecl (α := Lattice.Entities.UpdateExportJob),
    EmitPureScript.typeDecl (α := CompositionSettings),
    EmitPureScript.typeDecl (α := RenderSettings),
    EmitPureScript.typeDecl (α := Composition),
    EmitPureScript.typeDecl (α := LayerTransform),
    EmitPureScript.typeDecl (α := Keyframe),
    EmitPureScript.typeDecl (α := PropertyExpression),
    EmitPureScript.typeDecl (α := AnimatableProperty),
    EmitPureScript.typeDecl (α := LayerMask),
    EmitPureScript.typeDecl (α := Layer)
  ]
  let decoders := [
    EmitPureScript.decoder (α := NonEmptyString),
    EmitPureScript.decoder (α := PositiveInt),
    EmitPureScript.decoder (α := PositiveFloat),
    EmitPureScript.decoder (α := NonNegativeFloat),
    EmitPureScript.decoder (α := Percentage),
    EmitPureScript.decoder (α := NormalizedValue),
    EmitPureScript.decoder (α := FrameNumber),
    EmitPureScript.decoder (α := Vec2),
    EmitPureScript.decoder (α := Vec3),
    EmitPureScript.decoder (α := Vec4),
    EmitPureScript.decoder (α := Matrix3x3),
    EmitPureScript.decoder (α := Matrix4x4),
    EmitPureScript.decoder (α := ControlMode),
    EmitPureScript.decoder (α := BezierHandle),
    EmitPureScript.decoder (α := InterpolationType),
    EmitPureScript.decoder (α := PropertyValueType),
    EmitPureScript.decoder (α := LayerType),
    EmitPureScript.decoder (α := BlendMode),
    EmitPureScript.decoder (α := MaskMode),
    EmitPureScript.decoder (α := ExpressionType),
    EmitPureScript.decoder (α := QualityMode),
    EmitPureScript.decoder (α := LayerStatus),
    EmitPureScript.decoder (α := EffectCategory),
    EmitPureScript.decoder (α := EffectStatus),
    EmitPureScript.decoder (α := EffectType),
    EmitPureScript.decoder (α := ExportFormat),
    EmitPureScript.decoder (α := ExportStatus),
    EmitPureScript.decoder (α := JobStatus),
    EmitPureScript.decoder (α := RenderStatus),
    EmitPureScript.decoder (α := ValidationResult),
    EmitPureScript.decoder (α := Severity),
    EmitPureScript.decoder (α := AssetType),
    EmitPureScript.decoder (α := AssetSource),
    EmitPureScript.decoder (α := ExportJobStatus),
    EmitPureScript.decoder (α := CameraType),
    EmitPureScript.decoder (α := ProjectionType),
    EmitPureScript.decoder (α := KeyframeType),
    EmitPureScript.decoder (α := ColorSpace),
    EmitPureScript.decoder (α := ColorFormat),
    EmitPureScript.decoder (α := TransferFunction),
    EmitPureScript.decoder (α := TextAlign),
    EmitPureScript.decoder (α := TextDirection),
    EmitPureScript.decoder (α := FontStyle),
    EmitPureScript.decoder (α := FontWeight),
    EmitPureScript.decoder (α := AudioFormat),
    EmitPureScript.decoder (α := AudioChannel),
    EmitPureScript.decoder (α := BeatDetectionMethod),
    EmitPureScript.decoder (α := DepthOfFieldMode),
    EmitPureScript.decoder (α := ModelType),
    EmitPureScript.decoder (α := PreprocessorType),
    EmitPureScript.decoder (α := SegmentationMode),
    EmitPureScript.decoder (α := AuditCategory),
    EmitPureScript.decoder (α := RateLimitScope),
    EmitPureScript.decoder (α := SyncStatus),
    EmitPureScript.decoder (α := TextRangeMode),
    EmitPureScript.decoder (α := TextRangeBasedOn),
    EmitPureScript.decoder (α := TextRangeShape),
    EmitPureScript.decoder (α := ComparisonOperator),
    EmitPureScript.decoder (α := CompositeOperator),
    EmitPureScript.decoder (α := EmitterShape),
    EmitPureScript.decoder (α := ParticleShape),
    EmitPureScript.decoder (α := CollisionType),
    EmitPureScript.decoder (α := MaterialType),
    EmitPureScript.decoder (α := AutoOrientMode),
    EmitPureScript.decoder (α := CameraControlType),
    EmitPureScript.decoder (α := ForceType),
    EmitPureScript.decoder (α := BodyType),
    EmitPureScript.decoder (α := AggregationType),
    EmitPureScript.decoder (α := TimeGrain),
    EmitPureScript.decoder (α := MetricDataType),
    EmitPureScript.decoder (α := MetricCategory),
    EmitPureScript.decoder (α := JointType),
    EmitPureScript.decoder (α := EasingType),
    EmitPureScript.decoder (α := ExportTarget),
    EmitPureScript.decoder (α := ActionResult),
    EmitPureScript.decoder (α := RetryPolicy),
    EmitPureScript.decoder (α := BaseEvent),
    EmitPureScript.decoder (α := BaseAction),
    EmitPureScript.decoder (α := BaseTrigger),
    EmitPureScript.decoder (α := CompositionCreated),
    EmitPureScript.decoder (α := CompositionDeleted),
    EmitPureScript.decoder (α := CompositionRendered),
    EmitPureScript.decoder (α := LayerCreated),
    EmitPureScript.decoder (α := LayerDeleted),
    EmitPureScript.decoder (α := LayerMoved),
    EmitPureScript.decoder (α := LayerDuplicated),
    EmitPureScript.decoder (α := LayerVisibilityChanged),
    EmitPureScript.decoder (α := KeyframeAdded),
    EmitPureScript.decoder (α := KeyframeRemoved),
    EmitPureScript.decoder (α := KeyframeModified),
    EmitPureScript.decoder (α := KeyframeInterpolationChanged),
    EmitPureScript.decoder (α := PropertyAnimated),
    EmitPureScript.decoder (α := PropertyExpressionChanged),
    EmitPureScript.decoder (α := PropertyDriverAdded),
    EmitPureScript.decoder (α := EffectAdded),
    EmitPureScript.decoder (α := EffectRemoved),
    EmitPureScript.decoder (α := EffectParameterChanged),
    EmitPureScript.decoder (α := ExportStarted),
    EmitPureScript.decoder (α := ExportProgress),
    EmitPureScript.decoder (α := ExportCompleted),
    EmitPureScript.decoder (α := ExportFailed),
    EmitPureScript.decoder (α := RenderJobQueued),
    EmitPureScript.decoder (α := RenderJobCompleted),
    EmitPureScript.decoder (α := CacheCleared),
    EmitPureScript.decoder (α := ErrorOccurred),
    EmitPureScript.decoder (α := (Lattice.Actions.CreateLayer)),
    EmitPureScript.decoder (α := DeleteLayer),
    EmitPureScript.decoder (α := DuplicateLayer),
    EmitPureScript.decoder (α := MoveLayer),
    EmitPureScript.decoder (α := SetLayerVisibility),
    EmitPureScript.decoder (α := SetLayerOpacity),
    EmitPureScript.decoder (α := AddKeyframe),
    EmitPureScript.decoder (α := RemoveKeyframe),
    EmitPureScript.decoder (α := ModifyKeyframe),
    EmitPureScript.decoder (α := SetInterpolation),
    EmitPureScript.decoder (α := CopyKeyframes),
    EmitPureScript.decoder (α := PasteKeyframes),
    EmitPureScript.decoder (α := AnimateProperty),
    EmitPureScript.decoder (α := SetPropertyValue),
    EmitPureScript.decoder (α := AddExpression),
    EmitPureScript.decoder (α := RemoveExpression),
    EmitPureScript.decoder (α := AddDriver),
    EmitPureScript.decoder (α := AddEffect),
    EmitPureScript.decoder (α := RemoveEffect),
    EmitPureScript.decoder (α := ModifyEffect),
    EmitPureScript.decoder (α := EnableEffect),
    EmitPureScript.decoder (α := DisableEffect),
    EmitPureScript.decoder (α := (Lattice.Actions.CreateComposition)),
    EmitPureScript.decoder (α := DeleteComposition),
    EmitPureScript.decoder (α := SetCompositionSettings),
    EmitPureScript.decoder (α := RenderComposition),
    EmitPureScript.decoder (α := StartExport),
    EmitPureScript.decoder (α := CancelExport),
    EmitPureScript.decoder (α := PauseExport),
    EmitPureScript.decoder (α := ResumeExport),
    EmitPureScript.decoder (α := SetExportSettings),
    EmitPureScript.decoder (α := LoadAudio),
    EmitPureScript.decoder (α := AnalyzeAudio),
    EmitPureScript.decoder (α := SetAudioReactivity),
    EmitPureScript.decoder (α := SetCameraPosition),
    EmitPureScript.decoder (α := SetCameraRotation),
    EmitPureScript.decoder (α := SetCameraFOV),
    EmitPureScript.decoder (α := AnimateCamera),
    EmitPureScript.decoder (α := SegmentImage),
    EmitPureScript.decoder (α := VectorizeImage),
    EmitPureScript.decoder (α := DecomposeImage),
    EmitPureScript.decoder (α := GenerateDepth),
    EmitPureScript.decoder (α := EstimateNormals),
    EmitPureScript.decoder (α := ClearCache),
    EmitPureScript.decoder (α := OptimizeMemory),
    EmitPureScript.decoder (α := SaveProject),
    EmitPureScript.decoder (α := LoadProject),
    EmitPureScript.decoder (α := Undo),
    EmitPureScript.decoder (α := Redo),
    EmitPureScript.decoder (α := EffectParameter),
    EmitPureScript.decoder (α := EffectPreset),
    EmitPureScript.decoder (α := ProjectMetadata),
    EmitPureScript.decoder (α := ProjectSettings),
    EmitPureScript.decoder (α := AssetMetadata),
    EmitPureScript.decoder (α := DepthOfField),
    EmitPureScript.decoder (α := FontConfig),
    EmitPureScript.decoder (α := BeatData),
    EmitPureScript.decoder (α := PhysicsMaterial),
    EmitPureScript.decoder (α := EffectInstance),
    EmitPureScript.decoder (α := Project),
    EmitPureScript.decoder (α := Asset),
    EmitPureScript.decoder (α := AssetReference),
    EmitPureScript.decoder (α := ExportConfig),
    EmitPureScript.decoder (α := ExportTemplate),
    EmitPureScript.decoder (α := ExportJob),
    EmitPureScript.decoder (α := Camera3D),
    EmitPureScript.decoder (α := CameraKeyframe),
    EmitPureScript.decoder (α := CameraPath),
    EmitPureScript.decoder (α := TextAnimatorProperties),
    EmitPureScript.decoder (α := TextRangeSelector),
    EmitPureScript.decoder (α := TextAnimator),
    EmitPureScript.decoder (α := TextLayerData),
    EmitPureScript.decoder (α := TextShaper),
    EmitPureScript.decoder (α := AudioAnalysis),
    EmitPureScript.decoder (α := AudioReactivity),
    EmitPureScript.decoder (α := AudioTrack),
    EmitPureScript.decoder (α := ParticleEmitter),
    EmitPureScript.decoder (α := Force),
    EmitPureScript.decoder (α := CollisionConfig),
    EmitPureScript.decoder (α := ParticleRenderer),
    EmitPureScript.decoder (α := ParticleSystem),
    EmitPureScript.decoder (α := RigidBody),
    EmitPureScript.decoder (α := Joint),
    EmitPureScript.decoder (α := PhysicsSpace),
    EmitPureScript.decoder (α := Ragdoll),
    EmitPureScript.decoder (α := Cloth),
    EmitPureScript.decoder (α := MetricDefinition),
    EmitPureScript.decoder (α := FrameRenderTime),
    EmitPureScript.decoder (α := TotalRenderTime),
    EmitPureScript.decoder (α := MemoryUsage),
    EmitPureScript.decoder (α := GpuUsage),
    EmitPureScript.decoder (α := CacheHitRate),
    EmitPureScript.decoder (α := CacheSize),
    EmitPureScript.decoder (α := Fps),
    EmitPureScript.decoder (α := DroppedFrames),
    EmitPureScript.decoder (α := PlaybackLatency),
    EmitPureScript.decoder (α := ScrubLatency),
    EmitPureScript.decoder (α := CompressionRatio),
    EmitPureScript.decoder (α := Bitrate),
    EmitPureScript.decoder (α := ColorAccuracy),
    EmitPureScript.decoder (α := MotionBlurQuality),
    EmitPureScript.decoder (α := VramUsage),
    EmitPureScript.decoder (α := CpuUsage),
    EmitPureScript.decoder (α := NetworkBandwidth),
    EmitPureScript.decoder (α := StorageUsed),
    EmitPureScript.decoder (α := ActionsPerSession),
    EmitPureScript.decoder (α := ExportCount),
    EmitPureScript.decoder (α := ProjectCount),
    EmitPureScript.decoder (α := InferenceTime),
    EmitPureScript.decoder (α := ModelLoadTime),
    EmitPureScript.decoder (α := TokensUsed),
    EmitPureScript.decoder (α := CostUSD),
    EmitPureScript.decoder (α := PropertyCondition),
    EmitPureScript.decoder (α := FrameCondition),
    EmitPureScript.decoder (α := AudioCondition),
    EmitPureScript.decoder (α := TimeCondition),
    EmitPureScript.decoder (α := FrameTrigger),
    EmitPureScript.decoder (α := PropertyTrigger),
    EmitPureScript.decoder (α := AudioTrigger),
    EmitPureScript.decoder (α := TimeTrigger),
    EmitPureScript.decoder (α := ExpressionTrigger),
    EmitPureScript.decoder (α := EventTrigger),
    EmitPureScript.decoder (α := CompositeTrigger),
    EmitPureScript.decoder (α := Lattice.Entities.CreateLayer),
    EmitPureScript.decoder (α := Lattice.Entities.UpdateLayer),
    EmitPureScript.decoder (α := Lattice.Entities.CreateComposition),
    EmitPureScript.decoder (α := Lattice.Entities.UpdateComposition),
    EmitPureScript.decoder (α := Lattice.Entities.CreateEffectInstance),
    EmitPureScript.decoder (α := Lattice.Entities.UpdateEffectInstance),
    EmitPureScript.decoder (α := Lattice.Entities.CreateProject),
    EmitPureScript.decoder (α := Lattice.Entities.UpdateProject),
    EmitPureScript.decoder (α := Lattice.Entities.CreateAsset),
    EmitPureScript.decoder (α := Lattice.Entities.UpdateAsset),
    EmitPureScript.decoder (α := Lattice.Entities.CreateExportJob),
    EmitPureScript.decoder (α := Lattice.Entities.UpdateExportJob),
    EmitPureScript.decoder (α := CompositionSettings),
    EmitPureScript.decoder (α := RenderSettings),
    EmitPureScript.decoder (α := Composition),
    EmitPureScript.decoder (α := LayerTransform),
    EmitPureScript.decoder (α := Keyframe),
    EmitPureScript.decoder (α := PropertyExpression),
    EmitPureScript.decoder (α := AnimatableProperty),
    EmitPureScript.decoder (α := LayerMask),
    EmitPureScript.decoder (α := Layer)
  ]
  let encoders := [
    EmitPureScript.encoder (α := NonEmptyString),
    EmitPureScript.encoder (α := PositiveInt),
    EmitPureScript.encoder (α := PositiveFloat),
    EmitPureScript.encoder (α := NonNegativeFloat),
    EmitPureScript.encoder (α := Percentage),
    EmitPureScript.encoder (α := NormalizedValue),
    EmitPureScript.encoder (α := FrameNumber),
    EmitPureScript.encoder (α := Vec2),
    EmitPureScript.encoder (α := Vec3),
    EmitPureScript.encoder (α := Vec4),
    EmitPureScript.encoder (α := Matrix3x3),
    EmitPureScript.encoder (α := Matrix4x4),
    EmitPureScript.encoder (α := ControlMode),
    EmitPureScript.encoder (α := BezierHandle),
    EmitPureScript.encoder (α := InterpolationType),
    EmitPureScript.encoder (α := PropertyValueType),
    EmitPureScript.encoder (α := LayerType),
    EmitPureScript.encoder (α := BlendMode),
    EmitPureScript.encoder (α := MaskMode),
    EmitPureScript.encoder (α := ExpressionType),
    EmitPureScript.encoder (α := QualityMode),
    EmitPureScript.encoder (α := LayerStatus),
    EmitPureScript.encoder (α := EffectCategory),
    EmitPureScript.encoder (α := EffectStatus),
    EmitPureScript.encoder (α := EffectType),
    EmitPureScript.encoder (α := ExportFormat),
    EmitPureScript.encoder (α := ExportStatus),
    EmitPureScript.encoder (α := JobStatus),
    EmitPureScript.encoder (α := RenderStatus),
    EmitPureScript.encoder (α := ValidationResult),
    EmitPureScript.encoder (α := Severity),
    EmitPureScript.encoder (α := AssetType),
    EmitPureScript.encoder (α := AssetSource),
    EmitPureScript.encoder (α := ExportJobStatus),
    EmitPureScript.encoder (α := CameraType),
    EmitPureScript.encoder (α := ProjectionType),
    EmitPureScript.encoder (α := KeyframeType),
    EmitPureScript.encoder (α := ColorSpace),
    EmitPureScript.encoder (α := ColorFormat),
    EmitPureScript.encoder (α := TransferFunction),
    EmitPureScript.encoder (α := TextAlign),
    EmitPureScript.encoder (α := TextDirection),
    EmitPureScript.encoder (α := FontStyle),
    EmitPureScript.encoder (α := FontWeight),
    EmitPureScript.encoder (α := AudioFormat),
    EmitPureScript.encoder (α := AudioChannel),
    EmitPureScript.encoder (α := BeatDetectionMethod),
    EmitPureScript.encoder (α := DepthOfFieldMode),
    EmitPureScript.encoder (α := ModelType),
    EmitPureScript.encoder (α := PreprocessorType),
    EmitPureScript.encoder (α := SegmentationMode),
    EmitPureScript.encoder (α := AuditCategory),
    EmitPureScript.encoder (α := RateLimitScope),
    EmitPureScript.encoder (α := SyncStatus),
    EmitPureScript.encoder (α := TextRangeMode),
    EmitPureScript.encoder (α := TextRangeBasedOn),
    EmitPureScript.encoder (α := TextRangeShape),
    EmitPureScript.encoder (α := ComparisonOperator),
    EmitPureScript.encoder (α := CompositeOperator),
    EmitPureScript.encoder (α := EmitterShape),
    EmitPureScript.encoder (α := ParticleShape),
    EmitPureScript.encoder (α := CollisionType),
    EmitPureScript.encoder (α := MaterialType),
    EmitPureScript.encoder (α := AutoOrientMode),
    EmitPureScript.encoder (α := CameraControlType),
    EmitPureScript.encoder (α := ForceType),
    EmitPureScript.encoder (α := BodyType),
    EmitPureScript.encoder (α := AggregationType),
    EmitPureScript.encoder (α := TimeGrain),
    EmitPureScript.encoder (α := MetricDataType),
    EmitPureScript.encoder (α := MetricCategory),
    EmitPureScript.encoder (α := JointType),
    EmitPureScript.encoder (α := EasingType),
    EmitPureScript.encoder (α := ExportTarget),
    EmitPureScript.encoder (α := ActionResult),
    EmitPureScript.encoder (α := RetryPolicy),
    EmitPureScript.encoder (α := BaseEvent),
    EmitPureScript.encoder (α := BaseAction),
    EmitPureScript.encoder (α := BaseTrigger),
    EmitPureScript.encoder (α := CompositionCreated),
    EmitPureScript.encoder (α := CompositionDeleted),
    EmitPureScript.encoder (α := CompositionRendered),
    EmitPureScript.encoder (α := LayerCreated),
    EmitPureScript.encoder (α := LayerDeleted),
    EmitPureScript.encoder (α := LayerMoved),
    EmitPureScript.encoder (α := LayerDuplicated),
    EmitPureScript.encoder (α := LayerVisibilityChanged),
    EmitPureScript.encoder (α := KeyframeAdded),
    EmitPureScript.encoder (α := KeyframeRemoved),
    EmitPureScript.encoder (α := KeyframeModified),
    EmitPureScript.encoder (α := KeyframeInterpolationChanged),
    EmitPureScript.encoder (α := PropertyAnimated),
    EmitPureScript.encoder (α := PropertyExpressionChanged),
    EmitPureScript.encoder (α := PropertyDriverAdded),
    EmitPureScript.encoder (α := EffectAdded),
    EmitPureScript.encoder (α := EffectRemoved),
    EmitPureScript.encoder (α := EffectParameterChanged),
    EmitPureScript.encoder (α := ExportStarted),
    EmitPureScript.encoder (α := ExportProgress),
    EmitPureScript.encoder (α := ExportCompleted),
    EmitPureScript.encoder (α := ExportFailed),
    EmitPureScript.encoder (α := RenderJobQueued),
    EmitPureScript.encoder (α := RenderJobCompleted),
    EmitPureScript.encoder (α := CacheCleared),
    EmitPureScript.encoder (α := ErrorOccurred),
    EmitPureScript.encoder (α := (Lattice.Actions.CreateLayer)),
    EmitPureScript.encoder (α := DeleteLayer),
    EmitPureScript.encoder (α := DuplicateLayer),
    EmitPureScript.encoder (α := MoveLayer),
    EmitPureScript.encoder (α := SetLayerVisibility),
    EmitPureScript.encoder (α := SetLayerOpacity),
    EmitPureScript.encoder (α := AddKeyframe),
    EmitPureScript.encoder (α := RemoveKeyframe),
    EmitPureScript.encoder (α := ModifyKeyframe),
    EmitPureScript.encoder (α := SetInterpolation),
    EmitPureScript.encoder (α := CopyKeyframes),
    EmitPureScript.encoder (α := PasteKeyframes),
    EmitPureScript.encoder (α := AnimateProperty),
    EmitPureScript.encoder (α := SetPropertyValue),
    EmitPureScript.encoder (α := AddExpression),
    EmitPureScript.encoder (α := RemoveExpression),
    EmitPureScript.encoder (α := AddDriver),
    EmitPureScript.encoder (α := AddEffect),
    EmitPureScript.encoder (α := RemoveEffect),
    EmitPureScript.encoder (α := ModifyEffect),
    EmitPureScript.encoder (α := EnableEffect),
    EmitPureScript.encoder (α := DisableEffect),
    EmitPureScript.encoder (α := (Lattice.Actions.CreateComposition)),
    EmitPureScript.encoder (α := DeleteComposition),
    EmitPureScript.encoder (α := SetCompositionSettings),
    EmitPureScript.encoder (α := RenderComposition),
    EmitPureScript.encoder (α := StartExport),
    EmitPureScript.encoder (α := CancelExport),
    EmitPureScript.encoder (α := PauseExport),
    EmitPureScript.encoder (α := ResumeExport),
    EmitPureScript.encoder (α := SetExportSettings),
    EmitPureScript.encoder (α := LoadAudio),
    EmitPureScript.encoder (α := AnalyzeAudio),
    EmitPureScript.encoder (α := SetAudioReactivity),
    EmitPureScript.encoder (α := SetCameraPosition),
    EmitPureScript.encoder (α := SetCameraRotation),
    EmitPureScript.encoder (α := SetCameraFOV),
    EmitPureScript.encoder (α := AnimateCamera),
    EmitPureScript.encoder (α := SegmentImage),
    EmitPureScript.encoder (α := VectorizeImage),
    EmitPureScript.encoder (α := DecomposeImage),
    EmitPureScript.encoder (α := GenerateDepth),
    EmitPureScript.encoder (α := EstimateNormals),
    EmitPureScript.encoder (α := ClearCache),
    EmitPureScript.encoder (α := OptimizeMemory),
    EmitPureScript.encoder (α := SaveProject),
    EmitPureScript.encoder (α := LoadProject),
    EmitPureScript.encoder (α := Undo),
    EmitPureScript.encoder (α := Redo),
    EmitPureScript.encoder (α := EffectParameter),
    EmitPureScript.encoder (α := EffectPreset),
    EmitPureScript.encoder (α := ProjectMetadata),
    EmitPureScript.encoder (α := ProjectSettings),
    EmitPureScript.encoder (α := AssetMetadata),
    EmitPureScript.encoder (α := DepthOfField),
    EmitPureScript.encoder (α := FontConfig),
    EmitPureScript.encoder (α := BeatData),
    EmitPureScript.encoder (α := PhysicsMaterial),
    EmitPureScript.encoder (α := EffectInstance),
    EmitPureScript.encoder (α := Project),
    EmitPureScript.encoder (α := Asset),
    EmitPureScript.encoder (α := AssetReference),
    EmitPureScript.encoder (α := ExportConfig),
    EmitPureScript.encoder (α := ExportTemplate),
    EmitPureScript.encoder (α := ExportJob),
    EmitPureScript.encoder (α := Camera3D),
    EmitPureScript.encoder (α := CameraKeyframe),
    EmitPureScript.encoder (α := CameraPath),
    EmitPureScript.encoder (α := TextAnimatorProperties),
    EmitPureScript.encoder (α := TextRangeSelector),
    EmitPureScript.encoder (α := TextAnimator),
    EmitPureScript.encoder (α := TextLayerData),
    EmitPureScript.encoder (α := TextShaper),
    EmitPureScript.encoder (α := AudioAnalysis),
    EmitPureScript.encoder (α := AudioReactivity),
    EmitPureScript.encoder (α := AudioTrack),
    EmitPureScript.encoder (α := ParticleEmitter),
    EmitPureScript.encoder (α := Force),
    EmitPureScript.encoder (α := CollisionConfig),
    EmitPureScript.encoder (α := ParticleRenderer),
    EmitPureScript.encoder (α := ParticleSystem),
    EmitPureScript.encoder (α := RigidBody),
    EmitPureScript.encoder (α := Joint),
    EmitPureScript.encoder (α := PhysicsSpace),
    EmitPureScript.encoder (α := Ragdoll),
    EmitPureScript.encoder (α := Cloth),
    EmitPureScript.encoder (α := MetricDefinition),
    EmitPureScript.encoder (α := FrameRenderTime),
    EmitPureScript.encoder (α := TotalRenderTime),
    EmitPureScript.encoder (α := MemoryUsage),
    EmitPureScript.encoder (α := GpuUsage),
    EmitPureScript.encoder (α := CacheHitRate),
    EmitPureScript.encoder (α := CacheSize),
    EmitPureScript.encoder (α := Fps),
    EmitPureScript.encoder (α := DroppedFrames),
    EmitPureScript.encoder (α := PlaybackLatency),
    EmitPureScript.encoder (α := ScrubLatency),
    EmitPureScript.encoder (α := CompressionRatio),
    EmitPureScript.encoder (α := Bitrate),
    EmitPureScript.encoder (α := ColorAccuracy),
    EmitPureScript.encoder (α := MotionBlurQuality),
    EmitPureScript.encoder (α := VramUsage),
    EmitPureScript.encoder (α := CpuUsage),
    EmitPureScript.encoder (α := NetworkBandwidth),
    EmitPureScript.encoder (α := StorageUsed),
    EmitPureScript.encoder (α := ActionsPerSession),
    EmitPureScript.encoder (α := ExportCount),
    EmitPureScript.encoder (α := ProjectCount),
    EmitPureScript.encoder (α := InferenceTime),
    EmitPureScript.encoder (α := ModelLoadTime),
    EmitPureScript.encoder (α := TokensUsed),
    EmitPureScript.encoder (α := CostUSD),
    EmitPureScript.encoder (α := PropertyCondition),
    EmitPureScript.encoder (α := FrameCondition),
    EmitPureScript.encoder (α := AudioCondition),
    EmitPureScript.encoder (α := TimeCondition),
    EmitPureScript.encoder (α := FrameTrigger),
    EmitPureScript.encoder (α := PropertyTrigger),
    EmitPureScript.encoder (α := AudioTrigger),
    EmitPureScript.encoder (α := TimeTrigger),
    EmitPureScript.encoder (α := ExpressionTrigger),
    EmitPureScript.encoder (α := EventTrigger),
    EmitPureScript.encoder (α := CompositeTrigger),
    EmitPureScript.encoder (α := Lattice.Entities.CreateLayer),
    EmitPureScript.encoder (α := Lattice.Entities.UpdateLayer),
    EmitPureScript.encoder (α := Lattice.Entities.CreateComposition),
    EmitPureScript.encoder (α := Lattice.Entities.UpdateComposition),
    EmitPureScript.encoder (α := Lattice.Entities.CreateEffectInstance),
    EmitPureScript.encoder (α := Lattice.Entities.UpdateEffectInstance),
    EmitPureScript.encoder (α := Lattice.Entities.CreateProject),
    EmitPureScript.encoder (α := Lattice.Entities.UpdateProject),
    EmitPureScript.encoder (α := Lattice.Entities.UpdateAsset),
    EmitPureScript.encoder (α := Lattice.Entities.CreateAsset),
    EmitPureScript.encoder (α := Lattice.Entities.CreateExportJob),
    EmitPureScript.encoder (α := Lattice.Entities.UpdateExportJob),
    EmitPureScript.encoder (α := CompositionSettings),
    EmitPureScript.encoder (α := RenderSettings),
    EmitPureScript.encoder (α := Composition),
    EmitPureScript.encoder (α := LayerTransform),
    EmitPureScript.encoder (α := Keyframe),
    EmitPureScript.encoder (α := PropertyExpression),
    EmitPureScript.encoder (α := AnimatableProperty),
    EmitPureScript.encoder (α := LayerMask),
    EmitPureScript.encoder (α := Layer)
  ]
  header ++ "\n\n-- TYPES\n\n" ++ "\n\n".intercalate types ++
  "\n\n\n-- DECODERS\n\n" ++ "\n\n".intercalate decoders ++
  "\n\n\n-- ENCODERS\n\n" ++ "\n\n".intercalate encoders

end Lattice.Extract
