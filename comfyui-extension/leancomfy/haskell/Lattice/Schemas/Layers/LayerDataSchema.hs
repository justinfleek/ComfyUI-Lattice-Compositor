{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Layers.LayerDataSchema
Description : Layer data type enums
Copyright   : (c) Lattice, 2026
License     : MIT

Enums for all layer-specific data types.

Source: ui/src/schemas/layers/layer-data-schema.ts
-}

module Lattice.Schemas.Layers.LayerDataSchema
  ( -- * Image Layer
    ImageFitMode(..), imageFitModeFromText, imageFitModeToText
  , ImageSourceType(..), imageSourceTypeFromText
    -- * Video Layer
  , TimewarpMethod(..), timewarpMethodFromText
  , FrameBlending(..), frameBlendingFromText
    -- * Depth Layer
  , DepthVisualizationMode(..), depthVisualizationModeFromText
  , DepthColorMap(..), depthColorMapFromText
    -- * Normal Layer
  , NormalVisualizationMode(..), normalVisualizationModeFromText
  , NormalFormat(..), normalFormatFromText
    -- * Generated Layer
  , GenerationType(..), generationTypeFromText
  , GenerationStatus(..), generationStatusFromText
    -- * Control Layer
  , IconShape(..), iconShapeFromText
    -- * Camera Layer
  , CameraType(..), cameraTypeFromText
  , CameraLookMode(..), cameraLookModeFromText
  , CameraShakeType(..), cameraShakeTypeFromText
  , RackFocusEasing(..), rackFocusEasingFromText
  , AutoFocusMode(..), autoFocusModeFromText
    -- * Light Layer
  , LightType(..), lightTypeFromText
  , LightFalloff(..), lightFalloffFromText
    -- * Pose Layer
  , PoseFormat(..), poseFormatFromText
    -- * Model Layer
  , ModelType(..), modelTypeFromText
    -- * Point Cloud Layer
  , PointCloudFormat(..), pointCloudFormatFromText
  , PointCloudColorMode(..), pointCloudColorModeFromText
    -- * Matte Layer
  , MatteType(..), matteTypeFromText
  , MattePreviewMode(..), mattePreviewModeFromText
    -- * Procedural Matte
  , ProceduralMatteType(..), proceduralMatteTypeFromText
  , WaveType(..), waveTypeFromText
    -- * Depthflow Layer
  , DepthflowPreset(..), depthflowPresetFromText
    -- * Generated Map
  , GeneratedMapType(..), generatedMapTypeFromText
    -- * Spline/Path
  , ControlPointType(..), controlPointTypeFromText
  , GradientType(..), gradientTypeFromText
  , SplinePathEffectType(..), splinePathEffectTypeFromText
  , LineJoin(..), lineJoinFromText
  , LineCap(..), lineCapFromText
  , ZigZagPointType(..), zigZagPointTypeFromText
  , SplineLODMode(..), splineLODModeFromText
  , StrokeType(..), strokeTypeFromText
    -- * Text Layer
  , TextAlign(..), textAlignFromText
  , TextBaseline(..), textBaselineFromText
  , TextDirection(..), textDirectionFromText
  , TextFontStyle(..), textFontStyleFromText
  , TextRangeSelectorMode(..), textRangeSelectorModeFromText
  , TextBasedOn(..), textBasedOnFromText
  , TextSelectorShape(..), textSelectorShapeFromText
  , TextSelectorMode(..), textSelectorModeFromText
  , TextAnchorGrouping(..), textAnchorGroupingFromText
  , TextFillAndStroke(..), textFillAndStrokeFromText
  , TextCase(..), textCaseFromText
  , TextVerticalAlign(..), textVerticalAlignFromText
    -- * Particle Layer
  , EmitterShape(..), emitterShapeFromText
  , SpritePlayMode(..), spritePlayModeFromText
  , SplineEmitMode(..), splineEmitModeFromText
  , DepthMode(..), depthModeFromText
  , MaskChannel(..), maskChannelFromText
  , ForceFalloff(..), forceFalloffFromText
  , ModulationProperty(..), modulationPropertyFromText
  , BoundaryBehavior(..), boundaryBehaviorFromText
  , FloorBehavior(..), floorBehaviorFromText
  , AudioFeature(..), audioFeatureFromText
  , AudioBindingTarget(..), audioBindingTargetFromText
  , AudioBindingCurve(..), audioBindingCurveFromText
  , AudioTriggerMode(..), audioTriggerModeFromText
  , ParticleBlendMode(..), particleBlendModeFromText
  , ParticleShape(..), particleShapeFromText
  , MeshMode(..), meshModeFromText
  , MeshGeometry(..), meshGeometryFromText
  , SpringStructureType(..), springStructureTypeFromText
  , SPHFluidPreset(..), sphFluidPresetFromText
  , InterCharacterBlending(..), interCharacterBlendingFromText
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

--------------------------------------------------------------------------------
-- Image Layer
--------------------------------------------------------------------------------

data ImageFitMode = FitNone | FitContain | FitCover | FitFill
  deriving stock (Eq, Show, Generic, Enum, Bounded)

imageFitModeFromText :: Text -> Maybe ImageFitMode
imageFitModeFromText "none" = Just FitNone
imageFitModeFromText "contain" = Just FitContain
imageFitModeFromText "cover" = Just FitCover
imageFitModeFromText "fill" = Just FitFill
imageFitModeFromText _ = Nothing

imageFitModeToText :: ImageFitMode -> Text
imageFitModeToText FitNone = "none"
imageFitModeToText FitContain = "contain"
imageFitModeToText FitCover = "cover"
imageFitModeToText FitFill = "fill"

data ImageSourceType = SourceFile | SourceGenerated | SourceSegmented
  deriving stock (Eq, Show, Generic, Enum, Bounded)

imageSourceTypeFromText :: Text -> Maybe ImageSourceType
imageSourceTypeFromText "file" = Just SourceFile
imageSourceTypeFromText "generated" = Just SourceGenerated
imageSourceTypeFromText "segmented" = Just SourceSegmented
imageSourceTypeFromText _ = Nothing

--------------------------------------------------------------------------------
-- Video Layer
--------------------------------------------------------------------------------

data TimewarpMethod = TwWholeFrames | TwFrameMix | TwPixelMotion
  deriving stock (Eq, Show, Generic, Enum, Bounded)

timewarpMethodFromText :: Text -> Maybe TimewarpMethod
timewarpMethodFromText "whole-frames" = Just TwWholeFrames
timewarpMethodFromText "frame-mix" = Just TwFrameMix
timewarpMethodFromText "pixel-motion" = Just TwPixelMotion
timewarpMethodFromText _ = Nothing

data FrameBlending = FbNone | FbFrameMix | FbPixelMotion
  deriving stock (Eq, Show, Generic, Enum, Bounded)

frameBlendingFromText :: Text -> Maybe FrameBlending
frameBlendingFromText "none" = Just FbNone
frameBlendingFromText "frame-mix" = Just FbFrameMix
frameBlendingFromText "pixel-motion" = Just FbPixelMotion
frameBlendingFromText _ = Nothing

--------------------------------------------------------------------------------
-- Depth Layer
--------------------------------------------------------------------------------

data DepthVisualizationMode = DepthGrayscale | DepthColormap | DepthContour | DepthMesh3d
  deriving stock (Eq, Show, Generic, Enum, Bounded)

depthVisualizationModeFromText :: Text -> Maybe DepthVisualizationMode
depthVisualizationModeFromText "grayscale" = Just DepthGrayscale
depthVisualizationModeFromText "colormap" = Just DepthColormap
depthVisualizationModeFromText "contour" = Just DepthContour
depthVisualizationModeFromText "3d-mesh" = Just DepthMesh3d
depthVisualizationModeFromText _ = Nothing

data DepthColorMap = CmTurbo | CmViridis | CmPlasma | CmInferno | CmMagma | CmGrayscale
  deriving stock (Eq, Show, Generic, Enum, Bounded)

depthColorMapFromText :: Text -> Maybe DepthColorMap
depthColorMapFromText "turbo" = Just CmTurbo
depthColorMapFromText "viridis" = Just CmViridis
depthColorMapFromText "plasma" = Just CmPlasma
depthColorMapFromText "inferno" = Just CmInferno
depthColorMapFromText "magma" = Just CmMagma
depthColorMapFromText "grayscale" = Just CmGrayscale
depthColorMapFromText _ = Nothing

--------------------------------------------------------------------------------
-- Normal Layer
--------------------------------------------------------------------------------

data NormalVisualizationMode = NormRgb | NormHemisphere | NormArrows | NormLit
  deriving stock (Eq, Show, Generic, Enum, Bounded)

normalVisualizationModeFromText :: Text -> Maybe NormalVisualizationMode
normalVisualizationModeFromText "rgb" = Just NormRgb
normalVisualizationModeFromText "hemisphere" = Just NormHemisphere
normalVisualizationModeFromText "arrows" = Just NormArrows
normalVisualizationModeFromText "lit" = Just NormLit
normalVisualizationModeFromText _ = Nothing

data NormalFormat = NfOpenGL | NfDirectX
  deriving stock (Eq, Show, Generic, Enum, Bounded)

normalFormatFromText :: Text -> Maybe NormalFormat
normalFormatFromText "opengl" = Just NfOpenGL
normalFormatFromText "directx" = Just NfDirectX
normalFormatFromText _ = Nothing

--------------------------------------------------------------------------------
-- Generated Layer
--------------------------------------------------------------------------------

data GenerationType = GenDepth | GenNormal | GenEdge | GenSegment | GenInpaint | GenCustom
  deriving stock (Eq, Show, Generic, Enum, Bounded)

generationTypeFromText :: Text -> Maybe GenerationType
generationTypeFromText "depth" = Just GenDepth
generationTypeFromText "normal" = Just GenNormal
generationTypeFromText "edge" = Just GenEdge
generationTypeFromText "segment" = Just GenSegment
generationTypeFromText "inpaint" = Just GenInpaint
generationTypeFromText "custom" = Just GenCustom
generationTypeFromText _ = Nothing

data GenerationStatus = StatusPending | StatusGenerating | StatusComplete | StatusError
  deriving stock (Eq, Show, Generic, Enum, Bounded)

generationStatusFromText :: Text -> Maybe GenerationStatus
generationStatusFromText "pending" = Just StatusPending
generationStatusFromText "generating" = Just StatusGenerating
generationStatusFromText "complete" = Just StatusComplete
generationStatusFromText "error" = Just StatusError
generationStatusFromText _ = Nothing

--------------------------------------------------------------------------------
-- Control Layer
--------------------------------------------------------------------------------

data IconShape = IconCrosshair | IconDiamond | IconCircle | IconSquare
  deriving stock (Eq, Show, Generic, Enum, Bounded)

iconShapeFromText :: Text -> Maybe IconShape
iconShapeFromText "crosshair" = Just IconCrosshair
iconShapeFromText "diamond" = Just IconDiamond
iconShapeFromText "circle" = Just IconCircle
iconShapeFromText "square" = Just IconSquare
iconShapeFromText _ = Nothing

--------------------------------------------------------------------------------
-- Camera Layer
--------------------------------------------------------------------------------

data CameraType = CamOneNode | CamTwoNode
  deriving stock (Eq, Show, Generic, Enum, Bounded)

cameraTypeFromText :: Text -> Maybe CameraType
cameraTypeFromText "one-node" = Just CamOneNode
cameraTypeFromText "two-node" = Just CamTwoNode
cameraTypeFromText _ = Nothing

data CameraLookMode = LookTangent | LookTarget | LookFixed
  deriving stock (Eq, Show, Generic, Enum, Bounded)

cameraLookModeFromText :: Text -> Maybe CameraLookMode
cameraLookModeFromText "tangent" = Just LookTangent
cameraLookModeFromText "target" = Just LookTarget
cameraLookModeFromText "fixed" = Just LookFixed
cameraLookModeFromText _ = Nothing

data CameraShakeType = ShakeHandheld | ShakeImpact | ShakeEarthquake | ShakeSubtle | ShakeCustom
  deriving stock (Eq, Show, Generic, Enum, Bounded)

cameraShakeTypeFromText :: Text -> Maybe CameraShakeType
cameraShakeTypeFromText "handheld" = Just ShakeHandheld
cameraShakeTypeFromText "impact" = Just ShakeImpact
cameraShakeTypeFromText "earthquake" = Just ShakeEarthquake
cameraShakeTypeFromText "subtle" = Just ShakeSubtle
cameraShakeTypeFromText "custom" = Just ShakeCustom
cameraShakeTypeFromText _ = Nothing

data RackFocusEasing = RfLinear | RfEaseIn | RfEaseOut | RfEaseInOut | RfSnap
  deriving stock (Eq, Show, Generic, Enum, Bounded)

rackFocusEasingFromText :: Text -> Maybe RackFocusEasing
rackFocusEasingFromText "linear" = Just RfLinear
rackFocusEasingFromText "ease-in" = Just RfEaseIn
rackFocusEasingFromText "ease-out" = Just RfEaseOut
rackFocusEasingFromText "ease-in-out" = Just RfEaseInOut
rackFocusEasingFromText "snap" = Just RfSnap
rackFocusEasingFromText _ = Nothing

data AutoFocusMode = AfCenter | AfPoint | AfNearest | AfFarthest
  deriving stock (Eq, Show, Generic, Enum, Bounded)

autoFocusModeFromText :: Text -> Maybe AutoFocusMode
autoFocusModeFromText "center" = Just AfCenter
autoFocusModeFromText "point" = Just AfPoint
autoFocusModeFromText "nearest" = Just AfNearest
autoFocusModeFromText "farthest" = Just AfFarthest
autoFocusModeFromText _ = Nothing

--------------------------------------------------------------------------------
-- Light Layer
--------------------------------------------------------------------------------

data LightType = LightPoint | LightSpot | LightDirectional | LightAmbient
  deriving stock (Eq, Show, Generic, Enum, Bounded)

lightTypeFromText :: Text -> Maybe LightType
lightTypeFromText "point" = Just LightPoint
lightTypeFromText "spot" = Just LightSpot
lightTypeFromText "directional" = Just LightDirectional
lightTypeFromText "ambient" = Just LightAmbient
lightTypeFromText _ = Nothing

data LightFalloff = FalloffNone | FalloffLinear | FalloffQuadratic | FalloffSmooth
  deriving stock (Eq, Show, Generic, Enum, Bounded)

lightFalloffFromText :: Text -> Maybe LightFalloff
lightFalloffFromText "none" = Just FalloffNone
lightFalloffFromText "linear" = Just FalloffLinear
lightFalloffFromText "quadratic" = Just FalloffQuadratic
lightFalloffFromText "smooth" = Just FalloffSmooth
lightFalloffFromText _ = Nothing

--------------------------------------------------------------------------------
-- Pose Layer
--------------------------------------------------------------------------------

data PoseFormat = PoseCoco18 | PoseBody25 | PoseCustom
  deriving stock (Eq, Show, Generic, Enum, Bounded)

poseFormatFromText :: Text -> Maybe PoseFormat
poseFormatFromText "coco18" = Just PoseCoco18
poseFormatFromText "body25" = Just PoseBody25
poseFormatFromText "custom" = Just PoseCustom
poseFormatFromText _ = Nothing

--------------------------------------------------------------------------------
-- Model Layer
--------------------------------------------------------------------------------

data ModelType = ModelGltf | ModelObj | ModelFbx | ModelUsd
  deriving stock (Eq, Show, Generic, Enum, Bounded)

modelTypeFromText :: Text -> Maybe ModelType
modelTypeFromText "gltf" = Just ModelGltf
modelTypeFromText "obj" = Just ModelObj
modelTypeFromText "fbx" = Just ModelFbx
modelTypeFromText "usd" = Just ModelUsd
modelTypeFromText _ = Nothing

--------------------------------------------------------------------------------
-- Point Cloud Layer
--------------------------------------------------------------------------------

data PointCloudFormat = PcPly | PcPcd | PcLas | PcXyz
  deriving stock (Eq, Show, Generic, Enum, Bounded)

pointCloudFormatFromText :: Text -> Maybe PointCloudFormat
pointCloudFormatFromText "ply" = Just PcPly
pointCloudFormatFromText "pcd" = Just PcPcd
pointCloudFormatFromText "las" = Just PcLas
pointCloudFormatFromText "xyz" = Just PcXyz
pointCloudFormatFromText _ = Nothing

data PointCloudColorMode = PcRgb | PcHeight | PcIntensity | PcClassification
  deriving stock (Eq, Show, Generic, Enum, Bounded)

pointCloudColorModeFromText :: Text -> Maybe PointCloudColorMode
pointCloudColorModeFromText "rgb" = Just PcRgb
pointCloudColorModeFromText "height" = Just PcHeight
pointCloudColorModeFromText "intensity" = Just PcIntensity
pointCloudColorModeFromText "classification" = Just PcClassification
pointCloudColorModeFromText _ = Nothing

--------------------------------------------------------------------------------
-- Matte Layer
--------------------------------------------------------------------------------

data MatteType = MatteLuminance | MatteAlpha | MatteRed | MatteGreen | MatteBlue | MatteHue | MatteSaturation
  deriving stock (Eq, Show, Generic, Enum, Bounded)

matteTypeFromText :: Text -> Maybe MatteType
matteTypeFromText "luminance" = Just MatteLuminance
matteTypeFromText "alpha" = Just MatteAlpha
matteTypeFromText "red" = Just MatteRed
matteTypeFromText "green" = Just MatteGreen
matteTypeFromText "blue" = Just MatteBlue
matteTypeFromText "hue" = Just MatteHue
matteTypeFromText "saturation" = Just MatteSaturation
matteTypeFromText _ = Nothing

data MattePreviewMode = PreviewMatte | PreviewComposite | PreviewOverlay
  deriving stock (Eq, Show, Generic, Enum, Bounded)

mattePreviewModeFromText :: Text -> Maybe MattePreviewMode
mattePreviewModeFromText "matte" = Just PreviewMatte
mattePreviewModeFromText "composite" = Just PreviewComposite
mattePreviewModeFromText "overlay" = Just PreviewOverlay
mattePreviewModeFromText _ = Nothing

--------------------------------------------------------------------------------
-- Procedural Matte
--------------------------------------------------------------------------------

data ProceduralMatteType
  = PmLinearGradient | PmRadialGradient | PmAngularGradient | PmRamp
  | PmNoise | PmCheckerboard | PmCircle | PmRectangle | PmGrid | PmWave
  | PmVenetianBlinds | PmIris | PmRadialWipe | PmDissolve
  deriving stock (Eq, Show, Generic, Enum, Bounded)

proceduralMatteTypeFromText :: Text -> Maybe ProceduralMatteType
proceduralMatteTypeFromText "linear_gradient" = Just PmLinearGradient
proceduralMatteTypeFromText "radial_gradient" = Just PmRadialGradient
proceduralMatteTypeFromText "angular_gradient" = Just PmAngularGradient
proceduralMatteTypeFromText "ramp" = Just PmRamp
proceduralMatteTypeFromText "noise" = Just PmNoise
proceduralMatteTypeFromText "checkerboard" = Just PmCheckerboard
proceduralMatteTypeFromText "circle" = Just PmCircle
proceduralMatteTypeFromText "rectangle" = Just PmRectangle
proceduralMatteTypeFromText "grid" = Just PmGrid
proceduralMatteTypeFromText "wave" = Just PmWave
proceduralMatteTypeFromText "venetian_blinds" = Just PmVenetianBlinds
proceduralMatteTypeFromText "iris" = Just PmIris
proceduralMatteTypeFromText "radial_wipe" = Just PmRadialWipe
proceduralMatteTypeFromText "dissolve" = Just PmDissolve
proceduralMatteTypeFromText _ = Nothing

data WaveType = WaveSine | WaveTriangle | WaveSquare | WaveSawtooth
  deriving stock (Eq, Show, Generic, Enum, Bounded)

waveTypeFromText :: Text -> Maybe WaveType
waveTypeFromText "sine" = Just WaveSine
waveTypeFromText "triangle" = Just WaveTriangle
waveTypeFromText "square" = Just WaveSquare
waveTypeFromText "sawtooth" = Just WaveSawtooth
waveTypeFromText _ = Nothing

--------------------------------------------------------------------------------
-- Depthflow Layer
--------------------------------------------------------------------------------

data DepthflowPreset
  = DfStatic | DfZoomIn | DfZoomOut | DfDollyZoomIn | DfDollyZoomOut
  | DfPanLeft | DfPanRight | DfPanUp | DfPanDown
  | DfCircleCW | DfCircleCCW | DfHorizontalSwing | DfVerticalSwing | DfCustom
  deriving stock (Eq, Show, Generic, Enum, Bounded)

depthflowPresetFromText :: Text -> Maybe DepthflowPreset
depthflowPresetFromText "static" = Just DfStatic
depthflowPresetFromText "zoom_in" = Just DfZoomIn
depthflowPresetFromText "zoom_out" = Just DfZoomOut
depthflowPresetFromText "dolly_zoom_in" = Just DfDollyZoomIn
depthflowPresetFromText "dolly_zoom_out" = Just DfDollyZoomOut
depthflowPresetFromText "pan_left" = Just DfPanLeft
depthflowPresetFromText "pan_right" = Just DfPanRight
depthflowPresetFromText "pan_up" = Just DfPanUp
depthflowPresetFromText "pan_down" = Just DfPanDown
depthflowPresetFromText "circle_cw" = Just DfCircleCW
depthflowPresetFromText "circle_ccw" = Just DfCircleCCW
depthflowPresetFromText "horizontal_swing" = Just DfHorizontalSwing
depthflowPresetFromText "vertical_swing" = Just DfVerticalSwing
depthflowPresetFromText "custom" = Just DfCustom
depthflowPresetFromText _ = Nothing

--------------------------------------------------------------------------------
-- Generated Map
--------------------------------------------------------------------------------

data GeneratedMapType = GmDepth | GmNormal | GmEdge | GmSegment | GmPose | GmFlow
  deriving stock (Eq, Show, Generic, Enum, Bounded)

generatedMapTypeFromText :: Text -> Maybe GeneratedMapType
generatedMapTypeFromText "depth" = Just GmDepth
generatedMapTypeFromText "normal" = Just GmNormal
generatedMapTypeFromText "edge" = Just GmEdge
generatedMapTypeFromText "segment" = Just GmSegment
generatedMapTypeFromText "pose" = Just GmPose
generatedMapTypeFromText "flow" = Just GmFlow
generatedMapTypeFromText _ = Nothing

--------------------------------------------------------------------------------
-- Spline/Path
--------------------------------------------------------------------------------

data ControlPointType = CpCorner | CpSmooth | CpSymmetric
  deriving stock (Eq, Show, Generic, Enum, Bounded)

controlPointTypeFromText :: Text -> Maybe ControlPointType
controlPointTypeFromText "corner" = Just CpCorner
controlPointTypeFromText "smooth" = Just CpSmooth
controlPointTypeFromText "symmetric" = Just CpSymmetric
controlPointTypeFromText _ = Nothing

data GradientType = GradLinear | GradRadial
  deriving stock (Eq, Show, Generic, Enum, Bounded)

gradientTypeFromText :: Text -> Maybe GradientType
gradientTypeFromText "linear" = Just GradLinear
gradientTypeFromText "radial" = Just GradRadial
gradientTypeFromText _ = Nothing

data SplinePathEffectType = SpeOffsetPath | SpeRoughen | SpeWiggle | SpeZigzag | SpeWave
  deriving stock (Eq, Show, Generic, Enum, Bounded)

splinePathEffectTypeFromText :: Text -> Maybe SplinePathEffectType
splinePathEffectTypeFromText "offsetPath" = Just SpeOffsetPath
splinePathEffectTypeFromText "roughen" = Just SpeRoughen
splinePathEffectTypeFromText "wiggle" = Just SpeWiggle
splinePathEffectTypeFromText "zigzag" = Just SpeZigzag
splinePathEffectTypeFromText "wave" = Just SpeWave
splinePathEffectTypeFromText _ = Nothing

data LineJoin = JoinMiter | JoinRound | JoinBevel
  deriving stock (Eq, Show, Generic, Enum, Bounded)

lineJoinFromText :: Text -> Maybe LineJoin
lineJoinFromText "miter" = Just JoinMiter
lineJoinFromText "round" = Just JoinRound
lineJoinFromText "bevel" = Just JoinBevel
lineJoinFromText _ = Nothing

data LineCap = CapButt | CapRound | CapSquare
  deriving stock (Eq, Show, Generic, Enum, Bounded)

lineCapFromText :: Text -> Maybe LineCap
lineCapFromText "butt" = Just CapButt
lineCapFromText "round" = Just CapRound
lineCapFromText "square" = Just CapSquare
lineCapFromText _ = Nothing

data ZigZagPointType = ZzCorner | ZzSmooth
  deriving stock (Eq, Show, Generic, Enum, Bounded)

zigZagPointTypeFromText :: Text -> Maybe ZigZagPointType
zigZagPointTypeFromText "corner" = Just ZzCorner
zigZagPointTypeFromText "smooth" = Just ZzSmooth
zigZagPointTypeFromText _ = Nothing

data SplineLODMode = LodZoom | LodPlayback | LodBoth
  deriving stock (Eq, Show, Generic, Enum, Bounded)

splineLODModeFromText :: Text -> Maybe SplineLODMode
splineLODModeFromText "zoom" = Just LodZoom
splineLODModeFromText "playback" = Just LodPlayback
splineLODModeFromText "both" = Just LodBoth
splineLODModeFromText _ = Nothing

data StrokeType = StrokeSolid | StrokeGradient
  deriving stock (Eq, Show, Generic, Enum, Bounded)

strokeTypeFromText :: Text -> Maybe StrokeType
strokeTypeFromText "solid" = Just StrokeSolid
strokeTypeFromText "gradient" = Just StrokeGradient
strokeTypeFromText _ = Nothing

--------------------------------------------------------------------------------
-- Text Layer
--------------------------------------------------------------------------------

data TextAlign = AlignLeft | AlignCenter | AlignRight
  deriving stock (Eq, Show, Generic, Enum, Bounded)

textAlignFromText :: Text -> Maybe TextAlign
textAlignFromText "left" = Just AlignLeft
textAlignFromText "center" = Just AlignCenter
textAlignFromText "right" = Just AlignRight
textAlignFromText _ = Nothing

data TextBaseline = BaselineTop | BaselineMiddle | BaselineBottom
  deriving stock (Eq, Show, Generic, Enum, Bounded)

textBaselineFromText :: Text -> Maybe TextBaseline
textBaselineFromText "top" = Just BaselineTop
textBaselineFromText "middle" = Just BaselineMiddle
textBaselineFromText "bottom" = Just BaselineBottom
textBaselineFromText _ = Nothing

data TextDirection = DirLtr | DirRtl
  deriving stock (Eq, Show, Generic, Enum, Bounded)

textDirectionFromText :: Text -> Maybe TextDirection
textDirectionFromText "ltr" = Just DirLtr
textDirectionFromText "rtl" = Just DirRtl
textDirectionFromText _ = Nothing

data TextFontStyle = StyleNormal | StyleItalic
  deriving stock (Eq, Show, Generic, Enum, Bounded)

textFontStyleFromText :: Text -> Maybe TextFontStyle
textFontStyleFromText "normal" = Just StyleNormal
textFontStyleFromText "italic" = Just StyleItalic
textFontStyleFromText _ = Nothing

data TextRangeSelectorMode = RsPercent | RsIndex
  deriving stock (Eq, Show, Generic, Enum, Bounded)

textRangeSelectorModeFromText :: Text -> Maybe TextRangeSelectorMode
textRangeSelectorModeFromText "percent" = Just RsPercent
textRangeSelectorModeFromText "index" = Just RsIndex
textRangeSelectorModeFromText _ = Nothing

data TextBasedOn = BoCharacters | BoCharactersExcludingSpaces | BoWords | BoLines
  deriving stock (Eq, Show, Generic, Enum, Bounded)

textBasedOnFromText :: Text -> Maybe TextBasedOn
textBasedOnFromText "characters" = Just BoCharacters
textBasedOnFromText "characters_excluding_spaces" = Just BoCharactersExcludingSpaces
textBasedOnFromText "words" = Just BoWords
textBasedOnFromText "lines" = Just BoLines
textBasedOnFromText _ = Nothing

data TextSelectorShape = ShapeSquare | ShapeRampUp | ShapeRampDown | ShapeTriangle | ShapeRound | ShapeSmooth
  deriving stock (Eq, Show, Generic, Enum, Bounded)

textSelectorShapeFromText :: Text -> Maybe TextSelectorShape
textSelectorShapeFromText "square" = Just ShapeSquare
textSelectorShapeFromText "ramp_up" = Just ShapeRampUp
textSelectorShapeFromText "ramp_down" = Just ShapeRampDown
textSelectorShapeFromText "triangle" = Just ShapeTriangle
textSelectorShapeFromText "round" = Just ShapeRound
textSelectorShapeFromText "smooth" = Just ShapeSmooth
textSelectorShapeFromText _ = Nothing

data TextSelectorMode = SmAdd | SmSubtract | SmIntersect | SmMin | SmMax | SmDifference
  deriving stock (Eq, Show, Generic, Enum, Bounded)

textSelectorModeFromText :: Text -> Maybe TextSelectorMode
textSelectorModeFromText "add" = Just SmAdd
textSelectorModeFromText "subtract" = Just SmSubtract
textSelectorModeFromText "intersect" = Just SmIntersect
textSelectorModeFromText "min" = Just SmMin
textSelectorModeFromText "max" = Just SmMax
textSelectorModeFromText "difference" = Just SmDifference
textSelectorModeFromText _ = Nothing

data TextAnchorGrouping = AgCharacter | AgWord | AgLine | AgAll
  deriving stock (Eq, Show, Generic, Enum, Bounded)

textAnchorGroupingFromText :: Text -> Maybe TextAnchorGrouping
textAnchorGroupingFromText "character" = Just AgCharacter
textAnchorGroupingFromText "word" = Just AgWord
textAnchorGroupingFromText "line" = Just AgLine
textAnchorGroupingFromText "all" = Just AgAll
textAnchorGroupingFromText _ = Nothing

data TextFillAndStroke = FillOverStroke | StrokeOverFill
  deriving stock (Eq, Show, Generic, Enum, Bounded)

textFillAndStrokeFromText :: Text -> Maybe TextFillAndStroke
textFillAndStrokeFromText "fill-over-stroke" = Just FillOverStroke
textFillAndStrokeFromText "stroke-over-fill" = Just StrokeOverFill
textFillAndStrokeFromText _ = Nothing

data TextCase = CaseNormal | CaseUppercase | CaseLowercase | CaseSmallCaps
  deriving stock (Eq, Show, Generic, Enum, Bounded)

textCaseFromText :: Text -> Maybe TextCase
textCaseFromText "normal" = Just CaseNormal
textCaseFromText "uppercase" = Just CaseUppercase
textCaseFromText "lowercase" = Just CaseLowercase
textCaseFromText "smallCaps" = Just CaseSmallCaps
textCaseFromText _ = Nothing

data TextVerticalAlign = VaNormal | VaSuperscript | VaSubscript
  deriving stock (Eq, Show, Generic, Enum, Bounded)

textVerticalAlignFromText :: Text -> Maybe TextVerticalAlign
textVerticalAlignFromText "normal" = Just VaNormal
textVerticalAlignFromText "superscript" = Just VaSuperscript
textVerticalAlignFromText "subscript" = Just VaSubscript
textVerticalAlignFromText _ = Nothing

--------------------------------------------------------------------------------
-- Particle Layer
--------------------------------------------------------------------------------

data EmitterShape
  = EsPoint | EsLine | EsCircle | EsBox | EsSphere | EsRing
  | EsSpline | EsDepthMap | EsMask | EsCone | EsImage | EsDepthEdge
  deriving stock (Eq, Show, Generic, Enum, Bounded)

emitterShapeFromText :: Text -> Maybe EmitterShape
emitterShapeFromText "point" = Just EsPoint
emitterShapeFromText "line" = Just EsLine
emitterShapeFromText "circle" = Just EsCircle
emitterShapeFromText "box" = Just EsBox
emitterShapeFromText "sphere" = Just EsSphere
emitterShapeFromText "ring" = Just EsRing
emitterShapeFromText "spline" = Just EsSpline
emitterShapeFromText "depth-map" = Just EsDepthMap
emitterShapeFromText "mask" = Just EsMask
emitterShapeFromText "cone" = Just EsCone
emitterShapeFromText "image" = Just EsImage
emitterShapeFromText "depthEdge" = Just EsDepthEdge
emitterShapeFromText _ = Nothing

data SpritePlayMode = SpLoop | SpOnce | SpPingpong | SpRandom
  deriving stock (Eq, Show, Generic, Enum, Bounded)

spritePlayModeFromText :: Text -> Maybe SpritePlayMode
spritePlayModeFromText "loop" = Just SpLoop
spritePlayModeFromText "once" = Just SpOnce
spritePlayModeFromText "pingpong" = Just SpPingpong
spritePlayModeFromText "random" = Just SpRandom
spritePlayModeFromText _ = Nothing

data SplineEmitMode = SeUniform | SeRandom | SeStart | SeEnd | SeSequential
  deriving stock (Eq, Show, Generic, Enum, Bounded)

splineEmitModeFromText :: Text -> Maybe SplineEmitMode
splineEmitModeFromText "uniform" = Just SeUniform
splineEmitModeFromText "random" = Just SeRandom
splineEmitModeFromText "start" = Just SeStart
splineEmitModeFromText "end" = Just SeEnd
splineEmitModeFromText "sequential" = Just SeSequential
splineEmitModeFromText _ = Nothing

data DepthMode = DmNearWhite | DmNearBlack
  deriving stock (Eq, Show, Generic, Enum, Bounded)

depthModeFromText :: Text -> Maybe DepthMode
depthModeFromText "near-white" = Just DmNearWhite
depthModeFromText "near-black" = Just DmNearBlack
depthModeFromText _ = Nothing

data MaskChannel = McLuminance | McAlpha | McRed | McGreen | McBlue
  deriving stock (Eq, Show, Generic, Enum, Bounded)

maskChannelFromText :: Text -> Maybe MaskChannel
maskChannelFromText "luminance" = Just McLuminance
maskChannelFromText "alpha" = Just McAlpha
maskChannelFromText "red" = Just McRed
maskChannelFromText "green" = Just McGreen
maskChannelFromText "blue" = Just McBlue
maskChannelFromText _ = Nothing

data ForceFalloff = FfLinear | FfQuadratic | FfConstant
  deriving stock (Eq, Show, Generic, Enum, Bounded)

forceFalloffFromText :: Text -> Maybe ForceFalloff
forceFalloffFromText "linear" = Just FfLinear
forceFalloffFromText "quadratic" = Just FfQuadratic
forceFalloffFromText "constant" = Just FfConstant
forceFalloffFromText _ = Nothing

data ModulationProperty = ModSize | ModSpeed | ModOpacity | ModColorR | ModColorG | ModColorB
  deriving stock (Eq, Show, Generic, Enum, Bounded)

modulationPropertyFromText :: Text -> Maybe ModulationProperty
modulationPropertyFromText "size" = Just ModSize
modulationPropertyFromText "speed" = Just ModSpeed
modulationPropertyFromText "opacity" = Just ModOpacity
modulationPropertyFromText "colorR" = Just ModColorR
modulationPropertyFromText "colorG" = Just ModColorG
modulationPropertyFromText "colorB" = Just ModColorB
modulationPropertyFromText _ = Nothing

data BoundaryBehavior = BbNone | BbKill | BbBounce | BbWrap | BbStick
  deriving stock (Eq, Show, Generic, Enum, Bounded)

boundaryBehaviorFromText :: Text -> Maybe BoundaryBehavior
boundaryBehaviorFromText "none" = Just BbNone
boundaryBehaviorFromText "kill" = Just BbKill
boundaryBehaviorFromText "bounce" = Just BbBounce
boundaryBehaviorFromText "wrap" = Just BbWrap
boundaryBehaviorFromText "stick" = Just BbStick
boundaryBehaviorFromText _ = Nothing

data FloorBehavior = FloorNone | FloorBounce | FloorStick | FloorKill
  deriving stock (Eq, Show, Generic, Enum, Bounded)

floorBehaviorFromText :: Text -> Maybe FloorBehavior
floorBehaviorFromText "none" = Just FloorNone
floorBehaviorFromText "bounce" = Just FloorBounce
floorBehaviorFromText "stick" = Just FloorStick
floorBehaviorFromText "kill" = Just FloorKill
floorBehaviorFromText _ = Nothing

data AudioFeature = AfAmplitude | AfBass | AfMid | AfHigh | AfBeat | AfSpectralCentroid
  deriving stock (Eq, Show, Generic, Enum, Bounded)

audioFeatureFromText :: Text -> Maybe AudioFeature
audioFeatureFromText "amplitude" = Just AfAmplitude
audioFeatureFromText "bass" = Just AfBass
audioFeatureFromText "mid" = Just AfMid
audioFeatureFromText "high" = Just AfHigh
audioFeatureFromText "beat" = Just AfBeat
audioFeatureFromText "spectralCentroid" = Just AfSpectralCentroid
audioFeatureFromText _ = Nothing

data AudioBindingTarget = AtEmitter | AtSystem | AtForceField
  deriving stock (Eq, Show, Generic, Enum, Bounded)

audioBindingTargetFromText :: Text -> Maybe AudioBindingTarget
audioBindingTargetFromText "emitter" = Just AtEmitter
audioBindingTargetFromText "system" = Just AtSystem
audioBindingTargetFromText "forceField" = Just AtForceField
audioBindingTargetFromText _ = Nothing

data AudioBindingCurve = AbLinear | AbExponential | AbLogarithmic | AbStep
  deriving stock (Eq, Show, Generic, Enum, Bounded)

audioBindingCurveFromText :: Text -> Maybe AudioBindingCurve
audioBindingCurveFromText "linear" = Just AbLinear
audioBindingCurveFromText "exponential" = Just AbExponential
audioBindingCurveFromText "logarithmic" = Just AbLogarithmic
audioBindingCurveFromText "step" = Just AbStep
audioBindingCurveFromText _ = Nothing

data AudioTriggerMode = TmContinuous | TmOnThreshold | TmOnBeat
  deriving stock (Eq, Show, Generic, Enum, Bounded)

audioTriggerModeFromText :: Text -> Maybe AudioTriggerMode
audioTriggerModeFromText "continuous" = Just TmContinuous
audioTriggerModeFromText "onThreshold" = Just TmOnThreshold
audioTriggerModeFromText "onBeat" = Just TmOnBeat
audioTriggerModeFromText _ = Nothing

data ParticleBlendMode = PbNormal | PbAdditive | PbMultiply | PbScreen
  deriving stock (Eq, Show, Generic, Enum, Bounded)

particleBlendModeFromText :: Text -> Maybe ParticleBlendMode
particleBlendModeFromText "normal" = Just PbNormal
particleBlendModeFromText "additive" = Just PbAdditive
particleBlendModeFromText "multiply" = Just PbMultiply
particleBlendModeFromText "screen" = Just PbScreen
particleBlendModeFromText _ = Nothing

data ParticleShape = PsCircle | PsSquare | PsTriangle | PsStar
  deriving stock (Eq, Show, Generic, Enum, Bounded)

particleShapeFromText :: Text -> Maybe ParticleShape
particleShapeFromText "circle" = Just PsCircle
particleShapeFromText "square" = Just PsSquare
particleShapeFromText "triangle" = Just PsTriangle
particleShapeFromText "star" = Just PsStar
particleShapeFromText _ = Nothing

data MeshMode = MmBillboard | MmMesh
  deriving stock (Eq, Show, Generic, Enum, Bounded)

meshModeFromText :: Text -> Maybe MeshMode
meshModeFromText "billboard" = Just MmBillboard
meshModeFromText "mesh" = Just MmMesh
meshModeFromText _ = Nothing

data MeshGeometry = MgCube | MgSphere | MgCylinder | MgCone | MgTorus | MgCustom
  deriving stock (Eq, Show, Generic, Enum, Bounded)

meshGeometryFromText :: Text -> Maybe MeshGeometry
meshGeometryFromText "cube" = Just MgCube
meshGeometryFromText "sphere" = Just MgSphere
meshGeometryFromText "cylinder" = Just MgCylinder
meshGeometryFromText "cone" = Just MgCone
meshGeometryFromText "torus" = Just MgTorus
meshGeometryFromText "custom" = Just MgCustom
meshGeometryFromText _ = Nothing

data SpringStructureType = SsCloth | SsRope | SsSoftbody | SsCustom
  deriving stock (Eq, Show, Generic, Enum, Bounded)

springStructureTypeFromText :: Text -> Maybe SpringStructureType
springStructureTypeFromText "cloth" = Just SsCloth
springStructureTypeFromText "rope" = Just SsRope
springStructureTypeFromText "softbody" = Just SsSoftbody
springStructureTypeFromText "custom" = Just SsCustom
springStructureTypeFromText _ = Nothing

data SPHFluidPreset = SphWater | SphHoney | SphLava | SphGas | SphCustom
  deriving stock (Eq, Show, Generic, Enum, Bounded)

sphFluidPresetFromText :: Text -> Maybe SPHFluidPreset
sphFluidPresetFromText "water" = Just SphWater
sphFluidPresetFromText "honey" = Just SphHoney
sphFluidPresetFromText "lava" = Just SphLava
sphFluidPresetFromText "gas" = Just SphGas
sphFluidPresetFromText "custom" = Just SphCustom
sphFluidPresetFromText _ = Nothing

data InterCharacterBlending = IcbNormal | IcbMultiply | IcbScreen | IcbOverlay
  deriving stock (Eq, Show, Generic, Enum, Bounded)

interCharacterBlendingFromText :: Text -> Maybe InterCharacterBlending
interCharacterBlendingFromText "normal" = Just IcbNormal
interCharacterBlendingFromText "multiply" = Just IcbMultiply
interCharacterBlendingFromText "screen" = Just IcbScreen
interCharacterBlendingFromText "overlay" = Just IcbOverlay
interCharacterBlendingFromText _ = Nothing
