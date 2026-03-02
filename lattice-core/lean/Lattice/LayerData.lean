/-
  Lattice.LayerData - Layer-specific data interfaces

  Max 500 lines.

  Source: ui/src/types/layerData.ts (565 lines)

  Each layer type has its own data structure defining type-specific properties.
-/

import Lattice.Primitives
import Lattice.DataAsset

namespace Lattice.LayerData

open Lattice.Primitives
open Lattice.DataAsset

/-! ## Image Layer -/

/-- Image fit mode -/
inductive ImageFit where
  | none | contain | cover | fill
  deriving Repr, BEq, DecidableEq

/-- Image source type -/
inductive ImageSourceType where
  | file | generated | segmented | inline
  deriving Repr, BEq, DecidableEq

/-- Crop rectangle -/
structure CropRect where
  x : Float
  y : Float
  width : Float
  height : Float
  x_finite : x.isFinite
  y_finite : y.isFinite
  width_positive : width > 0
  width_finite : width.isFinite
  height_positive : height > 0
  height_finite : height.isFinite
  deriving Repr

/-- Image layer data -/
structure ImageLayerData where
  assetId : String
  source : String
  fit : ImageFit
  cropEnabled : Bool
  cropRect : CropRect
  sourceType : ImageSourceType
  segmentationMaskId : String
  deriving Repr

/-! ## Depth Layer -/

/-- Depth visualization mode -/
inductive DepthVisualizationMode where
  | grayscale | colormap | contour | mesh3d
  deriving Repr, BEq, DecidableEq

/-- Depth color map -/
inductive DepthColorMap where
  | turbo | viridis | plasma | inferno | magma | grayscale
  deriving Repr, BEq, DecidableEq

/-- Depth layer data -/
structure DepthLayerData where
  assetId : Option NonEmptyString
  visualizationMode : DepthVisualizationMode
  colorMap : DepthColorMap
  invert : Bool
  minDepth : Float
  maxDepth : Float
  autoNormalize : Bool
  contourLevels : Nat
  contourColor : HexColor
  contourWidth : Float
  meshDisplacementPropertyId : NonEmptyString
  meshResolution : Nat
  wireframe : Bool
  minDepth_finite : minDepth.isFinite
  maxDepth_finite : maxDepth.isFinite
  contourWidth_positive : contourWidth > 0
  contourWidth_finite : contourWidth.isFinite
  meshResolution_positive : meshResolution > 0
  deriving Repr

/-! ## Normal Layer -/

/-- Normal visualization mode -/
inductive NormalVisualizationMode where
  | rgb | hemisphere | arrows | lit
  deriving Repr, BEq, DecidableEq

/-- Normal map format -/
inductive NormalMapFormat where
  | opengl | directx
  deriving Repr, BEq, DecidableEq

/-- Normal layer data -/
structure NormalLayerData where
  assetId : Option NonEmptyString
  visualizationMode : NormalVisualizationMode
  format : NormalMapFormat
  flipX : Bool
  flipY : Bool
  flipZ : Bool
  arrowDensity : Float
  arrowScale : Float
  arrowColor : HexColor
  lightDirectionX : Float
  lightDirectionY : Float
  lightDirectionZ : Float
  lightIntensity : Float
  ambientIntensity : Float
  arrowDensity_positive : arrowDensity > 0
  arrowDensity_finite : arrowDensity.isFinite
  arrowScale_positive : arrowScale > 0
  arrowScale_finite : arrowScale.isFinite
  lightIntensity_ge_0 : lightIntensity ≥ 0
  lightIntensity_finite : lightIntensity.isFinite
  ambientIntensity_ge_0 : ambientIntensity ≥ 0
  ambientIntensity_finite : ambientIntensity.isFinite
  deriving Repr

/-! ## Audio Layer -/

/-- Audio layer data -/
structure AudioLayerData where
  assetId : Option NonEmptyString
  levelPropertyId : NonEmptyString
  muted : Bool
  solo : Bool
  panPropertyId : NonEmptyString
  startTime : Float
  loop : Bool
  speed : Float
  showWaveform : Bool
  waveformColor : HexColor
  exposeFeatures : Bool
  startTime_ge_0 : startTime ≥ 0
  startTime_finite : startTime.isFinite
  speed_positive : speed > 0
  speed_finite : speed.isFinite
  deriving Repr

/-! ## Video Data -/

/-- Frame blending mode -/
inductive FrameBlendingMode where
  | none | frameMix | pixelMotion
  deriving Repr, BEq, DecidableEq

/-- Timewarp method -/
inductive TimewarpMethod where
  | wholeFrames | frameMix | pixelMotion
  deriving Repr, BEq, DecidableEq

/-- Video data -/
structure VideoData where
  assetId : Option NonEmptyString
  loop : Bool
  pingPong : Bool
  startTime : Float
  endTime : Option Float
  speed : Float
  speedMapEnabled : Bool
  speedMapPropertyId : Option NonEmptyString
  timewarpEnabled : Bool
  timewarpSpeedPropertyId : Option NonEmptyString
  timewarpMethod : Option TimewarpMethod
  frameBlending : FrameBlendingMode
  audioEnabled : Bool
  audioLevel : Float
  posterFrame : FrameNumber
  startTime_ge_0 : startTime ≥ 0
  startTime_finite : startTime.isFinite
  speed_positive : speed > 0
  speed_finite : speed.isFinite
  audioLevel_ge_0 : audioLevel ≥ 0
  audioLevel_le_100 : audioLevel ≤ 100
  audioLevel_finite : audioLevel.isFinite
  deriving Repr

/-! ## Nested Comp Data -/

/-- Nested composition data -/
structure NestedCompData where
  compositionId : NonEmptyString
  speedMapEnabled : Bool
  speedMapPropertyId : Option NonEmptyString
  timewarpEnabled : Bool
  timewarpSpeedPropertyId : Option NonEmptyString
  timewarpMethod : Option TimewarpMethod
  flattenTransform : Bool
  overrideFrameRate : Bool
  frameRate : Option Float
  deriving Repr

/-! ## Generated Layer -/

/-- Generated map type -/
inductive GeneratedMapType where
  | depth | normal | edge | pose | segment | lineart | softedge
  deriving Repr, BEq, DecidableEq

/-- Generation status -/
inductive GenerationStatus where
  | pending | generating | complete | error
  deriving Repr, BEq, DecidableEq

/-- Generation type -/
inductive GenerationType where
  | depth | normal | edge | segment | inpaint | custom
  deriving Repr, BEq, DecidableEq

/-- Generated layer data -/
structure GeneratedLayerData where
  generationType : GenerationType
  sourceLayerId : Option NonEmptyString
  model : NonEmptyString
  parameters : Array (String × JSONValue)
  generatedAssetId : Option NonEmptyString
  status : GenerationStatus
  errorMessage : Option String
  autoRegenerate : Bool
  lastGenerated : Option NonEmptyString
  deriving Repr

/-! ## Matte Layer -/

/-- Matte extraction type -/
inductive MatteType where
  | luminance | alpha | red | green | blue | hue | saturation
  deriving Repr, BEq, DecidableEq

/-- Matte preview mode -/
inductive MattePreviewMode where
  | matte | composite | overlay
  deriving Repr, BEq, DecidableEq

/-- Matte layer data -/
structure MatteLayerData where
  matteType : MatteType
  invert : Bool
  threshold : Float
  feather : Float
  expansion : Float
  sourceLayerId : Option NonEmptyString
  previewMode : MattePreviewMode
  threshold_ge_0 : threshold ≥ 0
  threshold_le_1 : threshold ≤ 1
  threshold_finite : threshold.isFinite
  feather_ge_0 : feather ≥ 0
  feather_finite : feather.isFinite
  expansion_finite : expansion.isFinite
  deriving Repr

/-! ## Control Layer -/

/-- Control icon shape -/
inductive ControlIconShape where
  | crosshair | diamond | circle | square
  deriving Repr, BEq, DecidableEq

/-- Control layer data -/
structure ControlLayerData where
  size : Float
  showAxes : Bool
  showIcon : Bool
  iconShape : ControlIconShape
  iconColor : HexColor
  size_positive : size > 0
  size_finite : size.isFinite
  deriving Repr

/-! ## Solid Layer -/

/-- Solid layer data -/
structure SolidLayerData where
  color : HexColor
  width : Nat
  height : Nat
  shadowCatcher : Bool
  shadowOpacity : Option Float
  shadowColor : Option HexColor
  receiveShadow : Bool
  width_positive : width > 0
  height_positive : height > 0
  deriving Repr

/-! ## Group Layer -/

/-- Group layer data -/
structure GroupLayerData where
  collapsed : Bool
  color : Option HexColor
  passThrough : Bool
  isolate : Bool
  deriving Repr

/-! ## Effect Layer -/

/-- Effect layer data -/
structure EffectLayerData where
  effectLayer : Bool
  adjustmentLayer : Bool  -- Deprecated
  color : HexColor
  deriving Repr

/-! ## Model Layer -/

/-- Model instance data -/
structure ModelInstanceData where
  positionX : Float
  positionY : Float
  positionZ : Float
  rotationX : Float
  rotationY : Float
  rotationZ : Float
  scaleX : Float
  scaleY : Float
  scaleZ : Float
  color : Option HexColor
  deriving Repr

/-- Model layer data -/
structure ModelLayerData where
  assetId : Option NonEmptyString
  animationClip : Option NonEmptyString
  animationSpeed : Float
  animationLoop : Bool
  animationTimePropertyId : NonEmptyString
  materialAlbedoAssetId : Option NonEmptyString
  materialNormalAssetId : Option NonEmptyString
  materialRoughnessAssetId : Option NonEmptyString
  materialMetalnessAssetId : Option NonEmptyString
  materialEmissiveAssetId : Option NonEmptyString
  materialEmissiveIntensity : Option Float
  castShadows : Bool
  receiveShadows : Bool
  wireframe : Bool
  lodBias : Float
  instanceCount : Option Nat
  instanceData : Array ModelInstanceData
  animationSpeed_finite : animationSpeed.isFinite
  lodBias_finite : lodBias.isFinite
  deriving Repr

/-! ## Point Cloud Layer -/

/-- Point cloud color mode -/
inductive PointCloudColorMode where
  | vertex | height | intensity | solid
  deriving Repr, BEq, DecidableEq

/-- Point cloud layer data -/
structure PointCloudLayerData where
  assetId : Option NonEmptyString
  pointSizePropertyId : NonEmptyString
  sizeAttenuation : Bool
  colorMode : PointCloudColorMode
  solidColor : Option HexColor
  heightColormap : Option DepthColorMap
  heightMin : Option Float
  heightMax : Option Float
  intensityMin : Option Float
  intensityMax : Option Float
  decimation : Nat
  clipEnabled : Bool
  clipMinX : Option Float
  clipMaxX : Option Float
  clipMinY : Option Float
  clipMaxY : Option Float
  clipMinZ : Option Float
  clipMaxZ : Option Float
  decimation_positive : decimation > 0
  deriving Repr

/-! ## Pose Layer -/

/-- Pose format -/
inductive PoseFormat where
  | openpose | coco | dwpose
  deriving Repr, BEq, DecidableEq

/-- Pose keypoint -/
structure PoseKeypoint where
  x : Float          -- Normalized 0-1
  y : Float          -- Normalized 0-1
  confidence : Float -- 0-1
  x_ge_0 : x ≥ 0
  x_le_1 : x ≤ 1
  x_finite : x.isFinite
  y_ge_0 : y ≥ 0
  y_le_1 : y ≤ 1
  y_finite : y.isFinite
  confidence_ge_0 : confidence ≥ 0
  confidence_le_1 : confidence ≤ 1
  confidence_finite : confidence.isFinite
  deriving Repr

/-- Pose layer data -/
structure PoseLayerData where
  keypoints : Array PoseKeypoint
  format : PoseFormat
  lineWidth : Float
  jointRadius : Float
  lineColor : HexColor
  jointColor : HexColor
  showConfidence : Bool
  mirror : Bool
  lineWidth_positive : lineWidth > 0
  lineWidth_finite : lineWidth.isFinite
  jointRadius_positive : jointRadius > 0
  jointRadius_finite : jointRadius.isFinite
  deriving Repr

/-! ## OpenPose Constants -/

/-- OpenPose keypoint indices -/
def OPENPOSE_NOSE : Nat := 0
def OPENPOSE_NECK : Nat := 1
def OPENPOSE_RIGHT_SHOULDER : Nat := 2
def OPENPOSE_RIGHT_ELBOW : Nat := 3
def OPENPOSE_RIGHT_WRIST : Nat := 4
def OPENPOSE_LEFT_SHOULDER : Nat := 5
def OPENPOSE_LEFT_ELBOW : Nat := 6
def OPENPOSE_LEFT_WRIST : Nat := 7
def OPENPOSE_RIGHT_HIP : Nat := 8
def OPENPOSE_RIGHT_KNEE : Nat := 9
def OPENPOSE_RIGHT_ANKLE : Nat := 10
def OPENPOSE_LEFT_HIP : Nat := 11
def OPENPOSE_LEFT_KNEE : Nat := 12
def OPENPOSE_LEFT_ANKLE : Nat := 13
def OPENPOSE_RIGHT_EYE : Nat := 14
def OPENPOSE_LEFT_EYE : Nat := 15
def OPENPOSE_RIGHT_EAR : Nat := 16
def OPENPOSE_LEFT_EAR : Nat := 17

/-- OpenPose skeleton connections -/
def OPENPOSE_CONNECTIONS : Array (Nat × Nat) := #[
  (0, 1), (1, 2), (2, 3), (3, 4), (1, 5), (5, 6), (6, 7),
  (1, 8), (8, 9), (9, 10), (1, 11), (11, 12), (12, 13),
  (0, 14), (14, 16), (0, 15), (15, 17)
]

end Lattice.LayerData
