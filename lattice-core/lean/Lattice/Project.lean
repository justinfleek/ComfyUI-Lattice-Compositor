/-
  Lattice.Project - Core Project Types

  Max 500 lines.

  Source: ui/src/types/project.ts (2203 lines - split across modules)

  Defines the root project structure, compositions, layers, and core types.
  Layer-specific data is in LayerData module.
-/

import Lattice.Primitives
import Lattice.Animation
import Lattice.Transform

namespace Lattice.Project

open Lattice.Primitives
open Lattice.Animation
open Lattice.Transform

/-! ## Layer Type -/

/-- All supported layer types -/
inductive LayerType where
  | image
  | video
  | solid
  | text
  | shape
  | null
  | camera
  | light
  | audio
  | particle
  | adjustment
  | preComp
  | group
  | nestedComp
  | depth
  | normal
  | generated
  | matte
  | control
  | spline
  | path
  | pose
  | effect
  | model
  | pointCloud
  | depthflow
  deriving Repr, BEq, DecidableEq

/-! ## Blend Mode -/

/-- Compositing blend modes -/
inductive BlendMode where
  | normal
  | multiply
  | screen
  | overlay
  | darken
  | lighten
  | colorDodge
  | colorBurn
  | hardLight
  | softLight
  | difference
  | exclusion
  | hue
  | saturation
  | color
  | luminosity
  | add
  | subtract
  | divide
  | linearBurn
  | linearDodge
  | vividLight
  | linearLight
  | pinLight
  | hardMix
  | dissolve
  | darker
  | lighter
  deriving Repr, BEq, DecidableEq

/-! ## Track Matte Mode -/

/-- Track matte mode -/
inductive TrackMatteMode where
  | none
  | alpha
  | alphaInverted
  | luma
  | lumaInverted
  deriving Repr, BEq, DecidableEq

/-! ## Composition Settings -/

/-- Composition settings with validated dimensions -/
structure CompositionSettings where
  width : Nat
  height : Nat
  frameCount : Nat
  fps : Float
  duration : Float
  backgroundColor : HexColor
  autoResizeToContent : Bool
  frameBlendingEnabled : Bool
  width_positive : width > 0
  height_positive : height > 0
  width_div8 : width % 8 = 0
  height_div8 : height % 8 = 0
  fps_positive : fps > 0
  fps_finite : fps.isFinite
  duration_nonneg : duration ≥ 0
  duration_finite : duration.isFinite
  deriving Repr

/-! ## Project Metadata -/

/-- Project metadata -/
structure ProjectMeta where
  name : String
  created : NonEmptyString  -- ISO timestamp
  modified : NonEmptyString -- ISO timestamp
  author : Option String
  description : Option String
  tags : Array String
  deriving Repr

/-! ## Motion Blur Settings -/

/-- Motion blur configuration -/
structure MotionBlurSettings where
  enabled : Bool
  samplesPerFrame : Nat
  shutterAngle : Float
  shutterPhase : Float
  adaptiveSampling : Bool
  samples_positive : samplesPerFrame > 0 ∨ ¬enabled
  shutterAngle_range : shutterAngle ≥ 0 ∧ shutterAngle ≤ 720
  shutterAngle_finite : shutterAngle.isFinite
  shutterPhase_finite : shutterPhase.isFinite
  deriving Repr

/-! ## Layer Transform -/

/-- 2D layer transform -/
structure LayerTransform2D where
  anchorX : Float
  anchorY : Float
  positionX : Float
  positionY : Float
  scaleX : Float
  scaleY : Float
  rotation : Float
  opacity : Float
  all_finite : anchorX.isFinite ∧ anchorY.isFinite ∧
               positionX.isFinite ∧ positionY.isFinite ∧
               scaleX.isFinite ∧ scaleY.isFinite ∧
               rotation.isFinite ∧ opacity.isFinite
  opacity_range : opacity ≥ 0 ∧ opacity ≤ 100
  deriving Repr

/-- 3D layer transform extension -/
structure LayerTransform3D extends LayerTransform2D where
  positionZ : Float
  anchorZ : Float
  scaleZ : Float
  rotationX : Float
  rotationY : Float
  rotationZ : Float
  orientation : Option (Float × Float × Float)
  z_finite : positionZ.isFinite ∧ anchorZ.isFinite ∧ scaleZ.isFinite
  rot_finite : rotationX.isFinite ∧ rotationY.isFinite ∧ rotationZ.isFinite
  deriving Repr

/-! ## Layer Base -/

/-- Base layer structure (common to all layer types) -/
structure LayerBase where
  id : NonEmptyString
  name : NonEmptyString
  layerType : LayerType
  visible : Bool
  locked : Bool
  solo : Bool
  shy : Bool
  enabled : Bool
  selected : Bool
  collapsed : Bool
  guideLayer : Bool
  is3D : Bool
  blendMode : BlendMode
  opacity : Float
  startFrame : FrameNumber
  endFrame : FrameNumber
  inPoint : FrameNumber
  outPoint : FrameNumber
  stretch : Float
  parentId : Option NonEmptyString
  trackMatteMode : TrackMatteMode
  trackMatteLayerId : Option NonEmptyString
  motionBlur : Bool
  qualitySetting : Option NonEmptyString
  samplingQuality : Option NonEmptyString
  preserveTransparency : Bool
  frameBlending : Bool
  timeRemapEnabled : Bool
  opacity_range : opacity ≥ 0 ∧ opacity ≤ 100
  opacity_finite : opacity.isFinite
  stretch_positive : stretch > 0
  stretch_finite : stretch.isFinite
  timing_valid : startFrame.value ≤ endFrame.value
  deriving Repr

/-! ## Vec3 -/

/-- 3D vector -/
structure Vec3 where
  x : Float
  y : Float
  z : Float
  x_finite : x.isFinite
  y_finite : y.isFinite
  z_finite : z.isFinite
  deriving Repr

/-- Create Vec3 from raw floats (partial) -/
def Vec3.mk? (x y z : Float) : Option Vec3 :=
  if x.isFinite ∧ y.isFinite ∧ z.isFinite then
    some ⟨x, y, z, by simp_all, by simp_all, by simp_all⟩
  else
    none

/-! ## Point and BoundingBox -/

/-- 2D point -/
structure Point where
  x : Float
  y : Float
  x_finite : x.isFinite
  y_finite : y.isFinite
  deriving Repr

/-- Axis-aligned bounding box -/
structure BoundingBox where
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

/-! ## Composition -/

/-- A composition containing layers -/
structure Composition where
  id : NonEmptyString
  name : NonEmptyString
  settings : CompositionSettings
  layers : Array LayerBase
  currentFrame : FrameNumber
  isNestedComp : Bool
  parentCompId : Option NonEmptyString
  deriving Repr

/-! ## Asset Reference -/

/-- Asset type in project -/
inductive AssetType where
  | image
  | video
  | audio
  | font
  | model
  | pointCloud
  | data
  | lottie
  | svg
  deriving Repr, BEq, DecidableEq

/-- Asset metadata -/
structure AssetMeta where
  id : NonEmptyString
  name : NonEmptyString
  assetType : AssetType
  path : Option String
  mimeType : Option NonEmptyString
  fileSize : Option Nat
  width : Option Nat
  height : Option Nat
  duration : Option Float
  frameCount : Option Nat
  fps : Option Float
  deriving Repr

/-! ## Lattice Project -/

/-- Root project structure -/
structure LatticeProject where
  version : NonEmptyString
  schemaVersion : Nat
  meta : ProjectMeta
  compositions : Array Composition
  mainCompositionId : NonEmptyString
  assets : Array AssetMeta
  currentFrame : FrameNumber
  -- Invariants
  has_main_comp : compositions.any (fun c => c.id = mainCompositionId)
  schema_valid : schemaVersion ≥ 1
  deriving Repr

/-! ## Export Options -/

/-- Matte export mode -/
inductive MatteExportMode where
  | excludeText
  | includeAll
  deriving Repr, BEq, DecidableEq

/-- Export options -/
structure ExportOptions where
  format : NonEmptyString
  matteMode : MatteExportMode
  width : Nat
  height : Nat
  width_positive : width > 0
  height_positive : height > 0
  deriving Repr

/-! ## Color Gradient Stop -/

/-- Gradient stop for color ramps -/
structure GradientStop where
  position : Float
  color : HexColor
  position_range : position ≥ 0 ∧ position ≤ 1
  position_finite : position.isFinite
  deriving Repr

/-! ## Extracted Texture -/

/-- Extraction method for textures -/
inductive ExtractionMethod where
  | matseg
  | manual
  | sdxl
  deriving Repr, BEq, DecidableEq

/-- PBR texture set -/
structure PBRTextures where
  roughness : NonEmptyString  -- Base64 PNG
  metallic : NonEmptyString
  normal : NonEmptyString
  height : NonEmptyString
  ao : NonEmptyString
  deriving Repr

/-- Extracted tileable texture with PBR maps -/
structure ExtractedTexture where
  id : NonEmptyString
  sourceAssetId : NonEmptyString
  region : BoundingBox
  albedo : NonEmptyString  -- Base64 PNG
  pbr : PBRTextures
  extractionMethod : ExtractionMethod
  seamless : Bool
  resolutionWidth : Nat
  resolutionHeight : Nat
  resolution_positive : resolutionWidth > 0 ∧ resolutionHeight > 0
  deriving Repr

end Lattice.Project
