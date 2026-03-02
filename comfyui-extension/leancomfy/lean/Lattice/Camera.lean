/-
  Lattice.Camera - 2.5D Camera System Types

  Max 500 lines.

  Source: ui/src/types/camera.ts (282 lines)
-/

import Lattice.Primitives

namespace Lattice.Camera

open Lattice.Primitives

/-! ## Enumerations -/

/-- Camera type -/
inductive CameraType where
  | oneNode
  | twoNode
  deriving Repr, BEq, DecidableEq

/-- Auto-orient mode -/
inductive AutoOrientMode where
  | off
  | orientAlongPath
  | orientTowardsPOI
  deriving Repr, BEq, DecidableEq

/-- Film size measurement -/
inductive MeasureFilmSize where
  | horizontal
  | vertical
  | diagonal
  deriving Repr, BEq, DecidableEq

/-- Wireframe visibility -/
inductive WireframeVisibility where
  | always
  | selected
  | off
  deriving Repr, BEq, DecidableEq

/-- View type for multi-view layout -/
inductive ViewType where
  | activeCamera
  | custom1
  | custom2
  | custom3
  | front
  | back
  | left
  | right
  | top
  | bottom
  deriving Repr, BEq, DecidableEq

/-- View layout -/
inductive ViewLayout where
  | oneView
  | twoViewHorizontal
  | twoViewVertical
  | fourView
  deriving Repr, BEq, DecidableEq

/-- Spatial interpolation type -/
inductive SpatialInterpolation where
  | linear
  | bezier
  | autoBezier
  | continuousBezier
  deriving Repr, BEq, DecidableEq

/-- Temporal interpolation type -/
inductive TemporalInterpolation where
  | linear
  | bezier
  | hold
  deriving Repr, BEq, DecidableEq

/-! ## 3D Vector -/

/-- 3D position/rotation vector -/
structure Vec3 where
  x : Float
  y : Float
  z : Float
  x_finite : x.isFinite
  y_finite : y.isFinite
  z_finite : z.isFinite
  deriving Repr

/-! ## 2D Vector -/

/-- 2D offset vector -/
structure Vec2 where
  x : Float
  y : Float
  x_finite : x.isFinite
  y_finite : y.isFinite
  deriving Repr

/-! ## Depth of Field -/

/-- Depth of field settings -/
structure DepthOfFieldSettings where
  enabled : Bool
  focusDistance : Float              -- Pixels
  aperture : Float                   -- Pixels (internal)
  fStop : Float                      -- f-stop (display)
  blurLevel : Float                  -- 0-1 multiplier
  lockToZoom : Bool
  focusDistance_positive : focusDistance > 0
  focusDistance_finite : focusDistance.isFinite
  aperture_positive : aperture > 0
  aperture_finite : aperture.isFinite
  fStop_positive : fStop > 0
  fStop_finite : fStop.isFinite
  blurLevel_ge_0 : blurLevel ≥ 0
  blurLevel_le_1 : blurLevel ≤ 1
  blurLevel_finite : blurLevel.isFinite
  deriving Repr

/-! ## Iris Properties -/

/-- Iris properties -/
structure IrisProperties where
  shape : Float                      -- 0-10 (pentagon to circle)
  rotation : Float                   -- Degrees
  roundness : Float                  -- 0-1
  aspectRatio : Float                -- 0.5-2
  diffractionFringe : Float          -- 0-1
  shape_ge_0 : shape ≥ 0
  shape_le_10 : shape ≤ 10
  shape_finite : shape.isFinite
  rotation_finite : rotation.isFinite
  roundness_ge_0 : roundness ≥ 0
  roundness_le_1 : roundness ≤ 1
  roundness_finite : roundness.isFinite
  aspectRatio_ge_05 : aspectRatio ≥ 0.5
  aspectRatio_le_2 : aspectRatio ≤ 2
  aspectRatio_finite : aspectRatio.isFinite
  diffractionFringe_ge_0 : diffractionFringe ≥ 0
  diffractionFringe_le_1 : diffractionFringe ≤ 1
  diffractionFringe_finite : diffractionFringe.isFinite
  deriving Repr

/-! ## Highlight Properties -/

/-- Highlight properties -/
structure HighlightProperties where
  gain : Float                       -- 0-1
  threshold : Float                  -- 0-1
  saturation : Float                 -- 0-1
  gain_ge_0 : gain ≥ 0
  gain_le_1 : gain ≤ 1
  gain_finite : gain.isFinite
  threshold_ge_0 : threshold ≥ 0
  threshold_le_1 : threshold ≤ 1
  threshold_finite : threshold.isFinite
  saturation_ge_0 : saturation ≥ 0
  saturation_le_1 : saturation ≤ 1
  saturation_finite : saturation.isFinite
  deriving Repr

/-! ## Camera 3D -/

/-- 3D Camera -/
structure Camera3D where
  id : NonEmptyString
  name : NonEmptyString
  cameraType : CameraType
  -- Transform
  position : Vec3
  pointOfInterest : Vec3             -- Two-node only
  orientation : Vec3                 -- Combined XYZ rotation
  xRotation : Float                  -- Individual rotation (additive)
  yRotation : Float
  zRotation : Float
  -- Lens settings
  zoom : Float                       -- Pixels (AE internal)
  focalLength : Float                -- mm (display)
  angleOfView : Float                -- Degrees (computed)
  filmSize : Float                   -- mm (default 36 = full frame)
  measureFilmSize : MeasureFilmSize
  -- Depth of field
  depthOfField : DepthOfFieldSettings
  -- Iris
  iris : IrisProperties
  -- Highlight
  highlight : HighlightProperties
  -- Auto-orient
  autoOrient : AutoOrientMode
  -- Clipping
  nearClip : Float
  farClip : Float
  -- Proofs
  xRotation_finite : xRotation.isFinite
  yRotation_finite : yRotation.isFinite
  zRotation_finite : zRotation.isFinite
  zoom_positive : zoom > 0
  zoom_finite : zoom.isFinite
  focalLength_positive : focalLength > 0
  focalLength_finite : focalLength.isFinite
  angleOfView_positive : angleOfView > 0
  angleOfView_lt_180 : angleOfView < 180
  angleOfView_finite : angleOfView.isFinite
  filmSize_positive : filmSize > 0
  filmSize_finite : filmSize.isFinite
  nearClip_positive : nearClip > 0
  nearClip_finite : nearClip.isFinite
  farClip_positive : farClip > nearClip
  farClip_finite : farClip.isFinite
  deriving Repr

/-! ## Camera Preset -/

/-- Camera preset with standard focal length -/
structure CameraPreset where
  name : NonEmptyString
  focalLength : Float                -- mm
  angleOfView : Float                -- Degrees
  zoom : Float                       -- Pixels
  focalLength_positive : focalLength > 0
  focalLength_finite : focalLength.isFinite
  angleOfView_positive : angleOfView > 0
  angleOfView_lt_180 : angleOfView < 180
  angleOfView_finite : angleOfView.isFinite
  zoom_positive : zoom > 0
  zoom_finite : zoom.isFinite
  deriving Repr

/-! ## Custom View State -/

/-- Custom view state for viewport -/
structure CustomViewState where
  orbitCenter : Vec3
  orbitDistance : Float
  orbitPhi : Float                   -- Vertical angle (0=top, 90=side)
  orbitTheta : Float                 -- Horizontal angle
  orthoZoom : Float                  -- For orthographic views
  orthoOffset : Vec2
  orbitDistance_positive : orbitDistance > 0
  orbitDistance_finite : orbitDistance.isFinite
  orbitPhi_ge_0 : orbitPhi ≥ 0
  orbitPhi_le_180 : orbitPhi ≤ 180
  orbitPhi_finite : orbitPhi.isFinite
  orbitTheta_finite : orbitTheta.isFinite
  orthoZoom_positive : orthoZoom > 0
  orthoZoom_finite : orthoZoom.isFinite
  deriving Repr

/-! ## Viewport State -/

/-- Custom views map -/
structure CustomViews where
  custom1 : CustomViewState
  custom2 : CustomViewState
  custom3 : CustomViewState
  deriving Repr

/-- Viewport state -/
structure ViewportState where
  layout : ViewLayout
  views : Array ViewType             -- Which view in each panel
  customViews : CustomViews
  activeViewIndex : Nat
  deriving Repr

/-! ## View Options -/

/-- View options -/
structure ViewOptions where
  cameraWireframes : WireframeVisibility
  lightWireframes : WireframeVisibility
  showMotionPaths : Bool
  showLayerPaths : Bool              -- Shape/mask path visibility
  showLayerHandles : Bool
  showSafeZones : Bool
  showGrid : Bool
  showRulers : Bool
  show3DReferenceAxes : Bool
  showCompositionBounds : Bool       -- Canvas as 3D plane
  showFocalPlane : Bool              -- DOF focus indicator
  deriving Repr

/-! ## Camera Keyframe -/

/-- Camera keyframe for animation -/
structure CameraKeyframe where
  frame : FrameNumber
  -- Transform (optional)
  position : Option Vec3
  pointOfInterest : Option Vec3
  orientation : Option Vec3
  xRotation : Option Float
  yRotation : Option Float
  zRotation : Option Float
  -- Lens
  zoom : Option Float
  focalLength : Option Float
  focusDistance : Option Float
  aperture : Option Float
  -- Bezier handles
  inHandle : Option Vec2
  outHandle : Option Vec2
  -- Interpolation
  spatialInterpolation : Option SpatialInterpolation
  temporalInterpolation : Option TemporalInterpolation
  -- Separate dimensions
  separateDimensions : Bool
  deriving Repr

/-! ## Default Values -/

/-- Default zero Vec3 -/
def Vec3.zero : Vec3 :=
  ⟨0, 0, 0, by decide, by decide, by decide⟩

/-- Default zero Vec2 -/
def Vec2.zero : Vec2 :=
  ⟨0, 0, by decide, by decide⟩

end Lattice.Camera
