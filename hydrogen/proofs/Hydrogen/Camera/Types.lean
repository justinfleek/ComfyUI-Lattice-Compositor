/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      HYDROGEN // CAMERA // TYPES
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Core camera types with proven invariants.
  
  This module defines camera types following the LATTICE camera model,
  with all invariants proven at compile time:
  
  KEY INVARIANTS:
    - FOV: strictly between 0 and pi radians (0° < fov < 180°)
    - Near clip: strictly positive
    - Far clip: strictly greater than near clip
    - Focal length: strictly positive
    - Film/sensor size: strictly positive
    - Aspect ratio: strictly positive
    - Aperture (f-stop): strictly positive
    - Focus distance: strictly positive
  
  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Vec3       : Camera position and orientation
  - Quaternion : Camera rotation
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Math.Vec3
import Hydrogen.Math.Quaternion
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Hydrogen.Camera

open Hydrogen.Math

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: CAMERA TYPE ENUMERATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Camera projection type -/
inductive ProjectionType where
  | perspective
  | orthographic
  deriving Repr, BEq, DecidableEq

/-- Camera node mode (After Effects style) -/
inductive CameraNodeMode where
  | oneNode   -- Camera rotates in place
  | twoNode   -- Camera orbits around point of interest
  deriving Repr, BEq, DecidableEq

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: BOUNDED VALUE TYPES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Field of view in radians, strictly between 0 and pi.
    This ensures the frustum is well-defined (not degenerate). -/
structure FOV where
  value : ℝ
  positive : value > 0
  lt_pi : value < Real.pi

namespace FOV

/-- Default FOV: 50mm equivalent on full-frame (approx 39.6°) -/
noncomputable def default : FOV where
  value := 39.6 * Real.pi / 180
  positive := by positivity
  lt_pi := by
    have hpi : Real.pi > 0 := Real.pi_pos
    have h : (39.6 : ℝ) / 180 < 1 := by norm_num
    have : 39.6 * Real.pi / 180 = (39.6 / 180) * Real.pi := by ring
    rw [this]
    calc (39.6 / 180) * Real.pi < 1 * Real.pi := by nlinarith
      _ = Real.pi := one_mul _

/-- Wide angle FOV: 24mm equivalent (approx 73.7°) -/
noncomputable def wide : FOV where
  value := 73.7 * Real.pi / 180
  positive := by positivity
  lt_pi := by
    have hpi : Real.pi > 0 := Real.pi_pos
    have h : (73.7 : ℝ) / 180 < 1 := by norm_num
    have : 73.7 * Real.pi / 180 = (73.7 / 180) * Real.pi := by ring
    rw [this]
    calc (73.7 / 180) * Real.pi < 1 * Real.pi := by nlinarith
      _ = Real.pi := one_mul _

/-- Telephoto FOV: 135mm equivalent (approx 15.2°) -/
noncomputable def telephoto : FOV where
  value := 15.2 * Real.pi / 180
  positive := by positivity
  lt_pi := by
    have hpi : Real.pi > 0 := Real.pi_pos
    have h : (15.2 : ℝ) / 180 < 1 := by norm_num
    have : 15.2 * Real.pi / 180 = (15.2 / 180) * Real.pi := by ring
    rw [this]
    calc (15.2 / 180) * Real.pi < 1 * Real.pi := by nlinarith
      _ = Real.pi := one_mul _

/-- Convert FOV to degrees -/
noncomputable def toDegrees (fov : FOV) : ℝ := fov.value * 180 / Real.pi

/-- FOV in degrees is positive -/
theorem toDegrees_positive (fov : FOV) : fov.toDegrees > 0 := by
  unfold toDegrees
  have h1 : fov.value > 0 := fov.positive
  have h2 : (180 : ℝ) > 0 := by norm_num
  have h3 : Real.pi > 0 := Real.pi_pos
  positivity

/-- FOV in degrees is less than 180 -/
theorem toDegrees_lt_180 (fov : FOV) : fov.toDegrees < 180 := by
  unfold toDegrees
  have h := fov.lt_pi
  have hpi : Real.pi > 0 := Real.pi_pos
  have h180 : (180 : ℝ) > 0 := by norm_num
  have hpinv : Real.pi⁻¹ > 0 := inv_pos.mpr hpi
  have step1 : fov.value * 180 < Real.pi * 180 := by nlinarith
  have step2 : fov.value * 180 * Real.pi⁻¹ < Real.pi * 180 * Real.pi⁻¹ := by nlinarith
  simp only [div_eq_mul_inv]
  calc fov.value * 180 * Real.pi⁻¹ < Real.pi * 180 * Real.pi⁻¹ := step2
    _ = 180 := by field_simp

end FOV

/-- Clipping planes with near < far invariant -/
structure ClipPlanes where
  near : ℝ
  far : ℝ
  near_positive : near > 0
  far_gt_near : far > near

namespace ClipPlanes

/-- Default clip planes: 0.1 to 1000 -/
def default : ClipPlanes where
  near := 0.1
  far := 1000
  near_positive := by norm_num
  far_gt_near := by norm_num

/-- Near clip for close-up work -/
def closeUp : ClipPlanes where
  near := 0.01
  far := 100
  near_positive := by norm_num
  far_gt_near := by norm_num

/-- Far clip for large scenes -/
def landscape : ClipPlanes where
  near := 1
  far := 100000
  near_positive := by norm_num
  far_gt_near := by norm_num

/-- Clip range (far - near) -/
def range (cp : ClipPlanes) : ℝ := cp.far - cp.near

/-- Clip range is positive -/
theorem range_positive (cp : ClipPlanes) : cp.range > 0 := by
  unfold range
  linarith [cp.far_gt_near]

/-- Far is positive (derived from invariants) -/
theorem far_positive (cp : ClipPlanes) : cp.far > 0 := by
  linarith [cp.near_positive, cp.far_gt_near]

end ClipPlanes

/-- Aspect ratio (width / height), strictly positive -/
structure AspectRatio where
  value : ℝ
  positive : value > 0

namespace AspectRatio

/-- 16:9 widescreen -/
noncomputable def widescreen : AspectRatio where
  value := 16 / 9
  positive := by norm_num

/-- 4:3 standard -/
noncomputable def standard : AspectRatio where
  value := 4 / 3
  positive := by norm_num

/-- 1:1 square -/
def square : AspectRatio where
  value := 1
  positive := by norm_num

/-- 2.35:1 anamorphic cinema -/
def anamorphic : AspectRatio where
  value := 2.35
  positive := by norm_num

/-- 21:9 ultrawide -/
noncomputable def ultrawide : AspectRatio where
  value := 21 / 9
  positive := by norm_num

end AspectRatio

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: LENS PROPERTIES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Focal length in millimeters, strictly positive -/
structure FocalLength where
  mm : ℝ
  positive : mm > 0

namespace FocalLength

def standard : FocalLength where mm := 50; positive := by norm_num
def wide24 : FocalLength where mm := 24; positive := by norm_num
def wide35 : FocalLength where mm := 35; positive := by norm_num
def portrait85 : FocalLength where mm := 85; positive := by norm_num
def telephoto135 : FocalLength where mm := 135; positive := by norm_num
def telephoto200 : FocalLength where mm := 200; positive := by norm_num

end FocalLength

/-- Film/sensor size in millimeters, strictly positive -/
structure FilmSize where
  mm : ℝ
  positive : mm > 0

namespace FilmSize

/-- Full frame 35mm (36mm width) -/
def fullFrame : FilmSize where mm := 36; positive := by norm_num

/-- APS-C (Canon, ~22.3mm) -/
def apsC : FilmSize where mm := 22.3; positive := by norm_num

/-- Super 35 cinema (~24.89mm) -/
def super35 : FilmSize where mm := 24.89; positive := by norm_num

/-- Micro Four Thirds (~17.3mm) -/
def microFourThirds : FilmSize where mm := 17.3; positive := by norm_num

/-- Medium format (~53.7mm) -/
def mediumFormat : FilmSize where mm := 53.7; positive := by norm_num

end FilmSize

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: DEPTH OF FIELD
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- F-stop (aperture), strictly positive -/
structure FStop where
  value : ℝ
  positive : value > 0

namespace FStop

def f1_4 : FStop where value := 1.4; positive := by norm_num
def f2 : FStop where value := 2; positive := by norm_num
def f2_8 : FStop where value := 2.8; positive := by norm_num
def f4 : FStop where value := 4; positive := by norm_num
def f5_6 : FStop where value := 5.6; positive := by norm_num
def f8 : FStop where value := 8; positive := by norm_num
def f11 : FStop where value := 11; positive := by norm_num
def f16 : FStop where value := 16; positive := by norm_num
def f22 : FStop where value := 22; positive := by norm_num

end FStop

/-- Focus distance, strictly positive -/
structure FocusDistance where
  value : ℝ
  positive : value > 0

namespace FocusDistance

/-- Infinity focus (very large distance) -/
def infinity : FocusDistance where
  value := 1000000  -- 1 million units
  positive := by norm_num

/-- Close focus (portrait range) -/
def portrait : FocusDistance where
  value := 2  -- 2 units (meters typically)
  positive := by norm_num

/-- Macro focus -/
def macroFocus : FocusDistance where
  value := 0.3  -- 30cm
  positive := by norm_num

end FocusDistance

/-- Depth of field settings with proven invariants -/
structure DepthOfField where
  enabled : Bool
  focusDistance : FocusDistance
  fStop : FStop
  blurStrength : ℝ               -- Normalized 0-1
  blurStrength_ge_0 : blurStrength ≥ 0
  blurStrength_le_1 : blurStrength ≤ 1

namespace DepthOfField

/-- Default DOF (disabled) -/
def disabled : DepthOfField where
  enabled := false
  focusDistance := FocusDistance.infinity
  fStop := FStop.f8
  blurStrength := 0.5
  blurStrength_ge_0 := by norm_num
  blurStrength_le_1 := by norm_num

/-- Shallow DOF for portraits -/
def shallow : DepthOfField where
  enabled := true
  focusDistance := FocusDistance.portrait
  fStop := FStop.f1_4
  blurStrength := 1.0
  blurStrength_ge_0 := by norm_num
  blurStrength_le_1 := by norm_num

/-- Deep DOF for landscapes -/
def deep : DepthOfField where
  enabled := true
  focusDistance := FocusDistance.infinity
  fStop := FStop.f16
  blurStrength := 0.5
  blurStrength_ge_0 := by norm_num
  blurStrength_le_1 := by norm_num

end DepthOfField

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: CAMERA STRUCTURE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Perspective camera with all invariants proven -/
structure PerspectiveCamera where
  position : Vec3
  rotation : Quaternion
  fov : FOV
  aspect : AspectRatio
  clip : ClipPlanes

namespace PerspectiveCamera

/-- Default perspective camera at origin looking down -Z -/
noncomputable def default : PerspectiveCamera where
  position := Vec3.zero
  rotation := Quaternion.identity
  fov := FOV.default
  aspect := AspectRatio.widescreen
  clip := ClipPlanes.default

end PerspectiveCamera

/-- Orthographic camera with proven invariants -/
structure OrthographicCamera where
  position : Vec3
  rotation : Quaternion
  width : ℝ
  height : ℝ
  clip : ClipPlanes
  width_positive : width > 0
  height_positive : height > 0

namespace OrthographicCamera

/-- Default orthographic camera -/
def default : OrthographicCamera where
  position := Vec3.zero
  rotation := Quaternion.identity
  width := 10
  height := 10
  clip := ClipPlanes.default
  width_positive := by norm_num
  height_positive := by norm_num

/-- Aspect ratio of orthographic camera -/
noncomputable def aspect (cam : OrthographicCamera) : AspectRatio where
  value := cam.width / cam.height
  positive := by
    have hw := cam.width_positive
    have hh := cam.height_positive
    positivity

end OrthographicCamera

/-- Two-node camera (orbits around point of interest) -/
structure TwoNodeCamera where
  position : Vec3
  pointOfInterest : Vec3
  fov : FOV
  aspect : AspectRatio
  clip : ClipPlanes

namespace TwoNodeCamera

/-- Direction from camera to point of interest -/
noncomputable def direction (cam : TwoNodeCamera) : Vec3 :=
  Vec3.sub cam.pointOfInterest cam.position

/-- Distance to point of interest -/
noncomputable def distance (cam : TwoNodeCamera) : ℝ :=
  Vec3.length (direction cam)

end TwoNodeCamera

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6: BASIC THEOREMS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Half-FOV is positive and less than pi/2 -/
theorem fov_half_positive (fov : FOV) : fov.value / 2 > 0 := by
  have h := fov.positive
  linarith

theorem fov_half_lt_pi_half (fov : FOV) : fov.value / 2 < Real.pi / 2 := by
  have h := fov.lt_pi
  linarith

/-- Tangent of half-FOV is positive (needed for perspective projection) -/
theorem tan_half_fov_positive (fov : FOV) : Real.tan (fov.value / 2) > 0 := by
  have h1 := fov_half_positive fov
  have h2 := fov_half_lt_pi_half fov
  exact Real.tan_pos_of_pos_of_lt_pi_div_two h1 h2

/-- Perspective parameters are valid for projection -/
theorem perspective_params_valid (cam : PerspectiveCamera) :
    cam.fov.value > 0 ∧ 
    cam.fov.value < Real.pi ∧
    cam.aspect.value > 0 ∧
    cam.clip.near > 0 ∧
    cam.clip.far > cam.clip.near := by
  exact ⟨cam.fov.positive, cam.fov.lt_pi, cam.aspect.positive, 
         cam.clip.near_positive, cam.clip.far_gt_near⟩

/-- Orthographic parameters are valid for projection -/
theorem orthographic_params_valid (cam : OrthographicCamera) :
    cam.width > 0 ∧
    cam.height > 0 ∧
    cam.clip.near > 0 ∧
    cam.clip.far > cam.clip.near := by
  exact ⟨cam.width_positive, cam.height_positive,
         cam.clip.near_positive, cam.clip.far_gt_near⟩

end Hydrogen.Camera
