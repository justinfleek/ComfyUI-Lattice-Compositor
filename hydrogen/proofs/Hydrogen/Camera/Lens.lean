/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       HYDROGEN // CAMERA // LENS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Lens optics: FOV ↔ focal length conversions with proven bounds.
  
  This module provides the mathematical relationship between:
  - Field of View (FOV) in radians
  - Focal length in millimeters
  - Sensor/film size in millimeters
  
  The fundamental relation is:
    FOV = 2 * arctan(sensorSize / (2 * focalLength))
  
  Or equivalently:
    focalLength = sensorSize / (2 * tan(FOV / 2))
  
  PROVEN INVARIANTS:
    - focalLengthToFOV returns FOV in (0, pi)
    - fovToFocalLength returns positive focal length
    - The conversions are inverses (round-trip)
  
  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Types : FOV, FocalLength, FilmSize
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Camera.Types
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

namespace Hydrogen.Camera

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: CORE CONVERSIONS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Convert focal length and sensor size to field of view (radians).
    
    Formula: FOV = 2 * arctan(sensorSize / (2 * focalLength))
    
    This is the standard photographic formula relating these quantities. -/
noncomputable def focalLengthToFOV (focal : FocalLength) (sensor : FilmSize) : ℝ :=
  2 * Real.arctan (sensor.mm / (2 * focal.mm))

/-- Convert field of view and sensor size to focal length (mm).
    
    Formula: focalLength = sensorSize / (2 * tan(FOV / 2))
    
    Inverse of focalLengthToFOV. -/
noncomputable def fovToFocalLength (fov : FOV) (sensor : FilmSize) : ℝ :=
  sensor.mm / (2 * Real.tan (fov.value / 2))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: HELPER LEMMAS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- The argument to arctan is positive -/
theorem arctan_arg_positive (focal : FocalLength) (sensor : FilmSize) :
    sensor.mm / (2 * focal.mm) > 0 := by
  have hs := sensor.positive
  have hf := focal.positive
  positivity

/-- 2 * focal length is positive -/
theorem two_focal_positive (focal : FocalLength) : 2 * focal.mm > 0 := by
  have hf := focal.positive
  linarith

/-- tan of half-FOV is positive -/
theorem tan_half_fov_pos (fov : FOV) : Real.tan (fov.value / 2) > 0 := 
  tan_half_fov_positive fov

/-- 2 * tan(fov/2) is positive -/
theorem two_tan_half_fov_positive (fov : FOV) : 2 * Real.tan (fov.value / 2) > 0 := by
  have h := tan_half_fov_pos fov
  linarith

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: BOUND PROOFS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- arctan of positive argument is positive -/
theorem arctan_pos_of_pos {x : ℝ} (hx : x > 0) : Real.arctan x > 0 := by
  have h0 : Real.arctan 0 = 0 := Real.arctan_zero
  have hmono : StrictMono Real.arctan := Real.arctan_strictMono
  calc Real.arctan x > Real.arctan 0 := hmono hx
    _ = 0 := h0

/-- arctan is bounded above by pi/2 -/
theorem arctan_lt_pi_div_two (x : ℝ) : Real.arctan x < Real.pi / 2 := 
  Real.arctan_lt_pi_div_two x

/-- FOV computed from focal length is positive -/
theorem focalLengthToFOV_positive (focal : FocalLength) (sensor : FilmSize) :
    focalLengthToFOV focal sensor > 0 := by
  unfold focalLengthToFOV
  have harg := arctan_arg_positive focal sensor
  have hatan := arctan_pos_of_pos harg
  linarith

/-- FOV computed from focal length is less than pi -/
theorem focalLengthToFOV_lt_pi (focal : FocalLength) (sensor : FilmSize) :
    focalLengthToFOV focal sensor < Real.pi := by
  unfold focalLengthToFOV
  have h := arctan_lt_pi_div_two (sensor.mm / (2 * focal.mm))
  linarith

/-- Focal length computed from FOV is positive -/
theorem fovToFocalLength_positive (fov : FOV) (sensor : FilmSize) :
    fovToFocalLength fov sensor > 0 := by
  unfold fovToFocalLength
  have hs := sensor.positive
  have ht := two_tan_half_fov_positive fov
  positivity

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: SMART CONSTRUCTORS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Construct FOV from focal length (with proof that it's valid) -/
noncomputable def FOV.fromFocalLength (focal : FocalLength) (sensor : FilmSize) : FOV where
  value := focalLengthToFOV focal sensor
  positive := focalLengthToFOV_positive focal sensor
  lt_pi := focalLengthToFOV_lt_pi focal sensor

/-- Construct FocalLength from FOV (with proof that it's valid) -/
noncomputable def FocalLength.fromFOV (fov : FOV) (sensor : FilmSize) : FocalLength where
  mm := fovToFocalLength fov sensor
  positive := fovToFocalLength_positive fov sensor

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: ROUND-TRIP PROOFS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Converting FOV → focal length → FOV recovers the original FOV -/
theorem fov_focal_fov_roundtrip (fov : FOV) (sensor : FilmSize) :
    focalLengthToFOV (FocalLength.fromFOV fov sensor) sensor = fov.value := by
  unfold focalLengthToFOV FocalLength.fromFOV fovToFocalLength
  simp only
  have ht := two_tan_half_fov_positive fov
  have hs := sensor.positive
  have htan_ne : 2 * Real.tan (fov.value / 2) ≠ 0 := ne_of_gt ht
  -- sensor / (2 * tan(fov/2)) is the focal length
  -- arctan(sensor / (2 * (sensor / (2 * tan(fov/2))))) = arctan(tan(fov/2))
  have simplify : sensor.mm / (2 * (sensor.mm / (2 * Real.tan (fov.value / 2)))) = 
                  Real.tan (fov.value / 2) := by
    field_simp
  rw [simplify]
  -- 2 * arctan(tan(fov/2)) = fov when fov/2 ∈ (-pi/2, pi/2)
  have hpos := fov_half_positive fov
  have hlt := fov_half_lt_pi_half fov
  have hgt_neg : -(Real.pi / 2) < fov.value / 2 := by
    have hpi : Real.pi > 0 := Real.pi_pos
    linarith
  rw [Real.arctan_tan hgt_neg hlt]
  ring

/-- Converting focal length → FOV → focal length recovers the original -/
theorem focal_fov_focal_roundtrip (focal : FocalLength) (sensor : FilmSize) :
    fovToFocalLength (FOV.fromFocalLength focal sensor) sensor = focal.mm := by
  unfold fovToFocalLength FOV.fromFocalLength focalLengthToFOV
  simp only
  have hf := focal.positive
  have hs := sensor.positive
  have h2f := two_focal_positive focal
  have h2f_ne : 2 * focal.mm ≠ 0 := ne_of_gt h2f
  -- tan(arctan(x)) = x
  have _harg := arctan_arg_positive focal sensor
  -- Simplify 2 * arctan(...) / 2 = arctan(...)
  have half_cancel : 2 * Real.arctan (sensor.mm / (2 * focal.mm)) / 2 = 
                     Real.arctan (sensor.mm / (2 * focal.mm)) := by ring
  rw [half_cancel, Real.tan_arctan]
  -- Now: sensor / (2 * (sensor / (2 * focal))) = focal
  field_simp

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6: STANDARD LENS PRESETS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- FOV for 15mm on full frame (ultra-wide) -/
noncomputable def FOV.ultraWide : FOV := 
  FOV.fromFocalLength ⟨15, by norm_num⟩ FilmSize.fullFrame

/-- FOV for 24mm on full frame (wide) -/
noncomputable def FOV.wide24 : FOV := 
  FOV.fromFocalLength FocalLength.wide24 FilmSize.fullFrame

/-- FOV for 35mm on full frame (wide normal) -/
noncomputable def FOV.wide35 : FOV := 
  FOV.fromFocalLength FocalLength.wide35 FilmSize.fullFrame

/-- FOV for 50mm on full frame (standard) -/
noncomputable def FOV.standard : FOV := 
  FOV.fromFocalLength FocalLength.standard FilmSize.fullFrame

/-- FOV for 85mm on full frame (portrait) -/
noncomputable def FOV.portrait : FOV := 
  FOV.fromFocalLength FocalLength.portrait85 FilmSize.fullFrame

/-- FOV for 135mm on full frame (telephoto) -/
noncomputable def FOV.tele135 : FOV := 
  FOV.fromFocalLength FocalLength.telephoto135 FilmSize.fullFrame

/-- FOV for 200mm on full frame (long telephoto) -/
noncomputable def FOV.tele200 : FOV := 
  FOV.fromFocalLength FocalLength.telephoto200 FilmSize.fullFrame

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 7: CROP FACTOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Crop factor relative to full frame -/
noncomputable def cropFactor (sensor : FilmSize) : ℝ :=
  FilmSize.fullFrame.mm / sensor.mm

/-- Crop factor is positive -/
theorem cropFactor_positive (sensor : FilmSize) : cropFactor sensor > 0 := by
  unfold cropFactor
  have hs := sensor.positive
  have hff : FilmSize.fullFrame.mm > 0 := FilmSize.fullFrame.positive
  positivity

/-- Full frame has crop factor 1 -/
theorem cropFactor_fullFrame : cropFactor FilmSize.fullFrame = 1 := by
  unfold cropFactor FilmSize.fullFrame
  norm_num

/-- Equivalent focal length on full frame -/
noncomputable def equivalentFocalLength (focal : FocalLength) (sensor : FilmSize) : ℝ :=
  focal.mm * cropFactor sensor

/-- Equivalent focal length is positive -/
theorem equivalentFocalLength_positive (focal : FocalLength) (sensor : FilmSize) :
    equivalentFocalLength focal sensor > 0 := by
  unfold equivalentFocalLength
  have hf := focal.positive
  have hc := cropFactor_positive sensor
  positivity

end Hydrogen.Camera
