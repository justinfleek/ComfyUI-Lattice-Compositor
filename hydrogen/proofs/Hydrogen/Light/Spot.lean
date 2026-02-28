/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                          HYDROGEN // LIGHT // SPOT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Spot light with cone angle and penumbra, with proven attenuation.
  
  Spot lights emit light in a cone from a position in a direction. They have:
  - Position in 3D space
  - Direction (unit vector)
  - Cone angle (half-angle of the cone)
  - Penumbra (softness of the edge)
  - Distance attenuation (like point lights)
  
  KEY INVARIANTS:
    - Spot factor is 1 inside the cone (minus penumbra region)
    - Spot factor smoothly falls to 0 at cone edge
    - Spot factor is 0 outside the cone
    - Combined attenuation = distance attenuation × spot factor
  
  THREE.JS COMPATIBILITY:
    - angle: cone half-angle in radians (0, π/2]
    - penumbra: percentage of cone for soft edge [0, 1]
    - decay: distance attenuation exponent
    - distance: cutoff distance (0 = infinite)
    - Shadow uses SpotLightShadow with perspective camera
  
  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Types       : LightBase, ConeAngle, Penumbra, Decay, CutoffDistance
  - Attenuation : distanceAttenuation, cutoffFactor
  - Directional : UnitDirection
  - Point       : PointLight (for shared attenuation logic)
  - Vec3        : Position, direction, dot product
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Light.Types
import Hydrogen.Light.Attenuation
import Hydrogen.Light.Directional
import Hydrogen.Math.Vec3

namespace Hydrogen.Light

open Hydrogen.Math

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: SPOT LIGHT STRUCTURE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Spot light (directional cone of light from a point).
    
    The light cone is defined by:
    - position: origin of the cone
    - direction: center axis of the cone (points away from light)
    - angle: half-angle of the cone
    - penumbra: fraction of cone angle for soft falloff -/
structure SpotLight where
  base : LightBase
  position : Vec3
  direction : UnitDirection
  angle : ConeAngle
  penumbra : Penumbra
  decay : Decay
  cutoffDistance : CutoffDistance

namespace SpotLight

/-- Default spot light (white, pointing down, 30° cone) -/
noncomputable def default : SpotLight where
  base := LightBase.defaultWhite
  position := Vec3.mk 0 5 0
  direction := UnitDirection.down
  angle := ConeAngle.medium
  penumbra := Penumbra.soft
  decay := Decay.physical
  cutoffDistance := CutoffDistance.infinite

/-- Stage light preset (narrow, hard edge) -/
noncomputable def stageLight : SpotLight where
  base := {
    color := ColorRGB.white
    intensity := Intensity.bulb100W
    castShadow := true
    shadowConfig := ShadowConfig.highQuality
  }
  position := Vec3.mk 0 10 0
  direction := UnitDirection.down
  angle := ConeAngle.narrow
  penumbra := Penumbra.hard
  decay := Decay.physical
  cutoffDistance := CutoffDistance.long

/-- Flashlight preset (medium cone, soft edge) -/
noncomputable def flashlight : SpotLight where
  base := {
    color := ColorRGB.coolWhite
    intensity := { value := 200, non_negative := by norm_num }
    castShadow := true
    shadowConfig := ShadowConfig.lowQuality
  }
  position := Vec3.zero
  direction := UnitDirection.forward
  angle := ConeAngle.medium
  penumbra := Penumbra.soft
  decay := Decay.physical
  cutoffDistance := CutoffDistance.medium

/-- Move light to new position -/
def moveTo (light : SpotLight) (pos : Vec3) : SpotLight :=
  { light with position := pos }

/-- Point light in new direction -/
def pointAt (light : SpotLight) (dir : UnitDirection) : SpotLight :=
  { light with direction := dir }

/-- Set cone angle -/
def withAngle (light : SpotLight) (angle : ConeAngle) : SpotLight :=
  { light with angle := angle }

/-- Set penumbra -/
def withPenumbra (light : SpotLight) (penumbra : Penumbra) : SpotLight :=
  { light with penumbra := penumbra }

end SpotLight

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: SPOT FACTOR (Angular Attenuation)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Compute the spot factor (angular attenuation) for a point.
    
    Given:
    - toPoint: normalized direction from light to surface point
    - lightDir: light's direction (center of cone)
    - angle: cone half-angle
    - penumbra: softness of edge
    
    The spot factor is:
    - 1 if the point is inside the inner cone (angle * (1 - penumbra))
    - 0 if the point is outside the outer cone
    - Smooth interpolation in the penumbra region
    
    Implementation uses cosine comparison for efficiency:
    - cos(angle) = outer edge cutoff
    - cos(angle * (1 - penumbra)) = inner cone (full intensity) -/
noncomputable def spotFactor 
    (toPoint : UnitDirection) 
    (lightDir : UnitDirection) 
    (angle : ConeAngle) 
    (penumbra : Penumbra) : ℝ :=
  -- Dot product: 1 when aligned, 0 when perpendicular, -1 when opposite
  let cosTheta := Vec3.dot lightDir.vec toPoint.vec
  let cosOuter := angle.cosine  -- cos(angle) - outer edge
  -- Inner cone uses smaller angle (higher cosine)
  let innerAngleFactor := 1 - penumbra.value
  let cosInner := Real.cos (angle.value * innerAngleFactor)
  -- If outside outer cone: 0
  if cosTheta < cosOuter then 0
  -- If inside inner cone: 1
  else if cosTheta ≥ cosInner then 1
  -- In penumbra: smooth interpolation
  else (cosTheta - cosOuter) / (cosInner - cosOuter)

/-- Spot factor is non-negative -/
theorem spotFactor_nonneg 
    (toPoint lightDir : UnitDirection) (angle : ConeAngle) (penumbra : Penumbra) :
    spotFactor toPoint lightDir angle penumbra ≥ 0 := by
  unfold spotFactor
  simp only []
  split_ifs with h1 h2
  · norm_num
  · norm_num
  · -- In penumbra region: need to show (cosTheta - cosOuter) / (cosInner - cosOuter) ≥ 0
    -- We know cosTheta ≥ cosOuter (from ¬h1)
    -- And cosInner > cosOuter (inner cone is narrower)
    push_neg at h1
    -- cosTheta ≥ cosOuter means numerator ≥ 0
    -- cosInner > cosOuter means denominator > 0 (when penumbra > 0)
    -- So the quotient ≥ 0
    have hnum : Vec3.dot lightDir.vec toPoint.vec - angle.cosine ≥ 0 := by linarith
    -- For the denominator, we need cosInner > cosOuter
    -- This requires that innerAngleFactor < 1 (i.e., penumbra > 0) OR cosTheta < cosInner
    -- Since we're in the else branch, cosTheta < cosInner, so cosInner > cosOuter must hold
    -- (otherwise the if-then-else structure would break)
    have hdenom_pos : Real.cos (angle.value * (1 - penumbra.value)) - angle.cosine > 0 := by
      -- cosine decreases as angle increases
      -- Since angle * (1 - penumbra) ≤ angle and cosine is decreasing on [0, π]
      -- We have cos(angle * (1 - penumbra)) ≥ cos(angle)
      -- But we're in the interpolation region, so we need strict inequality
      -- This is true when penumbra > 0
      -- If penumbra = 0, then cosInner = cosOuter and we wouldn't be in this branch
      push_neg at h2
      -- h2: cosTheta < cosInner, and ¬h1: cosTheta ≥ cosOuter
      -- Therefore cosInner > cosOuter
      have : Vec3.dot lightDir.vec toPoint.vec < Real.cos (angle.value * (1 - penumbra.value)) := h2
      have : Vec3.dot lightDir.vec toPoint.vec ≥ angle.cosine := h1
      linarith
    exact div_nonneg hnum (le_of_lt hdenom_pos)

/-- Spot factor is at most 1 -/
theorem spotFactor_le_1 
    (toPoint lightDir : UnitDirection) (angle : ConeAngle) (penumbra : Penumbra) :
    spotFactor toPoint lightDir angle penumbra ≤ 1 := by
  unfold spotFactor
  simp only []
  split_ifs with h1 h2
  · norm_num
  · norm_num
  · -- In penumbra: (cosTheta - cosOuter) / (cosInner - cosOuter) ≤ 1
    -- Equivalent to: cosTheta - cosOuter ≤ cosInner - cosOuter
    -- Equivalent to: cosTheta ≤ cosInner
    -- Which is exactly h2 negated: ¬(cosTheta ≥ cosInner) means cosTheta < cosInner
    push_neg at h1 h2
    have hnum : Vec3.dot lightDir.vec toPoint.vec - angle.cosine ≤ 
                Real.cos (angle.value * (1 - penumbra.value)) - angle.cosine := by linarith
    have hdenom_pos : Real.cos (angle.value * (1 - penumbra.value)) - angle.cosine > 0 := by linarith
    rw [div_le_one hdenom_pos]
    exact hnum

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: COMBINED SPOT ATTENUATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Distance from spot light to a world point -/
noncomputable def SpotLight.distanceTo (light : SpotLight) (worldPoint : Vec3) : ℝ :=
  Vec3.distance light.position worldPoint

/-- Direction from spot light to a world point (unnormalized) -/
def SpotLight.directionTo (light : SpotLight) (worldPoint : Vec3) : Vec3 :=
  Vec3.sub worldPoint light.position

/-- Combined attenuation for spot light: distance × spot factor.
    
    This version requires a pre-normalized direction for simplicity. -/
noncomputable def SpotLight.attenuationWithDir 
    (light : SpotLight) 
    (distance : ℝ) 
    (toPoint : UnitDirection) : ℝ :=
  let distAtten := attenuation distance light.decay light.cutoffDistance
  let spotAtten := spotFactor toPoint light.direction light.angle light.penumbra
  distAtten * spotAtten

/-- Combined attenuation is non-negative -/
theorem SpotLight.attenuationWithDir_nonneg 
    (light : SpotLight) (distance : ℝ) (toPoint : UnitDirection) :
    light.attenuationWithDir distance toPoint ≥ 0 := by
  unfold attenuationWithDir
  simp only []
  have h1 := attenuation_nonneg distance light.decay light.cutoffDistance
  have h2 := spotFactor_nonneg toPoint light.direction light.angle light.penumbra
  exact mul_nonneg h1 h2

/-- Combined attenuation is at most 1 -/
theorem SpotLight.attenuationWithDir_le_1 
    (light : SpotLight) (distance : ℝ) (toPoint : UnitDirection) :
    light.attenuationWithDir distance toPoint ≤ 1 := by
  unfold attenuationWithDir
  simp only []
  have h1 := attenuation_le_1 distance light.decay light.cutoffDistance
  have h2 := spotFactor_le_1 toPoint light.direction light.angle light.penumbra
  have h3 := attenuation_nonneg distance light.decay light.cutoffDistance
  have h4 := spotFactor_nonneg toPoint light.direction light.angle light.penumbra
  calc attenuation distance light.decay light.cutoffDistance * 
       spotFactor toPoint light.direction light.angle light.penumbra
      ≤ 1 * spotFactor toPoint light.direction light.angle light.penumbra := by nlinarith
    _ = spotFactor toPoint light.direction light.angle light.penumbra := one_mul _
    _ ≤ 1 := h2

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: EFFECTIVE INTENSITY
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Compute effective intensity at a point with known direction -/
noncomputable def SpotLight.effectiveIntensityWithDir 
    (light : SpotLight) 
    (distance : ℝ) 
    (toPoint : UnitDirection) : ℝ :=
  light.base.intensity.value * light.attenuationWithDir distance toPoint

/-- Effective intensity is non-negative -/
theorem SpotLight.effectiveIntensity_nonneg 
    (light : SpotLight) (distance : ℝ) (toPoint : UnitDirection) :
    light.effectiveIntensityWithDir distance toPoint ≥ 0 := by
  unfold effectiveIntensityWithDir
  have h1 := light.base.intensity.non_negative
  have h2 := SpotLight.attenuationWithDir_nonneg light distance toPoint
  exact mul_nonneg h1 h2

/-- Effective intensity is at most base intensity -/
theorem SpotLight.effectiveIntensity_le_base 
    (light : SpotLight) (distance : ℝ) (toPoint : UnitDirection) :
    light.effectiveIntensityWithDir distance toPoint ≤ light.base.intensity.value := by
  unfold effectiveIntensityWithDir
  have h1 := light.base.intensity.non_negative
  have h2 := SpotLight.attenuationWithDir_le_1 light distance toPoint
  have h3 := SpotLight.attenuationWithDir_nonneg light distance toPoint
  calc light.base.intensity.value * light.attenuationWithDir distance toPoint
      ≤ light.base.intensity.value * 1 := by nlinarith
    _ = light.base.intensity.value := mul_one _

end Hydrogen.Light
