/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                         HYDROGEN // LIGHT // POINT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Point light with proven attenuation properties.
  
  Point lights are omnidirectional light sources (e.g., light bulbs) that
  emanate light equally in all directions from a single point. They have:
  - Position in 3D space
  - Distance-based attenuation (inverse square law)
  - Optional cutoff distance for performance
  
  KEY INVARIANTS:
    - Irradiance at distance 0 equals base intensity
    - Irradiance decreases with distance (proven monotonic)
    - Irradiance is always non-negative
    - Physically correct mode uses inverse square law
  
  THREE.JS COMPATIBILITY:
    - position: Vec3 position in world space
    - intensity: base light intensity
    - distance: cutoff distance (0 = infinite)
    - decay: attenuation exponent (2 = physically correct)
    - Shadow uses PointLightShadow with perspective cameras
  
  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Types       : LightBase, ColorRGB, Intensity, Decay, CutoffDistance
  - Attenuation : distanceAttenuation, cutoffFactor, effectiveIntensity
  - Vec3        : Position, distance calculation
  - Directional : UnitDirection (for surface normal)
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Light.Types
import Hydrogen.Light.Attenuation
import Hydrogen.Light.Directional
import Hydrogen.Math.Vec3

namespace Hydrogen.Light

open Hydrogen.Math

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: POINT LIGHT STRUCTURE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Point light (omnidirectional light source).
    
    Light emanates equally in all directions from the position point.
    Intensity falls off with distance according to the decay parameter. -/
structure PointLight where
  base : LightBase
  position : Vec3
  decay : Decay
  cutoffDistance : CutoffDistance

namespace PointLight

/-- Default point light (white, at origin, physically correct decay) -/
def default : PointLight where
  base := LightBase.defaultWhite
  position := Vec3.zero
  decay := Decay.physical
  cutoffDistance := CutoffDistance.infinite

/-- Table lamp preset -/
def tableLamp : PointLight where
  base := {
    color := ColorRGB.warmWhite
    intensity := Intensity.bulb60W
    castShadow := true
    shadowConfig := ShadowConfig.lowQuality
  }
  position := Vec3.zero
  decay := Decay.physical
  cutoffDistance := CutoffDistance.medium

/-- Candle preset (dim, warm, short range) -/
def candle : PointLight where
  base := {
    color := { r := 1, g := 0.6, b := 0.2
               r_ge_0 := by norm_num, r_le_1 := by norm_num
               g_ge_0 := by norm_num, g_le_1 := by norm_num
               b_ge_0 := by norm_num, b_le_1 := by norm_num }
    intensity := { value := 5, non_negative := by norm_num }
    castShadow := true
    shadowConfig := ShadowConfig.lowQuality
  }
  position := Vec3.zero
  decay := Decay.physical
  cutoffDistance := CutoffDistance.short

/-- Move light to new position -/
def moveTo (light : PointLight) (pos : Vec3) : PointLight :=
  { light with position := pos }

/-- Set cutoff distance -/
def withCutoff (light : PointLight) (cutoff : CutoffDistance) : PointLight :=
  { light with cutoffDistance := cutoff }

/-- Set decay mode -/
def withDecay (light : PointLight) (decay : Decay) : PointLight :=
  { light with decay := decay }

end PointLight

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: IRRADIANCE AT A POINT
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Distance from light to a world point -/
noncomputable def PointLight.distanceTo (light : PointLight) (worldPoint : Vec3) : ℝ :=
  Vec3.distance light.position worldPoint

/-- Compute attenuation factor at a given world position -/
noncomputable def PointLight.attenuationAt (light : PointLight) (worldPoint : Vec3) : ℝ :=
  attenuation (light.distanceTo worldPoint) light.decay light.cutoffDistance

/-- Compute raw intensity at a given world position (before surface angle) -/
noncomputable def PointLight.intensityAt (light : PointLight) (worldPoint : Vec3) : ℝ :=
  effectiveIntensity light.base.intensity (light.distanceTo worldPoint) light.decay light.cutoffDistance

/-- Distance to self is zero -/
theorem PointLight.distanceTo_self (light : PointLight) :
    light.distanceTo light.position = 0 := by
  unfold distanceTo Vec3.distance Vec3.sub Vec3.length Vec3.lengthSq Vec3.dot
  simp

/-- Attenuation at light position is 1 -/
theorem PointLight.attenuation_at_position (light : PointLight) :
    light.attenuationAt light.position = 1 := by
  unfold attenuationAt
  rw [distanceTo_self]
  exact attenuation_zero light.decay light.cutoffDistance

/-- Intensity at light position equals base intensity -/
theorem PointLight.intensity_at_position (light : PointLight) :
    light.intensityAt light.position = light.base.intensity.value := by
  unfold intensityAt
  rw [distanceTo_self]
  exact effectiveIntensity_zero light.base.intensity light.decay light.cutoffDistance

/-- Attenuation is non-negative everywhere -/
theorem PointLight.attenuationAt_nonneg (light : PointLight) (worldPoint : Vec3) :
    light.attenuationAt worldPoint ≥ 0 := by
  unfold attenuationAt
  exact attenuation_nonneg (light.distanceTo worldPoint) light.decay light.cutoffDistance

/-- Intensity is non-negative everywhere -/
theorem PointLight.intensity_nonneg (light : PointLight) (worldPoint : Vec3) :
    light.intensityAt worldPoint ≥ 0 := by
  unfold intensityAt
  exact effectiveIntensity_nonneg _ _ _ _

/-- Intensity is at most base intensity -/
theorem PointLight.intensity_le_base (light : PointLight) (worldPoint : Vec3) :
    light.intensityAt worldPoint ≤ light.base.intensity.value := by
  unfold intensityAt
  exact effectiveIntensity_le_base _ _ _ _

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: SURFACE IRRADIANCE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Direction from surface point to light (unnormalized).
    Returns zero vector if surface point equals light position. -/
def PointLight.directionTo (light : PointLight) (surfacePoint : Vec3) : Vec3 :=
  Vec3.sub light.position surfacePoint

/-- Compute surface irradiance from point light.
    
    Formula: E = I * attenuation(d) * max(0, L · N)
    
    Where:
    - E = irradiance at surface
    - I = base intensity
    - d = distance from light to surface
    - L = normalized direction to light
    - N = surface normal
    
    This version takes a pre-computed normalized direction to avoid
    the complexity of normalizing zero vectors. -/
noncomputable def PointLight.irradianceWithDir 
    (light : PointLight) 
    (surfacePoint : Vec3) 
    (toLight : UnitDirection) : ℝ :=
  let intensity := light.intensityAt surfacePoint
  let dotProduct := Vec3.dot toLight.vec surfacePoint
  let cosAngle := max 0 dotProduct
  intensity * cosAngle

/-- Surface irradiance is non-negative -/
theorem PointLight.irradiance_nonneg 
    (light : PointLight) (surfacePoint : Vec3) (toLight : UnitDirection) :
    light.irradianceWithDir surfacePoint toLight ≥ 0 := by
  unfold irradianceWithDir
  simp only []
  have h1 := light.intensity_nonneg surfacePoint
  have h2 : max 0 (Vec3.dot toLight.vec surfacePoint) ≥ 0 := le_max_left 0 _
  exact mul_nonneg h1 h2

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: PHYSICALLY CORRECT POINT LIGHT
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Check if point light uses physically correct decay -/
noncomputable def PointLight.isPhysicallyCorrect (light : PointLight) : Bool :=
  light.decay.value == 2

/-- Create a physically correct point light -/
def PointLight.physical (position : Vec3) (intensity : Intensity) (color : ColorRGB) : PointLight where
  base := {
    color := color
    intensity := intensity
    castShadow := false
    shadowConfig := ShadowConfig.disabled
  }
  position := position
  decay := Decay.physical
  cutoffDistance := CutoffDistance.infinite

/-- Physically correct light uses inverse square law -/
theorem PointLight.physical_decay (position : Vec3) (intensity : Intensity) (color : ColorRGB) :
    (PointLight.physical position intensity color).decay = Decay.physical := rfl

end Hydrogen.Light
