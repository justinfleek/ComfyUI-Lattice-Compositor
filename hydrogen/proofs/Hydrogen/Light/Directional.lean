/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                   HYDROGEN // LIGHT // DIRECTIONAL
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Directional light with proven properties.
  
  Directional lights simulate distant light sources (e.g., the sun) where
  rays are effectively parallel. They have:
  - Direction (unit vector pointing FROM the light source)
  - No position (infinitely far away)
  - No attenuation (constant intensity everywhere)
  
  KEY INVARIANTS:
    - Direction is a unit vector (length = 1)
    - Irradiance calculation uses dot product with surface normal
    - Irradiance is non-negative (clamped at grazing angles)
    - Shadow uses orthographic projection
  
  THREE.JS COMPATIBILITY:
    - direction = light.position.normalize() (position is actually direction)
    - No decay parameter
    - Shadow uses DirectionalLightShadow with orthographic camera
  
  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Types : LightBase, ColorRGB, Intensity, ShadowConfig
  - Vec3  : Direction vector, dot product
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Light.Types
import Hydrogen.Math.Vec3

namespace Hydrogen.Light

open Hydrogen.Math

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: UNIT DIRECTION VECTOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A unit vector representing direction.
    Invariant: length = 1 (enforced by proof) -/
structure UnitDirection where
  vec : Vec3
  is_unit : Vec3.lengthSq vec = 1

namespace UnitDirection

/-- Down direction (-Y), common for sun at noon -/
def down : UnitDirection where
  vec := Vec3.mk 0 (-1) 0
  is_unit := by simp [Vec3.lengthSq, Vec3.dot]

/-- Forward direction (-Z), common default -/
def forward : UnitDirection where
  vec := Vec3.mk 0 0 (-1)
  is_unit := by simp [Vec3.lengthSq, Vec3.dot]

/-- Sunlight at 45° angle (normalized) -/
noncomputable def sunlight45 : UnitDirection where
  vec := Vec3.mk 0 (-Real.sqrt 2 / 2) (-Real.sqrt 2 / 2)
  is_unit := by
    simp [Vec3.lengthSq, Vec3.dot]
    have h : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
    field_simp
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
    ring

/-- Negate direction (flip 180°) -/
def negate (d : UnitDirection) : UnitDirection where
  vec := Vec3.neg d.vec
  is_unit := by
    simp [Vec3.lengthSq, Vec3.dot, Vec3.neg]
    have h := d.is_unit
    simp [Vec3.lengthSq, Vec3.dot] at h
    linarith [sq_nonneg d.vec.x, sq_nonneg d.vec.y, sq_nonneg d.vec.z, h]

/-- Direction to light (negation of direction from light) -/
def toLight (d : UnitDirection) : UnitDirection := negate d

/-- Length of unit direction is 1 -/
noncomputable def length (d : UnitDirection) : ℝ := Vec3.length d.vec

theorem length_eq_1 (d : UnitDirection) : d.length = 1 := by
  unfold length Vec3.length
  rw [d.is_unit]
  exact Real.sqrt_one

end UnitDirection

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: DIRECTIONAL LIGHT
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Directional light (sun, distant light source).
    
    The direction vector points FROM the light source toward the scene.
    This matches Three.js convention where position is used as direction. -/
structure DirectionalLight where
  base : LightBase
  direction : UnitDirection

namespace DirectionalLight

/-- Default directional light (white, pointing down) -/
def default : DirectionalLight where
  base := LightBase.defaultWhite
  direction := UnitDirection.down

/-- Sun light preset (warm white, angled) -/
noncomputable def sun : DirectionalLight where
  base := {
    color := ColorRGB.warmWhite
    intensity := Intensity.directSunlight
    castShadow := true
    shadowConfig := ShadowConfig.highQuality
  }
  direction := UnitDirection.sunlight45

/-- Moon light preset (cool blue, low intensity) -/
def moon : DirectionalLight where
  base := {
    color := ColorRGB.coolWhite
    intensity := { value := 0.1, non_negative := by norm_num }
    castShadow := true
    shadowConfig := ShadowConfig.lowQuality
  }
  direction := UnitDirection.down

end DirectionalLight

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: IRRADIANCE CALCULATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Compute irradiance contribution from directional light on a surface.
    
    Formula: E = I * max(0, -L · N)
    
    Where:
    - E = irradiance (light per unit area)
    - I = light intensity
    - L = light direction (pointing toward scene)
    - N = surface normal (pointing away from surface)
    
    The negation of L is used because L points toward the scene,
    but we need the direction toward the light for the dot product.
    
    Result is clamped to non-negative (surfaces facing away get no light). -/
noncomputable def irradiance (light : DirectionalLight) (surfaceNormal : UnitDirection) : ℝ :=
  let dotProduct := Vec3.dot (light.direction.toLight.vec) surfaceNormal.vec
  let cosAngle := max 0 dotProduct
  light.base.intensity.value * cosAngle

/-- Irradiance is non-negative -/
theorem irradiance_nonneg (light : DirectionalLight) (normal : UnitDirection) :
    irradiance light normal ≥ 0 := by
  unfold irradiance
  simp only []
  have h1 : light.base.intensity.value ≥ 0 := light.base.intensity.non_negative
  have h2 : max 0 (Vec3.dot light.direction.toLight.vec normal.vec) ≥ 0 := le_max_left 0 _
  exact mul_nonneg h1 h2

/-- Dot product of unit vectors is bounded by 1.
    
    Proof: For unit vectors a, b with |a|² = |b|² = 1, 
    we have |a - b|² = |a|² - 2(a·b) + |b|² = 2 - 2(a·b) ≥ 0
    Therefore a·b ≤ 1 -/
theorem dot_unit_le_1 (a b : UnitDirection) : Vec3.dot a.vec b.vec ≤ 1 := by
  have ha := a.is_unit  -- |a|² = 1
  have hb := b.is_unit  -- |b|² = 1
  -- |a - b|² ≥ 0
  have hdiff : Vec3.lengthSq (Vec3.sub a.vec b.vec) ≥ 0 := by
    unfold Vec3.lengthSq Vec3.dot Vec3.sub
    have h1 : 0 ≤ (a.vec.x - b.vec.x) * (a.vec.x - b.vec.x) := mul_self_nonneg _
    have h2 : 0 ≤ (a.vec.y - b.vec.y) * (a.vec.y - b.vec.y) := mul_self_nonneg _
    have h3 : 0 ≤ (a.vec.z - b.vec.z) * (a.vec.z - b.vec.z) := mul_self_nonneg _
    linarith
  -- Expand: |a - b|² = |a|² - 2(a·b) + |b|²
  have hexpand : Vec3.lengthSq (Vec3.sub a.vec b.vec) = 
      Vec3.lengthSq a.vec - 2 * Vec3.dot a.vec b.vec + Vec3.lengthSq b.vec := by
    unfold Vec3.lengthSq Vec3.dot Vec3.sub
    ring
  rw [hexpand, ha, hb] at hdiff
  -- Now: 1 - 2(a·b) + 1 ≥ 0, so 2 - 2(a·b) ≥ 0, hence a·b ≤ 1
  linarith

/-- Irradiance is at most intensity (when surface directly faces light) -/
theorem irradiance_le_intensity (light : DirectionalLight) (normal : UnitDirection) :
    irradiance light normal ≤ light.base.intensity.value := by
  unfold irradiance
  simp only []
  have h1 : light.base.intensity.value ≥ 0 := light.base.intensity.non_negative
  -- The dot product of two unit vectors is at most 1
  have hdot : max 0 (Vec3.dot light.direction.toLight.vec normal.vec) ≤ 1 := by
    apply max_le
    · norm_num
    · exact dot_unit_le_1 light.direction.toLight normal
  calc light.base.intensity.value * max 0 (Vec3.dot light.direction.toLight.vec normal.vec)
      ≤ light.base.intensity.value * 1 := by nlinarith
    _ = light.base.intensity.value := mul_one _

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: SHADOW PROJECTION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Shadow camera frustum bounds for directional light.
    
    Directional lights use orthographic projection for shadows.
    The frustum is defined by left/right/bottom/top/near/far planes. -/
structure ShadowFrustum where
  left : ℝ
  right : ℝ
  bottom : ℝ
  top : ℝ
  near : ℝ
  far : ℝ
  left_lt_right : left < right
  bottom_lt_top : bottom < top
  near_lt_far : near < far

namespace ShadowFrustum

/-- Default frustum for shadow mapping -/
def default : ShadowFrustum where
  left := -10
  right := 10
  bottom := -10
  top := 10
  near := 0.5
  far := 500
  left_lt_right := by norm_num
  bottom_lt_top := by norm_num
  near_lt_far := by norm_num

/-- Width of frustum -/
noncomputable def width (f : ShadowFrustum) : ℝ := f.right - f.left

/-- Height of frustum -/
noncomputable def height (f : ShadowFrustum) : ℝ := f.top - f.bottom

/-- Depth of frustum -/
noncomputable def depth (f : ShadowFrustum) : ℝ := f.far - f.near

/-- Width is positive -/
theorem width_positive (f : ShadowFrustum) : f.width > 0 := by
  unfold width
  linarith [f.left_lt_right]

/-- Height is positive -/
theorem height_positive (f : ShadowFrustum) : f.height > 0 := by
  unfold height
  linarith [f.bottom_lt_top]

/-- Depth is positive -/
theorem depth_positive (f : ShadowFrustum) : f.depth > 0 := by
  unfold depth
  linarith [f.near_lt_far]

end ShadowFrustum

/-- Extended directional light with shadow configuration -/
structure DirectionalLightWithShadow where
  light : DirectionalLight
  frustum : ShadowFrustum

end Hydrogen.Light
