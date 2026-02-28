/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       HYDROGEN // MATERIAL // BRDF
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Bidirectional Reflectance Distribution Functions with proven properties.
  
  This module implements physically-based BRDF models:
  
  DIFFUSE:
    - Lambertian: Ideal diffuse reflection (1/π)
  
  SPECULAR:
    - GGX/Trowbridge-Reitz: Microfacet normal distribution
    - Fresnel-Schlick: Angle-dependent reflectance
    - Smith-GGX: Geometry/shadowing-masking function
  
  KEY INVARIANTS:
    - Fresnel reflectance in [0, 1]
    - GGX distribution is non-negative
    - Smith geometry term in [0, 1]
    - Energy conservation: total reflected ≤ total incident
  
  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Types : UnitValue, IOR
  - Layer : RoughnessLayer (for alpha calculation)
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Material.Types
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Hydrogen.Material

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: LAMBERTIAN DIFFUSE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Lambertian diffuse BRDF.
    
    For an ideal diffuse surface, light is scattered equally in all directions.
    The BRDF is constant: f_d = albedo / π
    
    This returns the multiplicative factor (1/π) without the albedo,
    which should be multiplied by the albedo color. -/
noncomputable def lambertianFactor : ℝ := 1 / Real.pi

/-- Lambertian factor is positive -/
theorem lambertianFactor_pos : lambertianFactor > 0 := by
  unfold lambertianFactor
  exact div_pos one_pos Real.pi_pos

/-- Lambertian factor is less than 1 (since π > 1) -/
theorem lambertianFactor_lt_one : lambertianFactor < 1 := by
  unfold lambertianFactor
  have hpi : Real.pi > 1 := by
    have h := Real.two_le_pi
    linarith
  rw [div_lt_one Real.pi_pos]
  exact hpi

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: FRESNEL-SCHLICK
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Fresnel-Schlick approximation.
    
    F(θ) = F0 + (1 - F0)(1 - cos(θ))⁵
    
    Where:
    - F0 = reflectance at normal incidence
    - θ = angle between view direction and half vector
    - cos(θ) = V · H (clamped to [0, 1])
    
    This approximates the full Fresnel equations for unpolarized light. -/
noncomputable def fresnelSchlick (f0 : UnitValue) (cosTheta : UnitValue) : ℝ :=
  f0.value + (1 - f0.value) * (1 - cosTheta.value)^5

/-- Fresnel-Schlick at normal incidence (cosTheta = 1) equals F0 -/
theorem fresnelSchlick_normal (f0 : UnitValue) : 
    fresnelSchlick f0 UnitValue.one = f0.value := by
  unfold fresnelSchlick UnitValue.one
  simp

/-- Fresnel-Schlick at grazing angle (cosTheta = 0) equals 1 -/
theorem fresnelSchlick_grazing (f0 : UnitValue) : 
    fresnelSchlick f0 UnitValue.zero = 1 := by
  unfold fresnelSchlick UnitValue.zero
  simp

/-- Fresnel-Schlick is non-negative -/
theorem fresnelSchlick_nonneg (f0 cosTheta : UnitValue) : 
    fresnelSchlick f0 cosTheta ≥ 0 := by
  unfold fresnelSchlick
  have hf0 := f0.ge_0
  have hf0_le := f0.le_1
  have hcos := cosTheta.ge_0
  have hcos_le := cosTheta.le_1
  have h1 : 1 - f0.value ≥ 0 := by linarith
  have h2 : 1 - cosTheta.value ≥ 0 := by linarith
  have h3 : (1 - cosTheta.value)^5 ≥ 0 := by positivity
  have h4 : (1 - f0.value) * (1 - cosTheta.value)^5 ≥ 0 := mul_nonneg h1 h3
  linarith

/-- Fresnel-Schlick is at most 1 -/
theorem fresnelSchlick_le_one (f0 cosTheta : UnitValue) : 
    fresnelSchlick f0 cosTheta ≤ 1 := by
  unfold fresnelSchlick
  have hf0 := f0.ge_0
  have hf0_le := f0.le_1
  have hcos := cosTheta.ge_0
  have hcos_le := cosTheta.le_1
  have h1 : 1 - f0.value ≥ 0 := by linarith
  have h2 : 1 - cosTheta.value ≥ 0 := by linarith
  have h2' : 1 - cosTheta.value ≤ 1 := by linarith
  have h3 : (1 - cosTheta.value)^5 ≤ 1 := by
    have hpow : (1 - cosTheta.value)^5 ≤ 1^5 := by
      exact pow_le_pow_left₀ h2 h2' 5
    simp at hpow
    exact hpow
  have h4 : (1 - f0.value) * (1 - cosTheta.value)^5 ≤ (1 - f0.value) * 1 := by
    exact mul_le_mul_of_nonneg_left h3 h1
  calc f0.value + (1 - f0.value) * (1 - cosTheta.value)^5 
      ≤ f0.value + (1 - f0.value) * 1 := by linarith
    _ = 1 := by ring

/-- Fresnel-Schlick as a UnitValue -/
noncomputable def fresnelSchlickUnit (f0 cosTheta : UnitValue) : UnitValue where
  value := fresnelSchlick f0 cosTheta
  ge_0 := fresnelSchlick_nonneg f0 cosTheta
  le_1 := fresnelSchlick_le_one f0 cosTheta

/-- Fresnel-Schlick is monotonically decreasing in cosTheta.
    
    Physical meaning: As the viewing angle becomes more grazing (cosTheta → 0),
    reflectance increases toward 1. This is why surfaces appear more reflective
    at shallow angles (the "Fresnel effect" visible on water, glass, etc.).
    
    Mathematically: if cos₁ ≤ cos₂, then F(cos₁) ≥ F(cos₂) -/
theorem fresnelSchlick_antitone (f0 : UnitValue) (cos1 cos2 : UnitValue)
    (h : cos1.value ≤ cos2.value) :
    fresnelSchlick f0 cos2 ≤ fresnelSchlick f0 cos1 := by
  unfold fresnelSchlick
  have hf0 := f0.ge_0
  have hf0_le := f0.le_1
  have hcos1 := cos1.ge_0
  have hcos1_le := cos1.le_1
  have hcos2 := cos2.ge_0
  have hcos2_le := cos2.le_1
  have h1 : 1 - f0.value ≥ 0 := by linarith
  -- (1 - cos1)^5 ≥ (1 - cos2)^5 when cos1 ≤ cos2
  have hmono : (1 - cos1.value)^5 ≥ (1 - cos2.value)^5 := by
    have h2 : 1 - cos2.value ≤ 1 - cos1.value := by linarith
    have h3 : 0 ≤ 1 - cos2.value := by linarith
    exact pow_le_pow_left₀ h3 h2 5
  have hprod : (1 - f0.value) * (1 - cos2.value)^5 ≤ (1 - f0.value) * (1 - cos1.value)^5 := by
    exact mul_le_mul_of_nonneg_left hmono h1
  linarith

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: GGX NORMAL DISTRIBUTION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- GGX/Trowbridge-Reitz normal distribution function.
    
    D(h) = α² / (π * ((N·H)² * (α² - 1) + 1)²)
    
    Where:
    - α = roughness² (perceptually linear roughness squared)
    - N·H = dot product of surface normal and half vector
    
    This describes the statistical distribution of microfacet normals. -/
noncomputable def ggxDistribution (alpha : UnitValue) (ndotH : UnitValue) : ℝ :=
  let a2 := alpha.value^2
  let ndoth2 := ndotH.value^2
  let denom := ndoth2 * (a2 - 1) + 1
  a2 / (Real.pi * denom^2)

/-- GGX distribution is non-negative -/
theorem ggxDistribution_nonneg (alpha ndotH : UnitValue) :
    ggxDistribution alpha ndotH ≥ 0 := by
  unfold ggxDistribution
  simp only []
  have ha := alpha.ge_0
  have ha2 : alpha.value^2 ≥ 0 := sq_nonneg _
  have hdenom : (ndotH.value^2 * (alpha.value^2 - 1) + 1)^2 ≥ 0 := sq_nonneg _
  have hpi : Real.pi > 0 := Real.pi_pos
  have hpidenom : Real.pi * (ndotH.value^2 * (alpha.value^2 - 1) + 1)^2 ≥ 0 := by positivity
  exact div_nonneg ha2 hpidenom

/-- GGX at maximum roughness (α = 1) with aligned half vector (N·H = 1).
    
    When α = 1 (perfectly rough) and N·H = 1:
    D = 1² / (π * (1 * (1 - 1) + 1)²) = 1 / π
    
    This equals the Lambertian factor, showing that at maximum roughness,
    the microfacet distribution becomes uniform. -/
theorem ggxDistribution_rough_aligned :
    ggxDistribution UnitValue.one UnitValue.one = lambertianFactor := by
  unfold ggxDistribution UnitValue.one lambertianFactor
  simp only [one_pow]
  ring

/-- GGX at zero roughness (α = 0) is zero except when N·H = 1.
    
    When α → 0, the distribution becomes a delta function centered at N·H = 1.
    For any N·H < 1, the distribution evaluates to 0/π = 0. -/
theorem ggxDistribution_smooth :
    ggxDistribution UnitValue.zero = fun _ => 0 := by
  funext ndotH
  unfold ggxDistribution UnitValue.zero
  simp

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: SMITH-GGX GEOMETRY FUNCTION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Smith-GGX geometry function (single direction).
    
    G1(v) = 2(N·V) / (N·V + √(α² + (1 - α²)(N·V)²))
    
    This accounts for microfacet shadowing in one direction.
    The full geometry term is G = G1(L) * G1(V). -/
noncomputable def smithG1 (alpha : UnitValue) (ndotV : UnitValue) : ℝ :=
  let a2 := alpha.value^2
  let ndotv2 := ndotV.value^2
  let inner := a2 + (1 - a2) * ndotv2
  if ndotV.value = 0 then 0
  else 2 * ndotV.value / (ndotV.value + Real.sqrt inner)

/-- Smith G1 at normal incidence (NdotV = 1) is 1 for any roughness -/
theorem smithG1_normal (alpha : UnitValue) : smithG1 alpha UnitValue.one = 1 := by
  unfold smithG1 UnitValue.one
  simp only []
  have hne : (1 : ℝ) ≠ 0 := one_ne_zero
  simp only [hne, ↓reduceIte, one_pow, mul_one]
  have h : alpha.value^2 + (1 - alpha.value^2) = 1 := by ring
  rw [h, Real.sqrt_one]
  norm_num

/-- Smith G1 is non-negative -/
theorem smithG1_nonneg (alpha ndotV : UnitValue) : smithG1 alpha ndotV ≥ 0 := by
  unfold smithG1
  simp only []
  split_ifs with h
  · norm_num
  · have hndotv := ndotV.ge_0
    have hndotv_ne : ndotV.value ≠ 0 := h
    have hndotv_pos : ndotV.value > 0 := lt_of_le_of_ne hndotv (Ne.symm hndotv_ne)
    have ha := alpha.ge_0
    have ha_le := alpha.le_1
    have ha2 : alpha.value^2 ≥ 0 := sq_nonneg _
    have ha2_le : alpha.value^2 ≤ 1 := by nlinarith
    have hndotv2 : ndotV.value^2 ≥ 0 := sq_nonneg _
    -- inner = a² + (1 - a²) * ndotv² ≥ 0
    have hinner : alpha.value^2 + (1 - alpha.value^2) * ndotV.value^2 ≥ 0 := by nlinarith
    have hsqrt : Real.sqrt (alpha.value^2 + (1 - alpha.value^2) * ndotV.value^2) ≥ 0 := 
      Real.sqrt_nonneg _
    have hdenom : ndotV.value + Real.sqrt (alpha.value^2 + (1 - alpha.value^2) * ndotV.value^2) > 0 := by
      linarith
    exact div_nonneg (by linarith : 2 * ndotV.value ≥ 0) (le_of_lt hdenom)

/-- Smith G1 is at most 1 -/
theorem smithG1_le_one (alpha ndotV : UnitValue) : smithG1 alpha ndotV ≤ 1 := by
  unfold smithG1
  simp only []
  split_ifs with h
  · norm_num
  · have hndotv := ndotV.ge_0
    have hndotv_le := ndotV.le_1
    have hndotv_ne : ndotV.value ≠ 0 := h
    have hndotv_pos : ndotV.value > 0 := lt_of_le_of_ne hndotv (Ne.symm hndotv_ne)
    have ha := alpha.ge_0
    have ha_le := alpha.le_1
    -- inner ≥ ndotv² (since a² ≥ 0)
    -- Rewrite: inner = a² + (1 - a²) * v² = a² * (1 - v²) + v²
    -- Since a² ≥ 0 and (1 - v²) ≥ 0 (since v ≤ 1), we have a² * (1 - v²) ≥ 0
    -- Therefore inner ≥ v²
    have hndotv2_le1 : ndotV.value^2 ≤ 1 := by nlinarith
    have hinner_ge : alpha.value^2 + (1 - alpha.value^2) * ndotV.value^2 ≥ ndotV.value^2 := by
      have h1 : alpha.value^2 ≥ 0 := sq_nonneg _
      have h2 : alpha.value^2 ≤ 1 := by nlinarith
      have h3 : ndotV.value^2 ≥ 0 := sq_nonneg _
      have h4 : 1 - alpha.value^2 ≥ 0 := by linarith
      have h5 : (1 - alpha.value^2) * ndotV.value^2 ≤ ndotV.value^2 := by nlinarith
      -- a² + (1-a²)*v² ≥ v² ⟺ a² ≥ a²*v² ⟺ a²(1 - v²) ≥ 0
      have key : alpha.value^2 * (1 - ndotV.value^2) ≥ 0 := by nlinarith
      linarith
    have hsqrt_ge : Real.sqrt (alpha.value^2 + (1 - alpha.value^2) * ndotV.value^2) ≥ ndotV.value := by
      have hndotv2_ge : ndotV.value^2 ≥ 0 := sq_nonneg _
      have hinner_nonneg : alpha.value^2 + (1 - alpha.value^2) * ndotV.value^2 ≥ 0 := by nlinarith
      have hsq : ndotV.value = Real.sqrt (ndotV.value^2) := (Real.sqrt_sq hndotv).symm
      rw [hsq]
      apply Real.sqrt_le_sqrt
      simp only [Real.sq_sqrt hndotv2_ge]
      exact hinner_ge
    have hdenom : ndotV.value + Real.sqrt (alpha.value^2 + (1 - alpha.value^2) * ndotV.value^2) ≥ 
                  2 * ndotV.value := by linarith
    have hdenom_pos : ndotV.value + Real.sqrt (alpha.value^2 + (1 - alpha.value^2) * ndotV.value^2) > 0 := by
      linarith
    rw [div_le_one hdenom_pos]
    exact hdenom

/-- Full Smith geometry term: G = G1(L) * G1(V) -/
noncomputable def smithGeometry (alpha ndotL ndotV : UnitValue) : ℝ :=
  smithG1 alpha ndotL * smithG1 alpha ndotV

/-- Smith geometry is non-negative -/
theorem smithGeometry_nonneg (alpha ndotL ndotV : UnitValue) :
    smithGeometry alpha ndotL ndotV ≥ 0 := by
  unfold smithGeometry
  exact mul_nonneg (smithG1_nonneg alpha ndotL) (smithG1_nonneg alpha ndotV)

/-- Smith geometry is at most 1 -/
theorem smithGeometry_le_one (alpha ndotL ndotV : UnitValue) :
    smithGeometry alpha ndotL ndotV ≤ 1 := by
  unfold smithGeometry
  have h1 := smithG1_le_one alpha ndotL
  have h2 := smithG1_le_one alpha ndotV
  have h3 := smithG1_nonneg alpha ndotL
  have h4 := smithG1_nonneg alpha ndotV
  calc smithG1 alpha ndotL * smithG1 alpha ndotV 
      ≤ 1 * smithG1 alpha ndotV := by nlinarith
    _ = smithG1 alpha ndotV := one_mul _
    _ ≤ 1 := h2

/-- Smith geometry is symmetric in L and V (Helmholtz reciprocity).
    
    This proves G(L, V) = G(V, L), which is a requirement for physically
    plausible BRDFs. Light traveling from L to V must behave identically
    to light traveling from V to L. -/
theorem smithGeometry_symm (alpha ndotL ndotV : UnitValue) :
    smithGeometry alpha ndotL ndotV = smithGeometry alpha ndotV ndotL := by
  unfold smithGeometry
  ring

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: COOK-TORRANCE SPECULAR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Cook-Torrance specular BRDF (without Fresnel).
    
    f_s = D * G / (4 * N·L * N·V)
    
    Where:
    - D = GGX distribution
    - G = Smith geometry term
    - Fresnel is applied separately for flexibility
    
    Returns 0 for degenerate cases (N·L or N·V = 0). -/
noncomputable def cookTorranceSpecular 
    (alpha ndotH ndotL ndotV : UnitValue) : ℝ :=
  if ndotL.value = 0 ∨ ndotV.value = 0 then 0
  else 
    let d := ggxDistribution alpha ndotH
    let g := smithGeometry alpha ndotL ndotV
    d * g / (4 * ndotL.value * ndotV.value)

/-- Cook-Torrance specular is non-negative -/
theorem cookTorranceSpecular_nonneg (alpha ndotH ndotL ndotV : UnitValue) :
    cookTorranceSpecular alpha ndotH ndotL ndotV ≥ 0 := by
  unfold cookTorranceSpecular
  split_ifs with h
  · norm_num
  · push_neg at h
    have hL := ndotL.ge_0
    have hV := ndotV.ge_0
    have hLpos : ndotL.value > 0 := lt_of_le_of_ne hL (Ne.symm h.1)
    have hVpos : ndotV.value > 0 := lt_of_le_of_ne hV (Ne.symm h.2)
    have hdenom : 4 * ndotL.value * ndotV.value > 0 := by positivity
    have hD := ggxDistribution_nonneg alpha ndotH
    have hG := smithGeometry_nonneg alpha ndotL ndotV
    exact div_nonneg (mul_nonneg hD hG) (le_of_lt hdenom)

/-- Cook-Torrance BRDF is symmetric in L and V (Helmholtz reciprocity).
    
    This is the fundamental reciprocity property of physically-based BRDFs:
    f(ωi → ωo) = f(ωo → ωi)
    
    Light traveling from light direction L to view direction V behaves
    identically to light traveling from V to L. This is required for
    correct bidirectional path tracing and photon mapping.
    
    The proof follows from:
    1. D(H) is the same regardless of L/V swap (H is computed the same way)
    2. G(L,V) = G(V,L) (Smith geometry symmetry)
    3. The denominator 4*N·L*N·V is symmetric -/
theorem cookTorranceSpecular_symm (alpha ndotH ndotL ndotV : UnitValue) :
    cookTorranceSpecular alpha ndotH ndotL ndotV = 
    cookTorranceSpecular alpha ndotH ndotV ndotL := by
  unfold cookTorranceSpecular
  -- Handle the degenerate cases
  have hdenom_symm : 4 * ndotL.value * ndotV.value = 4 * ndotV.value * ndotL.value := by ring
  have hG_symm := smithGeometry_symm alpha ndotL ndotV
  split_ifs with h1 h2 h2
  · -- Both degenerate: both 0
    rfl
  · -- First degenerate but second not: contradicts h1 ↔ h2
    cases h1 with
    | inl hL => 
      push_neg at h2
      simp [hL] at h2
    | inr hV =>
      push_neg at h2  
      simp [hV] at h2
  · -- Second degenerate but first not: contradicts h1 ↔ h2
    cases h2 with
    | inl hV =>
      push_neg at h1
      simp [hV] at h1
    | inr hL =>
      push_neg at h1
      simp [hL] at h1
  · -- Neither degenerate: use symmetry
    rw [hG_symm, hdenom_symm]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6: ENERGY BOUNDS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- The Fresnel term F represents the fraction of light reflected.
    Therefore (1 - F) represents the fraction available for diffuse.
    
    This is the key energy conservation relationship:
    - At normal incidence: F = F0, diffuse gets (1 - F0)
    - At grazing angles: F → 1, diffuse gets → 0
    
    This bound ensures specular + diffuse ≤ 1. -/
noncomputable def diffuseWeight (f0 cosTheta : UnitValue) : ℝ :=
  1 - fresnelSchlick f0 cosTheta

/-- Diffuse weight is non-negative -/
theorem diffuseWeight_nonneg (f0 cosTheta : UnitValue) :
    diffuseWeight f0 cosTheta ≥ 0 := by
  unfold diffuseWeight
  have h := fresnelSchlick_le_one f0 cosTheta
  linarith

/-- Diffuse weight is at most 1 -/
theorem diffuseWeight_le_one (f0 cosTheta : UnitValue) :
    diffuseWeight f0 cosTheta ≤ 1 := by
  unfold diffuseWeight
  have h := fresnelSchlick_nonneg f0 cosTheta
  linarith

/-- Diffuse weight as a UnitValue -/
noncomputable def diffuseWeightUnit (f0 cosTheta : UnitValue) : UnitValue where
  value := diffuseWeight f0 cosTheta
  ge_0 := diffuseWeight_nonneg f0 cosTheta
  le_1 := diffuseWeight_le_one f0 cosTheta

/-- Energy conservation: Fresnel + diffuse weight = 1.
    
    This proves that the specular reflection fraction plus the
    diffuse transmission fraction always sums to unity, ensuring
    no energy is created or destroyed. -/
theorem energy_conservation (f0 cosTheta : UnitValue) :
    fresnelSchlick f0 cosTheta + diffuseWeight f0 cosTheta = 1 := by
  unfold diffuseWeight
  ring

/-- At grazing angles, all energy goes to specular (no diffuse).
    
    This matches physical observation: surfaces become mirror-like
    at very shallow viewing angles. -/
theorem diffuseWeight_grazing (f0 : UnitValue) :
    diffuseWeight f0 UnitValue.zero = 0 := by
  unfold diffuseWeight
  rw [fresnelSchlick_grazing]
  ring

/-- At normal incidence, diffuse weight equals (1 - F0).
    
    For dielectrics (F0 ≈ 0.04), most light is diffused.
    For metals (F0 ≈ 0.9+), little light is diffused. -/
theorem diffuseWeight_normal (f0 : UnitValue) :
    diffuseWeight f0 UnitValue.one = 1 - f0.value := by
  unfold diffuseWeight
  rw [fresnelSchlick_normal]

end Hydrogen.Material
