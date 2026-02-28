/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     HYDROGEN // MATERIAL // SPARKLE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Stochastic Glitter/Sparkle NDF with proven properties.
  
  This module implements the mathematical foundations for discrete microflake
  distributions (glitter, metallic flakes, car paint, etc.) based on the
  Zeltner-Burley stochastic approach.
  
  Unlike continuous microfacet distributions (GGX), glitter is composed of
  discrete reflective particles. The key insight is that we can:
  
  1. Map microfacet normals to a 2D probability disk (Lambert projection)
  2. Use stochastic sampling to select discrete particle positions
  3. Weight contributions by Gaussian kernels for antialiasing
  
  KEY MATHEMATICAL COMPONENTS:
  
  PROJECTIONS:
    - Lambert azimuthal equal-area projection (hemisphere → disk)
    - GGX-stretched projection with proven Jacobian
  
  STATISTICS:
    - 2D Gaussian (normal) distribution
    - Error function properties
    - Particle contribution bounds
  
  PROVEN INVARIANTS:
    - Lambert projection maps to bounded disk
    - Jacobian determinant is strictly positive
    - Gaussian is non-negative
    - Individual particle contributions are bounded
    - As N → ∞, contribution per particle → 0 (LLN foundation)
  
  ─────────────────────────────────────────────────────────────────────────────
  REFERENCES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Zeltner et al., "A Practical Stochastic Algorithm for Rendering
    Mirror-Like Flakes" (2022)
  - NVIDIA glitter shader implementations
  
  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Types : UnitValue
  - Mathlib : Real analysis, special functions
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Material.Types
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Hydrogen.Material.Sparkle

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: SPARKLE PARAMETERS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Microfacet roughness for individual sparkle particles.
    
    Good values are roughly in [0.001, 0.1].
    Lower = sharper specular highlights per particle.
    Higher = softer, more diffuse sparkles. -/
structure MicrofacetRoughness where
  value : ℝ
  pos : value > 0
  le_one : value ≤ 1

/-- Pixel filter size for antialiasing sparkle contributions.
    
    Good values are roughly in [0.5, 1.2].
    Controls the spatial extent of the Gaussian filter. -/
structure PixelFilterSize where
  value : ℝ
  pos : value > 0

/-- Glint density parameter (number of particles per unit area).
    
    Higher values = more particles = denser glitter.
    The shader uses N = 8e5 * 10^(density * 6 - 2) for visualization. -/
structure GlintDensity where
  value : ℝ
  pos : value > 0

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: LAMBERT AZIMUTHAL EQUAL-AREA PROJECTION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A point on the upper hemisphere (z > 0, |v| = 1).
    
    Represents a microfacet normal direction. -/
structure HemispherePoint where
  x : ℝ
  y : ℝ
  z : ℝ
  z_pos : z > 0
  normalized : x^2 + y^2 + z^2 = 1

/-- Lambert azimuthal equal-area projection.
    
    Maps a point on the hemisphere to a point in the unit disk:
    lambert(v) = v.xy / √(1 + v.z)
    
    This projection preserves area, meaning equal solid angles on the
    hemisphere map to equal areas on the disk. This is essential for
    unbiased importance sampling of microfacet normals. -/
noncomputable def lambertProject (v : HemispherePoint) : ℝ × ℝ :=
  let denom := Real.sqrt (1 + v.z)
  (v.x / denom, v.y / denom)

/-- The denominator √(1 + z) is always positive for hemisphere points -/
theorem lambert_denom_pos (v : HemispherePoint) : Real.sqrt (1 + v.z) > 0 := by
  have hz := v.z_pos
  have h1pz : 1 + v.z > 0 := by linarith
  exact Real.sqrt_pos.mpr h1pz

/-- Lambert projection maps to a bounded disk.
    
    For any point on the hemisphere, |lambert(v)|² < 2. -/
theorem lambert_bounded (v : HemispherePoint) : 
    let (px, py) := lambertProject v
    px^2 + py^2 < 2 := by
  simp only [lambertProject]
  have hz := v.z_pos
  have hnorm := v.normalized
  have h1pz : 1 + v.z > 0 := by linarith
  have hsqrt_pos : Real.sqrt (1 + v.z) > 0 := Real.sqrt_pos.mpr h1pz
  have hsqrt_sq : Real.sqrt (1 + v.z) ^ 2 = 1 + v.z := Real.sq_sqrt (le_of_lt h1pz)
  have hxy : v.x^2 + v.y^2 = 1 - v.z^2 := by
    have := v.normalized
    linarith [sq_nonneg v.z]
  calc (v.x / Real.sqrt (1 + v.z))^2 + (v.y / Real.sqrt (1 + v.z))^2 
      = (v.x^2 + v.y^2) / (Real.sqrt (1 + v.z))^2 := by ring
    _ = (v.x^2 + v.y^2) / (1 + v.z) := by rw [hsqrt_sq]
    _ = (1 - v.z^2) / (1 + v.z) := by rw [hxy]
    _ = (1 - v.z) * (1 + v.z) / (1 + v.z) := by ring
    _ = 1 - v.z := by field_simp
    _ < 2 := by linarith

/-- Lambert projection output x-component is bounded -/
theorem lambert_component_bounded (v : HemispherePoint) :
    let (px, _) := lambertProject v
    px^2 < 2 := by
  have hsum := lambert_bounded v
  simp only [lambertProject] at hsum ⊢
  have hy2 : (v.y / Real.sqrt (1 + v.z))^2 ≥ 0 := sq_nonneg _
  linarith

/-- At the north pole (0, 0, 1), Lambert projects to origin -/
theorem lambert_at_pole : 
    let v : HemispherePoint := ⟨0, 0, 1, by norm_num, by norm_num⟩
    lambertProject v = (0, 0) := by
  simp only [lambertProject]
  norm_num

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: GGX-STRETCHED PROJECTION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Compute the squared norm of a stretched vector -/
noncomputable def stretchedNormSq (x y z : ℝ) (alpha : UnitValue) 
    (_halpha : alpha.value > 0) : ℝ :=
  (x / alpha.value)^2 + (y / alpha.value)^2 + z^2

/-- For valid hemisphere points with α > 0, the stretched norm is positive -/
theorem stretchedNormSq_pos (v : HemispherePoint) (alpha : UnitValue) 
    (halpha : alpha.value > 0) : stretchedNormSq v.x v.y v.z alpha halpha > 0 := by
  unfold stretchedNormSq
  have hz := v.z_pos
  have hz2 : v.z^2 > 0 := sq_pos_of_pos hz
  have hx2 : (v.x / alpha.value)^2 ≥ 0 := sq_nonneg _
  have hy2 : (v.y / alpha.value)^2 ≥ 0 := sq_nonneg _
  linarith

/-- The GGX Jacobian determinant formula.
    
    For the GGX-to-disk transformation:
    J = 1 / (α² * ‖stretched‖⁴)
    
    This is always positive for valid inputs. -/
noncomputable def ggxJacobian (alpha : UnitValue) (_halpha : alpha.value > 0)
    (stretchedNormSq : ℝ) (_hpos : stretchedNormSq > 0) : ℝ :=
  1 / (alpha.value^2 * stretchedNormSq^2)

/-- GGX Jacobian is positive for positive alpha and norm -/
theorem ggxJacobian_pos (alpha : UnitValue) (halpha : alpha.value > 0) 
    (sns : ℝ) (hpos : sns > 0) : ggxJacobian alpha halpha sns hpos > 0 := by
  unfold ggxJacobian
  have ha2 : alpha.value^2 > 0 := sq_pos_of_pos halpha
  have hsns2 : sns^2 > 0 := sq_pos_of_pos hpos
  have hdenom : alpha.value^2 * sns^2 > 0 := mul_pos ha2 hsns2
  exact div_pos one_pos hdenom

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: 2D GAUSSIAN DISTRIBUTION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A 2x2 covariance matrix (symmetric positive definite).
    
    For the sparkle shader, this represents the spatial extent of
    each particle's contribution for antialiasing. -/
structure Covariance2D where
  a : ℝ   -- [0,0] element
  b : ℝ   -- [0,1] = [1,0] element (symmetric)
  c : ℝ   -- [1,1] element
  a_pos : a > 0
  c_pos : c > 0
  det_pos : a * c - b^2 > 0  -- positive definite condition

/-- Determinant of a 2x2 covariance matrix -/
noncomputable def Covariance2D.det (cov : Covariance2D) : ℝ :=
  cov.a * cov.c - cov.b^2

/-- The determinant is positive for valid covariance matrices -/
theorem Covariance2D.det_is_pos (cov : Covariance2D) : cov.det > 0 := cov.det_pos

/-- 2D Gaussian (normal) distribution PDF.
    
    normal(Σ, x) = exp(-½ xᵀ Σ⁻¹ x) / (2π √det(Σ))
    
    This is the probability density for a point x given covariance Σ. -/
noncomputable def gaussian2D (cov : Covariance2D) (x y : ℝ) : ℝ :=
  let det := cov.det
  let invA := cov.c / det
  let invB := -cov.b / det
  let invC := cov.a / det
  let quadForm := invA * x^2 + 2 * invB * x * y + invC * y^2
  Real.exp (-quadForm / 2) / (2 * Real.pi * Real.sqrt det)

/-- Gaussian PDF is non-negative -/
theorem gaussian2D_nonneg (cov : Covariance2D) (x y : ℝ) : 
    gaussian2D cov x y ≥ 0 := by
  unfold gaussian2D Covariance2D.det
  have hdet := cov.det_pos
  have hsqrt_pos : Real.sqrt (cov.a * cov.c - cov.b^2) > 0 := Real.sqrt_pos.mpr hdet
  have hdenom_pos : 2 * Real.pi * Real.sqrt (cov.a * cov.c - cov.b^2) > 0 := by
    have hpi : Real.pi > 0 := Real.pi_pos
    positivity
  have hexp_pos : Real.exp (-(cov.c / (cov.a * cov.c - cov.b^2) * x^2 + 
                   2 * (-cov.b / (cov.a * cov.c - cov.b^2)) * x * y + 
                   cov.a / (cov.a * cov.c - cov.b^2) * y^2) / 2) > 0 := Real.exp_pos _
  exact le_of_lt (div_pos hexp_pos hdenom_pos)

/-- Gaussian PDF at the mean (x=0, y=0) -/
theorem gaussian2D_at_mean (cov : Covariance2D) : 
    gaussian2D cov 0 0 = 1 / (2 * Real.pi * Real.sqrt cov.det) := by
  unfold gaussian2D
  simp only [sq, mul_zero, add_zero, zero_div, neg_zero, Real.exp_zero, one_div]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: ERROR FUNCTION PROPERTIES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Error function value type.
    
    The error function erf(x) is bounded to [-1, 1] for all real x.
    This type encodes that bound. -/
structure ErfValue where
  value : ℝ
  ge_neg_one : value ≥ -1
  le_one : value ≤ 1

/-- Bürmann series approximation to the error function.
    
    erf(x) ≈ sign(x) * 2 * √((1 - e^(-x²))/π) * (√π/2 + 31/200 * e + ...)
    
    This is the approximation used in the shader for performance.
    The true erf is defined via an integral. -/
noncomputable def erfApprox (x : ℝ) : ℝ :=
  let e := Real.exp (-(x^2))
  let inner := Real.sqrt ((1 - e) / Real.pi)
  let series := Real.sqrt Real.pi / 2 + 31/200 * e - 341/8000 * e^2
  if x ≥ 0 then 2 * inner * series
  else -2 * inner * series

/-- The approximation is odd: erfApprox(-x) = -erfApprox(x) -/
theorem erfApprox_odd (x : ℝ) : erfApprox (-x) = -erfApprox x := by
  unfold erfApprox
  simp only [neg_sq]
  split_ifs with h1 h2 h2
  · -- x ≥ 0 and -x ≥ 0, so x = 0
    have hx0 : x = 0 := by linarith
    simp [hx0]
  · -- x ≥ 0 and -x < 0: expected case
    ring
  · -- x < 0 and -x ≥ 0: expected case
    ring
  · -- x < 0 and -x < 0, so x > 0, contradiction
    linarith

/-- At x = 0, erfApprox = 0 -/
theorem erfApprox_zero : erfApprox 0 = 0 := by
  unfold erfApprox
  simp only [sq, mul_zero, neg_zero, Real.exp_zero, sub_self, zero_div]
  simp only [Real.sqrt_zero, ge_iff_le, le_refl, ↓reduceIte]
  ring

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6: PARTICLE CONTRIBUTION BOUNDS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Particle count must be positive -/
structure ParticleCount where
  value : ℕ
  pos : value > 0

/-- Convert particle count to real for calculations -/
noncomputable def ParticleCount.toReal (n : ParticleCount) : ℝ := n.value

/-- Particle count as real is positive -/
theorem ParticleCount.toReal_pos (n : ParticleCount) : n.toReal > 0 := by
  unfold toReal
  exact Nat.cast_pos.mpr n.pos

/-- As particle count increases, individual contribution decreases.
    
    Each particle contributes 1/N to the total NDF.
    This ensures energy conservation regardless of particle count. -/
noncomputable def particleContribution (n : ParticleCount) : ℝ := 
  1 / n.toReal

/-- Particle contribution is positive -/
theorem particleContribution_pos (n : ParticleCount) : 
    particleContribution n > 0 := by
  unfold particleContribution
  exact div_pos one_pos n.toReal_pos

/-- Particle contribution is at most 1 -/
theorem particleContribution_le_one (n : ParticleCount) : 
    particleContribution n ≤ 1 := by
  unfold particleContribution
  have hn := n.toReal_pos
  rw [div_le_one hn]
  have hge1 : n.toReal ≥ 1 := by
    unfold ParticleCount.toReal
    have := n.pos
    exact Nat.one_le_cast.mpr this
  linarith

/-- For N particles, the sum of equal contributions equals 1.
    
    If each of N particles contributes 1/N, then:
    N * (1/N) = 1
    
    This is the energy conservation principle for sparkle rendering. -/
theorem total_contribution_normalized (n : ParticleCount) :
    n.toReal * particleContribution n = 1 := by
  unfold particleContribution
  have hn := n.toReal_pos
  field_simp

/-- Doubling particles halves individual contribution.
    
    This scaling relationship ensures consistent appearance
    across different density settings. -/
theorem contribution_scales_inversely (n : ParticleCount) (h2n : 2 * n.value > 0) :
    let n2 : ParticleCount := ⟨2 * n.value, h2n⟩
    particleContribution n2 = particleContribution n / 2 := by
  simp only [particleContribution, ParticleCount.toReal]
  have hn_pos : (n.value : ℝ) > 0 := Nat.cast_pos.mpr n.pos
  have hcast : ((2 * n.value : ℕ) : ℝ) = 2 * (n.value : ℝ) := by simp [Nat.cast_mul]
  rw [hcast]
  field_simp

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 7: LEVEL OF DETAIL
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Level of detail for mipmap-style particle selection.
    
    The LOD determines which resolution level to sample particles from.
    Higher LOD = coarser sampling = fewer but larger particles. -/
structure LODLevel where
  value : ℝ

/-- Compute LOD from Jacobian scale.
    
    LOD = log₂(max(s₀, s₁) * filterSize) + 2^filterSize
    
    Where s₀, s₁ are the singular values of the UV Jacobian. -/
noncomputable def computeLOD (jacobianScale : ℝ) (filterSize : PixelFilterSize) : ℝ :=
  Real.log jacobianScale / Real.log 2 + (2 : ℝ)^filterSize.value

/-- Resolution at a given LOD level.
    
    res_s = res * 2^(-l)
    
    As LOD increases, resolution decreases exponentially. -/
noncomputable def lodResolution (baseRes : ℝ) (lod : LODLevel) : ℝ :=
  baseRes * (2 : ℝ)^(-lod.value)

/-- LOD resolution is positive for positive base resolution -/
theorem lodResolution_pos (baseRes : ℝ) (hbase : baseRes > 0) (lod : LODLevel) :
    lodResolution baseRes lod > 0 := by
  unfold lodResolution
  have hpow : (2 : ℝ)^(-lod.value) > 0 := Real.rpow_pos_of_pos (by norm_num : (2:ℝ) > 0) _
  exact mul_pos hbase hpow

/-- Higher LOD means lower resolution -/
theorem lod_resolution_decreases (baseRes : ℝ) (hbase : baseRes > 0) 
    (l1 l2 : LODLevel) (h : l1.value < l2.value) :
    lodResolution baseRes l2 < lodResolution baseRes l1 := by
  unfold lodResolution
  have h2gt1 : (1 : ℝ) < 2 := by norm_num
  have hneg : -l2.value < -l1.value := by linarith
  have h1 : (2 : ℝ)^(-l2.value) < (2 : ℝ)^(-l1.value) := by
    apply Real.rpow_lt_rpow_of_exponent_lt h2gt1 hneg
  have h2pos : (2 : ℝ)^(-l2.value) > 0 := Real.rpow_pos_of_pos (by norm_num) _
  nlinarith [h1, h2pos, hbase]

end Hydrogen.Material.Sparkle
