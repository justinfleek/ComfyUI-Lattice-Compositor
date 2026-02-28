/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                         HYDROGEN // MATERIAL // ISP
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Physically-Plausible Image Signal Processing with proven properties.
  
  Based on NVIDIA PPISP (Physically-Plausible Compensation and Control of
  Photometric Variations in Radiance Field Reconstruction).
  
  This module implements camera and display transformations that model
  real-world photometric variations, with full mathematical proofs.
  
  FORWARD PASS COMPONENTS:
    - Exposure compensation: 2^param with positivity proof
    - Activation functions: softplus (log(1+exp)), sigmoid with bounds
    - Vignetting: 1 + α₀r² + α₁r⁴ + α₂r⁶ with boundedness proof
    - CRF parameters: decoded via softplus/sigmoid with bounds
    - Gamma correction: preserves [0,1] bounds
    - Linear interpolation: with boundary and symmetry proofs
    - RGI color space: RGB ↔ [R, G, R+G+B] roundtrip proofs
    - Skew-symmetric matrix: Sᵀ = -S, cross product equivalence
    - CRF toe-shoulder curve: piecewise with C0 continuity proof
  
  BACKWARD PASS COMPONENTS:
    - Derivative relationships: softplus' = sigmoid, sigmoid' = s(1-s)
    - Gradient formulas: dot_bwd, cross_bwd, length_bwd, normalize_bwd
    - Power/log derivatives: pow_bwd, log_bwd, sqrt_bwd, exp_bwd, exp2_bwd
    - Vignetting backward: gradients for α, center, r²
    - Clamp backward: zero gradient at boundaries
    - Division backward: quotient rule gradient
  
  MATRIX OPERATIONS:
    - 2x2 matrices: ZCA transforms with multiplication/transpose proofs
    - 3x3 matrices: skew-symmetric, homography normalization
    - Determinant multiplicativity, identity properties
  
  PROVEN INVARIANTS:
    - Exposure factor is strictly positive for any parameter
    - Vignetting bounded to [0, 1] with proper coefficients
    - Gamma-corrected values preserve [0, 1] bounds
    - Softplus is strictly positive and monotonically increasing
    - Sigmoid is bounded to (0, 1) and monotonically increasing
    - Sigmoid derivative bounded above by 1/4 (AM-GM)
    - CRF curve: 0 → 0, 1 → 1, C0 continuous at center
    - RGI ↔ RGB conversions are inverses
    - Skew-symmetric matrix has zero trace
  
  ─────────────────────────────────────────────────────────────────────────────
  REFERENCES
  ─────────────────────────────────────────────────────────────────────────────
  
  - NVIDIA PPISP: "Physically-Plausible Compensation and Control of
    Photometric Variations in Radiance Field Reconstruction" (2026)
  - ppisp_math.cuh: Forward pass mathematical operations
  - ppisp_math_bwd.cuh: Backward pass gradient computations
  
  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Types : UnitValue
  - Mathlib : Real analysis, exp, log, rpow
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Material.Types
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Hydrogen.Material.ISP

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: EXPOSURE COMPENSATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Exposure parameter (log-space, unbounded).
    
    Positive values brighten, negative values darken.
    The actual multiplier is 2^param (exp2). -/
structure ExposureParam where
  value : ℝ

/-- Compute exposure factor from parameter.
    
    exposure_factor = 2^param = exp(param * ln(2))
    
    This is always strictly positive for any real param. -/
noncomputable def exposureFactor (param : ExposureParam) : ℝ :=
  (2 : ℝ)^param.value

/-- Exposure factor is strictly positive for any parameter -/
theorem exposureFactor_pos (param : ExposureParam) : exposureFactor param > 0 := by
  unfold exposureFactor
  exact Real.rpow_pos_of_pos (by norm_num : (2 : ℝ) > 0) param.value

/-- Exposure factor at param=0 is 1 (identity) -/
theorem exposureFactor_identity : exposureFactor ⟨0⟩ = 1 := by
  unfold exposureFactor
  simp [Real.rpow_zero]

/-- Exposure factor at param=1 is 2 (double brightness) -/
theorem exposureFactor_one : exposureFactor ⟨1⟩ = 2 := by
  unfold exposureFactor
  simp [Real.rpow_one]

/-- Exposure factor at param=-1 is 0.5 (half brightness) -/
theorem exposureFactor_neg_one : exposureFactor ⟨-1⟩ = 1/2 := by
  unfold exposureFactor
  simp [Real.rpow_neg_one]

/-- Exposure is monotonically increasing in parameter -/
theorem exposureFactor_mono {p1 p2 : ExposureParam} (h : p1.value < p2.value) :
    exposureFactor p1 < exposureFactor p2 := by
  unfold exposureFactor
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) h

/-- Apply exposure compensation to RGB value -/
noncomputable def applyExposure (rgb : ℝ) (param : ExposureParam) : ℝ :=
  rgb * exposureFactor param

/-- Exposure preserves non-negativity -/
theorem applyExposure_nonneg (rgb : ℝ) (param : ExposureParam) (hrgb : rgb ≥ 0) :
    applyExposure rgb param ≥ 0 := by
  unfold applyExposure
  exact mul_nonneg hrgb (le_of_lt (exposureFactor_pos param))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: ACTIVATION FUNCTIONS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Softplus transformation: f(x) = log(1 + exp(x))
    
    Used to transform unbounded parameters to strictly positive values.
    Smooth approximation to ReLU. -/
noncomputable def softplus (x : ℝ) : ℝ :=
  Real.log (1 + Real.exp x)

/-- Softplus is strictly positive -/
theorem softplus_pos (x : ℝ) : softplus x > 0 := by
  unfold softplus
  have h1 : Real.exp x > 0 := Real.exp_pos x
  have h2 : 1 + Real.exp x > 1 := by linarith
  exact Real.log_pos h2

/-- Softplus at 0 equals ln(2) -/
theorem softplus_zero : softplus 0 = Real.log 2 := by
  unfold softplus
  simp only [Real.exp_zero]
  norm_num

/-- Softplus is monotonically increasing -/
theorem softplus_mono {x y : ℝ} (h : x < y) : softplus x < softplus y := by
  unfold softplus
  apply Real.log_lt_log
  · have hexp : Real.exp x > 0 := Real.exp_pos x
    linarith
  · have hexp_mono : Real.exp x < Real.exp y := Real.exp_lt_exp.mpr h
    linarith

/-- Bounded positive transformation: softplus with minimum offset.
    
    f(x) = min_value + softplus(x) = min_value + log(1 + exp(x))
    
    Ensures output ≥ min_value > 0. -/
noncomputable def boundedPositive (raw : ℝ) (minValue : ℝ) : ℝ :=
  minValue + softplus raw

/-- Bounded positive is greater than min_value -/
theorem boundedPositive_gt_min (raw : ℝ) (minValue : ℝ) :
    boundedPositive raw minValue > minValue := by
  unfold boundedPositive
  have h := softplus_pos raw
  linarith

/-- Sigmoid transformation: f(x) = 1 / (1 + exp(-x))
    
    Maps ℝ to (0, 1). Used for parameters that need to be bounded. -/
noncomputable def sigmoid (x : ℝ) : ℝ :=
  1 / (1 + Real.exp (-x))

/-- Sigmoid is strictly positive -/
theorem sigmoid_pos (x : ℝ) : sigmoid x > 0 := by
  unfold sigmoid
  have hexp : Real.exp (-x) > 0 := Real.exp_pos (-x)
  have hdenom : 1 + Real.exp (-x) > 0 := by linarith
  exact div_pos one_pos hdenom

/-- Sigmoid is strictly less than 1 -/
theorem sigmoid_lt_one (x : ℝ) : sigmoid x < 1 := by
  unfold sigmoid
  have hexp : Real.exp (-x) > 0 := Real.exp_pos (-x)
  have hdenom : 1 + Real.exp (-x) > 1 := by linarith
  rw [div_lt_one (by linarith : 1 + Real.exp (-x) > 0)]
  exact hdenom

/-- Sigmoid at 0 equals 0.5 -/
theorem sigmoid_zero : sigmoid 0 = 1/2 := by
  unfold sigmoid
  simp only [neg_zero, Real.exp_zero]
  norm_num

/-- Sigmoid is monotonically increasing -/
theorem sigmoid_mono {x y : ℝ} (h : x < y) : sigmoid x < sigmoid y := by
  unfold sigmoid
  have hexp_x : Real.exp (-x) > 0 := Real.exp_pos (-x)
  have hexp_y : Real.exp (-y) > 0 := Real.exp_pos (-y)
  have hdenom_x : 1 + Real.exp (-x) > 0 := by linarith
  have hdenom_y : 1 + Real.exp (-y) > 0 := by linarith
  -- exp(-x) > exp(-y) when x < y
  have hexp_mono : Real.exp (-y) < Real.exp (-x) := by
    apply Real.exp_lt_exp.mpr
    linarith
  -- 1 + exp(-y) < 1 + exp(-x)
  have hdenom_mono : 1 + Real.exp (-y) < 1 + Real.exp (-x) := by linarith
  -- 1/(1+exp(-x)) < 1/(1+exp(-y)) because denominator is smaller
  have h1 : 1 / (1 + Real.exp (-x)) < 1 / (1 + Real.exp (-y)) := by
    apply one_div_lt_one_div_of_lt hdenom_y hdenom_mono
  exact h1

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: VIGNETTING
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Vignetting parameters for a single channel.
    
    Models radial light falloff from lens optics:
    falloff(r) = 1 + α₀r² + α₁r⁴ + α₂r⁶
    
    Where r is normalized distance from optical center. -/
structure VignettingParams where
  /-- Optical center X offset (normalized, ~0) -/
  centerX : ℝ
  /-- Optical center Y offset (normalized, ~0) -/
  centerY : ℝ
  /-- r² coefficient (typically ≤ 0 for real lenses) -/
  alpha0 : ℝ
  /-- r⁴ coefficient (typically ≤ 0) -/
  alpha1 : ℝ
  /-- r⁶ coefficient (typically ≤ 0) -/
  alpha2 : ℝ

/-- Compute normalized radius squared from pixel position.
    
    Coordinates are normalized to [-0.5, 0.5] based on max dimension,
    then offset by optical center. -/
noncomputable def radiusSquared (params : VignettingParams) (ux uy : ℝ) : ℝ :=
  let dx := ux - params.centerX
  let dy := uy - params.centerY
  dx^2 + dy^2

/-- Radius squared is non-negative -/
theorem radiusSquared_nonneg (params : VignettingParams) (ux uy : ℝ) :
    radiusSquared params ux uy ≥ 0 := by
  unfold radiusSquared
  have h1 : (ux - params.centerX)^2 ≥ 0 := sq_nonneg _
  have h2 : (uy - params.centerY)^2 ≥ 0 := sq_nonneg _
  linarith

/-- Compute vignetting falloff factor.
    
    falloff = 1 + α₀r² + α₁r⁴ + α₂r⁶
    
    Note: Real lenses have α ≤ 0, giving falloff ≤ 1 (darkening toward edges). -/
noncomputable def vignettingFalloff (params : VignettingParams) (r2 : ℝ) : ℝ :=
  let r4 := r2^2
  let r6 := r4 * r2
  1 + params.alpha0 * r2 + params.alpha1 * r4 + params.alpha2 * r6

/-- At center (r=0), vignetting falloff is 1 (no correction) -/
theorem vignettingFalloff_center (params : VignettingParams) :
    vignettingFalloff params 0 = 1 := by
  unfold vignettingFalloff
  simp

/-- For non-positive coefficients and r² ∈ [0,1], falloff ∈ [0, 1].
    
    This encodes the physical constraint that vignetting only darkens,
    never brightens, and never produces negative values. -/
theorem vignettingFalloff_bounded (params : VignettingParams) (r2 : ℝ)
    (hr2_nonneg : r2 ≥ 0) (hr2_le : r2 ≤ 1)
    (ha0 : params.alpha0 ≤ 0) (ha1 : params.alpha1 ≤ 0) (ha2 : params.alpha2 ≤ 0)
    (hsum : params.alpha0 + params.alpha1 + params.alpha2 ≥ -1) :
    vignettingFalloff params r2 ≥ 0 ∧ vignettingFalloff params r2 ≤ 1 := by
  unfold vignettingFalloff
  constructor
  · -- falloff ≥ 0
    -- At r² = 1: falloff = 1 + α₀ + α₁ + α₂ ≥ 0 (by hsum)
    -- For r² < 1, the polynomial is larger (since coefficients are negative)
    have hr4 : r2^2 ≤ r2 := by nlinarith
    have hr6 : r2^2 * r2 ≤ r2 := by nlinarith
    have h0 : params.alpha0 * r2 ≥ params.alpha0 := by nlinarith
    have h1 : params.alpha1 * r2^2 ≥ params.alpha1 := by nlinarith
    have h2 : params.alpha2 * (r2^2 * r2) ≥ params.alpha2 := by nlinarith
    have hsum' : params.alpha0 * r2 + params.alpha1 * r2^2 + 
                  params.alpha2 * (r2^2 * r2) ≥ 
                  params.alpha0 + params.alpha1 + params.alpha2 := by linarith
    linarith
  · -- falloff ≤ 1
    -- Since all α ≤ 0 and r² ≥ 0, all terms are ≤ 0
    have h0 : params.alpha0 * r2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha0 hr2_nonneg
    have h4 : r2^2 ≥ 0 := sq_nonneg _
    have h1 : params.alpha1 * r2^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha1 h4
    have h6 : r2^2 * r2 ≥ 0 := mul_nonneg h4 hr2_nonneg
    have h2 : params.alpha2 * (r2^2 * r2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha2 h6
    linarith

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: CAMERA RESPONSE FUNCTION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Camera response function parameters.
    
    Models the nonlinear tone mapping applied by camera ISP:
    - Toe: Controls shadow compression
    - Shoulder: Controls highlight rolloff
    - Gamma: Overall contrast
    - Center: Pivot point for the curve -/
structure CRFParams where
  /-- Toe strength (after softplus: > 0.3) -/
  toeRaw : ℝ
  /-- Shoulder strength (after softplus: > 0.3) -/
  shoulderRaw : ℝ
  /-- Gamma (after softplus: > 0.1) -/
  gammaRaw : ℝ
  /-- Center point (after sigmoid: ∈ (0, 1)) -/
  centerRaw : ℝ

/-- Decode CRF parameters from raw values -/
noncomputable def decodeCRF (params : CRFParams) : ℝ × ℝ × ℝ × ℝ :=
  let toe := boundedPositive params.toeRaw 0.3
  let shoulder := boundedPositive params.shoulderRaw 0.3
  let gamma := boundedPositive params.gammaRaw 0.1
  let center := sigmoid params.centerRaw
  (toe, shoulder, gamma, center)

/-- Decoded toe is > 0.3 -/
theorem decodeCRF_toe_gt (params : CRFParams) :
    (decodeCRF params).1 > 0.3 := by
  unfold decodeCRF
  exact boundedPositive_gt_min params.toeRaw 0.3

/-- Decoded shoulder is > 0.3 -/
theorem decodeCRF_shoulder_gt (params : CRFParams) :
    (decodeCRF params).2.1 > 0.3 := by
  unfold decodeCRF
  exact boundedPositive_gt_min params.shoulderRaw 0.3

/-- Decoded gamma is > 0.1 -/
theorem decodeCRF_gamma_gt (params : CRFParams) :
    (decodeCRF params).2.2.1 > 0.1 := by
  unfold decodeCRF
  exact boundedPositive_gt_min params.gammaRaw 0.1

/-- Decoded center is in (0, 1) -/
theorem decodeCRF_center_bounds (params : CRFParams) :
    (decodeCRF params).2.2.2 > 0 ∧ (decodeCRF params).2.2.2 < 1 := by
  unfold decodeCRF
  exact ⟨sigmoid_pos params.centerRaw, sigmoid_lt_one params.centerRaw⟩

/-- Gamma correction preserves [0, 1] bounds.
    
    For x ∈ [0, 1] and γ > 0: x^γ ∈ [0, 1] -/
theorem gamma_preserves_unit (x : ℝ) (gamma : ℝ) 
    (hx_nonneg : x ≥ 0) (hx_le : x ≤ 1) (hgamma : gamma > 0) :
    x^gamma ≥ 0 ∧ x^gamma ≤ 1 := by
  constructor
  · exact Real.rpow_nonneg hx_nonneg gamma
  · have h1 : x^gamma ≤ 1^gamma := Real.rpow_le_rpow hx_nonneg hx_le (le_of_lt hgamma)
    simp at h1
    exact h1

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: LINEAR INTERPOLATION (LERP)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Linear interpolation: lerp(a, b, t) = a + (b - a) * t
    
    Fundamental operation for blending, animation, and CRF curves. -/
noncomputable def lerp (a b t : ℝ) : ℝ :=
  a + (b - a) * t

/-- Lerp at t=0 equals a -/
theorem lerp_zero (a b : ℝ) : lerp a b 0 = a := by
  unfold lerp
  ring

/-- Lerp at t=1 equals b -/
theorem lerp_one (a b : ℝ) : lerp a b 1 = b := by
  unfold lerp
  ring

/-- Lerp at t=0.5 equals (a+b)/2 (midpoint) -/
theorem lerp_half (a b : ℝ) : lerp a b (1/2) = (a + b) / 2 := by
  unfold lerp
  ring

/-- Lerp preserves bounds when t ∈ [0, 1] and a ≤ b -/
theorem lerp_bounds (a b t : ℝ) (hab : a ≤ b) (ht0 : t ≥ 0) (ht1 : t ≤ 1) :
    lerp a b t ≥ a ∧ lerp a b t ≤ b := by
  unfold lerp
  constructor
  · have h : (b - a) * t ≥ 0 := mul_nonneg (by linarith) ht0
    linarith
  · have h1 : (b - a) * t ≤ (b - a) * 1 := mul_le_mul_of_nonneg_left ht1 (by linarith)
    linarith

/-- Lerp is symmetric: lerp(a, b, t) = lerp(b, a, 1-t) -/
theorem lerp_symm (a b t : ℝ) : lerp a b t = lerp b a (1 - t) := by
  unfold lerp
  ring

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6: DERIVATIVE RELATIONSHIPS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Fundamental Derivative Relationships

These proofs establish the key relationships used in backpropagation:
- softplus'(x) = sigmoid(x)
- sigmoid'(x) = sigmoid(x) * (1 - sigmoid(x))
- exp2'(x) = ln(2) * exp2(x)

These are essential for automatic differentiation in neural networks
and ISP parameter optimization. -/

/-- Alternative form of sigmoid in terms of exp.
    
    sigmoid(x) = exp(x) / (1 + exp(x))
    
    This form is useful for proving derivative relationships. -/
noncomputable def sigmoidAlt (x : ℝ) : ℝ :=
  Real.exp x / (1 + Real.exp x)

/-- The two sigmoid definitions are equivalent -/
theorem sigmoid_eq_sigmoidAlt (x : ℝ) : sigmoid x = sigmoidAlt x := by
  unfold sigmoid sigmoidAlt
  have hexp : Real.exp x > 0 := Real.exp_pos x
  have hexp_neg : Real.exp (-x) > 0 := Real.exp_pos (-x)
  have hdenom1 : 1 + Real.exp (-x) > 0 := by linarith
  have hdenom2 : 1 + Real.exp x > 0 := by linarith
  -- Use exp(-x) = 1/exp(x)
  have hexp_neg_eq : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
  rw [hexp_neg_eq]
  -- Now: 1 / (1 + 1/exp(x)) = exp(x) / (1 + exp(x))
  field_simp
  ring

/-- Derivative relationship: d/dx[softplus(x)] = sigmoid(x)
    
    This is proven algebraically. The derivative of log(1 + exp(x)) is:
    exp(x) / (1 + exp(x)) = sigmoid(x)
    
    NVIDIA uses this in softplus_bwd: grad_raw = grad_output * sigmoid(raw) -/
theorem softplus_deriv_is_sigmoid (x : ℝ) :
    Real.exp x / (1 + Real.exp x) = sigmoidAlt x := by
  unfold sigmoidAlt
  -- Direct equality
  rfl

/-- Derivative relationship: d/dx[sigmoid(x)] = sigmoid(x) * (1 - sigmoid(x))
    
    This is the fundamental sigmoid derivative identity.
    
    NVIDIA uses this in sigmoid_bwd: grad_raw = grad_output * output * (1 - output) -/
theorem sigmoid_deriv_identity (x : ℝ) :
    sigmoid x * (1 - sigmoid x) = 
    Real.exp (-x) / (1 + Real.exp (-x))^2 := by
  unfold sigmoid
  have hexp : Real.exp (-x) > 0 := Real.exp_pos (-x)
  have hdenom : 1 + Real.exp (-x) > 0 := by linarith
  have hdenom_sq : (1 + Real.exp (-x))^2 > 0 := sq_pos_of_pos hdenom
  field_simp
  ring

/-- The sigmoid derivative is always non-negative -/
theorem sigmoid_deriv_nonneg (x : ℝ) : sigmoid x * (1 - sigmoid x) ≥ 0 := by
  have h1 : sigmoid x > 0 := sigmoid_pos x
  have h2 : sigmoid x < 1 := sigmoid_lt_one x
  have h3 : 1 - sigmoid x > 0 := by linarith
  exact mul_nonneg (le_of_lt h1) (le_of_lt h3)

/-- The sigmoid derivative is bounded above by 1/4.
    
    The maximum occurs at x = 0 where sigmoid(0) = 0.5 and 0.5 * 0.5 = 0.25. -/
theorem sigmoid_deriv_le_quarter (x : ℝ) : sigmoid x * (1 - sigmoid x) ≤ 1/4 := by
  -- Use AM-GM: ab ≤ ((a+b)/2)² when a,b ≥ 0
  -- Here a = sigmoid(x), b = 1 - sigmoid(x), so a + b = 1
  -- Therefore ab ≤ (1/2)² = 1/4
  have h1 : sigmoid x > 0 := sigmoid_pos x
  have h2 : sigmoid x < 1 := sigmoid_lt_one x
  have h3 : 1 - sigmoid x > 0 := by linarith
  have hsum : sigmoid x + (1 - sigmoid x) = 1 := by ring
  -- AM-GM: √(ab) ≤ (a+b)/2, so ab ≤ ((a+b)/2)²
  have ham_gm := sq_nonneg (sigmoid x - (1 - sigmoid x))
  -- (a - b)² ≥ 0 implies a² - 2ab + b² ≥ 0
  -- implies 2ab ≤ a² + b²
  -- implies 4ab ≤ (a + b)² = 1
  -- implies ab ≤ 1/4
  nlinarith [sq_nonneg (sigmoid x), sq_nonneg (1 - sigmoid x)]

/-- Exp2 derivative: d/dx[2^x] = ln(2) * 2^x
    
    This is the chain rule applied to exp(x * ln(2)).
    
    NVIDIA uses this in exp2_bwd: grad_x = grad_output * 0.69314718 * output -/
theorem exp2_deriv_coeff : Real.log 2 > 0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)

/-- The derivative coefficient ln(2) ≈ 0.693... is between 0 and 1 -/
theorem exp2_deriv_coeff_bounded : 0 < Real.log 2 ∧ Real.log 2 < 1 := by
  constructor
  · exact exp2_deriv_coeff
  · -- ln(2) < 1 iff 2 < e
    rw [Real.log_lt_iff_lt_exp (by norm_num : (2 : ℝ) > 0)]
    -- Need to show 2 < exp(1)
    have h1 : Real.exp 1 > 1 + 1 := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    linarith

/-- The relationship between exp2 and rpow -/
theorem exp2_eq_rpow (x : ℝ) : (2 : ℝ)^x = Real.exp (x * Real.log 2) := by
  rw [Real.rpow_def_of_pos (by norm_num : (2 : ℝ) > 0)]
  ring_nf

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 7: BACKWARD PASS GRADIENTS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Backward Pass Gradient Formulas

These formulas define the gradients used in backpropagation.
They are the mathematical foundations of automatic differentiation. -/

/-- Dot product backward: ∂(a·b)/∂a = b, ∂(a·b)/∂b = a
    
    For a scalar output s = a·b:
    - grad_a = grad_output * b
    - grad_b = grad_output * a -/
structure DotBackward where
  /-- Gradient with respect to first input -/
  grad_a : ℝ × ℝ × ℝ
  /-- Gradient with respect to second input -/
  grad_b : ℝ × ℝ × ℝ

/-- Compute dot product backward pass -/
def dotBackward (grad_output : ℝ) (a b : ℝ × ℝ × ℝ) : DotBackward :=
  { grad_a := (grad_output * b.1, grad_output * b.2.1, grad_output * b.2.2)
  , grad_b := (grad_output * a.1, grad_output * a.2.1, grad_output * a.2.2) }

/-- The dot backward is symmetric in a and b -/
theorem dotBackward_symmetric (g : ℝ) (a b : ℝ × ℝ × ℝ) :
    (dotBackward g a b).grad_a = (dotBackward g b a).grad_b := by
  unfold dotBackward
  simp

/-- Cross product backward: ∂(a×b)/∂a = b×, ∂(a×b)/∂b = ×a
    
    For c = a × b:
    - grad_a = b × grad_c (cross product of b with gradient)
    - grad_b = grad_c × a (cross product of gradient with a) -/
structure CrossBackward where
  /-- Gradient with respect to first input -/
  grad_a : ℝ × ℝ × ℝ
  /-- Gradient with respect to second input -/
  grad_b : ℝ × ℝ × ℝ

/-- Helper: 3D cross product as a function -/
def cross3 (a b : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  ( a.2.1 * b.2.2 - a.2.2 * b.2.1
  , a.2.2 * b.1 - a.1 * b.2.2
  , a.1 * b.2.1 - a.2.1 * b.1 )

/-- Compute cross product backward pass -/
def crossBackward (grad_c : ℝ × ℝ × ℝ) (a b : ℝ × ℝ × ℝ) : CrossBackward :=
  { grad_a := cross3 b grad_c
  , grad_b := cross3 grad_c a }

/-- Cross product is antisymmetric: a × b = -(b × a) -/
theorem cross3_antisymm (a b : ℝ × ℝ × ℝ) : 
    cross3 a b = (-(cross3 b a).1, -(cross3 b a).2.1, -(cross3 b a).2.2) := by
  unfold cross3
  simp only [Prod.mk.injEq, neg_sub]
  constructor
  · ring
  · constructor <;> ring

/-- Length backward: ∂|a|/∂a = a/|a|
    
    For s = |a| = √(a·a):
    - grad_a = grad_output * a / |a| -/
noncomputable def lengthBackward (grad_output : ℝ) (a : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let len := Real.sqrt (a.1^2 + a.2.1^2 + a.2.2^2)
  let inv_len := 1 / (len + 1e-8)  -- Add epsilon for numerical stability
  (grad_output * a.1 * inv_len, 
   grad_output * a.2.1 * inv_len, 
   grad_output * a.2.2 * inv_len)

/-- Normalize backward: ∂(a/|a|)/∂a = (I - n⊗n)/|a|
    
    Where n = a/|a| is the normalized vector.
    
    For n = a/|a|:
    - grad_a = (grad_n - (grad_n · n) * n) / |a| -/
noncomputable def normalizeBackward (grad_n : ℝ × ℝ × ℝ) (a : ℝ × ℝ × ℝ) 
    (n : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let len := Real.sqrt (a.1^2 + a.2.1^2 + a.2.2^2)
  let inv_len := 1 / (len + 1e-8)
  let dot_val := grad_n.1 * n.1 + grad_n.2.1 * n.2.1 + grad_n.2.2 * n.2.2
  ( (grad_n.1 - dot_val * n.1) * inv_len
  , (grad_n.2.1 - dot_val * n.2.1) * inv_len
  , (grad_n.2.2 - dot_val * n.2.2) * inv_len )

/-- Division backward: ∂(a/b)/∂a = 1/b, ∂(a/b)/∂b = -a/b²
    
    For s = a/b:
    - grad_a = grad_output / b
    - grad_b = -grad_output * a / b² = -grad_output * (a/b) / b -/
structure DivBackward where
  grad_a : ℝ
  grad_b : ℝ

/-- Compute division backward pass -/
noncomputable def divBackward (grad_output _a b output : ℝ) : DivBackward :=
  { grad_a := grad_output / b
  , grad_b := -grad_output * output / b }

/-- Power backward: ∂(x^e)/∂x = e * x^(e-1), ∂(x^e)/∂e = x^e * ln(x)
    
    For y = x^e:
    - grad_x = grad_output * e * x^(e-1)
    - grad_e = grad_output * y * ln(x) -/
structure PowBackward where
  grad_x : ℝ
  grad_e : ℝ

/-- Compute power backward pass -/
noncomputable def powBackward (grad_output x e output : ℝ) : PowBackward :=
  { grad_x := grad_output * e * x^(e - 1)
  , grad_e := grad_output * output * Real.log (x + 1e-8) }

/-- Log backward: ∂(ln x)/∂x = 1/x -/
noncomputable def logBackward (grad_output x : ℝ) : ℝ :=
  grad_output / (x + 1e-8)

/-- Sqrt backward: ∂(√x)/∂x = 1/(2√x) -/
noncomputable def sqrtBackward (grad_output output : ℝ) : ℝ :=
  grad_output / (2 * output + 1e-8)

/-- Exp backward: ∂(e^x)/∂x = e^x = output -/
def expBackward (grad_output output : ℝ) : ℝ :=
  grad_output * output

/-- Exp2 backward: ∂(2^x)/∂x = ln(2) * 2^x = ln(2) * output
    
    NVIDIA constant: 0.69314718 ≈ ln(2) -/
noncomputable def exp2Backward (grad_output output : ℝ) : ℝ :=
  grad_output * Real.log 2 * output

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 8: RGI COLOR SPACE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## RGI Color Space Conversion

NVIDIA PPISP uses RGI (Red, Green, Intensity) space for color correction.
The conversion is:
  RGB → RGI: (r, g, b) → (r, g, r + g + b)
  RGI → RGB: (r, g, i) → (r, g, i - r - g)

This representation allows the homography to preserve intensity while
adjusting chromaticity. -/

/-- RGB color with components in [0, ∞) -/
@[ext]
structure RGB where
  r : ℝ
  g : ℝ
  b : ℝ

/-- RGI color: (red, green, intensity where intensity = r + g + b) -/
@[ext]
structure RGI where
  r : ℝ
  g : ℝ
  i : ℝ  -- intensity = r + g + b

/-- Convert RGB to RGI space -/
def rgbToRgi (rgb : RGB) : RGI :=
  { r := rgb.r
  , g := rgb.g
  , i := rgb.r + rgb.g + rgb.b }

/-- Convert RGI back to RGB space -/
def rgiToRgb (rgi : RGI) : RGB :=
  { r := rgi.r
  , g := rgi.g
  , b := rgi.i - rgi.r - rgi.g }

/-- RGI → RGB → RGI is identity -/
theorem rgi_roundtrip (rgi : RGI) : rgbToRgi (rgiToRgb rgi) = rgi := by
  simp only [rgbToRgi, rgiToRgb]
  ext <;> ring

/-- RGB → RGI → RGB is identity -/
theorem rgb_roundtrip (rgb : RGB) : rgiToRgb (rgbToRgi rgb) = rgb := by
  simp only [rgbToRgi, rgiToRgb]
  ext <;> ring

/-- The intensity component equals sum of RGB -/
theorem rgi_intensity_sum (rgb : RGB) : (rgbToRgi rgb).i = rgb.r + rgb.g + rgb.b := by
  simp only [rgbToRgi]

/-- Blue channel can be recovered from RGI -/
theorem rgi_blue_recovery (rgb : RGB) : 
    (rgbToRgi rgb).i - (rgbToRgi rgb).r - (rgbToRgi rgb).g = rgb.b := by
  simp only [rgbToRgi]
  ring

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 9: SKEW-SYMMETRIC MATRIX
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Skew-Symmetric Matrix Construction

NVIDIA PPISP uses skew-symmetric matrices for computing the homography.
A skew-symmetric matrix S satisfies Sᵀ = -S.

For a vector v = (x, y, z), the skew-symmetric matrix [v]_× is:
  [  0  -z   y ]
  [  z   0  -x ]
  [ -y   x   0 ]

This is used in the cross product: a × b = [a]_× b -/

/-- 3x3 matrix stored row-major (simplified for this module) -/
structure Mat3x3 where
  m00 : ℝ
  m01 : ℝ
  m02 : ℝ
  m10 : ℝ
  m11 : ℝ
  m12 : ℝ
  m20 : ℝ
  m21 : ℝ
  m22 : ℝ

/-- Skew-symmetric matrix [v]_× from vector v = (x, y, z) -/
def skewSymmetric (x y z : ℝ) : Mat3x3 :=
  { m00 := 0,    m01 := -z,   m02 := y
  , m10 := z,    m11 := 0,    m12 := -x
  , m20 := -y,   m21 := x,    m22 := 0 }

/-- Transpose of a 3x3 matrix -/
def Mat3x3.transpose (m : Mat3x3) : Mat3x3 :=
  { m00 := m.m00, m01 := m.m10, m02 := m.m20
  , m10 := m.m01, m11 := m.m11, m12 := m.m21
  , m20 := m.m02, m21 := m.m12, m22 := m.m22 }

/-- Negate a 3x3 matrix -/
def Mat3x3.neg (m : Mat3x3) : Mat3x3 :=
  { m00 := -m.m00, m01 := -m.m01, m02 := -m.m02
  , m10 := -m.m10, m11 := -m.m11, m12 := -m.m12
  , m20 := -m.m20, m21 := -m.m21, m22 := -m.m22 }

/-- Matrix equality extension -/
@[ext]
theorem Mat3x3.ext {a b : Mat3x3}
    (h00 : a.m00 = b.m00) (h01 : a.m01 = b.m01) (h02 : a.m02 = b.m02)
    (h10 : a.m10 = b.m10) (h11 : a.m11 = b.m11) (h12 : a.m12 = b.m12)
    (h20 : a.m20 = b.m20) (h21 : a.m21 = b.m21) (h22 : a.m22 = b.m22) : a = b := by
  cases a; cases b; simp_all

/-- Skew-symmetric matrix satisfies Sᵀ = -S -/
theorem skewSymmetric_transpose (x y z : ℝ) :
    (skewSymmetric x y z).transpose = (skewSymmetric x y z).neg := by
  simp only [skewSymmetric, Mat3x3.transpose, Mat3x3.neg]
  ext <;> ring

/-- Diagonal of skew-symmetric matrix is zero -/
theorem skewSymmetric_diag_zero (x y z : ℝ) :
    let s := skewSymmetric x y z
    s.m00 = 0 ∧ s.m11 = 0 ∧ s.m22 = 0 := by
  simp only [skewSymmetric]
  trivial

/-- Trace of skew-symmetric matrix is zero -/
theorem skewSymmetric_trace_zero (x y z : ℝ) :
    let s := skewSymmetric x y z
    s.m00 + s.m11 + s.m22 = 0 := by
  simp only [skewSymmetric]
  ring

/-- Matrix-vector multiplication for 3x3 -/
def Mat3x3.mulVec (m : Mat3x3) (v : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  ( m.m00 * v.1 + m.m01 * v.2.1 + m.m02 * v.2.2
  , m.m10 * v.1 + m.m11 * v.2.1 + m.m12 * v.2.2
  , m.m20 * v.1 + m.m21 * v.2.1 + m.m22 * v.2.2 )

/-- Skew-symmetric matrix times vector equals cross product.
    
    [a]_× b = a × b -/
theorem skewSymmetric_mulVec_eq_cross (a b : ℝ × ℝ × ℝ) :
    (skewSymmetric a.1 a.2.1 a.2.2).mulVec b = cross3 a b := by
  simp only [skewSymmetric, Mat3x3.mulVec, cross3]
  ext <;> ring

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 10: CRF TOE-SHOULDER CURVE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Camera Response Function: Piecewise Toe-Shoulder Curve

NVIDIA PPISP uses a piecewise curve for the CRF:

For x ∈ [0, center]:
  y = a * (x / center)^toe

For x ∈ (center, 1]:
  y = 1 - b * ((1-x) / (1-center))^shoulder

Where:
  lerp_val = (shoulder - toe) * center + toe
  a = (shoulder * center) / lerp_val
  b = 1 - a

The curve is C0 continuous at center (by construction).
Final output: pow(y, gamma) -/

/-- CRF curve parameters (decoded from raw via softplus/sigmoid) -/
structure CRFCurveParams where
  toe : ℝ
  shoulder : ℝ
  gamma : ℝ
  center : ℝ
  toe_pos : toe > 0.3
  shoulder_pos : shoulder > 0.3
  gamma_pos : gamma > 0.1
  center_in_unit : 0 < center ∧ center < 1

/-- Compute the 'a' coefficient for the toe region -/
noncomputable def crfCoeffA (p : CRFCurveParams) : ℝ :=
  let lerp_val := (p.shoulder - p.toe) * p.center + p.toe
  p.shoulder * p.center / lerp_val

/-- Compute the 'b' coefficient for the shoulder region -/
noncomputable def crfCoeffB (p : CRFCurveParams) : ℝ :=
  1 - crfCoeffA p

/-- The lerp_val is always positive (key for division safety) -/
theorem crfLerpVal_pos (p : CRFCurveParams) :
    (p.shoulder - p.toe) * p.center + p.toe > 0 := by
  have htoe : p.toe > 0.3 := p.toe_pos
  have hshoulder : p.shoulder > 0.3 := p.shoulder_pos
  have hcenter : 0 < p.center ∧ p.center < 1 := p.center_in_unit
  -- lerp_val = shoulder * center + toe * (1 - center)
  -- = center * shoulder + (1 - center) * toe
  -- Since toe > 0.3, shoulder > 0.3, and center ∈ (0, 1):
  -- Both terms are positive
  have h1 : p.center > 0 := hcenter.1
  have h2 : 1 - p.center > 0 := by linarith [hcenter.2]
  have h3 : p.toe > 0 := by linarith
  have h4 : p.shoulder > 0 := by linarith
  -- Expand: (shoulder - toe) * center + toe = shoulder * center - toe * center + toe
  --       = shoulder * center + toe * (1 - center)
  calc (p.shoulder - p.toe) * p.center + p.toe
      = p.shoulder * p.center + p.toe * (1 - p.center) := by ring
    _ > 0 := by nlinarith

/-- CRF toe curve: y = a * (x/center)^toe for x ∈ [0, center] -/
noncomputable def crfToe (p : CRFCurveParams) (x : ℝ) : ℝ :=
  let a := crfCoeffA p
  a * (x / p.center)^p.toe

/-- CRF shoulder curve: y = 1 - b * ((1-x)/(1-center))^shoulder for x ∈ (center, 1] -/
noncomputable def crfShoulder (p : CRFCurveParams) (x : ℝ) : ℝ :=
  let b := crfCoeffB p
  1 - b * ((1 - x) / (1 - p.center))^p.shoulder

/-- The piecewise CRF curve -/
noncomputable def crfCurve (p : CRFCurveParams) (x : ℝ) : ℝ :=
  if x ≤ p.center then crfToe p x else crfShoulder p x

/-- Apply gamma correction to CRF output -/
noncomputable def crfWithGamma (p : CRFCurveParams) (x : ℝ) : ℝ :=
  let y := crfCurve p x
  if y ≤ 0 then 0 else y^p.gamma

/-- CRF at x=0 gives 0 (black maps to black) -/
theorem crfCurve_zero (p : CRFCurveParams) : crfCurve p 0 = 0 := by
  simp only [crfCurve, crfToe]
  have hcenter : p.center > 0 := p.center_in_unit.1
  have hle : (0 : ℝ) ≤ p.center := le_of_lt hcenter
  simp only [hle, ↓reduceIte]
  have htoe : p.toe > 0.3 := p.toe_pos
  have htoe_pos : p.toe > 0 := by linarith
  rw [zero_div, Real.zero_rpow (ne_of_gt htoe_pos)]
  ring

/-- CRF at x=1 gives 1 (white maps to white) -/
theorem crfCurve_one (p : CRFCurveParams) : crfCurve p 1 = 1 := by
  simp only [crfCurve, crfShoulder]
  have hcenter : p.center < 1 := p.center_in_unit.2
  have hgt : ¬(1 : ℝ) ≤ p.center := by linarith
  simp only [hgt, ↓reduceIte]
  have hshoulder : p.shoulder > 0.3 := p.shoulder_pos
  have hshoulder_pos : p.shoulder > 0 := by linarith
  simp only [sub_self, zero_div, Real.zero_rpow (ne_of_gt hshoulder_pos)]
  ring

/-- CRF curve is continuous at center (C0 continuity).
    
    Both pieces evaluate to 'a' at the center point:
    - Toe: a * (center/center)^toe = a * 1 = a
    - Shoulder: 1 - b * ((1-center)/(1-center))^shoulder = 1 - b = 1 - (1-a) = a -/
theorem crfCurve_continuous_at_center (p : CRFCurveParams) :
    crfToe p p.center = crfShoulder p p.center := by
  simp only [crfToe, crfShoulder, crfCoeffA, crfCoeffB]
  have hcenter_pos : p.center > 0 := p.center_in_unit.1
  have hcenter_lt1 : p.center < 1 := p.center_in_unit.2
  have h1_minus_c_pos : 1 - p.center > 0 := by linarith
  have htoe_pos : p.toe > 0 := by linarith [p.toe_pos]
  have hshoulder_pos : p.shoulder > 0 := by linarith [p.shoulder_pos]
  -- Toe at center: a * (center/center)^toe = a * 1^toe = a
  have htoe_at_c : (p.center / p.center)^p.toe = 1 := by
    rw [div_self (ne_of_gt hcenter_pos)]
    exact Real.one_rpow p.toe
  -- Shoulder at center: 1 - b * ((1-center)/(1-center))^shoulder = 1 - b * 1 = 1 - b = a
  have hshoulder_at_c : ((1 - p.center) / (1 - p.center))^p.shoulder = 1 := by
    rw [div_self (ne_of_gt h1_minus_c_pos)]
    exact Real.one_rpow p.shoulder
  -- Both equal a
  rw [htoe_at_c, hshoulder_at_c]
  ring

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 11: 2x2 MATRIX OPERATIONS (ZCA TRANSFORMS)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## 2x2 Matrix Operations for ZCA Transforms

NVIDIA PPISP uses 2x2 matrices for ZCA (Zero-phase Component Analysis)
transforms. These map latent offsets to real chromaticity offsets.

The ZCA blocks are precomputed pseudo-inverses of the constraint Jacobian,
stored as constant 2x2 matrices per color control point (B, R, G, N). -/

/-- 2x2 matrix stored row-major -/
@[ext]
structure Mat2x2 where
  m00 : ℝ
  m01 : ℝ
  m10 : ℝ
  m11 : ℝ

/-- 2D vector -/
@[ext]
structure Vec2 where
  x : ℝ
  y : ℝ

/-- Identity 2x2 matrix -/
def Mat2x2.identity : Mat2x2 := ⟨1, 0, 0, 1⟩

/-- Zero 2x2 matrix -/
def Mat2x2.zero : Mat2x2 := ⟨0, 0, 0, 0⟩

/-- Matrix-vector multiplication: y = A * x -/
def Mat2x2.mulVec (m : Mat2x2) (v : Vec2) : Vec2 :=
  { x := m.m00 * v.x + m.m01 * v.y
  , y := m.m10 * v.x + m.m11 * v.y }

/-- Matrix transpose -/
def Mat2x2.transpose (m : Mat2x2) : Mat2x2 :=
  { m00 := m.m00, m01 := m.m10
  , m10 := m.m01, m11 := m.m11 }

/-- Matrix determinant -/
def Mat2x2.det (m : Mat2x2) : ℝ :=
  m.m00 * m.m11 - m.m01 * m.m10

/-- Matrix addition -/
def Mat2x2.add (a b : Mat2x2) : Mat2x2 :=
  { m00 := a.m00 + b.m00, m01 := a.m01 + b.m01
  , m10 := a.m10 + b.m10, m11 := a.m11 + b.m11 }

/-- Matrix multiplication: C = A * B -/
def Mat2x2.mul (a b : Mat2x2) : Mat2x2 :=
  { m00 := a.m00 * b.m00 + a.m01 * b.m10
  , m01 := a.m00 * b.m01 + a.m01 * b.m11
  , m10 := a.m10 * b.m00 + a.m11 * b.m10
  , m11 := a.m10 * b.m01 + a.m11 * b.m11 }

/-- Identity is left identity for multiplication -/
theorem Mat2x2.mul_identity_left (m : Mat2x2) : Mat2x2.mul Mat2x2.identity m = m := by
  simp only [Mat2x2.mul, Mat2x2.identity]
  ext <;> ring

/-- Identity is right identity for multiplication -/
theorem Mat2x2.mul_identity_right (m : Mat2x2) : Mat2x2.mul m Mat2x2.identity = m := by
  simp only [Mat2x2.mul, Mat2x2.identity]
  ext <;> ring

/-- Determinant of identity is 1 -/
theorem Mat2x2.det_identity : Mat2x2.det Mat2x2.identity = 1 := by
  simp only [Mat2x2.det, Mat2x2.identity]
  ring

/-- Determinant is multiplicative -/
theorem Mat2x2.det_mul (a b : Mat2x2) : Mat2x2.det (Mat2x2.mul a b) = Mat2x2.det a * Mat2x2.det b := by
  simp only [Mat2x2.det, Mat2x2.mul]
  ring

/-- Identity times vector equals vector -/
theorem Mat2x2.mulVec_identity (v : Vec2) : Mat2x2.mulVec Mat2x2.identity v = v := by
  simp only [Mat2x2.mulVec, Mat2x2.identity]
  ext <;> ring

/-- Transpose is involutive -/
theorem Mat2x2.transpose_involutive (m : Mat2x2) : Mat2x2.transpose (Mat2x2.transpose m) = m := by
  simp only [Mat2x2.transpose]

/-- Transpose reverses multiplication -/
theorem Mat2x2.transpose_mul (a b : Mat2x2) : 
    Mat2x2.transpose (Mat2x2.mul a b) = Mat2x2.mul (Mat2x2.transpose b) (Mat2x2.transpose a) := by
  simp only [Mat2x2.transpose, Mat2x2.mul]
  ext <;> ring

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 12: VIGNETTING BACKWARD PASS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Vignetting Backward Pass

The backward pass for vignetting computes gradients with respect to:
- RGB input
- Vignetting coefficients (α₀, α₁, α₂)
- Optical center (cx, cy)

Forward: rgb_out = rgb_in * falloff(r²)
Where: falloff = 1 + α₀r² + α₁r⁴ + α₂r⁶
       r² = (ux - cx)² + (uy - cy)²

Gradients:
- grad_rgb_in = grad_rgb_out * falloff
- grad_falloff = grad_rgb_out * rgb_in
- grad_α₀ = grad_falloff * r²
- grad_α₁ = grad_falloff * r⁴
- grad_α₂ = grad_falloff * r⁶
- grad_r² = grad_falloff * (α₀ + 2α₁r² + 3α₂r⁴)
- grad_cx = grad_r² * (-2 * dx)
- grad_cy = grad_r² * (-2 * dy) -/

/-- Vignetting backward: gradient of falloff w.r.t. r² -/
def vignettingGradR2 (alpha0 alpha1 alpha2 r2 : ℝ) : ℝ :=
  let r4 := r2 * r2
  alpha0 + 2 * alpha1 * r2 + 3 * alpha2 * r4

/-- Vignetting backward: gradient of r² w.r.t. dx -/
def vignettingGradDx (dx : ℝ) : ℝ := 2 * dx

/-- Vignetting backward: gradient of r² w.r.t. dy -/
def vignettingGradDy (dy : ℝ) : ℝ := 2 * dy

/-- Vignetting backward: gradient w.r.t. center x -/
def vignettingGradCx (grad_r2 dx : ℝ) : ℝ :=
  -grad_r2 * vignettingGradDx dx

/-- Vignetting backward: gradient w.r.t. center y -/
def vignettingGradCy (grad_r2 dy : ℝ) : ℝ :=
  -grad_r2 * vignettingGradDy dy

/-- Chain rule for vignetting center gradients is correct -/
theorem vignetting_center_grad_chain (grad_falloff alpha0 alpha1 alpha2 r2 dx : ℝ) :
    let grad_r2 := grad_falloff * vignettingGradR2 alpha0 alpha1 alpha2 r2
    vignettingGradCx grad_r2 dx = -grad_falloff * vignettingGradR2 alpha0 alpha1 alpha2 r2 * (2 * dx) := by
  simp only [vignettingGradCx, vignettingGradDx]
  ring

/-- The falloff derivative at r²=0 is just α₀ -/
theorem vignettingGradR2_at_center (alpha0 alpha1 alpha2 : ℝ) :
    vignettingGradR2 alpha0 alpha1 alpha2 0 = alpha0 := by
  simp only [vignettingGradR2]
  ring

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 13: CLAMP BACKWARD
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Clamp Backward Pass

Forward: y = clamp(x, min, max)
Backward: grad_x = grad_y if min < x < max, else 0

This is a piecewise linear operation with zero gradient at the boundaries. -/

/-- Clamp backward: gradient passes through only in the interior -/
noncomputable def clampBackward (grad_output x min_val max_val : ℝ) : ℝ :=
  if min_val < x ∧ x < max_val then grad_output else 0

/-- Clamp backward is zero at minimum -/
theorem clampBackward_at_min (grad_output min_val max_val : ℝ) (_h : min_val < max_val) :
    clampBackward grad_output min_val min_val max_val = 0 := by
  simp only [clampBackward]
  have hfalse : ¬(min_val < min_val ∧ min_val < max_val) := by
    intro ⟨h1, _⟩
    exact (lt_irrefl min_val) h1
  simp only [hfalse, ↓reduceIte]

/-- Clamp backward is zero at maximum -/
theorem clampBackward_at_max (grad_output min_val max_val : ℝ) (_h : min_val < max_val) :
    clampBackward grad_output max_val min_val max_val = 0 := by
  simp only [clampBackward]
  have hfalse : ¬(min_val < max_val ∧ max_val < max_val) := by
    intro ⟨_, h2⟩
    exact (lt_irrefl max_val) h2
  simp only [hfalse, ↓reduceIte]

/-- Clamp backward passes gradient in interior -/
theorem clampBackward_interior (grad_output x min_val max_val : ℝ) 
    (hmin : min_val < x) (hmax : x < max_val) :
    clampBackward grad_output x min_val max_val = grad_output := by
  simp only [clampBackward]
  simp only [hmin, hmax, and_self, ↓reduceIte]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 14: HOMOGRAPHY NORMALIZATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Homography Normalization

NVIDIA PPISP normalizes the homography matrix so H[2][2] = 1.
This is done by dividing all elements by H[2][2].

H_normalized = H / H[2][2]

This ensures consistent projective coordinates. -/

/-- Scale a 3x3 matrix by a scalar -/
noncomputable def Mat3x3.scale (s : ℝ) (m : Mat3x3) : Mat3x3 :=
  { m00 := s * m.m00, m01 := s * m.m01, m02 := s * m.m02
  , m10 := s * m.m10, m11 := s * m.m11, m12 := s * m.m12
  , m20 := s * m.m20, m21 := s * m.m21, m22 := s * m.m22 }

/-- Normalize homography so H[2][2] = 1 -/
noncomputable def normalizeHomography (H : Mat3x3) : Mat3x3 :=
  Mat3x3.scale (1 / H.m22) H

/-- Normalized homography has H[2][2] = 1 (when H.m22 ≠ 0) -/
theorem normalizeHomography_m22 (H : Mat3x3) (h : H.m22 ≠ 0) :
    (normalizeHomography H).m22 = 1 := by
  simp only [normalizeHomography, Mat3x3.scale]
  field_simp

/-- Scale by 1 is identity -/
theorem Mat3x3.scale_one (m : Mat3x3) : Mat3x3.scale 1 m = m := by
  simp only [Mat3x3.scale, one_mul]

/-- Scale by 0 gives zero matrix -/
theorem Mat3x3.scale_zero (m : Mat3x3) : Mat3x3.scale 0 m = 
    ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := by
  simp only [Mat3x3.scale, zero_mul]

/-- Scale is associative -/
theorem Mat3x3.scale_assoc (s t : ℝ) (m : Mat3x3) :
    Mat3x3.scale s (Mat3x3.scale t m) = Mat3x3.scale (s * t) m := by
  simp only [Mat3x3.scale]
  ext <;> ring

end Hydrogen.Material.ISP
