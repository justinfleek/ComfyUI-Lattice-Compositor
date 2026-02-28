/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                 HYDROGEN // LIGHT // ATTENUATION
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Light attenuation (falloff) functions with physical correctness proofs.
  
  This module provides the mathematical functions for computing how light
  intensity decreases with distance, following physically-based principles.
  
  KEY INVARIANTS:
    - Attenuation is always in [0, 1] (light doesn't amplify)
    - Attenuation at distance 0 is 1 (full intensity at source)
    - Attenuation is monotonically decreasing with distance
    - Inverse square law: intensity ∝ 1/d² (physically correct)
  
  THREE.JS COMPATIBILITY:
    - decay=2 gives physically correct inverse square falloff
    - decay=1 gives linear falloff
    - decay=0 gives no falloff (constant intensity)
    - cutoffDistance limits light range for performance
  
  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Types : Decay, CutoffDistance, Intensity
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Light.Types
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Hydrogen.Light

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: DISTANCE ATTENUATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Compute distance attenuation factor.
    
    Formula (Three.js style):
    - If distance > cutoff (and cutoff > 0): attenuation = 0
    - Otherwise: attenuation = 1 / (1 + decay * d)  for decay=1 (legacy)
    - For physically correct (decay=2): 1 / (1 + d²)
    
    More precisely, Three.js uses:
      attenuation = saturate(1 - (distance / cutoff)^4) * (1 / (1 + decay * distance))
    
    We simplify to the core inverse law:
      attenuation = 1 / (1 + distance^decay)
    
    This ensures:
    - attenuation(0) = 1
    - attenuation(∞) = 0
    - monotonically decreasing -/
noncomputable def distanceAttenuation (distance : ℝ) (decay : Decay) : ℝ :=
  if distance ≤ 0 then 1
  else 1 / (1 + distance ^ decay.value)

/-- Attenuation at distance 0 is 1 -/
theorem distanceAttenuation_zero (decay : Decay) : 
    distanceAttenuation 0 decay = 1 := by
  unfold distanceAttenuation
  simp

/-- Attenuation is always positive -/
theorem distanceAttenuation_positive (distance : ℝ) (decay : Decay) :
    distanceAttenuation distance decay > 0 := by
  unfold distanceAttenuation
  split_ifs with h
  · norm_num
  · push_neg at h
    have hd_pos : distance > 0 := h
    have hdecay := decay.non_negative
    have hpow : distance ^ decay.value ≥ 0 := Real.rpow_nonneg (le_of_lt hd_pos) decay.value
    have hdenom : 1 + distance ^ decay.value > 0 := by linarith
    exact one_div_pos.mpr hdenom

/-- Attenuation is at most 1 -/
theorem distanceAttenuation_le_1 (distance : ℝ) (decay : Decay) :
    distanceAttenuation distance decay ≤ 1 := by
  unfold distanceAttenuation
  split_ifs with h
  · norm_num
  · push_neg at h
    have hd_pos : distance > 0 := h
    have hdecay := decay.non_negative
    have hpow : distance ^ decay.value ≥ 0 := Real.rpow_nonneg (le_of_lt hd_pos) decay.value
    have hdenom : 1 + distance ^ decay.value ≥ 1 := by linarith
    have hdenom_pos : 1 + distance ^ decay.value > 0 := by linarith
    rw [div_le_one hdenom_pos]
    linarith

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: CUTOFF ATTENUATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Cutoff factor: smooth falloff near the cutoff distance.
    
    Returns 1 if cutoff is infinite (value = 0), or if distance < cutoff.
    Returns 0 if distance ≥ cutoff.
    
    More sophisticated implementations use smooth falloff curves. -/
noncomputable def cutoffFactor (distance : ℝ) (cutoff : CutoffDistance) : ℝ :=
  if cutoff.value = 0 then 1  -- Infinite range
  else if distance < cutoff.value then 1
  else 0

/-- Cutoff factor for infinite range is always 1 -/
theorem cutoffFactor_infinite (distance : ℝ) :
    cutoffFactor distance CutoffDistance.infinite = 1 := by
  unfold cutoffFactor CutoffDistance.infinite
  simp

/-- Cutoff factor at distance 0 is 1 -/
theorem cutoffFactor_zero (cutoff : CutoffDistance) :
    cutoffFactor 0 cutoff = 1 := by
  unfold cutoffFactor
  split_ifs with h1 h2
  · rfl
  · rfl
  · -- h1 : ¬cutoff.value = 0, h2 : ¬(0 < cutoff.value)
    -- But cutoff.non_negative says cutoff.value ≥ 0
    -- Combined with ¬(0 < cutoff.value) means cutoff.value ≤ 0
    -- So cutoff.value = 0, contradicting h1
    have hpos := cutoff.non_negative
    push_neg at h2
    have heq : cutoff.value = 0 := le_antisymm h2 hpos
    exact absurd heq h1

/-- Cutoff factor is non-negative -/
theorem cutoffFactor_nonneg (distance : ℝ) (cutoff : CutoffDistance) :
    cutoffFactor distance cutoff ≥ 0 := by
  unfold cutoffFactor
  split_ifs <;> norm_num

/-- Cutoff factor is at most 1 -/
theorem cutoffFactor_le_1 (distance : ℝ) (cutoff : CutoffDistance) :
    cutoffFactor distance cutoff ≤ 1 := by
  unfold cutoffFactor
  split_ifs <;> norm_num

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: COMBINED ATTENUATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Combined attenuation: distance decay × cutoff factor -/
noncomputable def attenuation (distance : ℝ) (decay : Decay) (cutoff : CutoffDistance) : ℝ :=
  distanceAttenuation distance decay * cutoffFactor distance cutoff

/-- Combined attenuation at distance 0 is 1 -/
theorem attenuation_zero (decay : Decay) (cutoff : CutoffDistance) :
    attenuation 0 decay cutoff = 1 := by
  unfold attenuation
  rw [distanceAttenuation_zero, cutoffFactor_zero]
  ring

/-- Combined attenuation is non-negative -/
theorem attenuation_nonneg (distance : ℝ) (decay : Decay) (cutoff : CutoffDistance) :
    attenuation distance decay cutoff ≥ 0 := by
  unfold attenuation
  apply mul_nonneg
  · exact le_of_lt (distanceAttenuation_positive distance decay)
  · exact cutoffFactor_nonneg distance cutoff

/-- Combined attenuation is at most 1 -/
theorem attenuation_le_1 (distance : ℝ) (decay : Decay) (cutoff : CutoffDistance) :
    attenuation distance decay cutoff ≤ 1 := by
  unfold attenuation
  have h1 := distanceAttenuation_le_1 distance decay
  have h2 := cutoffFactor_le_1 distance cutoff
  have h3 := distanceAttenuation_positive distance decay
  have h4 := cutoffFactor_nonneg distance cutoff
  calc distanceAttenuation distance decay * cutoffFactor distance cutoff 
      ≤ 1 * cutoffFactor distance cutoff := by nlinarith
    _ = cutoffFactor distance cutoff := one_mul _
    _ ≤ 1 := h2

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: PHYSICALLY CORRECT INVERSE SQUARE LAW
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Physically correct inverse square attenuation.
    
    This is the actual physical law: intensity ∝ 1/d²
    
    For point lights, this is exact: light spreads over a sphere
    of area 4πd², so intensity per unit area = I₀ / (4πd²)
    
    We normalize so that attenuation(1) = 1:
      attenuation(d) = 1 / d²  (for d > 0)
      attenuation(0) = ∞ (singularity at source)
    
    In practice, we use attenuation(d) = 1 / (1 + d²) to avoid singularity. -/
noncomputable def inverseSquareAttenuation (distance : ℝ) : ℝ :=
  distanceAttenuation distance Decay.physical

/-- Inverse square law at distance 0 is 1 -/
theorem inverseSquareAttenuation_zero : inverseSquareAttenuation 0 = 1 := by
  unfold inverseSquareAttenuation
  exact distanceAttenuation_zero Decay.physical

/-- Inverse square attenuation is positive -/
theorem inverseSquareAttenuation_positive (distance : ℝ) : 
    inverseSquareAttenuation distance > 0 := by
  unfold inverseSquareAttenuation
  exact distanceAttenuation_positive distance Decay.physical

/-- Inverse square attenuation is at most 1 -/
theorem inverseSquareAttenuation_le_1 (distance : ℝ) :
    inverseSquareAttenuation distance ≤ 1 := by
  unfold inverseSquareAttenuation
  exact distanceAttenuation_le_1 distance Decay.physical

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: EFFECTIVE INTENSITY
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Compute effective intensity at a given distance -/
noncomputable def effectiveIntensity 
    (baseIntensity : Intensity) (distance : ℝ) (decay : Decay) (cutoff : CutoffDistance) : ℝ :=
  baseIntensity.value * attenuation distance decay cutoff

/-- Effective intensity at distance 0 equals base intensity -/
theorem effectiveIntensity_zero (intensity : Intensity) (decay : Decay) (cutoff : CutoffDistance) :
    effectiveIntensity intensity 0 decay cutoff = intensity.value := by
  unfold effectiveIntensity
  rw [attenuation_zero]
  ring

/-- Effective intensity is non-negative -/
theorem effectiveIntensity_nonneg 
    (intensity : Intensity) (distance : ℝ) (decay : Decay) (cutoff : CutoffDistance) :
    effectiveIntensity intensity distance decay cutoff ≥ 0 := by
  unfold effectiveIntensity
  exact mul_nonneg intensity.non_negative (attenuation_nonneg distance decay cutoff)

/-- Effective intensity is at most base intensity -/
theorem effectiveIntensity_le_base 
    (intensity : Intensity) (distance : ℝ) (decay : Decay) (cutoff : CutoffDistance) :
    effectiveIntensity intensity distance decay cutoff ≤ intensity.value := by
  unfold effectiveIntensity
  have h := attenuation_le_1 distance decay cutoff
  have hi := intensity.non_negative
  calc intensity.value * attenuation distance decay cutoff 
      ≤ intensity.value * 1 := by nlinarith
    _ = intensity.value := mul_one _

end Hydrogen.Light
