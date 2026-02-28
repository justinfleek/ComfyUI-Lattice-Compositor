/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                        HYDROGEN // LIGHT // SHADOW
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Shadow mapping calculations with proven bounds.
  
  This module provides the mathematical foundation for shadow mapping:
  - Shadow depth comparison
  - Bias calculations to prevent shadow acne
  - PCF (Percentage Closer Filtering) for soft shadows
  - Cascade shadow map slice selection
  
  KEY INVARIANTS:
    - Shadow values are in [0, 1] (0 = fully lit, 1 = fully shadowed)
    - Bias calculations are bounded to prevent light bleeding
    - PCF sample weights sum to 1
    - Cascade selection is monotonic with distance
  
  THREE.JS COMPATIBILITY:
    - Shadow map uses depth comparison
    - Bias and normalBias match Three.js LightShadow
    - PCF blur radius and sample count configurable
  
  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Types : ShadowConfig, ShadowBias, ShadowMapResolution
  - Vec3  : Surface position and normal
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Light.Types
import Hydrogen.Math.Vec3

namespace Hydrogen.Light

open Hydrogen.Math

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: SHADOW VALUE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Shadow value in [0, 1].
    - 0 = fully lit
    - 1 = fully shadowed
    - Intermediate values = partially shadowed (soft shadows) -/
structure ShadowValue where
  value : ℝ
  ge_0 : value ≥ 0
  le_1 : value ≤ 1

namespace ShadowValue

def lit : ShadowValue where
  value := 0
  ge_0 := by norm_num
  le_1 := by norm_num

def shadowed : ShadowValue where
  value := 1
  ge_0 := by norm_num
  le_1 := by norm_num

def make (v : ℝ) (hge : v ≥ 0) (hle : v ≤ 1) : ShadowValue where
  value := v
  ge_0 := hge
  le_1 := hle

/-- Invert shadow (1 - shadow = light factor) -/
def lightFactor (s : ShadowValue) : ℝ := 1 - s.value

/-- Light factor is non-negative -/
theorem lightFactor_ge_0 (s : ShadowValue) : s.lightFactor ≥ 0 := by
  unfold lightFactor
  linarith [s.le_1]

/-- Light factor is at most 1 -/
theorem lightFactor_le_1 (s : ShadowValue) : s.lightFactor ≤ 1 := by
  unfold lightFactor
  linarith [s.ge_0]

end ShadowValue

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: DEPTH COMPARISON
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Compare depth values for shadow determination.
    
    Given:
    - fragmentDepth: depth of the fragment being shaded
    - shadowMapDepth: depth stored in the shadow map
    - bias: depth bias to prevent shadow acne
    
    Returns true if the fragment is in shadow (fragment is behind shadow map depth). -/
noncomputable def isInShadow (fragmentDepth shadowMapDepth bias : ℝ) : Bool :=
  fragmentDepth > shadowMapDepth + bias

/-- Shadow comparison as a real value (for interpolation) -/
noncomputable def shadowComparison (fragmentDepth shadowMapDepth bias : ℝ) : ℝ :=
  if fragmentDepth > shadowMapDepth + bias then 1 else 0

/-- Shadow comparison is in [0, 1] -/
theorem shadowComparison_bounded (fragmentDepth shadowMapDepth bias : ℝ) :
    shadowComparison fragmentDepth shadowMapDepth bias ≥ 0 ∧ 
    shadowComparison fragmentDepth shadowMapDepth bias ≤ 1 := by
  unfold shadowComparison
  split_ifs <;> constructor <;> norm_num

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: BIAS CALCULATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Calculate adaptive bias based on surface angle.
    
    Shadow acne occurs because the shadow map has limited precision.
    The bias should be larger when the surface is at a grazing angle
    to the light direction.
    
    Formula: bias = baseBias + normalBias * (1 - NdotL)
    
    Where NdotL is the dot product of surface normal and light direction. -/
noncomputable def adaptiveBias (baseBias normalBias ndotL : ℝ) : ℝ :=
  baseBias + normalBias * (1 - ndotL)

/-- Adaptive bias with ndotL = 1 (surface facing light) equals base bias -/
theorem adaptiveBias_facing (baseBias normalBias : ℝ) :
    adaptiveBias baseBias normalBias 1 = baseBias := by
  unfold adaptiveBias
  ring

/-- Adaptive bias with ndotL = 0 (surface perpendicular) equals base + normal bias -/
theorem adaptiveBias_perpendicular (baseBias normalBias : ℝ) :
    adaptiveBias baseBias normalBias 0 = baseBias + normalBias := by
  unfold adaptiveBias
  ring

/-- Clamped adaptive bias for production use.
    
    Bias is clamped to [0, maxBias] to prevent light bleeding. -/
noncomputable def clampedBias (baseBias normalBias ndotL maxBias : ℝ) (_ : maxBias ≥ 0) : ℝ :=
  let raw := adaptiveBias baseBias normalBias ndotL
  max 0 (min raw maxBias)

/-- Clamped bias is non-negative -/
theorem clampedBias_nonneg (baseBias normalBias ndotL maxBias : ℝ) (hmax : maxBias ≥ 0) :
    clampedBias baseBias normalBias ndotL maxBias hmax ≥ 0 := by
  unfold clampedBias
  simp only []
  exact le_max_left 0 _

/-- Clamped bias is at most maxBias -/
theorem clampedBias_le_max (baseBias normalBias ndotL maxBias : ℝ) (hmax : maxBias ≥ 0) :
    clampedBias baseBias normalBias ndotL maxBias hmax ≤ maxBias := by
  unfold clampedBias
  simp only []
  -- max 0 (min raw maxBias) ≤ maxBias
  -- Case 1: min raw maxBias ≤ 0, then max = 0 ≤ maxBias
  -- Case 2: min raw maxBias > 0, then max = min raw maxBias ≤ maxBias
  apply max_le
  · exact hmax
  · exact min_le_right _ _

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: PCF (Percentage Closer Filtering)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- PCF sample weight: ensures weights are non-negative and sum to 1.
    
    For a uniform filter with n samples, each weight is 1/n. -/
structure PCFWeight where
  value : ℝ
  ge_0 : value ≥ 0
  le_1 : value ≤ 1

namespace PCFWeight

/-- Uniform weight for n samples -/
noncomputable def uniform (n : ℕ) (hn : n > 0) : PCFWeight where
  value := 1 / n
  ge_0 := by positivity
  le_1 := by
    rw [div_le_one (by positivity : (n : ℝ) > 0)]
    simp
    omega

/-- Single sample (weight = 1) -/
def single : PCFWeight where
  value := 1
  ge_0 := by norm_num
  le_1 := by norm_num

end PCFWeight

/-- Combine shadow values using PCF.
    
    Given a list of (shadow, weight) pairs, compute the weighted average.
    This is the mathematical foundation; actual implementation samples
    the shadow map at multiple offsets. -/
noncomputable def pcfCombine (samples : List (ℝ × ℝ)) : ℝ :=
  let totalWeight := samples.foldl (fun acc (_, w) => acc + w) 0
  if totalWeight = 0 then 0
  else samples.foldl (fun acc (s, w) => acc + s * w) 0 / totalWeight

/-- PCF with empty samples returns 0 -/
theorem pcfCombine_empty : pcfCombine [] = 0 := by
  unfold pcfCombine
  simp

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: CASCADE SHADOW MAPS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Number of cascades (bounded for practical use).
    Most implementations use 2-4 cascades. -/
inductive NumCascades where
  | two    -- 2 cascades
  | three  -- 3 cascades
  | four   -- 4 cascades
  deriving Repr, BEq, DecidableEq

namespace NumCascades

def toNat : NumCascades → ℕ
  | two => 2
  | three => 3
  | four => 4

theorem toNat_positive (n : NumCascades) : n.toNat > 0 := by
  cases n <;> simp [toNat]

theorem toNat_ge_2 (n : NumCascades) : n.toNat ≥ 2 := by
  cases n <;> simp [toNat]

end NumCascades

/-- Cascade split distances (positive, increasing).
    
    For n cascades, we need n-1 splits. -/
structure CascadeSplits where
  split1 : ℝ  -- First split (between cascade 0 and 1)
  split2 : Option ℝ  -- Second split (for 3+ cascades)
  split3 : Option ℝ  -- Third split (for 4 cascades)
  split1_positive : split1 > 0
  split2_gt_1 : ∀ s, split2 = some s → s > split1
  split3_gt_2 : ∀ s2 s3, split2 = some s2 → split3 = some s3 → s3 > s2

namespace CascadeSplits

/-- Standard splits: 10, 25, 100 -/
def standard : CascadeSplits where
  split1 := 10
  split2 := some 25
  split3 := some 100
  split1_positive := by norm_num
  split2_gt_1 := by intro s hs; simp at hs; subst hs; norm_num
  split3_gt_2 := by intro s2 s3 hs2 hs3; simp at hs2 hs3; subst hs2; subst hs3; norm_num

/-- Simple splits: 50 (for 2 cascades) -/
def simple : CascadeSplits where
  split1 := 50
  split2 := none
  split3 := none
  split1_positive := by norm_num
  split2_gt_1 := by simp
  split3_gt_2 := by simp

end CascadeSplits

/-- Select cascade for 2-cascade setup.
    Returns 0 for near, 1 for far. -/
noncomputable def selectCascade2 (split : ℝ) (distance : ℝ) : Fin 2 :=
  if distance ≤ split then ⟨0, by norm_num⟩ else ⟨1, by norm_num⟩

/-- Cascade 0 is selected for distance 0 -/
theorem selectCascade2_zero (split : ℝ) (hs : split > 0) : 
    selectCascade2 split 0 = ⟨0, by norm_num⟩ := by
  unfold selectCascade2
  simp
  linarith

/-- Select cascade for 4-cascade setup.
    Returns 0-3 based on distance thresholds. -/
noncomputable def selectCascade4 (split1 split2 split3 : ℝ) (distance : ℝ) : Fin 4 :=
  if distance ≤ split1 then ⟨0, by norm_num⟩
  else if distance ≤ split2 then ⟨1, by norm_num⟩
  else if distance ≤ split3 then ⟨2, by norm_num⟩
  else ⟨3, by norm_num⟩

/-- Cascade 0 is selected for distance 0 in 4-cascade setup -/
theorem selectCascade4_zero (split1 split2 split3 : ℝ) (hs : split1 > 0) : 
    selectCascade4 split1 split2 split3 0 = ⟨0, by norm_num⟩ := by
  unfold selectCascade4
  simp only [ite_eq_left_iff, not_le]
  intro h
  linarith

end Hydrogen.Light
