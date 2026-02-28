/-
  Hydrogen.Math.Constraint
  
  Distance and position constraints for soft body physics.
  
  PROVEN INVARIANTS:
    1. correction_parallel_to_separation: Correction is scalar multiple of separation
       → No perpendicular drift during constraint solving
    2. correction_orthogonal_to_tangent: Correction · perp(separation) = 0
    3. correction_zero_when_satisfied: Zero error = zero correction
    4. equal_mass_sum_zero: Equal mass corrections sum to zero (preserves center of mass)
    5. pinned_no_move: Zero inverse mass = no movement
  
  CONSTRAINT TYPES:
    - Distance: Maintain fixed distance between two particles
  
  ALGORITHM (Position-Based Dynamics / Verlet):
    Given particles A, B with rest length L:
    1. diff = B.pos - A.pos
    2. dist = |diff|
    3. error = (dist - L) / dist
    4. correction = diff * error * stiffness * 0.5
    5. A.pos += correction * (invMassA / totalInvMass)
    6. B.pos -= correction * (invMassB / totalInvMass)
  
  Status: FOUNDATIONAL - All theorems fully proven, no sorry, no custom axioms.
-/

import Hydrogen.Math.Vec2
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hydrogen.Math.Constraint

open Vec2

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONSTRAINT STATE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Distance constraint between two particles -/
structure DistanceConstraint where
  restLength : ℝ
  stiffness : ℝ  -- 0 to 1, where 1 = fully rigid

/-- Result of solving a distance constraint -/
structure ConstraintCorrection where
  correctionA : Vec2  -- Add to particle A's position
  correctionB : Vec2  -- Add to particle B's position

-- ═══════════════════════════════════════════════════════════════════════════════
-- BASIC OPERATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Displacement from A to B -/
def separation (posA posB : Vec2) : Vec2 :=
  Vec2.sub posB posA

/-- Squared distance between particles -/
def distanceSq (posA posB : Vec2) : ℝ :=
  Vec2.lengthSq (separation posA posB)

-- ═══════════════════════════════════════════════════════════════════════════════
-- CORRECTION COMPUTATION (SIMPLIFIED - NO DIVISION)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Correction vector given pre-computed error factor
    
    errorFactor = (dist - restLength) / dist  (computed externally)
    
    correction = diff * errorFactor * stiffness * 0.5
    
    This formulation avoids division in the proof-relevant parts.
-/
noncomputable def correctionFromError (posA posB : Vec2) (errorFactor stiffness : ℝ) : Vec2 :=
  let diff := separation posA posB
  Vec2.scale (errorFactor * stiffness / 2) diff

/-- Solve distance constraint with equal masses (simplified case)
    
    Both particles move by half the correction in opposite directions.
-/
noncomputable def solveEqualMass (posA posB : Vec2) (errorFactor stiffness : ℝ) : ConstraintCorrection :=
  let correction := correctionFromError posA posB errorFactor stiffness
  { correctionA := correction
    correctionB := Vec2.neg correction }

/-- Solve distance constraint with mass ratio
    
    ratioA + ratioB should equal 1 for proper mass weighting.
    ratioA = invMassA / (invMassA + invMassB)
    ratioB = invMassB / (invMassA + invMassB)
-/
noncomputable def solveWithRatios (posA posB : Vec2) (errorFactor stiffness ratioA ratioB : ℝ) : ConstraintCorrection :=
  let correction := correctionFromError posA posB errorFactor stiffness
  { correctionA := Vec2.scale ratioA correction
    correctionB := Vec2.neg (Vec2.scale ratioB correction) }

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: CORRECTION DIRECTION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- THE KEY THEOREM: Correction is parallel to separation vector
    
    Correction = scalar * (posB - posA)
    
    This means particles only move along the line connecting them,
    never perpendicular to it. Essential for stable constraint solving.
-/
theorem correction_parallel_to_separation (posA posB : Vec2) (errorFactor stiffness : ℝ) :
    ∃ k : ℝ, correctionFromError posA posB errorFactor stiffness = Vec2.scale k (separation posA posB) := by
  use errorFactor * stiffness / 2
  rfl

/-- Correction is orthogonal to perpendicular of separation
    
    dot(correction, perp(separation)) = 0
-/
theorem correction_orthogonal_to_tangent (posA posB : Vec2) (errorFactor stiffness : ℝ) :
    Vec2.dot (correctionFromError posA posB errorFactor stiffness) 
             (Vec2.perp (separation posA posB)) = 0 := by
  simp only [correctionFromError, separation, Vec2.dot, Vec2.scale, Vec2.perp, Vec2.sub]
  ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: OPPOSITE DIRECTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Equal mass corrections are exactly opposite -/
theorem equal_mass_opposite (posA posB : Vec2) (errorFactor stiffness : ℝ) :
    let result := solveEqualMass posA posB errorFactor stiffness
    result.correctionB = Vec2.neg result.correctionA := by
  simp only [solveEqualMass]

/-- Sum of equal-mass corrections is zero (preserves center of mass) -/
theorem equal_mass_sum_zero (posA posB : Vec2) (errorFactor stiffness : ℝ) :
    let result := solveEqualMass posA posB errorFactor stiffness
    Vec2.add result.correctionA result.correctionB = Vec2.zero := by
  simp only [solveEqualMass, correctionFromError, separation, Vec2.add, Vec2.neg, Vec2.scale, Vec2.sub, Vec2.zero]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: ZERO CONDITIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- When error is zero, correction is zero -/
theorem correction_zero_when_satisfied (posA posB : Vec2) (stiffness : ℝ) :
    correctionFromError posA posB 0 stiffness = Vec2.zero := by
  simp only [correctionFromError, separation, Vec2.scale, Vec2.sub, Vec2.zero]
  ext <;> ring

/-- Zero stiffness produces zero correction -/
theorem correction_zero_stiffness (posA posB : Vec2) (errorFactor : ℝ) :
    correctionFromError posA posB errorFactor 0 = Vec2.zero := by
  simp only [correctionFromError, separation, Vec2.scale, Vec2.sub, Vec2.zero]
  ext <;> ring

/-- When particles are at same position, separation is zero -/
theorem separation_self (p : Vec2) : separation p p = Vec2.zero := by
  simp only [separation, Vec2.sub, Vec2.zero]
  ext <;> ring

/-- Correction is zero when particles coincide -/
theorem correction_zero_coincident (p : Vec2) (errorFactor stiffness : ℝ) :
    correctionFromError p p errorFactor stiffness = Vec2.zero := by
  simp only [correctionFromError, separation, Vec2.scale, Vec2.sub, Vec2.zero]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: MASS WEIGHTING
-- ═══════════════════════════════════════════════════════════════════════════════

/-- When ratioA = 0 (pinned), particle A doesn't move -/
theorem pinned_A_no_move (posA posB : Vec2) (errorFactor stiffness ratioB : ℝ) :
    let result := solveWithRatios posA posB errorFactor stiffness 0 ratioB
    result.correctionA = Vec2.zero := by
  simp only [solveWithRatios, correctionFromError, separation, Vec2.scale, Vec2.sub, Vec2.zero]
  ext <;> ring

/-- When ratioB = 0 (pinned), particle B doesn't move -/
theorem pinned_B_no_move (posA posB : Vec2) (errorFactor stiffness ratioA : ℝ) :
    let result := solveWithRatios posA posB errorFactor stiffness ratioA 0
    result.correctionB = Vec2.zero := by
  simp only [solveWithRatios, correctionFromError, separation, Vec2.scale, Vec2.neg, Vec2.sub, Vec2.zero]
  ext <;> ring

/-- Equal ratios produce opposite corrections -/
theorem equal_ratios_opposite (posA posB : Vec2) (errorFactor stiffness ratio : ℝ) :
    let result := solveWithRatios posA posB errorFactor stiffness ratio ratio
    result.correctionA = Vec2.neg result.correctionB := by
  simp only [solveWithRatios, correctionFromError, separation, Vec2.scale, Vec2.neg, Vec2.sub]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: RATIO SUM
-- ═══════════════════════════════════════════════════════════════════════════════

/-- When ratios sum to 1, weighted corrections preserve a weighted center
    
    correctionA + correctionB = (ratioA - ratioB) * correction
    
    When ratioA = ratioB = 0.5, this equals zero (center preserved).
-/
theorem ratio_correction_sum (posA posB : Vec2) (errorFactor stiffness ratioA ratioB : ℝ) :
    let result := solveWithRatios posA posB errorFactor stiffness ratioA ratioB
    Vec2.add result.correctionA result.correctionB = 
    Vec2.scale (ratioA - ratioB) (correctionFromError posA posB errorFactor stiffness) := by
  simp only [solveWithRatios, correctionFromError, separation, Vec2.add, Vec2.neg, Vec2.scale, Vec2.sub]
  ext <;> ring

/-- Equal ratios (0.5, 0.5) sum to zero -/
theorem half_ratios_sum_zero (posA posB : Vec2) (errorFactor stiffness : ℝ) :
    let result := solveWithRatios posA posB errorFactor stiffness 0.5 0.5
    Vec2.add result.correctionA result.correctionB = Vec2.zero := by
  simp only [solveWithRatios, correctionFromError, separation, Vec2.add, Vec2.neg, Vec2.scale, Vec2.sub, Vec2.zero]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: STIFFNESS SCALING
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Stiffness scales correction linearly -/
theorem stiffness_scales (posA posB : Vec2) (errorFactor s : ℝ) :
    correctionFromError posA posB errorFactor (2 * s) = 
    Vec2.scale 2 (correctionFromError posA posB errorFactor s) := by
  simp only [correctionFromError, separation, Vec2.scale, Vec2.sub]
  ext <;> ring

/-- Error scales correction linearly -/
theorem error_scales (posA posB : Vec2) (stiffness e : ℝ) :
    correctionFromError posA posB (2 * e) stiffness = 
    Vec2.scale 2 (correctionFromError posA posB e stiffness) := by
  simp only [correctionFromError, separation, Vec2.scale, Vec2.sub]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: NEGATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Negating error negates correction (pull vs push) -/
theorem neg_error_neg_correction (posA posB : Vec2) (errorFactor stiffness : ℝ) :
    correctionFromError posA posB (-errorFactor) stiffness = 
    Vec2.neg (correctionFromError posA posB errorFactor stiffness) := by
  simp only [correctionFromError, separation, Vec2.scale, Vec2.neg, Vec2.sub]
  ext <;> ring

/-- Swapping positions negates correction direction -/
theorem swap_positions_neg_correction (posA posB : Vec2) (errorFactor stiffness : ℝ) :
    correctionFromError posB posA errorFactor stiffness = 
    Vec2.neg (correctionFromError posA posB errorFactor stiffness) := by
  simp only [correctionFromError, separation, Vec2.scale, Vec2.neg, Vec2.sub]
  ext <;> ring

end Hydrogen.Math.Constraint
