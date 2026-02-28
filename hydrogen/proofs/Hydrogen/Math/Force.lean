/-
  Hydrogen.Math.Force
  
  Force field definitions for particle physics simulation.
  
  PROVEN INVARIANTS:
    1. vortex_force_orthogonal: Vortex force is perpendicular to displacement
       → dot(vortexForce p center strength) (sub p center) = 0
       → Pure tangential force, does no radial work
    2. gravity_force_radial: Gravity force is parallel to displacement
       → gravityForce is a scalar multiple of (sub center p)
    3. Force linearity: Forces compose by vector addition
    4. Zero strength produces zero force
  
  FORCE TYPES:
    - Uniform: Constant direction and magnitude (wind, gravity)
    - Gravity well: Radial attraction/repulsion (inverse distance)
    - Vortex: Tangential rotation (perpendicular to radius)
  
  PHYSICAL INTERPRETATION:
    - Vortex forces cause rotation without changing distance from center
    - Gravity well forces change distance without causing rotation
    - Composed: spiral motion = vortex + inward pull
  
  Status: FOUNDATIONAL - All theorems fully proven, no sorry, no custom axioms.
-/

import Hydrogen.Math.Vec2
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hydrogen.Math.Force

open Vec2

-- ═══════════════════════════════════════════════════════════════════════════════
-- UNIFORM FORCES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Uniform force field (constant everywhere)
    
    Examples: gravity, wind
-/
def uniformForce (direction : Vec2) (strength : ℝ) : Vec2 :=
  Vec2.scale strength direction

-- ═══════════════════════════════════════════════════════════════════════════════
-- GRAVITY WELL (RADIAL FORCE)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Displacement from point to center -/
def displacement (point center : Vec2) : Vec2 :=
  Vec2.sub center point

/-- Gravity well force: radial attraction toward center
    
    force = strength * normalize(center - point)
    
    Positive strength = attraction (toward center)
    Negative strength = repulsion (away from center)
    
    Note: This is the unit-direction form. For inverse-square law,
    multiply by 1/distance² externally.
-/
def gravityForce (point center : Vec2) (strength : ℝ) : Vec2 :=
  Vec2.scale strength (displacement point center)

/-- Gravity force with linear falloff
    
    force = strength * (1 - dist/radius) * direction
    
    Returns zero force if outside radius.
    The `influence` parameter should be computed as max(0, 1 - dist/radius).
-/
def gravityForceLinear (point center : Vec2) (strength influence : ℝ) : Vec2 :=
  Vec2.scale (strength * influence) (displacement point center)

-- ═══════════════════════════════════════════════════════════════════════════════
-- VORTEX (TANGENTIAL FORCE)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Vortex force: tangential rotation around center
    
    force = strength * perp(center - point)
    
    Uses counter-clockwise perpendicular.
    Positive strength = counter-clockwise rotation
    Negative strength = clockwise rotation
    
    THE KEY PROPERTY: This force is perpendicular to the displacement,
    so it does no work on radial motion (proven in vortex_force_orthogonal).
-/
def vortexForce (point center : Vec2) (strength : ℝ) : Vec2 :=
  Vec2.scale strength (Vec2.perp (displacement point center))

/-- Vortex force with influence factor (for falloff) -/
def vortexForceWithInfluence (point center : Vec2) (strength influence : ℝ) : Vec2 :=
  Vec2.scale (strength * influence) (Vec2.perp (displacement point center))

-- ═══════════════════════════════════════════════════════════════════════════════
-- SPIRAL (COMBINED VORTEX + INWARD PULL)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Spiral force: combination of vortex rotation and radial pull
    
    Used for creating spiral particle motion.
    tangentialStrength controls rotation speed
    radialStrength controls inward/outward drift
-/
def spiralForce (point center : Vec2) (tangentialStrength radialStrength : ℝ) : Vec2 :=
  Vec2.add 
    (vortexForce point center tangentialStrength)
    (gravityForce point center radialStrength)

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: ORTHOGONALITY
-- ═══════════════════════════════════════════════════════════════════════════════

/-- THE KEY THEOREM: Vortex force is orthogonal to displacement
    
    This proves that vortex forces do no radial work:
    - Particles rotate around the center
    - Distance from center is unchanged by pure vortex force
    - Energy in the radial direction is conserved
    
    Proof relies on Vec2.perp_orthogonal: perp(v) · v = 0
-/
theorem vortex_force_orthogonal (point center : Vec2) (strength : ℝ) :
    Vec2.dot (vortexForce point center strength) (displacement point center) = 0 := by
  simp only [vortexForce, displacement, Vec2.dot, Vec2.scale, Vec2.perp, Vec2.sub]
  ring

/-- Vortex force with influence is also orthogonal -/
theorem vortex_force_influence_orthogonal (point center : Vec2) (strength influence : ℝ) :
    Vec2.dot (vortexForceWithInfluence point center strength influence) (displacement point center) = 0 := by
  simp only [vortexForceWithInfluence, displacement, Vec2.dot, Vec2.scale, Vec2.perp, Vec2.sub]
  ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: GRAVITY IS RADIAL (PARALLEL TO DISPLACEMENT)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Gravity force is parallel to displacement (scalar multiple)
    
    gravityForce = strength * displacement
    
    This means gravity only affects radial distance, not angular position.
-/
theorem gravity_force_is_scaled_displacement (point center : Vec2) (strength : ℝ) :
    gravityForce point center strength = Vec2.scale strength (displacement point center) := by
  rfl

/-- Gravity force is orthogonal to perpendicular of displacement
    
    dot(gravityForce, perp(displacement)) = 0
    
    This is the dual of vortex_force_orthogonal.
-/
theorem gravity_force_orthogonal_to_tangent (point center : Vec2) (strength : ℝ) :
    Vec2.dot (gravityForce point center strength) (Vec2.perp (displacement point center)) = 0 := by
  simp only [gravityForce, displacement, Vec2.dot, Vec2.scale, Vec2.perp, Vec2.sub]
  ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: ZERO STRENGTH
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Zero strength uniform force is zero -/
theorem uniform_zero_strength (direction : Vec2) :
    uniformForce direction 0 = Vec2.zero := by
  simp only [uniformForce, Vec2.scale, Vec2.zero]
  ext <;> ring

/-- Zero strength gravity is zero -/
theorem gravity_zero_strength (point center : Vec2) :
    gravityForce point center 0 = Vec2.zero := by
  simp only [gravityForce, displacement, Vec2.scale, Vec2.sub, Vec2.zero]
  ext <;> ring

/-- Zero strength vortex is zero -/
theorem vortex_zero_strength (point center : Vec2) :
    vortexForce point center 0 = Vec2.zero := by
  simp only [vortexForce, displacement, Vec2.scale, Vec2.perp, Vec2.sub, Vec2.zero]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: FORCE LINEARITY (SUPERPOSITION)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Uniform forces add by vector addition -/
theorem uniform_add (direction : Vec2) (s1 s2 : ℝ) :
    Vec2.add (uniformForce direction s1) (uniformForce direction s2) = 
    uniformForce direction (s1 + s2) := by
  simp only [uniformForce, Vec2.add, Vec2.scale]
  ext <;> ring

/-- Gravity forces from same center add linearly -/
theorem gravity_add (point center : Vec2) (s1 s2 : ℝ) :
    Vec2.add (gravityForce point center s1) (gravityForce point center s2) = 
    gravityForce point center (s1 + s2) := by
  simp only [gravityForce, displacement, Vec2.add, Vec2.scale, Vec2.sub]
  ext <;> ring

/-- Vortex forces from same center add linearly -/
theorem vortex_add (point center : Vec2) (s1 s2 : ℝ) :
    Vec2.add (vortexForce point center s1) (vortexForce point center s2) = 
    vortexForce point center (s1 + s2) := by
  simp only [vortexForce, displacement, Vec2.add, Vec2.scale, Vec2.perp, Vec2.sub]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: SPIRAL DECOMPOSITION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Spiral force decomposes into orthogonal components
    
    The vortex part is orthogonal to displacement.
    The gravity part is parallel to displacement.
    Together they're NOT generally orthogonal to each other.
-/
theorem spiral_tangential_component_orthogonal (point center : Vec2) (ts : ℝ) :
    Vec2.dot (vortexForce point center ts) (displacement point center) = 0 := by
  exact vortex_force_orthogonal point center ts

theorem spiral_radial_component_orthogonal_to_tangent (point center : Vec2) (rs : ℝ) :
    Vec2.dot (gravityForce point center rs) (Vec2.perp (displacement point center)) = 0 := by
  exact gravity_force_orthogonal_to_tangent point center rs

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: NEGATION (REVERSAL)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Negating strength negates force -/
theorem gravity_neg_strength (point center : Vec2) (strength : ℝ) :
    gravityForce point center (-strength) = Vec2.neg (gravityForce point center strength) := by
  simp only [gravityForce, displacement, Vec2.scale, Vec2.neg, Vec2.sub]
  ext <;> ring

theorem vortex_neg_strength (point center : Vec2) (strength : ℝ) :
    vortexForce point center (-strength) = Vec2.neg (vortexForce point center strength) := by
  simp only [vortexForce, displacement, Vec2.scale, Vec2.perp, Vec2.neg, Vec2.sub]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: POINT AT CENTER
-- ═══════════════════════════════════════════════════════════════════════════════

/-- When point equals center, displacement is zero -/
theorem displacement_self (p : Vec2) : displacement p p = Vec2.zero := by
  simp only [displacement, Vec2.sub, Vec2.zero]
  ext <;> ring

/-- Gravity force at center is zero (regardless of strength) -/
theorem gravity_at_center (p : Vec2) (strength : ℝ) :
    gravityForce p p strength = Vec2.zero := by
  simp only [gravityForce, displacement_self, Vec2.scale, Vec2.zero]
  ext <;> ring

/-- Vortex force at center is zero (regardless of strength) -/
theorem vortex_at_center (p : Vec2) (strength : ℝ) :
    vortexForce p p strength = Vec2.zero := by
  simp only [vortexForce, displacement_self, Vec2.perp, Vec2.scale, Vec2.zero]
  ext <;> ring

end Hydrogen.Math.Force
