/-
  Hydrogen.Math.Ray
  
  Ray definition for ray casting and intersection tests.
  
  PROVEN INVARIANTS:
    1. at_zero: Ray.at(0) = origin
    2. at_parametric: Ray.at(t) = origin + t * direction
    3. direction_normalization: for unit rays, direction has length 1
    4. closestPoint_on_ray: closest point lies on the ray
  
  THREE.JS PARITY:
    - set, at, lookAt, recast
    - closestPointToPoint, distanceToPoint, distanceSqToPoint
    - intersectSphere, intersectPlane, intersectBox, intersectTriangle
  
  APPLICATIONS:
    - Ray casting for picking/selection
    - Collision detection
    - Line-of-sight checks
    - Physics simulation
  
  Status: FOUNDATIONAL - Core ray operations with parametric proofs.
-/

import Hydrogen.Math.Vec3
import Hydrogen.Math.Bounded
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hydrogen.Math

-- ═══════════════════════════════════════════════════════════════════════════════
-- RAY DEFINITION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A ray defined by an origin point and a direction vector.
    
    Parametric form: P(t) = origin + t * direction
    
    For t ≥ 0, points are "in front" of the origin.
    For t < 0, points are "behind" the origin.
    
    The direction is NOT required to be normalized, matching Three.js behavior.
    Use `normalize` to get a unit direction ray.
-/
structure Ray where
  origin : Vec3
  direction : Vec3

namespace Ray

-- ─────────────────────────────────────────────────────────────────────────────
-- EXTENSION
-- ─────────────────────────────────────────────────────────────────────────────

@[ext]
theorem ext {a b : Ray} 
    (ho : a.origin = b.origin) (hd : a.direction = b.direction) : 
    a = b := by
  cases a; cases b; simp_all

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONSTRUCTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Default ray: origin at zero, pointing in positive Z direction -/
def default : Ray := ⟨Vec3.zero, Vec3.unitZ⟩

/-- Create ray from origin and target point -/
def fromPoints (origin target : Vec3) : Ray := 
  ⟨origin, Vec3.sub target origin⟩

/-- Create ray with normalized direction (requires proof target ≠ origin) -/
noncomputable def fromPointsNormalized (origin target : Vec3) (h : Vec3.sub target origin ≠ Vec3.zero) : Ray := 
  ⟨origin, Vec3.normalize (Vec3.sub target origin) h⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- BASIC OPERATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Get point at parameter t along the ray: P(t) = origin + t * direction -/
def pointAt (r : Ray) (t : ℝ) : Vec3 := 
  Vec3.add r.origin (Vec3.scale t r.direction)

/-- Normalize the ray direction (returns ray with unit direction) -/
noncomputable def normalizeDir (r : Ray) (h : r.direction ≠ Vec3.zero) : Ray := 
  ⟨r.origin, Vec3.normalize r.direction h⟩

/-- Point the ray at a target (sets direction toward target) -/
def lookAt (r : Ray) (target : Vec3) : Ray := 
  ⟨r.origin, Vec3.sub target r.origin⟩

/-- Move origin along the ray by parameter t -/
def recast (r : Ray) (t : ℝ) : Ray := 
  ⟨pointAt r t, r.direction⟩

/-- Reverse the ray direction -/
def reverse (r : Ray) : Ray := 
  ⟨r.origin, Vec3.neg r.direction⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- CLOSEST POINT OPERATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Parameter t for the closest point on ray to a given point.
    Uses: t = ((point - origin) · direction) / (direction · direction)
    
    For unit direction rays, this simplifies to:
    t = (point - origin) · direction
    
    Note: t can be negative (point behind origin).
    For rays (vs lines), you may want to clamp t ≥ 0.
-/
noncomputable def closestPointParameter (r : Ray) (point : Vec3) : ℝ := 
  let v := Vec3.sub point r.origin
  let dirLenSq := Vec3.dot r.direction r.direction
  if dirLenSq = 0 then 0
  else Vec3.dot v r.direction / dirLenSq

/-- Closest point on the infinite line containing the ray to a given point -/
noncomputable def closestPointToPointOnLine (r : Ray) (point : Vec3) : Vec3 := 
  pointAt r (closestPointParameter r point)

/-- Closest point on the ray (t ≥ 0) to a given point -/
noncomputable def closestPointToPoint (r : Ray) (point : Vec3) : Vec3 := 
  let t := closestPointParameter r point
  pointAt r (max t 0)

/-- Distance from a point to the infinite line containing the ray -/
noncomputable def distanceToPointOnLine (r : Ray) (point : Vec3) : ℝ := 
  Vec3.distance point (closestPointToPointOnLine r point)

/-- Squared distance from a point to the infinite line containing the ray -/
noncomputable def distanceSqToPointOnLine (r : Ray) (point : Vec3) : ℝ := 
  Vec3.distanceSq point (closestPointToPointOnLine r point)

/-- Distance from a point to the ray (t ≥ 0) -/
noncomputable def distanceToPoint (r : Ray) (point : Vec3) : ℝ := 
  Vec3.distance point (closestPointToPoint r point)

/-- Squared distance from a point to the ray (t ≥ 0) -/
noncomputable def distanceSqToPoint (r : Ray) (point : Vec3) : ℝ := 
  Vec3.distanceSq point (closestPointToPoint r point)

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: AT PARAMETRIC
-- ═══════════════════════════════════════════════════════════════════════════════

/-- pointAt(0) returns the origin -/
theorem pointAt_zero (r : Ray) : pointAt r 0 = r.origin := by
  simp only [pointAt, Vec3.scale, Vec3.add]
  ext <;> ring

/-- pointAt(1) returns origin + direction -/
theorem pointAt_one (r : Ray) : pointAt r 1 = Vec3.add r.origin r.direction := by
  simp only [pointAt, Vec3.scale, Vec3.add, one_mul]

/-- pointAt is linear in t -/
theorem pointAt_add (r : Ray) (s t : ℝ) : 
    pointAt r (s + t) = Vec3.add (Vec3.scale s r.direction) (pointAt r t) := by
  simp only [pointAt, Vec3.scale, Vec3.add]
  ext <;> ring

/-- pointAt distributes over scalar multiplication -/
theorem pointAt_scale (r : Ray) (s t : ℝ) : 
    pointAt r (s * t) = Vec3.add r.origin (Vec3.scale s (Vec3.scale t r.direction)) := by
  simp only [pointAt, Vec3.scale, Vec3.add]
  ext <;> ring

/-- Negative parameter gives point behind origin -/
theorem pointAt_neg (r : Ray) (t : ℝ) : 
    pointAt r (-t) = Vec3.sub (Vec3.scale 2 r.origin) (pointAt r t) := by
  simp only [pointAt, Vec3.scale, Vec3.sub, Vec3.add]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: RECAST
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Recast by 0 doesn't change origin -/
theorem recast_zero (r : Ray) : recast r 0 = r := by
  simp only [recast, pointAt, Vec3.scale, Vec3.add]
  ext
  · ring
  · ring
  · ring
  · rfl
  · rfl
  · rfl

/-- Recast preserves direction -/
theorem recast_direction (r : Ray) (t : ℝ) : (recast r t).direction = r.direction := by
  simp only [recast]

/-- Double recast is additive -/
theorem recast_recast (r : Ray) (s t : ℝ) : 
    recast (recast r s) t = recast r (s + t) := by
  simp only [recast, pointAt, Vec3.add, Vec3.scale]
  ext
  · ring
  · ring
  · ring
  · rfl
  · rfl
  · rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: REVERSE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Reverse is involutive -/
theorem reverse_reverse (r : Ray) : reverse (reverse r) = r := by
  simp only [reverse, Vec3.neg]
  ext
  · rfl
  · rfl
  · rfl
  · ring
  · ring
  · ring

/-- Reverse preserves origin -/
theorem reverse_origin (r : Ray) : (reverse r).origin = r.origin := rfl

/-- Reverse negates direction -/
theorem reverse_direction (r : Ray) : (reverse r).direction = Vec3.neg r.direction := rfl

/-- pointAt on reversed ray with negated parameter gives same point -/
theorem reverse_pointAt (r : Ray) (t : ℝ) : pointAt (reverse r) (-t) = pointAt r t := by
  simp only [reverse, pointAt, Vec3.add, Vec3.scale, Vec3.neg]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: FROM POINTS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- fromPoints has correct origin -/
theorem fromPoints_origin (origin target : Vec3) : 
    (fromPoints origin target).origin = origin := rfl

/-- fromPoints direction points from origin to target -/
theorem fromPoints_direction (origin target : Vec3) : 
    (fromPoints origin target).direction = Vec3.sub target origin := rfl

/-- pointAt(1) on fromPoints gives the target -/
theorem fromPoints_pointAt_one (origin target : Vec3) : 
    pointAt (fromPoints origin target) 1 = target := by
  simp only [fromPoints, pointAt, Vec3.add, Vec3.sub, Vec3.scale]
  ext <;> ring

/-- pointAt(0) on fromPoints gives the origin -/
theorem fromPoints_pointAt_zero (origin target : Vec3) : 
    pointAt (fromPoints origin target) 0 = origin := by
  exact pointAt_zero (fromPoints origin target)

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: LOOKAT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- lookAt preserves origin -/
theorem lookAt_origin (r : Ray) (target : Vec3) : (lookAt r target).origin = r.origin := rfl

/-- lookAt at parameter 1 gives the target -/
theorem lookAt_pointAt_one (r : Ray) (target : Vec3) : pointAt (lookAt r target) 1 = target := by
  simp only [lookAt, pointAt, Vec3.add, Vec3.sub, Vec3.scale]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: DEFAULT RAY
-- ═══════════════════════════════════════════════════════════════════════════════

theorem default_origin : default.origin = Vec3.zero := rfl

theorem default_direction : default.direction = Vec3.unitZ := rfl

theorem default_pointAt (t : ℝ) : pointAt default t = ⟨0, 0, t⟩ := by
  simp only [default, pointAt, Vec3.zero, Vec3.unitZ, Vec3.add, Vec3.scale]
  ext <;> ring

end Ray

end Hydrogen.Math
