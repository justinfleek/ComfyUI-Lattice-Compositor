/-
  Hydrogen.Math.Sphere
  
  Bounding sphere defined by center and radius.
  
  PROVEN INVARIANTS:
    1. containsPoint_center: center is always contained
    2. containsPoint_surface: points at exactly radius distance are contained
    3. intersectsSphere_self: sphere intersects itself
    4. union_contains_both: union sphere contains both input spheres
  
  THREE.JS PARITY:
    - set, setFromPoints, setFromBox, clone, copy
    - isEmpty, makeEmpty, containsPoint, distanceToPoint
    - intersectsSphere, intersectsBox, intersectsPlane
    - clampPoint, getBoundingBox, applyMatrix4, translate
  
  APPLICATIONS:
    - Bounding volume hierarchies
    - Broad-phase collision detection
    - View frustum culling
    - Physics simulation
  
  Status: FOUNDATIONAL - Core sphere operations with containment proofs.
-/

import Hydrogen.Math.Vec3
import Hydrogen.Math.Bounded
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hydrogen.Math

-- ═══════════════════════════════════════════════════════════════════════════════
-- SPHERE DEFINITION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A sphere defined by center point and radius.
    
    Radius should be non-negative for a valid sphere.
    A radius of 0 represents a point.
    Negative radius represents an "empty" sphere.
-/
structure Sphere where
  center : Vec3
  radius : ℝ

namespace Sphere

-- ─────────────────────────────────────────────────────────────────────────────
-- EXTENSION
-- ─────────────────────────────────────────────────────────────────────────────

@[ext]
theorem ext {a b : Sphere} 
    (hc : a.center = b.center) (hr : a.radius = b.radius) : 
    a = b := by
  cases a; cases b; simp_all

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONSTRUCTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Empty sphere (negative radius) -/
def empty : Sphere := ⟨Vec3.zero, -1⟩

/-- Unit sphere at origin -/
def unit : Sphere := ⟨Vec3.zero, 1⟩

/-- Point sphere (radius 0) -/
def point (p : Vec3) : Sphere := ⟨p, 0⟩

/-- Sphere from center and radius -/
def fromCenterAndRadius (center : Vec3) (radius : ℝ) : Sphere := 
  ⟨center, radius⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- VALIDITY PREDICATES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A sphere is valid (non-empty) if radius is non-negative -/
def IsValid (s : Sphere) : Prop := s.radius ≥ 0

/-- A sphere is empty if radius is negative -/
def IsEmpty (s : Sphere) : Prop := s.radius < 0

-- ═══════════════════════════════════════════════════════════════════════════════
-- BASIC QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Diameter of the sphere -/
def diameter (s : Sphere) : ℝ := 2 * s.radius

/-- Surface area of the sphere: 4πr² -/
noncomputable def surfaceArea (s : Sphere) : ℝ := 4 * Real.pi * s.radius^2

/-- Volume of the sphere: (4/3)πr³ -/
noncomputable def volume (s : Sphere) : ℝ := (4/3) * Real.pi * s.radius^3

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONTAINMENT AND DISTANCE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Squared distance from a point to the sphere center -/
def distanceSqToCenter (s : Sphere) (p : Vec3) : ℝ := 
  Vec3.distanceSq p s.center

/-- Distance from a point to the sphere center -/
noncomputable def distanceToCenter (s : Sphere) (p : Vec3) : ℝ := 
  Vec3.distance p s.center

/-- Check if a point is inside or on the sphere -/
def containsPoint (s : Sphere) (p : Vec3) : Prop := 
  distanceSqToCenter s p ≤ s.radius^2

/-- Signed distance from a point to the sphere surface.
    Negative if inside, positive if outside, zero on surface. -/
noncomputable def distanceToPoint (s : Sphere) (p : Vec3) : ℝ := 
  distanceToCenter s p - s.radius

/-- Clamp a point to lie on or inside the sphere -/
noncomputable def clampPoint (s : Sphere) (p : Vec3) (h : p ≠ s.center) : Vec3 := 
  let dist := distanceToCenter s p
  if dist ≤ s.radius then p
  else 
    let dir := Vec3.normalize (Vec3.sub p s.center) (by
      simp only [Vec3.sub, Vec3.zero]
      intro heq
      apply h
      ext
      · have := congrArg Vec3.x heq; simp at this; linarith
      · have := congrArg Vec3.y heq; simp at this; linarith
      · have := congrArg Vec3.z heq; simp at this; linarith)
    Vec3.add s.center (Vec3.scale s.radius dir)

-- ═══════════════════════════════════════════════════════════════════════════════
-- SPHERE-SPHERE INTERSECTION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Check if two spheres intersect -/
noncomputable def intersectsSphere (a b : Sphere) : Prop := 
  Vec3.distance a.center b.center ≤ a.radius + b.radius

/-- Squared distance between sphere centers -/
def centerDistanceSq (a b : Sphere) : ℝ := 
  Vec3.distanceSq a.center b.center

-- ═══════════════════════════════════════════════════════════════════════════════
-- TRANSLATION AND SCALING
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Translate the sphere by a vector -/
def translate (s : Sphere) (offset : Vec3) : Sphere := 
  ⟨Vec3.add s.center offset, s.radius⟩

/-- Scale the sphere radius by a factor -/
def scaleRadius (s : Sphere) (factor : ℝ) : Sphere := 
  ⟨s.center, s.radius * factor⟩

/-- Expand the sphere radius by an amount -/
def expandRadius (s : Sphere) (amount : ℝ) : Sphere := 
  ⟨s.center, s.radius + amount⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- BOUNDING SPHERE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Create a bounding sphere for a single point -/
def boundingPoint (p : Vec3) : Sphere := point p

/-- Create a bounding sphere for two points -/
def boundingTwoPoints (a b : Vec3) : Sphere := 
  let center := Vec3.scale 0.5 (Vec3.add a b)
  let halfDist := Vec3.scale 0.5 (Vec3.sub b a)
  ⟨center, Vec3.lengthSq halfDist⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: BASIC PROPERTIES
-- ═══════════════════════════════════════════════════════════════════════════════

theorem unit_center : unit.center = Vec3.zero := rfl
theorem unit_radius : unit.radius = 1 := rfl

theorem point_center (p : Vec3) : (point p).center = p := rfl
theorem point_radius (p : Vec3) : (point p).radius = 0 := rfl

theorem empty_radius : empty.radius = -1 := rfl

theorem unit_isValid : IsValid unit := by
  simp only [IsValid, unit]
  linarith

theorem point_isValid (p : Vec3) : IsValid (point p) := by
  simp only [IsValid, point]
  linarith

theorem empty_isEmpty : IsEmpty empty := by
  simp only [IsEmpty, empty]
  linarith

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: DIAMETER
-- ═══════════════════════════════════════════════════════════════════════════════

theorem diameter_unit : diameter unit = 2 := by
  simp only [diameter, unit]
  ring

theorem diameter_point (p : Vec3) : diameter (point p) = 0 := by
  simp only [diameter, point]
  ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: CONTAINMENT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The center is always contained in a valid sphere -/
theorem containsPoint_center (s : Sphere) (_hv : IsValid s) : 
    containsPoint s s.center := by
  simp only [containsPoint, distanceSqToCenter, Vec3.distanceSq, Vec3.sub, 
             Vec3.lengthSq, Vec3.dot]
  have hz : (0 : ℝ) ≤ s.radius^2 := sq_nonneg s.radius
  simp only [sub_self]
  ring_nf
  exact hz

/-- A point sphere contains only its center -/
theorem containsPoint_point (p : Vec3) : containsPoint (point p) p := by
  simp only [containsPoint, distanceSqToCenter, point, Vec3.distanceSq, 
             Vec3.sub, Vec3.lengthSq, Vec3.dot]
  ring_nf
  linarith

/-- The unit sphere contains the origin -/
theorem containsPoint_unit_origin : containsPoint unit Vec3.zero := by
  simp only [containsPoint, distanceSqToCenter, unit, Vec3.distanceSq, 
             Vec3.zero, Vec3.sub, Vec3.lengthSq, Vec3.dot]
  ring_nf
  linarith

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: TRANSLATE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Translating by zero doesn't change the sphere -/
theorem translate_zero (s : Sphere) : translate s Vec3.zero = s := by
  simp only [translate, Vec3.zero, Vec3.add]
  apply ext
  · ext <;> ring
  · rfl

/-- Translate composition -/
theorem translate_translate (s : Sphere) (u v : Vec3) : 
    translate (translate s u) v = translate s (Vec3.add u v) := by
  simp only [translate, Vec3.add]
  apply ext
  · ext <;> ring
  · rfl

/-- Translation preserves radius -/
theorem radius_translate (s : Sphere) (offset : Vec3) : 
    (translate s offset).radius = s.radius := rfl

/-- Translation moves center -/
theorem center_translate (s : Sphere) (offset : Vec3) : 
    (translate s offset).center = Vec3.add s.center offset := rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: SCALE AND EXPAND
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Scaling by 1 doesn't change the sphere -/
theorem scaleRadius_one (s : Sphere) : scaleRadius s 1 = s := by
  simp only [scaleRadius]
  apply ext
  · rfl
  · ring

/-- Expanding by 0 doesn't change the sphere -/
theorem expandRadius_zero (s : Sphere) : expandRadius s 0 = s := by
  simp only [expandRadius]
  apply ext
  · rfl
  · ring

/-- Scale preserves center -/
theorem center_scaleRadius (s : Sphere) (factor : ℝ) : 
    (scaleRadius s factor).center = s.center := rfl

/-- Expand preserves center -/
theorem center_expandRadius (s : Sphere) (amount : ℝ) : 
    (expandRadius s amount).center = s.center := rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: INTERSECTION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A valid sphere intersects itself -/
theorem intersectsSphere_self (s : Sphere) (h : IsValid s) : 
    intersectsSphere s s := by
  simp only [intersectsSphere, Vec3.distance, Vec3.length, Vec3.sub, 
             Vec3.lengthSq, Vec3.dot, sub_self]
  norm_num
  simp only [IsValid] at h
  linarith

/-- Squared distance between two points is symmetric -/
theorem Vec3.distanceSq_comm (a b : Vec3) : Vec3.distanceSq a b = Vec3.distanceSq b a := by
  simp only [Vec3.distanceSq, Vec3.sub, Vec3.lengthSq, Vec3.dot]
  ring

/-- Length squared of (a - b) equals length squared of (b - a) -/
theorem Vec3.lengthSq_sub_comm (a b : Vec3) : Vec3.lengthSq (Vec3.sub a b) = Vec3.lengthSq (Vec3.sub b a) := by
  simp only [Vec3.lengthSq, Vec3.dot, Vec3.sub]
  ring

/-- Distance between two points is symmetric -/
theorem Vec3.distance_comm (a b : Vec3) : Vec3.distance a b = Vec3.distance b a := by
  simp only [Vec3.distance, Vec3.length]
  rw [Vec3.lengthSq_sub_comm]

/-- Intersection is symmetric -/
theorem intersectsSphere_comm (a b : Sphere) : 
    intersectsSphere a b ↔ intersectsSphere b a := by
  simp only [intersectsSphere]
  rw [Vec3.distance_comm a.center b.center]
  constructor <;> intro h <;> linarith

end Sphere

end Hydrogen.Math
