/-
  Hydrogen.Math.Plane
  
  Infinite plane in 3D space, defined by normal vector and constant.
  
  PROVEN INVARIANTS:
    1. distanceToPoint_fromNormalAndPoint: point used in constructor lies on plane
    2. negate_negate: negation is involutive
    3. distanceToPoint_negate: negating flips sign of distance
    4. translate_zero: translating by zero is identity
  
  THREE.JS PARITY:
    - set, setFromNormalAndCoplanarPoint, setFromCoplanarPoints
    - negate, distanceToPoint, projectPoint, reflectPoint
    - coplanarPoint, translate
  
  APPLICATIONS:
    - Clipping planes
    - Frustum culling (6 planes)
    - Collision detection
    - Reflection calculations
  
  Status: FOUNDATIONAL - Core plane operations with distance proofs.
-/

import Hydrogen.Math.Vec3
import Hydrogen.Math.Bounded
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hydrogen.Math

-- ═══════════════════════════════════════════════════════════════════════════════
-- PLANE DEFINITION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- An infinite plane in 3D space.
    
    Defined by the equation: normal · point + constant = 0
    
    The normal is NOT required to be normalized, matching Three.js behavior.
    Use `normalize` to get a unit normal plane.
    
    When the normal is a unit vector:
    - constant = -distance from origin (signed distance)
    - positive constant means origin is on positive side of plane
-/
structure Plane where
  normal : Vec3
  constant : ℝ

namespace Plane

-- ─────────────────────────────────────────────────────────────────────────────
-- EXTENSION
-- ─────────────────────────────────────────────────────────────────────────────

@[ext]
theorem ext {a b : Plane} 
    (hn : a.normal = b.normal) (hc : a.constant = b.constant) : 
    a = b := by
  cases a; cases b; simp_all

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONSTRUCTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Default plane: XY plane (normal = +Z, passes through origin) -/
def default : Plane := ⟨Vec3.unitZ, 0⟩

/-- XY plane passing through origin -/
def xy : Plane := ⟨Vec3.unitZ, 0⟩

/-- XZ plane passing through origin -/
def xz : Plane := ⟨Vec3.unitY, 0⟩

/-- YZ plane passing through origin -/
def yz : Plane := ⟨Vec3.unitX, 0⟩

/-- Create plane from normal and constant -/
def fromNormalAndConstant (normal : Vec3) (c : ℝ) : Plane := 
  ⟨normal, c⟩

/-- Create plane from normal and a point on the plane -/
def fromNormalAndPoint (normal : Vec3) (point : Vec3) : Plane := 
  ⟨normal, -(Vec3.dot normal point)⟩

/-- Create plane from three coplanar points (counter-clockwise order for outward normal) -/
def fromCoplanarPoints (a b c : Vec3) : Plane := 
  let ab := Vec3.sub b a
  let ac := Vec3.sub c a
  let normal := Vec3.cross ab ac
  fromNormalAndPoint normal a

-- ═══════════════════════════════════════════════════════════════════════════════
-- BASIC OPERATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Signed distance from a point to the plane.
    
    For unit normal planes:
    - Positive: point is on the positive side (same side as normal)
    - Negative: point is on the negative side
    - Zero: point is on the plane
-/
def distanceToPoint (p : Plane) (point : Vec3) : ℝ := 
  Vec3.dot p.normal point + p.constant

/-- Negate the plane (flip normal and constant) -/
def negate (p : Plane) : Plane := 
  ⟨Vec3.neg p.normal, -p.constant⟩

/-- Normalize the plane (make normal a unit vector) -/
noncomputable def normalize (p : Plane) (h : p.normal ≠ Vec3.zero) : Plane := 
  let len := Vec3.length p.normal
  ⟨Vec3.normalize p.normal h, p.constant / len⟩

/-- Get a point on the plane (closest point to origin for unit normal) -/
def coplanarPoint (p : Plane) : Vec3 := 
  Vec3.scale (-p.constant) p.normal

/-- Project a point onto the plane -/
def projectPoint (p : Plane) (point : Vec3) : Vec3 := 
  let dist := distanceToPoint p point
  Vec3.sub point (Vec3.scale dist p.normal)

/-- Reflect a point across the plane -/
def reflectPoint (p : Plane) (point : Vec3) : Vec3 := 
  let dist := distanceToPoint p point
  Vec3.sub point (Vec3.scale (2 * dist) p.normal)

/-- Translate the plane by a vector -/
def translate (p : Plane) (offset : Vec3) : Plane := 
  ⟨p.normal, p.constant - Vec3.dot p.normal offset⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: BASIC PROPERTIES
-- ═══════════════════════════════════════════════════════════════════════════════

theorem default_normal : default.normal = Vec3.unitZ := rfl
theorem default_constant : default.constant = 0 := rfl

theorem xy_normal : xy.normal = Vec3.unitZ := rfl
theorem xz_normal : xz.normal = Vec3.unitY := rfl
theorem yz_normal : yz.normal = Vec3.unitX := rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: NEGATE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Negate is involutive -/
theorem negate_negate (p : Plane) : negate (negate p) = p := by
  simp only [negate, Vec3.neg]
  apply ext
  · ext <;> ring
  · ring

/-- Negating flips the sign of distance -/
theorem distanceToPoint_negate (p : Plane) (point : Vec3) : 
    distanceToPoint (negate p) point = -(distanceToPoint p point) := by
  simp only [distanceToPoint, negate, Vec3.dot, Vec3.neg]
  ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: DISTANCE TO POINT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Points created by fromNormalAndPoint lie on the plane -/
theorem distanceToPoint_fromNormalAndPoint (normal point : Vec3) : 
    distanceToPoint (fromNormalAndPoint normal point) point = 0 := by
  simp only [distanceToPoint, fromNormalAndPoint]
  ring

/-- Origin lies on plane iff constant is zero -/
theorem distanceToPoint_origin (p : Plane) : 
    distanceToPoint p Vec3.zero = p.constant := by
  simp only [distanceToPoint, Vec3.zero, Vec3.dot]
  ring

/-- Distance is linear in the point direction along normal -/
theorem distanceToPoint_add_normal (p : Plane) (point : Vec3) (t : ℝ) : 
    distanceToPoint p (Vec3.add point (Vec3.scale t p.normal)) = 
    distanceToPoint p point + t * Vec3.dot p.normal p.normal := by
  simp only [distanceToPoint, Vec3.add, Vec3.scale, Vec3.dot]
  ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: TRANSLATE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Translating by zero doesn't change the plane -/
theorem translate_zero (p : Plane) : translate p Vec3.zero = p := by
  simp only [translate, Vec3.zero, Vec3.dot]
  apply ext
  · rfl
  · ring

/-- Translate composition -/
theorem translate_translate (p : Plane) (u v : Vec3) : 
    translate (translate p u) v = translate p (Vec3.add u v) := by
  simp only [translate, Vec3.add, Vec3.dot]
  apply ext
  · rfl
  · ring

/-- Distance changes predictably with translation -/
theorem distanceToPoint_translate (p : Plane) (offset point : Vec3) : 
    distanceToPoint (translate p offset) point = 
    distanceToPoint p point - Vec3.dot p.normal offset := by
  simp only [distanceToPoint, translate, Vec3.dot]
  ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: FROM COPLANAR POINTS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- First point lies on the plane created from three coplanar points -/
theorem distanceToPoint_fromCoplanarPoints_a (a b c : Vec3) : 
    distanceToPoint (fromCoplanarPoints a b c) a = 0 := by
  simp only [fromCoplanarPoints, fromNormalAndPoint, distanceToPoint, 
             Vec3.sub, Vec3.cross, Vec3.dot]
  ring

/-- Second point lies on the plane created from three coplanar points -/
theorem distanceToPoint_fromCoplanarPoints_b (a b c : Vec3) : 
    distanceToPoint (fromCoplanarPoints a b c) b = 0 := by
  simp only [fromCoplanarPoints, fromNormalAndPoint, distanceToPoint, 
             Vec3.sub, Vec3.cross, Vec3.dot]
  ring

/-- Third point lies on the plane created from three coplanar points -/
theorem distanceToPoint_fromCoplanarPoints_c (a b c : Vec3) : 
    distanceToPoint (fromCoplanarPoints a b c) c = 0 := by
  simp only [fromCoplanarPoints, fromNormalAndPoint, distanceToPoint, 
             Vec3.sub, Vec3.cross, Vec3.dot]
  ring

end Plane

end Hydrogen.Math
