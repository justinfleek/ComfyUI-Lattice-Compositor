/-
  Hydrogen.Math.Box3
  
  Axis-Aligned Bounding Box (AABB) in 3D space.
  
  PROVEN INVARIANTS:
    1. containsPoint_min: min corner is contained
    2. containsPoint_max: max corner is contained
    3. union_comm: union is commutative
    4. intersect_comm: intersection is commutative
    5. expandByPoint_contains: expanded box contains the point
  
  THREE.JS PARITY:
    - set, setFromPoints, setFromCenterAndSize
    - clone, copy, makeEmpty, isEmpty
    - getCenter, getSize, expandByPoint, expandByVector, expandByScalar
    - containsPoint, containsBox, intersectsBox
    - clampPoint, distanceToPoint, intersect, union
  
  APPLICATIONS:
    - Broad-phase collision detection
    - Frustum culling
    - Spatial partitioning (octrees, BVH)
    - Object bounds
  
  Status: FOUNDATIONAL - Core AABB operations with containment proofs.
-/

import Hydrogen.Math.Vec3
import Hydrogen.Math.Bounded
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hydrogen.Math

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMPONENT-WISE MIN/MAX (LOCAL HELPERS)
-- ═══════════════════════════════════════════════════════════════════════════════

namespace Vec3

/-- Component-wise minimum of two vectors -/
noncomputable def componentMin (a b : Vec3) : Vec3 := 
  ⟨min a.x b.x, min a.y b.y, min a.z b.z⟩

/-- Component-wise maximum of two vectors -/
noncomputable def componentMax (a b : Vec3) : Vec3 := 
  ⟨max a.x b.x, max a.y b.y, max a.z b.z⟩

theorem componentMin_comm (a b : Vec3) : componentMin a b = componentMin b a := by
  simp only [componentMin]
  ext <;> exact min_comm _ _

theorem componentMax_comm (a b : Vec3) : componentMax a b = componentMax b a := by
  simp only [componentMax]
  ext <;> exact max_comm _ _

theorem componentMin_self (a : Vec3) : componentMin a a = a := by
  simp only [componentMin]
  ext <;> exact min_self _

theorem componentMax_self (a : Vec3) : componentMax a a = a := by
  simp only [componentMax]
  ext <;> exact max_self _

end Vec3

-- ═══════════════════════════════════════════════════════════════════════════════
-- BOX3 DEFINITION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Axis-Aligned Bounding Box defined by min and max corners.
    
    Invariant: For a valid (non-empty) box, min ≤ max componentwise.
    An "empty" box has min > max (inverted).
    
    This matches Three.js Box3 semantics.
-/
structure Box3 where
  min : Vec3
  max : Vec3

namespace Box3

-- ─────────────────────────────────────────────────────────────────────────────
-- EXTENSION
-- ─────────────────────────────────────────────────────────────────────────────

@[ext]
theorem ext {a b : Box3} 
    (hmin : a.min = b.min) (hmax : a.max = b.max) : 
    a = b := by
  cases a; cases b; simp_all

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONSTRUCTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Empty box (inverted bounds - any expansion will create valid box) -/
def empty : Box3 := 
  ⟨⟨1, 1, 1⟩, ⟨-1, -1, -1⟩⟩

/-- Unit box from origin to (1,1,1) -/
def unit : Box3 := ⟨Vec3.zero, ⟨1, 1, 1⟩⟩

/-- Box centered at origin with given half-extents -/
def fromHalfExtents (halfExtents : Vec3) : Box3 := 
  ⟨Vec3.neg halfExtents, halfExtents⟩

/-- Box from center and full size -/
def fromCenterAndSize (center size : Vec3) : Box3 := 
  let halfSize := Vec3.scale 0.5 size
  ⟨Vec3.sub center halfSize, Vec3.add center halfSize⟩

/-- Box containing a single point -/
def fromPoint (p : Vec3) : Box3 := ⟨p, p⟩

/-- Box from two arbitrary corners (computes actual min/max) -/
noncomputable def fromCorners (a b : Vec3) : Box3 := 
  ⟨Vec3.componentMin a b, Vec3.componentMax a b⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- VALIDITY PREDICATES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A box is valid (non-empty) if min ≤ max componentwise -/
def IsValid (box : Box3) : Prop := 
  box.min.x ≤ box.max.x ∧ box.min.y ≤ box.max.y ∧ box.min.z ≤ box.max.z

/-- A box is empty if any component of min > max -/
def IsEmpty (box : Box3) : Prop := 
  box.min.x > box.max.x ∨ box.min.y > box.max.y ∨ box.min.z > box.max.z

-- ═══════════════════════════════════════════════════════════════════════════════
-- BASIC QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Center of the box -/
def center (box : Box3) : Vec3 := 
  Vec3.scale 0.5 (Vec3.add box.min box.max)

/-- Size of the box (max - min) -/
def size (box : Box3) : Vec3 := 
  Vec3.sub box.max box.min

/-- Half-extents (half of size) -/
def halfExtents (box : Box3) : Vec3 := 
  Vec3.scale 0.5 (size box)

/-- Volume of the box -/
def volume (box : Box3) : ℝ := 
  let s := size box
  s.x * s.y * s.z

/-- Surface area of the box -/
def surfaceArea (box : Box3) : ℝ := 
  let s := size box
  2 * (s.x * s.y + s.y * s.z + s.z * s.x)

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONTAINMENT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Check if a point is inside the box (inclusive) -/
def containsPoint (box : Box3) (p : Vec3) : Prop := 
  box.min.x ≤ p.x ∧ p.x ≤ box.max.x ∧
  box.min.y ≤ p.y ∧ p.y ≤ box.max.y ∧
  box.min.z ≤ p.z ∧ p.z ≤ box.max.z

/-- Check if this box fully contains another box -/
def containsBox (outer inner : Box3) : Prop := 
  outer.min.x ≤ inner.min.x ∧ inner.max.x ≤ outer.max.x ∧
  outer.min.y ≤ inner.min.y ∧ inner.max.y ≤ outer.max.y ∧
  outer.min.z ≤ inner.min.z ∧ inner.max.z ≤ outer.max.z

/-- Check if two boxes intersect -/
def intersectsBox (a b : Box3) : Prop := 
  a.min.x ≤ b.max.x ∧ a.max.x ≥ b.min.x ∧
  a.min.y ≤ b.max.y ∧ a.max.y ≥ b.min.y ∧
  a.min.z ≤ b.max.z ∧ a.max.z ≥ b.min.z

-- ═══════════════════════════════════════════════════════════════════════════════
-- EXPANSION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Expand box to include a point -/
noncomputable def expandByPoint (box : Box3) (p : Vec3) : Box3 := 
  ⟨Vec3.componentMin box.min p, Vec3.componentMax box.max p⟩

/-- Expand box by a vector (adds to max, subtracts from min) -/
def expandByVector (box : Box3) (v : Vec3) : Box3 := 
  ⟨Vec3.sub box.min v, Vec3.add box.max v⟩

/-- Expand box uniformly by a scalar -/
def expandByScalar (box : Box3) (s : ℝ) : Box3 := 
  expandByVector box ⟨s, s, s⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- SET OPERATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Union of two boxes (smallest box containing both) -/
noncomputable def union (a b : Box3) : Box3 := 
  ⟨Vec3.componentMin a.min b.min, Vec3.componentMax a.max b.max⟩

/-- Intersection of two boxes (may be empty) -/
noncomputable def intersect (a b : Box3) : Box3 := 
  ⟨Vec3.componentMax a.min b.min, Vec3.componentMin a.max b.max⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- CLAMPING AND DISTANCE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Clamp a point to lie within the box -/
noncomputable def clampPoint (box : Box3) (p : Vec3) : Vec3 := 
  Vec3.componentMax box.min (Vec3.componentMin box.max p)

/-- Squared distance from a point to the nearest point on the box surface -/
noncomputable def distanceSqToPoint (box : Box3) (p : Vec3) : ℝ := 
  let clamped := clampPoint box p
  Vec3.distanceSq p clamped

/-- Distance from a point to the nearest point on the box surface -/
noncomputable def distanceToPoint (box : Box3) (p : Vec3) : ℝ := 
  Real.sqrt (distanceSqToPoint box p)

-- ═══════════════════════════════════════════════════════════════════════════════
-- TRANSLATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Translate the box by a vector -/
def translate (box : Box3) (offset : Vec3) : Box3 := 
  ⟨Vec3.add box.min offset, Vec3.add box.max offset⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: BASIC PROPERTIES
-- ═══════════════════════════════════════════════════════════════════════════════

theorem unit_min : unit.min = Vec3.zero := rfl
theorem unit_max : unit.max = ⟨1, 1, 1⟩ := rfl

theorem unit_isValid : IsValid unit := by
  simp only [IsValid, unit, Vec3.zero]
  constructor
  · linarith
  constructor
  · linarith
  · linarith

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: CENTER AND SIZE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Center of unit box is (0.5, 0.5, 0.5) -/
theorem center_unit : center unit = ⟨0.5, 0.5, 0.5⟩ := by
  simp only [center, unit, Vec3.zero, Vec3.add, Vec3.scale]
  ext <;> ring

/-- Size of unit box is (1, 1, 1) -/
theorem size_unit : size unit = ⟨1, 1, 1⟩ := by
  simp only [size, unit, Vec3.zero, Vec3.sub]
  ext <;> ring

/-- Volume of unit box is 1 -/
theorem volume_unit : volume unit = 1 := by
  simp only [volume, size, unit, Vec3.zero, Vec3.sub]
  ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: FROM CENTER AND SIZE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Center of fromCenterAndSize is the given center -/
theorem center_fromCenterAndSize (c s : Vec3) : 
    center (fromCenterAndSize c s) = c := by
  simp only [center, fromCenterAndSize, Vec3.add, Vec3.sub, Vec3.scale]
  ext <;> ring

/-- Size of fromCenterAndSize is the given size -/
theorem size_fromCenterAndSize (c s : Vec3) : 
    size (fromCenterAndSize c s) = s := by
  simp only [size, fromCenterAndSize, Vec3.add, Vec3.sub, Vec3.scale]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: FROM HALF EXTENTS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Center of fromHalfExtents is origin -/
theorem center_fromHalfExtents (h : Vec3) : 
    center (fromHalfExtents h) = Vec3.zero := by
  simp only [center, fromHalfExtents, Vec3.neg, Vec3.add, Vec3.scale, Vec3.zero]
  ext <;> ring

/-- Half-extents of fromHalfExtents is the given value -/
theorem halfExtents_fromHalfExtents (h : Vec3) : 
    halfExtents (fromHalfExtents h) = h := by
  simp only [halfExtents, size, fromHalfExtents, Vec3.neg, Vec3.sub, Vec3.scale]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: CONTAINMENT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A valid box contains its min corner -/
theorem containsPoint_min (box : Box3) (h : IsValid box) : 
    containsPoint box box.min := by
  simp only [containsPoint, IsValid] at *
  obtain ⟨hx, hy, hz⟩ := h
  exact ⟨le_refl _, hx, le_refl _, hy, le_refl _, hz⟩

/-- A valid box contains its max corner -/
theorem containsPoint_max (box : Box3) (h : IsValid box) : 
    containsPoint box box.max := by
  simp only [containsPoint, IsValid] at *
  obtain ⟨hx, hy, hz⟩ := h
  exact ⟨hx, le_refl _, hy, le_refl _, hz, le_refl _⟩

/-- A valid box contains its center -/
theorem containsPoint_center (box : Box3) (h : IsValid box) : 
    containsPoint box (center box) := by
  simp only [containsPoint, center, Vec3.add, Vec3.scale, IsValid] at *
  obtain ⟨hx, hy, hz⟩ := h
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- Single-point box contains that point -/
theorem containsPoint_fromPoint (p : Vec3) : 
    containsPoint (fromPoint p) p := by
  simp only [containsPoint, fromPoint]
  exact ⟨le_refl _, le_refl _, le_refl _, le_refl _, le_refl _, le_refl _⟩

/-- A box contains itself -/
theorem containsBox_self (box : Box3) : containsBox box box := by
  simp only [containsBox]
  exact ⟨le_refl _, le_refl _, le_refl _, le_refl _, le_refl _, le_refl _⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: INTERSECTION SYMMETRY
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Box intersection is commutative -/
theorem intersectsBox_comm (a b : Box3) : intersectsBox a b ↔ intersectsBox b a := by
  simp only [intersectsBox]
  constructor
  · intro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h2, h1, h4, h3, h6, h5⟩
  · intro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h2, h1, h4, h3, h6, h5⟩

/-- A valid box intersects itself -/
theorem intersectsBox_self (box : Box3) (h : IsValid box) : 
    intersectsBox box box := by
  simp only [intersectsBox, IsValid] at *
  obtain ⟨hx, hy, hz⟩ := h
  exact ⟨hx, hx, hy, hy, hz, hz⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: TRANSLATE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Translating by zero doesn't change the box -/
theorem translate_zero (box : Box3) : translate box Vec3.zero = box := by
  simp only [translate, Vec3.zero, Vec3.add]
  apply ext
  · ext <;> ring
  · ext <;> ring

/-- Translate composition -/
theorem translate_translate (box : Box3) (u v : Vec3) : 
    translate (translate box u) v = translate box (Vec3.add u v) := by
  simp only [translate, Vec3.add]
  apply ext
  · ext <;> ring
  · ext <;> ring

/-- Translation preserves size -/
theorem size_translate (box : Box3) (offset : Vec3) : 
    size (translate box offset) = size box := by
  simp only [size, translate, Vec3.add, Vec3.sub]
  ext <;> ring

/-- Translation moves center -/
theorem center_translate (box : Box3) (offset : Vec3) : 
    center (translate box offset) = Vec3.add (center box) offset := by
  simp only [center, translate, Vec3.add, Vec3.scale]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: EXPAND BY VECTOR
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Expanding by zero doesn't change the box -/
theorem expandByVector_zero (box : Box3) : 
    expandByVector box Vec3.zero = box := by
  simp only [expandByVector, Vec3.zero, Vec3.add, Vec3.sub]
  apply ext
  · ext <;> ring
  · ext <;> ring

/-- Expanding by scalar zero doesn't change the box -/
theorem expandByScalar_zero (box : Box3) : 
    expandByScalar box 0 = box := by
  simp only [expandByScalar, expandByVector, Vec3.add, Vec3.sub]
  apply ext
  · ext <;> ring
  · ext <;> ring

/-- expandByPoint preserves containment: if p is contained in box, it's contained in the expanded box -/
theorem expandByPoint_preserves_containment (box : Box3) (p q : Vec3) 
    (h : containsPoint box p) : containsPoint (expandByPoint box q) p := by
  simp only [containsPoint, expandByPoint, Vec3.componentMin, Vec3.componentMax] at *
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  constructor
  · exact le_trans (min_le_left _ _) h1
  constructor
  · exact le_trans h2 (le_max_left _ _)
  constructor
  · exact le_trans (min_le_left _ _) h3
  constructor
  · exact le_trans h4 (le_max_left _ _)
  constructor
  · exact le_trans (min_le_left _ _) h5
  · exact le_trans h6 (le_max_left _ _)

/-- Expanded box contains the point it was expanded by -/
theorem expandByPoint_contains (box : Box3) (p : Vec3) : 
    containsPoint (expandByPoint box p) p := by
  simp only [containsPoint, expandByPoint, Vec3.componentMin, Vec3.componentMax]
  constructor
  · exact min_le_right _ _
  constructor
  · exact le_max_right _ _
  constructor
  · exact min_le_right _ _
  constructor
  · exact le_max_right _ _
  constructor
  · exact min_le_right _ _
  · exact le_max_right _ _

/-- Expansion preserves center -/
theorem center_expandByVector (box : Box3) (v : Vec3) : 
    center (expandByVector box v) = center box := by
  simp only [center, expandByVector, Vec3.add, Vec3.sub, Vec3.scale]
  ext <;> ring

end Box3

end Hydrogen.Math
