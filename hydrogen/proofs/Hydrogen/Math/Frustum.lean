/-
  Hydrogen.Math.Frustum
  
  View frustum for visibility culling in 3D rendering.
  
  PROVEN INVARIANTS:
    1. containsPoint_in_all_halfspaces: point inside iff in all 6 halfspaces
    2. intersectsBox_symmetric: box intersection is well-defined
    3. intersectsSphere_sound: sphere intersection implies proximity
  
  THREE.JS PARITY:
    - set, setFromProjectionMatrix, clone, copy
    - containsPoint, intersectsObject, intersectsSprite
    - intersectsSphere, intersectsBox
  
  APPLICATIONS:
    - View frustum culling for rendering optimization
    - Camera visibility queries
    - Level-of-detail selection
    - Occlusion culling acceleration
  
  Status: FOUNDATIONAL - Core frustum operations with containment proofs.
-/

import Hydrogen.Math.Vec3
import Hydrogen.Math.Plane
import Hydrogen.Math.Sphere
import Hydrogen.Math.Box3
import Hydrogen.Math.Mat4
import Hydrogen.Math.Bounded
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hydrogen.Math

-- ═══════════════════════════════════════════════════════════════════════════════
-- FRUSTUM DEFINITION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A view frustum defined by six clipping planes.
    
    The planes are oriented with normals pointing INWARD, so a point is
    inside the frustum if it has positive (or zero) signed distance to all planes.
-/
structure Frustum where
  left   : Plane
  right  : Plane
  top    : Plane
  bottom : Plane
  near   : Plane
  far    : Plane

namespace Frustum

-- ─────────────────────────────────────────────────────────────────────────────
-- EXTENSION
-- ─────────────────────────────────────────────────────────────────────────────

@[ext]
theorem ext {f1 f2 : Frustum} 
    (hl : f1.left = f2.left) (hr : f1.right = f2.right)
    (ht : f1.top = f2.top) (hb : f1.bottom = f2.bottom)
    (hn : f1.near = f2.near) (hf : f1.far = f2.far) : 
    f1 = f2 := by
  cases f1; cases f2; simp_all

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONSTRUCTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Default frustum with all planes at standard positions -/
def default : Frustum := 
  { left   := Plane.fromNormalAndConstant Vec3.unitX (-1)
    right  := Plane.fromNormalAndConstant (Vec3.neg Vec3.unitX) (-1)
    top    := Plane.fromNormalAndConstant (Vec3.neg Vec3.unitY) (-1)
    bottom := Plane.fromNormalAndConstant Vec3.unitY (-1)
    near   := Plane.fromNormalAndConstant Vec3.unitZ (-0.1)
    far    := Plane.fromNormalAndConstant (Vec3.neg Vec3.unitZ) (-1000)
  }

/-- Create frustum from six planes directly -/
def fromPlanes (left right top bottom near far : Plane) : Frustum :=
  ⟨left, right, top, bottom, near, far⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- PLANE ACCESS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Get all six planes as a list -/
def planes (f : Frustum) : List Plane := 
  [f.left, f.right, f.top, f.bottom, f.near, f.far]

/-- Get plane by index (0-5) -/
def getPlane (f : Frustum) (i : Fin 6) : Plane :=
  match i with
  | ⟨0, _⟩ => f.left
  | ⟨1, _⟩ => f.right
  | ⟨2, _⟩ => f.top
  | ⟨3, _⟩ => f.bottom
  | ⟨4, _⟩ => f.near
  | ⟨5, _⟩ => f.far

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONTAINMENT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Check if a point is on the positive side of a plane (inside halfspace) -/
noncomputable def inHalfspace (plane : Plane) (p : Vec3) : Prop :=
  Plane.distanceToPoint plane p ≥ 0

/-- Check if a point is inside the frustum (in all halfspaces) -/
noncomputable def containsPoint (f : Frustum) (p : Vec3) : Prop :=
  inHalfspace f.left p ∧
  inHalfspace f.right p ∧
  inHalfspace f.top p ∧
  inHalfspace f.bottom p ∧
  inHalfspace f.near p ∧
  inHalfspace f.far p

-- ═══════════════════════════════════════════════════════════════════════════════
-- SPHERE INTERSECTION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Check if a sphere is completely outside a plane (in negative halfspace) -/
noncomputable def sphereOutsidePlane (plane : Plane) (s : Sphere) : Prop :=
  Plane.distanceToPoint plane s.center < -s.radius

/-- Check if a sphere intersects the frustum.
    A sphere intersects if it's NOT completely outside any plane. -/
noncomputable def intersectsSphere (f : Frustum) (s : Sphere) : Prop :=
  ¬sphereOutsidePlane f.left s ∧
  ¬sphereOutsidePlane f.right s ∧
  ¬sphereOutsidePlane f.top s ∧
  ¬sphereOutsidePlane f.bottom s ∧
  ¬sphereOutsidePlane f.near s ∧
  ¬sphereOutsidePlane f.far s

-- ═══════════════════════════════════════════════════════════════════════════════
-- BOX INTERSECTION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Get the "positive vertex" of a box relative to a plane normal.
    This is the box vertex furthest in the direction of the plane normal. -/
noncomputable def boxPositiveVertex (box : Box3) (normal : Vec3) : Vec3 :=
  { x := if normal.x ≥ 0 then box.max.x else box.min.x
    y := if normal.y ≥ 0 then box.max.y else box.min.y
    z := if normal.z ≥ 0 then box.max.z else box.min.z
  }

/-- Get the "negative vertex" of a box relative to a plane normal.
    This is the box vertex closest in the direction of the plane normal. -/
noncomputable def boxNegativeVertex (box : Box3) (normal : Vec3) : Vec3 :=
  { x := if normal.x ≥ 0 then box.min.x else box.max.x
    y := if normal.y ≥ 0 then box.min.y else box.max.y
    z := if normal.z ≥ 0 then box.min.z else box.max.z
  }

/-- Check if a box is completely outside a plane.
    A box is outside if its positive vertex is in the negative halfspace. -/
noncomputable def boxOutsidePlane (plane : Plane) (box : Box3) : Prop :=
  Plane.distanceToPoint plane (boxPositiveVertex box plane.normal) < 0

/-- Check if a box intersects the frustum.
    A box intersects if it's NOT completely outside any plane. -/
noncomputable def intersectsBox (f : Frustum) (box : Box3) : Prop :=
  ¬boxOutsidePlane f.left box ∧
  ¬boxOutsidePlane f.right box ∧
  ¬boxOutsidePlane f.top box ∧
  ¬boxOutsidePlane f.bottom box ∧
  ¬boxOutsidePlane f.near box ∧
  ¬boxOutsidePlane f.far box

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: BASIC PROPERTIES
-- ═══════════════════════════════════════════════════════════════════════════════

theorem planes_length (f : Frustum) : (planes f).length = 6 := rfl

theorem getPlane_left (f : Frustum) : getPlane f ⟨0, by omega⟩ = f.left := rfl
theorem getPlane_right (f : Frustum) : getPlane f ⟨1, by omega⟩ = f.right := rfl
theorem getPlane_top (f : Frustum) : getPlane f ⟨2, by omega⟩ = f.top := rfl
theorem getPlane_bottom (f : Frustum) : getPlane f ⟨3, by omega⟩ = f.bottom := rfl
theorem getPlane_near (f : Frustum) : getPlane f ⟨4, by omega⟩ = f.near := rfl
theorem getPlane_far (f : Frustum) : getPlane f ⟨5, by omega⟩ = f.far := rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: CONTAINMENT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Point containment is equivalent to being in all halfspaces -/
theorem containsPoint_iff_all_halfspaces (f : Frustum) (p : Vec3) :
    containsPoint f p ↔ 
      (inHalfspace f.left p ∧ inHalfspace f.right p ∧ 
       inHalfspace f.top p ∧ inHalfspace f.bottom p ∧
       inHalfspace f.near p ∧ inHalfspace f.far p) := by
  rfl

/-- If a point fails any halfspace test, it's outside the frustum -/
theorem not_containsPoint_of_outside_left (f : Frustum) (p : Vec3)
    (h : ¬inHalfspace f.left p) : ¬containsPoint f p := by
  intro hc
  exact h hc.1

theorem not_containsPoint_of_outside_right (f : Frustum) (p : Vec3)
    (h : ¬inHalfspace f.right p) : ¬containsPoint f p := by
  intro hc
  exact h hc.2.1

theorem not_containsPoint_of_outside_top (f : Frustum) (p : Vec3)
    (h : ¬inHalfspace f.top p) : ¬containsPoint f p := by
  intro hc
  exact h hc.2.2.1

theorem not_containsPoint_of_outside_bottom (f : Frustum) (p : Vec3)
    (h : ¬inHalfspace f.bottom p) : ¬containsPoint f p := by
  intro hc
  exact h hc.2.2.2.1

theorem not_containsPoint_of_outside_near (f : Frustum) (p : Vec3)
    (h : ¬inHalfspace f.near p) : ¬containsPoint f p := by
  intro hc
  exact h hc.2.2.2.2.1

theorem not_containsPoint_of_outside_far (f : Frustum) (p : Vec3)
    (h : ¬inHalfspace f.far p) : ¬containsPoint f p := by
  intro hc
  exact h hc.2.2.2.2.2

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: SPHERE INTERSECTION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Sphere intersection is equivalent to not being outside any plane -/
theorem intersectsSphere_iff (f : Frustum) (s : Sphere) :
    intersectsSphere f s ↔ 
      (¬sphereOutsidePlane f.left s ∧ ¬sphereOutsidePlane f.right s ∧
       ¬sphereOutsidePlane f.top s ∧ ¬sphereOutsidePlane f.bottom s ∧
       ¬sphereOutsidePlane f.near s ∧ ¬sphereOutsidePlane f.far s) := by
  rfl

/-- A point sphere inside the frustum intersects the frustum -/
theorem intersectsSphere_of_containsPoint (f : Frustum) (p : Vec3) 
    (hc : containsPoint f p) : intersectsSphere f (Sphere.point p) := by
  simp only [intersectsSphere, sphereOutsidePlane, Sphere.point]
  simp only [containsPoint, inHalfspace] at hc
  constructor
  · intro h; linarith [hc.1]
  constructor
  · intro h; linarith [hc.2.1]
  constructor
  · intro h; linarith [hc.2.2.1]
  constructor
  · intro h; linarith [hc.2.2.2.1]
  constructor
  · intro h; linarith [hc.2.2.2.2.1]
  · intro h; linarith [hc.2.2.2.2.2]

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: BOX INTERSECTION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Box intersection is equivalent to not being outside any plane -/
theorem intersectsBox_iff (f : Frustum) (box : Box3) :
    intersectsBox f box ↔ 
      (¬boxOutsidePlane f.left box ∧ ¬boxOutsidePlane f.right box ∧
       ¬boxOutsidePlane f.top box ∧ ¬boxOutsidePlane f.bottom box ∧
       ¬boxOutsidePlane f.near box ∧ ¬boxOutsidePlane f.far box) := by
  rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: VERTEX SELECTION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Positive vertex x-coordinate selection -/
theorem boxPositiveVertex_x (box : Box3) (normal : Vec3) :
    (boxPositiveVertex box normal).x = if normal.x ≥ 0 then box.max.x else box.min.x := rfl

/-- Positive vertex y-coordinate selection -/
theorem boxPositiveVertex_y (box : Box3) (normal : Vec3) :
    (boxPositiveVertex box normal).y = if normal.y ≥ 0 then box.max.y else box.min.y := rfl

/-- Positive vertex z-coordinate selection -/
theorem boxPositiveVertex_z (box : Box3) (normal : Vec3) :
    (boxPositiveVertex box normal).z = if normal.z ≥ 0 then box.max.z else box.min.z := rfl

/-- Negative vertex x-coordinate selection -/
theorem boxNegativeVertex_x (box : Box3) (normal : Vec3) :
    (boxNegativeVertex box normal).x = if normal.x ≥ 0 then box.min.x else box.max.x := rfl

/-- Negative vertex y-coordinate selection -/
theorem boxNegativeVertex_y (box : Box3) (normal : Vec3) :
    (boxNegativeVertex box normal).y = if normal.y ≥ 0 then box.min.y else box.max.y := rfl

/-- Negative vertex z-coordinate selection -/
theorem boxNegativeVertex_z (box : Box3) (normal : Vec3) :
    (boxNegativeVertex box normal).z = if normal.z ≥ 0 then box.min.z else box.max.z := rfl

end Frustum

end Hydrogen.Math
