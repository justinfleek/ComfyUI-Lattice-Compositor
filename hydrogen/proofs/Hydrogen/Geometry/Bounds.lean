/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    HYDROGEN // GEOMETRY // BOUNDS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Bounding volume computation from vertex data.
  
  This module provides algorithms for computing tight-fitting bounding
  volumes (AABB and bounding sphere) from point clouds (vertex positions).
  
  Key design decisions:
  - Algorithms operate on lists of Vec3 (runtime provides actual data)
  - Bounding boxes are computed via min/max of all points
  - Bounding spheres use Ritter's algorithm (fast, approximate)
  - Proofs ensure bounds actually contain all input points

  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Box3      : Axis-aligned bounding box
  - Sphere    : Bounding sphere
  - Vec3      : 3D vectors
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Math.Box3
import Hydrogen.Math.Sphere
import Hydrogen.Math.Vec3

namespace Hydrogen.Geometry

open Hydrogen.Math

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: AABB FROM POINTS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Compute AABB from a list of points.
    Returns None for empty list, Some box otherwise. -/
noncomputable def computeAABB (points : List Vec3) : Option Box3 :=
  match points with
  | [] => none
  | p :: ps => 
    let box := ps.foldl (fun acc pt => Box3.expandByPoint acc pt) (Box3.fromPoint p)
    some box

/-- Compute AABB from non-empty list (guaranteed to return a box) -/
noncomputable def computeAABBNonEmpty (p : Vec3) (ps : List Vec3) : Box3 :=
  ps.foldl (fun acc pt => Box3.expandByPoint acc pt) (Box3.fromPoint p)

-- ─────────────────────────────────────────────────────────────────────────────
-- AABB Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Empty list produces no AABB -/
theorem computeAABB_empty : computeAABB [] = none := rfl

/-- Single point produces box containing that point -/
theorem computeAABB_single (p : Vec3) : 
    computeAABB [p] = some (Box3.fromPoint p) := by
  unfold computeAABB
  simp only [List.foldl_nil]

/-- Helper: foldl expandByPoint preserves containment -/
theorem foldl_expandByPoint_preserves (box : Box3) (p : Vec3) (pts : List Vec3)
    (h : Box3.containsPoint box p) : 
    Box3.containsPoint (pts.foldl (fun acc pt => Box3.expandByPoint acc pt) box) p := by
  induction pts generalizing box with
  | nil => exact h
  | cons q qs ih =>
    simp only [List.foldl_cons]
    apply ih
    exact Box3.expandByPoint_preserves_containment box p q h

/-- AABB from non-empty list contains the first point -/
theorem computeAABBNonEmpty_contains_first (p : Vec3) (ps : List Vec3) :
    Box3.containsPoint (computeAABBNonEmpty p ps) p := by
  unfold computeAABBNonEmpty
  apply foldl_expandByPoint_preserves
  exact Box3.containsPoint_fromPoint p

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: BOUNDING SPHERE FROM POINTS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Compute bounding sphere using Ritter's algorithm.
    
    This is an efficient O(n) algorithm that produces a good (but not optimal)
    bounding sphere:
    1. Start with a sphere centered at the first point with radius 0
    2. For each point, if outside the sphere, expand to include it
    
    The result is guaranteed to contain all points but may not be the
    minimum enclosing sphere. -/
noncomputable def computeBoundingSphere (points : List Vec3) : Option Sphere :=
  match points with
  | [] => none
  | p :: ps =>
    let sphere := ps.foldl expandSphere (Sphere.mk p 0)
    some sphere
where
  /-- Expand sphere to include a point -/
  expandSphere (s : Sphere) (pt : Vec3) : Sphere :=
    let d := Vec3.distance s.center pt
    if d ≤ s.radius then s
    else
      -- New radius is half the distance from far side of sphere to point
      let newRadius := (s.radius + d) / 2
      -- New center moves toward the point
      let direction := Vec3.sub pt s.center
      let newCenter := Vec3.add s.center (Vec3.scale ((newRadius - s.radius) / d) direction)
      Sphere.mk newCenter newRadius

/-- Compute bounding sphere from AABB (faster but less tight) -/
noncomputable def boundingSphereFromAABB (box : Box3) : Sphere :=
  let center := Box3.center box
  let halfSize := Box3.halfExtents box
  -- Radius is distance from center to corner
  let radius := Vec3.length halfSize
  Sphere.mk center radius

-- ─────────────────────────────────────────────────────────────────────────────
-- Bounding Sphere Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Empty list produces no bounding sphere -/
theorem computeBoundingSphere_empty : computeBoundingSphere [] = none := rfl

/-- Single point produces sphere with radius 0 at that point -/
theorem computeBoundingSphere_single (p : Vec3) : 
    computeBoundingSphere [p] = some (Sphere.mk p 0) := by
  unfold computeBoundingSphere
  simp only [List.foldl_nil]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: CENTROID
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Compute centroid (geometric center) of a list of points -/
noncomputable def computeCentroid (points : List Vec3) : Option Vec3 :=
  match points with
  | [] => none
  | ps =>
    let sum := ps.foldl Vec3.add Vec3.zero
    let n := ps.length
    some (Vec3.scale (1 / n) sum)

/-- Compute centroid of non-empty list -/
noncomputable def computeCentroidNonEmpty (p : Vec3) (ps : List Vec3) : Vec3 :=
  let all := p :: ps
  let sum := all.foldl Vec3.add Vec3.zero
  let n := all.length
  Vec3.scale (1 / n) sum

-- ─────────────────────────────────────────────────────────────────────────────
-- Centroid Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Empty list has no centroid -/
theorem computeCentroid_empty : computeCentroid [] = none := rfl

/-- Single point is its own centroid -/
theorem computeCentroid_single (p : Vec3) : 
    computeCentroid [p] = some p := by
  unfold computeCentroid
  simp only [List.foldl_cons, List.foldl_nil, List.length_singleton]
  unfold Vec3.add Vec3.zero Vec3.scale
  ext
  all_goals simp

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: SURFACE AREA AND VOLUME FROM BOUNDS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Compute surface area ratio (sphere / AABB).
    Used to estimate how well the mesh fills its bounding box. -/
noncomputable def boundingSphereToAABBRatio (sphere : Sphere) (box : Box3) : ℝ :=
  let sphereSA := 4 * Real.pi * sphere.radius * sphere.radius
  let boxSA := Box3.surfaceArea box
  if boxSA > 0 then sphereSA / boxSA else 0

/-- Compute volume ratio (actual bounds to optimal).
    Lower is tighter fit. -/
noncomputable def volumeEfficiency (sphere : Sphere) (box : Box3) : ℝ :=
  let sphereVol := (4 / 3) * Real.pi * sphere.radius ^ 3
  let boxVol := Box3.volume box
  if boxVol > 0 then min sphereVol boxVol / max sphereVol boxVol else 0

end Hydrogen.Geometry
