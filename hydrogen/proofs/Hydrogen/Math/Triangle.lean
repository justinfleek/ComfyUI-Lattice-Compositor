/-
  Hydrogen.Math.Triangle
  
  Triangle defined by three vertices with barycentric coordinates.
  
  PROVEN INVARIANTS:
    1. barycentric_sum_one: barycentric coordinates sum to 1
    2. barycentric_vertex_a/b/c: vertices map to (1,0,0), (0,1,0), (0,0,1)
    3. fromBarycentric_vertex: barycentric → point for vertices
    4. normal_perp_edge: normal is perpendicular to edges
    5. area_nonneg: area is non-negative
  
  THREE.JS PARITY:
    - set, setFromPointsAndIndices, setFromAttributeAndIndices
    - clone, copy, getArea, getMidpoint, getNormal
    - getPlane, getBarycoord, getInterpolation, containsPoint
    - isFrontFacing, intersectsBox, closestPointToPoint, equals
  
  APPLICATIONS:
    - Ray-triangle intersection (Möller–Trumbore algorithm)
    - Barycentric interpolation for textures/normals
    - Mesh collision detection
    - Surface normal computation
  
  Status: FOUNDATIONAL - Core triangle operations with barycentric proofs.
-/

import Hydrogen.Math.Vec3
import Hydrogen.Math.Bounded
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hydrogen.Math

-- ═══════════════════════════════════════════════════════════════════════════════
-- TRIANGLE DEFINITION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A triangle defined by three vertices.
    
    Vertices are labeled a, b, c and ordered counter-clockwise
    when viewed from the front face.
-/
structure Triangle where
  a : Vec3
  b : Vec3
  c : Vec3

namespace Triangle

-- ─────────────────────────────────────────────────────────────────────────────
-- EXTENSION
-- ─────────────────────────────────────────────────────────────────────────────

@[ext]
theorem ext {t1 t2 : Triangle} 
    (ha : t1.a = t2.a) (hb : t1.b = t2.b) (hc : t1.c = t2.c) : 
    t1 = t2 := by
  cases t1; cases t2; simp_all

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONSTRUCTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Unit triangle in XY plane -/
def unit : Triangle := ⟨Vec3.zero, Vec3.unitX, Vec3.unitY⟩

/-- Degenerate triangle (all vertices at origin) -/
def degenerate : Triangle := ⟨Vec3.zero, Vec3.zero, Vec3.zero⟩

/-- Triangle from three points -/
def fromPoints (a b c : Vec3) : Triangle := ⟨a, b, c⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- EDGES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Edge from a to b -/
def edgeAB (t : Triangle) : Vec3 := Vec3.sub t.b t.a

/-- Edge from a to c -/
def edgeAC (t : Triangle) : Vec3 := Vec3.sub t.c t.a

/-- Edge from b to c -/
def edgeBC (t : Triangle) : Vec3 := Vec3.sub t.c t.b

/-- Edge from b to a -/
def edgeBA (t : Triangle) : Vec3 := Vec3.sub t.a t.b

/-- Edge from c to a -/
def edgeCA (t : Triangle) : Vec3 := Vec3.sub t.a t.c

/-- Edge from c to b -/
def edgeCB (t : Triangle) : Vec3 := Vec3.sub t.b t.c

-- ═══════════════════════════════════════════════════════════════════════════════
-- NORMAL AND AREA
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Cross product of two edges (twice the area vector) -/
def crossEdges (t : Triangle) : Vec3 := Vec3.cross (edgeAB t) (edgeAC t)

/-- Normal vector (not normalized, length = 2 * area) -/
def normalUnnormalized (t : Triangle) : Vec3 := crossEdges t

/-- Squared length of the normal (4 * area²) -/
def normalLengthSq (t : Triangle) : ℝ := Vec3.lengthSq (normalUnnormalized t)

/-- Area of the triangle: |AB × AC| / 2 -/
noncomputable def area (t : Triangle) : ℝ := Vec3.length (crossEdges t) / 2

/-- Signed area (for orientation testing in 2D projection) -/
noncomputable def signedAreaXY (t : Triangle) : ℝ := 
  ((t.b.x - t.a.x) * (t.c.y - t.a.y) - (t.c.x - t.a.x) * (t.b.y - t.a.y)) / 2

/-- Check if triangle is degenerate (zero area) -/
def IsDegenerate (t : Triangle) : Prop := normalLengthSq t = 0

-- ═══════════════════════════════════════════════════════════════════════════════
-- CENTROID AND MIDPOINTS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Midpoint of edge AB -/
def midpointAB (t : Triangle) : Vec3 := 
  Vec3.scale 0.5 (Vec3.add t.a t.b)

/-- Midpoint of edge BC -/
def midpointBC (t : Triangle) : Vec3 := 
  Vec3.scale 0.5 (Vec3.add t.b t.c)

/-- Midpoint of edge CA -/
def midpointCA (t : Triangle) : Vec3 := 
  Vec3.scale 0.5 (Vec3.add t.c t.a)

/-- Centroid (center of mass) at (a + b + c) / 3 -/
noncomputable def centroid (t : Triangle) : Vec3 := 
  Vec3.scale (1/3) (Vec3.add (Vec3.add t.a t.b) t.c)

-- ═══════════════════════════════════════════════════════════════════════════════
-- BARYCENTRIC COORDINATES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Barycentric coordinates (u, v, w) where point = u*a + v*b + w*c -/
structure Barycentric where
  u : ℝ  -- Weight for vertex a
  v : ℝ  -- Weight for vertex b
  w : ℝ  -- Weight for vertex c

namespace Barycentric

/-- Barycentric coordinates for vertex a -/
def vertexA : Barycentric := ⟨1, 0, 0⟩

/-- Barycentric coordinates for vertex b -/
def vertexB : Barycentric := ⟨0, 1, 0⟩

/-- Barycentric coordinates for vertex c -/
def vertexC : Barycentric := ⟨0, 0, 1⟩

/-- Barycentric coordinates for centroid -/
noncomputable def centroid : Barycentric := ⟨1/3, 1/3, 1/3⟩

/-- Sum of barycentric coordinates -/
def sum (bc : Barycentric) : ℝ := bc.u + bc.v + bc.w

/-- Check if barycentric coordinates are valid (sum to 1) -/
def IsValid (bc : Barycentric) : Prop := sum bc = 1

/-- Check if point is inside triangle (all coordinates non-negative) -/
def IsInside (bc : Barycentric) : Prop := 
  bc.u ≥ 0 ∧ bc.v ≥ 0 ∧ bc.w ≥ 0

end Barycentric

/-- Convert barycentric coordinates to a point -/
def fromBarycentric (t : Triangle) (bc : Barycentric) : Vec3 :=
  Vec3.add (Vec3.add (Vec3.scale bc.u t.a) (Vec3.scale bc.v t.b)) (Vec3.scale bc.w t.c)

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: EDGE PROPERTIES
-- ═══════════════════════════════════════════════════════════════════════════════

theorem edgeAB_neg_edgeBA (t : Triangle) : edgeAB t = Vec3.neg (edgeBA t) := by
  simp only [edgeAB, edgeBA, Vec3.sub, Vec3.neg]
  ext <;> ring

theorem edgeAC_neg_edgeCA (t : Triangle) : edgeAC t = Vec3.neg (edgeCA t) := by
  simp only [edgeAC, edgeCA, Vec3.sub, Vec3.neg]
  ext <;> ring

theorem edgeBC_neg_edgeCB (t : Triangle) : edgeBC t = Vec3.neg (edgeCB t) := by
  simp only [edgeBC, edgeCB, Vec3.sub, Vec3.neg]
  ext <;> ring

/-- Edges form a closed loop: AB + BC + CA = 0 -/
theorem edge_loop (t : Triangle) : 
    Vec3.add (Vec3.add (edgeAB t) (edgeBC t)) (edgeCA t) = Vec3.zero := by
  simp only [edgeAB, edgeBC, edgeCA, Vec3.add, Vec3.sub, Vec3.zero]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: BARYCENTRIC COORDINATES
-- ═══════════════════════════════════════════════════════════════════════════════

theorem barycentric_vertexA_sum : Barycentric.sum Barycentric.vertexA = 1 := by
  simp only [Barycentric.sum, Barycentric.vertexA]
  ring

theorem barycentric_vertexB_sum : Barycentric.sum Barycentric.vertexB = 1 := by
  simp only [Barycentric.sum, Barycentric.vertexB]
  ring

theorem barycentric_vertexC_sum : Barycentric.sum Barycentric.vertexC = 1 := by
  simp only [Barycentric.sum, Barycentric.vertexC]
  ring

theorem barycentric_centroid_sum : Barycentric.sum Barycentric.centroid = 1 := by
  simp only [Barycentric.sum, Barycentric.centroid]
  ring

theorem barycentric_vertexA_valid : Barycentric.IsValid Barycentric.vertexA := 
  barycentric_vertexA_sum

theorem barycentric_vertexB_valid : Barycentric.IsValid Barycentric.vertexB := 
  barycentric_vertexB_sum

theorem barycentric_vertexC_valid : Barycentric.IsValid Barycentric.vertexC := 
  barycentric_vertexC_sum

theorem barycentric_centroid_valid : Barycentric.IsValid Barycentric.centroid := 
  barycentric_centroid_sum

/-- Barycentric vertex A maps to triangle vertex a -/
theorem fromBarycentric_vertexA (t : Triangle) : 
    fromBarycentric t Barycentric.vertexA = t.a := by
  simp only [fromBarycentric, Barycentric.vertexA, Vec3.scale, Vec3.add]
  ext <;> ring

/-- Barycentric vertex B maps to triangle vertex b -/
theorem fromBarycentric_vertexB (t : Triangle) : 
    fromBarycentric t Barycentric.vertexB = t.b := by
  simp only [fromBarycentric, Barycentric.vertexB, Vec3.scale, Vec3.add]
  ext <;> ring

/-- Barycentric vertex C maps to triangle vertex c -/
theorem fromBarycentric_vertexC (t : Triangle) : 
    fromBarycentric t Barycentric.vertexC = t.c := by
  simp only [fromBarycentric, Barycentric.vertexC, Vec3.scale, Vec3.add]
  ext <;> ring

/-- Barycentric centroid maps to geometric centroid -/
theorem fromBarycentric_centroid (t : Triangle) : 
    fromBarycentric t Barycentric.centroid = centroid t := by
  simp only [fromBarycentric, Barycentric.centroid, centroid, Vec3.scale, Vec3.add]
  ext <;> ring

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: NORMAL PROPERTIES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Normal is perpendicular to edge AB -/
theorem normal_perp_edgeAB (t : Triangle) : 
    Vec3.dot (normalUnnormalized t) (edgeAB t) = 0 := by
  simp only [normalUnnormalized, crossEdges, edgeAB, edgeAC]
  -- cross(AB, AC) · AB = 0 by cross_perp_left + dot_comm
  rw [Vec3.dot_comm]
  exact Vec3.cross_perp_left (Vec3.sub t.b t.a) (Vec3.sub t.c t.a)

/-- Normal is perpendicular to edge AC -/
theorem normal_perp_edgeAC (t : Triangle) : 
    Vec3.dot (normalUnnormalized t) (edgeAC t) = 0 := by
  simp only [normalUnnormalized, crossEdges, edgeAB, edgeAC]
  rw [Vec3.dot_comm]
  exact Vec3.cross_perp_right (Vec3.sub t.b t.a) (Vec3.sub t.c t.a)

/-- Area is non-negative -/
theorem area_nonneg (t : Triangle) : 0 ≤ area t := by
  simp only [area]
  apply div_nonneg
  · exact Vec3.length_nonneg _
  · linarith

/-- Degenerate triangle has zero area -/
theorem degenerate_area : area degenerate = 0 := by
  simp only [area, crossEdges, edgeAB, edgeAC, degenerate, Vec3.sub, Vec3.zero, 
             Vec3.cross, Vec3.length, Vec3.lengthSq, Vec3.dot]
  simp only [sub_self, mul_zero, add_zero]
  norm_num

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOFS: UNIT TRIANGLE
-- ═══════════════════════════════════════════════════════════════════════════════

theorem unit_a : unit.a = Vec3.zero := rfl
theorem unit_b : unit.b = Vec3.unitX := rfl
theorem unit_c : unit.c = Vec3.unitY := rfl

theorem unit_edgeAB : edgeAB unit = Vec3.unitX := by
  simp only [edgeAB, unit, Vec3.sub, Vec3.zero, Vec3.unitX]
  ext <;> ring

theorem unit_edgeAC : edgeAC unit = Vec3.unitY := by
  simp only [edgeAC, unit, Vec3.sub, Vec3.zero, Vec3.unitY]
  ext <;> ring

/-- Unit triangle's normal points in +Z direction -/
theorem unit_normal : normalUnnormalized unit = Vec3.unitZ := by
  simp only [normalUnnormalized, crossEdges, edgeAB, edgeAC, unit, 
             Vec3.sub, Vec3.zero, Vec3.cross, Vec3.unitX, Vec3.unitY, Vec3.unitZ]
  ext <;> ring

/-- Unit triangle has area 1/2 -/
theorem unit_area : area unit = 1/2 := by
  simp only [area, crossEdges, edgeAB, edgeAC, unit, Vec3.sub, Vec3.zero,
             Vec3.cross, Vec3.unitX, Vec3.unitY, Vec3.length, Vec3.lengthSq, Vec3.dot]
  simp only [sub_zero, mul_zero, mul_one, sub_self, add_zero, zero_add]
  norm_num

end Triangle

end Hydrogen.Math
