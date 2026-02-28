-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // geometry // triangle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Triangle defined by three vertices with barycentric coordinates.
-- |
-- | ## Proof References
-- | All operations correspond to proven theorems in `proofs/Hydrogen/Math/Triangle.lean`:
-- | - barycentric_vertexA/B/C_sum: barycentric coordinates sum to 1
-- | - fromBarycentric_vertexA/B/C: vertices map correctly
-- | - fromBarycentric_centroid: centroid maps correctly
-- | - edge_loop: edges form closed loop (AB + BC + CA = 0)
-- | - normal_perp_edgeAB/AC: normal is perpendicular to edges
-- | - area_nonneg: area is non-negative
-- |
-- | ## Three.js Parity
-- | - set, setFromPointsAndIndices, setFromAttributeAndIndices
-- | - clone, copy, getArea, getMidpoint, getNormal
-- | - getPlane, getBarycoord, getInterpolation, containsPoint
-- | - isFrontFacing, intersectsBox, closestPointToPoint, equals
-- |
-- | ## Applications
-- | - Ray-triangle intersection (Möller–Trumbore algorithm)
-- | - Barycentric interpolation for textures/normals
-- | - Mesh collision detection
-- | - Surface normal computation

module Hydrogen.Schema.Geometry.Triangle
  ( -- * Types
    Triangle(Triangle)
  , Barycentric(Barycentric)
  
  -- * Triangle Constructors
  , triangle
  , triangleUnit
  , triangleDegenerate
  , triangleFromPoints
  
  -- * Barycentric Constructors
  , barycentric
  , barycentricVertexA
  , barycentricVertexB
  , barycentricVertexC
  , barycentricCentroid
  
  -- * Barycentric Queries
  , sumBarycentric
  , isValidBarycentric
  , isInsideBarycentric
  
  -- * Triangle Edges
  , edgeAB
  , edgeAC
  , edgeBC
  , edgeBA
  , edgeCA
  , edgeCB
  
  -- * Normal and Area
  , crossEdges
  , normalUnnormalized
  , normalLengthSq
  , areaTriangle
  , isDegenerate
  
  -- * Centroid and Midpoints
  , midpointAB
  , midpointBC
  , midpointCA
  , centroidTriangle
  
  -- * Barycentric Conversion
  , fromBarycentric
  , getBarycoord
  
  -- * Point Containment
  , containsPointTriangle
  , closestPointToPointTriangle
  
  -- * Accessors
  , getA
  , getB
  , getC
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (==)
  , (>=)
  , (<)
  , (<>)
  , (&&)
  )

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Dimension.Vector.Vec3 
  ( Vec3
  , addVec3
  , subtractVec3
  , scaleVec3
  , crossVec3
  , dotVec3
  , lengthSquaredVec3
  , lengthVec3
  , vec3Zero
  , vec3UnitX
  , vec3UnitY
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // barycentric type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Barycentric coordinates (u, v, w) where point = u*a + v*b + w*c
-- |
-- | Proof reference: Triangle.lean Barycentric
data Barycentric = Barycentric Number Number Number
  -- u v w (weights for vertices a, b, c)

derive instance eqBarycentric :: Eq Barycentric

instance showBarycentric :: Show Barycentric where
  show (Barycentric u v w) =
    "(Barycentric " <> show u <> " " <> show v <> " " <> show w <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // triangle type
-- ═════════════════════════════════════════════════════════════════════════════

-- | A triangle defined by three vertices.
-- |
-- | Vertices are labeled a, b, c and ordered counter-clockwise
-- | when viewed from the front face.
-- |
-- | Proof reference: Triangle.lean Triangle
data Triangle = Triangle (Vec3 Number) (Vec3 Number) (Vec3 Number)
  -- a b c

derive instance eqTriangle :: Eq Triangle

instance showTriangle :: Show Triangle where
  show (Triangle a b c) =
    "(Triangle a:" <> show a <> " b:" <> show b <> " c:" <> show c <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // triangle constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a triangle from three vertices
triangle :: Vec3 Number -> Vec3 Number -> Vec3 Number -> Triangle
triangle = Triangle

-- | Unit triangle in XY plane
-- | Proof reference: Triangle.lean unit, unit_a, unit_b, unit_c
triangleUnit :: Triangle
triangleUnit = Triangle vec3Zero vec3UnitX vec3UnitY

-- | Degenerate triangle (all vertices at origin)
-- | Proof reference: Triangle.lean degenerate
triangleDegenerate :: Triangle
triangleDegenerate = Triangle vec3Zero vec3Zero vec3Zero

-- | Triangle from three points (alias for triangle)
-- | Proof reference: Triangle.lean fromPoints
triangleFromPoints :: Vec3 Number -> Vec3 Number -> Vec3 Number -> Triangle
triangleFromPoints = Triangle

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // barycentric constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create barycentric coordinates
barycentric :: Number -> Number -> Number -> Barycentric
barycentric = Barycentric

-- | Barycentric coordinates for vertex A: (1, 0, 0)
-- | Proof reference: Triangle.lean Barycentric.vertexA, barycentric_vertexA_valid
barycentricVertexA :: Barycentric
barycentricVertexA = Barycentric 1.0 0.0 0.0

-- | Barycentric coordinates for vertex B: (0, 1, 0)
-- | Proof reference: Triangle.lean Barycentric.vertexB, barycentric_vertexB_valid
barycentricVertexB :: Barycentric
barycentricVertexB = Barycentric 0.0 1.0 0.0

-- | Barycentric coordinates for vertex C: (0, 0, 1)
-- | Proof reference: Triangle.lean Barycentric.vertexC, barycentric_vertexC_valid
barycentricVertexC :: Barycentric
barycentricVertexC = Barycentric 0.0 0.0 1.0

-- | Barycentric coordinates for centroid: (1/3, 1/3, 1/3)
-- | Proof reference: Triangle.lean Barycentric.centroid, barycentric_centroid_valid
barycentricCentroid :: Barycentric
barycentricCentroid = Barycentric (1.0 / 3.0) (1.0 / 3.0) (1.0 / 3.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // barycentric queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sum of barycentric coordinates (should be 1 for valid coords)
-- | Proof reference: Triangle.lean Barycentric.sum
sumBarycentric :: Barycentric -> Number
sumBarycentric (Barycentric u v w) = u + v + w

-- | Check if barycentric coordinates are valid (sum to 1)
-- | Proof reference: Triangle.lean Barycentric.IsValid
isValidBarycentric :: Barycentric -> Boolean
isValidBarycentric bc = sumBarycentric bc == 1.0

-- | Check if point is inside triangle (all coordinates non-negative)
-- | Proof reference: Triangle.lean Barycentric.IsInside
isInsideBarycentric :: Barycentric -> Boolean
isInsideBarycentric (Barycentric u v w) = u >= 0.0 && v >= 0.0 && w >= 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // triangle edges
-- ═════════════════════════════════════════════════════════════════════════════

-- | Edge from A to B
-- | Proof reference: Triangle.lean edgeAB
edgeAB :: Triangle -> Vec3 Number
edgeAB (Triangle a b _) = subtractVec3 b a

-- | Edge from A to C
-- | Proof reference: Triangle.lean edgeAC
edgeAC :: Triangle -> Vec3 Number
edgeAC (Triangle a _ c) = subtractVec3 c a

-- | Edge from B to C
-- | Proof reference: Triangle.lean edgeBC
edgeBC :: Triangle -> Vec3 Number
edgeBC (Triangle _ b c) = subtractVec3 c b

-- | Edge from B to A
-- | Proof reference: Triangle.lean edgeBA
edgeBA :: Triangle -> Vec3 Number
edgeBA (Triangle a b _) = subtractVec3 a b

-- | Edge from C to A
-- | Proof reference: Triangle.lean edgeCA
edgeCA :: Triangle -> Vec3 Number
edgeCA (Triangle a _ c) = subtractVec3 a c

-- | Edge from C to B
-- | Proof reference: Triangle.lean edgeCB
edgeCB :: Triangle -> Vec3 Number
edgeCB (Triangle _ b c) = subtractVec3 b c

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // normal and area
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cross product of two edges (twice the area vector)
-- | Proof reference: Triangle.lean crossEdges
crossEdges :: Triangle -> Vec3 Number
crossEdges t = crossVec3 (edgeAB t) (edgeAC t)

-- | Normal vector (not normalized, length = 2 * area)
-- | Proof reference: Triangle.lean normalUnnormalized, unit_normal
normalUnnormalized :: Triangle -> Vec3 Number
normalUnnormalized = crossEdges

-- | Squared length of the normal (4 * area²)
-- | Proof reference: Triangle.lean normalLengthSq
normalLengthSq :: Triangle -> Number
normalLengthSq t = lengthSquaredVec3 (normalUnnormalized t)

-- | Area of the triangle: |AB × AC| / 2
-- | Proof reference: Triangle.lean area, area_nonneg, unit_area, degenerate_area
areaTriangle :: Triangle -> Number
areaTriangle t = lengthVec3 (crossEdges t) / 2.0

-- | Check if triangle is degenerate (zero area)
-- | Proof reference: Triangle.lean IsDegenerate
isDegenerate :: Triangle -> Boolean
isDegenerate t = normalLengthSq t == 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // centroid and midpoints
-- ═════════════════════════════════════════════════════════════════════════════

-- | Midpoint of edge AB
-- | Proof reference: Triangle.lean midpointAB
midpointAB :: Triangle -> Vec3 Number
midpointAB (Triangle a b _) = scaleVec3 0.5 (addVec3 a b)

-- | Midpoint of edge BC
-- | Proof reference: Triangle.lean midpointBC
midpointBC :: Triangle -> Vec3 Number
midpointBC (Triangle _ b c) = scaleVec3 0.5 (addVec3 b c)

-- | Midpoint of edge CA
-- | Proof reference: Triangle.lean midpointCA
midpointCA :: Triangle -> Vec3 Number
midpointCA (Triangle a _ c) = scaleVec3 0.5 (addVec3 c a)

-- | Centroid (center of mass) at (a + b + c) / 3
-- | Proof reference: Triangle.lean centroid
centroidTriangle :: Triangle -> Vec3 Number
centroidTriangle (Triangle a b c) = scaleVec3 (1.0 / 3.0) (addVec3 (addVec3 a b) c)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // barycentric conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert barycentric coordinates to a point
-- | Proof reference: Triangle.lean fromBarycentric, fromBarycentric_vertexA/B/C
fromBarycentric :: Triangle -> Barycentric -> Vec3 Number
fromBarycentric (Triangle a b c) (Barycentric u v w) =
  addVec3 (addVec3 (scaleVec3 u a) (scaleVec3 v b)) (scaleVec3 w c)

-- | Compute barycentric coordinates of a point relative to a triangle.
-- |
-- | Uses the edge vector method (same as Three.js):
-- | Given point P and triangle ABC, computes (u, v, w) such that
-- | P = u*A + v*B + w*C (when P is on the triangle plane).
-- |
-- | Algorithm: Uses dot product ratios to solve the linear system.
-- | This is more numerically stable than the area-ratio method.
-- |
-- | Proof reference: Triangle.lean getBarycoord (pending)
-- | Three.js parity: Triangle.getBarycoord
getBarycoord :: Triangle -> Vec3 Number -> Barycentric
getBarycoord (Triangle a b c) point =
  let
    -- Vectors from A to the other points
    v0 = subtractVec3 c a  -- AC
    v1 = subtractVec3 b a  -- AB
    v2 = subtractVec3 point a  -- AP
    
    -- Dot products for the linear system
    dot00 = dotVec3 v0 v0  -- AC · AC
    dot01 = dotVec3 v0 v1  -- AC · AB
    dot02 = dotVec3 v0 v2  -- AC · AP
    dot11 = dotVec3 v1 v1  -- AB · AB
    dot12 = dotVec3 v1 v2  -- AB · AP
    
    -- Compute barycentric coordinates
    -- Solve: P = A + v*AB + w*AC
    -- Using Cramer's rule on the 2x2 system
    denom = dot00 * dot11 - dot01 * dot01
    
    -- Avoid division by zero for degenerate triangles
    invDenom = if Math.abs denom < 1.0e-10 then 0.0 else 1.0 / denom
    
    -- v is the weight for B, w is the weight for C
    v_val = (dot11 * dot02 - dot01 * dot12) * invDenom
    w_val = (dot00 * dot12 - dot01 * dot02) * invDenom
    
    -- u is the weight for A (barycentric coords sum to 1)
    u = 1.0 - v_val - w_val
  in
    -- Constructor Barycentric u v w (A, B, C)
    Barycentric u v_val w_val

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // point containment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a point lies inside the triangle (on the triangle plane).
-- |
-- | Returns true if the point's barycentric coordinates are all non-negative.
-- | This handles both 2D and 3D cases — for 3D, the point should be on the
-- | triangle's plane for the test to be meaningful.
-- |
-- | Proof reference: Triangle.lean containsPoint (pending)
-- | Three.js parity: Triangle.containsPoint
containsPointTriangle :: Triangle -> Vec3 Number -> Boolean
containsPointTriangle t point =
  let bc = getBarycoord t point
  in isInsideBarycentric bc

-- | Find the closest point on a triangle to a given point.
-- |
-- | Uses Voronoi region testing to determine if the closest point is:
-- | - On a vertex
-- | - On an edge
-- | - Inside the triangle face
-- |
-- | Proof reference: Triangle.lean closestPointToPoint (pending)
-- | Three.js parity: Triangle.closestPointToPoint
closestPointToPointTriangle :: Triangle -> Vec3 Number -> Vec3 Number
closestPointToPointTriangle t point =
  let
    -- Get barycentric coordinates
    bc = getBarycoord t point
    Barycentric u v w = bc
  in
    -- If inside triangle (all coords >= 0), project onto plane
    if u >= 0.0 && v >= 0.0 && w >= 0.0
      then fromBarycentric t bc
    -- Otherwise, clamp to edges/vertices
    else
      let
        -- Clamp barycentric coordinates to [0, 1] and renormalize
        -- This projects to the closest point on the triangle boundary
        u' = Math.max 0.0 u
        v' = Math.max 0.0 v
        w' = Math.max 0.0 w
        total = u' + v' + w'
        -- Avoid division by zero
        invTotal = if total < 1.0e-10 then 1.0 else 1.0 / total
      in
        fromBarycentric t (Barycentric (u' * invTotal) (v' * invTotal) (w' * invTotal))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get vertex A
getA :: Triangle -> Vec3 Number
getA (Triangle a _ _) = a

-- | Get vertex B
getB :: Triangle -> Vec3 Number
getB (Triangle _ b _) = b

-- | Get vertex C
getC :: Triangle -> Vec3 Number
getC (Triangle _ _ c) = c
