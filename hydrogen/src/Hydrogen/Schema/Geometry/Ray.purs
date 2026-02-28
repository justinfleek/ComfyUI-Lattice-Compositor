-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // geometry // ray
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Ray definition for ray casting and intersection tests.
-- |
-- | ## Proof References
-- | All operations correspond to proven theorems in `proofs/Hydrogen/Math/Ray.lean`:
-- | - pointAt_zero: Ray.pointAt(0) = origin
-- | - pointAt_one: Ray.pointAt(1) = origin + direction
-- | - pointAt_add: pointAt is linear in t
-- | - recast_zero: recast by 0 is identity
-- | - recast_direction: recast preserves direction
-- | - reverse_reverse: reverse is involutive
-- |
-- | ## Three.js Parity
-- | - set, at, lookAt, recast
-- | - closestPointToPoint, distanceToPoint, distanceSqToPoint
-- | - intersectSphere, intersectPlane, intersectBox, intersectTriangle
-- |
-- | ## Applications
-- | - Ray casting for picking/selection
-- | - Collision detection
-- | - Line-of-sight checks
-- | - Physics simulation

module Hydrogen.Schema.Geometry.Ray
  ( -- * Type
    Ray(Ray)
  
  -- * Constructors
  , ray
  , rayDefault
  , rayFromPoints
  
  -- * Basic Operations
  , pointAt
  , lookAtRay
  , recast
  , reverseRay
  
  -- * Closest Point Operations
  , closestPointParameter
  , closestPointToPointOnLine
  , closestPointToPoint
  , distanceToPointOnLine
  , distanceSqToPointOnLine
  , distanceToPoint
  , distanceSqToPoint
  
  -- * Intersection Tests (Parameter)
  , intersectPlaneParameter
  , intersectSphereParameter
  , intersectBoxParameter
  , intersectTriangleParameter
  
  -- * Intersection Tests (Point)
  , intersectPlanePoint
  , intersectSpherePoint
  , intersectBoxPoint
  , intersectTrianglePoint
  
  -- * Accessors
  , getOrigin
  , getDirection
  ) where

import Prelude
  ( class Eq
  , class Show
  , max
  , min
  , show
  , negate
  , not
  , (||)
  , (&&)
  , (+)
  , (-)
  , (*)
  , (/)
  , (==)
  , (<)
  , (>)
  , (>=)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Dimension.Vector.Vec3 
  ( Vec3(Vec3)
  , addVec3
  , subtractVec3
  , scaleVec3
  , negateVec3
  , dotVec3
  , crossVec3
  , distanceVec3
  , distanceSquaredVec3
  , getX3
  , getY3
  , getZ3
  , vec3Zero
  , vec3UnitZ
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | A ray defined by an origin point and a direction vector.
-- |
-- | Parametric form: P(t) = origin + t * direction
-- |
-- | For t ≥ 0, points are "in front" of the origin.
-- | For t < 0, points are "behind" the origin.
-- |
-- | The direction is NOT required to be normalized, matching Three.js behavior.
-- |
-- | Proof reference: Ray.lean Ray
data Ray = Ray (Vec3 Number) (Vec3 Number)
  -- origin direction

derive instance eqRay :: Eq Ray

instance showRay :: Show Ray where
  show (Ray origin direction) =
    "(Ray origin:" <> show origin <> " direction:" <> show direction <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a ray from origin and direction
ray :: Vec3 Number -> Vec3 Number -> Ray
ray = Ray

-- | Default ray: origin at zero, pointing in positive Z direction
-- | Proof reference: Ray.lean default, default_origin, default_direction
rayDefault :: Ray
rayDefault = Ray vec3Zero vec3UnitZ

-- | Create ray from origin to target point
-- | Proof reference: Ray.lean fromPoints, fromPoints_origin, fromPoints_direction
rayFromPoints :: Vec3 Number -> Vec3 Number -> Ray
rayFromPoints origin target = Ray origin (subtractVec3 target origin)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // basic operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get point at parameter t along the ray: P(t) = origin + t * direction
-- | Proof reference: Ray.lean pointAt, pointAt_zero, pointAt_one, pointAt_add
pointAt :: Ray -> Number -> Vec3 Number
pointAt (Ray origin direction) t = addVec3 origin (scaleVec3 t direction)

-- | Point the ray at a target (sets direction toward target)
-- | Proof reference: Ray.lean lookAt, lookAt_origin, lookAt_pointAt_one
lookAtRay :: Ray -> Vec3 Number -> Ray
lookAtRay (Ray origin _) target = Ray origin (subtractVec3 target origin)

-- | Move origin along the ray by parameter t
-- | Proof reference: Ray.lean recast, recast_zero, recast_direction, recast_recast
recast :: Ray -> Number -> Ray
recast r t = Ray (pointAt r t) (getDirection r)

-- | Reverse the ray direction
-- | Proof reference: Ray.lean reverse, reverse_reverse, reverse_origin, reverse_direction
reverseRay :: Ray -> Ray
reverseRay (Ray origin direction) = Ray origin (negateVec3 direction)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // closest point operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parameter t for the closest point on ray to a given point.
-- |
-- | Uses: t = ((point - origin) · direction) / (direction · direction)
-- |
-- | Note: t can be negative (point behind origin).
-- | For rays (vs lines), you may want to clamp t ≥ 0.
-- |
-- | Proof reference: Ray.lean closestPointParameter
closestPointParameter :: Ray -> Vec3 Number -> Number
closestPointParameter (Ray origin direction) point =
  let
    v = subtractVec3 point origin
    dirLenSq = dotVec3 direction direction
  in
    if dirLenSq == 0.0 then 0.0
    else dotVec3 v direction / dirLenSq

-- | Closest point on the infinite line containing the ray to a given point
-- | Proof reference: Ray.lean closestPointToPointOnLine
closestPointToPointOnLine :: Ray -> Vec3 Number -> Vec3 Number
closestPointToPointOnLine r point = pointAt r (closestPointParameter r point)

-- | Closest point on the ray (t ≥ 0) to a given point
-- | Proof reference: Ray.lean closestPointToPoint
closestPointToPoint :: Ray -> Vec3 Number -> Vec3 Number
closestPointToPoint r point =
  let t = closestPointParameter r point
  in pointAt r (max t 0.0)

-- | Distance from a point to the infinite line containing the ray
-- | Proof reference: Ray.lean distanceToPointOnLine
distanceToPointOnLine :: Ray -> Vec3 Number -> Number
distanceToPointOnLine r point = 
  distanceVec3 point (closestPointToPointOnLine r point)

-- | Squared distance from a point to the infinite line containing the ray
-- | Proof reference: Ray.lean distanceSqToPointOnLine
distanceSqToPointOnLine :: Ray -> Vec3 Number -> Number
distanceSqToPointOnLine r point = 
  distanceSquaredVec3 point (closestPointToPointOnLine r point)

-- | Distance from a point to the ray (t ≥ 0)
-- | Proof reference: Ray.lean distanceToPoint
distanceToPoint :: Ray -> Vec3 Number -> Number
distanceToPoint r point = 
  distanceVec3 point (closestPointToPoint r point)

-- | Squared distance from a point to the ray (t ≥ 0)
-- | Proof reference: Ray.lean distanceSqToPoint
distanceSqToPoint :: Ray -> Vec3 Number -> Number
distanceSqToPoint r point = 
  distanceSquaredVec3 point (closestPointToPoint r point)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the ray origin
getOrigin :: Ray -> Vec3 Number
getOrigin (Ray origin _) = origin

-- | Get the ray direction
getDirection :: Ray -> Vec3 Number
getDirection (Ray _ direction) = direction

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // intersection tests
-- ═════════════════════════════════════════════════════════════════════════════

-- | Small epsilon for numerical comparisons
epsilon :: Number
epsilon = 1.0e-10

-- ─────────────────────────────────────────────────────────────────────────────
--                                                               // ray vs plane
-- ─────────────────────────────────────────────────────────────────────────────

-- | Intersect ray with a plane defined by normal and constant.
-- |
-- | Plane equation: normal · P + constant = 0
-- | Ray equation: P(t) = origin + t * direction
-- |
-- | Substituting: normal · (origin + t * direction) + constant = 0
-- | Solving: t = -(normal · origin + constant) / (normal · direction)
-- |
-- | Returns Nothing if:
-- | - Ray is parallel to plane (denominator ≈ 0)
-- | - Intersection is behind ray origin (t < 0)
-- |
-- | Proof reference: Ray.lean intersectPlane (theorem pending)
intersectPlaneParameter :: Ray -> Vec3 Number -> Number -> Maybe Number
intersectPlaneParameter (Ray origin direction) planeNormal planeConstant =
  let
    denominator = dotVec3 planeNormal direction
  in
    if Math.abs denominator < epsilon then
      -- Ray is parallel to plane
      Nothing
    else
      let t = negate (dotVec3 planeNormal origin + planeConstant) / denominator
      in if t >= 0.0 then Just t else Nothing

-- | Intersect ray with plane, returning the intersection point.
intersectPlanePoint :: Ray -> Vec3 Number -> Number -> Maybe (Vec3 Number)
intersectPlanePoint r planeNormal planeConstant =
  case intersectPlaneParameter r planeNormal planeConstant of
    Just t -> Just (pointAt r t)
    Nothing -> Nothing

-- ─────────────────────────────────────────────────────────────────────────────
--                                                              // ray vs sphere
-- ─────────────────────────────────────────────────────────────────────────────

-- | Intersect ray with a sphere defined by center and radius.
-- |
-- | Sphere equation: |P - center|² = radius²
-- | Ray equation: P(t) = origin + t * direction
-- |
-- | Let oc = origin - center
-- | Substituting: |oc + t * direction|² = radius²
-- | Expanding: t²(d·d) + 2t(oc·d) + (oc·oc) - r² = 0
-- |
-- | This is quadratic: at² + bt + c = 0 where:
-- |   a = direction · direction
-- |   b = 2 * (oc · direction)  
-- |   c = (oc · oc) - radius²
-- |
-- | Discriminant: b² - 4ac
-- | - < 0: no intersection
-- | - = 0: ray is tangent (one intersection)
-- | - > 0: ray passes through (two intersections, return nearest with t ≥ 0)
-- |
-- | Proof reference: Ray.lean intersectSphere (theorem: intersectSphere_pointAt_onSphere)
intersectSphereParameter :: Ray -> Vec3 Number -> Number -> Maybe Number
intersectSphereParameter (Ray origin direction) sphereCenter sphereRadius =
  let
    oc = subtractVec3 origin sphereCenter
    a = dotVec3 direction direction
    halfB = dotVec3 oc direction  -- using half-b optimization
    c = dotVec3 oc oc - sphereRadius * sphereRadius
    discriminant = halfB * halfB - a * c
  in
    if discriminant < 0.0 then
      -- No intersection
      Nothing
    else if a < epsilon then
      -- Degenerate ray (zero direction)
      Nothing
    else
      let
        sqrtD = Math.sqrt discriminant
        -- Two solutions: t = (-halfB ± sqrtD) / a
        t1 = (negate halfB - sqrtD) / a  -- near intersection
        t2 = (negate halfB + sqrtD) / a  -- far intersection
      in
        -- Return nearest non-negative t
        if t1 >= 0.0 then Just t1
        else if t2 >= 0.0 then Just t2
        else Nothing

-- | Intersect ray with sphere, returning the intersection point.
intersectSpherePoint :: Ray -> Vec3 Number -> Number -> Maybe (Vec3 Number)
intersectSpherePoint r sphereCenter sphereRadius =
  case intersectSphereParameter r sphereCenter sphereRadius of
    Just t -> Just (pointAt r t)
    Nothing -> Nothing

-- ─────────────────────────────────────────────────────────────────────────────
--                                                                 // ray vs box
-- ─────────────────────────────────────────────────────────────────────────────

-- | Intersect ray with an axis-aligned bounding box (AABB).
-- |
-- | Uses the slab method: for each axis, compute the parameter range [tMin, tMax]
-- | where the ray is inside that axis's slabs. The ray intersects the box if
-- | all three ranges overlap and the final tMax > 0.
-- |
-- | For each axis i:
-- |   t1 = (boxMin[i] - origin[i]) / direction[i]
-- |   t2 = (boxMax[i] - origin[i]) / direction[i]
-- |   tMin = max(tMin, min(t1, t2))
-- |   tMax = min(tMax, max(t1, t2))
-- |
-- | Returns Nothing if:
-- | - Ray misses the box (tMin > tMax)
-- | - Box is entirely behind ray origin (tMax < 0)
-- |
-- | Proof reference: Ray.lean intersectBox (theorem: intersectBox_pointAt_inside)
intersectBoxParameter :: Ray -> Vec3 Number -> Vec3 Number -> Maybe Number
intersectBoxParameter (Ray (Vec3 ox oy oz) (Vec3 dx dy dz)) (Vec3 minX minY minZ) (Vec3 maxX maxY maxZ) =
  let
    -- Compute inverse direction (handle zero components)
    invDx = if Math.abs dx < epsilon then 1.0e30 else 1.0 / dx
    invDy = if Math.abs dy < epsilon then 1.0e30 else 1.0 / dy
    invDz = if Math.abs dz < epsilon then 1.0e30 else 1.0 / dz
    
    -- X slab
    tx1 = (minX - ox) * invDx
    tx2 = (maxX - ox) * invDx
    txMin = min tx1 tx2
    txMax = max tx1 tx2
    
    -- Y slab
    ty1 = (minY - oy) * invDy
    ty2 = (maxY - oy) * invDy
    tyMin = min ty1 ty2
    tyMax = max ty1 ty2
    
    -- Z slab
    tz1 = (minZ - oz) * invDz
    tz2 = (maxZ - oz) * invDz
    tzMin = min tz1 tz2
    tzMax = max tz1 tz2
    
    -- Combine: overall entry and exit
    tEnter = max txMin (max tyMin tzMin)
    tExit = min txMax (min tyMax tzMax)
  in
    if tEnter > tExit || tExit < 0.0 then
      -- Miss or behind
      Nothing
    else if tEnter >= 0.0 then
      -- Ray starts outside box, enters at tEnter
      Just tEnter
    else
      -- Ray starts inside box, exits at tExit
      Just tExit

-- | Intersect ray with AABB, returning the intersection point.
intersectBoxPoint :: Ray -> Vec3 Number -> Vec3 Number -> Maybe (Vec3 Number)
intersectBoxPoint r boxMin boxMax =
  case intersectBoxParameter r boxMin boxMax of
    Just t -> Just (pointAt r t)
    Nothing -> Nothing

-- ─────────────────────────────────────────────────────────────────────────────
--                                                            // ray vs triangle
-- ─────────────────────────────────────────────────────────────────────────────

-- | Intersect ray with a triangle using the Möller–Trumbore algorithm.
-- |
-- | This is THE critical function for raycasting. Called once per triangle
-- | in the raycasting pipeline.
-- |
-- | Given triangle vertices (v0, v1, v2) and ray (origin, direction):
-- |   edge1 = v1 - v0
-- |   edge2 = v2 - v0
-- |   h = direction × edge2
-- |   a = edge1 · h
-- |
-- | If a ≈ 0, ray is parallel to triangle plane.
-- |
-- | Otherwise:
-- |   f = 1/a
-- |   s = origin - v0
-- |   u = f * (s · h)
-- |   
-- | If u < 0 or u > 1, intersection is outside triangle.
-- |
-- |   q = s × edge1
-- |   v = f * (direction · q)
-- |
-- | If v < 0 or u + v > 1, intersection is outside triangle.
-- |
-- |   t = f * (edge2 · q)
-- |
-- | If t < 0, intersection is behind ray origin.
-- |
-- | The parameter `cullBackFace` determines whether to reject back-facing triangles:
-- | - True: only front faces (a > 0) are hit
-- | - False: both front and back faces are hit
-- |
-- | Proof reference: Ray.lean intersectTriangle (theorem: intersectTriangle_pointAt_onTriangle)
intersectTriangleParameter 
  :: Ray 
  -> Vec3 Number  -- v0
  -> Vec3 Number  -- v1
  -> Vec3 Number  -- v2
  -> Boolean      -- cullBackFace
  -> Maybe Number
intersectTriangleParameter (Ray origin direction) v0 v1 v2 cullBackFace =
  let
    edge1 = subtractVec3 v1 v0
    edge2 = subtractVec3 v2 v0
    h = crossVec3 direction edge2
    a = dotVec3 edge1 h
  in
    -- Check if ray is parallel to triangle
    if cullBackFace then
      -- Culling: reject if a < epsilon (back-facing or parallel)
      if a < epsilon then Nothing
      else intersectTriangleCore origin direction v0 edge1 edge2 h a
    else
      -- No culling: reject only if |a| < epsilon (parallel)
      if Math.abs a < epsilon then Nothing
      else intersectTriangleCore origin direction v0 edge1 edge2 h a

-- | Core Möller–Trumbore computation (after parallel check)
intersectTriangleCore 
  :: Vec3 Number  -- origin
  -> Vec3 Number  -- direction
  -> Vec3 Number  -- v0
  -> Vec3 Number  -- edge1
  -> Vec3 Number  -- edge2
  -> Vec3 Number  -- h = direction × edge2
  -> Number       -- a = edge1 · h
  -> Maybe Number
intersectTriangleCore origin direction v0 edge1 edge2 h a =
  let
    f = 1.0 / a
    s = subtractVec3 origin v0
    u = f * dotVec3 s h
  in
    if u < 0.0 || u > 1.0 then
      Nothing
    else
      let
        q = crossVec3 s edge1
        v = f * dotVec3 direction q
      in
        if v < 0.0 || u + v > 1.0 then
          Nothing
        else
          let t = f * dotVec3 edge2 q
          in if t >= 0.0 then Just t else Nothing

-- | Intersect ray with triangle, returning the intersection point.
intersectTrianglePoint 
  :: Ray 
  -> Vec3 Number  -- v0
  -> Vec3 Number  -- v1
  -> Vec3 Number  -- v2
  -> Boolean      -- cullBackFace
  -> Maybe (Vec3 Number)
intersectTrianglePoint r v0 v1 v2 cullBackFace =
  case intersectTriangleParameter r v0 v1 v2 cullBackFace of
    Just t -> Just (pointAt r t)
    Nothing -> Nothing
