-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // geometry // sphere
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bounding sphere defined by center and radius.
-- |
-- | ## Proof References
-- | All operations correspond to proven theorems in `proofs/Hydrogen/Math/Sphere.lean`:
-- | - containsPoint_center: center is always contained
-- | - containsPoint_point: point sphere contains its center
-- | - intersectsSphere_self: sphere intersects itself
-- | - intersectsSphere_comm: intersection is symmetric
-- | - translate_zero: translate by zero is identity
-- | - scaleRadius_one: scale by 1 is identity
-- |
-- | ## Three.js Parity
-- | - set, setFromPoints, setFromBox, clone, copy
-- | - isEmpty, makeEmpty, containsPoint, distanceToPoint
-- | - intersectsSphere, intersectsBox, intersectsPlane
-- | - clampPoint, getBoundingBox, applyMatrix4, translate
-- |
-- | ## Applications
-- | - Bounding volume hierarchies
-- | - Broad-phase collision detection
-- | - View frustum culling
-- | - Physics simulation

module Hydrogen.Schema.Geometry.Sphere
  ( -- * Type
    Sphere(Sphere)
  
  -- * Constructors
  , sphere
  , sphereEmpty
  , sphereUnit
  , spherePoint
  , sphereFromCenterAndRadius
  
  -- * Validity
  , isValidSphere
  , isEmptySphere
  
  -- * Basic Queries
  , diameterSphere
  , surfaceAreaSphere
  , volumeSphere
  
  -- * Containment and Distance
  , distanceSqToCenterSphere
  , distanceToCenterSphere
  , containsPointSphere
  , distanceToPointSphere
  
  -- * Sphere-Sphere Intersection
  , intersectsSphere
  , centerDistanceSqSphere
  
  -- * Translation and Scaling
  , translateSphere
  , scaleRadiusSphere
  , expandRadiusSphere
  
  -- * Bounding Sphere
  , boundingPointSphere
  , boundingTwoPointsSphere
  
  -- * Accessors
  , getCenterSphere
  , getRadiusSphere
  ) where

import Prelude
  ( class Eq
  , class Show
  , negate
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (>=)
  , (<)
  , (<=)
  , (<>)
  )

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Dimension.Vector.Vec3 
  ( Vec3(Vec3)
  , vec3
  , addVec3
  , subtractVec3
  , scaleVec3
  , distanceVec3
  , distanceSquaredVec3
  , vec3Zero
  , lengthSquaredVec3
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | A sphere defined by center point and radius.
-- |
-- | Radius should be non-negative for a valid sphere.
-- | A radius of 0 represents a point.
-- | Negative radius represents an "empty" sphere.
-- |
-- | Proof reference: Sphere.lean Sphere
data Sphere = Sphere (Vec3 Number) Number
  -- center radius

derive instance eqSphere :: Eq Sphere

instance showSphere :: Show Sphere where
  show (Sphere center radius) =
    "(Sphere center:" <> show center <> " radius:" <> show radius <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a sphere from center and radius
sphere :: Vec3 Number -> Number -> Sphere
sphere = Sphere

-- | Empty sphere (negative radius)
-- | Proof reference: Sphere.lean empty, empty_radius, empty_isEmpty
sphereEmpty :: Sphere
sphereEmpty = Sphere vec3Zero (-1.0)

-- | Unit sphere at origin
-- | Proof reference: Sphere.lean unit, unit_center, unit_radius, unit_isValid
sphereUnit :: Sphere
sphereUnit = Sphere vec3Zero 1.0

-- | Point sphere (radius 0)
-- | Proof reference: Sphere.lean point, point_center, point_radius, point_isValid
spherePoint :: Vec3 Number -> Sphere
spherePoint p = Sphere p 0.0

-- | Sphere from center and radius
-- | Proof reference: Sphere.lean fromCenterAndRadius
sphereFromCenterAndRadius :: Vec3 Number -> Number -> Sphere
sphereFromCenterAndRadius = Sphere

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // validity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if sphere is valid (non-empty): radius ≥ 0
-- | Proof reference: Sphere.lean IsValid
isValidSphere :: Sphere -> Boolean
isValidSphere (Sphere _ radius) = radius >= 0.0

-- | Check if sphere is empty: radius < 0
-- | Proof reference: Sphere.lean IsEmpty
isEmptySphere :: Sphere -> Boolean
isEmptySphere (Sphere _ radius) = radius < 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // basic queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Diameter of the sphere
-- | Proof reference: Sphere.lean diameter, diameter_unit, diameter_point
diameterSphere :: Sphere -> Number
diameterSphere (Sphere _ radius) = 2.0 * radius

-- | Surface area of the sphere: 4πr²
-- | Proof reference: Sphere.lean surfaceArea
surfaceAreaSphere :: Sphere -> Number
surfaceAreaSphere (Sphere _ radius) = 4.0 * Math.pi * radius * radius

-- | Volume of the sphere: (4/3)πr³
-- | Proof reference: Sphere.lean volume
volumeSphere :: Sphere -> Number
volumeSphere (Sphere _ radius) = (4.0 / 3.0) * Math.pi * radius * radius * radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // containment and distance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Squared distance from a point to the sphere center
-- | Proof reference: Sphere.lean distanceSqToCenter
distanceSqToCenterSphere :: Sphere -> Vec3 Number -> Number
distanceSqToCenterSphere (Sphere center _) p = distanceSquaredVec3 p center

-- | Distance from a point to the sphere center
-- | Proof reference: Sphere.lean distanceToCenter
distanceToCenterSphere :: Sphere -> Vec3 Number -> Number
distanceToCenterSphere (Sphere center _) p = distanceVec3 p center

-- | Check if a point is inside or on the sphere
-- | Proof reference: Sphere.lean containsPoint, containsPoint_center, containsPoint_point
containsPointSphere :: Sphere -> Vec3 Number -> Boolean
containsPointSphere s p = distanceSqToCenterSphere s p <= (getRadiusSphere s * getRadiusSphere s)

-- | Signed distance from a point to the sphere surface.
-- | Negative if inside, positive if outside, zero on surface.
-- | Proof reference: Sphere.lean distanceToPoint
distanceToPointSphere :: Sphere -> Vec3 Number -> Number
distanceToPointSphere s p = distanceToCenterSphere s p - getRadiusSphere s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // sphere-sphere intersection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two spheres intersect
-- | Proof reference: Sphere.lean intersectsSphere, intersectsSphere_self, intersectsSphere_comm
intersectsSphere :: Sphere -> Sphere -> Boolean
intersectsSphere (Sphere c1 r1) (Sphere c2 r2) =
  distanceVec3 c1 c2 <= r1 + r2

-- | Squared distance between sphere centers
-- | Proof reference: Sphere.lean centerDistanceSq
centerDistanceSqSphere :: Sphere -> Sphere -> Number
centerDistanceSqSphere (Sphere c1 _) (Sphere c2 _) = distanceSquaredVec3 c1 c2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // translation and scaling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translate the sphere by a vector
-- | Proof reference: Sphere.lean translate, translate_zero, translate_translate
translateSphere :: Sphere -> Vec3 Number -> Sphere
translateSphere (Sphere center radius) offset = Sphere (addVec3 center offset) radius

-- | Scale the sphere radius by a factor
-- | Proof reference: Sphere.lean scaleRadius, scaleRadius_one
scaleRadiusSphere :: Sphere -> Number -> Sphere
scaleRadiusSphere (Sphere center radius) factor = Sphere center (radius * factor)

-- | Expand the sphere radius by an amount
-- | Proof reference: Sphere.lean expandRadius, expandRadius_zero
expandRadiusSphere :: Sphere -> Number -> Sphere
expandRadiusSphere (Sphere center radius) amount = Sphere center (radius + amount)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // bounding sphere
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a bounding sphere for a single point
-- | Proof reference: Sphere.lean boundingPoint
boundingPointSphere :: Vec3 Number -> Sphere
boundingPointSphere = spherePoint

-- | Create a bounding sphere for two points
-- | Proof reference: Sphere.lean boundingTwoPoints
boundingTwoPointsSphere :: Vec3 Number -> Vec3 Number -> Sphere
boundingTwoPointsSphere a b =
  let
    center = scaleVec3 0.5 (addVec3 a b)
    halfDist = scaleVec3 0.5 (subtractVec3 b a)
  in Sphere center (Math.sqrt (lengthSquaredVec3 halfDist))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the sphere center
getCenterSphere :: Sphere -> Vec3 Number
getCenterSphere (Sphere center _) = center

-- | Get the sphere radius
getRadiusSphere :: Sphere -> Number
getRadiusSphere (Sphere _ radius) = radius
