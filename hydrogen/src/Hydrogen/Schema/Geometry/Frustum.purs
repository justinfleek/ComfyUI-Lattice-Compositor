-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // geometry // frustum
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | View frustum for visibility culling in 3D rendering.
-- |
-- | ## Proof References
-- | All operations correspond to proven theorems in `proofs/Hydrogen/Math/Frustum.lean`:
-- | - containsPoint_iff_all_halfspaces: point inside iff in all 6 halfspaces
-- | - intersectsSphere_iff: sphere intersection definition
-- | - intersectsBox_iff: box intersection definition
-- | - intersectsSphere_of_containsPoint: contained point sphere intersects
-- |
-- | ## Three.js Parity
-- | - set, setFromProjectionMatrix, clone, copy
-- | - containsPoint, intersectsObject, intersectsSprite
-- | - intersectsSphere, intersectsBox
-- |
-- | ## Applications
-- | - View frustum culling for rendering optimization
-- | - Camera visibility queries
-- | - Level-of-detail selection
-- | - Occlusion culling acceleration

module Hydrogen.Schema.Geometry.Frustum
  ( -- * Type
    Frustum(Frustum)
  
  -- * Constructors
  , frustum
  , frustumDefault
  , frustumFromPlanes
  
  -- * Plane Access
  , getLeftPlane
  , getRightPlane
  , getTopPlane
  , getBottomPlane
  , getNearPlane
  , getFarPlane
  , getAllPlanes
  
  -- * Containment
  , inHalfspace
  , containsPointFrustum
  
  -- * Sphere Intersection
  , sphereOutsidePlane
  , intersectsSphereFrustum
  
  -- * Box Intersection
  , boxPositiveVertex
  , boxNegativeVertex
  , boxOutsidePlane
  , intersectsBoxFrustum
  ) where

import Prelude
  ( class Eq
  , class Show
  , negate
  , show
  , (<)
  , (>=)
  , (<>)
  , (&&)
  , not
  )

import Hydrogen.Schema.Dimension.Vector.Vec3 
  ( Vec3(Vec3)
  , vec3
  , negateVec3
  , vec3UnitX
  , vec3UnitY
  , vec3UnitZ
  )

import Hydrogen.Schema.Geometry.Plane
  ( Plane
  , planeFromNormalAndConstant
  , distanceToPointPlane
  , getNormalPlane
  )

import Hydrogen.Schema.Geometry.Box3
  ( Box3
  , getMinBox3
  , getMaxBox3
  )

import Hydrogen.Schema.Geometry.Sphere
  ( Sphere
  , getCenterSphere
  , getRadiusSphere
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | A view frustum defined by six clipping planes.
-- |
-- | The planes are oriented with normals pointing INWARD, so a point is
-- | inside the frustum if it has positive (or zero) signed distance to all planes.
-- |
-- | Proof reference: Frustum.lean Frustum
data Frustum = Frustum Plane Plane Plane Plane Plane Plane
  -- left right top bottom near far

derive instance eqFrustum :: Eq Frustum

instance showFrustum :: Show Frustum where
  show (Frustum left right top bottom near far) =
    "(Frustum left:" <> show left <> 
    " right:" <> show right <>
    " top:" <> show top <>
    " bottom:" <> show bottom <>
    " near:" <> show near <>
    " far:" <> show far <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a frustum from six planes
frustum :: Plane -> Plane -> Plane -> Plane -> Plane -> Plane -> Frustum
frustum = Frustum

-- | Default frustum with standard plane positions
-- | Proof reference: Frustum.lean default
frustumDefault :: Frustum
frustumDefault = Frustum
  (planeFromNormalAndConstant vec3UnitX (negate 1.0))                   -- left
  (planeFromNormalAndConstant (negateVec3 vec3UnitX) (negate 1.0))      -- right
  (planeFromNormalAndConstant (negateVec3 vec3UnitY) (negate 1.0))      -- top
  (planeFromNormalAndConstant vec3UnitY (negate 1.0))                   -- bottom
  (planeFromNormalAndConstant vec3UnitZ (negate 0.1))                   -- near
  (planeFromNormalAndConstant (negateVec3 vec3UnitZ) (negate 1000.0))   -- far

-- | Create frustum from six planes directly
-- | Proof reference: Frustum.lean fromPlanes
frustumFromPlanes :: Plane -> Plane -> Plane -> Plane -> Plane -> Plane -> Frustum
frustumFromPlanes = Frustum

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // plane access
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the left clipping plane
-- | Proof reference: Frustum.lean getPlane_left
getLeftPlane :: Frustum -> Plane
getLeftPlane (Frustum left _ _ _ _ _) = left

-- | Get the right clipping plane
-- | Proof reference: Frustum.lean getPlane_right
getRightPlane :: Frustum -> Plane
getRightPlane (Frustum _ right _ _ _ _) = right

-- | Get the top clipping plane
-- | Proof reference: Frustum.lean getPlane_top
getTopPlane :: Frustum -> Plane
getTopPlane (Frustum _ _ top _ _ _) = top

-- | Get the bottom clipping plane
-- | Proof reference: Frustum.lean getPlane_bottom
getBottomPlane :: Frustum -> Plane
getBottomPlane (Frustum _ _ _ bottom _ _) = bottom

-- | Get the near clipping plane
-- | Proof reference: Frustum.lean getPlane_near
getNearPlane :: Frustum -> Plane
getNearPlane (Frustum _ _ _ _ near _) = near

-- | Get the far clipping plane
-- | Proof reference: Frustum.lean getPlane_far
getFarPlane :: Frustum -> Plane
getFarPlane (Frustum _ _ _ _ _ far) = far

-- | Get all six planes as an array
-- | Proof reference: Frustum.lean planes, planes_length
getAllPlanes :: Frustum -> Array Plane
getAllPlanes (Frustum left right top bottom near far) =
  [left, right, top, bottom, near, far]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // containment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a point is on the positive side of a plane (inside halfspace)
-- | Proof reference: Frustum.lean inHalfspace
inHalfspace :: Plane -> Vec3 Number -> Boolean
inHalfspace plane p = distanceToPointPlane plane p >= 0.0

-- | Check if a point is inside the frustum (in all halfspaces)
-- | Proof reference: Frustum.lean containsPoint, containsPoint_iff_all_halfspaces
containsPointFrustum :: Frustum -> Vec3 Number -> Boolean
containsPointFrustum (Frustum left right top bottom near far) p =
  inHalfspace left p &&
  inHalfspace right p &&
  inHalfspace top p &&
  inHalfspace bottom p &&
  inHalfspace near p &&
  inHalfspace far p

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // sphere intersection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a sphere is completely outside a plane (in negative halfspace)
-- | Proof reference: Frustum.lean sphereOutsidePlane
sphereOutsidePlane :: Plane -> Sphere -> Boolean
sphereOutsidePlane plane s =
  distanceToPointPlane plane (getCenterSphere s) < negate (getRadiusSphere s)

-- | Check if a sphere intersects the frustum.
-- | A sphere intersects if it's NOT completely outside any plane.
-- | Proof reference: Frustum.lean intersectsSphere, intersectsSphere_iff
intersectsSphereFrustum :: Frustum -> Sphere -> Boolean
intersectsSphereFrustum (Frustum left right top bottom near far) s =
  not (sphereOutsidePlane left s) &&
  not (sphereOutsidePlane right s) &&
  not (sphereOutsidePlane top s) &&
  not (sphereOutsidePlane bottom s) &&
  not (sphereOutsidePlane near s) &&
  not (sphereOutsidePlane far s)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // box intersection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the "positive vertex" of a box relative to a plane normal.
-- | This is the box vertex furthest in the direction of the plane normal.
-- | Proof reference: Frustum.lean boxPositiveVertex
boxPositiveVertex :: Box3 -> Vec3 Number -> Vec3 Number
boxPositiveVertex box normal =
  let
    Vec3 minX minY minZ = getMinBox3 box
    Vec3 maxX maxY maxZ = getMaxBox3 box
    Vec3 nx ny nz = normal
  in vec3
    (if nx >= 0.0 then maxX else minX)
    (if ny >= 0.0 then maxY else minY)
    (if nz >= 0.0 then maxZ else minZ)

-- | Get the "negative vertex" of a box relative to a plane normal.
-- | This is the box vertex closest in the direction of the plane normal.
-- | Proof reference: Frustum.lean boxNegativeVertex
boxNegativeVertex :: Box3 -> Vec3 Number -> Vec3 Number
boxNegativeVertex box normal =
  let
    Vec3 minX minY minZ = getMinBox3 box
    Vec3 maxX maxY maxZ = getMaxBox3 box
    Vec3 nx ny nz = normal
  in vec3
    (if nx >= 0.0 then minX else maxX)
    (if ny >= 0.0 then minY else maxY)
    (if nz >= 0.0 then minZ else maxZ)

-- | Check if a box is completely outside a plane.
-- | A box is outside if its positive vertex is in the negative halfspace.
-- | Proof reference: Frustum.lean boxOutsidePlane
boxOutsidePlane :: Plane -> Box3 -> Boolean
boxOutsidePlane plane box =
  distanceToPointPlane plane (boxPositiveVertex box (getNormalPlane plane)) < 0.0

-- | Check if a box intersects the frustum.
-- | A box intersects if it's NOT completely outside any plane.
-- | Proof reference: Frustum.lean intersectsBox, intersectsBox_iff
intersectsBoxFrustum :: Frustum -> Box3 -> Boolean
intersectsBoxFrustum (Frustum left right top bottom near far) box =
  not (boxOutsidePlane left box) &&
  not (boxOutsidePlane right box) &&
  not (boxOutsidePlane top box) &&
  not (boxOutsidePlane bottom box) &&
  not (boxOutsidePlane near box) &&
  not (boxOutsidePlane far box)
