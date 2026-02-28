-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // geometry // box3
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Axis-Aligned Bounding Box (AABB) in 3D space.
-- |
-- | ## Proof References
-- | All operations correspond to proven theorems in `proofs/Hydrogen/Math/Box3.lean`:
-- | - containsPoint_min: min corner is contained
-- | - containsPoint_max: max corner is contained
-- | - containsPoint_center: center is contained
-- | - center_fromCenterAndSize: center preserved through constructor
-- | - size_fromCenterAndSize: size preserved through constructor
-- | - translate_zero: translate by zero is identity
-- | - expandByPoint_contains: expanded box contains the point
-- |
-- | ## Three.js Parity
-- | - set, setFromPoints, setFromCenterAndSize
-- | - clone, copy, makeEmpty, isEmpty
-- | - getCenter, getSize, expandByPoint, expandByVector, expandByScalar
-- | - containsPoint, containsBox, intersectsBox
-- | - clampPoint, distanceToPoint, intersect, union
-- |
-- | ## Applications
-- | - Broad-phase collision detection
-- | - Frustum culling
-- | - Spatial partitioning (octrees, BVH)
-- | - Object bounds

module Hydrogen.Schema.Geometry.Box3
  ( -- * Type
    Box3(Box3)
  
  -- * Constructors
  , box3
  , box3Empty
  , box3Unit
  , box3FromHalfExtents
  , box3FromCenterAndSize
  , box3FromPoint
  , box3FromCorners
  
  -- * Validity
  , isValidBox3
  , isEmptyBox3
  
  -- * Basic Queries
  , centerBox3
  , sizeBox3
  , halfExtentsBox3
  , volumeBox3
  , surfaceAreaBox3
  
  -- * Containment
  , containsPointBox3
  , containsBoxBox3
  , intersectsBoxBox3
  
  -- * Expansion
  , expandByPointBox3
  , expandByVectorBox3
  , expandByScalarBox3
  
  -- * Set Operations
  , unionBox3
  , intersectBox3
  
  -- * Clamping and Distance
  , clampPointBox3
  , distanceSqToPointBox3
  , distanceToPointBox3
  
  -- * Translation
  , translateBox3
  
  -- * Transform
  , applyMatrix4Box3
  
  -- * Accessors
  , getMinBox3
  , getMaxBox3
  ) where

import Prelude
  ( class Eq
  , class Show
  , min
  , max
  , show
  , negate
  , (+)
  , (*)
  , (<=)
  , (>=)
  , (>)
  , (<>)
  , (&&)
  , (||)
  )

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Dimension.Vector.Vec3 
  ( Vec3(Vec3)
  , vec3
  , addVec3
  , subtractVec3
  , scaleVec3
  , negateVec3
  , vec3Zero
  , distanceSquaredVec3
  )
import Hydrogen.Schema.Dimension.Matrix.Mat4 (Mat4, mulPointMat4)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Axis-Aligned Bounding Box defined by min and max corners.
-- |
-- | Invariant: For a valid (non-empty) box, min ≤ max componentwise.
-- | An "empty" box has min > max (inverted).
-- |
-- | Proof reference: Box3.lean Box3
data Box3 = Box3 (Vec3 Number) (Vec3 Number)
  -- min max

derive instance eqBox3 :: Eq Box3

instance showBox3 :: Show Box3 where
  show (Box3 minV maxV) =
    "(Box3 min:" <> show minV <> " max:" <> show maxV <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a box from min and max corners
box3 :: Vec3 Number -> Vec3 Number -> Box3
box3 = Box3

-- | Empty box (inverted bounds - any expansion will create valid box)
-- | Proof reference: Box3.lean empty
box3Empty :: Box3
box3Empty = Box3 (vec3 1.0 1.0 1.0) (vec3 (-1.0) (-1.0) (-1.0))

-- | Unit box from origin to (1,1,1)
-- | Proof reference: Box3.lean unit, unit_isValid, unit_min, unit_max
box3Unit :: Box3
box3Unit = Box3 vec3Zero (vec3 1.0 1.0 1.0)

-- | Box centered at origin with given half-extents
-- | Proof reference: Box3.lean fromHalfExtents, center_fromHalfExtents
box3FromHalfExtents :: Vec3 Number -> Box3
box3FromHalfExtents halfExtents = Box3 (negateVec3 halfExtents) halfExtents

-- | Box from center and full size
-- | Proof reference: Box3.lean fromCenterAndSize, center_fromCenterAndSize, size_fromCenterAndSize
box3FromCenterAndSize :: Vec3 Number -> Vec3 Number -> Box3
box3FromCenterAndSize center size =
  let halfSize = scaleVec3 0.5 size
  in Box3 (subtractVec3 center halfSize) (addVec3 center halfSize)

-- | Box containing a single point
-- | Proof reference: Box3.lean fromPoint, containsPoint_fromPoint
box3FromPoint :: Vec3 Number -> Box3
box3FromPoint p = Box3 p p

-- | Box from two arbitrary corners (computes actual min/max)
-- | Proof reference: Box3.lean fromCorners
box3FromCorners :: Vec3 Number -> Vec3 Number -> Box3
box3FromCorners (Vec3 ax ay az) (Vec3 bx by bz) =
  Box3
    (vec3 (min ax bx) (min ay by) (min az bz))
    (vec3 (max ax bx) (max ay by) (max az bz))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // validity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if box is valid (non-empty): min ≤ max componentwise
-- | Proof reference: Box3.lean IsValid
isValidBox3 :: Box3 -> Boolean
isValidBox3 (Box3 (Vec3 minX minY minZ) (Vec3 maxX maxY maxZ)) =
  minX <= maxX && minY <= maxY && minZ <= maxZ

-- | Check if box is empty: any component of min > max
-- | Proof reference: Box3.lean IsEmpty
isEmptyBox3 :: Box3 -> Boolean
isEmptyBox3 (Box3 (Vec3 minX minY minZ) (Vec3 maxX maxY maxZ)) =
  minX > maxX || minY > maxY || minZ > maxZ

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // basic queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Center of the box
-- | Proof reference: Box3.lean center, center_unit, center_fromCenterAndSize
centerBox3 :: Box3 -> Vec3 Number
centerBox3 (Box3 minV maxV) = scaleVec3 0.5 (addVec3 minV maxV)

-- | Size of the box (max - min)
-- | Proof reference: Box3.lean size, size_unit, size_fromCenterAndSize
sizeBox3 :: Box3 -> Vec3 Number
sizeBox3 (Box3 minV maxV) = subtractVec3 maxV minV

-- | Half-extents (half of size)
-- | Proof reference: Box3.lean halfExtents, halfExtents_fromHalfExtents
halfExtentsBox3 :: Box3 -> Vec3 Number
halfExtentsBox3 b = scaleVec3 0.5 (sizeBox3 b)

-- | Volume of the box
-- | Proof reference: Box3.lean volume, volume_unit
volumeBox3 :: Box3 -> Number
volumeBox3 b =
  let Vec3 sx sy sz = sizeBox3 b
  in sx * sy * sz

-- | Surface area of the box
-- | Proof reference: Box3.lean surfaceArea
surfaceAreaBox3 :: Box3 -> Number
surfaceAreaBox3 b =
  let Vec3 sx sy sz = sizeBox3 b
  in 2.0 * (sx * sy + sy * sz + sz * sx)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // containment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a point is inside the box (inclusive)
-- | Proof reference: Box3.lean containsPoint, containsPoint_min, containsPoint_max
containsPointBox3 :: Box3 -> Vec3 Number -> Boolean
containsPointBox3 (Box3 (Vec3 minX minY minZ) (Vec3 maxX maxY maxZ)) (Vec3 px py pz) =
  minX <= px && px <= maxX &&
  minY <= py && py <= maxY &&
  minZ <= pz && pz <= maxZ

-- | Check if this box fully contains another box
-- | Proof reference: Box3.lean containsBox, containsBox_self
containsBoxBox3 :: Box3 -> Box3 -> Boolean
containsBoxBox3 (Box3 (Vec3 oMinX oMinY oMinZ) (Vec3 oMaxX oMaxY oMaxZ))
                (Box3 (Vec3 iMinX iMinY iMinZ) (Vec3 iMaxX iMaxY iMaxZ)) =
  oMinX <= iMinX && iMaxX <= oMaxX &&
  oMinY <= iMinY && iMaxY <= oMaxY &&
  oMinZ <= iMinZ && iMaxZ <= oMaxZ

-- | Check if two boxes intersect
-- | Proof reference: Box3.lean intersectsBox, intersectsBox_comm, intersectsBox_self
intersectsBoxBox3 :: Box3 -> Box3 -> Boolean
intersectsBoxBox3 (Box3 (Vec3 aMinX aMinY aMinZ) (Vec3 aMaxX aMaxY aMaxZ))
                  (Box3 (Vec3 bMinX bMinY bMinZ) (Vec3 bMaxX bMaxY bMaxZ)) =
  aMinX <= bMaxX && aMaxX >= bMinX &&
  aMinY <= bMaxY && aMaxY >= bMinY &&
  aMinZ <= bMaxZ && aMaxZ >= bMinZ

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // expansion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Expand box to include a point
-- | Proof reference: Box3.lean expandByPoint, expandByPoint_contains, expandByPoint_preserves_containment
expandByPointBox3 :: Box3 -> Vec3 Number -> Box3
expandByPointBox3 (Box3 (Vec3 minX minY minZ) (Vec3 maxX maxY maxZ)) (Vec3 px py pz) =
  Box3
    (vec3 (min minX px) (min minY py) (min minZ pz))
    (vec3 (max maxX px) (max maxY py) (max maxZ pz))

-- | Expand box by a vector (adds to max, subtracts from min)
-- | Proof reference: Box3.lean expandByVector, expandByVector_zero
expandByVectorBox3 :: Box3 -> Vec3 Number -> Box3
expandByVectorBox3 (Box3 minV maxV) v =
  Box3 (subtractVec3 minV v) (addVec3 maxV v)

-- | Expand box uniformly by a scalar
-- | Proof reference: Box3.lean expandByScalar, expandByScalar_zero
expandByScalarBox3 :: Box3 -> Number -> Box3
expandByScalarBox3 b s = expandByVectorBox3 b (vec3 s s s)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // set operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Union of two boxes (smallest box containing both)
-- | Proof reference: Box3.lean union
unionBox3 :: Box3 -> Box3 -> Box3
unionBox3 (Box3 (Vec3 aMinX aMinY aMinZ) (Vec3 aMaxX aMaxY aMaxZ))
          (Box3 (Vec3 bMinX bMinY bMinZ) (Vec3 bMaxX bMaxY bMaxZ)) =
  Box3
    (vec3 (min aMinX bMinX) (min aMinY bMinY) (min aMinZ bMinZ))
    (vec3 (max aMaxX bMaxX) (max aMaxY bMaxY) (max aMaxZ bMaxZ))

-- | Intersection of two boxes (may be empty)
-- | Proof reference: Box3.lean intersect
intersectBox3 :: Box3 -> Box3 -> Box3
intersectBox3 (Box3 (Vec3 aMinX aMinY aMinZ) (Vec3 aMaxX aMaxY aMaxZ))
              (Box3 (Vec3 bMinX bMinY bMinZ) (Vec3 bMaxX bMaxY bMaxZ)) =
  Box3
    (vec3 (max aMinX bMinX) (max aMinY bMinY) (max aMinZ bMinZ))
    (vec3 (min aMaxX bMaxX) (min aMaxY bMaxY) (min aMaxZ bMaxZ))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // clamping and distance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a point to lie within the box
-- | Proof reference: Box3.lean clampPoint
clampPointBox3 :: Box3 -> Vec3 Number -> Vec3 Number
clampPointBox3 (Box3 (Vec3 minX minY minZ) (Vec3 maxX maxY maxZ)) (Vec3 px py pz) =
  vec3
    (max minX (min maxX px))
    (max minY (min maxY py))
    (max minZ (min maxZ pz))

-- | Squared distance from a point to the nearest point on the box surface
-- | Proof reference: Box3.lean distanceSqToPoint
distanceSqToPointBox3 :: Box3 -> Vec3 Number -> Number
distanceSqToPointBox3 b p =
  let clamped = clampPointBox3 b p
  in distanceSquaredVec3 p clamped

-- | Distance from a point to the nearest point on the box surface
-- | Proof reference: Box3.lean distanceToPoint
distanceToPointBox3 :: Box3 -> Vec3 Number -> Number
distanceToPointBox3 b p = Math.sqrt (distanceSqToPointBox3 b p)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // translation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translate the box by a vector
-- | Proof reference: Box3.lean translate, translate_zero, translate_translate, size_translate
translateBox3 :: Box3 -> Vec3 Number -> Box3
translateBox3 (Box3 minV maxV) offset =
  Box3 (addVec3 minV offset) (addVec3 maxV offset)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // transform
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transform an AABB by a 4x4 matrix.
-- |
-- | Transforms all 8 corners of the box and computes a new AABB that
-- | contains all transformed corners. This means the result may be larger
-- | than the original box if the transform includes rotation.
-- |
-- | For rotation-only or scale-only transforms, there are more efficient
-- | algorithms, but this general approach works for any affine transform.
-- |
-- | Proof reference: Box3.lean applyMatrix4, applyMatrix4_identity (pending)
-- | Three.js parity: Box3.applyMatrix4
applyMatrix4Box3 :: Box3 -> Mat4 -> Box3
applyMatrix4Box3 (Box3 (Vec3 minX minY minZ) (Vec3 maxX maxY maxZ)) matrix =
  let
    -- Transform all 8 corners
    c0 = mulPointMat4 matrix (vec3 minX minY minZ)  -- min, min, min
    c1 = mulPointMat4 matrix (vec3 minX minY maxZ)  -- min, min, max
    c2 = mulPointMat4 matrix (vec3 minX maxY minZ)  -- min, max, min
    c3 = mulPointMat4 matrix (vec3 minX maxY maxZ)  -- min, max, max
    c4 = mulPointMat4 matrix (vec3 maxX minY minZ)  -- max, min, min
    c5 = mulPointMat4 matrix (vec3 maxX minY maxZ)  -- max, min, max
    c6 = mulPointMat4 matrix (vec3 maxX maxY minZ)  -- max, max, min
    c7 = mulPointMat4 matrix (vec3 maxX maxY maxZ)  -- max, max, max
    
    -- Find the new AABB containing all transformed corners
    -- Start with first corner and expand
    result = expandByPointBox3
              (expandByPointBox3
                (expandByPointBox3
                  (expandByPointBox3
                    (expandByPointBox3
                      (expandByPointBox3
                        (expandByPointBox3 (box3FromPoint c0) c1)
                        c2)
                      c3)
                    c4)
                  c5)
                c6)
              c7
  in result

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the minimum corner
getMinBox3 :: Box3 -> Vec3 Number
getMinBox3 (Box3 minV _) = minV

-- | Get the maximum corner
getMaxBox3 :: Box3 -> Vec3 Number
getMaxBox3 (Box3 _ maxV) = maxV
