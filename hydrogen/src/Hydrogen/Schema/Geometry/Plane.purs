-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // geometry // plane
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Infinite plane in 3D space, defined by normal vector and constant.
-- |
-- | ## Proof References
-- | All operations correspond to proven theorems in `proofs/Hydrogen/Math/Plane.lean`:
-- | - distanceToPoint_fromNormalAndPoint: point used in constructor lies on plane
-- | - distanceToPoint_fromCoplanarPoints_a/b/c: all three points lie on plane
-- | - negate_negate: negation is involutive
-- | - distanceToPoint_negate: negating flips sign of distance
-- | - translate_zero: translating by zero is identity
-- |
-- | ## Three.js Parity
-- | - set, setFromNormalAndCoplanarPoint, setFromCoplanarPoints
-- | - negate, distanceToPoint, projectPoint, reflectPoint
-- | - coplanarPoint, translate
-- |
-- | ## Applications
-- | - Clipping planes
-- | - Frustum culling (6 planes)
-- | - Collision detection
-- | - Reflection calculations

module Hydrogen.Schema.Geometry.Plane
  ( -- * Type
    Plane(Plane)
  
  -- * Constructors
  , plane
  , planeDefault
  , planeXY
  , planeXZ
  , planeYZ
  , planeFromNormalAndConstant
  , planeFromNormalAndPoint
  , planeFromCoplanarPoints
  
  -- * Basic Operations
  , distanceToPointPlane
  , negatePlane
  , normalizePlane
  , coplanarPointPlane
  , projectPointPlane
  , reflectPointPlane
  , translatePlane
  
  -- * Accessors
  , getNormalPlane
  , getConstantPlane
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
  , (<)
  , (<>)
  )

import Hydrogen.Schema.Dimension.Vector.Vec3 
  ( Vec3
  , subtractVec3
  , scaleVec3
  , negateVec3
  , dotVec3
  , crossVec3
  , lengthVec3
  , vec3UnitX
  , vec3UnitY
  , vec3UnitZ
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | An infinite plane in 3D space.
-- |
-- | Defined by the equation: normal · point + constant = 0
-- |
-- | The normal is NOT required to be normalized, matching Three.js behavior.
-- |
-- | When the normal is a unit vector:
-- | - constant = -distance from origin (signed distance)
-- | - positive constant means origin is on positive side of plane
-- |
-- | Proof reference: Plane.lean Plane
data Plane = Plane (Vec3 Number) Number
  -- normal constant

derive instance eqPlane :: Eq Plane

instance showPlane :: Show Plane where
  show (Plane normal constant) =
    "(Plane normal:" <> show normal <> " constant:" <> show constant <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a plane from normal and constant
plane :: Vec3 Number -> Number -> Plane
plane = Plane

-- | Default plane: XY plane (normal = +Z, passes through origin)
-- | Proof reference: Plane.lean default, default_normal, default_constant
planeDefault :: Plane
planeDefault = Plane vec3UnitZ 0.0

-- | XY plane passing through origin
-- | Proof reference: Plane.lean xy, xy_normal
planeXY :: Plane
planeXY = Plane vec3UnitZ 0.0

-- | XZ plane passing through origin
-- | Proof reference: Plane.lean xz, xz_normal
planeXZ :: Plane
planeXZ = Plane vec3UnitY 0.0

-- | YZ plane passing through origin
-- | Proof reference: Plane.lean yz, yz_normal
planeYZ :: Plane
planeYZ = Plane vec3UnitX 0.0

-- | Create plane from normal and constant
-- | Proof reference: Plane.lean fromNormalAndConstant
planeFromNormalAndConstant :: Vec3 Number -> Number -> Plane
planeFromNormalAndConstant = Plane

-- | Create plane from normal and a point on the plane
-- | Proof reference: Plane.lean fromNormalAndPoint, distanceToPoint_fromNormalAndPoint
planeFromNormalAndPoint :: Vec3 Number -> Vec3 Number -> Plane
planeFromNormalAndPoint normal point = Plane normal (negate (dotVec3 normal point))

-- | Create plane from three coplanar points (counter-clockwise order for outward normal)
-- | Proof reference: Plane.lean fromCoplanarPoints, distanceToPoint_fromCoplanarPoints_a/b/c
planeFromCoplanarPoints :: Vec3 Number -> Vec3 Number -> Vec3 Number -> Plane
planeFromCoplanarPoints a b c =
  let
    ab = subtractVec3 b a
    ac = subtractVec3 c a
    normal = crossVec3 ab ac
  in planeFromNormalAndPoint normal a

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // basic operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Signed distance from a point to the plane.
-- |
-- | For unit normal planes:
-- | - Positive: point is on the positive side (same side as normal)
-- | - Negative: point is on the negative side
-- | - Zero: point is on the plane
-- |
-- | Proof reference: Plane.lean distanceToPoint, distanceToPoint_origin
distanceToPointPlane :: Plane -> Vec3 Number -> Number
distanceToPointPlane (Plane normal constant) point = dotVec3 normal point + constant

-- | Negate the plane (flip normal and constant)
-- | Proof reference: Plane.lean negate, negate_negate, distanceToPoint_negate
negatePlane :: Plane -> Plane
negatePlane (Plane normal constant) = Plane (negateVec3 normal) (negate constant)

-- | Normalize the plane so the normal vector has unit length.
-- |
-- | After normalization:
-- | - The normal has length 1
-- | - The constant equals the signed distance from origin to the plane
-- | - distanceToPointPlane returns the actual Euclidean distance
-- |
-- | If the normal has near-zero length (degenerate plane), returns the
-- | plane unchanged to avoid division by zero.
-- |
-- | Proof reference: Plane.lean normalize, normalize_idempotent (pending)
-- | Three.js parity: Plane.normalize
normalizePlane :: Plane -> Plane
normalizePlane (Plane normal constant) =
  let
    len = lengthVec3 normal
  in
    if len < 1.0e-10
      then Plane normal constant  -- Degenerate plane, return unchanged
      else
        let invLen = 1.0 / len
        in Plane (scaleVec3 invLen normal) (constant * invLen)

-- | Get a point on the plane (closest point to origin for unit normal)
-- | Proof reference: Plane.lean coplanarPoint
coplanarPointPlane :: Plane -> Vec3 Number
coplanarPointPlane (Plane normal constant) = scaleVec3 (negate constant) normal

-- | Project a point onto the plane
-- | Proof reference: Plane.lean projectPoint
projectPointPlane :: Plane -> Vec3 Number -> Vec3 Number
projectPointPlane p point =
  let dist = distanceToPointPlane p point
  in subtractVec3 point (scaleVec3 dist (getNormalPlane p))

-- | Reflect a point across the plane
-- | Proof reference: Plane.lean reflectPoint
reflectPointPlane :: Plane -> Vec3 Number -> Vec3 Number
reflectPointPlane p point =
  let dist = distanceToPointPlane p point
  in subtractVec3 point (scaleVec3 (2.0 * dist) (getNormalPlane p))

-- | Translate the plane by a vector
-- | Proof reference: Plane.lean translate, translate_zero, translate_translate
translatePlane :: Plane -> Vec3 Number -> Plane
translatePlane (Plane normal constant) offset =
  Plane normal (constant - dotVec3 normal offset)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the plane normal
getNormalPlane :: Plane -> Vec3 Number
getNormalPlane (Plane normal _) = normal

-- | Get the plane constant
getConstantPlane :: Plane -> Number
getConstantPlane (Plane _ constant) = constant
