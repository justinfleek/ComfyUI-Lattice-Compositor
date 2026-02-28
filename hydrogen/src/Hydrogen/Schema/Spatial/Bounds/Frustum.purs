-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // spatial // bounds // frustum
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Frustum — 6-plane view volume for cameras and lights.
-- |
-- | A frustum is a truncated pyramid defining the visible volume of a camera
-- | or the illuminated volume of a light. Used for:
-- |
-- | - **Frustum Culling**: Skip rendering objects outside camera view
-- | - **Shadow Mapping**: Define light's visible region
-- | - **LOD Selection**: Choose detail level based on distance
-- |
-- | ## Structure
-- |
-- | Six planes define the frustum bounds:
-- | - **Near**: Closest visible distance
-- | - **Far**: Farthest visible distance
-- | - **Left/Right**: Horizontal bounds
-- | - **Top/Bottom**: Vertical bounds
-- |
-- | Each plane is defined by a normal (pointing inward) and distance from origin.

module Hydrogen.Schema.Spatial.Bounds.Frustum
  ( -- * Types
    Plane(..)
  , Frustum(..)
  , FrustumPlane(..)
  
  -- * Plane Constructors
  , plane
  , planeFromPointNormal
  , planeFromPoints
  
  -- * Frustum Constructors
  , frustum
  , frustumPerspective
  , frustumOrthographic
  
  -- * Accessors
  , getPlane
  , nearPlane
  , farPlane
  , allPlanes
  
  -- * Operations
  , distanceToPlane
  , containsPoint
  , containsSphere
  , containsAABB
  , intersectsSphere
  
  -- * Predicates
  , isPointInFront
  , isPointBehind
  
  -- * Transformations
  , translatePlane
  , closestPointOnPlane
  ) where

import Prelude

import Data.Array (all)
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3(Vec3), vec3, dotVec3, crossVec3, subtractVec3, normalizeVec3, lengthVec3, scaleVec3, addVec3)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // plane
-- ═════════════════════════════════════════════════════════════════════════════

-- | A plane in 3D space defined by normal and distance from origin.
-- |
-- | The plane equation is: dot(normal, point) + distance = 0
-- | Points with positive values are "in front" of the plane.
newtype Plane = Plane
  { normal :: Vec3 Number    -- ^ Unit normal (points "outward" from frustum)
  , distance :: Number       -- ^ Distance from origin along normal
  }

derive instance eqPlane :: Eq Plane

instance showPlane :: Show Plane where
  show (Plane p) = "Plane { normal: " <> show p.normal <> ", distance: " <> show p.distance <> " }"

-- | Create a plane from normal and distance
plane :: Vec3 Number -> Number -> Plane
plane n d = Plane { normal: normalizeVec3 n, distance: d }

-- | Create a plane from a point on the plane and normal
planeFromPointNormal :: Vec3 Number -> Vec3 Number -> Plane
planeFromPointNormal point n =
  let normalized = normalizeVec3 n
      d = -(dotVec3 normalized point)
  in Plane { normal: normalized, distance: d }

-- | Create a plane from three points (counter-clockwise winding)
planeFromPoints :: Vec3 Number -> Vec3 Number -> Vec3 Number -> Maybe Plane
planeFromPoints p0 p1 p2 =
  let
    edge1 = subtractVec3 p1 p0
    edge2 = subtractVec3 p2 p0
    n = crossVec3 edge1 edge2
    len = lengthVec3 n
  in if len < 0.0001
     then Nothing
     else Just (planeFromPointNormal p0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // frustum plane
-- ═════════════════════════════════════════════════════════════════════════════

-- | Named frustum planes
data FrustumPlane
  = Near
  | Far
  | Left
  | Right
  | Top
  | Bottom

derive instance eqFrustumPlane :: Eq FrustumPlane
derive instance ordFrustumPlane :: Ord FrustumPlane

instance showFrustumPlane :: Show FrustumPlane where
  show Near = "Near"
  show Far = "Far"
  show Left = "Left"
  show Right = "Right"
  show Top = "Top"
  show Bottom = "Bottom"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // frustum
-- ═════════════════════════════════════════════════════════════════════════════

-- | View frustum defined by 6 planes
-- |
-- | Planes have normals pointing inward (toward the visible region).
newtype Frustum = Frustum
  { near :: Plane
  , far :: Plane
  , left :: Plane
  , right :: Plane
  , top :: Plane
  , bottom :: Plane
  }

derive instance eqFrustum :: Eq Frustum

instance showFrustum :: Show Frustum where
  show (Frustum f) =
    "Frustum { near: " <> show f.near <>
    ", far: " <> show f.far <>
    ", left: " <> show f.left <>
    ", right: " <> show f.right <>
    ", top: " <> show f.top <>
    ", bottom: " <> show f.bottom <> " }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a frustum from 6 explicit planes
frustum :: Plane -> Plane -> Plane -> Plane -> Plane -> Plane -> Frustum
frustum near far left right top bottom = Frustum
  { near, far, left, right, top, bottom }

-- | Create a perspective frustum
-- |
-- | Parameters:
-- | - fovY: Vertical field of view in radians
-- | - aspect: Width / Height ratio
-- | - nearDist: Near clipping distance
-- | - farDist: Far clipping distance
frustumPerspective :: Number -> Number -> Number -> Number -> Frustum
frustumPerspective fovY aspect nearDist farDist =
  let
    -- Half angles
    tanHalfFovY = tan (fovY / 2.0)
    tanHalfFovX = tanHalfFovY * aspect
    
    -- Near plane
    nearP = plane (vec3 0.0 0.0 (-1.0)) nearDist
    
    -- Far plane
    farP = plane (vec3 0.0 0.0 1.0) (-farDist)
    
    -- Side planes (normals point inward)
    -- Left: normal points right
    leftN = normalizeVec3 (vec3 1.0 0.0 tanHalfFovX)
    leftP = Plane { normal: leftN, distance: 0.0 }
    
    -- Right: normal points left
    rightN = normalizeVec3 (vec3 (-1.0) 0.0 tanHalfFovX)
    rightP = Plane { normal: rightN, distance: 0.0 }
    
    -- Top: normal points down
    topN = normalizeVec3 (vec3 0.0 (-1.0) tanHalfFovY)
    topP = Plane { normal: topN, distance: 0.0 }
    
    -- Bottom: normal points up
    bottomN = normalizeVec3 (vec3 0.0 1.0 tanHalfFovY)
    bottomP = Plane { normal: bottomN, distance: 0.0 }
    
  in Frustum
    { near: nearP
    , far: farP
    , left: leftP
    , right: rightP
    , top: topP
    , bottom: bottomP
    }

-- | Create an orthographic frustum
-- |
-- | Parameters:
-- | - width: View width
-- | - height: View height
-- | - nearDist: Near clipping distance
-- | - farDist: Far clipping distance
frustumOrthographic :: Number -> Number -> Number -> Number -> Frustum
frustumOrthographic width height nearDist farDist =
  let
    halfWidth = width / 2.0
    halfHeight = height / 2.0
    
    nearP = plane (vec3 0.0 0.0 (-1.0)) nearDist
    farP = plane (vec3 0.0 0.0 1.0) (-farDist)
    leftP = plane (vec3 1.0 0.0 0.0) halfWidth
    rightP = plane (vec3 (-1.0) 0.0 0.0) halfWidth
    topP = plane (vec3 0.0 (-1.0) 0.0) halfHeight
    bottomP = plane (vec3 0.0 1.0 0.0) halfHeight
    
  in Frustum
    { near: nearP
    , far: farP
    , left: leftP
    , right: rightP
    , top: topP
    , bottom: bottomP
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get a specific plane from the frustum
getPlane :: FrustumPlane -> Frustum -> Plane
getPlane Near (Frustum f) = f.near
getPlane Far (Frustum f) = f.far
getPlane Left (Frustum f) = f.left
getPlane Right (Frustum f) = f.right
getPlane Top (Frustum f) = f.top
getPlane Bottom (Frustum f) = f.bottom

-- | Get the near plane
nearPlane :: Frustum -> Plane
nearPlane = getPlane Near

-- | Get the far plane
farPlane :: Frustum -> Plane
farPlane = getPlane Far

-- | Get all 6 planes as an array
allPlanes :: Frustum -> Array Plane
allPlanes (Frustum f) = [f.near, f.far, f.left, f.right, f.top, f.bottom]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Signed distance from point to plane
-- |
-- | Positive: in front (same side as normal)
-- | Negative: behind (opposite side from normal)
-- | Zero: on the plane
distanceToPlane :: Vec3 Number -> Plane -> Number
distanceToPlane point (Plane p) = dotVec3 p.normal point + p.distance

-- | Check if a point is inside the frustum
containsPoint :: Vec3 Number -> Frustum -> Boolean
containsPoint point fr =
  all (\p -> distanceToPlane point p >= 0.0) (allPlanes fr)

-- | Check if a sphere is completely inside the frustum
containsSphere :: Vec3 Number -> Number -> Frustum -> Boolean
containsSphere center radius fr =
  all (\p -> distanceToPlane center p >= radius) (allPlanes fr)

-- | Check if an AABB is completely inside the frustum
containsAABB :: { min :: Vec3 Number, max :: Vec3 Number } -> Frustum -> Boolean
containsAABB aabb fr =
  let
    Vec3 minX minY minZ = aabb.min
    Vec3 maxX maxY maxZ = aabb.max
    corners =
      [ vec3 minX minY minZ
      , vec3 maxX minY minZ
      , vec3 minX maxY minZ
      , vec3 maxX maxY minZ
      , vec3 minX minY maxZ
      , vec3 maxX minY maxZ
      , vec3 minX maxY maxZ
      , vec3 maxX maxY maxZ
      ]
  in all (\corner -> containsPoint corner fr) corners

-- | Check if a sphere intersects the frustum
-- |
-- | Returns true if any part of the sphere is inside.
intersectsSphere :: Vec3 Number -> Number -> Frustum -> Boolean
intersectsSphere center radius fr =
  all (\p -> distanceToPlane center p >= -radius) (allPlanes fr)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a point is in front of a plane
isPointInFront :: Vec3 Number -> Plane -> Boolean
isPointInFront point p = distanceToPlane point p > 0.0

-- | Check if a point is behind a plane
isPointBehind :: Vec3 Number -> Plane -> Boolean
isPointBehind point p = distanceToPlane point p < 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tangent function for perspective calculations
tan :: Number -> Number
tan x = Math.sin x / Math.cos x

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transformations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translate a plane by a vector
-- |
-- | Moves the plane along the translation vector.
translatePlane :: Vec3 Number -> Plane -> Plane
translatePlane translation (Plane p) =
  let
    -- New distance adjusts by the projection of translation onto normal
    newDistance = p.distance - dotVec3 p.normal translation
  in Plane { normal: p.normal, distance: newDistance }

-- | Find the closest point on a plane to a given point
-- |
-- | Projects the point onto the plane along the normal direction.
closestPointOnPlane :: Vec3 Number -> Plane -> Vec3 Number
closestPointOnPlane point (Plane p) =
  let
    dist = distanceToPlane point (Plane p)
    offset = scaleVec3 (-dist) p.normal
  in addVec3 point offset
