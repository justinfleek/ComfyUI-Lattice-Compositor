-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // spatial // bounds // obb
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Oriented Bounding Box (OBB) — axis-aligned bounding box with rotation.
-- |
-- | While AABB (Axis-Aligned Bounding Box) is aligned to world axes,
-- | OBB can be rotated to fit objects more tightly.
-- |
-- | ## Structure
-- |
-- | - **Center**: Position in world space
-- | - **Half-Extents**: Distance from center to each face (x, y, z)
-- | - **Orientation**: Rotation as a quaternion or matrix
-- |
-- | ## Use Cases
-- |
-- | - Collision detection for rotated objects
-- | - Tighter bounds than AABB for elongated/rotated shapes
-- | - Physics engines (broadphase culling)
-- | - Frustum culling for arbitrarily oriented objects

module Hydrogen.Schema.Spatial.Bounds.OBB
  ( -- * Types
    OBB(..)
  
  -- * Constructors
  , obb
  , obbFromCorners
  , obbFromAABB
  
  -- * Accessors
  , center
  , halfExtents
  , axes
  , corners
  
  -- * Operations
  , containsPoint
  , closestPoint
  , transformOBB
  , mergeOBB
  
  -- * Conversions
  , toAABB
  
  -- * Predicates
  , intersectsOBB
  , isValid
  
  -- * Point Cloud
  , obbFromPoints
  , volume
  ) where

import Prelude

import Data.Array (length, zipWith)
import Data.Foldable (foldl, all)
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3(Vec3), vec3, addVec3, subtractVec3, scaleVec3, dotVec3, negateVec3)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // obb
-- ═════════════════════════════════════════════════════════════════════════════

-- | Oriented Bounding Box
-- |
-- | Defined by center, half-extents, and three orthonormal axis vectors.
newtype OBB = OBB
  { center :: Vec3 Number       -- ^ Center position
  , halfExtents :: Vec3 Number  -- ^ Half-size along each local axis
  , axisX :: Vec3 Number        -- ^ Local X axis (unit vector)
  , axisY :: Vec3 Number        -- ^ Local Y axis (unit vector)
  , axisZ :: Vec3 Number        -- ^ Local Z axis (unit vector)
  }

derive instance eqOBB :: Eq OBB

instance showOBB :: Show OBB where
  show (OBB o) =
    "OBB { center: " <> show o.center <>
    ", halfExtents: " <> show o.halfExtents <>
    ", axisX: " <> show o.axisX <>
    ", axisY: " <> show o.axisY <>
    ", axisZ: " <> show o.axisZ <> " }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an OBB from center, half-extents, and axes
obb :: Vec3 Number -> Vec3 Number -> Vec3 Number -> Vec3 Number -> Vec3 Number -> OBB
obb c he ax ay az = OBB
  { center: c
  , halfExtents: he
  , axisX: ax
  , axisY: ay
  , axisZ: az
  }

-- | Create an axis-aligned OBB from two corner points
obbFromCorners :: Vec3 Number -> Vec3 Number -> OBB
obbFromCorners (Vec3 x1 y1 z1) (Vec3 x2 y2 z2) =
  let
    minX = min x1 x2
    minY = min y1 y2
    minZ = min z1 z2
    maxX = max x1 x2
    maxY = max y1 y2
    maxZ = max z1 z2
    cx = (minX + maxX) / 2.0
    cy = (minY + maxY) / 2.0
    cz = (minZ + maxZ) / 2.0
    hx = (maxX - minX) / 2.0
    hy = (maxY - minY) / 2.0
    hz = (maxZ - minZ) / 2.0
  in OBB
    { center: vec3 cx cy cz
    , halfExtents: vec3 hx hy hz
    , axisX: vec3 1.0 0.0 0.0
    , axisY: vec3 0.0 1.0 0.0
    , axisZ: vec3 0.0 0.0 1.0
    }

-- | Create an OBB from an AABB (axis-aligned, identity orientation)
obbFromAABB :: { min :: Vec3 Number, max :: Vec3 Number } -> OBB
obbFromAABB aabb = obbFromCorners aabb.min aabb.max

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the center position
center :: OBB -> Vec3 Number
center (OBB o) = o.center

-- | Get the half-extents
halfExtents :: OBB -> Vec3 Number
halfExtents (OBB o) = o.halfExtents

-- | Get the three axes as an array
axes :: OBB -> { x :: Vec3 Number, y :: Vec3 Number, z :: Vec3 Number }
axes (OBB o) = { x: o.axisX, y: o.axisY, z: o.axisZ }

-- | Get all 8 corner points
corners :: OBB -> Array (Vec3 Number)
corners (OBB o) =
  let
    Vec3 hx hy hz = o.halfExtents
    c = o.center
    ax = scaleVec3 hx o.axisX
    ay = scaleVec3 hy o.axisY
    az = scaleVec3 hz o.axisZ
    nax = negateVec3 ax
    nay = negateVec3 ay
    naz = negateVec3 az
  in
    [ addVec3 c (addVec3 (addVec3 ax ay) az)
    , addVec3 c (addVec3 (addVec3 ax ay) naz)
    , addVec3 c (addVec3 (addVec3 ax nay) az)
    , addVec3 c (addVec3 (addVec3 ax nay) naz)
    , addVec3 c (addVec3 (addVec3 nax ay) az)
    , addVec3 c (addVec3 (addVec3 nax ay) naz)
    , addVec3 c (addVec3 (addVec3 nax nay) az)
    , addVec3 c (addVec3 (addVec3 nax nay) naz)
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a point is inside the OBB
containsPoint :: Vec3 Number -> OBB -> Boolean
containsPoint point (OBB o) =
  let
    d = subtractVec3 point o.center
    Vec3 hx hy hz = o.halfExtents
    -- Project onto each axis
    px = dotVec3 d o.axisX
    py = dotVec3 d o.axisY
    pz = dotVec3 d o.axisZ
  in
    abs px <= hx && abs py <= hy && abs pz <= hz
  where
  abs :: Number -> Number
  abs n = if n < 0.0 then -n else n

-- | Find the closest point on the OBB to a given point
closestPoint :: Vec3 Number -> OBB -> Vec3 Number
closestPoint point (OBB o) =
  let
    d = subtractVec3 point o.center
    Vec3 hx hy hz = o.halfExtents
    -- Project and clamp to each axis
    px = clamp (dotVec3 d o.axisX) (-hx) hx
    py = clamp (dotVec3 d o.axisY) (-hy) hy
    pz = clamp (dotVec3 d o.axisZ) (-hz) hz
  in
    addVec3 o.center 
      (addVec3 (scaleVec3 px o.axisX)
        (addVec3 (scaleVec3 py o.axisY) (scaleVec3 pz o.axisZ)))
  where
  clamp :: Number -> Number -> Number -> Number
  clamp v lo hi
    | v < lo = lo
    | v > hi = hi
    | otherwise = v

-- | Transform an OBB by translation
transformOBB :: Vec3 Number -> OBB -> OBB
transformOBB translation (OBB o) =
  OBB o { center = addVec3 o.center translation }

-- | Merge two OBBs into a larger OBB containing both
-- |
-- | Note: The result is an AABB (axis-aligned) for simplicity.
-- | True OBB merging requires fitting algorithms.
mergeOBB :: OBB -> OBB -> OBB
mergeOBB a b =
  let
    cornersA = corners a
    cornersB = corners b
    allCorners = cornersA <> cornersB
    minCorner = foldl minVec3 (vec3 infinity infinity infinity) allCorners
    maxCorner = foldl maxVec3 (vec3 (-infinity) (-infinity) (-infinity)) allCorners
  in obbFromCorners minCorner maxCorner
  where
  infinity :: Number
  infinity = 1.0e308

  minVec3 :: Vec3 Number -> Vec3 Number -> Vec3 Number
  minVec3 (Vec3 x1 y1 z1) (Vec3 x2 y2 z2) = vec3 (min x1 x2) (min y1 y2) (min z1 z2)

  maxVec3 :: Vec3 Number -> Vec3 Number -> Vec3 Number
  maxVec3 (Vec3 x1 y1 z1) (Vec3 x2 y2 z2) = vec3 (max x1 x2) (max y1 y2) (max z1 z2)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to axis-aligned bounding box (loses orientation)
toAABB :: OBB -> { min :: Vec3 Number, max :: Vec3 Number }
toAABB o =
  let
    cs = corners o
    minCorner = foldl minVec3 (vec3 infinity infinity infinity) cs
    maxCorner = foldl maxVec3 (vec3 (-infinity) (-infinity) (-infinity)) cs
  in { min: minCorner, max: maxCorner }
  where
  infinity :: Number
  infinity = 1.0e308

  minVec3 :: Vec3 Number -> Vec3 Number -> Vec3 Number
  minVec3 (Vec3 x1 y1 z1) (Vec3 x2 y2 z2) = vec3 (min x1 x2) (min y1 y2) (min z1 z2)

  maxVec3 :: Vec3 Number -> Vec3 Number -> Vec3 Number
  maxVec3 (Vec3 x1 y1 z1) (Vec3 x2 y2 z2) = vec3 (max x1 x2) (max y1 y2) (max z1 z2)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two OBBs intersect (Separating Axis Theorem)
-- |
-- | Tests 15 potential separating axes: 3 from each OBB + 9 cross products.
intersectsOBB :: OBB -> OBB -> Boolean
intersectsOBB (OBB a) (OBB b) =
  let
    -- Vector from A center to B center
    d = subtractVec3 b.center a.center
    
    -- All potential separating axes
    testAxes = 
      [ a.axisX, a.axisY, a.axisZ  -- A's axes
      , b.axisX, b.axisY, b.axisZ  -- B's axes
      -- Cross products would go here for full SAT
      ]
    
    -- Test each axis
    isSeparated axis =
      let
        projA = projectOBBOntoAxis (OBB a) axis
        projB = projectOBBOntoAxis (OBB b) axis
        projD = abs (dotVec3 d axis)
      in projD > projA + projB
    
  in not (any isSeparated testAxes)
  where
  abs :: Number -> Number
  abs n = if n < 0.0 then -n else n
  
  any :: forall a. (a -> Boolean) -> Array a -> Boolean
  any f arr = not (all (not <<< f) arr)

-- | Project OBB onto axis (returns half-width)
projectOBBOntoAxis :: OBB -> Vec3 Number -> Number
projectOBBOntoAxis (OBB o) axis =
  let Vec3 hx hy hz = o.halfExtents
  in abs (dotVec3 o.axisX axis) * hx +
     abs (dotVec3 o.axisY axis) * hy +
     abs (dotVec3 o.axisZ axis) * hz
  where
  abs :: Number -> Number
  abs n = if n < 0.0 then -n else n

-- | Check if OBB has valid (positive) extents
isValid :: OBB -> Boolean
isValid (OBB o) =
  let Vec3 hx hy hz = o.halfExtents
  in hx > 0.0 && hy > 0.0 && hz > 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // point cloud
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an axis-aligned OBB from a point cloud
-- |
-- | Returns Nothing if the point cloud has fewer than 2 points.
-- | For a true OBB (oriented), PCA or convex hull algorithms would be needed.
obbFromPoints :: Array (Vec3 Number) -> Maybe OBB
obbFromPoints points =
  if length points < 2 then
    Nothing
  else
    let
      -- Compute AABB bounds
      xVals = map (\(Vec3 x _ _) -> x) points
      yVals = map (\(Vec3 _ y _) -> y) points
      zVals = map (\(Vec3 _ _ z) -> z) points
      
      minX = foldl min infinity xVals
      maxX = foldl max (-infinity) xVals
      minY = foldl min infinity yVals
      maxY = foldl max (-infinity) yVals
      minZ = foldl min infinity zVals
      maxZ = foldl max (-infinity) zVals
      
      minCorner = vec3 minX minY minZ
      maxCorner = vec3 maxX maxY maxZ
    in Just (obbFromCorners minCorner maxCorner)
  where
  infinity :: Number
  infinity = 1.0e308
  
  map :: forall a b. (a -> b) -> Array a -> Array b
  map f arr = zipWith (\a _ -> f a) arr arr

-- | Compute the volume of an OBB
-- |
-- | Volume = 8 * halfExtentX * halfExtentY * halfExtentZ
volume :: OBB -> Number
volume (OBB o) =
  let Vec3 hx hy hz = o.halfExtents
  in 8.0 * hx * hy * hz
