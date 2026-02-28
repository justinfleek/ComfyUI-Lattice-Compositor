-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // spatial // bounds // aabb
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AABB - Axis-Aligned Bounding Box.
-- |
-- | The simplest 3D bounding volume. Defined by min/max corners.
-- | Used for:
-- | - Spatial partitioning (octrees, BVH)
-- | - Broad-phase collision
-- | - Frustum culling
-- | - Ray intersection tests

module Hydrogen.Schema.Spatial.Bounds.AABB
  ( -- * AABB
    AABB
  , aabb
  , aabbFromPoints
  , aabbMin
  , aabbMax
  , aabbCenter
  , aabbSize
  , aabbHalfSize
  , showAABB
  , sameAABB
  
  -- * Operations
  , containsPoint
  , containsAABB
  , intersectsAABB
  , expandToInclude
  , merge
  , intersection
  , negate
  
  -- * Transformations
  , translate
  , scale
  , expand
  
  -- * Queries
  , surfaceArea
  , volume
  , Axis(..)
  , longestAxis
  , shortestAxis
  , isDegenerate
  , isLargerVolume
  , isLargerSurfaceArea
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (&&)
  , (||)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , max
  , min
  )
import Prelude (negate) as P

import Data.Maybe (Maybe(..))
import Data.Array (head) as Array
import Data.Foldable (foldl)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // aabb
-- ═════════════════════════════════════════════════════════════════════════════

-- | AABB - axis-aligned bounding box defined by min/max corners.
type AABB =
  { minX :: Number
  , minY :: Number
  , minZ :: Number
  , maxX :: Number
  , maxY :: Number
  , maxZ :: Number
  }

-- | Construct an AABB from min/max corners.
aabb :: Number -> Number -> Number -> Number -> Number -> Number -> AABB
aabb x1 y1 z1 x2 y2 z2 =
  { minX: min x1 x2
  , minY: min y1 y2
  , minZ: min z1 z2
  , maxX: max x1 x2
  , maxY: max y1 y2
  , maxZ: max z1 z2
  }

-- | Construct AABB from array of points.
aabbFromPoints :: Array { x :: Number, y :: Number, z :: Number } -> Maybe AABB
aabbFromPoints [] = Nothing
aabbFromPoints points = Just (foldPoints points)

foldPoints :: Array { x :: Number, y :: Number, z :: Number } -> AABB
foldPoints points = foldl updateBounds initBounds points
  where
    initBounds = case Array.head points of
      Nothing -> aabb 0.0 0.0 0.0 0.0 0.0 0.0
      Just p -> aabb p.x p.y p.z p.x p.y p.z
    
    updateBounds box p =
      { minX: min box.minX p.x
      , minY: min box.minY p.y
      , minZ: min box.minZ p.z
      , maxX: max box.maxX p.x
      , maxY: max box.maxY p.y
      , maxZ: max box.maxZ p.z
      }

-- | Get min corner.
aabbMin :: AABB -> { x :: Number, y :: Number, z :: Number }
aabbMin b = { x: b.minX, y: b.minY, z: b.minZ }

-- | Get max corner.
aabbMax :: AABB -> { x :: Number, y :: Number, z :: Number }
aabbMax b = { x: b.maxX, y: b.maxY, z: b.maxZ }

-- | Get center point.
aabbCenter :: AABB -> { x :: Number, y :: Number, z :: Number }
aabbCenter b =
  { x: (b.minX + b.maxX) / 2.0
  , y: (b.minY + b.maxY) / 2.0
  , z: (b.minZ + b.maxZ) / 2.0
  }

-- | Get full size (width, height, depth).
aabbSize :: AABB -> { width :: Number, height :: Number, depth :: Number }
aabbSize b =
  { width: b.maxX - b.minX
  , height: b.maxY - b.minY
  , depth: b.maxZ - b.minZ
  }

-- | Get half-size (extents).
aabbHalfSize :: AABB -> { x :: Number, y :: Number, z :: Number }
aabbHalfSize b =
  { x: (b.maxX - b.minX) / 2.0
  , y: (b.maxY - b.minY) / 2.0
  , z: (b.maxZ - b.minZ) / 2.0
  }

-- | Show AABB for debug output.
showAABB :: AABB -> String
showAABB b =
  "(AABB min=(" <> show b.minX <> ", " <> show b.minY <> ", " <> show b.minZ <>
  ") max=(" <> show b.maxX <> ", " <> show b.maxY <> ", " <> show b.maxZ <> "))"

-- | Check if two AABBs are exactly equal.
sameAABB :: AABB -> AABB -> Boolean
sameAABB a b =
  a.minX == b.minX && a.minY == b.minY && a.minZ == b.minZ &&
  a.maxX == b.maxX && a.maxY == b.maxY && a.maxZ == b.maxZ

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if AABB contains point.
containsPoint :: AABB -> Number -> Number -> Number -> Boolean
containsPoint b px py pz =
  px >= b.minX && px <= b.maxX &&
  py >= b.minY && py <= b.maxY &&
  pz >= b.minZ && pz <= b.maxZ

-- | Check if AABB fully contains another AABB.
containsAABB :: AABB -> AABB -> Boolean
containsAABB outer inner =
  inner.minX >= outer.minX && inner.maxX <= outer.maxX &&
  inner.minY >= outer.minY && inner.maxY <= outer.maxY &&
  inner.minZ >= outer.minZ && inner.maxZ <= outer.maxZ

-- | Check if two AABBs intersect.
intersectsAABB :: AABB -> AABB -> Boolean
intersectsAABB a b =
  a.minX <= b.maxX && a.maxX >= b.minX &&
  a.minY <= b.maxY && a.maxY >= b.minY &&
  a.minZ <= b.maxZ && a.maxZ >= b.minZ

-- | Expand AABB to include a point.
expandToInclude :: AABB -> Number -> Number -> Number -> AABB
expandToInclude b px py pz =
  { minX: min b.minX px
  , minY: min b.minY py
  , minZ: min b.minZ pz
  , maxX: max b.maxX px
  , maxY: max b.maxY py
  , maxZ: max b.maxZ pz
  }

-- | Merge two AABBs.
merge :: AABB -> AABB -> AABB
merge a b =
  { minX: min a.minX b.minX
  , minY: min a.minY b.minY
  , minZ: min a.minZ b.minZ
  , maxX: max a.maxX b.maxX
  , maxY: max a.maxY b.maxY
  , maxZ: max a.maxZ b.maxZ
  }

-- | Get intersection of two AABBs (Nothing if they don't intersect).
intersection :: AABB -> AABB -> Maybe AABB
intersection a b =
  if intersectsAABB a b
  then Just
    { minX: max a.minX b.minX
    , minY: max a.minY b.minY
    , minZ: max a.minZ b.minZ
    , maxX: min a.maxX b.maxX
    , maxY: min a.maxY b.maxY
    , maxZ: min a.maxZ b.maxZ
    }
  else Nothing

-- | Negate AABB (flip through origin).
-- | Creates mirror image across all axes.
negate :: AABB -> AABB
negate b =
  { minX: P.negate b.maxX
  , minY: P.negate b.maxY
  , minZ: P.negate b.maxZ
  , maxX: P.negate b.minX
  , maxY: P.negate b.minY
  , maxZ: P.negate b.minZ
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transformations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translate AABB by offset.
translate :: Number -> Number -> Number -> AABB -> AABB
translate dx dy dz b =
  { minX: b.minX + dx
  , minY: b.minY + dy
  , minZ: b.minZ + dz
  , maxX: b.maxX + dx
  , maxY: b.maxY + dy
  , maxZ: b.maxZ + dz
  }

-- | Scale AABB from center.
scale :: Number -> Number -> Number -> AABB -> AABB
scale sx sy sz b =
  let cx = (b.minX + b.maxX) / 2.0
      cy = (b.minY + b.maxY) / 2.0
      cz = (b.minZ + b.maxZ) / 2.0
      hx = (b.maxX - b.minX) / 2.0 * sx
      hy = (b.maxY - b.minY) / 2.0 * sy
      hz = (b.maxZ - b.minZ) / 2.0 * sz
  in { minX: cx - hx
     , minY: cy - hy
     , minZ: cz - hz
     , maxX: cx + hx
     , maxY: cy + hy
     , maxZ: cz + hz
     }

-- | Expand AABB uniformly by amount.
expand :: Number -> AABB -> AABB
expand amount b =
  { minX: b.minX - amount
  , minY: b.minY - amount
  , minZ: b.minZ - amount
  , maxX: b.maxX + amount
  , maxY: b.maxY + amount
  , maxZ: b.maxZ + amount
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate surface area.
surfaceArea :: AABB -> Number
surfaceArea b =
  let w = b.maxX - b.minX
      h = b.maxY - b.minY
      d = b.maxZ - b.minZ
  in 2.0 * (w * h + h * d + w * d)

-- | Calculate volume.
volume :: AABB -> Number
volume b =
  (b.maxX - b.minX) * (b.maxY - b.minY) * (b.maxZ - b.minZ)

-- | Axis enumeration.
data Axis = AxisX | AxisY | AxisZ

derive instance eqAxis :: Eq Axis
derive instance ordAxis :: Ord Axis

instance showAxis :: Show Axis where
  show AxisX = "X"
  show AxisY = "Y"
  show AxisZ = "Z"

-- | Get longest axis.
longestAxis :: AABB -> Axis
longestAxis b =
  let w = b.maxX - b.minX
      h = b.maxY - b.minY
      d = b.maxZ - b.minZ
  in if w >= h && w >= d then AxisX
     else if h >= d then AxisY
     else AxisZ

-- | Get shortest axis.
shortestAxis :: AABB -> Axis
shortestAxis b =
  let w = b.maxX - b.minX
      h = b.maxY - b.minY
      d = b.maxZ - b.minZ
  in if w <= h && w <= d then AxisX
     else if h <= d then AxisY
     else AxisZ

-- | Check if AABB has zero volume (degenerate).
isDegenerate :: AABB -> Boolean
isDegenerate b =
  b.minX >= b.maxX || b.minY >= b.maxY || b.minZ >= b.maxZ

-- | Check if first AABB has larger volume than second.
isLargerVolume :: AABB -> AABB -> Boolean
isLargerVolume a b = volume a > volume b

-- | Check if first AABB has larger surface area than second.
isLargerSurfaceArea :: AABB -> AABB -> Boolean
isLargerSurfaceArea a b = surfaceArea a > surfaceArea b
