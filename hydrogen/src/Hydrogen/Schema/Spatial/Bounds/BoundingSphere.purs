-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // spatial // bounds // sphere
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | BoundingSphere - spherical bounding volume.
-- |
-- | Simple and fast collision primitive. Used for:
-- | - Broad-phase collision detection
-- | - Frustum culling
-- | - Level-of-detail selection
-- | - Point containment queries

module Hydrogen.Schema.Spatial.Bounds.BoundingSphere
  ( -- * Bounding Sphere
    BoundingSphere
  , boundingSphere
  , sphereCenter
  , sphereRadius
  
  -- * Operations
  , containsPoint
  , containsSphere
  , intersectsSphere
  , intersectsAABB
  , expandToInclude
  , merge
  
  -- * Transformations
  , translateSphere
  , scaleSphere
  
  -- * Queries
  , surfaceArea
  , volume
  , diameter
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
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
  , negate
  , max
  , min
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // bounding sphere
-- ═════════════════════════════════════════════════════════════════════════════

-- | BoundingSphere - center point and radius.
type BoundingSphere =
  { centerX :: Number
  , centerY :: Number
  , centerZ :: Number
  , radius :: Number
  }

-- | Construct a bounding sphere.
boundingSphere :: Number -> Number -> Number -> Number -> BoundingSphere
boundingSphere cx cy cz r =
  { centerX: cx
  , centerY: cy
  , centerZ: cz
  , radius: max 0.0 r
  }

-- | Get center point.
sphereCenter :: BoundingSphere -> { x :: Number, y :: Number, z :: Number }
sphereCenter s = { x: s.centerX, y: s.centerY, z: s.centerZ }

-- | Get radius.
sphereRadius :: BoundingSphere -> Number
sphereRadius s = s.radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if sphere contains point.
containsPoint :: BoundingSphere -> Number -> Number -> Number -> Boolean
containsPoint s px py pz =
  let dx = px - s.centerX
      dy = py - s.centerY
      dz = pz - s.centerZ
      distSq = dx * dx + dy * dy + dz * dz
      rSq = s.radius * s.radius
  in distSq <= rSq

-- | Check if sphere fully contains another sphere.
containsSphere :: BoundingSphere -> BoundingSphere -> Boolean
containsSphere outer inner =
  let dx = inner.centerX - outer.centerX
      dy = inner.centerY - outer.centerY
      dz = inner.centerZ - outer.centerZ
      dist = sqrt (dx * dx + dy * dy + dz * dz)
  in dist + inner.radius <= outer.radius

-- | Check if two spheres intersect.
intersectsSphere :: BoundingSphere -> BoundingSphere -> Boolean
intersectsSphere s1 s2 =
  let dx = s2.centerX - s1.centerX
      dy = s2.centerY - s1.centerY
      dz = s2.centerZ - s1.centerZ
      distSq = dx * dx + dy * dy + dz * dz
      radiusSum = s1.radius + s2.radius
      radiusSumSq = radiusSum * radiusSum
  in distSq <= radiusSumSq

-- | Check if sphere intersects an AABB.
intersectsAABB :: BoundingSphere -> { minX :: Number, minY :: Number, minZ :: Number, maxX :: Number, maxY :: Number, maxZ :: Number } -> Boolean
intersectsAABB s box =
  let closestX = max box.minX (min s.centerX box.maxX)
      closestY = max box.minY (min s.centerY box.maxY)
      closestZ = max box.minZ (min s.centerZ box.maxZ)
      dx = closestX - s.centerX
      dy = closestY - s.centerY
      dz = closestZ - s.centerZ
      distSq = dx * dx + dy * dy + dz * dz
      rSq = s.radius * s.radius
  in distSq <= rSq

-- | Expand sphere to include a point.
expandToInclude :: BoundingSphere -> Number -> Number -> Number -> BoundingSphere
expandToInclude s px py pz =
  if containsPoint s px py pz
  then s
  else
    let dx = px - s.centerX
        dy = py - s.centerY
        dz = pz - s.centerZ
        dist = sqrt (dx * dx + dy * dy + dz * dz)
        newRadius = (s.radius + dist) / 2.0
        ratio = (newRadius - s.radius) / dist
        newCx = s.centerX + dx * ratio
        newCy = s.centerY + dy * ratio
        newCz = s.centerZ + dz * ratio
    in boundingSphere newCx newCy newCz newRadius

-- | Merge two spheres into a single enclosing sphere.
merge :: BoundingSphere -> BoundingSphere -> BoundingSphere
merge s1 s2 =
  let dx = s2.centerX - s1.centerX
      dy = s2.centerY - s1.centerY
      dz = s2.centerZ - s1.centerZ
      dist = sqrt (dx * dx + dy * dy + dz * dz)
  in if dist + s2.radius <= s1.radius
     then s1  -- s1 contains s2
     else if dist + s1.radius <= s2.radius
          then s2  -- s2 contains s1
          else
            let newRadius = (dist + s1.radius + s2.radius) / 2.0
                ratio = (newRadius - s1.radius) / dist
                newCx = s1.centerX + dx * ratio
                newCy = s1.centerY + dy * ratio
                newCz = s1.centerZ + dz * ratio
            in boundingSphere newCx newCy newCz newRadius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transformations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translate sphere by offset.
translateSphere :: Number -> Number -> Number -> BoundingSphere -> BoundingSphere
translateSphere dx dy dz s =
  boundingSphere (s.centerX + dx) (s.centerY + dy) (s.centerZ + dz) s.radius

-- | Scale sphere uniformly.
scaleSphere :: Number -> BoundingSphere -> BoundingSphere
scaleSphere factor s =
  let absFactor = if factor < 0.0 then negate factor else factor
  in boundingSphere s.centerX s.centerY s.centerZ (s.radius * absFactor)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate surface area.
surfaceArea :: BoundingSphere -> Number
surfaceArea s = 4.0 * pi * s.radius * s.radius

-- | Calculate volume.
volume :: BoundingSphere -> Number
volume s = (4.0 / 3.0) * pi * s.radius * s.radius * s.radius

-- | Get diameter.
diameter :: BoundingSphere -> Number
diameter s = 2.0 * s.radius

-- | Pi constant.
pi :: Number
pi = 3.141592653589793

-- | Square root (approximation using Newton's method).
sqrt :: Number -> Number
sqrt x
  | x <= 0.0 = 0.0
  | otherwise = sqrtNewton x (x / 2.0) 10

sqrtNewton :: Number -> Number -> Int -> Number
sqrtNewton x guess 0 = guess
sqrtNewton x guess n = sqrtNewton x ((guess + x / guess) / 2.0) (n - 1)
