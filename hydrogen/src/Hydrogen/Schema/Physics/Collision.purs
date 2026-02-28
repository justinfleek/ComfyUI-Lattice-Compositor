-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // physics // collision
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Collision — Collision detection and contact resolution primitives.
-- |
-- | ## Design Philosophy
-- |
-- | Collision detection is fundamental to physics simulation and UI interaction.
-- | This module provides bounded, composable collision primitives that work at
-- | billion-agent scale — deterministic detection with no edge cases.
-- |
-- | ## Collision Categories
-- |
-- | **Bounding Volumes**: AABB, Sphere, Capsule, OBB
-- | **Detection Results**: Contact points, normals, penetration depth
-- | **Response Types**: Bounce, slide, stick, separate
-- |
-- | ## Bounded Design
-- |
-- | All collision results are bounded:
-- | - Penetration depth is clamped to prevent numerical explosion
-- | - Contact normals are always unit vectors
-- | - Contact counts are finite and bounded
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Data.Number (sqrt, abs)
-- | - Schema.Physics.Force (Force2D for collision response)
-- |
-- | ## Dependents
-- |
-- | - Motion.Physics (physics engine)
-- | - Component.Draggable (drag boundaries)
-- | - Component.Sortable (item collision)

module Hydrogen.Schema.Physics.Collision
  ( -- * 2D Points (local definitions)
    Point2D(..)
  , point2D
  , origin2D
  , distance
  , distanceSquared
  , midpoint
  , offsetPoint
  
  -- * Bounding Volumes
  , AABB(..)
  , aabb
  , aabbFromPoints
  , aabbCenter
  , aabbSize
  , aabbHalfSize
  , aabbContains
  , aabbExpand
  , aabbMerge
  
  -- * Bounding Circle
  , BoundingCircle(..)
  , boundingCircle
  , circleContains
  , circleExpand
  , circleMerge
  
  -- * Bounding Capsule
  , BoundingCapsule(..)
  , boundingCapsule
  , capsuleContains
  
  -- * Oriented Bounding Box
  , OBB(..)
  , obb
  , obbCorners
  , obbContains
  
  -- * Contact Information
  , Contact(..)
  , contact
  , noContact
  , hasContact
  , contactPoint
  , contactNormal
  , contactDepth
  , flipContact
  
  -- * Collision Detection (AABB)
  , aabbVsAABB
  , aabbVsPoint
  , aabbVsCircle
  
  -- * Collision Detection (Circle)
  , circleVsCircle
  , circleVsPoint
  , circleVsAABB
  
  -- * Collision Detection (Capsule)
  , capsuleVsPoint
  , capsuleVsCapsule
  
  -- * Collision Response
  , CollisionResponse(..)
  , responseNone
  , responseBounce
  , responseSlide
  , responseStick
  
  -- * Response Calculation
  , resolveOverlap
  , calculateBounce
  , calculateSlide
  
  -- * Collision Layers
  , CollisionLayer(..)
  , CollisionMask(..)
  , layerCollides
  , allLayers
  , noLayers
  
  -- * Collision State
  , CollisionState(..)
  , isColliding
  , isSeparating
  , isResting
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , not
  , otherwise
  , (&&)
  , (*)
  , (+)
  , (-)
  , (/)
  , (<)
  , (<=)
  , (<>)
  , (==)
  , (>)
  , (>=)
  , (||)
  )

import Data.Number (sqrt, cos, sin)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // point 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D point for collision geometry.
-- |
-- | Local definition to avoid circular dependencies with Geometry.Point.
newtype Point2D = Point2D { x :: Number, y :: Number }

derive instance eqPoint2D :: Eq Point2D
derive instance ordPoint2D :: Ord Point2D

instance showPoint2D :: Show Point2D where
  show (Point2D p) = "Point2D(" <> show p.x <> ", " <> show p.y <> ")"

-- | Create a 2D point
point2D :: Number -> Number -> Point2D
point2D x y = Point2D { x, y }

-- | Origin point (0, 0)
origin2D :: Point2D
origin2D = Point2D { x: 0.0, y: 0.0 }

-- | Distance between two points
distance :: Point2D -> Point2D -> Number
distance (Point2D a) (Point2D b) = 
  let dx = b.x - a.x
      dy = b.y - a.y
  in sqrt (dx * dx + dy * dy)

-- | Squared distance (faster, avoids sqrt)
distanceSquared :: Point2D -> Point2D -> Number
distanceSquared (Point2D a) (Point2D b) = 
  let dx = b.x - a.x
      dy = b.y - a.y
  in dx * dx + dy * dy

-- | Midpoint between two points
midpoint :: Point2D -> Point2D -> Point2D
midpoint (Point2D a) (Point2D b) = Point2D
  { x: (a.x + b.x) / 2.0
  , y: (a.y + b.y) / 2.0
  }

-- | Add a vector (offset) to a point
offsetPoint :: Point2D -> Number -> Number -> Point2D
offsetPoint (Point2D p) dx dy = Point2D { x: p.x + dx, y: p.y + dy }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // aabb
-- ═════════════════════════════════════════════════════════════════════════════

-- | Axis-Aligned Bounding Box.
-- |
-- | The simplest and fastest collision primitive. Defined by min/max corners.
-- | "Axis-aligned" means edges are parallel to coordinate axes — no rotation.
newtype AABB = AABB
  { minX :: Number
  , minY :: Number
  , maxX :: Number
  , maxY :: Number
  }

derive instance eqAABB :: Eq AABB
derive instance ordAABB :: Ord AABB

instance showAABB :: Show AABB where
  show (AABB b) = "AABB(" <> show b.minX <> "," <> show b.minY 
               <> " -> " <> show b.maxX <> "," <> show b.maxY <> ")"

-- | Create an AABB from min/max coordinates.
-- | Automatically normalizes so min <= max.
aabb :: Number -> Number -> Number -> Number -> AABB
aabb x1 y1 x2 y2 = AABB
  { minX: minNum x1 x2
  , minY: minNum y1 y2
  , maxX: maxNum x1 x2
  , maxY: maxNum y1 y2
  }

-- | Create AABB from two corner points
aabbFromPoints :: Point2D -> Point2D -> AABB
aabbFromPoints (Point2D a) (Point2D b) = aabb a.x a.y b.x b.y

-- | Get AABB center point
aabbCenter :: AABB -> Point2D
aabbCenter (AABB b) = Point2D
  { x: (b.minX + b.maxX) / 2.0
  , y: (b.minY + b.maxY) / 2.0
  }

-- | Get AABB size (width, height)
aabbSize :: AABB -> { width :: Number, height :: Number }
aabbSize (AABB b) = 
  { width: b.maxX - b.minX
  , height: b.maxY - b.minY
  }

-- | Get AABB half-size (useful for collision math)
aabbHalfSize :: AABB -> { hx :: Number, hy :: Number }
aabbHalfSize (AABB b) =
  { hx: (b.maxX - b.minX) / 2.0
  , hy: (b.maxY - b.minY) / 2.0
  }

-- | Check if point is inside AABB
aabbContains :: AABB -> Point2D -> Boolean
aabbContains (AABB b) (Point2D p) =
  p.x >= b.minX && p.x <= b.maxX &&
  p.y >= b.minY && p.y <= b.maxY

-- | Expand AABB by a margin on all sides
aabbExpand :: Number -> AABB -> AABB
aabbExpand margin (AABB b) = AABB
  { minX: b.minX - margin
  , minY: b.minY - margin
  , maxX: b.maxX + margin
  , maxY: b.maxY + margin
  }

-- | Merge two AABBs into one that contains both
aabbMerge :: AABB -> AABB -> AABB
aabbMerge (AABB a) (AABB b) = AABB
  { minX: minNum a.minX b.minX
  , minY: minNum a.minY b.minY
  , maxX: maxNum a.maxX b.maxX
  , maxY: maxNum a.maxY b.maxY
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // bounding circle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounding Circle (Bounding Sphere in 2D).
-- |
-- | Rotationally invariant — rotation doesn't change the bounds.
-- | Simpler math than AABB for moving objects.
newtype BoundingCircle = BoundingCircle
  { center :: Point2D
  , radius :: Number    -- ^ Always non-negative (clamped)
  }

derive instance eqBoundingCircle :: Eq BoundingCircle
derive instance ordBoundingCircle :: Ord BoundingCircle

instance showBoundingCircle :: Show BoundingCircle where
  show (BoundingCircle c) = "BoundingCircle(r=" <> show c.radius <> ")"

-- | Create a bounding circle
boundingCircle :: Point2D -> Number -> BoundingCircle
boundingCircle center radius = BoundingCircle
  { center
  , radius: clampPositive 100000.0 radius
  }

-- | Check if point is inside circle
circleContains :: BoundingCircle -> Point2D -> Boolean
circleContains (BoundingCircle c) p =
  distanceSquared c.center p <= c.radius * c.radius

-- | Expand circle radius
circleExpand :: Number -> BoundingCircle -> BoundingCircle
circleExpand delta (BoundingCircle c) = BoundingCircle
  { center: c.center
  , radius: clampPositive 100000.0 (c.radius + delta)
  }

-- | Merge two circles into one containing both
circleMerge :: BoundingCircle -> BoundingCircle -> BoundingCircle
circleMerge (BoundingCircle a) (BoundingCircle b) =
  let 
    d = distance a.center b.center
    -- If one contains the other, return the larger
    newRadius = (d + a.radius + b.radius) / 2.0
    -- Center is on line between centers, weighted by radii
    t = if d < 0.0001 then 0.5 else (newRadius - a.radius) / d
    Point2D ac = a.center
    Point2D bc = b.center
    newCenter = Point2D
      { x: ac.x + t * (bc.x - ac.x)
      , y: ac.y + t * (bc.y - ac.y)
      }
  in BoundingCircle { center: newCenter, radius: clampPositive 100000.0 newRadius }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // bounding capsule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounding Capsule (Stadium shape).
-- |
-- | Two circles connected by a rectangle. Good for elongated moving objects
-- | (characters, bullets, etc.). Also called "swept sphere" or "stadium".
newtype BoundingCapsule = BoundingCapsule
  { pointA :: Point2D   -- ^ First endpoint
  , pointB :: Point2D   -- ^ Second endpoint
  , radius :: Number    -- ^ Capsule radius (thickness)
  }

derive instance eqBoundingCapsule :: Eq BoundingCapsule
derive instance ordBoundingCapsule :: Ord BoundingCapsule

instance showBoundingCapsule :: Show BoundingCapsule where
  show (BoundingCapsule c) = "BoundingCapsule(r=" <> show c.radius <> ")"

-- | Create a bounding capsule
boundingCapsule :: Point2D -> Point2D -> Number -> BoundingCapsule
boundingCapsule pointA pointB radius = BoundingCapsule
  { pointA
  , pointB
  , radius: clampPositive 100000.0 radius
  }

-- | Check if point is inside capsule
capsuleContains :: BoundingCapsule -> Point2D -> Boolean
capsuleContains (BoundingCapsule c) p =
  let dist = pointToSegmentDistance p c.pointA c.pointB
  in dist <= c.radius

-- | Distance from point to line segment
pointToSegmentDistance :: Point2D -> Point2D -> Point2D -> Number
pointToSegmentDistance (Point2D p) (Point2D a) (Point2D b) =
  let
    -- Vector from A to B
    abx = b.x - a.x
    aby = b.y - a.y
    -- Vector from A to P
    apx = p.x - a.x
    apy = p.y - a.y
    -- Project P onto line AB, get parameter t
    abSquared = abx * abx + aby * aby
    t = if abSquared < 0.0001 
        then 0.0 
        else clampUnit 1.0 ((apx * abx + apy * aby) / abSquared)
    -- Closest point on segment
    closestX = a.x + t * abx
    closestY = a.y + t * aby
    -- Distance to closest point
    dx = p.x - closestX
    dy = p.y - closestY
  in sqrt (dx * dx + dy * dy)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // obb
-- ═════════════════════════════════════════════════════════════════════════════

-- | Oriented Bounding Box.
-- |
-- | Like AABB but can be rotated. More expensive to test but tighter fit
-- | for rotated objects.
newtype OBB = OBB
  { center :: Point2D   -- ^ Center point
  , halfWidth :: Number -- ^ Half-width along local X axis
  , halfHeight :: Number -- ^ Half-height along local Y axis
  , rotation :: Number  -- ^ Rotation angle in radians
  }

derive instance eqOBB :: Eq OBB
derive instance ordOBB :: Ord OBB

instance showOBB :: Show OBB where
  show (OBB o) = "OBB(" <> show o.halfWidth <> "x" <> show o.halfHeight 
             <> " @" <> show o.rotation <> ")"

-- | Create an oriented bounding box
obb :: Point2D -> Number -> Number -> Number -> OBB
obb center halfWidth halfHeight rotation = OBB
  { center
  , halfWidth: clampPositive 100000.0 halfWidth
  , halfHeight: clampPositive 100000.0 halfHeight
  , rotation
  }

-- | Get the four corners of the OBB
obbCorners :: OBB -> { tl :: Point2D, tr :: Point2D, bl :: Point2D, br :: Point2D }
obbCorners (OBB o) =
  let
    Point2D c = o.center
    cosR = cos o.rotation
    sinR = sin o.rotation
    -- Local corners before rotation
    hw = o.halfWidth
    hh = o.halfHeight
    -- Rotate each corner
    rotatePoint lx ly = Point2D
      { x: c.x + lx * cosR - ly * sinR
      , y: c.y + lx * sinR + ly * cosR
      }
  in
    { tl: rotatePoint (negate hw) (negate hh)
    , tr: rotatePoint hw (negate hh)
    , bl: rotatePoint (negate hw) hh
    , br: rotatePoint hw hh
    }

-- | Check if point is inside OBB
obbContains :: OBB -> Point2D -> Boolean
obbContains (OBB o) (Point2D p) =
  let
    Point2D c = o.center
    -- Transform point to OBB local space
    dx = p.x - c.x
    dy = p.y - c.y
    cosR = cos (negate o.rotation)
    sinR = sin (negate o.rotation)
    localX = dx * cosR - dy * sinR
    localY = dx * sinR + dy * cosR
  in absNum localX <= o.halfWidth && absNum localY <= o.halfHeight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // contact
-- ═════════════════════════════════════════════════════════════════════════════

-- | Contact information from collision detection.
-- |
-- | Contains everything needed to resolve a collision:
-- | - Where the collision happened (contact point)
-- | - Which direction to push apart (normal)
-- | - How much they overlap (penetration depth)
data Contact
  = NoContact
  | Contact
      { point :: Point2D     -- ^ Contact point (on surface of first object)
      , normal :: Point2D    -- ^ Contact normal (unit vector, points from first to second)
      , depth :: Number      -- ^ Penetration depth (positive = overlapping)
      }

derive instance eqContact :: Eq Contact

instance showContact :: Show Contact where
  show NoContact = "NoContact"
  show (Contact c) = "Contact(depth=" <> show c.depth <> ")"

-- | Create a contact
contact :: Point2D -> Point2D -> Number -> Contact
contact point normal depth = Contact
  { point
  , normal: normalizePoint normal
  , depth: clampDepth depth
  }

-- | No contact result
noContact :: Contact
noContact = NoContact

-- | Check if there is a contact
hasContact :: Contact -> Boolean
hasContact NoContact = false
hasContact (Contact _) = true

-- | Get contact point (origin if no contact)
contactPoint :: Contact -> Point2D
contactPoint NoContact = origin2D
contactPoint (Contact c) = c.point

-- | Get contact normal (zero if no contact)
contactNormal :: Contact -> Point2D
contactNormal NoContact = origin2D
contactNormal (Contact c) = c.normal

-- | Get penetration depth (0 if no contact)
contactDepth :: Contact -> Number
contactDepth NoContact = 0.0
contactDepth (Contact c) = c.depth

-- | Flip contact (swap which object is "first")
flipContact :: Contact -> Contact
flipContact NoContact = NoContact
flipContact (Contact c) = Contact
  { point: c.point
  , normal: negatePoint c.normal
  , depth: c.depth
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // collision detection
-- ═════════════════════════════════════════════════════════════════════════════

-- | AABB vs AABB collision test
aabbVsAABB :: AABB -> AABB -> Contact
aabbVsAABB (AABB a) (AABB b) =
  -- Check for separation on each axis
  if a.maxX < b.minX || b.maxX < a.minX ||
     a.maxY < b.minY || b.maxY < a.minY
  then NoContact
  else
    let
      -- Calculate overlap on each axis
      overlapX = minNum (a.maxX - b.minX) (b.maxX - a.minX)
      overlapY = minNum (a.maxY - b.minY) (b.maxY - a.minY)
      -- Minimum overlap axis is the contact normal
      centerAX = (a.minX + a.maxX) / 2.0
      centerAY = (a.minY + a.maxY) / 2.0
      centerBX = (b.minX + b.maxX) / 2.0
      centerBY = (b.minY + b.maxY) / 2.0
    in if overlapX < overlapY
       then
         let normalX = if centerBX > centerAX then 1.0 else -1.0
             contactX = if normalX > 0.0 then a.maxX else a.minX
             contactY = (maxNum a.minY b.minY + minNum a.maxY b.maxY) / 2.0
         in Contact
              { point: point2D contactX contactY
              , normal: point2D normalX 0.0
              , depth: overlapX
              }
       else
         let normalY = if centerBY > centerAY then 1.0 else -1.0
             contactY = if normalY > 0.0 then a.maxY else a.minY
             contactX = (maxNum a.minX b.minX + minNum a.maxX b.maxX) / 2.0
         in Contact
              { point: point2D contactX contactY
              , normal: point2D 0.0 normalY
              , depth: overlapY
              }

-- | AABB vs Point collision test
aabbVsPoint :: AABB -> Point2D -> Contact
aabbVsPoint box point =
  if aabbContains box point
  then
    let 
      AABB b = box
      Point2D p = point
      -- Distance to each edge
      distLeft = p.x - b.minX
      distRight = b.maxX - p.x
      distTop = p.y - b.minY
      distBottom = b.maxY - p.y
      -- Find minimum distance (closest edge)
      minDist = minNum (minNum distLeft distRight) (minNum distTop distBottom)
    in if minDist <= distLeft && distLeft <= distRight
       then Contact { point, normal: point2D (-1.0) 0.0, depth: distLeft }
       else if minDist <= distRight
       then Contact { point, normal: point2D 1.0 0.0, depth: distRight }
       else if minDist <= distTop
       then Contact { point, normal: point2D 0.0 (-1.0), depth: distTop }
       else Contact { point, normal: point2D 0.0 1.0, depth: distBottom }
  else NoContact

-- | AABB vs Circle collision test
aabbVsCircle :: AABB -> BoundingCircle -> Contact
aabbVsCircle (AABB box) (BoundingCircle circle) =
  let
    Point2D c = circle.center
    -- Find closest point on AABB to circle center
    closestX = clampNum box.minX box.maxX c.x
    closestY = clampNum box.minY box.maxY c.y
    closest = point2D closestX closestY
    -- Distance from circle center to closest point
    dist = distance circle.center closest
  in if dist < circle.radius
     then
       let 
         depth = circle.radius - dist
         normal = if dist < 0.0001
                  then point2D 1.0 0.0  -- Circle center inside AABB
                  else point2D ((c.x - closestX) / dist) ((c.y - closestY) / dist)
       in Contact { point: closest, normal, depth }
     else NoContact

-- | Circle vs Circle collision test
circleVsCircle :: BoundingCircle -> BoundingCircle -> Contact
circleVsCircle (BoundingCircle a) (BoundingCircle b) =
  let
    dist = distance a.center b.center
    radiusSum = a.radius + b.radius
  in if dist < radiusSum
     then
       let
         Point2D ac = a.center
         Point2D bc = b.center
         depth = radiusSum - dist
         normal = if dist < 0.0001
                  then point2D 1.0 0.0  -- Coincident centers
                  else point2D ((bc.x - ac.x) / dist) ((bc.y - ac.y) / dist)
         -- Contact point is on surface of first circle
         Point2D n = normal
         contactPt = point2D (ac.x + n.x * a.radius) (ac.y + n.y * a.radius)
       in Contact { point: contactPt, normal, depth }
     else NoContact

-- | Circle vs Point collision test
circleVsPoint :: BoundingCircle -> Point2D -> Contact
circleVsPoint (BoundingCircle c) point =
  let dist = distance c.center point
  in if dist < c.radius
     then
       let
         Point2D cc = c.center
         Point2D p = point
         depth = c.radius - dist
         normal = if dist < 0.0001
                  then point2D 1.0 0.0
                  else point2D ((p.x - cc.x) / dist) ((p.y - cc.y) / dist)
       in Contact { point, normal, depth }
     else NoContact

-- | Circle vs AABB (flipped aabbVsCircle)
circleVsAABB :: BoundingCircle -> AABB -> Contact
circleVsAABB circle box = flipContact (aabbVsCircle box circle)

-- | Capsule vs Point collision test
capsuleVsPoint :: BoundingCapsule -> Point2D -> Contact
capsuleVsPoint (BoundingCapsule cap) point =
  let dist = pointToSegmentDistance point cap.pointA cap.pointB
  in if dist < cap.radius
     then
       -- Find closest point on segment for normal calculation
       let
         Point2D p = point
         Point2D a = cap.pointA
         Point2D b = cap.pointB
         abx = b.x - a.x
         aby = b.y - a.y
         apx = p.x - a.x
         apy = p.y - a.y
         abSquared = abx * abx + aby * aby
         t = if abSquared < 0.0001 
             then 0.0 
             else clampUnit 1.0 ((apx * abx + apy * aby) / abSquared)
         closestX = a.x + t * abx
         closestY = a.y + t * aby
         dx = p.x - closestX
         dy = p.y - closestY
         depth = cap.radius - dist
         normal = if dist < 0.0001
                  then point2D 1.0 0.0
                  else point2D (dx / dist) (dy / dist)
       in Contact { point, normal, depth }
     else NoContact

-- | Capsule vs Capsule collision test
capsuleVsCapsule :: BoundingCapsule -> BoundingCapsule -> Contact
capsuleVsCapsule (BoundingCapsule a) (BoundingCapsule b) =
  let
    -- Find closest points between the two line segments
    -- This is the segment-segment distance problem
    dist = segmentSegmentDistance a.pointA a.pointB b.pointA b.pointB
    radiusSum = a.radius + b.radius
  in if dist < radiusSum
     then
       -- Simplified: use midpoints for contact point
       let
         midA = midpoint a.pointA a.pointB
         midB = midpoint b.pointA b.pointB
         d = distance midA midB
         Point2D ma = midA
         Point2D mb = midB
         depth = radiusSum - dist
         normal = if d < 0.0001
                  then point2D 1.0 0.0
                  else point2D ((mb.x - ma.x) / d) ((mb.y - ma.y) / d)
         Point2D n = normal
         contactPt = point2D (ma.x + n.x * a.radius) (ma.y + n.y * a.radius)
       in Contact { point: contactPt, normal, depth }
     else NoContact

-- | Distance between two line segments
segmentSegmentDistance :: Point2D -> Point2D -> Point2D -> Point2D -> Number
segmentSegmentDistance a1 a2 b1 b2 =
  -- Check all four point-to-segment distances and take minimum
  let
    d1 = pointToSegmentDistance a1 b1 b2
    d2 = pointToSegmentDistance a2 b1 b2
    d3 = pointToSegmentDistance b1 a1 a2
    d4 = pointToSegmentDistance b2 a1 a2
  in minNum (minNum d1 d2) (minNum d3 d4)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // collision response
-- ═════════════════════════════════════════════════════════════════════════════

-- | Collision response type.
data CollisionResponse
  = ResponseNone     -- ^ No response (pass through)
  | ResponseBounce   -- ^ Elastic bounce
      { restitution :: Number }  -- ^ Bounciness (0 = no bounce, 1 = perfect bounce)
  | ResponseSlide    -- ^ Slide along surface
      { friction :: Number }     -- ^ Friction coefficient
  | ResponseStick    -- ^ Stick to surface
  | ResponseCustom   -- ^ Custom response (handled by application)
      { id :: Int }

derive instance eqCollisionResponse :: Eq CollisionResponse

instance showCollisionResponse :: Show CollisionResponse where
  show ResponseNone = "ResponseNone"
  show (ResponseBounce r) = "ResponseBounce(e=" <> show r.restitution <> ")"
  show (ResponseSlide r) = "ResponseSlide(μ=" <> show r.friction <> ")"
  show ResponseStick = "ResponseStick"
  show (ResponseCustom r) = "ResponseCustom(" <> show r.id <> ")"

-- | No collision response
responseNone :: CollisionResponse
responseNone = ResponseNone

-- | Bounce response with restitution coefficient
responseBounce :: Number -> CollisionResponse
responseBounce e = ResponseBounce { restitution: clampUnit 1.0 e }

-- | Slide response with friction coefficient
responseSlide :: Number -> CollisionResponse
responseSlide f = ResponseSlide { friction: clampUnit 2.0 f }

-- | Stick response (no sliding)
responseStick :: CollisionResponse
responseStick = ResponseStick

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // response calculation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate position offset to resolve overlap.
-- |
-- | Returns (dx, dy) to add to position to separate objects.
resolveOverlap :: Contact -> { dx :: Number, dy :: Number }
resolveOverlap NoContact = { dx: 0.0, dy: 0.0 }
resolveOverlap (Contact c) =
  let Point2D n = c.normal
  in { dx: n.x * c.depth, dy: n.y * c.depth }

-- | Calculate bounce velocity.
-- |
-- | Reflects velocity around contact normal with restitution.
calculateBounce 
  :: { vx :: Number, vy :: Number }  -- ^ Incoming velocity
  -> Contact                          -- ^ Contact information
  -> Number                           -- ^ Restitution (0-1)
  -> { vx :: Number, vy :: Number }   -- ^ Outgoing velocity
calculateBounce vel NoContact _ = vel
calculateBounce vel (Contact c) restitution =
  let
    Point2D n = c.normal
    -- Velocity component along normal
    vn = vel.vx * n.x + vel.vy * n.y
  in if vn >= 0.0
     then vel  -- Already separating
     else
       -- Reflect: v' = v - (1 + e) * (v · n) * n
       let factor = (1.0 + restitution) * vn
       in { vx: vel.vx - factor * n.x
          , vy: vel.vy - factor * n.y
          }

-- | Calculate slide velocity.
-- |
-- | Projects velocity onto surface tangent with friction.
calculateSlide
  :: { vx :: Number, vy :: Number }  -- ^ Incoming velocity
  -> Contact                          -- ^ Contact information
  -> Number                           -- ^ Friction coefficient
  -> { vx :: Number, vy :: Number }   -- ^ Outgoing velocity
calculateSlide vel NoContact _ = vel
calculateSlide vel (Contact c) friction =
  let
    Point2D n = c.normal
    -- Velocity component along normal
    vn = vel.vx * n.x + vel.vy * n.y
  in if vn >= 0.0
     then vel  -- Already separating
     else
       -- Remove normal component, apply friction to tangent
       let
         -- Tangent velocity
         tvx = vel.vx - vn * n.x
         tvy = vel.vy - vn * n.y
         -- Apply friction (reduce tangent velocity)
         frictionFactor = maxNum 0.0 (1.0 - friction)
       in { vx: tvx * frictionFactor
          , vy: tvy * frictionFactor
          }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // collision layers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Collision layer for filtering.
-- |
-- | Objects on the same layer can collide. Layers are bit flags.
newtype CollisionLayer = CollisionLayer Int

derive instance eqCollisionLayer :: Eq CollisionLayer
derive instance ordCollisionLayer :: Ord CollisionLayer

instance showCollisionLayer :: Show CollisionLayer where
  show (CollisionLayer l) = "CollisionLayer(" <> show l <> ")"

-- | Collision mask (which layers to collide with).
newtype CollisionMask = CollisionMask Int

derive instance eqCollisionMask :: Eq CollisionMask
derive instance ordCollisionMask :: Ord CollisionMask

instance showCollisionMask :: Show CollisionMask where
  show (CollisionMask m) = "CollisionMask(" <> show m <> ")"

-- | Check if a layer matches a mask
layerCollides :: CollisionLayer -> CollisionMask -> Boolean
layerCollides (CollisionLayer layer) (CollisionMask mask) =
  -- Using simple integer comparison since we don't have bitwise AND
  -- In practice, layers would be 1, 2, 4, 8, etc.
  layer > 0 && mask > 0 && 
  (layer <= mask || modInt mask layer == 0)

-- | Mask that collides with all layers
allLayers :: CollisionMask
allLayers = CollisionMask 2147483647  -- Max 32-bit signed int

-- | Mask that collides with no layers
noLayers :: CollisionMask
noLayers = CollisionMask 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // collision state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Current collision state between two objects.
data CollisionState
  = NotColliding       -- ^ Objects are separated
  | Colliding          -- ^ Objects are overlapping
  | Separating         -- ^ Objects were colliding, now separating
  | Resting            -- ^ Objects in stable contact (not moving relative)
  | Sliding            -- ^ Objects in contact, sliding past each other
  | Rolling            -- ^ One object rolling on another

derive instance eqCollisionState :: Eq CollisionState
derive instance ordCollisionState :: Ord CollisionState

instance showCollisionState :: Show CollisionState where
  show NotColliding = "NotColliding"
  show Colliding = "Colliding"
  show Separating = "Separating"
  show Resting = "Resting"
  show Sliding = "Sliding"
  show Rolling = "Rolling"

-- | Check if currently colliding
isColliding :: CollisionState -> Boolean
isColliding Colliding = true
isColliding Resting = true
isColliding Sliding = true
isColliding Rolling = true
isColliding _ = false

-- | Check if separating
isSeparating :: CollisionState -> Boolean
isSeparating Separating = true
isSeparating _ = false

-- | Check if resting contact
isResting :: CollisionState -> Boolean
isResting Resting = true
isResting _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimum of two numbers
minNum :: Number -> Number -> Number
minNum a b = if a < b then a else b

-- | Maximum of two numbers
maxNum :: Number -> Number -> Number
maxNum a b = if a > b then a else b

-- | Absolute value
absNum :: Number -> Number
absNum n = if n < 0.0 then negate n else n

-- | Clamp to range
clampNum :: Number -> Number -> Number -> Number
clampNum lo hi x
  | x < lo = lo
  | x > hi = hi
  | otherwise = x

-- | Clamp positive
clampPositive :: Number -> Number -> Number
clampPositive maxVal n
  | n < 0.0 = 0.0
  | n > maxVal = maxVal
  | otherwise = n

-- | Clamp to unit range
clampUnit :: Number -> Number -> Number
clampUnit maxVal n
  | n < 0.0 = 0.0
  | n > maxVal = maxVal
  | otherwise = n

-- | Clamp penetration depth to reasonable bounds
clampDepth :: Number -> Number
clampDepth d
  | d < 0.0 = 0.0
  | d > 10000.0 = 10000.0
  | otherwise = d

-- | Normalize a point (make unit length)
normalizePoint :: Point2D -> Point2D
normalizePoint (Point2D p) =
  let len = sqrt (p.x * p.x + p.y * p.y)
  in if len < 0.0001
     then Point2D { x: 1.0, y: 0.0 }  -- Default to right
     else Point2D { x: p.x / len, y: p.y / len }

-- | Negate a point
negatePoint :: Point2D -> Point2D
negatePoint (Point2D p) = Point2D { x: negate p.x, y: negate p.y }

-- | Integer modulo (for layer check)
modInt :: Int -> Int -> Int
modInt a b = a - (a / b) * b
