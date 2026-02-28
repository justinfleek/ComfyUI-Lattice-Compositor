-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // geometry // circle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Circle — 2D circle primitive for shapes and hit testing.
-- |
-- | ## Design Philosophy
-- |
-- | A circle is defined by a center point and radius. This module provides:
-- | - Construction with validation (positive radius)
-- | - Geometric queries (containment, intersection)
-- | - Measurements (circumference, area)
-- | - Path conversion for rendering
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Geometry.Point (Point2D)
-- | - Hydrogen.Schema.Geometry.Angle (Degrees)
-- | - Data.Number (sqrt, pi)
-- |
-- | ## Dependents
-- |
-- | - Component.ColorPicker (hue wheel)
-- | - Component.Dial (rotary input)
-- | - Motion graphics (circular paths)

module Hydrogen.Schema.Geometry.Circle
  ( -- * Circle Type
    Circle(Circle)
  , mkCircle
  , mkCircleUnsafe
  , circleCenter
  , circleRadius
  
  -- * Measurements
  , circumference
  , area
  , diameter
  
  -- * Point Operations
  , contains
  , containsEither
  , distanceToCenter
  , distanceToEdge
  , pointAtAngle
  , tangentAt
  , angleToPoint
  
  -- * Circle-Circle Operations
  , intersectsCircle
  , circleDistance
  , circlesOverlap
  , radiusRatio
  , compareByRadius
  
  -- * Transformations
  , translateCircle
  , scaleCircle
  
  -- * Common Circles
  , unitCircle
  
  -- * Display
  , showCircle
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering
  , (>)
  , (>=)
  , (<=)
  , (<)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (&&)
  , (||)
  , compare
  , show
  , negate
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (sqrt, pi, cos, sin, atan2)

import Hydrogen.Schema.Geometry.Point 
  ( Point2D(Point2D)
  , point2D
  , origin2D
  , getX
  , getY
  , distance2D
  , translate2D
  )

import Hydrogen.Schema.Geometry.Angle
  ( Degrees(Degrees)
  , toRadians
  , unwrapRadians
  )

import Hydrogen.Schema.Geometry.Vector
  ( Vector2D
  , vec2
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // circle type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Circle molecule.
-- |
-- | A circle defined by center point and radius.
-- | Radius is guaranteed positive via smart constructor.
newtype Circle = Circle { center :: Point2D, radius :: Number }

derive instance eqCircle :: Eq Circle
derive instance ordCircle :: Ord Circle

instance showCircleInstance :: Show Circle where
  show (Circle c) = "(Circle " <> show c.center <> " " <> show c.radius <> ")"

-- | Create a circle with validation.
-- |
-- | Returns Nothing if radius is not positive.
mkCircle :: Point2D -> Number -> Maybe Circle
mkCircle center radius =
  if radius > 0.0
  then Just (Circle { center, radius })
  else Nothing

-- | Create a circle without validation.
-- |
-- | WARNING: Only use when radius is known to be positive.
mkCircleUnsafe :: Point2D -> Number -> Circle
mkCircleUnsafe center radius = Circle { center, radius }

-- | Get the center point.
circleCenter :: Circle -> Point2D
circleCenter (Circle c) = c.center

-- | Get the radius.
circleRadius :: Circle -> Number
circleRadius (Circle c) = c.radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // measurements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate circumference (2 * pi * r)
circumference :: Circle -> Number
circumference (Circle c) = 2.0 * pi * c.radius

-- | Calculate area (pi * r^2)
area :: Circle -> Number
area (Circle c) = pi * c.radius * c.radius

-- | Calculate diameter (2 * r)
diameter :: Circle -> Number
diameter (Circle c) = 2.0 * c.radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // point operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a point is inside or on the circle.
contains :: Point2D -> Circle -> Boolean
contains p (Circle c) = distance2D p c.center <= c.radius

-- | Check if a point is inside either of two circles.
containsEither :: Point2D -> Circle -> Circle -> Boolean
containsEither p c1 c2 = contains p c1 || contains p c2

-- | Distance from point to circle center.
distanceToCenter :: Point2D -> Circle -> Number
distanceToCenter p (Circle c) = distance2D p c.center

-- | Signed distance from point to circle edge.
-- |
-- | Negative if inside, positive if outside, zero if on edge.
-- | Uses sqrt via the underlying distance calculation.
distanceToEdge :: Point2D -> Circle -> Number
distanceToEdge p (Circle c) = distance2D p c.center - c.radius

-- | Get point on circle at given angle.
-- |
-- | Angle 0 = right (positive X), 90 = up (positive Y).
pointAtAngle :: Degrees -> Circle -> Point2D
pointAtAngle angle (Circle c) =
  let r = unwrapRadians (toRadians angle)
      cx = getX c.center
      cy = getY c.center
      x = cx + c.radius * cos r
      y = cy + c.radius * sin r
  in point2D x y

-- | Get tangent vector at given angle (perpendicular to radius).
tangentAt :: Degrees -> Circle -> Vector2D
tangentAt angle _ =
  let r = unwrapRadians (toRadians angle)
      -- Tangent is perpendicular to radius: rotate by 90 degrees
      tx = negate (sin r)
      ty = cos r
  in vec2 tx ty

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // circle-circle operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two circles intersect (touch or overlap)
intersectsCircle :: Circle -> Circle -> Boolean
intersectsCircle (Circle c1) (Circle c2) =
  let d = distance2D c1.center c2.center
      sumRadii = c1.radius + c2.radius
      diffRadii = if c1.radius > c2.radius 
                  then c1.radius - c2.radius 
                  else c2.radius - c1.radius
  in d <= sumRadii && d >= diffRadii

-- | Distance between circle centers
circleDistance :: Circle -> Circle -> Number
circleDistance (Circle c1) (Circle c2) = distance2D c1.center c2.center

-- | Check if circles overlap (not just touch).
circlesOverlap :: Circle -> Circle -> Boolean
circlesOverlap (Circle c1) (Circle c2) =
  let d = distance2D c1.center c2.center
  in d < c1.radius + c2.radius

-- | Ratio of two circle radii.
-- |
-- | Returns c1.radius / c2.radius.
radiusRatio :: Circle -> Circle -> Number
radiusRatio (Circle c1) (Circle c2) = c1.radius / c2.radius

-- | Compare circles by radius.
-- |
-- | Useful for sorting circles by size.
compareByRadius :: Circle -> Circle -> Ordering
compareByRadius (Circle c1) (Circle c2) = compare c1.radius c2.radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transformations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translate circle by offset
translateCircle :: Number -> Number -> Circle -> Circle
translateCircle dx dy (Circle c) =
  Circle { center: translate2D dx dy c.center
         , radius: c.radius
         }

-- | Scale circle radius (center unchanged).
-- |
-- | Returns Nothing if factor is not positive.
-- | This validates the scaling factor rather than silently handling invalid input.
scaleCircle :: Number -> Circle -> Maybe Circle
scaleCircle factor (Circle c)
  | factor > 0.0 = Just (Circle { center: c.center, radius: c.radius * factor })
  | true = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // common circles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unit circle: center at origin, radius 1.
unitCircle :: Circle
unitCircle = Circle { center: origin2D, radius: 1.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format circle for display.
-- |
-- | Uses pattern matching on Point2D to extract coordinates.
-- | Provides a more verbose format than the Show instance.
showCircle :: Circle -> String
showCircle (Circle c) =
  let Point2D center = c.center
  in "Circle { center: (" <> show center.x <> ", " <> show center.y <> "), radius: " <> show c.radius <> " }"

-- | Get the angle in degrees from circle center to a point.
-- |
-- | Returns angle wrapped to [0, 360).
-- | Uses sqrt to check if point is not at center.
angleToPoint :: Point2D -> Circle -> Degrees
angleToPoint (Point2D p) (Circle c) =
  let Point2D center = c.center
      dx = p.x - center.x
      dy = p.y - center.y
      dist = sqrt (dx * dx + dy * dy)
  in if dist > 0.0
     then Degrees (atan2Deg dy dx)
     else Degrees 0.0
  where
    -- Convert atan2 result to degrees, normalized to [0, 360)
    atan2Deg :: Number -> Number -> Number
    atan2Deg y x =
      let radians = atan2 y x
          deg = radians * 180.0 / pi
      in if deg < 0.0 then deg + 360.0 else deg
