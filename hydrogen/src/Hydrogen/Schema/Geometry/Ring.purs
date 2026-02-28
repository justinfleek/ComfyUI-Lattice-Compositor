-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // geometry // ring
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Ring (Annulus) — 2D shape bounded by two concentric circles.
-- |
-- | ## Design Philosophy
-- |
-- | A ring (annulus) is defined by:
-- | - Center point
-- | - Inner radius (hole)
-- | - Outer radius (boundary)
-- |
-- | This creates a "donut" shape where points must be:
-- | - At least innerRadius from center
-- | - At most outerRadius from center
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Geometry.Point (Point2D)
-- | - Hydrogen.Schema.Geometry.Circle (Circle)
-- | - Hydrogen.Schema.Geometry.Angle (Degrees)
-- | - Data.Number (sqrt, pi)
-- |
-- | ## Dependents
-- |
-- | - Progress indicators (circular loading bars)
-- | - Pie/donut charts
-- | - Component.Dial (rotary controls with center hole)
-- | - Audio visualizers (spectrum rings)

module Hydrogen.Schema.Geometry.Ring
  ( -- * Ring Type
    Ring(Ring)
  , mkRing
  , mkRingUnsafe
  , ringCenter
  , ringInnerRadius
  , ringOuterRadius
  
  -- * Measurements
  , ringArea
  , ringWidth
  , innerCircumference
  , outerCircumference
  , averageCircumference
  
  -- * Properties
  , radiusRatio
  , isNarrow
  , isWide
  
  -- * Point Operations
  , contains
  , containsAngle
  , distanceToRing
  , nearestPointOnRing
  , pointAtAngle
  , innerPointAtAngle
  , outerPointAtAngle
  
  -- * Circle Operations
  , innerCircle
  , outerCircle
  , toCircles
  
  -- * Transformations
  , translateRing
  , scaleRing
  , setInnerRadius
  , setOuterRadius
  , setWidth
  
  -- * Constructors
  , unitRing
  , ringFromWidth
  , ringFromCircle
  
  -- * Comparison
  , compareByOuterRadius
  , compareByWidth
  , sameWidth
  
  -- * Display
  , showRing
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
  , (==)
  , compare
  , show
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (sqrt, pi, cos, sin)

import Hydrogen.Schema.Geometry.Point 
  ( Point2D(Point2D)
  , point2D
  , origin2D
  , distance2D
  , translate2D
  )

import Hydrogen.Schema.Geometry.Circle
  ( Circle
  , mkCircleUnsafe
  , circleCenter
  , circleRadius
  )

import Hydrogen.Schema.Geometry.Angle
  ( Degrees
  , toRadians
  , unwrapRadians
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // ring type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ring (Annulus) molecule.
-- |
-- | A ring is defined by a center point and two radii:
-- | - innerRadius: radius of the inner circle (hole)
-- | - outerRadius: radius of the outer circle (boundary)
-- |
-- | Invariants:
-- | - Both radii must be positive
-- | - outerRadius > innerRadius
newtype Ring = Ring
  { center :: Point2D
  , innerRadius :: Number
  , outerRadius :: Number
  }

derive instance eqRing :: Eq Ring
derive instance ordRing :: Ord Ring

instance showRingInstance :: Show Ring where
  show (Ring r) = "(Ring " <> show r <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a ring with validation.
-- |
-- | Returns Nothing if:
-- | - Either radius is not positive
-- | - Inner radius >= outer radius
mkRing :: Point2D -> Number -> Number -> Maybe Ring
mkRing center inner outer =
  if inner > 0.0 && outer > 0.0 && outer > inner
  then Just (Ring { center, innerRadius: inner, outerRadius: outer })
  else Nothing

-- | Create a ring without validation.
-- |
-- | WARNING: Only use when invariants are guaranteed.
mkRingUnsafe :: Point2D -> Number -> Number -> Ring
mkRingUnsafe center inner outer =
  Ring { center, innerRadius: inner, outerRadius: outer }

-- | Get the center point.
ringCenter :: Ring -> Point2D
ringCenter (Ring r) = r.center

-- | Get the inner radius.
ringInnerRadius :: Ring -> Number
ringInnerRadius (Ring r) = r.innerRadius

-- | Get the outer radius.
ringOuterRadius :: Ring -> Number
ringOuterRadius (Ring r) = r.outerRadius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // measurements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate area of the ring (annulus).
-- |
-- | A = π × (r_outer² - r_inner²)
ringArea :: Ring -> Number
ringArea (Ring r) =
  pi * (r.outerRadius * r.outerRadius - r.innerRadius * r.innerRadius)

-- | Width of the ring (difference between radii).
ringWidth :: Ring -> Number
ringWidth (Ring r) = r.outerRadius - r.innerRadius

-- | Circumference of the inner circle.
innerCircumference :: Ring -> Number
innerCircumference (Ring r) = 2.0 * pi * r.innerRadius

-- | Circumference of the outer circle.
outerCircumference :: Ring -> Number
outerCircumference (Ring r) = 2.0 * pi * r.outerRadius

-- | Average circumference (at the middle of the ring width).
-- |
-- | Useful for calculating arc lengths at the visual center of the ring.
averageCircumference :: Ring -> Number
averageCircumference (Ring r) =
  let avgRadius = (r.innerRadius + r.outerRadius) / 2.0
  in 2.0 * pi * avgRadius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ratio of inner to outer radius.
-- |
-- | Range: (0, 1)
-- | Closer to 0 = wide ring (small hole)
-- | Closer to 1 = narrow ring (large hole)
radiusRatio :: Ring -> Number
radiusRatio (Ring r) = r.innerRadius / r.outerRadius

-- | Check if ring is narrow (ratio > 0.8).
-- |
-- | Narrow rings have a thin band between inner and outer circles.
isNarrow :: Ring -> Boolean
isNarrow ring = radiusRatio ring > 0.8

-- | Check if ring is wide (ratio < 0.3).
-- |
-- | Wide rings have a large band between inner and outer circles.
isWide :: Ring -> Boolean
isWide ring = radiusRatio ring < 0.3

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // point operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a point is inside the ring (between inner and outer circles).
contains :: Point2D -> Ring -> Boolean
contains p (Ring r) =
  let d = distance2D p r.center
  in d >= r.innerRadius && d <= r.outerRadius

-- | Check if a point at a specific angle would be in the ring.
-- |
-- | Always true since the ring is rotationally symmetric.
-- | Included for API consistency with Sector.
containsAngle :: Degrees -> Ring -> Boolean
containsAngle _ _ = true

-- | Signed distance from a point to the ring.
-- |
-- | Negative = inside the ring
-- | Zero = on the ring boundary (inner or outer)
-- | Positive = outside the ring (either in the hole or beyond the outer)
distanceToRing :: Point2D -> Ring -> Number
distanceToRing p (Ring r) =
  let d = distance2D p r.center
  in if d < r.innerRadius
     then r.innerRadius - d  -- In the hole, positive distance to ring
     else if d > r.outerRadius
          then d - r.outerRadius  -- Outside, positive distance to ring
          else 0.0  -- In the ring

-- | Find nearest point on ring to given point.
-- |
-- | Projects onto inner or outer circle, whichever is closer.
nearestPointOnRing :: Point2D -> Ring -> Point2D
nearestPointOnRing (Point2D p) (Ring r) =
  let Point2D c = r.center
      dx = p.x - c.x
      dy = p.y - c.y
      d = sqrt (dx * dx + dy * dy)
  in if d == 0.0
     -- Point is at center, return point on inner circle at angle 0
     then point2D (c.x + r.innerRadius) c.y
     else
       let
         -- Normalize direction
         nx = dx / d
         ny = dy / d
         -- Choose inner or outer circle based on distance
         targetRadius = if d < (r.innerRadius + r.outerRadius) / 2.0
                        then r.innerRadius
                        else r.outerRadius
       in point2D (c.x + nx * targetRadius) (c.y + ny * targetRadius)

-- | Get a point at the midpoint of the ring width at given angle.
pointAtAngle :: Degrees -> Ring -> Point2D
pointAtAngle angle (Ring r) =
  let rad = unwrapRadians (toRadians angle)
      Point2D c = r.center
      avgRadius = (r.innerRadius + r.outerRadius) / 2.0
      x = c.x + avgRadius * cos rad
      y = c.y + avgRadius * sin rad
  in point2D x y

-- | Get point on inner circle at given angle.
innerPointAtAngle :: Degrees -> Ring -> Point2D
innerPointAtAngle angle (Ring r) =
  let rad = unwrapRadians (toRadians angle)
      Point2D c = r.center
      x = c.x + r.innerRadius * cos rad
      y = c.y + r.innerRadius * sin rad
  in point2D x y

-- | Get point on outer circle at given angle.
outerPointAtAngle :: Degrees -> Ring -> Point2D
outerPointAtAngle angle (Ring r) =
  let rad = unwrapRadians (toRadians angle)
      Point2D c = r.center
      x = c.x + r.outerRadius * cos rad
      y = c.y + r.outerRadius * sin rad
  in point2D x y

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // circle operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the inner circle.
innerCircle :: Ring -> Circle
innerCircle (Ring r) = mkCircleUnsafe r.center r.innerRadius

-- | Get the outer circle.
outerCircle :: Ring -> Circle
outerCircle (Ring r) = mkCircleUnsafe r.center r.outerRadius

-- | Get both circles as a pair.
toCircles :: Ring -> { inner :: Circle, outer :: Circle }
toCircles ring = { inner: innerCircle ring, outer: outerCircle ring }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transformations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translate ring by offset.
translateRing :: Number -> Number -> Ring -> Ring
translateRing dx dy (Ring r) =
  Ring (r { center = translate2D dx dy r.center })

-- | Scale both radii uniformly.
-- |
-- | Returns Nothing if factor is not positive.
scaleRing :: Number -> Ring -> Maybe Ring
scaleRing factor (Ring r)
  | factor > 0.0 = Just (Ring (r { innerRadius = r.innerRadius * factor
                                 , outerRadius = r.outerRadius * factor
                                 }))
  | true = Nothing

-- | Set a new inner radius.
-- |
-- | Returns Nothing if new radius is not valid.
setInnerRadius :: Number -> Ring -> Maybe Ring
setInnerRadius newInner (Ring r)
  | newInner > 0.0 && newInner < r.outerRadius = 
      Just (Ring (r { innerRadius = newInner }))
  | true = Nothing

-- | Set a new outer radius.
-- |
-- | Returns Nothing if new radius is not valid.
setOuterRadius :: Number -> Ring -> Maybe Ring
setOuterRadius newOuter (Ring r)
  | newOuter > r.innerRadius = 
      Just (Ring (r { outerRadius = newOuter }))
  | true = Nothing

-- | Set ring width while keeping outer radius fixed.
-- |
-- | Adjusts inner radius to achieve desired width.
-- | Returns Nothing if width is not valid.
setWidth :: Number -> Ring -> Maybe Ring
setWidth width (Ring r)
  | width > 0.0 && width < r.outerRadius =
      Just (Ring (r { innerRadius = r.outerRadius - width }))
  | true = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // preset constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unit ring: center at origin, inner radius 0.5, outer radius 1.0.
unitRing :: Ring
unitRing = Ring { center: origin2D, innerRadius: 0.5, outerRadius: 1.0 }

-- | Create ring from outer radius and width.
-- |
-- | Useful when you know the boundary size and band thickness.
ringFromWidth :: Point2D -> Number -> Number -> Maybe Ring
ringFromWidth center outer width =
  let inner = outer - width
  in mkRing center inner outer

-- | Create ring from a circle by adding a hole.
-- |
-- | The input circle becomes the outer boundary.
ringFromCircle :: Circle -> Number -> Maybe Ring
ringFromCircle outerC inner =
  let center = circleCenter outerC
      outer = circleRadius outerC
  in mkRing center inner outer

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compare rings by outer radius.
compareByOuterRadius :: Ring -> Ring -> Ordering
compareByOuterRadius r1 r2 = compare (ringOuterRadius r1) (ringOuterRadius r2)

-- | Compare rings by width.
compareByWidth :: Ring -> Ring -> Ordering
compareByWidth r1 r2 = compare (ringWidth r1) (ringWidth r2)

-- | Check if two rings have the same width.
sameWidth :: Ring -> Ring -> Boolean
sameWidth r1 r2 = ringWidth r1 == ringWidth r2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format ring for display.
showRing :: Ring -> String
showRing (Ring r) =
  let Point2D center = r.center
  in "Ring { center: (" <> show center.x <> ", " <> show center.y 
     <> "), inner: " <> show r.innerRadius 
     <> ", outer: " <> show r.outerRadius <> " }"
