-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // geometry // polar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Polar — 2D polar coordinate system (radius, angle).
-- |
-- | ## Design Philosophy
-- |
-- | Polar coordinates represent 2D points as (radius, angle) pairs:
-- | - **radius**: distance from origin (non-negative)
-- | - **angle**: direction from positive X-axis (counter-clockwise)
-- |
-- | This is the natural coordinate system for:
-- | - Circular UI elements (color wheels, dials, radial menus)
-- | - Rotational motion and animation
-- | - Spiral patterns
-- |
-- | ## Conversion
-- |
-- | ```purescript
-- | -- Cartesian (x, y) to Polar (r, θ)
-- | r = sqrt(x² + y²)
-- | θ = atan2(y, x)
-- |
-- | -- Polar (r, θ) to Cartesian (x, y)
-- | x = r * cos(θ)
-- | y = r * sin(θ)
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Geometry.Point (Point2D)
-- | - Hydrogen.Schema.Geometry.Angle (Degrees, Radians)
-- | - Data.Number (sqrt, cos, sin, atan2)
-- |
-- | ## Dependents
-- |
-- | - Component.ColorPicker (hue wheel positions)
-- | - Component.Dial (rotary input)
-- | - Motion.Spiral (spiral animations)

module Hydrogen.Schema.Geometry.Polar
  ( -- * PolarPoint Type
    PolarPoint(PolarPoint)
  , mkPolarPoint
  , mkPolarPointUnsafe
  , polarRadius
  , polarAngle
  
  -- * Conversions
  , toCartesian
  , fromCartesian
  , toCartesianAt
  , fromCartesianAt
  
  -- * Operations
  , rotatePolar
  , scalePolar
  , translateRadial
  , mirrorPolar
  
  -- * Common Points
  , polarOrigin
  , polarRight
  , polarUp
  , polarLeft
  , polarDown
  
  -- * Interpolation
  , lerpPolar
  , lerpPolarShortest
  
  -- * Comparison
  , polarDistanceSquared
  , polarDistance
  , sameRadius
  , sameAngle
  
  -- * Display
  , showPolar
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
  , otherwise
  , (>)
  , (>=)
  , (<)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (&&)
  , (==)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (sqrt, cos, sin, atan2, pi)

import Hydrogen.Schema.Geometry.Point 
  ( Point2D(Point2D)
  , point2D
  , origin2D
  , getX
  , getY
  )

import Hydrogen.Schema.Geometry.Angle
  ( Degrees(Degrees)
  , toRadians
  , unwrapRadians
  , unwrapDegrees
  , addAngle
  , subtractAngle
  , lerpAngle
  , shortestPath
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // polar point type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Polar coordinate point.
-- |
-- | Radius is non-negative (enforced via smart constructor).
-- | Angle is in degrees, normalized to [0, 360).
newtype PolarPoint = PolarPoint
  { radius :: Number
  , angle :: Degrees
  }

derive instance eqPolarPoint :: Eq PolarPoint
derive instance ordPolarPoint :: Ord PolarPoint

instance showPolarPointInstance :: Show PolarPoint where
  show (PolarPoint p) = "(PolarPoint r=" <> show p.radius <> " θ=" <> show p.angle <> ")"

-- | Create a polar point with validation.
-- |
-- | Returns Nothing if radius is negative.
-- | Angle is normalized to [0, 360).
mkPolarPoint :: Number -> Degrees -> Maybe PolarPoint
mkPolarPoint r angle =
  if r >= 0.0
  then Just (PolarPoint { radius: r, angle: normalizeAngle angle })
  else Nothing
  where
    normalizeAngle :: Degrees -> Degrees
    normalizeAngle (Degrees d) =
      let wrapped = d - 360.0 * floor (d / 360.0)
      in Degrees (if wrapped < 0.0 then wrapped + 360.0 else wrapped)
    
    floor :: Number -> Number
    floor n = if n >= 0.0 then floorPos n else negate (floorPos (negate n)) - 1.0
    
    floorPos :: Number -> Number
    floorPos n = n - (n - truncate n)
    
    truncate :: Number -> Number
    truncate n = if n >= 0.0 then truncatePos n else negate (truncatePos (negate n))
    
    truncatePos :: Number -> Number
    truncatePos n = n - fmod n 1.0
    
    fmod :: Number -> Number -> Number
    fmod a b = a - b * floor (a / b)

-- | Create a polar point without validation.
-- |
-- | WARNING: Only use when radius is known to be non-negative.
mkPolarPointUnsafe :: Number -> Degrees -> PolarPoint
mkPolarPointUnsafe r angle = PolarPoint { radius: r, angle: angle }

-- | Get the radius component.
polarRadius :: PolarPoint -> Number
polarRadius (PolarPoint p) = p.radius

-- | Get the angle component.
polarAngle :: PolarPoint -> Degrees
polarAngle (PolarPoint p) = p.angle

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert polar coordinates to Cartesian (relative to origin).
-- |
-- | x = r * cos(θ)
-- | y = r * sin(θ)
toCartesian :: PolarPoint -> Point2D
toCartesian (PolarPoint p) =
  let rad = unwrapRadians (toRadians p.angle)
      x = p.radius * cos rad
      y = p.radius * sin rad
  in point2D x y

-- | Convert Cartesian coordinates to polar (relative to origin).
-- |
-- | r = sqrt(x² + y²)
-- | θ = atan2(y, x)
fromCartesian :: Point2D -> PolarPoint
fromCartesian pt =
  let x = getX pt
      y = getY pt
      r = sqrt (x * x + y * y)
      angleDeg = atan2 y x * 180.0 / pi
      normalized = if angleDeg < 0.0 then angleDeg + 360.0 else angleDeg
  in PolarPoint { radius: r, angle: Degrees normalized }

-- | Convert polar to Cartesian with a custom center point.
toCartesianAt :: Point2D -> PolarPoint -> Point2D
toCartesianAt center polar =
  let Point2D c = center
      cartesian = toCartesian polar
  in point2D (getX cartesian + c.x) (getY cartesian + c.y)

-- | Convert Cartesian to polar with a custom center point.
fromCartesianAt :: Point2D -> Point2D -> PolarPoint
fromCartesianAt center pt =
  let Point2D c = center
      relative = point2D (getX pt - c.x) (getY pt - c.y)
  in fromCartesian relative

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotate a polar point by adding to its angle.
rotatePolar :: Degrees -> PolarPoint -> PolarPoint
rotatePolar delta (PolarPoint p) =
  PolarPoint { radius: p.radius, angle: addAngle p.angle delta }

-- | Scale a polar point's radius.
-- |
-- | Negative factors flip the angle by 180° and use absolute factor.
scalePolar :: Number -> PolarPoint -> PolarPoint
scalePolar factor (PolarPoint p)
  | factor >= 0.0 = PolarPoint { radius: p.radius * factor, angle: p.angle }
  | otherwise = PolarPoint 
      { radius: p.radius * negate factor
      , angle: addAngle p.angle (Degrees 180.0) 
      }

-- | Translate along the radial direction.
-- |
-- | Clamps to zero if result would be negative.
translateRadial :: Number -> PolarPoint -> PolarPoint
translateRadial delta (PolarPoint p) =
  let newRadius = p.radius + delta
  in PolarPoint { radius: if newRadius < 0.0 then 0.0 else newRadius, angle: p.angle }

-- | Mirror a polar point across the X-axis (negate angle).
mirrorPolar :: PolarPoint -> PolarPoint
mirrorPolar (PolarPoint p) =
  let Degrees d = p.angle
      mirrored = if d == 0.0 then 0.0 else 360.0 - d
  in PolarPoint { radius: p.radius, angle: Degrees mirrored }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // common points
-- ═════════════════════════════════════════════════════════════════════════════

-- | Origin in polar coordinates (r=0).
polarOrigin :: PolarPoint
polarOrigin = PolarPoint { radius: 0.0, angle: Degrees 0.0 }

-- | Unit point at 0° (positive X direction).
polarRight :: PolarPoint
polarRight = PolarPoint { radius: 1.0, angle: Degrees 0.0 }

-- | Unit point at 90° (positive Y direction).
polarUp :: PolarPoint
polarUp = PolarPoint { radius: 1.0, angle: Degrees 90.0 }

-- | Unit point at 180° (negative X direction).
polarLeft :: PolarPoint
polarLeft = PolarPoint { radius: 1.0, angle: Degrees 180.0 }

-- | Unit point at 270° (negative Y direction).
polarDown :: PolarPoint
polarDown = PolarPoint { radius: 1.0, angle: Degrees 270.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation between polar points.
-- |
-- | Interpolates radius linearly and angle via additive interpolation.
-- | t=0 returns p1, t=1 returns p2.
lerpPolar :: Number -> PolarPoint -> PolarPoint -> PolarPoint
lerpPolar t (PolarPoint p1) (PolarPoint p2) =
  let r = p1.radius + t * (p2.radius - p1.radius)
      angle = lerpAngle t p1.angle p2.angle
  in PolarPoint { radius: r, angle: angle }

-- | Interpolation using shortest angular path.
-- |
-- | Unlike lerpPolar, this always takes the shorter route around the circle.
lerpPolarShortest :: Number -> PolarPoint -> PolarPoint -> PolarPoint
lerpPolarShortest t (PolarPoint p1) (PolarPoint p2) =
  let r = p1.radius + t * (p2.radius - p1.radius)
      delta = shortestPath p1.angle p2.angle
      Degrees d1 = p1.angle
      Degrees dd = delta
      angle = Degrees (d1 + t * dd)
  in PolarPoint { radius: r, angle: angle }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Squared distance between two polar points in Cartesian space.
-- |
-- | More efficient than polarDistance when only comparing distances.
polarDistanceSquared :: PolarPoint -> PolarPoint -> Number
polarDistanceSquared p1 p2 =
  let c1 = toCartesian p1
      c2 = toCartesian p2
      dx = getX c2 - getX c1
      dy = getY c2 - getY c1
  in dx * dx + dy * dy

-- | Distance between two polar points in Cartesian space.
polarDistance :: PolarPoint -> PolarPoint -> Number
polarDistance p1 p2 = sqrt (polarDistanceSquared p1 p2)

-- | Check if two polar points have the same radius.
sameRadius :: PolarPoint -> PolarPoint -> Boolean
sameRadius (PolarPoint p1) (PolarPoint p2) = p1.radius == p2.radius

-- | Check if two polar points have the same angle.
sameAngle :: PolarPoint -> PolarPoint -> Boolean
sameAngle (PolarPoint p1) (PolarPoint p2) = p1.angle == p2.angle

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format polar point for display.
showPolar :: PolarPoint -> String
showPolar (PolarPoint p) =
  let Degrees d = p.angle
  in "Polar { r: " <> show p.radius <> ", θ: " <> show d <> "° }"
