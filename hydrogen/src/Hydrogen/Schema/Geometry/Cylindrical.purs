-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // geometry // cylindrical
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Cylindrical — 3D cylindrical coordinate system (radius, angle, height).
-- |
-- | ## Design Philosophy
-- |
-- | Cylindrical coordinates extend polar coordinates into 3D by adding height:
-- | - **radius**: distance from the Z-axis (non-negative)
-- | - **angle**: direction in the XY plane from positive X-axis
-- | - **height**: Z coordinate (unbounded)
-- |
-- | This is the natural coordinate system for:
-- | - Helical motion (springs, DNA visualization)
-- | - Cylindrical UI layouts (carousel, tower)
-- | - Radial 3D positioning
-- |
-- | ## Conversion
-- |
-- | ```purescript
-- | -- Cartesian (x, y, z) to Cylindrical (r, θ, z)
-- | r = sqrt(x² + y²)
-- | θ = atan2(y, x)
-- | z = z
-- |
-- | -- Cylindrical (r, θ, z) to Cartesian (x, y, z)
-- | x = r * cos(θ)
-- | y = r * sin(θ)
-- | z = z
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Geometry.Point (Point3D)
-- | - Hydrogen.Schema.Geometry.Angle (Degrees)
-- | - Hydrogen.Schema.Geometry.Polar (PolarPoint)
-- | - Data.Number (sqrt, cos, sin, atan2)
-- |
-- | ## Dependents
-- |
-- | - 3D carousel components
-- | - Helical animations
-- | - Cylindrical selection

module Hydrogen.Schema.Geometry.Cylindrical
  ( -- * CylindricalPoint Type
    CylindricalPoint(CylindricalPoint)
  , mkCylindricalPoint
  , mkCylindricalPointUnsafe
  , cylindricalRadius
  , cylindricalAngle
  , cylindricalHeight
  
  -- * Conversions
  , toCartesian
  , fromCartesian
  , toPolar
  , fromPolar
  
  -- * Operations
  , rotateCylindrical
  , scaleCylindrical
  , translateHeight
  , translateRadial
  , mirrorXY
  , mirrorZ
  
  -- * Common Points
  , cylindricalOrigin
  
  -- * Interpolation
  , lerpCylindrical
  , lerpCylindricalShortest
  
  -- * Comparison
  , cylindricalDistance
  , cylindricalDistanceSquared
  , sameRadius
  , sameAngle
  , sameHeight
  
  -- * Helix Generation
  , helixPoint
  
  -- * Display
  , showCylindrical
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
  , (==)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (sqrt, cos, sin, atan2, pi)

import Hydrogen.Schema.Geometry.Point 
  ( Point3D(Point3D)
  , point3D
  , getX3
  , getY3
  , getZ3
  )

import Hydrogen.Schema.Geometry.Angle
  ( Degrees(Degrees)
  , toRadians
  , unwrapRadians
  , unwrapDegrees
  , addAngle
  , lerpAngle
  , shortestPath
  )

import Hydrogen.Schema.Geometry.Polar as Polar

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // cylindrical point type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cylindrical coordinate point.
-- |
-- | Radius is non-negative (enforced via smart constructor).
-- | Angle is in degrees.
-- | Height is unbounded (any real number).
newtype CylindricalPoint = CylindricalPoint
  { radius :: Number
  , angle :: Degrees
  , height :: Number
  }

derive instance eqCylindricalPoint :: Eq CylindricalPoint
derive instance ordCylindricalPoint :: Ord CylindricalPoint

instance showCylindricalPointInstance :: Show CylindricalPoint where
  show (CylindricalPoint p) = 
    "(CylindricalPoint r=" <> show p.radius 
    <> " θ=" <> show p.angle 
    <> " z=" <> show p.height <> ")"

-- | Create a cylindrical point with validation.
-- |
-- | Returns Nothing if radius is negative.
mkCylindricalPoint :: Number -> Degrees -> Number -> Maybe CylindricalPoint
mkCylindricalPoint r angle h =
  if r >= 0.0
  then Just (CylindricalPoint { radius: r, angle: angle, height: h })
  else Nothing

-- | Create a cylindrical point without validation.
-- |
-- | WARNING: Only use when radius is known to be non-negative.
mkCylindricalPointUnsafe :: Number -> Degrees -> Number -> CylindricalPoint
mkCylindricalPointUnsafe r angle h = 
  CylindricalPoint { radius: r, angle: angle, height: h }

-- | Get the radius component.
cylindricalRadius :: CylindricalPoint -> Number
cylindricalRadius (CylindricalPoint p) = p.radius

-- | Get the angle component.
cylindricalAngle :: CylindricalPoint -> Degrees
cylindricalAngle (CylindricalPoint p) = p.angle

-- | Get the height component.
cylindricalHeight :: CylindricalPoint -> Number
cylindricalHeight (CylindricalPoint p) = p.height

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert cylindrical coordinates to Cartesian.
-- |
-- | x = r * cos(θ)
-- | y = r * sin(θ)
-- | z = z
toCartesian :: CylindricalPoint -> Point3D
toCartesian (CylindricalPoint p) =
  let rad = unwrapRadians (toRadians p.angle)
      x = p.radius * cos rad
      y = p.radius * sin rad
  in point3D x y p.height

-- | Convert Cartesian coordinates to cylindrical.
-- |
-- | r = sqrt(x² + y²)
-- | θ = atan2(y, x)
-- | z = z
fromCartesian :: Point3D -> CylindricalPoint
fromCartesian pt =
  let x = getX3 pt
      y = getY3 pt
      z = getZ3 pt
      r = sqrt (x * x + y * y)
      angleDeg = atan2 y x * 180.0 / pi
      normalized = if angleDeg < 0.0 then angleDeg + 360.0 else angleDeg
  in CylindricalPoint { radius: r, angle: Degrees normalized, height: z }

-- | Convert cylindrical to polar (discarding height).
toPolar :: CylindricalPoint -> Polar.PolarPoint
toPolar (CylindricalPoint p) = 
  Polar.mkPolarPointUnsafe p.radius p.angle

-- | Convert polar to cylindrical (with specified height).
fromPolar :: Number -> Polar.PolarPoint -> CylindricalPoint
fromPolar h polar = 
  CylindricalPoint 
    { radius: Polar.polarRadius polar
    , angle: Polar.polarAngle polar
    , height: h
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotate a cylindrical point around the Z-axis.
rotateCylindrical :: Degrees -> CylindricalPoint -> CylindricalPoint
rotateCylindrical delta (CylindricalPoint p) =
  CylindricalPoint { radius: p.radius, angle: addAngle p.angle delta, height: p.height }

-- | Scale the radius of a cylindrical point.
-- |
-- | Negative factors flip the angle by 180° and use absolute factor.
scaleCylindrical :: Number -> CylindricalPoint -> CylindricalPoint
scaleCylindrical factor (CylindricalPoint p)
  | factor >= 0.0 = CylindricalPoint { radius: p.radius * factor, angle: p.angle, height: p.height }
  | otherwise = CylindricalPoint 
      { radius: p.radius * negate factor
      , angle: addAngle p.angle (Degrees 180.0)
      , height: p.height
      }

-- | Translate along the Z-axis.
translateHeight :: Number -> CylindricalPoint -> CylindricalPoint
translateHeight delta (CylindricalPoint p) =
  CylindricalPoint { radius: p.radius, angle: p.angle, height: p.height + delta }

-- | Translate along the radial direction.
-- |
-- | Clamps to zero if result would be negative.
translateRadial :: Number -> CylindricalPoint -> CylindricalPoint
translateRadial delta (CylindricalPoint p) =
  let newRadius = p.radius + delta
  in CylindricalPoint 
    { radius: if newRadius < 0.0 then 0.0 else newRadius
    , angle: p.angle
    , height: p.height
    }

-- | Mirror across the XY plane (negate height).
mirrorXY :: CylindricalPoint -> CylindricalPoint
mirrorXY (CylindricalPoint p) =
  CylindricalPoint { radius: p.radius, angle: p.angle, height: negate p.height }

-- | Mirror across a plane containing the Z-axis (negate angle).
mirrorZ :: CylindricalPoint -> CylindricalPoint
mirrorZ (CylindricalPoint p) =
  let Degrees d = p.angle
      mirrored = if d == 0.0 then 0.0 else 360.0 - d
  in CylindricalPoint { radius: p.radius, angle: Degrees mirrored, height: p.height }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // common points
-- ═════════════════════════════════════════════════════════════════════════════

-- | Origin in cylindrical coordinates.
cylindricalOrigin :: CylindricalPoint
cylindricalOrigin = CylindricalPoint { radius: 0.0, angle: Degrees 0.0, height: 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation between cylindrical points.
-- |
-- | Interpolates radius and height linearly, angle via additive interpolation.
-- | t=0 returns p1, t=1 returns p2.
lerpCylindrical :: Number -> CylindricalPoint -> CylindricalPoint -> CylindricalPoint
lerpCylindrical t (CylindricalPoint p1) (CylindricalPoint p2) =
  let r = p1.radius + t * (p2.radius - p1.radius)
      h = p1.height + t * (p2.height - p1.height)
      angle = lerpAngle t p1.angle p2.angle
  in CylindricalPoint { radius: r, angle: angle, height: h }

-- | Interpolation using shortest angular path.
-- |
-- | Unlike lerpCylindrical, this always takes the shorter route around the Z-axis.
lerpCylindricalShortest :: Number -> CylindricalPoint -> CylindricalPoint -> CylindricalPoint
lerpCylindricalShortest t (CylindricalPoint p1) (CylindricalPoint p2) =
  let r = p1.radius + t * (p2.radius - p1.radius)
      h = p1.height + t * (p2.height - p1.height)
      delta = shortestPath p1.angle p2.angle
      Degrees d1 = p1.angle
      Degrees dd = delta
      angle = Degrees (d1 + t * dd)
  in CylindricalPoint { radius: r, angle: angle, height: h }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Squared distance between two cylindrical points in Cartesian space.
cylindricalDistanceSquared :: CylindricalPoint -> CylindricalPoint -> Number
cylindricalDistanceSquared p1 p2 =
  let c1 = toCartesian p1
      c2 = toCartesian p2
      dx = getX3 c2 - getX3 c1
      dy = getY3 c2 - getY3 c1
      dz = getZ3 c2 - getZ3 c1
  in dx * dx + dy * dy + dz * dz

-- | Distance between two cylindrical points in Cartesian space.
cylindricalDistance :: CylindricalPoint -> CylindricalPoint -> Number
cylindricalDistance p1 p2 = sqrt (cylindricalDistanceSquared p1 p2)

-- | Check if two points have the same radius.
sameRadius :: CylindricalPoint -> CylindricalPoint -> Boolean
sameRadius (CylindricalPoint p1) (CylindricalPoint p2) = p1.radius == p2.radius

-- | Check if two points have the same angle.
sameAngle :: CylindricalPoint -> CylindricalPoint -> Boolean
sameAngle (CylindricalPoint p1) (CylindricalPoint p2) = p1.angle == p2.angle

-- | Check if two points have the same height.
sameHeight :: CylindricalPoint -> CylindricalPoint -> Boolean
sameHeight (CylindricalPoint p1) (CylindricalPoint p2) = p1.height == p2.height

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // helix generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate a point on a helix.
-- |
-- | Parameters:
-- | - radius: helix radius
-- | - pitch: height gained per full rotation (360°)
-- | - turns: number of turns (can be fractional)
-- |
-- | Returns the point at the given number of turns.
helixPoint :: Number -> Number -> Number -> CylindricalPoint
helixPoint radius pitch turns =
  let angle = Degrees (turns * 360.0)
      height = turns * pitch
  in CylindricalPoint { radius: radius, angle: angle, height: height }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format cylindrical point for display.
showCylindrical :: CylindricalPoint -> String
showCylindrical (CylindricalPoint p) =
  let Degrees d = p.angle
  in "Cylindrical { r: " <> show p.radius 
     <> ", θ: " <> show d <> "°"
     <> ", z: " <> show p.height <> " }"
