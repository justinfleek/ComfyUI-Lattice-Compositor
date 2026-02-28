-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // geometry // spherical
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spherical — 3D spherical coordinate system (radius, theta, phi).
-- |
-- | ## Design Philosophy
-- |
-- | Spherical coordinates represent 3D points as (radius, theta, phi):
-- | - **radius**: distance from origin (non-negative)
-- | - **theta**: azimuthal angle in XY plane from positive X-axis [0, 360°)
-- | - **phi**: polar/elevation angle from positive Z-axis [0, 180°]
-- |
-- | This is the physics/math convention (ISO 31-11). Note that some systems
-- | swap theta and phi or measure phi from the XY plane — we use the ISO standard.
-- |
-- | This is the natural coordinate system for:
-- | - 3D camera orbiting
-- | - Globe/earth coordinates (with phi measured from equator)
-- | - Omnidirectional sound/light sources
-- | - Particle systems with spherical emission
-- |
-- | ## Conversion
-- |
-- | ```purescript
-- | -- Cartesian (x, y, z) to Spherical (r, θ, φ)
-- | r = sqrt(x² + y² + z²)
-- | θ = atan2(y, x)
-- | φ = acos(z / r)
-- |
-- | -- Spherical (r, θ, φ) to Cartesian (x, y, z)
-- | x = r * sin(φ) * cos(θ)
-- | y = r * sin(φ) * sin(θ)
-- | z = r * cos(φ)
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Geometry.Point (Point3D)
-- | - Hydrogen.Schema.Geometry.Angle (Degrees)
-- | - Data.Number (sqrt, cos, sin, acos, atan2)
-- |
-- | ## Dependents
-- |
-- | - 3D camera controls (orbit camera)
-- | - Globe visualization
-- | - Skybox/environment mapping

module Hydrogen.Schema.Geometry.Spherical
  ( -- * SphericalPoint Type
    SphericalPoint(SphericalPoint)
  , mkSphericalPoint
  , mkSphericalPointUnsafe
  , sphericalRadius
  , sphericalTheta
  , sphericalPhi
  
  -- * Conversions
  , toCartesian
  , fromCartesian
  , toLatLon
  , fromLatLon
  
  -- * Operations
  , rotateTheta
  , rotatePhi
  , scaleSpherical
  , translateRadial
  , mirrorTheta
  , mirrorPhi
  
  -- * Common Points
  , sphericalOrigin
  , northPole
  , southPole
  
  -- * Interpolation
  , lerpSpherical
  , slerp
  
  -- * Comparison
  , sphericalDistance
  , sphericalDistanceSquared
  , greatCircleDistance
  , sameRadius
  , sameTheta
  , samePhi
  
  -- * Surface Sampling
  , fibonacciSphere
  
  -- * Display
  , showSpherical
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
  , (<=)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (==)
  , (&&)
  , map
  )

import Data.Array (snoc)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (sqrt, cos, sin, acos, atan2, pi)
import Data.Int (toNumber)

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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // spherical point type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spherical coordinate point.
-- |
-- | - radius: non-negative distance from origin
-- | - theta: azimuthal angle in XY plane [0, 360°)
-- | - phi: polar angle from positive Z-axis [0, 180°]
newtype SphericalPoint = SphericalPoint
  { radius :: Number
  , theta :: Degrees   -- ^ Azimuthal angle (around Z-axis)
  , phi :: Degrees     -- ^ Polar angle (from Z-axis)
  }

derive instance eqSphericalPoint :: Eq SphericalPoint
derive instance ordSphericalPoint :: Ord SphericalPoint

instance showSphericalPointInstance :: Show SphericalPoint where
  show (SphericalPoint p) = 
    "(SphericalPoint r=" <> show p.radius 
    <> " θ=" <> show p.theta 
    <> " φ=" <> show p.phi <> ")"

-- | Create a spherical point with validation.
-- |
-- | Returns Nothing if radius is negative or phi is outside [0, 180].
mkSphericalPoint :: Number -> Degrees -> Degrees -> Maybe SphericalPoint
mkSphericalPoint r theta phi =
  let Degrees phiDeg = phi
  in if r >= 0.0 && phiDeg >= 0.0 && phiDeg <= 180.0
     then Just (SphericalPoint { radius: r, theta: normalizeTheta theta, phi: phi })
     else Nothing
  where
    normalizeTheta :: Degrees -> Degrees
    normalizeTheta (Degrees d) =
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

-- | Create a spherical point without validation.
-- |
-- | WARNING: Only use when radius >= 0 and phi in [0, 180].
mkSphericalPointUnsafe :: Number -> Degrees -> Degrees -> SphericalPoint
mkSphericalPointUnsafe r theta phi = 
  SphericalPoint { radius: r, theta: theta, phi: phi }

-- | Get the radius component.
sphericalRadius :: SphericalPoint -> Number
sphericalRadius (SphericalPoint p) = p.radius

-- | Get the theta (azimuthal) angle.
sphericalTheta :: SphericalPoint -> Degrees
sphericalTheta (SphericalPoint p) = p.theta

-- | Get the phi (polar) angle.
sphericalPhi :: SphericalPoint -> Degrees
sphericalPhi (SphericalPoint p) = p.phi

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert spherical coordinates to Cartesian.
-- |
-- | x = r * sin(φ) * cos(θ)
-- | y = r * sin(φ) * sin(θ)
-- | z = r * cos(φ)
toCartesian :: SphericalPoint -> Point3D
toCartesian (SphericalPoint p) =
  let thetaRad = unwrapRadians (toRadians p.theta)
      phiRad = unwrapRadians (toRadians p.phi)
      sinPhi = sin phiRad
      x = p.radius * sinPhi * cos thetaRad
      y = p.radius * sinPhi * sin thetaRad
      z = p.radius * cos phiRad
  in point3D x y z

-- | Convert Cartesian coordinates to spherical.
-- |
-- | r = sqrt(x² + y² + z²)
-- | θ = atan2(y, x)
-- | φ = acos(z / r)
fromCartesian :: Point3D -> SphericalPoint
fromCartesian pt =
  let x = getX3 pt
      y = getY3 pt
      z = getZ3 pt
      r = sqrt (x * x + y * y + z * z)
  in if r == 0.0
     then SphericalPoint { radius: 0.0, theta: Degrees 0.0, phi: Degrees 0.0 }
     else
       let thetaDeg = atan2 y x * 180.0 / pi
           thetaNorm = if thetaDeg < 0.0 then thetaDeg + 360.0 else thetaDeg
           phiDeg = acos (z / r) * 180.0 / pi
       in SphericalPoint { radius: r, theta: Degrees thetaNorm, phi: Degrees phiDeg }

-- | Convert to latitude/longitude style coordinates.
-- |
-- | Returns (latitude, longitude) where:
-- | - latitude: -90 to 90 (measured from equator, positive = north)
-- | - longitude: -180 to 180 (measured from prime meridian)
toLatLon :: SphericalPoint -> { latitude :: Number, longitude :: Number }
toLatLon (SphericalPoint p) =
  let Degrees phiDeg = p.phi
      Degrees thetaDeg = p.theta
      -- phi = 0 is north pole (+90 lat), phi = 90 is equator (0 lat), phi = 180 is south pole (-90 lat)
      latitude = 90.0 - phiDeg
      -- theta to longitude: theta = 0 -> lon = 0, theta = 180 -> lon = 180 or -180
      longitude = if thetaDeg > 180.0 then thetaDeg - 360.0 else thetaDeg
  in { latitude, longitude }

-- | Convert from latitude/longitude to spherical coordinates.
-- |
-- | Assumes unit sphere (radius = 1).
fromLatLon :: Number -> Number -> SphericalPoint
fromLatLon latitude longitude =
  let phi = 90.0 - latitude
      theta = if longitude < 0.0 then longitude + 360.0 else longitude
  in SphericalPoint { radius: 1.0, theta: Degrees theta, phi: Degrees phi }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotate around the Z-axis (change theta).
rotateTheta :: Degrees -> SphericalPoint -> SphericalPoint
rotateTheta delta (SphericalPoint p) =
  SphericalPoint { radius: p.radius, theta: addAngle p.theta delta, phi: p.phi }

-- | Rotate toward/away from Z-axis (change phi).
-- |
-- | Clamps phi to [0, 180].
rotatePhi :: Degrees -> SphericalPoint -> SphericalPoint
rotatePhi delta (SphericalPoint p) =
  let Degrees currentPhi = p.phi
      Degrees deltaDeg = delta
      newPhi = currentPhi + deltaDeg
      clampedPhi = if newPhi < 0.0 then 0.0 else if newPhi > 180.0 then 180.0 else newPhi
  in SphericalPoint { radius: p.radius, theta: p.theta, phi: Degrees clampedPhi }

-- | Scale the radius.
-- |
-- | Negative factors are treated as zero.
scaleSpherical :: Number -> SphericalPoint -> SphericalPoint
scaleSpherical factor (SphericalPoint p) =
  let newRadius = if factor < 0.0 then 0.0 else p.radius * factor
  in SphericalPoint { radius: newRadius, theta: p.theta, phi: p.phi }

-- | Translate along the radial direction.
-- |
-- | Clamps to zero if result would be negative.
translateRadial :: Number -> SphericalPoint -> SphericalPoint
translateRadial delta (SphericalPoint p) =
  let newRadius = p.radius + delta
  in SphericalPoint 
    { radius: if newRadius < 0.0 then 0.0 else newRadius
    , theta: p.theta
    , phi: p.phi
    }

-- | Mirror across a plane containing the Z-axis (negate theta).
mirrorTheta :: SphericalPoint -> SphericalPoint
mirrorTheta (SphericalPoint p) =
  let Degrees d = p.theta
      mirrored = if d == 0.0 then 0.0 else 360.0 - d
  in SphericalPoint { radius: p.radius, theta: Degrees mirrored, phi: p.phi }

-- | Mirror across the XY plane (reflect phi across 90°).
mirrorPhi :: SphericalPoint -> SphericalPoint
mirrorPhi (SphericalPoint p) =
  let Degrees phiDeg = p.phi
      mirrored = 180.0 - phiDeg
  in SphericalPoint { radius: p.radius, theta: p.theta, phi: Degrees mirrored }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // common points
-- ═════════════════════════════════════════════════════════════════════════════

-- | Origin in spherical coordinates.
sphericalOrigin :: SphericalPoint
sphericalOrigin = SphericalPoint { radius: 0.0, theta: Degrees 0.0, phi: Degrees 0.0 }

-- | Unit north pole (positive Z-axis).
northPole :: SphericalPoint
northPole = SphericalPoint { radius: 1.0, theta: Degrees 0.0, phi: Degrees 0.0 }

-- | Unit south pole (negative Z-axis).
southPole :: SphericalPoint
southPole = SphericalPoint { radius: 1.0, theta: Degrees 0.0, phi: Degrees 180.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation between spherical points.
-- |
-- | Interpolates each component independently.
-- | For great circle interpolation on a sphere, use `slerp`.
lerpSpherical :: Number -> SphericalPoint -> SphericalPoint -> SphericalPoint
lerpSpherical t (SphericalPoint p1) (SphericalPoint p2) =
  let r = p1.radius + t * (p2.radius - p1.radius)
      theta = lerpAngle t p1.theta p2.theta
      Degrees phi1 = p1.phi
      Degrees phi2 = p2.phi
      phi = phi1 + t * (phi2 - phi1)
  in SphericalPoint { radius: r, theta: theta, phi: Degrees phi }

-- | Spherical linear interpolation (slerp).
-- |
-- | Interpolates along the great circle connecting two points on a sphere.
-- | Assumes both points are at the same radius.
slerp :: Number -> SphericalPoint -> SphericalPoint -> SphericalPoint
slerp t sp1 sp2 =
  let p1 = toCartesian sp1
      p2 = toCartesian sp2
      -- Normalize to unit sphere
      r = (sphericalRadius sp1 + sphericalRadius sp2) / 2.0
      -- Dot product for angle
      dot = getX3 p1 * getX3 p2 + getY3 p1 * getY3 p2 + getZ3 p1 * getZ3 p2
      -- Clamp to avoid acos domain errors
      dotClamped = if dot < negate 1.0 then negate 1.0 else if dot > 1.0 then 1.0 else dot
      omega = acos dotClamped
  in if omega < 0.0001
     -- Points are nearly identical, use linear interpolation
     then lerpSpherical t sp1 sp2
     else
       let sinOmega = sin omega
           a = sin ((1.0 - t) * omega) / sinOmega
           b = sin (t * omega) / sinOmega
           x = a * getX3 p1 + b * getX3 p2
           y = a * getY3 p1 + b * getY3 p2
           z = a * getZ3 p1 + b * getZ3 p2
           result = fromCartesian (point3D x y z)
       in SphericalPoint 
            { radius: r
            , theta: sphericalTheta result
            , phi: sphericalPhi result
            }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Squared distance between two spherical points in Cartesian space.
sphericalDistanceSquared :: SphericalPoint -> SphericalPoint -> Number
sphericalDistanceSquared p1 p2 =
  let c1 = toCartesian p1
      c2 = toCartesian p2
      dx = getX3 c2 - getX3 c1
      dy = getY3 c2 - getY3 c1
      dz = getZ3 c2 - getZ3 c1
  in dx * dx + dy * dy + dz * dz

-- | Distance between two spherical points in Cartesian space.
sphericalDistance :: SphericalPoint -> SphericalPoint -> Number
sphericalDistance p1 p2 = sqrt (sphericalDistanceSquared p1 p2)

-- | Great circle distance between two points on a sphere.
-- |
-- | Returns the arc length along the sphere's surface.
-- | Uses the Haversine formula for numerical stability.
greatCircleDistance :: SphericalPoint -> SphericalPoint -> Number
greatCircleDistance sp1 sp2 =
  let r = (sphericalRadius sp1 + sphericalRadius sp2) / 2.0
      p1 = toCartesian sp1
      p2 = toCartesian sp2
      -- Normalize
      d1 = sqrt (getX3 p1 * getX3 p1 + getY3 p1 * getY3 p1 + getZ3 p1 * getZ3 p1)
      d2 = sqrt (getX3 p2 * getX3 p2 + getY3 p2 * getY3 p2 + getZ3 p2 * getZ3 p2)
      n1x = if d1 > 0.0 then getX3 p1 / d1 else 0.0
      n1y = if d1 > 0.0 then getY3 p1 / d1 else 0.0
      n1z = if d1 > 0.0 then getZ3 p1 / d1 else 0.0
      n2x = if d2 > 0.0 then getX3 p2 / d2 else 0.0
      n2y = if d2 > 0.0 then getY3 p2 / d2 else 0.0
      n2z = if d2 > 0.0 then getZ3 p2 / d2 else 0.0
      -- Central angle
      dot = n1x * n2x + n1y * n2y + n1z * n2z
      dotClamped = if dot < negate 1.0 then negate 1.0 else if dot > 1.0 then 1.0 else dot
      centralAngle = acos dotClamped
  in r * centralAngle

-- | Check if two points have the same radius.
sameRadius :: SphericalPoint -> SphericalPoint -> Boolean
sameRadius (SphericalPoint p1) (SphericalPoint p2) = p1.radius == p2.radius

-- | Check if two points have the same theta (azimuthal angle).
sameTheta :: SphericalPoint -> SphericalPoint -> Boolean
sameTheta (SphericalPoint p1) (SphericalPoint p2) = p1.theta == p2.theta

-- | Check if two points have the same phi (polar angle).
samePhi :: SphericalPoint -> SphericalPoint -> Boolean
samePhi (SphericalPoint p1) (SphericalPoint p2) = p1.phi == p2.phi

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // surface sampling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate evenly distributed points on a sphere using Fibonacci spiral.
-- |
-- | This produces a nearly-uniform distribution of n points on a unit sphere.
-- | Useful for environment sampling, particle distribution, etc.
fibonacciSphere :: Int -> Array SphericalPoint
fibonacciSphere n =
  let goldenRatio = (1.0 + sqrt 5.0) / 2.0
      goldenAngle = 2.0 * pi / (goldenRatio * goldenRatio)
      nFloat = toNumber n
      makePoint i =
        let iFloat = toNumber i
            -- y goes from 1 to -1
            y = 1.0 - (iFloat / (nFloat - 1.0)) * 2.0
            -- radius at this height
            radiusAtY = sqrt (1.0 - y * y)
            -- theta increases by golden angle
            theta = iFloat * goldenAngle
            -- convert to our coordinate system
            x = cos theta * radiusAtY
            z = sin theta * radiusAtY
        in fromCartesian (point3D x z y)  -- Note: swapping y and z for our convention
  in map makePoint (range 0 (n - 1))
  where
    range :: Int -> Int -> Array Int
    range start end = rangeHelper start end []
    
    rangeHelper :: Int -> Int -> Array Int -> Array Int
    rangeHelper cur end acc
      | cur > end = acc
      | otherwise = rangeHelper (cur + 1) end (snoc acc cur)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format spherical point for display.
showSpherical :: SphericalPoint -> String
showSpherical (SphericalPoint p) =
  let Degrees thetaDeg = p.theta
      Degrees phiDeg = p.phi
  in "Spherical { r: " <> show p.radius 
     <> ", θ: " <> show thetaDeg <> "°"
     <> ", φ: " <> show phiDeg <> "° }"
