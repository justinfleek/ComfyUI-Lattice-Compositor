-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // geometry // ellipse
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Ellipse — 2D ellipse primitive for shapes and hit testing.
-- |
-- | ## Design Philosophy
-- |
-- | An ellipse is defined by center, semi-axes (rx, ry), and rotation.
-- | When rx = ry, it degenerates to a circle.
-- |
-- | This module provides:
-- | - Construction with validation (positive radii)
-- | - Geometric queries (containment, foci)
-- | - Measurements (circumference approximation, area)
-- | - Eccentricity for shape classification
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Geometry.Point (Point2D)
-- | - Hydrogen.Schema.Geometry.Angle (Degrees)
-- | - Data.Number (sqrt, pi, cos, sin)
-- |
-- | ## Dependents
-- |
-- | - SVG ellipse rendering
-- | - Orbital mechanics
-- | - UI rounded containers

module Hydrogen.Schema.Geometry.Ellipse
  ( -- * Ellipse Type
    Ellipse(Ellipse)
  , mkEllipse
  , mkEllipseUnsafe
  , ellipseCenter
  , ellipseRadiusX
  , ellipseRadiusY
  , ellipseRotation
  
  -- * Measurements
  , area
  , circumferenceApprox
  , semiMajor
  , semiMinor
  
  -- * Geometric Properties
  , eccentricity
  , foci
  , focalDistance
  , isCircle
  
  -- * Point Operations
  , contains
  , pointAtAngle
  
  -- * Transformations
  , translateEllipse
  , scaleEllipse
  , rotateEllipse
  
  -- * Conversion
  , fromCircle
  
  -- * Comparison
  , ellipsesEqual
  , compareByArea
  , containsEither
  
  -- * Display
  , showEllipse
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
  , (==)
  , compare
  , show
  , negate
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (sqrt, pi, cos, sin)
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Schema.Geometry.Point 
  ( Point2D(Point2D)
  , point2D
  , getX
  , getY
  , translate2D
  )

import Hydrogen.Schema.Geometry.Angle
  ( Degrees(Degrees)
  , toRadians
  , unwrapRadians
  , addAngle
  )

import Hydrogen.Schema.Geometry.Circle as Circle

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // ellipse type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ellipse molecule.
-- |
-- | An ellipse defined by center, semi-axes (rx, ry), and rotation angle.
-- | Semi-axes are guaranteed positive via smart constructor.
-- | Rotation is measured counter-clockwise from the positive X-axis.
newtype Ellipse = Ellipse
  { center :: Point2D
  , rx :: Number       -- ^ Semi-axis in X direction (before rotation)
  , ry :: Number       -- ^ Semi-axis in Y direction (before rotation)
  , rotation :: Degrees
  }

derive instance eqEllipse :: Eq Ellipse
derive instance ordEllipse :: Ord Ellipse

instance showEllipseInstance :: Show Ellipse where
  show (Ellipse e) = "(Ellipse " <> show e.center <> " " <> show e.rx <> " " <> show e.ry <> " " <> show e.rotation <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an ellipse with validation.
-- |
-- | Returns Nothing if either radius is not positive.
mkEllipse :: Point2D -> Number -> Number -> Degrees -> Maybe Ellipse
mkEllipse center rx ry rotation =
  if rx > 0.0 && ry > 0.0
  then Just (Ellipse { center, rx, ry, rotation })
  else Nothing

-- | Create an ellipse without validation.
-- |
-- | WARNING: Only use when radii are known to be positive.
mkEllipseUnsafe :: Point2D -> Number -> Number -> Degrees -> Ellipse
mkEllipseUnsafe center rx ry rotation = Ellipse { center, rx, ry, rotation }

-- | Get the center point.
ellipseCenter :: Ellipse -> Point2D
ellipseCenter (Ellipse e) = e.center

-- | Get the X semi-axis radius.
ellipseRadiusX :: Ellipse -> Number
ellipseRadiusX (Ellipse e) = e.rx

-- | Get the Y semi-axis radius.
ellipseRadiusY :: Ellipse -> Number
ellipseRadiusY (Ellipse e) = e.ry

-- | Get the rotation angle.
ellipseRotation :: Ellipse -> Degrees
ellipseRotation (Ellipse e) = e.rotation

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // measurements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Area of the ellipse.
-- |
-- | A = π × rx × ry
area :: Ellipse -> Number
area (Ellipse e) = pi * e.rx * e.ry

-- | Approximate circumference using Ramanujan's formula.
-- |
-- | This is accurate to within 0.005% for all ellipses.
-- | C ≈ π × (3(a+b) - √((3a+b)(a+3b)))
circumferenceApprox :: Ellipse -> Number
circumferenceApprox el =
  let a = semiMajor el
      b = semiMinor el
      term1 = 3.0 * (a + b)
      term2 = sqrt ((3.0 * a + b) * (a + 3.0 * b))
  in pi * (term1 - term2)

-- | Get the semi-major axis (larger radius).
semiMajor :: Ellipse -> Number
semiMajor (Ellipse e) = if e.rx >= e.ry then e.rx else e.ry

-- | Get the semi-minor axis (smaller radius).
semiMinor :: Ellipse -> Number
semiMinor (Ellipse e) = if e.rx <= e.ry then e.rx else e.ry

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // geometric properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Eccentricity of the ellipse.
-- |
-- | e = √(1 - (b²/a²)) where a is semi-major, b is semi-minor.
-- | Returns 0 for circles, approaches 1 for very elongated ellipses.
eccentricity :: Ellipse -> Number
eccentricity el =
  let a = semiMajor el
      b = semiMinor el
      ratio = (b * b) / (a * a)
  in sqrt (1.0 - ratio)

-- | Distance from center to each focus.
-- |
-- | c = √(a² - b²) where a is semi-major, b is semi-minor.
focalDistance :: Ellipse -> Number
focalDistance el =
  let a = semiMajor el
      b = semiMinor el
  in sqrt (a * a - b * b)

-- | Get both foci of the ellipse.
-- |
-- | Returns (focus1, focus2) along the major axis.
-- | Accounts for ellipse rotation.
foci :: Ellipse -> Tuple Point2D Point2D
foci el@(Ellipse e) =
  let c = focalDistance el
      rot = unwrapRadians (toRadians e.rotation)
      cx = getX e.center
      cy = getY e.center
      -- Foci are along the major axis direction
      -- If rx > ry, major axis is along rotated X; else along rotated Y
      dx = if e.rx >= e.ry then c * cos rot else negate (c * sin rot)
      dy = if e.rx >= e.ry then c * sin rot else c * cos rot
      f1 = point2D (cx + dx) (cy + dy)
      f2 = point2D (cx - dx) (cy - dy)
  in Tuple f1 f2

-- | Check if ellipse is effectively a circle.
-- |
-- | Returns true if rx equals ry (within floating-point tolerance).
isCircle :: Ellipse -> Boolean
isCircle (Ellipse e) =
  let diff = if e.rx > e.ry then e.rx - e.ry else e.ry - e.rx
  in diff < 1.0e-10

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // point operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a point is inside or on the ellipse.
-- |
-- | Uses the ellipse equation: (x'/rx)² + (y'/ry)² <= 1
-- | where (x', y') is the point transformed to ellipse-local coordinates.
contains :: Point2D -> Ellipse -> Boolean
contains (Point2D p) (Ellipse e) =
  let Point2D center = e.center
      -- Translate to center
      dx = p.x - center.x
      dy = p.y - center.y
      -- Rotate to align with ellipse axes (inverse rotation)
      rot = negate (unwrapRadians (toRadians e.rotation))
      cosR = cos rot
      sinR = sin rot
      x' = dx * cosR - dy * sinR
      y' = dx * sinR + dy * cosR
      -- Normalized coordinates
      nx = x' / e.rx
      ny = y' / e.ry
  in nx * nx + ny * ny <= 1.0

-- | Get point on ellipse boundary at given angle.
-- |
-- | Angle is measured from the rotated major axis.
pointAtAngle :: Degrees -> Ellipse -> Point2D
pointAtAngle angle (Ellipse e) =
  let a = unwrapRadians (toRadians angle)
      rot = unwrapRadians (toRadians e.rotation)
      -- Point on unrotated ellipse
      x' = e.rx * cos a
      y' = e.ry * sin a
      -- Apply ellipse rotation
      cosR = cos rot
      sinR = sin rot
      x = x' * cosR - y' * sinR
      y = x' * sinR + y' * cosR
      cx = getX e.center
      cy = getY e.center
  in point2D (cx + x) (cy + y)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transformations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translate ellipse by offset.
translateEllipse :: Number -> Number -> Ellipse -> Ellipse
translateEllipse dx dy (Ellipse e) =
  Ellipse { center: translate2D dx dy e.center
          , rx: e.rx
          , ry: e.ry
          , rotation: e.rotation
          }

-- | Scale ellipse radii uniformly.
-- |
-- | Returns Nothing if factor is not positive.
scaleEllipse :: Number -> Ellipse -> Maybe Ellipse
scaleEllipse factor (Ellipse e)
  | factor > 0.0 = Just (Ellipse
      { center: e.center
      , rx: e.rx * factor
      , ry: e.ry * factor
      , rotation: e.rotation
      })
  | true = Nothing

-- | Rotate ellipse by additional angle.
rotateEllipse :: Degrees -> Ellipse -> Ellipse
rotateEllipse angle (Ellipse e) =
  Ellipse { center: e.center
          , rx: e.rx
          , ry: e.ry
          , rotation: addAngle e.rotation angle
          }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an ellipse from a circle.
-- |
-- | The resulting ellipse has equal radii and zero rotation.
fromCircle :: Circle.Circle -> Ellipse
fromCircle c =
  Ellipse { center: Circle.circleCenter c
          , rx: Circle.circleRadius c
          , ry: Circle.circleRadius c
          , rotation: Degrees 0.0
          }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format ellipse for display.
-- |
-- | Provides a more verbose format than the Show instance.
showEllipse :: Ellipse -> String
showEllipse (Ellipse e) =
  let Point2D center = e.center
      Degrees rot = e.rotation
  in "Ellipse { center: (" <> show center.x <> ", " <> show center.y 
     <> "), rx: " <> show e.rx 
     <> ", ry: " <> show e.ry 
     <> ", rotation: " <> show rot <> "° }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two ellipses are equal.
-- |
-- | Compares center, radii, and rotation.
-- | Note: Derived Eq instance exists; this is for explicit comparison.
ellipsesEqual :: Ellipse -> Ellipse -> Boolean
ellipsesEqual (Ellipse e1) (Ellipse e2) =
  let Point2D c1 = e1.center
      Point2D c2 = e2.center
      Degrees r1 = e1.rotation
      Degrees r2 = e2.rotation
  in c1.x == c2.x && c1.y == c2.y 
     && e1.rx == e2.rx && e1.ry == e2.ry
     && r1 == r2

-- | Compare ellipses by area.
-- |
-- | Useful for sorting ellipses by size.
compareByArea :: Ellipse -> Ellipse -> Ordering
compareByArea el1 el2 = compare (area el1) (area el2)

-- | Check if a point is inside either of two ellipses.
containsEither :: Point2D -> Ellipse -> Ellipse -> Boolean
containsEither p el1 el2 = contains p el1 || contains p el2
