-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // geometry // arc
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Arc — circular arc segment for paths and pie charts.
-- |
-- | ## Design Philosophy
-- |
-- | An arc is a portion of a circle's circumference, defined by:
-- | - Center point
-- | - Radius
-- | - Start angle
-- | - End angle
-- | - Direction (clockwise or counter-clockwise)
-- |
-- | This module provides:
-- | - Arc construction and validation
-- | - Length calculation
-- | - Point sampling along the arc
-- | - Sector (pie slice) and ring (annulus) variants
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Geometry.Point (Point2D)
-- | - Hydrogen.Schema.Geometry.Angle (Degrees)
-- | - Data.Number (pi, cos, sin)
-- |
-- | ## Dependents
-- |
-- | - SVG arc paths
-- | - Pie charts
-- | - Progress indicators
-- | - Radial menus

module Hydrogen.Schema.Geometry.Arc
  ( -- * Arc Type
    Arc(Arc)
  , mkArc
  , mkArcUnsafe
  , arcCenter
  , arcRadius
  , arcStartAngle
  , arcEndAngle
  , arcDirection
  
  -- * Direction
  , ArcDirection(..)
  
  -- * Measurements
  , arcLength
  , sweepAngle
  , arcArea
  
  -- * Point Operations
  , pointAtParameter
  , startPoint
  , endPoint
  , midPoint
  , containsAngle
  
  -- * Variants
  , Sector(Sector)
  , mkSector
  , sectorArea
  
  , Ring(Ring)
  , mkRing
  , ringArea
  
  -- * Transformations
  , translateArc
  , scaleArc
  , reverseArc
  
  -- * Comparison
  , compareByLength
  
  -- * Display
  , showArc
  
  -- * Angular Operations
  , angularDistance
  , arcLengthRadians
  , reflectArcCenter
  , samplePoints
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
  , map
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (pi, cos, sin, abs)
import Data.Int (toNumber, floor) as Int

import Hydrogen.Schema.Geometry.Point 
  ( Point2D(Point2D)
  , point2D
  , translate2D
  )

import Hydrogen.Schema.Geometry.Angle
  ( Degrees(Degrees)
  , toRadians
  , unwrapRadians
  , unwrapDegrees
  , subtractAngle
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // arc direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Direction of arc traversal.
data ArcDirection
  = Clockwise         -- ^ Sweep in clockwise direction
  | CounterClockwise  -- ^ Sweep in counter-clockwise direction

derive instance eqArcDirection :: Eq ArcDirection
derive instance ordArcDirection :: Ord ArcDirection

instance showArcDirection :: Show ArcDirection where
  show Clockwise = "Clockwise"
  show CounterClockwise = "CounterClockwise"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // arc type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Arc molecule.
-- |
-- | A portion of a circle's circumference.
newtype Arc = Arc
  { center :: Point2D
  , radius :: Number
  , startAngle :: Degrees
  , endAngle :: Degrees
  , direction :: ArcDirection
  }

derive instance eqArc :: Eq Arc
derive instance ordArc :: Ord Arc

instance showArcInstance :: Show Arc where
  show (Arc a) = "(Arc " <> show a.center <> " r=" <> show a.radius 
                 <> " " <> show a.startAngle <> "->" <> show a.endAngle 
                 <> " " <> show a.direction <> ")"

-- | Create an arc with validation.
-- |
-- | Returns Nothing if radius is not positive.
mkArc :: Point2D -> Number -> Degrees -> Degrees -> ArcDirection -> Maybe Arc
mkArc center radius startAngle endAngle direction =
  if radius > 0.0
  then Just (Arc { center, radius, startAngle, endAngle, direction })
  else Nothing

-- | Create an arc without validation.
-- |
-- | WARNING: Only use when radius is known to be positive.
mkArcUnsafe :: Point2D -> Number -> Degrees -> Degrees -> ArcDirection -> Arc
mkArcUnsafe center radius startAngle endAngle direction =
  Arc { center, radius, startAngle, endAngle, direction }

-- | Get the center point.
arcCenter :: Arc -> Point2D
arcCenter (Arc a) = a.center

-- | Get the radius.
arcRadius :: Arc -> Number
arcRadius (Arc a) = a.radius

-- | Get the start angle.
arcStartAngle :: Arc -> Degrees
arcStartAngle (Arc a) = a.startAngle

-- | Get the end angle.
arcEndAngle :: Arc -> Degrees
arcEndAngle (Arc a) = a.endAngle

-- | Get the direction.
arcDirection :: Arc -> ArcDirection
arcDirection (Arc a) = a.direction

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // measurements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate the sweep angle (angular extent) of the arc.
-- |
-- | Always returns a positive value.
sweepAngle :: Arc -> Degrees
sweepAngle (Arc a) =
  let startDeg = unwrapDegrees a.startAngle
      endDeg = unwrapDegrees a.endAngle
      diff = case a.direction of
        CounterClockwise ->
          if endDeg >= startDeg
          then endDeg - startDeg
          else 360.0 - startDeg + endDeg
        Clockwise ->
          if startDeg >= endDeg
          then startDeg - endDeg
          else 360.0 - endDeg + startDeg
  in Degrees diff

-- | Calculate the arc length.
-- |
-- | L = r × θ (where θ is in radians)
arcLength :: Arc -> Number
arcLength arc@(Arc a) =
  let Degrees sweep = sweepAngle arc
      sweepRad = sweep * pi / 180.0
  in a.radius * sweepRad

-- | Calculate the area of the circular sector formed by the arc.
-- |
-- | A = (1/2) × r² × θ
arcArea :: Arc -> Number
arcArea arc@(Arc a) =
  let Degrees sweep = sweepAngle arc
      sweepRad = sweep * pi / 180.0
  in 0.5 * a.radius * a.radius * sweepRad

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // point operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get point on arc at parameter t in [0, 1].
-- |
-- | t=0 is start, t=1 is end.
pointAtParameter :: Number -> Arc -> Point2D
pointAtParameter t (Arc a) =
  let startDeg = unwrapDegrees a.startAngle
      Degrees sweep = sweepAngle (Arc a)
      -- Adjust direction
      angleDeg = case a.direction of
        CounterClockwise -> startDeg + t * sweep
        Clockwise -> startDeg - t * sweep
      angleRad = angleDeg * pi / 180.0
      Point2D center = a.center
      x = center.x + a.radius * cos angleRad
      y = center.y + a.radius * sin angleRad
  in point2D x y

-- | Get the start point of the arc.
startPoint :: Arc -> Point2D
startPoint = pointAtParameter 0.0

-- | Get the end point of the arc.
endPoint :: Arc -> Point2D
endPoint = pointAtParameter 1.0

-- | Get the midpoint of the arc.
midPoint :: Arc -> Point2D
midPoint = pointAtParameter 0.5

-- | Check if an angle falls within the arc's sweep.
containsAngle :: Degrees -> Arc -> Boolean
containsAngle (Degrees angle) (Arc a) =
  let startDeg = unwrapDegrees a.startAngle
      endDeg = unwrapDegrees a.endAngle
      -- Normalize angle to [0, 360)
      normAngle = normalizeAngle angle
      normStart = normalizeAngle startDeg
      normEnd = normalizeAngle endDeg
  in case a.direction of
    CounterClockwise ->
      if normEnd >= normStart
      then normAngle >= normStart && normAngle <= normEnd
      else normAngle >= normStart || normAngle <= normEnd
    Clockwise ->
      if normStart >= normEnd
      then normAngle <= normStart && normAngle >= normEnd
      else normAngle <= normStart || normAngle >= normEnd
  where
    normalizeAngle :: Number -> Number
    normalizeAngle deg =
      let wrapped = deg - 360.0 * Int.toNumber (Int.floor (deg / 360.0))
      in if wrapped < 0.0 then wrapped + 360.0 else wrapped

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sector (pie slice) — arc with lines to center.
-- |
-- | Like a slice of pie, includes the arc and two radii.
newtype Sector = Sector Arc

derive instance eqSector :: Eq Sector
derive instance ordSector :: Ord Sector

instance showSector :: Show Sector where
  show (Sector arc) = "(Sector " <> show arc <> ")"

-- | Create a sector from arc parameters.
mkSector :: Point2D -> Number -> Degrees -> Degrees -> ArcDirection -> Maybe Sector
mkSector center radius startAngle endAngle direction =
  case mkArc center radius startAngle endAngle direction of
    Just arc -> Just (Sector arc)
    Nothing -> Nothing

-- | Area of a sector.
-- |
-- | Same as arcArea — the area of the pie slice.
sectorArea :: Sector -> Number
sectorArea (Sector arc) = arcArea arc

-- | Ring (annulus segment) — arc with inner and outer radii.
-- |
-- | Like a section of a donut.
newtype Ring = Ring
  { center :: Point2D
  , innerRadius :: Number
  , outerRadius :: Number
  , startAngle :: Degrees
  , endAngle :: Degrees
  , direction :: ArcDirection
  }

derive instance eqRing :: Eq Ring
derive instance ordRing :: Ord Ring

instance showRing :: Show Ring where
  show (Ring r) = "(Ring " <> show r.center <> " inner=" <> show r.innerRadius 
                  <> " outer=" <> show r.outerRadius <> ")"

-- | Create a ring with validation.
-- |
-- | Returns Nothing if radii are not positive or inner >= outer.
mkRing :: Point2D -> Number -> Number -> Degrees -> Degrees -> ArcDirection -> Maybe Ring
mkRing center innerRadius outerRadius startAngle endAngle direction =
  if innerRadius > 0.0 && outerRadius > innerRadius
  then Just (Ring { center, innerRadius, outerRadius, startAngle, endAngle, direction })
  else Nothing

-- | Area of a ring segment.
-- |
-- | A = (1/2) × (r_outer² - r_inner²) × θ
ringArea :: Ring -> Number
ringArea (Ring r) =
  let startDeg = unwrapDegrees r.startAngle
      endDeg = unwrapDegrees r.endAngle
      sweep = case r.direction of
        CounterClockwise ->
          if endDeg >= startDeg
          then endDeg - startDeg
          else 360.0 - startDeg + endDeg
        Clockwise ->
          if startDeg >= endDeg
          then startDeg - endDeg
          else 360.0 - endDeg + startDeg
      sweepRad = sweep * pi / 180.0
  in 0.5 * (r.outerRadius * r.outerRadius - r.innerRadius * r.innerRadius) * sweepRad

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transformations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translate arc center by offset.
translateArc :: Number -> Number -> Arc -> Arc
translateArc dx dy (Arc a) =
  Arc { center: translate2D dx dy a.center
      , radius: a.radius
      , startAngle: a.startAngle
      , endAngle: a.endAngle
      , direction: a.direction
      }

-- | Scale arc radius.
-- |
-- | Returns Nothing if factor is not positive.
scaleArc :: Number -> Arc -> Maybe Arc
scaleArc factor (Arc a) =
  if factor > 0.0
  then Just (Arc 
    { center: a.center
    , radius: a.radius * factor
    , startAngle: a.startAngle
    , endAngle: a.endAngle
    , direction: a.direction
    })
  else Nothing

-- | Reverse arc direction.
-- |
-- | Swaps start and end angles, flips direction.
reverseArc :: Arc -> Arc
reverseArc (Arc a) =
  Arc { center: a.center
      , radius: a.radius
      , startAngle: a.endAngle
      , endAngle: a.startAngle
      , direction: flipDirection a.direction
      }
  where
    flipDirection :: ArcDirection -> ArcDirection
    flipDirection Clockwise = CounterClockwise
    flipDirection CounterClockwise = Clockwise

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compare arcs by length.
compareByLength :: Arc -> Arc -> Ordering
compareByLength a1 a2 = compare (arcLength a1) (arcLength a2)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format arc for display.
-- |
-- | Shows center, radius, angles, and direction.
showArc :: Arc -> String
showArc (Arc a) =
  let Degrees startDeg = a.startAngle
      Degrees endDeg = a.endAngle
  in "Arc { center: " <> show a.center 
     <> ", radius: " <> show a.radius 
     <> ", " <> show startDeg <> "° -> " <> show endDeg <> "°"
     <> ", " <> show a.direction <> " }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // angular operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Angular distance between two angles (shortest path).
-- |
-- | Uses subtractAngle and abs to find the smallest difference.
angularDistance :: Degrees -> Degrees -> Degrees
angularDistance a b =
  let diff = subtractAngle a b
      Degrees d = diff
      normalized = abs d
  in if normalized > 180.0 then Degrees (360.0 - normalized) else Degrees normalized

-- | Get the arc length in radians.
-- |
-- | Uses toRadians for conversion.
arcLengthRadians :: Arc -> Number
arcLengthRadians arc@(Arc a) =
  let Degrees sweep = sweepAngle arc
      sweepRad = unwrapRadians (toRadians (Degrees sweep))
  in a.radius * sweepRad

-- | Reflect arc across its center (negate the center offset).
-- |
-- | Useful for mirroring arcs.
reflectArcCenter :: Arc -> Arc
reflectArcCenter (Arc a) =
  let Point2D center = a.center
  in Arc { center: point2D (negate center.x) (negate center.y)
         , radius: a.radius
         , startAngle: a.startAngle
         , endAngle: a.endAngle
         , direction: a.direction
         }

-- | Sample multiple points along the arc.
-- |
-- | Returns n evenly-spaced points from start to end.
-- | Uses floor for integer division.
samplePoints :: Int -> Arc -> Array Point2D
samplePoints n arc =
  if n <= 1
  then [pointAtParameter 0.5 arc]
  else map (\i -> pointAtParameter (Int.toNumber i / Int.toNumber (n - 1)) arc) (range 0 (n - 1))
  where
    range :: Int -> Int -> Array Int
    range start end = rangeHelper start end []
    
    rangeHelper :: Int -> Int -> Array Int -> Array Int
    rangeHelper cur end acc =
      if cur > end
      then acc
      else rangeHelper (cur + 1) end (snoc acc cur)
    
    snoc :: forall a. Array a -> a -> Array a
    snoc arr x = arr <> [x]
