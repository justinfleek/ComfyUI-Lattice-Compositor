-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // geometry // star
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Star — radial shape with alternating outer and inner vertices.
-- |
-- | ## Design Philosophy
-- |
-- | A star is defined by:
-- | - Number of points (rays/spikes)
-- | - Outer radius (tips of the star)
-- | - Inner radius (valleys between tips)
-- | - Center point
-- | - Rotation angle (orientation of first point)
-- |
-- | Stars are rendered as polygons with 2n vertices where n is the point count.
-- | Vertices alternate between outer radius (tips) and inner radius (valleys).
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Geometry.Point (Point2D)
-- | - Hydrogen.Schema.Geometry.Angle (Degrees, Radians)
-- | - Hydrogen.Schema.Geometry.Polygon (Polygon, for conversion)
-- |
-- | ## Dependents
-- |
-- | - Icon systems (star ratings)
-- | - Decorative elements
-- | - Badge and seal designs
-- | - Game graphics

module Hydrogen.Schema.Geometry.Star
  ( -- * Star Type
    Star(Star)
  , mkStar
  , points
  , outerRadius
  , innerRadius
  , center
  , rotation
  
  -- * Constructors
  , fivePointStar
  , sixPointStar
  , davidStar
  , eightPointStar
  , burstStar
  
  -- * Computed Properties
  , vertexCount
  , tipAngle
  , valleyAngle
  , innerToOuterRatio
  
  -- * Vertex Generation
  , vertices
  , outerVertices
  , innerVertices
  
  -- * Measurements
  , boundingRadius
  , approximateArea
  , approximatePerimeter
  
  -- * Transformations
  , translateStar
  , scaleStar
  , rotateStar
  , setInnerRadius
  , setOuterRadius
  
  -- * Conversion
  , toPolygon
  
  -- * Comparison
  , compareByPoints
  , compareByOuterRadius
  , samePointCount
  
  -- * Display
  , showStar
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
  , (<)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (==)
  , compare
  , show
  , otherwise
  , negate
  )

import Data.Array (snoc, length, foldl, (!!))
import Data.Int (toNumber)
import Data.Maybe (fromMaybe)
import Data.Number (pi, cos, sin, sqrt)

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
  )

import Hydrogen.Schema.Geometry.Polygon
  ( Polygon
  , mkPolygonUnsafe
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // star type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Star molecule.
-- |
-- | A radial shape with alternating outer tips and inner valleys.
-- | Defined by point count, radii, center, and rotation.
-- |
-- | Invariants:
-- | - points >= 3 (minimum for a recognizable star)
-- | - outerRadius > innerRadius > 0
-- | - When innerRadius = 0, star degenerates to a regular polygon
newtype Star = Star
  { points :: Int           -- ^ Number of star points (tips)
  , outerRadius :: Number   -- ^ Distance from center to tips
  , innerRadius :: Number   -- ^ Distance from center to valleys
  , center :: Point2D       -- ^ Center of the star
  , rotation :: Degrees     -- ^ Rotation of first tip from +X axis
  }

derive instance eqStar :: Eq Star
derive instance ordStar :: Ord Star

instance showStarInstance :: Show Star where
  show (Star s) = "(Star " <> show s <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a star with validation.
-- |
-- | Ensures:
-- | - At least 3 points
-- | - Positive radii
-- | - Outer radius > inner radius
mkStar :: Int -> Number -> Number -> Point2D -> Degrees -> Star
mkStar pts outer inner ctr rot =
  let
    validPoints = if pts < 3 then 3 else pts
    validOuter = if outer < 0.0 then 1.0 else outer
    validInner = if inner < 0.0 then 0.0 else if inner >= validOuter then validOuter * 0.5 else inner
  in
    Star
      { points: validPoints
      , outerRadius: validOuter
      , innerRadius: validInner
      , center: ctr
      , rotation: rot
      }

-- | Extract the number of points from a star.
points :: Star -> Int
points (Star s) = s.points

-- | Extract the outer radius.
outerRadius :: Star -> Number
outerRadius (Star s) = s.outerRadius

-- | Extract the inner radius.
innerRadius :: Star -> Number
innerRadius (Star s) = s.innerRadius

-- | Extract the center point.
center :: Star -> Point2D
center (Star s) = s.center

-- | Extract the rotation angle.
rotation :: Star -> Degrees
rotation (Star s) = s.rotation

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // preset constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Classic 5-pointed star (pentagram proportions).
-- |
-- | Inner radius is approximately 0.382 of outer radius (golden ratio related).
-- | First point at top (-90° from +X axis).
fivePointStar :: Point2D -> Number -> Star
fivePointStar ctr radius =
  mkStar 5 radius (radius * 0.382) ctr (Degrees (-90.0))

-- | Six-pointed star (hexagram).
-- |
-- | Inner radius creates the classic Star of David proportions.
-- | First point at top.
sixPointStar :: Point2D -> Number -> Star
sixPointStar ctr radius =
  mkStar 6 radius (radius * 0.5) ctr (Degrees (-90.0))

-- | Star of David (alias for sixPointStar).
-- |
-- | Traditional hexagram with specific inner/outer ratio.
davidStar :: Point2D -> Number -> Star
davidStar = sixPointStar

-- | Eight-pointed star.
-- |
-- | Common in Islamic geometric patterns and compass roses.
eightPointStar :: Point2D -> Number -> Star
eightPointStar ctr radius =
  mkStar 8 radius (radius * 0.4) ctr (Degrees (-90.0))

-- | Burst star with many thin points.
-- |
-- | Creates a sunburst or starburst effect.
-- | Small inner radius creates sharp, needle-like points.
burstStar :: Int -> Point2D -> Number -> Star
burstStar numPoints ctr radius =
  let pts = if numPoints < 8 then 8 else numPoints
  in mkStar pts radius (radius * 0.2) ctr (Degrees 0.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // computed properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Total number of vertices in the star polygon.
-- |
-- | A star with n points has 2n vertices (alternating outer/inner).
vertexCount :: Star -> Int
vertexCount (Star s) = s.points * 2

-- | Angle at each tip of the star.
-- |
-- | Sharper tips have smaller angles.
-- | Computed from the geometry of the star.
tipAngle :: Star -> Degrees
tipAngle (Star s) =
  let
    n = toNumber s.points
    halfPointAngle = pi / n  -- Half the angle between adjacent tips
    -- Use law of cosines in the triangle formed by tip, center, and valley
    -- The tip angle depends on the ratio of inner to outer radius
    r = s.innerRadius / s.outerRadius
    -- Approximate tip angle using atan2-based calculation
    -- For a proper calculation, we'd need the actual vertex positions
    -- Here we use a simplified geometric relationship
    tipRad = 2.0 * halfPointAngle * (1.0 - r)
    tipDeg = tipRad * 180.0 / pi
  in
    Degrees tipDeg

-- | Angle at each valley of the star.
-- |
-- | Wider valleys have larger angles.
valleyAngle :: Star -> Degrees
valleyAngle star =
  let
    n = toNumber (points star)
    -- Sum of angles in a polygon with 2n vertices
    interiorSum = (2.0 * n - 2.0) * 180.0
    Degrees tipDeg = tipAngle star
    -- Valley angles = total - tip angles, distributed among n valleys
    valleyDeg = (interiorSum - n * tipDeg) / n
  in
    Degrees valleyDeg

-- | Ratio of inner radius to outer radius.
-- |
-- | Range: 0.0 (degenerate) to 1.0 (approaches regular polygon).
-- | Common values: 0.382 (golden), 0.5 (hexagram), 0.2 (burst).
innerToOuterRatio :: Star -> Number
innerToOuterRatio (Star s) = s.innerRadius / s.outerRadius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // vertex generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate all vertices of the star.
-- |
-- | Returns 2n vertices alternating between outer (tips) and inner (valleys).
-- | Ordered counter-clockwise starting from the first tip.
vertices :: Star -> Array Point2D
vertices (Star s) =
  let
    n = s.points
    Point2D c = s.center
    baseAngle = unwrapRadians (toRadians s.rotation)
    angleStep = pi / toNumber n  -- Half the angle between tips
    
    makeVertex :: Int -> Point2D
    makeVertex i =
      let
        angle = baseAngle + toNumber i * angleStep
        radius = if i `mod2` 2 == 0 then s.outerRadius else s.innerRadius
        x = c.x + radius * cos angle
        y = c.y + radius * sin angle
      in
        point2D x y
  in
    foldl (\acc i -> snoc acc (makeVertex i)) [] (range 0 (2 * n - 1))
  where
    range :: Int -> Int -> Array Int
    range start end = rangeHelper start end []
    
    rangeHelper :: Int -> Int -> Array Int -> Array Int
    rangeHelper cur end acc
      | cur > end = acc
      | otherwise = rangeHelper (cur + 1) end (snoc acc cur)
    
    mod2 :: Int -> Int -> Int
    mod2 a b = a - (a / b) * b

-- | Get only the outer vertices (tips).
outerVertices :: Star -> Array Point2D
outerVertices (Star s) =
  let
    n = s.points
    Point2D c = s.center
    baseAngle = unwrapRadians (toRadians s.rotation)
    fullAngleStep = 2.0 * pi / toNumber n
    
    makeVertex :: Int -> Point2D
    makeVertex i =
      let
        angle = baseAngle + toNumber i * fullAngleStep
        x = c.x + s.outerRadius * cos angle
        y = c.y + s.outerRadius * sin angle
      in
        point2D x y
  in
    foldl (\acc i -> snoc acc (makeVertex i)) [] (range 0 (n - 1))
  where
    range :: Int -> Int -> Array Int
    range start end = rangeHelper start end []
    
    rangeHelper :: Int -> Int -> Array Int -> Array Int
    rangeHelper cur end acc
      | cur > end = acc
      | otherwise = rangeHelper (cur + 1) end (snoc acc cur)

-- | Get only the inner vertices (valleys).
innerVertices :: Star -> Array Point2D
innerVertices (Star s) =
  let
    n = s.points
    Point2D c = s.center
    baseAngle = unwrapRadians (toRadians s.rotation)
    halfAngleStep = pi / toNumber n
    fullAngleStep = 2.0 * pi / toNumber n
    
    makeVertex :: Int -> Point2D
    makeVertex i =
      let
        -- Inner vertices are offset by half the angle step
        angle = baseAngle + halfAngleStep + toNumber i * fullAngleStep
        x = c.x + s.innerRadius * cos angle
        y = c.y + s.innerRadius * sin angle
      in
        point2D x y
  in
    foldl (\acc i -> snoc acc (makeVertex i)) [] (range 0 (n - 1))
  where
    range :: Int -> Int -> Array Int
    range start end = rangeHelper start end []
    
    rangeHelper :: Int -> Int -> Array Int -> Array Int
    rangeHelper cur end acc
      | cur > end = acc
      | otherwise = rangeHelper (cur + 1) end (snoc acc cur)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // measurements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounding radius (equals outer radius).
-- |
-- | Radius of smallest circle that contains the entire star.
boundingRadius :: Star -> Number
boundingRadius = outerRadius

-- | Approximate area of the star.
-- |
-- | Computed as sum of triangular sections from center.
-- | Uses the formula: A = n × r_outer × r_inner × sin(π/n)
approximateArea :: Star -> Number
approximateArea (Star s) =
  let
    n = toNumber s.points
    angleStep = pi / n
    -- Each triangle from center has base between outer and inner vertex
    -- Area = 0.5 × r_out × r_in × sin(angle)
    -- Total = 2n triangles (alternating orientation)
    singleTriangleArea = 0.5 * s.outerRadius * s.innerRadius * sin angleStep
  in
    2.0 * n * singleTriangleArea

-- | Approximate perimeter of the star.
-- |
-- | Sum of distances between consecutive vertices.
approximatePerimeter :: Star -> Number
approximatePerimeter star =
  let
    verts = vertices star
    n = length verts
  in
    foldl (\acc i -> acc + edgeLength verts n i) 0.0 (range 0 (n - 1))
  where
    edgeLength :: Array Point2D -> Int -> Int -> Number
    edgeLength arr len i =
      let
        p1 = fromMaybe (point2D 0.0 0.0) (arr !! i)
        p2 = fromMaybe (point2D 0.0 0.0) (arr !! ((i + 1) `mod2` len))
        dx = getX p2 - getX p1
        dy = getY p2 - getY p1
      in
        sqrt (dx * dx + dy * dy)
    
    range :: Int -> Int -> Array Int
    range start end = rangeHelper start end []
    
    rangeHelper :: Int -> Int -> Array Int -> Array Int
    rangeHelper cur end acc
      | cur > end = acc
      | otherwise = rangeHelper (cur + 1) end (snoc acc cur)
    
    mod2 :: Int -> Int -> Int
    mod2 a b = a - (a / b) * b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transformations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translate the star by an offset.
translateStar :: Number -> Number -> Star -> Star
translateStar dx dy (Star s) =
  Star (s { center = translate2D dx dy s.center })

-- | Scale both radii uniformly.
scaleStar :: Number -> Star -> Star
scaleStar factor (Star s) =
  Star (s { outerRadius = s.outerRadius * factor
          , innerRadius = s.innerRadius * factor
          })

-- | Add rotation to the star.
rotateStar :: Degrees -> Star -> Star
rotateStar (Degrees delta) (Star s) =
  let Degrees current = s.rotation
  in Star (s { rotation = Degrees (current + delta) })

-- | Set a new inner radius.
setInnerRadius :: Number -> Star -> Star
setInnerRadius newInner (Star s) =
  let validInner = if newInner < 0.0 then 0.0 
                   else if newInner >= s.outerRadius then s.outerRadius * 0.9
                   else newInner
  in Star (s { innerRadius = validInner })

-- | Set a new outer radius.
setOuterRadius :: Number -> Star -> Star
setOuterRadius newOuter (Star s) =
  let validOuter = if newOuter < s.innerRadius then s.innerRadius * 1.1
                   else if newOuter < 0.0 then 1.0
                   else newOuter
  in Star (s { outerRadius = validOuter })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert star to a polygon.
-- |
-- | The resulting polygon has 2n vertices.
toPolygon :: Star -> Polygon
toPolygon star = mkPolygonUnsafe (vertices star)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compare stars by number of points.
compareByPoints :: Star -> Star -> Ordering
compareByPoints s1 s2 = compare (points s1) (points s2)

-- | Compare stars by outer radius.
compareByOuterRadius :: Star -> Star -> Ordering
compareByOuterRadius s1 s2 = compare (outerRadius s1) (outerRadius s2)

-- | Check if two stars have the same number of points.
samePointCount :: Star -> Star -> Boolean
samePointCount s1 s2 = points s1 == points s2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format star for display.
showStar :: Star -> String
showStar (Star s) =
  "Star { points: " <> show s.points 
    <> ", outer: " <> show s.outerRadius 
    <> ", inner: " <> show s.innerRadius 
    <> " }"


