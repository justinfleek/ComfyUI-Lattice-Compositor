-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // motion // shapes // generators
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shape generator property records.
-- |
-- | Generators create paths: Rectangle, Ellipse, Polygon, Star, Path.
-- | Each has bounded properties defining its geometry.

module Hydrogen.Schema.Motion.Shapes.Generators
  ( -- * Rectangle
    RectangleProps
  , rectangleProps
  , defaultRectangle
  
  -- * Ellipse
  , EllipseProps
  , ellipseProps
  , defaultEllipse
  
  -- * Polygon
  , PolygonProps
  , polygonProps
  , defaultPolygon
  
  -- * Star
  , StarProps
  , starProps
  , defaultStar
  
  -- * Path
  , PathProps
  , pathProps
  , defaultPath
  
  -- * Corner Radius
  , CornerRadius
  , cornerRadius
  , cornerRadiusUniform
  , cornerRadiusNone
  , unwrapCornerRadius
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , ($)
  , (<>)
  , (&&)
  , (||)
  , not
  , (==)
  , (/=)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , compare
  , min
  , max
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  , otherwise
  , show
  , map
  , pure
  )
import Data.Ord (abs)
import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Dimension.Point2D (Point2D, origin)
import Hydrogen.Schema.Geometry.Path.Types (Path(Path))
import Hydrogen.Schema.Motion.Shapes (PathDirection(PDClockwise))
import Hydrogen.Schema.Motion.Shapes.Operators 
  ( PositiveNumber
  , positiveNumber
  , unwrapPositiveNumber
  , PositiveInt
  , positiveInt
  , Percent
  , percent
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // corner // radius
-- ═════════════════════════════════════════════════════════════════════════════

-- | Corner radius for rectangles.
-- |
-- | Can be uniform (all corners same) or per-corner (topLeft, topRight,
-- | bottomRight, bottomLeft).
data CornerRadius
  = UniformRadius PositiveNumber
  | PerCornerRadius
      { topLeft :: PositiveNumber
      , topRight :: PositiveNumber
      , bottomRight :: PositiveNumber
      , bottomLeft :: PositiveNumber
      }

derive instance eqCornerRadius :: Eq CornerRadius
derive instance ordCornerRadius :: Ord CornerRadius

instance showCornerRadius :: Show CornerRadius where
  show (UniformRadius r) = "Uniform(" <> show r <> ")"
  show (PerCornerRadius c) = 
    "PerCorner(TL:" <> show c.topLeft <> 
    ", TR:" <> show c.topRight <>
    ", BR:" <> show c.bottomRight <>
    ", BL:" <> show c.bottomLeft <> ")"

-- | Create per-corner radius.
cornerRadius
  :: Number  -- ^ Top left
  -> Number  -- ^ Top right
  -> Number  -- ^ Bottom right
  -> Number  -- ^ Bottom left
  -> CornerRadius
cornerRadius tl tr br bl = PerCornerRadius
  { topLeft: positiveNumber tl
  , topRight: positiveNumber tr
  , bottomRight: positiveNumber br
  , bottomLeft: positiveNumber bl
  }

-- | Create uniform corner radius.
cornerRadiusUniform :: Number -> CornerRadius
cornerRadiusUniform r = UniformRadius (positiveNumber r)

-- | No corner radius (sharp corners).
cornerRadiusNone :: CornerRadius
cornerRadiusNone = UniformRadius (positiveNumber 0.0)

-- | Extract first radius value (for uniform cases).
unwrapCornerRadius :: CornerRadius -> Number
unwrapCornerRadius (UniformRadius r) = unwrapPositiveNumber r
unwrapCornerRadius (PerCornerRadius c) = unwrapPositiveNumber c.topLeft

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // rectangle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rectangle generator properties.
-- |
-- | Creates a rectangle path from size, position, and corner radius.
type RectangleProps =
  { size :: { width :: PositiveNumber, height :: PositiveNumber }
  , position :: Point2D       -- ^ Center position
  , roundness :: Percent      -- ^ 0-100% for corners
  , cornerRadius :: CornerRadius
  , direction :: PathDirection
  }

-- | Create RectangleProps.
rectangleProps
  :: Number        -- ^ Width
  -> Number        -- ^ Height
  -> Point2D       -- ^ Position
  -> Number        -- ^ Roundness (%)
  -> CornerRadius
  -> PathDirection
  -> RectangleProps
rectangleProps w h pos rnd cr dir =
  { size: { width: positiveNumber w, height: positiveNumber h }
  , position: pos
  , roundness: percent rnd
  , cornerRadius: cr
  , direction: dir
  }

-- | Default Rectangle: 100x100 at origin.
defaultRectangle :: RectangleProps
defaultRectangle =
  { size: { width: positiveNumber 100.0, height: positiveNumber 100.0 }
  , position: origin
  , roundness: percent 0.0
  , cornerRadius: cornerRadiusNone
  , direction: PDClockwise
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // ellipse
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ellipse generator properties.
-- |
-- | Creates an ellipse (or circle when width = height).
type EllipseProps =
  { size :: { width :: PositiveNumber, height :: PositiveNumber }
  , position :: Point2D  -- ^ Center position
  , direction :: PathDirection
  }

-- | Create EllipseProps.
ellipseProps
  :: Number       -- ^ Width
  -> Number       -- ^ Height
  -> Point2D      -- ^ Position
  -> PathDirection
  -> EllipseProps
ellipseProps w h pos dir =
  { size: { width: positiveNumber w, height: positiveNumber h }
  , position: pos
  , direction: dir
  }

-- | Default Ellipse: 100x100 circle at origin.
defaultEllipse :: EllipseProps
defaultEllipse =
  { size: { width: positiveNumber 100.0, height: positiveNumber 100.0 }
  , position: origin
  , direction: PDClockwise
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // polygon
-- ═════════════════════════════════════════════════════════════════════════════

-- | Polygon generator properties.
-- |
-- | Creates a regular polygon with n sides.
type PolygonProps =
  { points :: PositiveInt        -- ^ Number of sides (3+)
  , position :: Point2D          -- ^ Center position
  , outerRadius :: PositiveNumber  -- ^ Distance from center to vertices
  , outerRoundness :: Percent    -- ^ Roundness of outer vertices
  , direction :: PathDirection
  }

-- | Create PolygonProps.
polygonProps
  :: Int           -- ^ Number of points
  -> Point2D       -- ^ Position
  -> Number        -- ^ Outer radius
  -> Number        -- ^ Outer roundness (%)
  -> PathDirection
  -> PolygonProps
polygonProps pts pos radius rnd dir =
  { points: positiveInt (maxInt 3 pts)  -- At least 3 sides
  , position: pos
  , outerRadius: positiveNumber radius
  , outerRoundness: percent rnd
  , direction: dir
  }
  where
  maxInt :: Int -> Int -> Int
  maxInt a b
    | a < b = b
    | otherwise = a

-- | Default Polygon: hexagon (6 sides).
defaultPolygon :: PolygonProps
defaultPolygon =
  { points: positiveInt 6
  , position: origin
  , outerRadius: positiveNumber 50.0
  , outerRoundness: percent 0.0
  , direction: PDClockwise
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // star
-- ═════════════════════════════════════════════════════════════════════════════

-- | Star generator properties.
-- |
-- | Creates a star with inner and outer radii.
type StarProps =
  { points :: PositiveInt         -- ^ Number of star points (3+)
  , position :: Point2D           -- ^ Center position
  , outerRadius :: PositiveNumber -- ^ Distance to outer points
  , innerRadius :: PositiveNumber -- ^ Distance to inner points
  , outerRoundness :: Percent     -- ^ Roundness of outer points
  , innerRoundness :: Percent     -- ^ Roundness of inner points
  , rotation :: Number            -- ^ Initial rotation (degrees)
  , direction :: PathDirection
  }

-- | Create StarProps.
starProps
  :: Int           -- ^ Number of points
  -> Point2D       -- ^ Position
  -> Number        -- ^ Outer radius
  -> Number        -- ^ Inner radius
  -> Number        -- ^ Outer roundness (%)
  -> Number        -- ^ Inner roundness (%)
  -> Number        -- ^ Rotation (degrees)
  -> PathDirection
  -> StarProps
starProps pts pos outerR innerR outerRnd innerRnd rot dir =
  { points: positiveInt (maxInt 3 pts)
  , position: pos
  , outerRadius: positiveNumber outerR
  , innerRadius: positiveNumber innerR
  , outerRoundness: percent outerRnd
  , innerRoundness: percent innerRnd
  , rotation: clampNumber (-36000.0) 36000.0 rot
  , direction: dir
  }
  where
  maxInt :: Int -> Int -> Int
  maxInt a b
    | a < b = b
    | otherwise = a

-- | Default Star: 5-pointed star.
defaultStar :: StarProps
defaultStar =
  { points: positiveInt 5
  , position: origin
  , outerRadius: positiveNumber 50.0
  , innerRadius: positiveNumber 25.0
  , outerRoundness: percent 0.0
  , innerRoundness: percent 0.0
  , rotation: 0.0
  , direction: PDClockwise
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // path
-- ═════════════════════════════════════════════════════════════════════════════

-- | Path generator properties.
-- |
-- | Contains a bezier path (array of path commands).
type PathProps =
  { path :: Path          -- ^ The bezier path data
  , closed :: Boolean     -- ^ Whether path is closed
  , direction :: PathDirection
  }

-- | Create PathProps.
pathProps
  :: Path
  -> Boolean        -- ^ Closed
  -> PathDirection
  -> PathProps
pathProps p c dir =
  { path: p
  , closed: c
  , direction: dir
  }

-- | Default Path: empty path.
defaultPath :: PathProps
defaultPath =
  { path: Path []
  , closed: not true  -- false
  , direction: PDClockwise
  }
