-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // geometry // shape
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shape — Foundational geometric primitives for vector graphics.
-- |
-- | ## Design Philosophy
-- |
-- | Shapes are pure data descriptions of geometry. They compose algebraically
-- | via boolean operations and path combinations. This is the vocabulary for
-- | "Illustrator on steroids" — everything from simple rectangles to complex
-- | compound paths with boolean operations.
-- |
-- | ## Shape Categories
-- |
-- | **Primitives**: Rectangle, Circle, Ellipse, Line, Polygon, Polyline
-- | **Curves**: Bezier (cubic/quadratic), Arc, Spline, NURBS
-- | **Complex**: Star, Ring, Spiral, Arrow, Cross, Heart, Gear
-- | **Paths**: Open paths, Closed paths, Compound paths
-- | **Operations**: Union, Subtract, Intersect, Exclude, Divide
-- | **3D Extrusion**: Extrude, Revolve, Sweep, Loft
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show, Bounded)
-- | - Schema.Dimension.Device (Pixel for measurements)
-- | - Schema.Geometry.Radius (corner treatments)

module Hydrogen.Schema.Geometry.Shape
  ( -- * Primitive Shapes
    ShapePrimitive(..)
  
  -- * Path Primitives
  , PathCommand(..)
  , WindingRule(..)
  , ArcParams
  
  -- * Pixel Point Types (distinct from Geometry.Point)
  , PixelPoint2D
  , pixelPoint2D
  , pixelOrigin
  , PixelPoint3D
  , pixelPoint3D
  , pixelOrigin3D
  
  -- * Anchor Points (for Bezier)
  , AnchorPoint
  , anchorPoint
  , smoothAnchor
  , cornerAnchor
  , symmetricAnchor
  , AnchorType(..)
  
  -- * Rectangle
  , RectangleShape
  , rectangleShape
  , squareShape
  
  -- * Circle/Ellipse
  , EllipseShape
  , ellipseShape
  , circleShape
  
  -- * Line
  , LineShape
  , lineShape
  
  -- * Polygon
  , PolygonShape
  , polygonShape
  , triangleShape
  , pentagonShape
  , hexagonShape
  
  -- * Star
  , StarShape
  , starShape
  
  -- * Ring/Donut
  , RingShape
  , ringShape
  
  -- * Spiral
  , SpiralShape
  , spiralShape
  , SpiralDirection(..)
  
  -- * Arrow
  , ArrowShape
  , arrowShape
  , ArrowHeadStyle(..)
  
  -- * Cross
  , CrossShape
  , crossShape
  
  -- * Gear
  , GearShape
  , gearShape
  
  -- * Path
  , PathShape
  , pathShape
  , closedPath
  , openPath
  
  -- * Boolean Operations
  , BooleanOp(..)
  , CompoundShape
  , compoundShape
  , unionShapes
  , subtractShapes
  , intersectShapes
  , excludeShapes
  
  -- * 3D Operations
  , ExtrudeOp
  , extrudeOp
  , RevolveOp
  , revolveOp
  , SweepOp
  , sweepOp
  
  -- * Shape Wrapper
  , Shape(..)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (==)
  , (>)
  , (<)
  , negate
  )

import Data.Array (length) as Array

import Hydrogen.Schema.Dimension.Device (Pixel(Pixel))
import Hydrogen.Schema.Geometry.Radius (Corners) as Radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // pixel point 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | A 2D point in pixel space with explicit Pixel units.
-- |
-- | This is distinct from Geometry.Point.Point2D which uses unbounded Numbers.
-- | PixelPoint2D is used for shape vertices and control points where we need
-- | type-safe unit tracking.
-- |
-- | For generic coordinate operations, use Geometry.Point.Point2D.
-- | For shape definitions with pixel measurements, use PixelPoint2D.
type PixelPoint2D = { x :: Pixel, y :: Pixel }

-- | Smart constructor for PixelPoint2D
pixelPoint2D :: Pixel -> Pixel -> PixelPoint2D
pixelPoint2D x y = { x, y }

-- | The pixel origin point (0, 0)
pixelOrigin :: PixelPoint2D
pixelOrigin = { x: Pixel 0.0, y: Pixel 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // pixel point 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | A 3D point in pixel space with explicit Pixel units.
-- |
-- | Extends PixelPoint2D with a Z coordinate for:
-- | - 3D viewport positioning (widgets floating in space)
-- | - Depth sorting for overlapping elements
-- | - WebGL/WebGPU vertex data with type-safe units
-- | - Gimbal and gizmo positioning for interactive 3D controls
-- |
-- | The Z axis follows WebGL convention: positive Z comes toward the viewer.
-- |
-- | ## Example: Bento box widget at depth
-- |
-- | ```purescript
-- | widgetPosition = pixelPoint3D (Pixel 100.0) (Pixel 50.0) (Pixel 10.0)
-- | -- Widget is 100px right, 50px down, 10px toward viewer
-- | ```
type PixelPoint3D = { x :: Pixel, y :: Pixel, z :: Pixel }

-- | Smart constructor for PixelPoint3D
pixelPoint3D :: Pixel -> Pixel -> Pixel -> PixelPoint3D
pixelPoint3D x y z = { x, y, z }

-- | The 3D pixel origin point (0, 0, 0)
pixelOrigin3D :: PixelPoint3D
pixelOrigin3D = { x: Pixel 0.0, y: Pixel 0.0, z: Pixel 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // anchor point
-- ═════════════════════════════════════════════════════════════════════════════

-- | Anchor point type for Bezier curve vertices.
-- | Determines how control handles behave at this vertex.
data AnchorType
  = AnchorSmooth      -- ^ Handles are colinear (C1 continuity)
  | AnchorCorner      -- ^ Handles are independent (no continuity)
  | AnchorSymmetric   -- ^ Handles are colinear and equal length

derive instance eqAnchorType :: Eq AnchorType
derive instance ordAnchorType :: Ord AnchorType

instance showAnchorType :: Show AnchorType where
  show AnchorSmooth = "(AnchorType Smooth)"
  show AnchorCorner = "(AnchorType Corner)"
  show AnchorSymmetric = "(AnchorType Symmetric)"

-- | A bezier anchor point with position and control handles.
-- | Control handles are relative to the anchor position.
type AnchorPoint =
  { position :: PixelPoint2D
  , handleIn :: PixelPoint2D    -- ^ Incoming control handle (relative)
  , handleOut :: PixelPoint2D   -- ^ Outgoing control handle (relative)
  , anchorType :: AnchorType
  }

-- | Create an anchor point with explicit handles
anchorPoint :: PixelPoint2D -> PixelPoint2D -> PixelPoint2D -> AnchorType -> AnchorPoint
anchorPoint position handleIn handleOut anchorType =
  { position, handleIn, handleOut, anchorType }

-- | Create a smooth anchor with colinear handles
smoothAnchor :: PixelPoint2D -> PixelPoint2D -> PixelPoint2D -> AnchorPoint
smoothAnchor position handleIn handleOut =
  anchorPoint position handleIn handleOut AnchorSmooth

-- | Create a corner anchor (sharp, independent handles)
cornerAnchor :: PixelPoint2D -> AnchorPoint
cornerAnchor position =
  anchorPoint position pixelOrigin pixelOrigin AnchorCorner

-- | Create a symmetric anchor (handles mirror each other)
symmetricAnchor :: PixelPoint2D -> PixelPoint2D -> AnchorPoint
symmetricAnchor position handle =
  anchorPoint position (negatePoint handle) handle AnchorSymmetric
  where
    negatePoint :: PixelPoint2D -> PixelPoint2D
    negatePoint { x: Pixel px, y: Pixel py } = 
      { x: Pixel (negate px), y: Pixel (negate py) }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // path commands
-- ═════════════════════════════════════════════════════════════════════════════

-- | Winding rule for determining inside/outside of paths.
-- | Critical for boolean operations and fill rendering.
data WindingRule
  = WindingNonZero   -- ^ Non-zero winding rule (SVG default)
  | WindingEvenOdd   -- ^ Even-odd (alternate) rule

derive instance eqWindingRule :: Eq WindingRule
derive instance ordWindingRule :: Ord WindingRule

instance showWindingRule :: Show WindingRule where
  show WindingNonZero = "(WindingRule NonZero)"
  show WindingEvenOdd = "(WindingRule EvenOdd)"

-- | Path commands following SVG path semantics.
-- | These are the atomic operations for constructing paths.
data PathCommand
  = MoveTo PixelPoint2D              -- ^ Move to point (starts new subpath)
  | LineTo PixelPoint2D              -- ^ Draw line to point
  | HorizontalTo Pixel               -- ^ Draw horizontal line to X
  | VerticalTo Pixel                 -- ^ Draw vertical line to Y
  | CubicTo PixelPoint2D PixelPoint2D PixelPoint2D  -- ^ Cubic bezier (c1, c2, end)
  | QuadraticTo PixelPoint2D PixelPoint2D           -- ^ Quadratic bezier (control, end)
  | ArcTo ArcParams PixelPoint2D                    -- ^ Elliptical arc to point
  | ClosePath                                       -- ^ Close current subpath

derive instance eqPathCommand :: Eq PathCommand

instance showPathCommand :: Show PathCommand where
  show (MoveTo p) = "(PathCommand MoveTo " <> show p <> ")"
  show (LineTo p) = "(PathCommand LineTo " <> show p <> ")"
  show (HorizontalTo x) = "(PathCommand HorizontalTo " <> show x <> ")"
  show (VerticalTo y) = "(PathCommand VerticalTo " <> show y <> ")"
  show (CubicTo c1 c2 end) = "(PathCommand CubicTo " <> show c1 <> " " <> show c2 <> " " <> show end <> ")"
  show (QuadraticTo c end) = "(PathCommand QuadraticTo " <> show c <> " " <> show end <> ")"
  show (ArcTo _ end) = "(PathCommand ArcTo " <> show end <> ")"
  show ClosePath = "(PathCommand ClosePath)"

-- | Parameters for elliptical arc commands
type ArcParams =
  { radiusX :: Pixel
  , radiusY :: Pixel
  , rotation :: Number       -- ^ X-axis rotation in degrees
  , largeArc :: Boolean      -- ^ Use large arc sweep
  , sweep :: Boolean         -- ^ Clockwise sweep direction
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // primitive shapes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enumeration of all primitive shape types.
-- | Used for type-level discrimination and pattern matching.
data ShapePrimitive
  = PrimitiveRectangle
  | PrimitiveEllipse
  | PrimitiveLine
  | PrimitivePolygon
  | PrimitiveStar
  | PrimitiveRing
  | PrimitiveSpiral
  | PrimitiveArrow
  | PrimitiveCross
  | PrimitiveGear
  | PrimitivePath

derive instance eqShapePrimitive :: Eq ShapePrimitive
derive instance ordShapePrimitive :: Ord ShapePrimitive

instance showShapePrimitive :: Show ShapePrimitive where
  show PrimitiveRectangle = "(ShapePrimitive Rectangle)"
  show PrimitiveEllipse = "(ShapePrimitive Ellipse)"
  show PrimitiveLine = "(ShapePrimitive Line)"
  show PrimitivePolygon = "(ShapePrimitive Polygon)"
  show PrimitiveStar = "(ShapePrimitive Star)"
  show PrimitiveRing = "(ShapePrimitive Ring)"
  show PrimitiveSpiral = "(ShapePrimitive Spiral)"
  show PrimitiveArrow = "(ShapePrimitive Arrow)"
  show PrimitiveCross = "(ShapePrimitive Cross)"
  show PrimitiveGear = "(ShapePrimitive Gear)"
  show PrimitivePath = "(ShapePrimitive Path)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // rectangle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rectangle shape with position, dimensions, and optional corner radii.
type RectangleShape =
  { center :: PixelPoint2D
  , width :: Pixel
  , height :: Pixel
  , corners :: Radius.Corners
  }

-- | Create a rectangle shape
rectangleShape :: PixelPoint2D -> Pixel -> Pixel -> Radius.Corners -> RectangleShape
rectangleShape center width height corners =
  { center, width, height, corners }

-- | Create a square shape (equal width and height)
squareShape :: PixelPoint2D -> Pixel -> Radius.Corners -> RectangleShape
squareShape center size corners =
  rectangleShape center size size corners

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // ellipse
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ellipse shape with center and radii.
-- | When radiusX == radiusY, this is a circle.
type EllipseShape =
  { center :: PixelPoint2D
  , radiusX :: Pixel
  , radiusY :: Pixel
  }

-- | Create an ellipse shape
ellipseShape :: PixelPoint2D -> Pixel -> Pixel -> EllipseShape
ellipseShape center radiusX radiusY =
  { center, radiusX, radiusY }

-- | Create a circle shape (equal radii)
circleShape :: PixelPoint2D -> Pixel -> EllipseShape
circleShape center radius =
  ellipseShape center radius radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // line
-- ═════════════════════════════════════════════════════════════════════════════

-- | Line segment from start to end point.
type LineShape =
  { start :: PixelPoint2D
  , end :: PixelPoint2D
  }

-- | Create a line shape
lineShape :: PixelPoint2D -> PixelPoint2D -> LineShape
lineShape start end = { start, end }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // polygon
-- ═════════════════════════════════════════════════════════════════════════════

-- | Regular polygon with N sides inscribed in a circle.
type PolygonShape =
  { center :: PixelPoint2D
  , radius :: Pixel        -- ^ Distance from center to vertices
  , sides :: Int           -- ^ Number of sides (minimum 3)
  , rotation :: Number     -- ^ Rotation in degrees
  }

-- | Create a polygon shape
polygonShape :: PixelPoint2D -> Pixel -> Int -> Number -> PolygonShape
polygonShape center radius sides rotation =
  { center, radius, sides: max 3 sides, rotation }
  where
    max a b = if a > b then a else b

-- | Create an equilateral triangle
triangleShape :: PixelPoint2D -> Pixel -> PolygonShape
triangleShape center radius = polygonShape center radius 3 0.0

-- | Create a regular pentagon
pentagonShape :: PixelPoint2D -> Pixel -> PolygonShape
pentagonShape center radius = polygonShape center radius 5 0.0

-- | Create a regular hexagon
hexagonShape :: PixelPoint2D -> Pixel -> PolygonShape
hexagonShape center radius = polygonShape center radius 6 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // star
-- ═════════════════════════════════════════════════════════════════════════════

-- | Star shape with configurable points and inner/outer radii.
type StarShape =
  { center :: PixelPoint2D
  , outerRadius :: Pixel    -- ^ Distance to star points
  , innerRadius :: Pixel    -- ^ Distance to inner vertices
  , points :: Int           -- ^ Number of points (minimum 3)
  , rotation :: Number      -- ^ Rotation in degrees
  }

-- | Create a star shape
starShape :: PixelPoint2D -> Pixel -> Pixel -> Int -> Number -> StarShape
starShape center outerRadius innerRadius points rotation =
  { center
  , outerRadius
  , innerRadius
  , points: max 3 points
  , rotation
  }
  where
    max a b = if a > b then a else b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // ring
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ring (donut) shape with inner and outer radii.
type RingShape =
  { center :: PixelPoint2D
  , outerRadius :: Pixel    -- ^ Outer circle radius
  , innerRadius :: Pixel    -- ^ Inner hole radius
  }

-- | Create a ring shape
ringShape :: PixelPoint2D -> Pixel -> Pixel -> RingShape
ringShape center outerRadius innerRadius =
  { center, outerRadius, innerRadius }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // spiral
-- ═════════════════════════════════════════════════════════════════════════════

-- | Direction of spiral winding
data SpiralDirection
  = SpiralClockwise
  | SpiralCounterclockwise

derive instance eqSpiralDirection :: Eq SpiralDirection
derive instance ordSpiralDirection :: Ord SpiralDirection

instance showSpiralDirection :: Show SpiralDirection where
  show SpiralClockwise = "(SpiralDirection Clockwise)"
  show SpiralCounterclockwise = "(SpiralDirection Counterclockwise)"

-- | Spiral shape (Archimedean spiral)
type SpiralShape =
  { center :: PixelPoint2D
  , startRadius :: Pixel    -- ^ Starting radius
  , endRadius :: Pixel      -- ^ Ending radius
  , turns :: Number         -- ^ Number of full rotations
  , direction :: SpiralDirection
  }

-- | Create a spiral shape
spiralShape :: PixelPoint2D -> Pixel -> Pixel -> Number -> SpiralDirection -> SpiralShape
spiralShape center startRadius endRadius turns direction =
  { center, startRadius, endRadius, turns, direction }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // arrow
-- ═════════════════════════════════════════════════════════════════════════════

-- | Arrow head styles
data ArrowHeadStyle
  = ArrowTriangle       -- ^ Simple triangular head
  | ArrowStealth        -- ^ Stealth/sharp arrow head
  | ArrowDiamond        -- ^ Diamond-shaped head
  | ArrowCircle         -- ^ Circular head
  | ArrowSquare         -- ^ Square head
  | ArrowNone           -- ^ No arrow head

derive instance eqArrowHeadStyle :: Eq ArrowHeadStyle
derive instance ordArrowHeadStyle :: Ord ArrowHeadStyle

instance showArrowHeadStyle :: Show ArrowHeadStyle where
  show ArrowTriangle = "(ArrowHeadStyle Triangle)"
  show ArrowStealth = "(ArrowHeadStyle Stealth)"
  show ArrowDiamond = "(ArrowHeadStyle Diamond)"
  show ArrowCircle = "(ArrowHeadStyle Circle)"
  show ArrowSquare = "(ArrowHeadStyle Square)"
  show ArrowNone = "(ArrowHeadStyle None)"

-- | Arrow shape with configurable head and tail styles
type ArrowShape =
  { start :: PixelPoint2D
  , end :: PixelPoint2D
  , headStyle :: ArrowHeadStyle
  , tailStyle :: ArrowHeadStyle
  , headSize :: Pixel       -- ^ Size of arrow head
  , shaftWidth :: Pixel     -- ^ Width of arrow shaft
  }

-- | Create an arrow shape
arrowShape :: PixelPoint2D -> PixelPoint2D -> ArrowHeadStyle -> Pixel -> Pixel -> ArrowShape
arrowShape start end headStyle headSize shaftWidth =
  { start
  , end
  , headStyle
  , tailStyle: ArrowNone
  , headSize
  , shaftWidth
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // cross
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cross/plus shape
type CrossShape =
  { center :: PixelPoint2D
  , armLength :: Pixel      -- ^ Length of each arm from center
  , armWidth :: Pixel       -- ^ Width/thickness of arms
  , rotation :: Number      -- ^ Rotation in degrees (0 = plus, 45 = X)
  }

-- | Create a cross shape
crossShape :: PixelPoint2D -> Pixel -> Pixel -> Number -> CrossShape
crossShape center armLength armWidth rotation =
  { center, armLength, armWidth, rotation }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // gear
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gear/cog shape
type GearShape =
  { center :: PixelPoint2D
  , outerRadius :: Pixel    -- ^ Radius to tooth tips
  , innerRadius :: Pixel    -- ^ Radius to tooth valleys
  , holeRadius :: Pixel     -- ^ Center hole radius
  , teeth :: Int            -- ^ Number of teeth (minimum 3)
  , toothWidth :: Number    -- ^ Tooth width ratio (0.0-1.0)
  }

-- | Create a gear shape
gearShape :: PixelPoint2D -> Pixel -> Pixel -> Pixel -> Int -> Number -> GearShape
gearShape center outerRadius innerRadius holeRadius teeth toothWidth =
  { center
  , outerRadius
  , innerRadius
  , holeRadius
  , teeth: max 3 teeth
  , toothWidth: clamp01 toothWidth
  }
  where
    max a b = if a > b then a else b
    clamp01 n = if n < 0.0 then 0.0 else if n > 1.0 then 1.0 else n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // path
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generic path shape defined by commands
type PathShape =
  { commands :: Array PathCommand
  , windingRule :: WindingRule
  , closed :: Boolean
  }

-- | Create a path shape from commands
pathShape :: Array PathCommand -> WindingRule -> PathShape
pathShape commands windingRule =
  { commands
  , windingRule
  , closed: Array.length commands > 0
  }

-- | Create a closed path
closedPath :: Array PathCommand -> PathShape
closedPath commands =
  { commands
  , windingRule: WindingNonZero
  , closed: true
  }

-- | Create an open path
openPath :: Array PathCommand -> PathShape
openPath commands =
  { commands
  , windingRule: WindingNonZero
  , closed: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // boolean operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Boolean operations for combining shapes
data BooleanOp
  = BoolUnion           -- ^ Combine shapes (OR)
  | BoolSubtract        -- ^ Remove second from first
  | BoolIntersect       -- ^ Keep only overlap (AND)
  | BoolExclude         -- ^ Keep non-overlapping parts (XOR)
  | BoolDivide          -- ^ Split into separate pieces

derive instance eqBooleanOp :: Eq BooleanOp
derive instance ordBooleanOp :: Ord BooleanOp

instance showBooleanOp :: Show BooleanOp where
  show BoolUnion = "(BooleanOp Union)"
  show BoolSubtract = "(BooleanOp Subtract)"
  show BoolIntersect = "(BooleanOp Intersect)"
  show BoolExclude = "(BooleanOp Exclude)"
  show BoolDivide = "(BooleanOp Divide)"

-- | Compound shape from boolean operations
type CompoundShape =
  { operation :: BooleanOp
  , shapes :: Array Shape
  }

-- | Create a compound shape from boolean operation
compoundShape :: BooleanOp -> Array Shape -> CompoundShape
compoundShape operation shapes = { operation, shapes }

-- | Union multiple shapes
unionShapes :: Array Shape -> CompoundShape
unionShapes = compoundShape BoolUnion

-- | Subtract shapes from first shape
subtractShapes :: Array Shape -> CompoundShape
subtractShapes = compoundShape BoolSubtract

-- | Intersect shapes
intersectShapes :: Array Shape -> CompoundShape
intersectShapes = compoundShape BoolIntersect

-- | Exclude overlapping regions
excludeShapes :: Array Shape -> CompoundShape
excludeShapes = compoundShape BoolExclude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // 3d operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extrude operation - extend 2D shape into 3D along Z axis
type ExtrudeOp =
  { depth :: Pixel          -- ^ Extrusion depth
  , bevel :: Pixel          -- ^ Bevel amount at edges
  , bevelSegments :: Int    -- ^ Smoothness of bevel
  }

-- | Create an extrude operation
extrudeOp :: Pixel -> Pixel -> Int -> ExtrudeOp
extrudeOp depth bevel bevelSegments =
  { depth, bevel, bevelSegments }

-- | Revolve operation - rotate 2D shape around axis to create 3D
type RevolveOp =
  { angle :: Number         -- ^ Rotation angle in degrees (360 = full revolution)
  , segments :: Int         -- ^ Number of segments for smoothness
  , axisOffset :: Pixel     -- ^ Distance of axis from shape
  }

-- | Create a revolve operation
revolveOp :: Number -> Int -> Pixel -> RevolveOp
revolveOp angle segments axisOffset =
  { angle, segments, axisOffset }

-- | Sweep operation - extrude shape along a path
type SweepOp =
  { path :: PathShape       -- ^ Path to sweep along
  , twist :: Number         -- ^ Rotation along path in degrees
  , scale :: Number         -- ^ Scale factor at end (1.0 = no change)
  }

-- | Create a sweep operation
sweepOp :: PathShape -> Number -> Number -> SweepOp
sweepOp path twist scale =
  { path, twist, scale }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // shape wrapper
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unified shape type that can hold any shape primitive
data Shape
  = ShapeRectangle RectangleShape
  | ShapeEllipse EllipseShape
  | ShapeLine LineShape
  | ShapePolygon PolygonShape
  | ShapeStar StarShape
  | ShapeRing RingShape
  | ShapeSpiral SpiralShape
  | ShapeArrow ArrowShape
  | ShapeCross CrossShape
  | ShapeGear GearShape
  | ShapePath PathShape
  | ShapeCompound CompoundShape

derive instance eqShape :: Eq Shape

instance showShape :: Show Shape where
  show (ShapeRectangle _) = "(Shape Rectangle)"
  show (ShapeEllipse _) = "(Shape Ellipse)"
  show (ShapeLine _) = "(Shape Line)"
  show (ShapePolygon _) = "(Shape Polygon)"
  show (ShapeStar _) = "(Shape Star)"
  show (ShapeRing _) = "(Shape Ring)"
  show (ShapeSpiral _) = "(Shape Spiral)"
  show (ShapeArrow _) = "(Shape Arrow)"
  show (ShapeCross _) = "(Shape Cross)"
  show (ShapeGear _) = "(Shape Gear)"
  show (ShapePath _) = "(Shape Path)"
  show (ShapeCompound _) = "(Shape Compound)"
