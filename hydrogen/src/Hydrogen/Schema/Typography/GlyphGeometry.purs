-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // typography // glyph-geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GlyphGeometry — Typography as pure geometry.
-- |
-- | ## Design Philosophy
-- |
-- | A glyph is NOT special-cased text rendering. A glyph IS a shape: bezier
-- | paths that can be manipulated, extruded, beveled, and animated like any
-- | other vector geometry. The letter 'O' is two elliptical paths (outer and
-- | counter). The letter 'A' is three line segments. This unifies the entire
-- | rendering pipeline.
-- |
-- | ## Structure
-- |
-- | - GlyphPath: Complete character with metadata (advance width, bounds)
-- | - Contour: Single closed path within a glyph (glyphs may have multiple)
-- | - ContourWinding: Clockwise (outer) or counter-clockwise (hole)
-- | - ControlPoint3D: Point in 3D space for per-control-point animation
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Schema.Dimension.Device (Pixel for coordinates)
-- | - Schema.Geometry.Shape (PathCommand for path operations)
-- | - Schema.Bounded (clamping utilities)

module Hydrogen.Schema.Typography.GlyphGeometry
  ( -- * Core Types
    GlyphPath
  , Contour
  , ContourWinding(..)
  
  -- * 3D Control Points
  , ControlPoint3D
  , controlPoint3D
  , controlPoint2D
  
  -- * Path Commands in 3D
  , PathCommand3D(..)
  
  -- * Glyph Bounds
  , GlyphBounds
  , glyphBounds
  , emptyBounds
  
  -- * Constructors
  , glyphPath
  , contour
  , emptyGlyph
  
  -- * Operations
  , addContour
  , getOuterContour
  , getCounterContours
  , totalControlPoints
  , mapControlPoints
  , transformGlyph
  , glyphToPath2D
  
  -- * Bounds Utilities
  , boundsWidth
  , boundsHeight
  , boundsDepth
  , unionBounds
  , computeBoundsFromCommands
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , map
  , negate
  , (+)
  , (-)
  , (*)
  , (<>)
  , (==)
  , (>)
  , (<)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Dimension.Device (Pixel(Pixel))
import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Geometry.Shape
  ( PathCommand(MoveTo, LineTo, CubicTo, QuadraticTo, ClosePath)
  , PixelPoint2D
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // 3d control points
-- ═════════════════════════════════════════════════════════════════════════════

-- | A control point in 3D space.
-- |
-- | The Z coordinate enables:
-- | - Depth-based stacking for overlapping paths
-- | - 3D transformations for perspective typography
-- | - Animation along the Z axis (letters floating up)
-- | - Extrusion reference points
-- |
-- | All coordinates in Pixel units. Z is bounded to prevent extreme values
-- | at swarm scale: -10000 to 10000 pixels depth.
type ControlPoint3D =
  { x :: Pixel
  , y :: Pixel
  , z :: Pixel
  }

-- | Create a 3D control point with Z clamping.
-- |
-- | Z coordinate clamped to -10000..10000 to ensure bounded depth.
controlPoint3D :: Pixel -> Pixel -> Pixel -> ControlPoint3D
controlPoint3D x y z =
  { x
  , y
  , z: clampZ z
  }
  where
    clampZ :: Pixel -> Pixel
    clampZ (Pixel n) = Pixel (Bounded.clampNumber (-10000.0) 10000.0 n)

-- | Create a control point from 2D coordinates (Z = 0).
-- |
-- | Standard case for flat typography before extrusion.
controlPoint2D :: Pixel -> Pixel -> ControlPoint3D
controlPoint2D x y = { x, y, z: Pixel 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // 3d path commands
-- ═════════════════════════════════════════════════════════════════════════════

-- | Path commands in 3D space.
-- |
-- | Extended from Shape.PathCommand to include Z coordinates. This enables
-- | true 3D typography where bezier curves exist in space, not just on a plane.
-- |
-- | ## Command Types
-- |
-- | - MoveTo3D: Begin new subpath at point
-- | - LineTo3D: Straight line to point
-- | - QuadraticTo3D: TrueType-style curve (1 control point)
-- | - CubicTo3D: PostScript/CFF-style curve (2 control points)
-- | - ClosePath3D: Close current subpath to start
data PathCommand3D
  = MoveTo3D ControlPoint3D
  | LineTo3D ControlPoint3D
  | QuadraticTo3D ControlPoint3D ControlPoint3D    -- control, end
  | CubicTo3D ControlPoint3D ControlPoint3D ControlPoint3D  -- c1, c2, end
  | ClosePath3D

derive instance eqPathCommand3D :: Eq PathCommand3D

instance showPathCommand3D :: Show PathCommand3D where
  show (MoveTo3D _) = "M3D"
  show (LineTo3D _) = "L3D"
  show (QuadraticTo3D _ _) = "Q3D"
  show (CubicTo3D _ _ _) = "C3D"
  show ClosePath3D = "Z3D"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // contour (subpath)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Winding direction of a contour.
-- |
-- | Determines fill behavior using the non-zero winding rule:
-- | - WindingClockwise: Outer boundary (adds to fill)
-- | - WindingCounterClockwise: Hole/counter (subtracts from fill)
-- |
-- | For glyphs like 'O', 'A', 'B', '8':
-- | - The outer shape is clockwise
-- | - The inner hole(s) are counter-clockwise
data ContourWinding
  = WindingClockwise
  | WindingCounterClockwise

derive instance eqContourWinding :: Eq ContourWinding
derive instance ordContourWinding :: Ord ContourWinding

instance showContourWinding :: Show ContourWinding where
  show WindingClockwise = "cw"
  show WindingCounterClockwise = "ccw"

-- | A single closed contour (subpath) of a glyph.
-- |
-- | Every glyph consists of one or more contours:
-- | - Simple letters ('l', 'v', 'z'): 1 contour
-- | - Letters with holes ('o', 'a', 'e'): 2+ contours
-- | - Complex letters ('8', 'B', '&'): multiple contours
-- |
-- | Each contour MUST be closed. The winding direction determines
-- | whether it contributes to fill (outer) or removes from fill (hole).
type Contour =
  { commands :: Array PathCommand3D
  , winding :: ContourWinding
  }

-- | Create a contour from commands and winding direction.
-- |
-- | Commands should describe a closed path. ClosePath3D will be appended
-- | if not already present.
contour :: Array PathCommand3D -> ContourWinding -> Contour
contour commands winding = { commands: ensureClosed commands, winding }
  where
    ensureClosed :: Array PathCommand3D -> Array PathCommand3D
    ensureClosed cmds = case Array.last cmds of
      Just ClosePath3D -> cmds
      _ -> Array.snoc cmds ClosePath3D

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // glyph bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounding box for a glyph in 3D space.
-- |
-- | These are tight bounds around the actual geometry, not the advance box.
-- | Used for:
-- | - Culling during rendering
-- | - Hit testing
-- | - Layout calculations
-- | - 3D collision detection
type GlyphBounds =
  { minX :: Pixel
  , maxX :: Pixel
  , minY :: Pixel
  , maxY :: Pixel
  , minZ :: Pixel
  , maxZ :: Pixel
  }

-- | Create glyph bounds from min/max coordinates.
glyphBounds :: Pixel -> Pixel -> Pixel -> Pixel -> Pixel -> Pixel -> GlyphBounds
glyphBounds minX maxX minY maxY minZ maxZ =
  { minX, maxX, minY, maxY, minZ, maxZ }

-- | Empty bounds (point at origin).
emptyBounds :: GlyphBounds
emptyBounds = glyphBounds (Pixel 0.0) (Pixel 0.0) (Pixel 0.0) (Pixel 0.0) (Pixel 0.0) (Pixel 0.0)

-- | Width of bounds.
boundsWidth :: GlyphBounds -> Pixel
boundsWidth b = b.maxX - b.minX

-- | Height of bounds.
boundsHeight :: GlyphBounds -> Pixel
boundsHeight b = b.maxY - b.minY

-- | Depth of bounds.
boundsDepth :: GlyphBounds -> Pixel
boundsDepth b = b.maxZ - b.minZ

-- | Union of two bounding boxes.
unionBounds :: GlyphBounds -> GlyphBounds -> GlyphBounds
unionBounds a b =
  { minX: minPx a.minX b.minX
  , maxX: maxPx a.maxX b.maxX
  , minY: minPx a.minY b.minY
  , maxY: maxPx a.maxY b.maxY
  , minZ: minPx a.minZ b.minZ
  , maxZ: maxPx a.maxZ b.maxZ
  }
  where
    minPx :: Pixel -> Pixel -> Pixel
    minPx (Pixel x) (Pixel y) = Pixel (if x < y then x else y)
    
    maxPx :: Pixel -> Pixel -> Pixel
    maxPx (Pixel x) (Pixel y) = Pixel (if x > y then x else y)

-- | Compute bounds from an array of 3D path commands.
computeBoundsFromCommands :: Array PathCommand3D -> GlyphBounds
computeBoundsFromCommands cmds =
  let points = extractPoints cmds
  in case Array.uncons points of
    Nothing -> emptyBounds
    Just { head, tail } -> foldl expandBounds (pointBounds head) tail
  where
    expandBounds :: GlyphBounds -> ControlPoint3D -> GlyphBounds
    expandBounds bounds pt =
      { minX: minPx bounds.minX pt.x
      , maxX: maxPx bounds.maxX pt.x
      , minY: minPx bounds.minY pt.y
      , maxY: maxPx bounds.maxY pt.y
      , minZ: minPx bounds.minZ pt.z
      , maxZ: maxPx bounds.maxZ pt.z
      }
    
    pointBounds :: ControlPoint3D -> GlyphBounds
    pointBounds pt = glyphBounds pt.x pt.x pt.y pt.y pt.z pt.z
    
    minPx :: Pixel -> Pixel -> Pixel
    minPx (Pixel x) (Pixel y) = Pixel (if x < y then x else y)
    
    maxPx :: Pixel -> Pixel -> Pixel
    maxPx (Pixel x) (Pixel y) = Pixel (if x > y then x else y)

-- | Extract all control points from path commands.
extractPoints :: Array PathCommand3D -> Array ControlPoint3D
extractPoints = Array.concatMap commandPoints
  where
    commandPoints :: PathCommand3D -> Array ControlPoint3D
    commandPoints (MoveTo3D p) = [p]
    commandPoints (LineTo3D p) = [p]
    commandPoints (QuadraticTo3D c1 end) = [c1, end]
    commandPoints (CubicTo3D c1 c2 end) = [c1, c2, end]
    commandPoints ClosePath3D = []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // glyphpath
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single character rendered as bezier geometry.
-- |
-- | This is the fundamental unit of typography-as-geometry. A GlyphPath
-- | contains all bezier paths needed to render a single character, including
-- | outer boundaries and counter-shapes (holes).
-- |
-- | ## Structure
-- |
-- | - contours: Array of closed paths. First is usually outer, rest are counters.
-- | - bounds: Pre-computed 3D bounding box for layout and culling.
-- | - advanceWidth: Horizontal distance to next glyph origin.
-- | - leftSideBearing: Space before the glyph's visible bounds.
-- |
-- | ## Animation
-- |
-- | Each control point can be individually animated via `mapControlPoints`.
-- | The structure preserves contour and command indices for targeting.
type GlyphPath =
  { contours :: Array Contour
  , bounds :: GlyphBounds
  , advanceWidth :: Pixel
  , leftSideBearing :: Pixel
  }

-- | Create an empty glyph (e.g., for space character).
-- |
-- | Space has no visible geometry but still has advance width.
emptyGlyph :: Pixel -> GlyphPath
emptyGlyph advanceWidth =
  { contours: []
  , bounds: emptyBounds
  , advanceWidth
  , leftSideBearing: Pixel 0.0
  }

-- | Create a glyph path from contours.
-- |
-- | Bounds are computed automatically from the geometry.
glyphPath :: Array Contour -> Pixel -> Pixel -> GlyphPath
glyphPath contours advanceWidth leftSideBearing =
  { contours
  , bounds: computeGlyphBounds contours
  , advanceWidth
  , leftSideBearing
  }
  where
    computeGlyphBounds :: Array Contour -> GlyphBounds
    computeGlyphBounds cs =
      let allCommands = Array.concatMap _.commands cs
      in computeBoundsFromCommands allCommands

-- | Add a contour to a glyph, recomputing bounds.
addContour :: Contour -> GlyphPath -> GlyphPath
addContour c gp =
  let newContours = Array.snoc gp.contours c
      contourBounds = computeBoundsFromCommands c.commands
  in gp
    { contours = newContours
    , bounds = unionBounds gp.bounds contourBounds
    }

-- | Get the outer contour (first clockwise contour).
-- |
-- | For well-formed glyphs, this is the main visible shape.
getOuterContour :: GlyphPath -> Maybe Contour
getOuterContour gp = Array.find (\c -> c.winding == WindingClockwise) gp.contours

-- | Get all counter contours (holes).
-- |
-- | For letters like 'O', 'A', '8', these are the interior cutouts.
getCounterContours :: GlyphPath -> Array Contour
getCounterContours gp = Array.filter (\c -> c.winding == WindingCounterClockwise) gp.contours

-- | Count total control points in glyph.
-- |
-- | Useful for animation budgeting and complexity analysis.
totalControlPoints :: GlyphPath -> Int
totalControlPoints gp =
  foldl (\acc c -> acc + countContourPoints c) 0 gp.contours
  where
    countContourPoints :: Contour -> Int
    countContourPoints c = foldl (\acc cmd -> acc + pointsInCommand cmd) 0 c.commands
    
    pointsInCommand :: PathCommand3D -> Int
    pointsInCommand (MoveTo3D _) = 1
    pointsInCommand (LineTo3D _) = 1
    pointsInCommand (QuadraticTo3D _ _) = 2
    pointsInCommand (CubicTo3D _ _ _) = 3
    pointsInCommand ClosePath3D = 0

-- | Map a function over all control points.
-- |
-- | Enables animation by transforming every point in the glyph.
-- | Bounds are recomputed after transformation.
mapControlPoints :: (ControlPoint3D -> ControlPoint3D) -> GlyphPath -> GlyphPath
mapControlPoints f gp =
  let newContours = map (mapContourPoints f) gp.contours
      allCommands = Array.concatMap _.commands newContours
  in gp
    { contours = newContours
    , bounds = computeBoundsFromCommands allCommands
    }
  where
    mapContourPoints :: (ControlPoint3D -> ControlPoint3D) -> Contour -> Contour
    mapContourPoints g c = c { commands = map (mapCommandPoint g) c.commands }
    
    mapCommandPoint :: (ControlPoint3D -> ControlPoint3D) -> PathCommand3D -> PathCommand3D
    mapCommandPoint g (MoveTo3D p) = MoveTo3D (g p)
    mapCommandPoint g (LineTo3D p) = LineTo3D (g p)
    mapCommandPoint g (QuadraticTo3D c1 end) = QuadraticTo3D (g c1) (g end)
    mapCommandPoint g (CubicTo3D c1 c2 end) = CubicTo3D (g c1) (g c2) (g end)
    mapCommandPoint _ ClosePath3D = ClosePath3D

-- | Apply a 2D transform (scale + translate) to glyph.
-- |
-- | Simplified transform for common layout operations.
transformGlyph
  :: { scaleX :: Number, scaleY :: Number, translateX :: Pixel, translateY :: Pixel }
  -> GlyphPath
  -> GlyphPath
transformGlyph t = mapControlPoints transformPoint
  where
    transformPoint :: ControlPoint3D -> ControlPoint3D
    transformPoint { x: Pixel px, y: Pixel py, z } =
      let Pixel tx = t.translateX
          Pixel ty = t.translateY
      in { x: Pixel (px * t.scaleX + tx)
         , y: Pixel (py * t.scaleY + ty)
         , z
         }

-- | Convert GlyphPath to 2D PathCommands (loses Z information).
-- |
-- | Used when rendering to 2D targets or integrating with existing Shape
-- | infrastructure.
glyphToPath2D :: GlyphPath -> Array PathCommand
glyphToPath2D gp = Array.concatMap contourToPath2D gp.contours
  where
    contourToPath2D :: Contour -> Array PathCommand
    contourToPath2D c = map command3DTo2D c.commands
    
    command3DTo2D :: PathCommand3D -> PathCommand
    command3DTo2D (MoveTo3D p) = MoveTo (to2D p)
    command3DTo2D (LineTo3D p) = LineTo (to2D p)
    command3DTo2D (QuadraticTo3D c1 end) = QuadraticTo (to2D c1) (to2D end)
    command3DTo2D (CubicTo3D c1 c2 end) = CubicTo (to2D c1) (to2D c2) (to2D end)
    command3DTo2D ClosePath3D = ClosePath
    
    to2D :: ControlPoint3D -> PixelPoint2D
    to2D { x, y } = { x, y }
