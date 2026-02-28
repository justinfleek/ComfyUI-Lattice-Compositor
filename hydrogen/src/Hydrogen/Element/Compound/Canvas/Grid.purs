-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // compound // canvas // grid
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Grid — Bounded visual grids with snap points.
-- |
-- | ## Design Philosophy
-- |
-- | Grids for design canvases must be:
-- |
-- | 1. **Bounded** — Never infinitely small (unusable), never infinitely large
-- | 2. **Snappable** — Every grid point can be a snap target
-- | 3. **Dynamic** — Adapt to zoom level (show more detail when zoomed in)
-- | 4. **Deterministic** — Same inputs = same grid, always
-- |
-- | ## Bounded Parameters
-- |
-- | - **GridSpacing**: 1 to 10000 canvas units (pixels at 100% zoom)
-- | - **Subdivisions**: 1 to 10 (no subdivision to decimal precision)
-- | - **Angle**: 0° to 90° (covers all unique orientations via symmetry)
-- | - **RadialDivisions**: 2 to 360 (half-circles to degree precision)
-- |
-- | ## Grid Types
-- |
-- | - **Square**: Standard rectangular grid (UI, general design)
-- | - **Isometric**: 30° grid for 2.5D/game art
-- | - **Perspective**: 1/2/3 point perspective with vanishing points
-- | - **Polar**: Radial grid for circular designs
-- | - **Hexagonal**: Honeycomb pattern for game maps
-- | - **GoldenRatio**: Phi-spaced lines for classical composition
-- | - **RuleOfThirds**: 9-section grid for photography
-- | - **Baseline**: Horizontal lines for typography
-- | - **Modular**: Column + gutter system for print
-- | - **Dot**: Minimal dots at intersections only
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Angle (bounded angles)
-- | - Canvas.Types (GridConfig, GridStyle)
-- | - Canvas.State (CanvasState, viewport access)

module Hydrogen.Element.Compound.Canvas.Grid
  ( -- * Bounded Grid Spacing
    GridSpacing
  , gridSpacing
  , spacingValue
  , minSpacing
  , maxSpacing
  , defaultSpacing
  , doubleSpacing
  , halveSpacing
  , clampSpacing
  
  -- * Bounded Subdivisions
  , Subdivisions
  , subdivisions
  , subdivisionsValue
  , minSubdivisions
  , maxSubdivisions
  , noSubdivisions
  , decimalSubdivisions
  
  -- * Extended Grid Types
  , ExtendedGridStyle(..)
  , gridStyleAngle
  , isIsometricFamily
  , isPerspectiveFamily
  , isRadialFamily
  
  -- * Grid Geometry
  , GridGeometry
  , gridGeometry
  , geometryLines
  , geometrySnapPoints
  , geometryMajorLines
  , geometryMinorLines
  
  -- * Snap Point Computation
  , SnapPoint
  , snapPoint
  , snapPointPosition
  , snapPointType
  , SnapPointType(..)
  , nearestSnapPoint
  , snapPointsInBounds
  , snapToGrid
  
  -- * Zoom-Adaptive Display
  , ZoomLevel
  , zoomLevel
  , visibleGridLevel
  , effectiveSpacing
  , shouldShowMajorLines
  , shouldShowMinorLines
  , shouldShowDots
  
  -- * Grid Line Generation
  , GridLine
  , gridLine
  , lineStart
  , lineEnd
  , lineIsMajor
  , generateSquareGrid
  , generateIsometricGrid
  , generatePolarGrid
  , generateHexGrid
  
  -- * Perspective Grid
  , VanishingPoint
  , vanishingPoint
  , vpPosition
  , vpHorizonY
  , PerspectiveGrid
  , perspectiveGrid1Point
  , perspectiveGrid2Point
  , perspectiveGrid3Point
  , perspectiveRays
  
  -- * Composition Grids
  , goldenRatioGrid
  , ruleOfThirdsGrid
  , diagonalGrid
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , otherwise
  , (<>)
  , (==)
  , (/=)
  , (&&)
  , (||)
  , (>)
  , (<)
  , (>=)
  , (<=)
  , (+)
  , (-)
  , (*)
  , (/)
  , ($)
  , max
  , min
  , not
  , negate
  )

import Data.Array (filter, concat, length, snoc, index, head, null)
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Int (toNumber, floor) as Int

import Hydrogen.Schema.Geometry.Angle (Degrees, degrees, unwrapDegrees)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // bounded grid spacing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid spacing with bounds.
-- |
-- | **Bounds:**
-- | - Minimum: 1.0 canvas unit (any smaller is visual noise)
-- | - Maximum: 10000.0 canvas units (any larger is effectively no grid)
-- |
-- | At 100% zoom, 1 canvas unit = 1 pixel. At 200% zoom, 1 canvas unit = 2 pixels.
-- |
-- | **Why these bounds?**
-- | - Min 1: A 1-pixel grid at 100% is already very fine. Going smaller
-- |   creates more lines than pixels, which is meaningless.
-- | - Max 10000: A 10000-pixel grid has at most 1-2 lines visible on any
-- |   reasonable viewport. Going larger means 0 lines visible.
newtype GridSpacing = GridSpacing Number

derive instance eqGridSpacing :: Eq GridSpacing
derive instance ordGridSpacing :: Ord GridSpacing

instance showGridSpacing :: Show GridSpacing where
  show (GridSpacing s) = show s <> "px"

-- | Minimum allowed grid spacing.
minSpacing :: Number
minSpacing = 1.0

-- | Maximum allowed grid spacing.
maxSpacing :: Number
maxSpacing = 10000.0

-- | Create bounded grid spacing.
-- |
-- | Values are clamped to [1.0, 10000.0].
gridSpacing :: Number -> GridSpacing
gridSpacing n = GridSpacing $ clampSpacing n

-- | Clamp a number to valid spacing range.
clampSpacing :: Number -> Number
clampSpacing n = max minSpacing (min maxSpacing n)

-- | Extract spacing value.
spacingValue :: GridSpacing -> Number
spacingValue (GridSpacing s) = s

-- | Default grid spacing (10 pixels).
defaultSpacing :: GridSpacing
defaultSpacing = GridSpacing 10.0

-- | Double the grid spacing (zoom out grid).
-- |
-- | Clamped to maximum.
doubleSpacing :: GridSpacing -> GridSpacing
doubleSpacing (GridSpacing s) = gridSpacing (s * 2.0)

-- | Halve the grid spacing (zoom in grid).
-- |
-- | Clamped to minimum.
halveSpacing :: GridSpacing -> GridSpacing
halveSpacing (GridSpacing s) = gridSpacing (s / 2.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // bounded subdivisions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number of subdivisions per grid cell.
-- |
-- | **Bounds:**
-- | - Minimum: 1 (no subdivision — major lines only)
-- | - Maximum: 10 (decimal precision — 10ths of a cell)
-- |
-- | **Common values:**
-- | - 1: Major lines only
-- | - 2: Halves
-- | - 4: Quarters (imperial friendly)
-- | - 5: Fifths (metric friendly)
-- | - 10: Decimal (base-10 precision)
newtype Subdivisions = Subdivisions Int

derive instance eqSubdivisions :: Eq Subdivisions
derive instance ordSubdivisions :: Ord Subdivisions

instance showSubdivisions :: Show Subdivisions where
  show (Subdivisions n) = show n <> " subdivisions"

-- | Minimum subdivisions.
minSubdivisions :: Int
minSubdivisions = 1

-- | Maximum subdivisions.
maxSubdivisions :: Int
maxSubdivisions = 10

-- | Create bounded subdivisions.
-- |
-- | Values are clamped to [1, 10].
subdivisions :: Int -> Subdivisions
subdivisions n = Subdivisions $ max minSubdivisions (min maxSubdivisions n)

-- | Extract subdivision count.
subdivisionsValue :: Subdivisions -> Int
subdivisionsValue (Subdivisions n) = n

-- | No subdivisions (major lines only).
noSubdivisions :: Subdivisions
noSubdivisions = Subdivisions 1

-- | Decimal subdivisions (10ths).
decimalSubdivisions :: Subdivisions
decimalSubdivisions = Subdivisions 10

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // extended grid styles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extended grid styles beyond the basic Types.GridStyle.
-- |
-- | Includes all professional grid types with their specific parameters.
data ExtendedGridStyle
  -- Basic grids
  = StyleSquare                                    -- ^ Standard rectangular grid
  | StyleDot                                       -- ^ Dots at intersections only
  | StyleCrosshair                                 -- ^ Small + at intersections
  
  -- Isometric family (bounded angle: 0° to 90°)
  | StyleIsometric Degrees                         -- ^ Isometric with custom angle
  | StyleIsometric30                               -- ^ Classic 30° isometric
  | StyleIsometric45                               -- ^ 45° dimetric
  
  -- Perspective family (bounded: 1-3 vanishing points)
  | StylePerspective1 VanishingPoint               -- ^ 1-point perspective
  | StylePerspective2 VanishingPoint VanishingPoint -- ^ 2-point perspective
  | StylePerspective3 VanishingPoint VanishingPoint VanishingPoint -- ^ 3-point
  
  -- Radial family (bounded divisions: 2 to 360)
  | StylePolar Int                                 -- ^ Radial with n divisions
  | StyleHexagonal                                 -- ^ Hexagonal honeycomb
  
  -- Composition grids
  | StyleGoldenRatio                               -- ^ Golden ratio (φ) divisions
  | StyleRuleOfThirds                              -- ^ 3×3 grid
  | StyleDiagonal                                  -- ^ Diagonal guidelines

derive instance eqExtendedGridStyle :: Eq ExtendedGridStyle

instance showExtendedGridStyle :: Show ExtendedGridStyle where
  show StyleSquare = "square"
  show StyleDot = "dot"
  show StyleCrosshair = "crosshair"
  show (StyleIsometric angle) = "isometric(" <> show angle <> ")"
  show StyleIsometric30 = "isometric-30"
  show StyleIsometric45 = "isometric-45"
  show (StylePerspective1 _) = "perspective-1pt"
  show (StylePerspective2 _ _) = "perspective-2pt"
  show (StylePerspective3 _ _ _) = "perspective-3pt"
  show (StylePolar n) = "polar(" <> show n <> ")"
  show StyleHexagonal = "hexagonal"
  show StyleGoldenRatio = "golden-ratio"
  show StyleRuleOfThirds = "rule-of-thirds"
  show StyleDiagonal = "diagonal"

-- | Get the angle associated with a grid style (for isometric family).
gridStyleAngle :: ExtendedGridStyle -> Maybe Degrees
gridStyleAngle (StyleIsometric angle) = Just angle
gridStyleAngle StyleIsometric30 = Just (degrees 30.0)
gridStyleAngle StyleIsometric45 = Just (degrees 45.0)
gridStyleAngle _ = Nothing

-- | Check if style is in the isometric family.
isIsometricFamily :: ExtendedGridStyle -> Boolean
isIsometricFamily (StyleIsometric _) = true
isIsometricFamily StyleIsometric30 = true
isIsometricFamily StyleIsometric45 = true
isIsometricFamily _ = false

-- | Check if style is in the perspective family.
isPerspectiveFamily :: ExtendedGridStyle -> Boolean
isPerspectiveFamily (StylePerspective1 _) = true
isPerspectiveFamily (StylePerspective2 _ _) = true
isPerspectiveFamily (StylePerspective3 _ _ _) = true
isPerspectiveFamily _ = false

-- | Check if style is in the radial family.
isRadialFamily :: ExtendedGridStyle -> Boolean
isRadialFamily (StylePolar _) = true
isRadialFamily StyleHexagonal = true
isRadialFamily _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // vanishing point
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vanishing point for perspective grids.
-- |
-- | Position is in canvas coordinates.
-- | HorizonY is the y-coordinate of the horizon line.
newtype VanishingPoint = VanishingPoint 
  { x :: Number
  , y :: Number
  , horizonY :: Number
  }

derive instance eqVanishingPoint :: Eq VanishingPoint

instance showVanishingPoint :: Show VanishingPoint where
  show (VanishingPoint vp) = "VP(" <> show vp.x <> "," <> show vp.y <> ")"

-- | Create a vanishing point.
vanishingPoint :: Number -> Number -> Number -> VanishingPoint
vanishingPoint x y horizonY = VanishingPoint { x, y, horizonY }

-- | Get vanishing point position.
vpPosition :: VanishingPoint -> { x :: Number, y :: Number }
vpPosition (VanishingPoint vp) = { x: vp.x, y: vp.y }

-- | Get horizon Y coordinate.
vpHorizonY :: VanishingPoint -> Number
vpHorizonY (VanishingPoint vp) = vp.horizonY

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // snap points
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of snap point.
data SnapPointType
  = SnapMajorIntersection   -- ^ Major grid line intersection
  | SnapMinorIntersection   -- ^ Minor grid line intersection
  | SnapHexCenter           -- ^ Center of hexagonal cell
  | SnapHexVertex           -- ^ Vertex of hexagonal cell
  | SnapPolarCenter         -- ^ Center of polar grid
  | SnapPolarIntersection   -- ^ Radial/arc intersection
  | SnapVanishingPoint      -- ^ Perspective vanishing point
  | SnapCompositionPoint    -- ^ Golden ratio / rule of thirds

derive instance eqSnapPointType :: Eq SnapPointType
derive instance ordSnapPointType :: Ord SnapPointType

instance showSnapPointType :: Show SnapPointType where
  show SnapMajorIntersection = "major"
  show SnapMinorIntersection = "minor"
  show SnapHexCenter = "hex-center"
  show SnapHexVertex = "hex-vertex"
  show SnapPolarCenter = "polar-center"
  show SnapPolarIntersection = "polar-intersection"
  show SnapVanishingPoint = "vanishing-point"
  show SnapCompositionPoint = "composition"

-- | A point that can be snapped to.
newtype SnapPoint = SnapPoint
  { x :: Number
  , y :: Number
  , pointType :: SnapPointType
  }

derive instance eqSnapPoint :: Eq SnapPoint

instance showSnapPoint :: Show SnapPoint where
  show (SnapPoint sp) = "SnapPoint(" <> show sp.x <> "," <> show sp.y <> ")"

-- | Create a snap point.
snapPoint :: Number -> Number -> SnapPointType -> SnapPoint
snapPoint x y pointType = SnapPoint { x, y, pointType }

-- | Get snap point position.
snapPointPosition :: SnapPoint -> { x :: Number, y :: Number }
snapPointPosition (SnapPoint sp) = { x: sp.x, y: sp.y }

-- | Get snap point type.
snapPointType :: SnapPoint -> SnapPointType
snapPointType (SnapPoint sp) = sp.pointType

-- | Find the nearest snap point to a position.
-- |
-- | Returns Nothing if no snap points are within the threshold distance.
nearestSnapPoint :: Number -> { x :: Number, y :: Number } -> Array SnapPoint -> Maybe SnapPoint
nearestSnapPoint threshold pos points =
  case points of
    [] -> Nothing
    _ -> 
      let 
        withDist = map (\sp -> { point: sp, dist: distanceTo pos sp }) points
        sorted = sortByDistance withDist
      in case head sorted of
        Nothing -> Nothing
        Just closest -> 
          if closest.dist <= threshold 
            then Just closest.point 
            else Nothing

-- | Get all snap points within given bounds.
snapPointsInBounds :: { x :: Number, y :: Number, width :: Number, height :: Number } 
                   -> Array SnapPoint 
                   -> Array SnapPoint
snapPointsInBounds bounds points =
  filter (\(SnapPoint sp) -> 
    sp.x >= bounds.x && sp.x <= bounds.x + bounds.width &&
    sp.y >= bounds.y && sp.y <= bounds.y + bounds.height
  ) points

-- | Snap a position to the grid.
-- |
-- | Given spacing and subdivisions, find the nearest grid intersection.
snapToGrid :: GridSpacing -> Subdivisions -> { x :: Number, y :: Number } -> { x :: Number, y :: Number }
snapToGrid (GridSpacing spacing) (Subdivisions subs) pos =
  let 
    step = spacing / Int.toNumber subs
    snapValue v = Int.toNumber (Int.floor ((v / step) + 0.5)) * step
  in { x: snapValue pos.x, y: snapValue pos.y }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // zoom level
-- ═════════════════════════════════════════════════════════════════════════════

-- | Zoom level wrapper.
-- |
-- | Bounded: 0.1 (10%) to 10.0 (1000%)
newtype ZoomLevel = ZoomLevel Number

derive instance eqZoomLevel :: Eq ZoomLevel
derive instance ordZoomLevel :: Ord ZoomLevel

instance showZoomLevel :: Show ZoomLevel where
  show (ZoomLevel z) = show (z * 100.0) <> "%"

-- | Create bounded zoom level.
zoomLevel :: Number -> ZoomLevel
zoomLevel z = ZoomLevel $ max 0.1 (min 10.0 z)

-- | Determine which grid level should be visible at current zoom.
-- |
-- | Returns the spacing multiplier:
-- | - At high zoom (>200%), show minor lines
-- | - At normal zoom (50%-200%), show major lines
-- | - At low zoom (<50%), hide minor lines, increase major spacing
visibleGridLevel :: ZoomLevel -> Int
visibleGridLevel (ZoomLevel z)
  | z >= 2.0 = 1    -- Show finest detail
  | z >= 1.0 = 2    -- Normal detail
  | z >= 0.5 = 4    -- Reduced detail
  | z >= 0.25 = 8   -- Coarse grid
  | otherwise = 16  -- Very coarse grid

-- | Calculate effective spacing at current zoom.
-- |
-- | Adjusts spacing so grid doesn't become too dense or sparse.
effectiveSpacing :: GridSpacing -> ZoomLevel -> Number
effectiveSpacing (GridSpacing spacing) zoom =
  let 
    level = visibleGridLevel zoom
    adjusted = spacing * Int.toNumber level
  in clampSpacing adjusted

-- | Should major grid lines be shown at this zoom?
shouldShowMajorLines :: ZoomLevel -> Boolean
shouldShowMajorLines (ZoomLevel z) = z >= 0.1  -- Always show major lines

-- | Should minor grid lines be shown at this zoom?
shouldShowMinorLines :: ZoomLevel -> Boolean
shouldShowMinorLines (ZoomLevel z) = z >= 0.5  -- Hide below 50% zoom

-- | Should dots be shown at this zoom?
shouldShowDots :: ZoomLevel -> Boolean
shouldShowDots (ZoomLevel z) = z >= 0.25  -- Hide below 25% zoom

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // grid lines
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single grid line.
newtype GridLine = GridLine
  { x1 :: Number
  , y1 :: Number
  , x2 :: Number
  , y2 :: Number
  , isMajor :: Boolean
  }

derive instance eqGridLine :: Eq GridLine

instance showGridLine :: Show GridLine where
  show (GridLine l) = 
    "Line(" <> show l.x1 <> "," <> show l.y1 <> "->" <> 
    show l.x2 <> "," <> show l.y2 <> ")"

-- | Create a grid line.
gridLine :: Number -> Number -> Number -> Number -> Boolean -> GridLine
gridLine x1 y1 x2 y2 isMajor = GridLine { x1, y1, x2, y2, isMajor }

-- | Get line start point.
lineStart :: GridLine -> { x :: Number, y :: Number }
lineStart (GridLine l) = { x: l.x1, y: l.y1 }

-- | Get line end point.
lineEnd :: GridLine -> { x :: Number, y :: Number }
lineEnd (GridLine l) = { x: l.x2, y: l.y2 }

-- | Check if line is major (vs minor).
lineIsMajor :: GridLine -> Boolean
lineIsMajor (GridLine l) = l.isMajor

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // grid geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete grid geometry (lines + snap points).
newtype GridGeometry = GridGeometry
  { lines :: Array GridLine
  , snapPoints :: Array SnapPoint
  }

instance showGridGeometry :: Show GridGeometry where
  show (GridGeometry g) = 
    "GridGeometry(" <> show (length g.lines) <> " lines, " <>
    show (length g.snapPoints) <> " snap points)"

-- | Create grid geometry.
gridGeometry :: Array GridLine -> Array SnapPoint -> GridGeometry
gridGeometry lines snapPoints = GridGeometry { lines, snapPoints }

-- | Get all grid lines.
geometryLines :: GridGeometry -> Array GridLine
geometryLines (GridGeometry g) = g.lines

-- | Get all snap points.
geometrySnapPoints :: GridGeometry -> Array SnapPoint
geometrySnapPoints (GridGeometry g) = g.snapPoints

-- | Get only major grid lines.
geometryMajorLines :: GridGeometry -> Array GridLine
geometryMajorLines (GridGeometry g) = filter lineIsMajor g.lines

-- | Get only minor grid lines.
geometryMinorLines :: GridGeometry -> Array GridLine
geometryMinorLines (GridGeometry g) = filter isMinor g.lines
  where
    isMinor line = not (lineIsMajor line)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // grid line generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate a square grid within bounds.
generateSquareGrid :: GridSpacing 
                   -> Subdivisions 
                   -> { x :: Number, y :: Number, width :: Number, height :: Number }
                   -> GridGeometry
generateSquareGrid (GridSpacing spacing) (Subdivisions subs) bounds =
  let 
    minorStep = spacing / Int.toNumber subs
    
    -- Calculate start/end for lines (extend beyond bounds for clean edges)
    startX = Int.toNumber (Int.floor (bounds.x / spacing)) * spacing
    endX = bounds.x + bounds.width
    startY = Int.toNumber (Int.floor (bounds.y / spacing)) * spacing
    endY = bounds.y + bounds.height
    
    -- Generate vertical lines
    verticalLines = generateLinesRange startX endX minorStep spacing bounds.y (bounds.y + bounds.height) true
    
    -- Generate horizontal lines
    horizontalLines = generateLinesRange startY endY minorStep spacing bounds.x (bounds.x + bounds.width) false
    
    -- Generate snap points at intersections
    points = generateGridSnapPoints startX endX startY endY minorStep spacing
    
  in GridGeometry 
    { lines: concat [verticalLines, horizontalLines]
    , snapPoints: points
    }

-- | Generate an isometric grid.
generateIsometricGrid :: Degrees 
                      -> GridSpacing 
                      -> { x :: Number, y :: Number, width :: Number, height :: Number }
                      -> GridGeometry
generateIsometricGrid angle (GridSpacing spacing) bounds =
  let 
    angleDeg = unwrapDegrees angle
    angleRad = angleDeg * 3.14159265359 / 180.0
    
    -- Horizontal lines (same as square grid)
    horizontalLines = generateHorizontalLines bounds.y (bounds.y + bounds.height) spacing bounds.x (bounds.x + bounds.width)
    
    -- Diagonal lines at +angle
    diagonalUp = generateDiagonalLines angleDeg spacing bounds
    
    -- Diagonal lines at -angle
    diagonalDown = generateDiagonalLines (negate angleDeg) spacing bounds
    
    -- Snap points at intersections (simplified - major points only)
    points = []  -- TODO: Calculate isometric intersections
    
  in GridGeometry 
    { lines: concat [horizontalLines, diagonalUp, diagonalDown]
    , snapPoints: points
    }

-- | Generate a polar/radial grid.
generatePolarGrid :: { x :: Number, y :: Number }  -- ^ Center
                  -> Int                           -- ^ Number of radial divisions (clamped 2-360)
                  -> GridSpacing                   -- ^ Spacing between rings
                  -> Number                        -- ^ Maximum radius
                  -> GridGeometry
generatePolarGrid center divisions (GridSpacing ringSpacing) maxRadius =
  let 
    -- Clamp divisions to valid range
    div = max 2 (min 360 divisions)
    angleStep = 360.0 / Int.toNumber div
    
    -- Generate radial lines from center
    radialLines = generateRadialLines center div maxRadius
    
    -- Generate concentric rings
    rings = generateConcentricRings center ringSpacing maxRadius
    
    -- Center is always a snap point
    centerPoint = snapPoint center.x center.y SnapPolarCenter
    
  in GridGeometry
    { lines: concat [radialLines, rings]
    , snapPoints: [centerPoint]  -- TODO: Add ring intersections
    }

-- | Generate a hexagonal grid.
generateHexGrid :: GridSpacing 
                -> { x :: Number, y :: Number, width :: Number, height :: Number }
                -> GridGeometry
generateHexGrid (GridSpacing size) bounds =
  let 
    -- Hex dimensions
    hexWidth = size * 2.0
    hexHeight = size * 1.732050808  -- sqrt(3)
    
    -- Generate hex centers and vertices
    points = generateHexPoints size bounds
    
    -- Generate hex edges
    lines = generateHexLines size bounds
    
  in GridGeometry
    { lines: lines
    , snapPoints: points
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // perspective grid
-- ═════════════════════════════════════════════════════════════════════════════

-- | Perspective grid configuration.
newtype PerspectiveGrid = PerspectiveGrid
  { vanishingPoints :: Array VanishingPoint
  , rayCount :: Int  -- Rays per vanishing point (bounded 4-64)
  }

instance showPerspectiveGrid :: Show PerspectiveGrid where
  show (PerspectiveGrid p) = 
    "PerspectiveGrid(" <> show (length p.vanishingPoints) <> "-point)"

-- | Create 1-point perspective grid.
perspectiveGrid1Point :: VanishingPoint -> Int -> PerspectiveGrid
perspectiveGrid1Point vp rays = PerspectiveGrid 
  { vanishingPoints: [vp]
  , rayCount: max 4 (min 64 rays)
  }

-- | Create 2-point perspective grid.
perspectiveGrid2Point :: VanishingPoint -> VanishingPoint -> Int -> PerspectiveGrid
perspectiveGrid2Point vp1 vp2 rays = PerspectiveGrid 
  { vanishingPoints: [vp1, vp2]
  , rayCount: max 4 (min 64 rays)
  }

-- | Create 3-point perspective grid.
perspectiveGrid3Point :: VanishingPoint -> VanishingPoint -> VanishingPoint -> Int -> PerspectiveGrid
perspectiveGrid3Point vp1 vp2 vp3 rays = PerspectiveGrid 
  { vanishingPoints: [vp1, vp2, vp3]
  , rayCount: max 4 (min 64 rays)
  }

-- | Generate perspective rays from all vanishing points.
perspectiveRays :: PerspectiveGrid 
                -> { x :: Number, y :: Number, width :: Number, height :: Number }
                -> Array GridLine
perspectiveRays (PerspectiveGrid pg) bounds =
  concat $ map (\vp -> generateRaysFromVP vp pg.rayCount bounds) pg.vanishingPoints

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // composition grids
-- ═════════════════════════════════════════════════════════════════════════════

-- | Golden ratio (φ = 1.618...) grid.
goldenRatioGrid :: { width :: Number, height :: Number } -> GridGeometry
goldenRatioGrid size =
  let 
    phi = 1.6180339887  -- Golden ratio
    
    -- Vertical divisions at 1/φ and (φ-1)/φ
    v1 = size.width / phi
    v2 = size.width - v1
    
    -- Horizontal divisions at 1/φ and (φ-1)/φ
    h1 = size.height / phi
    h2 = size.height - h1
    
    lines = 
      [ gridLine v1 0.0 v1 size.height true
      , gridLine v2 0.0 v2 size.height true
      , gridLine 0.0 h1 size.width h1 true
      , gridLine 0.0 h2 size.width h2 true
      ]
    
    -- Intersection points
    points = 
      [ snapPoint v1 h1 SnapCompositionPoint
      , snapPoint v1 h2 SnapCompositionPoint
      , snapPoint v2 h1 SnapCompositionPoint
      , snapPoint v2 h2 SnapCompositionPoint
      ]
    
  in GridGeometry { lines, snapPoints: points }

-- | Rule of thirds grid.
ruleOfThirdsGrid :: { width :: Number, height :: Number } -> GridGeometry
ruleOfThirdsGrid size =
  let 
    third = 1.0 / 3.0
    twoThirds = 2.0 / 3.0
    
    v1 = size.width * third
    v2 = size.width * twoThirds
    h1 = size.height * third
    h2 = size.height * twoThirds
    
    lines = 
      [ gridLine v1 0.0 v1 size.height true
      , gridLine v2 0.0 v2 size.height true
      , gridLine 0.0 h1 size.width h1 true
      , gridLine 0.0 h2 size.width h2 true
      ]
    
    -- Power points (intersections)
    points = 
      [ snapPoint v1 h1 SnapCompositionPoint
      , snapPoint v1 h2 SnapCompositionPoint
      , snapPoint v2 h1 SnapCompositionPoint
      , snapPoint v2 h2 SnapCompositionPoint
      ]
    
  in GridGeometry { lines, snapPoints: points }

-- | Diagonal guidelines.
diagonalGrid :: { width :: Number, height :: Number } -> GridGeometry
diagonalGrid size =
  let 
    lines = 
      [ gridLine 0.0 0.0 size.width size.height true          -- Top-left to bottom-right
      , gridLine size.width 0.0 0.0 size.height true          -- Top-right to bottom-left
      , gridLine 0.0 size.height size.width 0.0 true          -- Bottom-left to top-right (same as above)
      ]
    
    -- Center point
    centerX = size.width / 2.0
    centerY = size.height / 2.0
    points = [snapPoint centerX centerY SnapCompositionPoint]
    
  in GridGeometry { lines, snapPoints: points }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Distance from a position to a snap point.
distanceTo :: { x :: Number, y :: Number } -> SnapPoint -> Number
distanceTo pos (SnapPoint sp) =
  let 
    dx = pos.x - sp.x
    dy = pos.y - sp.y
  in sqrt (dx * dx + dy * dy)

-- | Approximate square root using Newton's method.
sqrt :: Number -> Number
sqrt n =
  if n <= 0.0 then 0.0
  else newtonSqrt n (n / 2.0) 0

-- | Newton's method for square root (max 10 iterations).
newtonSqrt :: Number -> Number -> Int -> Number
newtonSqrt n guess iterations =
  if iterations >= 10 then guess
  else 
    let nextGuess = (guess + n / guess) / 2.0
    in if abs (nextGuess - guess) < 0.0001 
       then nextGuess 
       else newtonSqrt n nextGuess (iterations + 1)

-- | Absolute value.
abs :: Number -> Number
abs n = if n < 0.0 then negate n else n

-- | Sort by distance (simple insertion sort for small arrays).
sortByDistance :: Array { point :: SnapPoint, dist :: Number } -> Array { point :: SnapPoint, dist :: Number }
sortByDistance arr = foldl insertSorted [] arr

-- | Insert into sorted array.
insertSorted :: Array { point :: SnapPoint, dist :: Number } 
             -> { point :: SnapPoint, dist :: Number } 
             -> Array { point :: SnapPoint, dist :: Number }
insertSorted sorted item =
  let 
    smaller = filter (\x -> x.dist < item.dist) sorted
    larger = filter (\x -> x.dist >= item.dist) sorted
  in concat [smaller, [item], larger]

-- | Generate lines in a range (helper for square grid).
generateLinesRange :: Number -> Number -> Number -> Number -> Number -> Number -> Boolean -> Array GridLine
generateLinesRange start end minorStep majorSpacing lineStart' lineEnd' isVertical =
  generateLinesHelper start end minorStep majorSpacing lineStart' lineEnd' isVertical []

-- | Helper for line generation.
generateLinesHelper :: Number -> Number -> Number -> Number -> Number -> Number -> Boolean -> Array GridLine -> Array GridLine
generateLinesHelper current end minorStep majorSpacing lineStart' lineEnd' isVertical acc =
  if current > end then acc
  else 
    let 
      isMajor = isMajorLine current majorSpacing minorStep
      line = if isVertical 
             then gridLine current lineStart' current lineEnd' isMajor
             else gridLine lineStart' current lineEnd' current isMajor
      newAcc = snoc acc line
    in generateLinesHelper (current + minorStep) end minorStep majorSpacing lineStart' lineEnd' isVertical newAcc

-- | Check if a position is on a major line.
isMajorLine :: Number -> Number -> Number -> Boolean
isMajorLine pos majorSpacing minorStep =
  let 
    ratio = pos / majorSpacing
    rounded = Int.toNumber (Int.floor (ratio + 0.0001))
  in abs (ratio - rounded) < 0.0001

-- | Generate snap points for a square grid.
generateGridSnapPoints :: Number -> Number -> Number -> Number -> Number -> Number -> Array SnapPoint
generateGridSnapPoints startX endX startY endY minorStep majorSpacing =
  generateSnapPointsHelper startX endX startY endY minorStep majorSpacing startX startY []

-- | Helper for snap point generation.
generateSnapPointsHelper :: Number -> Number -> Number -> Number -> Number -> Number -> Number -> Number -> Array SnapPoint -> Array SnapPoint
generateSnapPointsHelper endX endY startY' _endY' minorStep majorSpacing currentX currentY acc =
  if currentX > endX then acc
  else if currentY > endY then 
    generateSnapPointsHelper endX endY startY' endY minorStep majorSpacing (currentX + minorStep) startY' acc
  else
    let 
      isMajorX = isMajorLine currentX majorSpacing minorStep
      isMajorY = isMajorLine currentY majorSpacing minorStep
      pointType = if isMajorX && isMajorY then SnapMajorIntersection else SnapMinorIntersection
      point = snapPoint currentX currentY pointType
      newAcc = snoc acc point
    in generateSnapPointsHelper endX endY startY' endY minorStep majorSpacing currentX (currentY + minorStep) newAcc

-- | Generate horizontal lines.
generateHorizontalLines :: Number -> Number -> Number -> Number -> Number -> Array GridLine
generateHorizontalLines start end spacing lineStart' lineEnd' =
  generateHorizontalHelper start end spacing lineStart' lineEnd' []

generateHorizontalHelper :: Number -> Number -> Number -> Number -> Number -> Array GridLine -> Array GridLine
generateHorizontalHelper current end spacing lineStart' lineEnd' acc =
  if current > end then acc
  else 
    let line = gridLine lineStart' current lineEnd' current true
        newAcc = snoc acc line
    in generateHorizontalHelper (current + spacing) end spacing lineStart' lineEnd' newAcc

-- | Generate diagonal lines at an angle (simplified).
generateDiagonalLines :: Number -> Number -> { x :: Number, y :: Number, width :: Number, height :: Number } -> Array GridLine
generateDiagonalLines _angleDeg _spacing _bounds = []  -- TODO: Implement

-- | Generate radial lines from center.
generateRadialLines :: { x :: Number, y :: Number } -> Int -> Number -> Array GridLine
generateRadialLines center divisions maxRadius =
  generateRadialHelper center divisions maxRadius 0 []

generateRadialHelper :: { x :: Number, y :: Number } -> Int -> Number -> Int -> Array GridLine -> Array GridLine
generateRadialHelper center divisions maxRadius current acc =
  if current >= divisions then acc
  else
    let 
      angleDeg = 360.0 * Int.toNumber current / Int.toNumber divisions
      angleRad = angleDeg * 3.14159265359 / 180.0
      endX = center.x + maxRadius * cosApprox angleRad
      endY = center.y + maxRadius * sinApprox angleRad
      line = gridLine center.x center.y endX endY true
      newAcc = snoc acc line
    in generateRadialHelper center divisions maxRadius (current + 1) newAcc

-- | Generate concentric rings.
generateConcentricRings :: { x :: Number, y :: Number } -> Number -> Number -> Array GridLine
generateConcentricRings _center _spacing _maxRadius = []  -- Rings are arcs, not lines - TODO

-- | Generate hex points.
generateHexPoints :: Number -> { x :: Number, y :: Number, width :: Number, height :: Number } -> Array SnapPoint
generateHexPoints _size _bounds = []  -- TODO: Implement

-- | Generate hex lines.
generateHexLines :: Number -> { x :: Number, y :: Number, width :: Number, height :: Number } -> Array GridLine
generateHexLines _size _bounds = []  -- TODO: Implement

-- | Generate rays from a vanishing point.
generateRaysFromVP :: VanishingPoint -> Int -> { x :: Number, y :: Number, width :: Number, height :: Number } -> Array GridLine
generateRaysFromVP (VanishingPoint vp) rayCount bounds =
  generateVPRaysHelper vp rayCount bounds 0 []

generateVPRaysHelper :: { x :: Number, y :: Number, horizonY :: Number } -> Int -> { x :: Number, y :: Number, width :: Number, height :: Number } -> Int -> Array GridLine -> Array GridLine
generateVPRaysHelper vp rayCount bounds current acc =
  if current >= rayCount then acc
  else
    let 
      -- Distribute rays evenly across viewport width
      targetX = bounds.x + bounds.width * Int.toNumber current / Int.toNumber (rayCount - 1)
      targetY = bounds.y + bounds.height  -- Bottom of viewport
      line = gridLine vp.x vp.y targetX targetY true
      newAcc = snoc acc line
    in generateVPRaysHelper vp rayCount bounds (current + 1) newAcc

-- | Approximate cosine using Taylor series.
cosApprox :: Number -> Number
cosApprox x = 
  let x2 = x * x
      x4 = x2 * x2
      x6 = x4 * x2
  in 1.0 - (x2 / 2.0) + (x4 / 24.0) - (x6 / 720.0)

-- | Approximate sine using Taylor series.
sinApprox :: Number -> Number
sinApprox x = 
  let x2 = x * x
      x3 = x2 * x
      x5 = x3 * x2
      x7 = x5 * x2
  in x - (x3 / 6.0) + (x5 / 120.0) - (x7 / 5040.0)

-- | Map over array.
map :: forall a b. (a -> b) -> Array a -> Array b
map f arr = mapHelper f arr []

mapHelper :: forall a b. (a -> b) -> Array a -> Array b -> Array b
mapHelper f arr acc =
  case index arr (length acc) of
    Nothing -> acc
    Just x -> mapHelper f arr (snoc acc (f x))
