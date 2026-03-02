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
  , otherwise
  , (<>)
  , (==)
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

import Data.Array (filter, concat, length, snoc, index, head)
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
-- |
-- | Creates a grid with horizontal lines and two sets of diagonal lines
-- | at ±angle degrees, commonly used for 2.5D/isometric illustration.
-- |
-- | **Isometric snap points:**
-- | At each horizontal line, we calculate where the diagonals intersect
-- | to provide snap points for isometric positioning.
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
    
    -- Calculate isometric intersection snap points
    -- At each horizontal line y, intersections occur at regular x intervals
    -- determined by the angle: x_spacing = spacing / tan(angleRad)
    tanAngle = sinApprox angleRad / cosApprox angleRad
    xSpacing = if tanAngle > 0.001 then spacing / tanAngle else spacing
    
    -- Generate snap points at intersections
    points = generateIsometricSnapPoints bounds spacing xSpacing
    
  in GridGeometry 
    { lines: concat [horizontalLines, diagonalUp, diagonalDown]
    , snapPoints: points
    }

-- | Generate isometric grid snap points at line intersections.
generateIsometricSnapPoints :: { x :: Number, y :: Number, width :: Number, height :: Number } 
                            -> Number -> Number -> Array SnapPoint
generateIsometricSnapPoints bounds ySpacing xSpacing =
  let
    rowCount = Int.floor (bounds.height / ySpacing) + 1
    colCount = Int.floor (bounds.width / xSpacing) + 1
    rowIndices = generateIntRange 0 rowCount
    colIndices = generateIntRange 0 colCount
    
    generatePoint rowIdx colIdx =
      let
        y = bounds.y + Int.toNumber rowIdx * ySpacing
        x = bounds.x + Int.toNumber colIdx * xSpacing
        -- Offset odd rows for isometric alignment
        xOffset = if mod rowIdx 2 == 1 then xSpacing / 2.0 else 0.0
        finalX = x + xOffset
      in
        if finalX <= bounds.x + bounds.width
          then Just (snapPoint finalX y SnapMinorIntersection)
          else Nothing
    
    generateRow rowIdx = mapMaybe (generatePoint rowIdx) colIndices
  in
    concat (map generateRow rowIndices)

-- | Generate a polar/radial grid.
-- |
-- | Creates a radial grid with lines emanating from center and concentric rings.
-- | Snap points are generated at the center and at all radial/ring intersections.
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
    angleStepRad = angleStep * 3.14159265359 / 180.0
    
    -- Generate radial lines from center
    radialLines = generateRadialLines center div maxRadius
    
    -- Generate concentric rings
    rings = generateConcentricRings center ringSpacing maxRadius
    
    -- Center is always a snap point
    centerPoint = snapPoint center.x center.y SnapPolarCenter
    
    -- Generate snap points at radial/ring intersections
    ringCount = Int.floor (maxRadius / ringSpacing)
    radialIndices = generateIntRange 0 (div - 1)
    ringIndices = generateIntRange 1 ringCount
    
    -- Generate intersection point at given radial and ring
    generateIntersection radialIdx ringIdx =
      let
        angle = Int.toNumber radialIdx * angleStepRad
        radius = Int.toNumber ringIdx * ringSpacing
        x = center.x + radius * cosApprox angle
        y = center.y + radius * sinApprox angle
        -- Major intersections at cardinal directions (0°, 90°, 180°, 270°)
        isMajor = mod radialIdx (div / 4) == 0 && div >= 4
        snapType = if isMajor then SnapMajorIntersection else SnapMinorIntersection
      in
        snapPoint x y snapType
    
    -- Generate all intersection points
    generateRadialIntersections radialIdx = map (generateIntersection radialIdx) ringIndices
    intersectionPoints = concat (map generateRadialIntersections radialIndices)
    
  in GridGeometry
    { lines: concat [radialLines, rings]
    , snapPoints: snoc intersectionPoints centerPoint
    }

-- | Generate a hexagonal grid.
-- |
-- | Creates a grid of hexagons using "pointy-top" orientation (flat sides on left/right).
-- |
-- | **Hex dimensions from size (circumradius):**
-- | - Width (point to point): size × 2
-- | - Height (flat to flat): size × √3 ≈ size × 1.732
-- |
-- | The snap points include hex centers (major) and vertices (minor).
-- | The lines are the hex edges.
generateHexGrid :: GridSpacing 
                -> { x :: Number, y :: Number, width :: Number, height :: Number }
                -> GridGeometry
generateHexGrid (GridSpacing size) bounds =
  let 
    -- Hex dimensions (used for documentation/validation)
    hexWidth = size * 2.0
    hexHeight = size * 1.732050808  -- sqrt(3)
    
    -- Validate hex fits in bounds (at least one hex should be visible)
    boundsValid = bounds.width >= hexWidth && bounds.height >= hexHeight
    
    -- Generate hex centers and vertices
    points = if boundsValid then generateHexPoints size bounds else []
    
    -- Generate hex edges
    lines = if boundsValid then generateHexLines size bounds else []
    
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
-- |
-- | A position is on a major line if it falls within a tolerance of an exact
-- | multiple of the major spacing. The tolerance is based on a fraction of
-- | the minor step to handle floating-point precision.
isMajorLine :: Number -> Number -> Number -> Boolean
isMajorLine pos majorSpacing minorStep =
  let 
    ratio = pos / majorSpacing
    rounded = Int.toNumber (Int.floor (ratio + 0.0001))
    -- Tolerance is 1% of minor step or 0.0001, whichever is larger
    tolerance = max 0.0001 (minorStep * 0.01)
  in abs (ratio - rounded) < tolerance / majorSpacing

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

-- | Generate diagonal lines at an angle.
-- |
-- | Creates parallel diagonal lines across the bounding rectangle.
-- | The angle is measured from horizontal (positive = counterclockwise).
-- |
-- | **Algorithm:**
-- | 1. Calculate the diagonal length needed to cover the entire bounds
-- | 2. Determine perpendicular offset direction based on angle
-- | 3. Generate lines at regular spacing perpendicular to the line direction
-- |
-- | **Parameters:**
-- | - `angleDeg`: Angle in degrees from horizontal (-90 to 90 is useful range)
-- | - `spacing`: Distance between parallel lines
-- | - `bounds`: Bounding rectangle to fill with lines
generateDiagonalLines :: Number -> Number -> { x :: Number, y :: Number, width :: Number, height :: Number } -> Array GridLine
generateDiagonalLines angleDeg spacing bounds =
  let
    -- Convert angle to radians
    angleRad = angleDeg * 3.14159265359 / 180.0
    
    -- Direction vector for the lines (unit vector)
    dirX = cosApprox angleRad
    dirY = sinApprox angleRad
    
    -- Perpendicular direction (for spacing offset)
    perpX = negate dirY
    perpY = dirX
    
    -- Calculate the diagonal of the bounding box (maximum line length needed)
    diagonal = sqrt (bounds.width * bounds.width + bounds.height * bounds.height)
    
    -- Center of the bounding box
    centerX = bounds.x + bounds.width / 2.0
    centerY = bounds.y + bounds.height / 2.0
    
    -- Calculate how many lines we need on each side of center
    halfCount = Int.floor (diagonal / spacing) + 1
    
    -- Generate lines from -halfCount to +halfCount
    lineIndices = generateIntRange (negate halfCount) halfCount
    
    -- Generate one line for each index
    generateOneLine idx = 
      let
        -- Offset from center along perpendicular direction
        offset = Int.toNumber idx * spacing
        
        -- Line center point
        lineCenterX = centerX + offset * perpX
        lineCenterY = centerY + offset * perpY
        
        -- Line endpoints (extend diagonal/2 in each direction)
        halfLen = diagonal / 2.0
        startX = lineCenterX - halfLen * dirX
        startY = lineCenterY - halfLen * dirY
        endX = lineCenterX + halfLen * dirX
        endY = lineCenterY + halfLen * dirY
        
        -- Clip to bounds - only include if line passes through bounds
        passesThrough = lineIntersectsBounds startX startY endX endY bounds
      in
        if passesThrough 
          then Just (gridLine startX startY endX endY false)
          else Nothing
    
  in filter (\_ -> true) (mapMaybe generateOneLine lineIndices)

-- | Check if a line segment intersects a bounding rectangle.
-- |
-- | Uses simple bounding box overlap check - if line's bounding box
-- | overlaps with bounds, the line is considered to intersect.
lineIntersectsBounds :: Number -> Number -> Number -> Number -> { x :: Number, y :: Number, width :: Number, height :: Number } -> Boolean
lineIntersectsBounds x1 y1 x2 y2 bounds =
  let
    lineMinX = min x1 x2
    lineMaxX = max x1 x2
    lineMinY = min y1 y2
    lineMaxY = max y1 y2
    boundsMaxX = bounds.x + bounds.width
    boundsMaxY = bounds.y + bounds.height
  in
    -- Check bounding box overlap
    lineMaxX >= bounds.x && lineMinX <= boundsMaxX &&
    lineMaxY >= bounds.y && lineMinY <= boundsMaxY

-- | Generate a range of integers [start..end].
generateIntRange :: Int -> Int -> Array Int
generateIntRange start end = generateIntRangeHelper start end []

generateIntRangeHelper :: Int -> Int -> Array Int -> Array Int
generateIntRangeHelper current end acc =
  if current > end then acc
  else generateIntRangeHelper (current + 1) end (snoc acc current)

-- | Map over array, keeping only Just values.
-- |
-- | Uses fold to accumulate results, filtering out Nothing values.
mapMaybe :: forall a b. (a -> Maybe b) -> Array a -> Array b
mapMaybe f arr = 
  foldl (\acc x -> case f x of
    Nothing -> acc
    Just y -> snoc acc y
  ) [] arr



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

-- | Generate concentric rings as line segment approximations.
-- |
-- | Since GridLine represents straight lines, we approximate each ring
-- | as a polygon with many sides (32 segments per ring gives good visual quality).
-- |
-- | **Parameters:**
-- | - `center`: Center point of all rings
-- | - `spacing`: Distance between consecutive rings
-- | - `maxRadius`: Outer radius limit
-- |
-- | **Returns:**
-- | Array of line segments approximating circular rings. Each ring is made
-- | of 32 line segments forming a closed polygon.
generateConcentricRings :: { x :: Number, y :: Number } -> Number -> Number -> Array GridLine
generateConcentricRings center spacing maxRadius =
  let
    -- Number of segments per ring (32 gives smooth appearance)
    segmentsPerRing = 32
    
    -- Calculate number of rings
    ringCount = Int.floor (maxRadius / spacing)
    
    -- Generate all rings
    ringIndices = generateIntRange 1 ringCount
    
    -- Generate one ring (array of line segments forming a circle)
    generateRing ringIndex =
      let
        radius = Int.toNumber ringIndex * spacing
        segmentIndices = generateIntRange 0 (segmentsPerRing - 1)
        
        -- Generate one segment of the ring
        generateSegment segIndex =
          let
            -- Angle for this segment start
            startAngle = 2.0 * 3.14159265359 * Int.toNumber segIndex / Int.toNumber segmentsPerRing
            -- Angle for segment end
            endAngle = 2.0 * 3.14159265359 * Int.toNumber (segIndex + 1) / Int.toNumber segmentsPerRing
            
            -- Calculate endpoints
            startX = center.x + radius * cosApprox startAngle
            startY = center.y + radius * sinApprox startAngle
            endX = center.x + radius * cosApprox endAngle
            endY = center.y + radius * sinApprox endAngle
            
            -- Major if it's a multiple of spacing that's also multiple of 4
            isMajor = ringIndex `mod` 4 == 0
          in
            gridLine startX startY endX endY isMajor
      in
        map generateSegment segmentIndices
    
  in concat (map generateRing ringIndices)

-- | Integer modulo operation.
mod :: Int -> Int -> Int
mod a b = a - (Int.floor (Int.toNumber a / Int.toNumber b)) * b

-- | Generate hex grid snap points.
-- |
-- | Creates snap points at the centers and vertices of a hexagonal grid.
-- | Uses "pointy-top" hexagon orientation (flat sides on left/right).
-- |
-- | **Hexagonal Grid Geometry:**
-- | - Horizontal spacing between hex centers: size * 1.5
-- | - Vertical spacing between rows: size * sqrt(3) ≈ size * 1.732
-- | - Odd rows are offset by size * 0.75 horizontally
-- |
-- | **Parameters:**
-- | - `size`: Distance from hex center to vertex (circumradius)
-- | - `bounds`: Bounding rectangle to fill with points
-- |
-- | **Returns:**
-- | Snap points at all hex centers (major) and vertices (minor).
generateHexPoints :: Number -> { x :: Number, y :: Number, width :: Number, height :: Number } -> Array SnapPoint
generateHexPoints size bounds =
  let
    -- Hexagonal grid spacing
    horizSpacing = size * 1.5
    vertSpacing = size * sqrt3
    
    -- sqrt(3) ≈ 1.732050808
    sqrt3 = 1.732050808
    
    -- Calculate grid extents
    colCount = Int.floor (bounds.width / horizSpacing) + 2
    rowCount = Int.floor (bounds.height / vertSpacing) + 2
    
    -- Generate all rows
    rowIndices = generateIntRange 0 rowCount
    colIndices = generateIntRange 0 colCount
    
    -- Generate points for one hex center
    generateHexCenterPoints rowIdx colIdx =
      let
        -- Odd rows are offset
        rowOffset = if mod rowIdx 2 == 1 then horizSpacing / 2.0 else 0.0
        
        -- Center position
        centerX = bounds.x + Int.toNumber colIdx * horizSpacing + rowOffset
        centerY = bounds.y + Int.toNumber rowIdx * vertSpacing
        
        -- Create center snap point (major)
        centerPoint = snapPoint centerX centerY SnapMajorIntersection
        
        -- Generate 6 vertex points (minor) at 60° intervals
        -- Only generate vertices that are "owned" by this hex to avoid duplicates
        -- We'll generate the top-right and right vertices only
        angle1 = 0.0  -- Right vertex
        angle2 = 60.0 * 3.14159265359 / 180.0  -- Top-right vertex
        
        v1x = centerX + size * cosApprox angle1
        v1y = centerY + size * sinApprox angle1
        v2x = centerX + size * cosApprox angle2
        v2y = centerY + size * sinApprox angle2
        
        vertexPoint1 = snapPoint v1x v1y SnapMinorIntersection
        vertexPoint2 = snapPoint v2x v2y SnapMinorIntersection
        
        -- Filter to points within bounds
        inBounds p = 
          let pos = snapPointPosition p
          in pos.x >= bounds.x && pos.x <= bounds.x + bounds.width &&
             pos.y >= bounds.y && pos.y <= bounds.y + bounds.height
      in
        filter inBounds [centerPoint, vertexPoint1, vertexPoint2]
    
    -- Generate points for all hexes in a row
    generateRow rowIdx = concat (map (generateHexCenterPoints rowIdx) colIndices)
    
  in concat (map generateRow rowIndices)

-- | Generate hex grid lines.
-- |
-- | Creates the edges of a hexagonal grid. Uses "pointy-top" orientation.
-- |
-- | **Hexagonal Grid Edges:**
-- | Each hex has 6 edges. To avoid duplicates, each hex "owns" only 3 edges:
-- | - Top-right edge (from top vertex to top-right vertex)
-- | - Right edge (from top-right vertex to bottom-right vertex)
-- | - Bottom-right edge (from bottom-right vertex to bottom vertex)
-- |
-- | The other 3 edges are owned by neighboring hexes.
-- |
-- | **Parameters:**
-- | - `size`: Distance from hex center to vertex (circumradius)
-- | - `bounds`: Bounding rectangle to fill with hex edges
-- |
-- | **Returns:**
-- | Array of line segments forming the hexagonal grid edges.
generateHexLines :: Number -> { x :: Number, y :: Number, width :: Number, height :: Number } -> Array GridLine
generateHexLines size bounds =
  let
    -- Hexagonal grid spacing
    horizSpacing = size * 1.5
    vertSpacing = size * sqrt3
    
    -- sqrt(3) ≈ 1.732050808
    sqrt3 = 1.732050808
    
    -- Calculate grid extents (add extra margin for edge hexes)
    colCount = Int.floor (bounds.width / horizSpacing) + 2
    rowCount = Int.floor (bounds.height / vertSpacing) + 2
    
    -- Generate all rows
    rowIndices = generateIntRange 0 rowCount
    colIndices = generateIntRange 0 colCount
    
    -- Hex vertex angles (0° is right, going counterclockwise)
    -- For pointy-top: vertices at 30°, 90°, 150°, 210°, 270°, 330°
    -- But for simplicity we use flat-top: 0°, 60°, 120°, 180°, 240°, 300°
    angleAt idx = Int.toNumber idx * 60.0 * 3.14159265359 / 180.0
    
    -- Generate the 3 "owned" edges for one hex
    generateHexEdges rowIdx colIdx =
      let
        -- Odd rows are offset
        rowOffset = if mod rowIdx 2 == 1 then horizSpacing / 2.0 else 0.0
        
        -- Center position
        centerX = bounds.x + Int.toNumber colIdx * horizSpacing + rowOffset
        centerY = bounds.y + Int.toNumber rowIdx * vertSpacing
        
        -- Calculate vertex positions
        vertex idx = 
          { x: centerX + size * cosApprox (angleAt idx)
          , y: centerY + size * sinApprox (angleAt idx)
          }
        
        -- 6 vertices: 0=right, 1=top-right, 2=top-left, 3=left, 4=bottom-left, 5=bottom-right
        v0 = vertex 0  -- Right
        v1 = vertex 1  -- Top-right
        v2 = vertex 2  -- Top-left
        v5 = vertex 5  -- Bottom-right
        
        -- Generate 3 owned edges
        edge1 = gridLine v1.x v1.y v2.x v2.y false  -- Top edge
        edge2 = gridLine v0.x v0.y v1.x v1.y false  -- Top-right edge
        edge3 = gridLine v5.x v5.y v0.x v0.y false  -- Bottom-right edge
        
        -- Check if edge is within bounds (at least one endpoint in bounds)
        edgeInBounds line =
          let
            startPos = lineStart line
            endPos = lineEnd line
          in
            pointInBounds startPos.x startPos.y bounds ||
            pointInBounds endPos.x endPos.y bounds
      in
        filter edgeInBounds [edge1, edge2, edge3]
    
    -- Generate edges for all hexes in a row
    generateRow rowIdx = concat (map (generateHexEdges rowIdx) colIndices)
    
  in concat (map generateRow rowIndices)

-- | Check if a point is within bounds.
pointInBounds :: Number -> Number -> { x :: Number, y :: Number, width :: Number, height :: Number } -> Boolean
pointInBounds px py bounds =
  px >= bounds.x && px <= bounds.x + bounds.width &&
  py >= bounds.y && py <= bounds.y + bounds.height

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
