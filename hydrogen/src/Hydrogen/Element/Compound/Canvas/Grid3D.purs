-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // element // compound // canvas // grid3d
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Grid3D — 3D grid system for motion graphics and VFX.
-- |
-- | ## Design Philosophy
-- |
-- | Professional 3D tools (After Effects, Cinema 4D, Nuke, Blender) require:
-- |
-- | 1. **World Origin (0,0,0)** — Center of 3D space
-- | 2. **World Planes** — XY (floor), XZ (front), YZ (side)
-- | 3. **Bounded Extent** — Grid doesn't extend to infinity
-- | 4. **Orthographic Views** — Top, Front, Side, Perspective
-- | 5. **Axis Coloring** — X=Red, Y=Green, Z=Blue (RGB convention)
-- |
-- | ## Bounded Parameters
-- |
-- | - **GridSpacing3D**: 1 to 10000 units (same as 2D)
-- | - **GridExtent**: 1 to 100000 units from origin
-- | - **Subdivisions**: 1 to 10 per major cell
-- |
-- | ## Coordinate System
-- |
-- | Uses right-handed coordinates:
-- | - **X**: Right (Red axis)
-- | - **Y**: Up (Green axis)
-- | - **Z**: Toward viewer / out of screen (Blue axis)
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Point (Point3D, origin3D)
-- | - Schema.Geometry.Plane (planeXY, planeXZ, planeYZ)
-- | - Schema.Geometry.Vector (Vec3)
-- | - Canvas.Grid (GridSpacing, Subdivisions)

module Hydrogen.Element.Compound.Canvas.Grid3D
  ( -- * 3D Grid Extent
    GridExtent
  , gridExtent
  , extentValue
  , minExtent
  , maxExtent
  , defaultExtent
  
  -- * World Planes
  , WorldPlane(..)
  , planeNormal
  , planeTangent
  , planeBitangent
  , planeAxisColor
  
  -- * 3D Grid Configuration
  , Grid3DConfig
  , defaultGrid3DConfig
  , withSpacing3D
  , withExtent
  , withActivePlane
  , withShowAllPlanes
  , withShowAxes
  
  -- * 3D Snap Points
  , SnapPoint3D
  , snapPoint3D
  , snap3DPosition
  , snap3DType
  , SnapPoint3DType(..)
  , nearestSnapPoint3D
  , snapToGrid3D
  
  -- * 3D Grid Lines
  , GridLine3D
  , gridLine3D
  , line3DStart
  , line3DEnd
  , line3DIsMajor
  , line3DAxis
  
  -- * Axis
  , Axis(..)
  , axisColor
  , axisVector
  
  -- * 3D Grid Generation
  , Grid3DGeometry
  , generate3DGrid
  , generateFloorGrid
  , generateWallGrid
  , generateAxes
  
  -- * Orthographic Views
  , OrthoView(..)
  , viewPlane
  , viewUp
  , viewRight
  
  -- * Camera Integration
  , gridVisibleInFrustum
  , projectGridToScreen
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
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
  , negate
  )

import Data.Array (concat, snoc, filter, length, index)
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Int (toNumber, floor) as Int

import Hydrogen.Element.Compound.Canvas.Grid 
  ( GridSpacing
  , gridSpacing
  , spacingValue
  , Subdivisions
  , subdivisions
  , subdivisionsValue
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // grid extent
-- ═════════════════════════════════════════════════════════════════════════════

-- | How far the 3D grid extends from the origin.
-- |
-- | **Bounds:**
-- | - Minimum: 1 unit (at least something visible)
-- | - Maximum: 100000 units (bounded scene, not infinite)
-- |
-- | For reference:
-- | - 100 units: Small object scale (character, prop)
-- | - 1000 units: Room/building scale
-- | - 10000 units: City block scale
-- | - 100000 units: Landscape/terrain scale
newtype GridExtent = GridExtent Number

derive instance eqGridExtent :: Eq GridExtent
derive instance ordGridExtent :: Ord GridExtent

instance showGridExtent :: Show GridExtent where
  show (GridExtent e) = show e <> " units"

-- | Minimum grid extent.
minExtent :: Number
minExtent = 1.0

-- | Maximum grid extent.
maxExtent :: Number
maxExtent = 100000.0

-- | Create bounded grid extent.
gridExtent :: Number -> GridExtent
gridExtent n = GridExtent $ max minExtent (min maxExtent n)

-- | Extract extent value.
extentValue :: GridExtent -> Number
extentValue (GridExtent e) = e

-- | Default extent (1000 units — room scale).
defaultExtent :: GridExtent
defaultExtent = GridExtent 1000.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // world planes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard world planes aligned to axes.
-- |
-- | These correspond to the three orthogonal planes through the origin.
data WorldPlane
  = PlaneXY    -- ^ Floor/ground plane (horizontal) — normal is +Z
  | PlaneXZ    -- ^ Front/back plane (vertical) — normal is +Y
  | PlaneYZ    -- ^ Side plane (vertical) — normal is +X

derive instance eqWorldPlane :: Eq WorldPlane
derive instance ordWorldPlane :: Ord WorldPlane

instance showWorldPlane :: Show WorldPlane where
  show PlaneXY = "XY (floor)"
  show PlaneXZ = "XZ (front)"
  show PlaneYZ = "YZ (side)"

-- | Get the normal vector for a world plane.
-- |
-- | Returns {x, y, z} unit vector perpendicular to the plane.
planeNormal :: WorldPlane -> { x :: Number, y :: Number, z :: Number }
planeNormal PlaneXY = { x: 0.0, y: 0.0, z: 1.0 }  -- +Z
planeNormal PlaneXZ = { x: 0.0, y: 1.0, z: 0.0 }  -- +Y
planeNormal PlaneYZ = { x: 1.0, y: 0.0, z: 0.0 }  -- +X

-- | Get the tangent (U) vector for a world plane.
-- |
-- | This is the "horizontal" direction within the plane.
planeTangent :: WorldPlane -> { x :: Number, y :: Number, z :: Number }
planeTangent PlaneXY = { x: 1.0, y: 0.0, z: 0.0 }  -- +X
planeTangent PlaneXZ = { x: 1.0, y: 0.0, z: 0.0 }  -- +X
planeTangent PlaneYZ = { x: 0.0, y: 0.0, z: 1.0 }  -- +Z

-- | Get the bitangent (V) vector for a world plane.
-- |
-- | This is the "vertical" direction within the plane.
planeBitangent :: WorldPlane -> { x :: Number, y :: Number, z :: Number }
planeBitangent PlaneXY = { x: 0.0, y: 1.0, z: 0.0 }  -- +Y
planeBitangent PlaneXZ = { x: 0.0, y: 0.0, z: 1.0 }  -- +Z  
planeBitangent PlaneYZ = { x: 0.0, y: 1.0, z: 0.0 }  -- +Y

-- | Get the axis color for a world plane's normal.
-- |
-- | Following the RGB convention: X=Red, Y=Green, Z=Blue
planeAxisColor :: WorldPlane -> { r :: Number, g :: Number, b :: Number }
planeAxisColor PlaneXY = { r: 0.2, g: 0.4, b: 1.0 }   -- Blue (Z normal)
planeAxisColor PlaneXZ = { r: 0.2, g: 0.9, b: 0.3 }   -- Green (Y normal)
planeAxisColor PlaneYZ = { r: 1.0, g: 0.3, b: 0.3 }   -- Red (X normal)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // axis
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D axis identifier.
data Axis
  = AxisX    -- ^ X axis (Red)
  | AxisY    -- ^ Y axis (Green)
  | AxisZ    -- ^ Z axis (Blue)

derive instance eqAxis :: Eq Axis
derive instance ordAxis :: Ord Axis

instance showAxis :: Show Axis where
  show AxisX = "X"
  show AxisY = "Y"
  show AxisZ = "Z"

-- | Get the color for an axis (RGB convention).
axisColor :: Axis -> { r :: Number, g :: Number, b :: Number }
axisColor AxisX = { r: 1.0, g: 0.2, b: 0.2 }   -- Red
axisColor AxisY = { r: 0.2, g: 0.9, b: 0.2 }   -- Green
axisColor AxisZ = { r: 0.2, g: 0.4, b: 1.0 }   -- Blue

-- | Get the unit vector for an axis.
axisVector :: Axis -> { x :: Number, y :: Number, z :: Number }
axisVector AxisX = { x: 1.0, y: 0.0, z: 0.0 }
axisVector AxisY = { x: 0.0, y: 1.0, z: 0.0 }
axisVector AxisZ = { x: 0.0, y: 0.0, z: 1.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // 3d grid config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for 3D grid display.
type Grid3DConfig =
  { enabled :: Boolean
  , spacing :: GridSpacing
  , subdivisions :: Subdivisions
  , extent :: GridExtent
  , activePlane :: WorldPlane        -- Which plane is currently active for editing
  , showXY :: Boolean                -- Show floor grid
  , showXZ :: Boolean                -- Show front grid
  , showYZ :: Boolean                -- Show side grid
  , showAxes :: Boolean              -- Show axis lines through origin
  , axisLength :: GridExtent         -- How far axes extend
  , fadeWithDistance :: Boolean      -- Fade grid lines based on camera distance
  , adaptToZoom :: Boolean           -- Adjust grid density based on camera distance
  }

-- | Default 3D grid configuration.
-- |
-- | Shows floor grid (XY) with axes, room-scale extent.
defaultGrid3DConfig :: Grid3DConfig
defaultGrid3DConfig =
  { enabled: true
  , spacing: gridSpacing 10.0
  , subdivisions: subdivisions 4
  , extent: defaultExtent
  , activePlane: PlaneXY
  , showXY: true
  , showXZ: false
  , showYZ: false
  , showAxes: true
  , axisLength: defaultExtent
  , fadeWithDistance: true
  , adaptToZoom: true
  }

-- | Set grid spacing.
withSpacing3D :: Number -> Grid3DConfig -> Grid3DConfig
withSpacing3D s config = config { spacing = gridSpacing s }

-- | Set grid extent.
withExtent :: Number -> Grid3DConfig -> Grid3DConfig
withExtent e config = config { extent = gridExtent e }

-- | Set active editing plane.
withActivePlane :: WorldPlane -> Grid3DConfig -> Grid3DConfig
withActivePlane plane config = config { activePlane = plane }

-- | Show all three planes.
withShowAllPlanes :: Boolean -> Grid3DConfig -> Grid3DConfig
withShowAllPlanes showAll config = config
  { showXY = showAll
  , showXZ = showAll
  , showYZ = showAll
  }

-- | Toggle axis display.
withShowAxes :: Boolean -> Grid3DConfig -> Grid3DConfig
withShowAxes showAxes config = config { showAxes = showAxes }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // 3d snap points
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of 3D snap point.
data SnapPoint3DType
  = Snap3DOrigin             -- ^ World origin (0,0,0)
  | Snap3DAxisPoint          -- ^ Point on an axis
  | Snap3DMajorIntersection  -- ^ Major grid line intersection
  | Snap3DMinorIntersection  -- ^ Minor grid line intersection
  | Snap3DPlaneCenter        -- ^ Center of a grid plane

derive instance eqSnapPoint3DType :: Eq SnapPoint3DType
derive instance ordSnapPoint3DType :: Ord SnapPoint3DType

instance showSnapPoint3DType :: Show SnapPoint3DType where
  show Snap3DOrigin = "origin"
  show Snap3DAxisPoint = "axis"
  show Snap3DMajorIntersection = "major"
  show Snap3DMinorIntersection = "minor"
  show Snap3DPlaneCenter = "plane-center"

-- | A 3D snap point.
newtype SnapPoint3D = SnapPoint3D
  { x :: Number
  , y :: Number
  , z :: Number
  , pointType :: SnapPoint3DType
  , plane :: Maybe WorldPlane  -- Which plane this point is on (if any)
  }

derive instance eqSnapPoint3D :: Eq SnapPoint3D

instance showSnapPoint3D :: Show SnapPoint3D where
  show (SnapPoint3D sp) = 
    "Snap3D(" <> show sp.x <> "," <> show sp.y <> "," <> show sp.z <> ")"

-- | Create a 3D snap point.
snapPoint3D :: Number -> Number -> Number -> SnapPoint3DType -> Maybe WorldPlane -> SnapPoint3D
snapPoint3D x y z pointType plane = SnapPoint3D { x, y, z, pointType, plane }

-- | Get snap point position.
snap3DPosition :: SnapPoint3D -> { x :: Number, y :: Number, z :: Number }
snap3DPosition (SnapPoint3D sp) = { x: sp.x, y: sp.y, z: sp.z }

-- | Get snap point type.
snap3DType :: SnapPoint3D -> SnapPoint3DType
snap3DType (SnapPoint3D sp) = sp.pointType

-- | Find nearest 3D snap point.
nearestSnapPoint3D :: Number 
                   -> { x :: Number, y :: Number, z :: Number } 
                   -> Array SnapPoint3D 
                   -> Maybe SnapPoint3D
nearestSnapPoint3D threshold pos points =
  case points of
    [] -> Nothing
    _ ->
      let 
        withDist = map3D (\sp -> { point: sp, dist: distance3D pos sp }) points
        sorted = sortByDistance3D withDist
      in case head3D sorted of
        Nothing -> Nothing
        Just closest ->
          if closest.dist <= threshold
            then Just closest.point
            else Nothing

-- | Snap a 3D position to the grid on a specific plane.
snapToGrid3D :: GridSpacing 
             -> Subdivisions 
             -> WorldPlane
             -> { x :: Number, y :: Number, z :: Number } 
             -> { x :: Number, y :: Number, z :: Number }
snapToGrid3D gridSpace subs plane pos =
  let 
    spacing = spacingValue gridSpace
    subsCount = subdivisionsValue subs
    step = spacing / Int.toNumber subsCount
    snapValue v = Int.toNumber (Int.floor ((v / step) + 0.5)) * step
  in case plane of
    PlaneXY -> { x: snapValue pos.x, y: snapValue pos.y, z: pos.z }
    PlaneXZ -> { x: snapValue pos.x, y: pos.y, z: snapValue pos.z }
    PlaneYZ -> { x: pos.x, y: snapValue pos.y, z: snapValue pos.z }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // 3d grid lines
-- ═════════════════════════════════════════════════════════════════════════════

-- | A line in 3D space.
newtype GridLine3D = GridLine3D
  { x1 :: Number, y1 :: Number, z1 :: Number
  , x2 :: Number, y2 :: Number, z2 :: Number
  , isMajor :: Boolean
  , axis :: Maybe Axis  -- Which axis this line is parallel to
  }

derive instance eqGridLine3D :: Eq GridLine3D

instance showGridLine3D :: Show GridLine3D where
  show (GridLine3D l) =
    "Line3D(" <> show l.x1 <> "," <> show l.y1 <> "," <> show l.z1 <> "->" <>
    show l.x2 <> "," <> show l.y2 <> "," <> show l.z2 <> ")"

-- | Create a 3D grid line.
gridLine3D :: Number -> Number -> Number 
           -> Number -> Number -> Number 
           -> Boolean -> Maybe Axis -> GridLine3D
gridLine3D x1 y1 z1 x2 y2 z2 isMajor axis = 
  GridLine3D { x1, y1, z1, x2, y2, z2, isMajor, axis }

-- | Get line start point.
line3DStart :: GridLine3D -> { x :: Number, y :: Number, z :: Number }
line3DStart (GridLine3D l) = { x: l.x1, y: l.y1, z: l.z1 }

-- | Get line end point.
line3DEnd :: GridLine3D -> { x :: Number, y :: Number, z :: Number }
line3DEnd (GridLine3D l) = { x: l.x2, y: l.y2, z: l.z2 }

-- | Check if line is major.
line3DIsMajor :: GridLine3D -> Boolean
line3DIsMajor (GridLine3D l) = l.isMajor

-- | Get axis this line is parallel to.
line3DAxis :: GridLine3D -> Maybe Axis
line3DAxis (GridLine3D l) = l.axis

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // 3d grid geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete 3D grid geometry.
newtype Grid3DGeometry = Grid3DGeometry
  { lines :: Array GridLine3D
  , snapPoints :: Array SnapPoint3D
  , axisLines :: Array GridLine3D  -- The X, Y, Z axis lines (always colored)
  }

instance showGrid3DGeometry :: Show Grid3DGeometry where
  show (Grid3DGeometry g) =
    "Grid3D(" <> show (length3D g.lines) <> " lines, " <>
    show (length3D g.snapPoints) <> " snaps)"

-- | Generate complete 3D grid.
generate3DGrid :: Grid3DConfig -> Grid3DGeometry
generate3DGrid config =
  let
    spacing' = spacingValue config.spacing
    extent' = extentValue config.extent
    
    -- Generate grid lines for each visible plane
    xyLines = if config.showXY 
              then generatePlaneGrid PlaneXY spacing' extent' 
              else []
    xzLines = if config.showXZ 
              then generatePlaneGrid PlaneXZ spacing' extent' 
              else []
    yzLines = if config.showYZ 
              then generatePlaneGrid PlaneYZ spacing' extent' 
              else []
    
    -- Generate axis lines
    axes = if config.showAxes 
           then generateAxes (extentValue config.axisLength)
           else []
    
    -- Origin snap point (always present)
    originSnap = snapPoint3D 0.0 0.0 0.0 Snap3DOrigin Nothing
    
  in Grid3DGeometry
    { lines: concat [xyLines, xzLines, yzLines]
    , snapPoints: [originSnap]  -- TODO: Add grid intersections
    , axisLines: axes
    }

-- | Generate floor (XY plane) grid centered at origin.
generateFloorGrid :: Number -> Number -> Array GridLine3D
generateFloorGrid = generatePlaneGrid PlaneXY

-- | Generate wall (XZ or YZ plane) grid.
generateWallGrid :: WorldPlane -> Number -> Number -> Array GridLine3D
generateWallGrid plane spacing extent' =
  if plane == PlaneXY 
    then []  -- XY is floor, not wall
    else generatePlaneGrid plane spacing extent'

-- | Generate the three axis lines through origin.
-- |
-- | Each axis extends from -length to +length through origin.
generateAxes :: Number -> Array GridLine3D
generateAxes length' =
  [ -- X axis (Red)
    gridLine3D (negate length') 0.0 0.0 length' 0.0 0.0 true (Just AxisX)
  , -- Y axis (Green)
    gridLine3D 0.0 (negate length') 0.0 0.0 length' 0.0 true (Just AxisY)
  , -- Z axis (Blue)
    gridLine3D 0.0 0.0 (negate length') 0.0 0.0 length' true (Just AxisZ)
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // orthographic views
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard orthographic views.
data OrthoView
  = ViewTop      -- ^ Looking down -Z axis (sees XY plane)
  | ViewBottom   -- ^ Looking up +Z axis
  | ViewFront    -- ^ Looking down -Y axis (sees XZ plane)
  | ViewBack     -- ^ Looking down +Y axis
  | ViewLeft     -- ^ Looking down +X axis (sees YZ plane)
  | ViewRight    -- ^ Looking down -X axis

derive instance eqOrthoView :: Eq OrthoView
derive instance ordOrthoView :: Ord OrthoView

instance showOrthoView :: Show OrthoView where
  show ViewTop = "top"
  show ViewBottom = "bottom"
  show ViewFront = "front"
  show ViewBack = "back"
  show ViewLeft = "left"
  show ViewRight = "right"

-- | Get the world plane visible in an orthographic view.
viewPlane :: OrthoView -> WorldPlane
viewPlane ViewTop = PlaneXY
viewPlane ViewBottom = PlaneXY
viewPlane ViewFront = PlaneXZ
viewPlane ViewBack = PlaneXZ
viewPlane ViewLeft = PlaneYZ
viewPlane ViewRight = PlaneYZ

-- | Get the "up" vector for an orthographic view.
viewUp :: OrthoView -> { x :: Number, y :: Number, z :: Number }
viewUp ViewTop = { x: 0.0, y: 1.0, z: 0.0 }     -- Y up
viewUp ViewBottom = { x: 0.0, y: 1.0, z: 0.0 }  -- Y up
viewUp ViewFront = { x: 0.0, y: 0.0, z: 1.0 }   -- Z up
viewUp ViewBack = { x: 0.0, y: 0.0, z: 1.0 }    -- Z up
viewUp ViewLeft = { x: 0.0, y: 0.0, z: 1.0 }    -- Z up
viewUp ViewRight = { x: 0.0, y: 0.0, z: 1.0 }   -- Z up

-- | Get the "right" vector for an orthographic view.
viewRight :: OrthoView -> { x :: Number, y :: Number, z :: Number }
viewRight ViewTop = { x: 1.0, y: 0.0, z: 0.0 }     -- X right
viewRight ViewBottom = { x: 1.0, y: 0.0, z: 0.0 }  -- X right (flipped Y)
viewRight ViewFront = { x: 1.0, y: 0.0, z: 0.0 }   -- X right
viewRight ViewBack = { x: negate 1.0, y: 0.0, z: 0.0 }  -- -X right
viewRight ViewLeft = { x: 0.0, y: 0.0, z: 1.0 }    -- Z right
viewRight ViewRight = { x: 0.0, y: 0.0, z: negate 1.0 } -- -Z right

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // camera integration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if grid is visible in camera frustum.
-- |
-- | Simple check: is the grid extent within the camera's view?
-- | Full frustum culling would require the Frustum schema type.
gridVisibleInFrustum :: Grid3DConfig 
                     -> { cameraPos :: { x :: Number, y :: Number, z :: Number }
                        , farPlane :: Number 
                        }
                     -> Boolean
gridVisibleInFrustum config camera =
  let 
    extent' = extentValue config.extent
    -- Simple distance check: is camera within 2x grid extent?
    dist = sqrt3D (camera.cameraPos.x * camera.cameraPos.x +
                   camera.cameraPos.y * camera.cameraPos.y +
                   camera.cameraPos.z * camera.cameraPos.z)
  in dist < extent' * 2.0 && camera.farPlane > 1.0

-- | Project 3D grid lines to 2D screen space.
-- |
-- | This is a simplified projection — full projection requires
-- | the camera's view/projection matrices.
projectGridToScreen :: Grid3DGeometry 
                    -> { width :: Number, height :: Number }
                    -> Array { x1 :: Number, y1 :: Number, x2 :: Number, y2 :: Number }
projectGridToScreen (Grid3DGeometry geo) viewport =
  map3D (projectLine viewport) geo.lines

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate grid lines for a world plane.
generatePlaneGrid :: WorldPlane -> Number -> Number -> Array GridLine3D
generatePlaneGrid plane spacing extent' =
  let
    -- Number of lines in each direction
    count = Int.floor (extent' / spacing)
    
    tangent = planeTangent plane
    bitangent = planeBitangent plane
  in concat 
    [ generateParallelLines plane spacing extent' tangent bitangent count
    , generateParallelLines plane spacing extent' bitangent tangent count
    ]

-- | Generate parallel lines along one direction.
generateParallelLines :: WorldPlane 
                      -> Number 
                      -> Number 
                      -> { x :: Number, y :: Number, z :: Number }  -- Direction of lines
                      -> { x :: Number, y :: Number, z :: Number }  -- Perpendicular direction
                      -> Int 
                      -> Array GridLine3D
generateParallelLines plane spacing extent' lineDir perpDir count =
  generateLinesHelper plane spacing extent' lineDir perpDir (negate count) count []

generateLinesHelper :: WorldPlane 
                    -> Number 
                    -> Number 
                    -> { x :: Number, y :: Number, z :: Number }
                    -> { x :: Number, y :: Number, z :: Number }
                    -> Int 
                    -> Int 
                    -> Array GridLine3D 
                    -> Array GridLine3D
generateLinesHelper plane spacing extent' lineDir perpDir current maxCount acc =
  if current > maxCount then acc
  else
    let
      offset = Int.toNumber current * spacing
      -- Start and end points
      startX = lineDir.x * (negate extent') + perpDir.x * offset
      startY = lineDir.y * (negate extent') + perpDir.y * offset
      startZ = lineDir.z * (negate extent') + perpDir.z * offset
      endX = lineDir.x * extent' + perpDir.x * offset
      endY = lineDir.y * extent' + perpDir.y * offset
      endZ = lineDir.z * extent' + perpDir.z * offset
      
      isMajor = current == 0 || mod' current 5 == 0  -- Every 5th line is major
      
      line = gridLine3D startX startY startZ endX endY endZ isMajor Nothing
      newAcc = snoc acc line
    in generateLinesHelper plane spacing extent' lineDir perpDir (current + 1) maxCount newAcc

-- | Integer modulo.
mod' :: Int -> Int -> Int
mod' a b = a - (Int.floor (Int.toNumber a / Int.toNumber b) * b)

-- | Distance from position to 3D snap point.
distance3D :: { x :: Number, y :: Number, z :: Number } -> SnapPoint3D -> Number
distance3D pos (SnapPoint3D sp) =
  let
    dx = pos.x - sp.x
    dy = pos.y - sp.y
    dz = pos.z - sp.z
  in sqrt3D (dx * dx + dy * dy + dz * dz)

-- | 3D square root approximation.
sqrt3D :: Number -> Number
sqrt3D n =
  if n <= 0.0 then 0.0
  else newton3D n (n / 2.0) 0

newton3D :: Number -> Number -> Int -> Number
newton3D n guess iterations =
  if iterations >= 10 then guess
  else
    let nextGuess = (guess + n / guess) / 2.0
    in if abs3D (nextGuess - guess) < 0.0001
       then nextGuess
       else newton3D n nextGuess (iterations + 1)

abs3D :: Number -> Number
abs3D n = if n < 0.0 then negate n else n

-- | Sort by distance.
sortByDistance3D :: Array { point :: SnapPoint3D, dist :: Number } 
                 -> Array { point :: SnapPoint3D, dist :: Number }
sortByDistance3D arr = foldl insertSorted3D [] arr

insertSorted3D :: Array { point :: SnapPoint3D, dist :: Number }
               -> { point :: SnapPoint3D, dist :: Number }
               -> Array { point :: SnapPoint3D, dist :: Number }
insertSorted3D sorted item =
  let
    smaller = filter (\x -> x.dist < item.dist) sorted
    larger = filter (\x -> x.dist >= item.dist) sorted
  in concat [smaller, [item], larger]

-- | Map for 3D arrays.
map3D :: forall a b. (a -> b) -> Array a -> Array b
map3D f arr = map3DHelper f arr 0 []

map3DHelper :: forall a b. (a -> b) -> Array a -> Int -> Array b -> Array b
map3DHelper f arr idx acc =
  case index3D arr idx of
    Nothing -> acc
    Just x -> map3DHelper f arr (idx + 1) (snoc acc (f x))

-- | Head of array.
head3D :: forall a. Array a -> Maybe a
head3D arr = index arr 0

-- | Index into array.
index3D :: forall a. Array a -> Int -> Maybe a
index3D arr idx = index arr idx

-- | Array length.
length3D :: forall a. Array a -> Int
length3D arr = length arr

-- | Project a 3D line to 2D (simple orthographic for now).
projectLine :: { width :: Number, height :: Number } 
            -> GridLine3D 
            -> { x1 :: Number, y1 :: Number, x2 :: Number, y2 :: Number }
projectLine viewport (GridLine3D l) =
  let
    -- Simple orthographic: X maps to screen X, Y maps to screen Y
    cx = viewport.width / 2.0
    cy = viewport.height / 2.0
  in { x1: l.x1 + cx
     , y1: cy - l.y1  -- Flip Y for screen coordinates
     , x2: l.x2 + cx
     , y2: cy - l.y2
     }
