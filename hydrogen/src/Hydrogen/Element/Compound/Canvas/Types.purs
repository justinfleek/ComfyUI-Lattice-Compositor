-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // compound // canvas // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Types — Core type definitions for infinite canvas component.
-- |
-- | ## Design Philosophy
-- |
-- | The Canvas is the foundational surface for all design tools. It provides:
-- |
-- | - **Infinite space**: Pan in any direction, zoom from 0.1% to 6400%
-- | - **Layer composition**: N-deep stacking with occlusion culling
-- | - **Material backgrounds**: Each component can have diffusion-ready noise
-- | - **Shape masking**: Clip paths, mattes, effects on every layer
-- | - **Hyper-interactivity**: Touch, gesture, haptic, mobile-first
-- |
-- | ## Architecture
-- |
-- | Canvas wraps Schema.Graph.Viewport for viewport math and adds:
-- |
-- | - Tool state (select, pan, zoom, marquee, etc.)
-- | - Selection management (single, multi, group)
-- | - Grid/guide rendering
-- | - Snap behavior
-- | - History (undo/redo stack)
-- |
-- | ## Coordinate Systems
-- |
-- | - **Screen space**: Pixels on device (0,0 = top-left of canvas element)
-- | - **Canvas space**: Infinite coordinate system (can be negative)
-- | - **Object space**: Local to each object (0,0 = object origin)
-- |
-- | Conversion: screen → canvas requires viewport transform.
-- |
-- | ## Dependencies
-- |
-- | - Schema.Graph.Viewport (ViewportState, ViewportZoom, etc.)
-- | - Schema.Geometry (Point2D, Rect, Transform2D)
-- | - Schema.Color (for grid, selection colors)
-- | - Schema.Dimension.Device (Pixel)

module Hydrogen.Element.Compound.Canvas.Types
  ( -- * Canvas ID
    CanvasId(..)
  , canvasId
  
  -- * Tool Types
  , CanvasTool(..)
  , isSelectionTool
  , isPanTool
  , isZoomTool
  , isDrawingTool
  
  -- * Selection Types
  , SelectionMode(..)
  , SelectionState
  , emptySelection
  , singleSelection
  , multiSelection
  , addToSelection
  , removeFromSelection
  , clearSelection
  , isSelected
  , selectionCount
  , selectionBounds
  
  -- * Object Types
  , CanvasObjectId(..)
  , CanvasObject
  , defaultCanvasObject
  , objectId
  , objectBounds
  , objectTransform
  , objectVisible
  , objectLocked
  , objectName
  , objectZIndex
  , objectBlendMode
  , objectOpacity
  , objectClipPath
  , objectMask
  , objectTrackMatteMode
  , objectMatteLayerId
  
  -- * Re-exports for compositing
  , module Blend
  , module Mask
  , module ClipPath
  -- Note: TrackMatteMode from Composition is used via qualified import
  -- to avoid BlendMode name collision with Blend module
  
  -- * Grid Types
  , GridStyle(..)
  , GridConfig
  , defaultGridConfig
  , gridEnabled
  , gridVisible
  , gridSnap
  , withGridSize
  , withGridStyle
  , withGridColor
  , withGridOpacity
  
  -- * Snap Types
  , SnapTarget(..)
  , SnapConfig
  , defaultSnapConfig
  , snapEnabled
  , snapDistance
  , snapToGrid
  , snapToObjects
  , snapToGuides
  
  -- * Guide Types
  , Guide(..)
  , GuideOrientation(..)
  , guideHorizontal
  , guideVertical
  , guidePosition
  , guideId
  
  -- * Canvas Config
  , CanvasConfig
  , defaultCanvasConfig
  , withMinZoom
  , withMaxZoom
  , withGridConfig
  , withSnapConfig
  , withBackgroundColor
  
  -- * Canvas Dimensions
  , CanvasBounds
  , infiniteBounds
  , finiteBounds
  , boundsContains
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
  , (/=)
  , (&&)
  , (>=)
  , (<=)
  , (>)
  , (<)
  , (+)
  , (-)
  , negate
  , max
  , min
  )

import Data.Array (length, filter, snoc, elem, index)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Foldable (foldl)

import Hydrogen.Schema.Graph.Viewport 
  ( ViewportZoom
  , viewportZoom
  )
import Hydrogen.Schema.Geometry.Transform (Transform2D, identityTransform)

-- Compositing imports
import Hydrogen.Schema.Color.Blend as Blend
import Hydrogen.Schema.Geometry.Mask as Mask
import Hydrogen.Schema.Geometry.ClipPath as ClipPath
import Hydrogen.Schema.Motion.Composition as Composition

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // canvas id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a canvas instance.
newtype CanvasId = CanvasId String

derive instance eqCanvasId :: Eq CanvasId
derive instance ordCanvasId :: Ord CanvasId

instance showCanvasId :: Show CanvasId where
  show (CanvasId id) = "CanvasId(" <> id <> ")"

-- | Create a canvas ID.
canvasId :: String -> CanvasId
canvasId = CanvasId

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // tool types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Available canvas tools.
-- |
-- | Tools determine how mouse/touch interactions are interpreted.
data CanvasTool
  = ToolSelect           -- ^ Select and transform objects
  | ToolDirectSelect     -- ^ Select individual points/vertices
  | ToolPan              -- ^ Pan the viewport (hand tool)
  | ToolZoom             -- ^ Zoom in/out
  | ToolMarquee          -- ^ Rectangular selection
  | ToolLasso            -- ^ Freeform selection
  | ToolPen              -- ^ Draw bezier paths
  | ToolPencil           -- ^ Freehand drawing
  | ToolRectangle        -- ^ Draw rectangles
  | ToolEllipse          -- ^ Draw ellipses
  | ToolLine             -- ^ Draw lines
  | ToolText             -- ^ Add/edit text
  | ToolEyedropper       -- ^ Sample colors
  | ToolMove             -- ^ Move objects (without selection handles)
  | ToolRotate           -- ^ Rotate objects
  | ToolScale            -- ^ Scale objects
  | ToolCustom String    -- ^ Custom tool with identifier

derive instance eqCanvasTool :: Eq CanvasTool
derive instance ordCanvasTool :: Ord CanvasTool

instance showCanvasTool :: Show CanvasTool where
  show ToolSelect = "select"
  show ToolDirectSelect = "direct-select"
  show ToolPan = "pan"
  show ToolZoom = "zoom"
  show ToolMarquee = "marquee"
  show ToolLasso = "lasso"
  show ToolPen = "pen"
  show ToolPencil = "pencil"
  show ToolRectangle = "rectangle"
  show ToolEllipse = "ellipse"
  show ToolLine = "line"
  show ToolText = "text"
  show ToolEyedropper = "eyedropper"
  show ToolMove = "move"
  show ToolRotate = "rotate"
  show ToolScale = "scale"
  show (ToolCustom name) = "custom:" <> name

-- | Is this a selection tool?
isSelectionTool :: CanvasTool -> Boolean
isSelectionTool ToolSelect = true
isSelectionTool ToolDirectSelect = true
isSelectionTool ToolMarquee = true
isSelectionTool ToolLasso = true
isSelectionTool _ = false

-- | Is this a pan tool?
isPanTool :: CanvasTool -> Boolean
isPanTool ToolPan = true
isPanTool _ = false

-- | Is this a zoom tool?
isZoomTool :: CanvasTool -> Boolean
isZoomTool ToolZoom = true
isZoomTool _ = false

-- | Is this a drawing tool?
isDrawingTool :: CanvasTool -> Boolean
isDrawingTool ToolPen = true
isDrawingTool ToolPencil = true
isDrawingTool ToolRectangle = true
isDrawingTool ToolEllipse = true
isDrawingTool ToolLine = true
isDrawingTool ToolText = true
isDrawingTool _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // selection types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Selection behavior mode.
data SelectionMode
  = SelectReplace      -- ^ New selection replaces existing
  | SelectAdd          -- ^ Add to existing selection (Shift)
  | SelectSubtract     -- ^ Remove from selection (Alt)
  | SelectToggle       -- ^ Toggle selection state (Ctrl)
  | SelectIntersect    -- ^ Keep only intersection

derive instance eqSelectionMode :: Eq SelectionMode

instance showSelectionMode :: Show SelectionMode where
  show SelectReplace = "replace"
  show SelectAdd = "add"
  show SelectSubtract = "subtract"
  show SelectToggle = "toggle"
  show SelectIntersect = "intersect"

-- | Current selection state.
-- |
-- | Tracks which objects are selected and selection metadata.
type SelectionState =
  { selectedIds :: Array CanvasObjectId
  , primaryId :: Maybe CanvasObjectId    -- The "main" selected object
  , anchorPoint :: Maybe { x :: Number, y :: Number }  -- Transform anchor
  }

-- | Empty selection.
emptySelection :: SelectionState
emptySelection =
  { selectedIds: []
  , primaryId: Nothing
  , anchorPoint: Nothing
  }

-- | Select a single object.
singleSelection :: CanvasObjectId -> SelectionState
singleSelection objId =
  { selectedIds: [objId]
  , primaryId: Just objId
  , anchorPoint: Nothing
  }

-- | Select multiple objects.
multiSelection :: Array CanvasObjectId -> SelectionState
multiSelection ids =
  { selectedIds: ids
  , primaryId: if length ids > 0 then headMaybe ids else Nothing
  , anchorPoint: Nothing
  }
  where
    headMaybe :: forall a. Array a -> Maybe a
    headMaybe arr = case length arr of
      0 -> Nothing
      _ -> arrayIndex arr 0

-- | Add an object to selection.
addToSelection :: CanvasObjectId -> SelectionState -> SelectionState
addToSelection objId state =
  if elem objId state.selectedIds
    then state
    else state { selectedIds = snoc state.selectedIds objId }

-- | Remove an object from selection.
removeFromSelection :: CanvasObjectId -> SelectionState -> SelectionState
removeFromSelection objId state =
  let newIds = filter (\id -> id /= objId) state.selectedIds
      newPrimary = if state.primaryId == Just objId 
                     then headMaybe newIds 
                     else state.primaryId
  in state 
       { selectedIds = newIds
       , primaryId = newPrimary
       }
  where
    headMaybe :: forall a. Array a -> Maybe a
    headMaybe arr = arrayIndex arr 0

-- | Clear all selection.
clearSelection :: SelectionState -> SelectionState
clearSelection _ = emptySelection

-- | Check if object is selected.
isSelected :: CanvasObjectId -> SelectionState -> Boolean
isSelected objId state = elem objId state.selectedIds

-- | Get number of selected objects.
selectionCount :: SelectionState -> Int
selectionCount state = length state.selectedIds

-- | Calculate bounding box of selection.
-- |
-- | Returns Nothing if selection is empty or objects can't be found.
selectionBounds :: SelectionState -> Array CanvasObject -> Maybe { x :: Number, y :: Number, width :: Number, height :: Number }
selectionBounds state objects =
  let 
    selectedObjects = filter (\obj -> elem (objectId obj) state.selectedIds) objects
  in
    if length selectedObjects == 0
      then Nothing
      else Just (calculateBounds selectedObjects)
  where
    calculateBounds :: Array CanvasObject -> { x :: Number, y :: Number, width :: Number, height :: Number }
    calculateBounds objs =
      let
        initial = { minX: infinity, minY: infinity, maxX: negInfinity, maxY: negInfinity }
        result = foldl accumulateBounds initial objs
      in
        { x: result.minX
        , y: result.minY
        , width: result.maxX - result.minX
        , height: result.maxY - result.minY
        }
    
    accumulateBounds acc obj =
      let bounds = objectBounds obj
      in
        { minX: min acc.minX bounds.x
        , minY: min acc.minY bounds.y
        , maxX: max acc.maxX (bounds.x + bounds.width)
        , maxY: max acc.maxY (bounds.y + bounds.height)
        }
    
    infinity :: Number
    infinity = 1.0e308
    
    negInfinity :: Number
    negInfinity = -1.0e308

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // object types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for canvas objects.
newtype CanvasObjectId = CanvasObjectId String

derive instance eqCanvasObjectId :: Eq CanvasObjectId
derive instance ordCanvasObjectId :: Ord CanvasObjectId

instance showCanvasObjectId :: Show CanvasObjectId where
  show (CanvasObjectId id) = "ObjectId(" <> id <> ")"

-- | A canvas object with bounds, transform, and compositing properties.
-- |
-- | This is the complete interface needed for canvas operations including
-- | layer stacking with 1+N layers, blend modes, masks, clips, and mattes.
-- |
-- | ## Compositing Order
-- |
-- | When rendering, compositing is applied in this order:
-- | 1. Apply object's clip path (binary visibility)
-- | 2. Apply object's mask (soft alpha)
-- | 3. If trackMatte is set, use the referenced matte layer for masking
-- | 4. Apply blend mode when compositing onto layers below
-- | 5. Apply object opacity as final alpha multiplier
-- |
-- | ## Layer Ordering
-- |
-- | Objects are rendered in ascending zIndex order (lower = behind).
-- | Multiple objects can share the same zIndex; tie-breaking uses array order.
type CanvasObject =
  { -- Identity
    id :: CanvasObjectId
  , name :: String
  
  -- Spatial
  , bounds :: { x :: Number, y :: Number, width :: Number, height :: Number }
  , transform :: Transform2D
  
  -- Visibility & Interaction
  , visible :: Boolean
  , locked :: Boolean
  
  -- Layer ordering
  , zIndex :: Int
  
  -- Compositing: Blend Mode
  , blendMode :: Blend.BlendMode            -- ^ How this layer blends with layers below
  , opacity :: Number                        -- ^ Object opacity (0.0-1.0)
  
  -- Compositing: Clipping
  , clipPath :: Maybe ClipPath.ClipPath      -- ^ Binary clip (inside/outside)
  
  -- Compositing: Masking
  , mask :: Maybe Mask.Mask                  -- ^ Soft alpha mask
  
  -- Compositing: Track Matte
  , trackMatteMode :: Composition.TrackMatteMode  -- ^ How to use matte layer
  , matteLayerId :: Maybe CanvasObjectId     -- ^ Reference to matte layer (if any)
  }

-- | Get object ID.
objectId :: CanvasObject -> CanvasObjectId
objectId obj = obj.id

-- | Get object bounds in canvas space.
objectBounds :: CanvasObject -> { x :: Number, y :: Number, width :: Number, height :: Number }
objectBounds obj = obj.bounds

-- | Get object transform.
objectTransform :: CanvasObject -> Transform2D
objectTransform obj = obj.transform

-- | Check if object is visible.
objectVisible :: CanvasObject -> Boolean
objectVisible obj = obj.visible

-- | Check if object is locked.
objectLocked :: CanvasObject -> Boolean
objectLocked obj = obj.locked

-- | Get object name.
objectName :: CanvasObject -> String
objectName obj = obj.name

-- | Get object z-index (layer order).
objectZIndex :: CanvasObject -> Int
objectZIndex obj = obj.zIndex

-- | Get object blend mode.
objectBlendMode :: CanvasObject -> Blend.BlendMode
objectBlendMode obj = obj.blendMode

-- | Get object opacity (0.0-1.0).
objectOpacity :: CanvasObject -> Number
objectOpacity obj = obj.opacity

-- | Get object clip path (if any).
objectClipPath :: CanvasObject -> Maybe ClipPath.ClipPath
objectClipPath obj = obj.clipPath

-- | Get object mask (if any).
objectMask :: CanvasObject -> Maybe Mask.Mask
objectMask obj = obj.mask

-- | Get object track matte mode.
objectTrackMatteMode :: CanvasObject -> Composition.TrackMatteMode
objectTrackMatteMode obj = obj.trackMatteMode

-- | Get reference to matte layer (if any).
objectMatteLayerId :: CanvasObject -> Maybe CanvasObjectId
objectMatteLayerId obj = obj.matteLayerId

-- | Create a default canvas object with no compositing effects.
-- |
-- | Uses Normal blend mode, full opacity, no clip/mask/matte.
defaultCanvasObject :: CanvasObjectId -> String -> CanvasObject
defaultCanvasObject objId name =
  { id: objId
  , name: name
  , bounds: { x: 0.0, y: 0.0, width: 100.0, height: 100.0 }
  , transform: identityTransform
  , visible: true
  , locked: false
  , zIndex: 0
  , blendMode: Blend.Normal
  , opacity: 1.0
  , clipPath: Nothing
  , mask: Nothing
  , trackMatteMode: Composition.TMNone
  , matteLayerId: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // grid types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual style for the canvas grid.
data GridStyle
  = GridDots          -- ^ Dots at intersections
  | GridLines         -- ^ Full grid lines
  | GridCrosshairs    -- ^ Small crosses at intersections
  | GridIsometric     -- ^ 30° isometric grid
  | GridPerspective   -- ^ Perspective grid with vanishing point

derive instance eqGridStyle :: Eq GridStyle

instance showGridStyle :: Show GridStyle where
  show GridDots = "dots"
  show GridLines = "lines"
  show GridCrosshairs = "crosshairs"
  show GridIsometric = "isometric"
  show GridPerspective = "perspective"

-- | Grid configuration.
type GridConfig =
  { enabled :: Boolean
  , visible :: Boolean
  , snap :: Boolean
  , size :: Number              -- Grid cell size in canvas units
  , subdivisions :: Int         -- Subdivisions per cell
  , style :: GridStyle
  , majorColor :: String        -- Color for major grid lines (hex)
  , minorColor :: String        -- Color for minor grid lines (hex)
  , majorOpacity :: Number      -- 0.0 - 1.0
  , minorOpacity :: Number      -- 0.0 - 1.0
  , majorWidth :: Number        -- Stroke width for major lines
  , minorWidth :: Number        -- Stroke width for minor lines
  }

-- | Default grid configuration.
defaultGridConfig :: GridConfig
defaultGridConfig =
  { enabled: true
  , visible: true
  , snap: true
  , size: 10.0
  , subdivisions: 4
  , style: GridLines
  , majorColor: "#3b82f6"       -- Blue-500
  , minorColor: "#94a3b8"       -- Slate-400
  , majorOpacity: 0.3
  , minorOpacity: 0.1
  , majorWidth: 1.0
  , minorWidth: 0.5
  }

-- | Check if grid is enabled.
gridEnabled :: GridConfig -> Boolean
gridEnabled config = config.enabled

-- | Check if grid is visible.
gridVisible :: GridConfig -> Boolean
gridVisible config = config.enabled && config.visible

-- | Check if snap to grid is active.
gridSnap :: GridConfig -> Boolean
gridSnap config = config.enabled && config.snap

-- | Set grid size.
withGridSize :: Number -> GridConfig -> GridConfig
withGridSize size config = config { size = size }

-- | Set grid style.
withGridStyle :: GridStyle -> GridConfig -> GridConfig
withGridStyle style config = config { style = style }

-- | Set grid color.
withGridColor :: String -> GridConfig -> GridConfig
withGridColor color config = config { majorColor = color }

-- | Set grid opacity.
withGridOpacity :: Number -> GridConfig -> GridConfig
withGridOpacity opacity config = config { majorOpacity = clamp01 opacity }
  where
    clamp01 n = max 0.0 (min 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // snap types
-- ═════════════════════════════════════════════════════════════════════════════

-- | What objects/features to snap to.
data SnapTarget
  = SnapGrid            -- ^ Snap to grid intersections
  | SnapObjects         -- ^ Snap to object bounds/centers
  | SnapGuides          -- ^ Snap to guides
  | SnapPixels          -- ^ Snap to whole pixels
  | SnapKeyObjects      -- ^ Snap to "key" objects (selection centers, etc.)

derive instance eqSnapTarget :: Eq SnapTarget

instance showSnapTarget :: Show SnapTarget where
  show SnapGrid = "grid"
  show SnapObjects = "objects"
  show SnapGuides = "guides"
  show SnapPixels = "pixels"
  show SnapKeyObjects = "key-objects"

-- | Snap configuration.
type SnapConfig =
  { enabled :: Boolean
  , distance :: Number          -- Snap threshold in screen pixels
  , targets :: Array SnapTarget -- What to snap to
  , showIndicators :: Boolean   -- Show snap lines/points
  , indicatorColor :: String    -- Color for snap indicators
  }

-- | Default snap configuration.
defaultSnapConfig :: SnapConfig
defaultSnapConfig =
  { enabled: true
  , distance: 8.0
  , targets: [SnapGrid, SnapObjects, SnapGuides]
  , showIndicators: true
  , indicatorColor: "#f97316"   -- Orange-500
  }

-- | Check if snap is enabled.
snapEnabled :: SnapConfig -> Boolean
snapEnabled config = config.enabled

-- | Get snap distance.
snapDistance :: SnapConfig -> Number
snapDistance config = config.distance

-- | Check if snapping to grid.
snapToGrid :: SnapConfig -> Boolean
snapToGrid config = config.enabled && elem SnapGrid config.targets

-- | Check if snapping to objects.
snapToObjects :: SnapConfig -> Boolean
snapToObjects config = config.enabled && elem SnapObjects config.targets

-- | Check if snapping to guides.
snapToGuides :: SnapConfig -> Boolean
snapToGuides config = config.enabled && elem SnapGuides config.targets

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // guide types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Guide orientation.
data GuideOrientation
  = GuideHorizontal
  | GuideVertical

derive instance eqGuideOrientation :: Eq GuideOrientation

instance showGuideOrientation :: Show GuideOrientation where
  show GuideHorizontal = "horizontal"
  show GuideVertical = "vertical"

-- | A ruler guide.
data Guide = Guide
  { id :: String
  , orientation :: GuideOrientation
  , position :: Number          -- Position in canvas coordinates
  , color :: String             -- Guide color (hex)
  , locked :: Boolean
  }

derive instance eqGuide :: Eq Guide

instance showGuide :: Show Guide where
  show (Guide g) = "Guide(" <> g.id <> " " <> show g.orientation <> " @" <> show g.position <> ")"

-- | Create horizontal guide.
guideHorizontal :: String -> Number -> Guide
guideHorizontal id pos = Guide
  { id
  , orientation: GuideHorizontal
  , position: pos
  , color: "#06b6d4"            -- Cyan-500
  , locked: false
  }

-- | Create vertical guide.
guideVertical :: String -> Number -> Guide
guideVertical id pos = Guide
  { id
  , orientation: GuideVertical
  , position: pos
  , color: "#06b6d4"            -- Cyan-500
  , locked: false
  }

-- | Get guide position.
guidePosition :: Guide -> Number
guidePosition (Guide g) = g.position

-- | Get guide ID.
guideId :: Guide -> String
guideId (Guide g) = g.id

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // canvas config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete canvas configuration.
type CanvasConfig =
  { minZoom :: ViewportZoom
  , maxZoom :: ViewportZoom
  , gridConfig :: GridConfig
  , snapConfig :: SnapConfig
  , backgroundColor :: String
  , rulerVisible :: Boolean
  , rulerUnits :: String        -- "px" | "pt" | "mm" | "in"
  , scrollbarsVisible :: Boolean
  , antialiased :: Boolean
  , pixelPerfect :: Boolean     -- Snap to whole pixels when rendering
  }

-- | Default canvas configuration.
defaultCanvasConfig :: CanvasConfig
defaultCanvasConfig =
  { minZoom: viewportZoom 0.01   -- 1%
  , maxZoom: viewportZoom 64.0   -- 6400%
  , gridConfig: defaultGridConfig
  , snapConfig: defaultSnapConfig
  , backgroundColor: "#1e1e1e"  -- Dark gray
  , rulerVisible: true
  , rulerUnits: "px"
  , scrollbarsVisible: true
  , antialiased: true
  , pixelPerfect: false
  }

-- | Set minimum zoom.
withMinZoom :: ViewportZoom -> CanvasConfig -> CanvasConfig
withMinZoom z config = config { minZoom = z }

-- | Set maximum zoom.
withMaxZoom :: ViewportZoom -> CanvasConfig -> CanvasConfig
withMaxZoom z config = config { maxZoom = z }

-- | Set grid configuration.
withGridConfig :: GridConfig -> CanvasConfig -> CanvasConfig
withGridConfig grid config = config { gridConfig = grid }

-- | Set snap configuration.
withSnapConfig :: SnapConfig -> CanvasConfig -> CanvasConfig
withSnapConfig snap config = config { snapConfig = snap }

-- | Set background color.
withBackgroundColor :: String -> CanvasConfig -> CanvasConfig
withBackgroundColor color config = config { backgroundColor = color }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // canvas dimensions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Canvas bounds (can be infinite or finite).
-- |
-- | - Infinite: No boundaries, pan forever
-- | - Finite: Clamped to specified rectangle
data CanvasBounds
  = Infinite
  | Finite { x :: Number, y :: Number, width :: Number, height :: Number }

derive instance eqCanvasBounds :: Eq CanvasBounds

instance showCanvasBounds :: Show CanvasBounds where
  show Infinite = "infinite"
  show (Finite b) = "bounds(" <> show b.width <> "x" <> show b.height <> ")"

-- | Infinite canvas bounds.
infiniteBounds :: CanvasBounds
infiniteBounds = Infinite

-- | Finite canvas bounds.
finiteBounds :: Number -> Number -> Number -> Number -> CanvasBounds
finiteBounds x y width height = Finite { x, y, width, height }

-- | Check if point is within canvas bounds.
boundsContains :: Number -> Number -> CanvasBounds -> Boolean
boundsContains _ _ Infinite = true
boundsContains px py (Finite b) =
  px >= b.x && px <= (b.x + b.width) &&
  py >= b.y && py <= (b.y + b.height)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Safe array indexing using Data.Array.index
arrayIndex :: forall a. Array a -> Int -> Maybe a
arrayIndex = index
