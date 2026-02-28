-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // gpu // scene3d // selection
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Selection — Object selection state and visual feedback.
-- |
-- | ## Design Philosophy
-- | Selection is pure data. Visual highlighting (outlines, tinting) is
-- | computed from selection state by the renderer.
-- |
-- | ## Three.js Parity
-- | - OutlinePass for selection highlighting
-- | - Box selection (marquee)
-- | - Multi-select with modifiers
-- |
-- | ## Cinema4D Parity  
-- | - Orange selection highlight
-- | - Hierarchy selection (parent/children)
-- | - Component selection (vertex/edge/face)

module Hydrogen.GPU.Scene3D.Selection
  ( -- * Selection Mode
    SelectionLevel
      ( ObjectLevel
      , VertexLevel
      , EdgeLevel
      , FaceLevel
      )
  
  -- * Selection State
  , SelectionState
  , defaultSelectionState
  
  -- * Highlight Style
  , HighlightStyle
  , defaultHighlightStyle
  , selectionHighlight
  , hoverHighlight
  
  -- * Selection Operations
  , selectObject
  , deselectObject
  , toggleObject
  , selectAll
  , deselectAll
  , invertSelection
  , selectInMarquee
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , map
  , not
  , (==)
  , (&&)
  , (||)
  , (<=)
  , (>=)
  )

import Data.Array (filter)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Set (Set)
import Data.Set as Set

import Hydrogen.Schema.Color.SRGB (SRGB, srgb)
import Hydrogen.Schema.Dimension.Vector.Vec2 (Vec2(Vec2))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // selection level
-- ═════════════════════════════════════════════════════════════════════════════

-- | Level of selection granularity.
-- |
-- | ObjectLevel: Select entire objects (default)
-- | VertexLevel: Select individual vertices (edit mode)
-- | EdgeLevel: Select edges between vertices
-- | FaceLevel: Select polygon faces
data SelectionLevel
  = ObjectLevel
  | VertexLevel
  | EdgeLevel
  | FaceLevel

derive instance eqSelectionLevel :: Eq SelectionLevel

instance showSelectionLevel :: Show SelectionLevel where
  show ObjectLevel = "ObjectLevel"
  show VertexLevel = "VertexLevel"
  show EdgeLevel = "EdgeLevel"
  show FaceLevel = "FaceLevel"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // highlight style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual style for selection highlighting.
-- |
-- | Used to render outlines, tints, or other visual feedback
-- | for selected and hovered objects.
type HighlightStyle =
  { outlineColor :: SRGB              -- Outline color
  , outlineWidth :: Number            -- Outline thickness (pixels)
  , fillTint :: Maybe SRGB            -- Optional fill color overlay
  , fillOpacity :: Number             -- Fill tint opacity (0-1)
  , pulseEnabled :: Boolean           -- Animate outline?
  , pulseSpeed :: Number              -- Pulse animation speed
  }

-- | Default highlight style — no highlighting.
defaultHighlightStyle :: HighlightStyle
defaultHighlightStyle =
  { outlineColor: srgb 255 128 0      -- Orange (Cinema4D style)
  , outlineWidth: 2.0
  , fillTint: Nothing
  , fillOpacity: 0.0
  , pulseEnabled: false
  , pulseSpeed: 1.0
  }

-- | Standard selection highlight — orange outline.
selectionHighlight :: HighlightStyle
selectionHighlight =
  { outlineColor: srgb 255 128 0      -- Orange
  , outlineWidth: 2.0
  , fillTint: Just (srgb 255 153 51)
  , fillOpacity: 0.1
  , pulseEnabled: false
  , pulseSpeed: 1.0
  }

-- | Hover highlight — lighter, thinner outline.
hoverHighlight :: HighlightStyle
hoverHighlight =
  { outlineColor: srgb 255 204 102    -- Light orange
  , outlineWidth: 1.0
  , fillTint: Nothing
  , fillOpacity: 0.0
  , pulseEnabled: false
  , pulseSpeed: 1.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // selection state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete selection state.
-- |
-- | Tracks which objects are selected, hovered, and the selection mode.
type SelectionState =
  { level :: SelectionLevel           -- Object/Vertex/Edge/Face
  , selectedObjects :: Set Int        -- Indices of selected objects
  , hoveredObject :: Maybe Int        -- Object under cursor
  , activeObject :: Maybe Int         -- Primary selection (last clicked)
  -- Component selection (for vertex/edge/face modes)
  , selectedVertices :: Set Int       -- Selected vertex indices
  , selectedEdges :: Set Int          -- Selected edge indices
  , selectedFaces :: Set Int          -- Selected face indices
  -- Highlight styles
  , selectionStyle :: HighlightStyle
  , hoverStyle :: HighlightStyle
  -- Marquee state
  , isMarqueeActive :: Boolean
  , marqueeStart :: Vec2 Number
  , marqueeEnd :: Vec2 Number
  }

-- | Default selection state — nothing selected, object mode.
defaultSelectionState :: SelectionState
defaultSelectionState =
  { level: ObjectLevel
  , selectedObjects: Set.empty
  , hoveredObject: Nothing
  , activeObject: Nothing
  , selectedVertices: Set.empty
  , selectedEdges: Set.empty
  , selectedFaces: Set.empty
  , selectionStyle: selectionHighlight
  , hoverStyle: hoverHighlight
  , isMarqueeActive: false
  , marqueeStart: Vec2 0.0 0.0
  , marqueeEnd: Vec2 0.0 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // selection operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Select an object (add to selection, make active).
selectObject :: Int -> SelectionState -> SelectionState
selectObject idx state = state
  { selectedObjects = Set.insert idx state.selectedObjects
  , activeObject = Just idx
  }

-- | Deselect an object.
deselectObject :: Int -> SelectionState -> SelectionState
deselectObject idx state = state
  { selectedObjects = Set.delete idx state.selectedObjects
  , activeObject = if state.activeObject == Just idx then Nothing else state.activeObject
  }

-- | Toggle object selection.
toggleObject :: Int -> SelectionState -> SelectionState
toggleObject idx state =
  if Set.member idx state.selectedObjects
    then deselectObject idx state
    else selectObject idx state

-- | Select all objects (caller provides full list).
selectAll :: Array Int -> SelectionState -> SelectionState
selectAll allIndices state = state
  { selectedObjects = Set.fromFoldable allIndices
  }

-- | Clear all selection.
deselectAll :: SelectionState -> SelectionState
deselectAll state = state
  { selectedObjects = Set.empty
  , activeObject = Nothing
  , selectedVertices = Set.empty
  , selectedEdges = Set.empty
  , selectedFaces = Set.empty
  }

-- | Invert selection (requires knowing all object indices).
invertSelection :: Array Int -> SelectionState -> SelectionState
invertSelection allIndices state = state
  { selectedObjects = Set.fromFoldable (filter notSelected allIndices)
  }
  where
    notSelected idx = not (Set.member idx state.selectedObjects)

-- | Select objects within a screen-space rectangle.
-- |
-- | Takes object screen positions and returns which are inside marquee.
-- | Caller is responsible for computing screen positions of objects.
selectInMarquee 
  :: Array { idx :: Int, screenPos :: Vec2 Number }
  -> SelectionState 
  -> SelectionState
selectInMarquee objectPositions state =
  let
    Vec2 x1 y1 = state.marqueeStart
    Vec2 x2 y2 = state.marqueeEnd
    minX = if x1 <= x2 then x1 else x2
    maxX = if x1 >= x2 then x1 else x2
    minY = if y1 <= y2 then y1 else y2
    maxY = if y1 >= y2 then y1 else y2
    
    inMarquee { screenPos: Vec2 px py } =
      px >= minX && px <= maxX && py >= minY && py <= maxY
    
    insideObjects = filter inMarquee objectPositions
    insideIndices = map (\o -> o.idx) insideObjects
  in
    state { selectedObjects = Set.fromFoldable insideIndices }
