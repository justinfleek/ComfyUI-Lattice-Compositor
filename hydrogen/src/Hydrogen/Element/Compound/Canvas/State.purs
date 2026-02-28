-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // compound // canvas // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas State — Complete state management for infinite canvas.
-- |
-- | ## Design Philosophy
-- |
-- | Canvas state is a **pure data structure** that combines:
-- |
-- | - **Viewport state**: Pan, zoom, visible bounds (from Schema.Graph.Viewport)
-- | - **Gesture state**: Active gestures, touch tracking (from Schema.Gestural)
-- | - **Selection state**: Selected objects, anchor point
-- | - **Tool state**: Current tool, tool-specific state
-- | - **Interaction state**: Hover, drag, focus
-- | - **History state**: Undo/redo stack
-- |
-- | ## Event-Driven Model
-- |
-- | Canvas does NOT poll or animate continuously. State changes via:
-- |
-- | 1. User input (pointer, touch, keyboard)
-- | 2. External data changes
-- | 3. Timer/animation completion
-- |
-- | Each event produces a new CanvasState. The runtime diffs and patches.
-- |
-- | ## Gesture Integration
-- |
-- | All gesture types from Schema.Gestural are supported:
-- |
-- | - **Pointer**: Mouse, touch, pen with pressure/tilt
-- | - **Gestures**: Tap, LongPress, Swipe, Pan, Pinch, Rotate
-- | - **DragDrop**: Full drag lifecycle with transfer data
-- | - **Keyboard**: Keys, modifiers, shortcuts
-- |
-- | ## Dependencies
-- |
-- | - Schema.Graph.Viewport (viewport state)
-- | - Schema.Gestural.* (all gesture types)
-- | - Composition.Trigger (event system)
-- | - Canvas.Types (canvas-specific types)

module Hydrogen.Element.Compound.Canvas.State
  ( -- * Canvas State
    CanvasState
  , HistoryEntry
  , initialCanvasState
  , resetCanvasState
  
  -- * Viewport Operations
  , getViewport
  , setViewport
  , panBy
  , panTo
  , zoomIn
  , zoomOut
  , zoomTo
  , zoomToFit
  , zoomToSelection
  
  -- * Tool Operations
  , getTool
  , setTool
  , previousTool
  , toggleSpacebarPan
  
  -- * Selection Operations
  , getSelection
  , setSelection
  , selectObject
  , deselectObject
  , selectAll
  , deselectAll
  , toggleSelection
  , selectInRect
  
  -- * Config Operations
  , getConfig
  , getGridConfig
  , getGuides
  
  -- * Object/Layer Operations
  , addObject
  , removeObject
  , updateObject
  , getObjects
  , setObjectZIndex
  , bringToFront
  , sendToBack
  , moveLayerUp
  , moveLayerDown
  
  -- * Gesture Operations
  , getGestureState
  , updateGestureState
  , getPointerState
  , updatePointerState
  , getDragState
  , updateDragState
  , getTouchState
  , updateTouchState
  
  -- * Interaction State
  , InteractionMode(..)
  , getInteractionMode
  , setInteractionMode
  , isIdle
  , isPanning
  , isZooming
  , isSelecting
  , isDragging
  , isDrawing
  
  -- * Hover State
  , getHoveredObject
  , setHoveredObject
  , clearHoveredObject
  , hasHoveredObject
  
  -- * Keyboard State
  , getKeyboardState
  , updateKeyboardState
  , isCtrlHeld
  , isAltHeld
  , isShiftHeld
  , isMetaHeld
  , hasAnyModifier
  , lastPressedKey
  
  -- * History Operations
  , canUndo
  , canRedo
  , pushHistory
  , undo
  , redo
  , clearHistory
  
  -- * Derived State
  , visibleObjects
  , isObjectVisible
  , screenToCanvas
  , canvasToScreen
  
  -- * State Queries
  , hasSelection
  , selectionCount
  , objectCount
  , undoStackDepth
  , redoStackDepth
  , objectAtIndex
  , currentZoomPercent
  , isAtMinZoom
  , isAtMaxZoom
  , isZoomInRange
  , stateDebugInfo
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (==)
  , (/=)
  , (&&)
  , (||)
  , (>=)
  , (<=)
  , (>)
  , (<)
  , (+)
  , (-)
  , (*)
  , (/)
  , not
  , max
  , min
  , ($)
  )

import Data.Array (length, filter, snoc, take, drop, null, index, head, foldl)
import Data.Array ((:)) as Array
import Data.Maybe (Maybe(Just, Nothing), isJust, fromMaybe)
import Data.Functor (map)

-- Viewport state from Schema
import Hydrogen.Schema.Graph.Viewport as VP
  
-- Gesture states from Schema
import Hydrogen.Schema.Gestural.Gesture as Gesture
import Hydrogen.Schema.Gestural.Pointer as Pointer
import Hydrogen.Schema.Gestural.DragDrop as DragDrop
import Hydrogen.Schema.Gestural.Touch as Touch
import Hydrogen.Schema.Gestural.Keyboard as Keyboard

-- Canvas-specific types (qualified import)
import Hydrogen.Element.Compound.Canvas.Types as Types

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // interaction mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Current interaction mode determines how input is interpreted.
data InteractionMode
  = ModeIdle              -- ^ No active interaction
  | ModePanning           -- ^ Viewport pan in progress
  | ModeZooming           -- ^ Zoom gesture in progress
  | ModeSelecting         -- ^ Selection marquee active
  | ModeDragging          -- ^ Object drag in progress
  | ModeDrawing           -- ^ Shape/path drawing active
  | ModeEditing           -- ^ Text/point editing active
  | ModeContextMenu       -- ^ Context menu open
  | ModeCustom String     -- ^ Custom mode for extensions

derive instance eqInteractionMode :: Eq InteractionMode

instance showInteractionMode :: Show InteractionMode where
  show ModeIdle = "idle"
  show ModePanning = "panning"
  show ModeZooming = "zooming"
  show ModeSelecting = "selecting"
  show ModeDragging = "dragging"
  show ModeDrawing = "drawing"
  show ModeEditing = "editing"
  show ModeContextMenu = "context-menu"
  show (ModeCustom name) = "custom:" <> name

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // history entry
-- ═════════════════════════════════════════════════════════════════════════════

-- | History entry for undo/redo.
-- |
-- | Stores enough state to restore canvas to a previous point.
type HistoryEntry =
  { objects :: Array Types.CanvasObject
  , selection :: Types.SelectionState
  , label :: String                    -- Human-readable description
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // canvas state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete canvas state.
-- |
-- | This is the single source of truth for the canvas component.
-- | All operations produce a new CanvasState (immutable).
type CanvasState =
  { -- Identity
    id :: Types.CanvasId
  , config :: Types.CanvasConfig
  , bounds :: Types.CanvasBounds
  
  -- Viewport (from Schema.Graph.Viewport)
  , viewport :: VP.ViewportState
  
  -- Tools
  , currentTool :: Types.CanvasTool
  , previousTool :: Maybe Types.CanvasTool   -- For spacebar-pan toggle
  , spacebarHeld :: Boolean
  
  -- Selection
  , selection :: Types.SelectionState
  
  -- Objects (the actual content)
  , objects :: Array Types.CanvasObject
  
  -- Guides
  , guides :: Array Types.Guide
  
  -- Interaction
  , interactionMode :: InteractionMode
  , hoveredObject :: Maybe Types.CanvasObjectId
  
  -- Gesture states (from Schema.Gestural)
  , gestureState :: Gesture.GestureState
  , pointerState :: Pointer.PointerState
  , dragState :: DragDrop.DragState
  , touchState :: Touch.TouchState
  , keyboardState :: Keyboard.KeyboardState
  
  -- History
  , undoStack :: Array HistoryEntry
  , redoStack :: Array HistoryEntry
  , maxHistorySize :: Int
  
  -- Performance
  , lastRenderTime :: Number           -- For FPS tracking
  , frameCount :: Int
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create initial canvas state.
initialCanvasState :: Types.CanvasId -> Number -> Number -> CanvasState
initialCanvasState canvasId width height =
  { id: canvasId
  , config: Types.defaultCanvasConfig
  , bounds: Types.infiniteBounds
  , viewport: VP.initialViewport width height
  , currentTool: Types.ToolSelect
  , previousTool: Nothing
  , spacebarHeld: false
  , selection: Types.emptySelection
  , objects: []
  , guides: []
  , interactionMode: ModeIdle
  , hoveredObject: Nothing
  , gestureState: Gesture.initialGestureState
  , pointerState: Pointer.defaultPointerState
  , dragState: DragDrop.initialDragState
  , touchState: Touch.noTouches
  , keyboardState: Keyboard.initialKeyboardState
  , undoStack: []
  , redoStack: []
  , maxHistorySize: 100
  , lastRenderTime: 0.0
  , frameCount: 0
  }

-- | Reset canvas to initial state, preserving config.
resetCanvasState :: CanvasState -> CanvasState
resetCanvasState state =
  let initial = initialCanvasState state.id (screenWidth state) (screenHeight state)
  in initial { config = state.config }
  where
    screenWidth s = s.viewport.screenWidth
    screenHeight s = s.viewport.screenHeight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // viewport operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current viewport state.
getViewport :: CanvasState -> VP.ViewportState
getViewport state = state.viewport

-- | Set viewport state.
setViewport :: VP.ViewportState -> CanvasState -> CanvasState
setViewport vp state = state { viewport = vp }

-- | Pan by delta (in screen pixels).
panBy :: Number -> Number -> CanvasState -> CanvasState
panBy dx dy state = state { viewport = VP.applyPan dx dy state.viewport }

-- | Pan to absolute position (in canvas coordinates).
panTo :: Number -> Number -> CanvasState -> CanvasState
panTo x y state = state { viewport = VP.setPan (VP.panTo x y) state.viewport }

-- | Zoom in by one step.
zoomIn :: CanvasState -> CanvasState
zoomIn state = state { viewport = VP.applyZoom (VP.zoomIn (VP.viewportZoomLevel state.viewport)) state.viewport }

-- | Zoom out by one step.
zoomOut :: CanvasState -> CanvasState
zoomOut state = state { viewport = VP.applyZoom (VP.zoomOut (VP.viewportZoomLevel state.viewport)) state.viewport }

-- | Zoom to specific level.
zoomTo :: VP.ViewportZoom -> CanvasState -> CanvasState
zoomTo zoom state = state { viewport = VP.applyZoom zoom state.viewport }

-- | Zoom to fit all objects in view.
zoomToFit :: CanvasState -> CanvasState
zoomToFit state =
  case calculateObjectsBounds state.objects of
    Nothing -> state  -- No objects, keep current
    Just bounds -> state { viewport = VP.fitContent bounds state.viewport }

-- | Zoom to fit selection in view.
zoomToSelection :: CanvasState -> CanvasState
zoomToSelection state =
  case Types.selectionBounds state.selection state.objects of
    Nothing -> state  -- No selection
    Just bounds -> 
      let vpBounds = 
            { left: bounds.x
            , top: bounds.y
            , right: bounds.x + bounds.width
            , bottom: bounds.y + bounds.height
            }
      in state { viewport = VP.fitContent vpBounds state.viewport }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // tool operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current tool.
getTool :: CanvasState -> Types.CanvasTool
getTool state = state.currentTool

-- | Set current tool.
setTool :: Types.CanvasTool -> CanvasState -> CanvasState
setTool tool state = state 
  { currentTool = tool
  , previousTool = Just state.currentTool
  }

-- | Revert to previous tool.
previousTool :: CanvasState -> CanvasState
previousTool state = case state.previousTool of
  Nothing -> state
  Just prev -> state { currentTool = prev, previousTool = Nothing }

-- | Toggle spacebar pan mode.
toggleSpacebarPan :: Boolean -> CanvasState -> CanvasState
toggleSpacebarPan held state =
  if held && not state.spacebarHeld
    then state 
      { spacebarHeld = true
      , previousTool = Just state.currentTool
      , currentTool = Types.ToolPan
      }
    else if not held && state.spacebarHeld
      then state
        { spacebarHeld = false
        , currentTool = fromMaybe Types.ToolSelect state.previousTool
        , previousTool = Nothing
        }
      else state

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // selection operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current selection.
getSelection :: CanvasState -> Types.SelectionState
getSelection state = state.selection

-- | Set selection.
setSelection :: Types.SelectionState -> CanvasState -> CanvasState
setSelection sel state = state { selection = sel }

-- | Select a single object.
selectObject :: Types.CanvasObjectId -> CanvasState -> CanvasState
selectObject objId state = state { selection = Types.singleSelection objId }

-- | Deselect a specific object.
deselectObject :: Types.CanvasObjectId -> CanvasState -> CanvasState
deselectObject objId state = state { selection = Types.removeFromSelection objId state.selection }

-- | Select all objects.
selectAll :: CanvasState -> CanvasState
selectAll state = 
  let allIds = getAllObjectIds state.objects
  in state { selection = Types.multiSelection allIds }

-- | Deselect all objects.
deselectAll :: CanvasState -> CanvasState
deselectAll state = state { selection = Types.emptySelection }

-- | Toggle selection of an object.
toggleSelection :: Types.CanvasObjectId -> CanvasState -> CanvasState
toggleSelection objId state =
  if Types.isSelected objId state.selection
    then deselectObject objId state
    else state { selection = Types.addToSelection objId state.selection }

-- | Select all objects within a rectangle (in canvas coordinates).
selectInRect :: { x :: Number, y :: Number, width :: Number, height :: Number } -> CanvasState -> CanvasState
selectInRect rect state =
  let 
    objectsInRect = filter (objectIntersectsRect rect) state.objects
    ids = getAllObjectIds objectsInRect
  in state { selection = Types.multiSelection ids }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // config operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get canvas configuration.
getConfig :: CanvasState -> Types.CanvasConfig
getConfig state = state.config

-- | Get grid configuration.
getGridConfig :: CanvasState -> Types.GridConfig
getGridConfig state = state.config.gridConfig

-- | Get all guides.
getGuides :: CanvasState -> Array Types.Guide
getGuides state = state.guides

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // object/layer operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add an object to the canvas.
-- |
-- | New objects are added at the end (highest z-index by array position).
addObject :: Types.CanvasObject -> CanvasState -> CanvasState
addObject obj state = state { objects = snoc state.objects obj }

-- | Remove an object from the canvas by ID.
removeObject :: Types.CanvasObjectId -> CanvasState -> CanvasState
removeObject objId state = 
  state { objects = filter (\obj -> Types.objectId obj /= objId) state.objects }

-- | Update an object by ID.
-- |
-- | If the object doesn't exist, state is unchanged.
updateObject :: Types.CanvasObjectId -> (Types.CanvasObject -> Types.CanvasObject) -> CanvasState -> CanvasState
updateObject objId updateFn state =
  state { objects = map (\obj -> 
    if Types.objectId obj == objId 
      then updateFn obj 
      else obj
  ) state.objects }

-- | Get all objects.
getObjects :: CanvasState -> Array Types.CanvasObject
getObjects state = state.objects

-- | Set z-index for an object.
setObjectZIndex :: Types.CanvasObjectId -> Int -> CanvasState -> CanvasState
setObjectZIndex objId newZ state =
  updateObject objId (\obj -> obj { zIndex = newZ }) state

-- | Find maximum z-index in canvas.
maxZIndex :: CanvasState -> Int
maxZIndex state = 
  case head state.objects of
    Nothing -> 0
    Just first -> foldl (\acc obj -> max acc (Types.objectZIndex obj)) (Types.objectZIndex first) state.objects

-- | Find minimum z-index in canvas.
minZIndex :: CanvasState -> Int
minZIndex state = 
  case head state.objects of
    Nothing -> 0
    Just first -> foldl (\acc obj -> min acc (Types.objectZIndex obj)) (Types.objectZIndex first) state.objects

-- | Bring object to front (highest z-index).
bringToFront :: Types.CanvasObjectId -> CanvasState -> CanvasState
bringToFront objId state =
  let newZ = maxZIndex state + 1
  in setObjectZIndex objId newZ state

-- | Send object to back (lowest z-index).
sendToBack :: Types.CanvasObjectId -> CanvasState -> CanvasState
sendToBack objId state =
  let newZ = minZIndex state - 1
  in setObjectZIndex objId newZ state

-- | Move layer up (increase z-index by 1).
moveLayerUp :: Types.CanvasObjectId -> CanvasState -> CanvasState
moveLayerUp objId state =
  case findObject objId state.objects of
    Nothing -> state
    Just obj -> setObjectZIndex objId (Types.objectZIndex obj + 1) state

-- | Move layer down (decrease z-index by 1).
moveLayerDown :: Types.CanvasObjectId -> CanvasState -> CanvasState
moveLayerDown objId state =
  case findObject objId state.objects of
    Nothing -> state
    Just obj -> setObjectZIndex objId (Types.objectZIndex obj - 1) state

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // gesture operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get gesture state.
getGestureState :: CanvasState -> Gesture.GestureState
getGestureState state = state.gestureState

-- | Update gesture state.
updateGestureState :: Gesture.GestureState -> CanvasState -> CanvasState
updateGestureState gs state = state { gestureState = gs }

-- | Get pointer state.
getPointerState :: CanvasState -> Pointer.PointerState
getPointerState state = state.pointerState

-- | Update pointer state.
updatePointerState :: Pointer.PointerState -> CanvasState -> CanvasState
updatePointerState ps state = state { pointerState = ps }

-- | Get drag state.
getDragState :: CanvasState -> DragDrop.DragState
getDragState state = state.dragState

-- | Update drag state.
updateDragState :: DragDrop.DragState -> CanvasState -> CanvasState
updateDragState ds state = state { dragState = ds }

-- | Get touch state.
getTouchState :: CanvasState -> Touch.TouchState
getTouchState state = state.touchState

-- | Update touch state.
updateTouchState :: Touch.TouchState -> CanvasState -> CanvasState
updateTouchState ts state = state { touchState = ts }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // interaction queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get interaction mode.
getInteractionMode :: CanvasState -> InteractionMode
getInteractionMode state = state.interactionMode

-- | Set interaction mode.
setInteractionMode :: InteractionMode -> CanvasState -> CanvasState
setInteractionMode mode state = state { interactionMode = mode }

-- | Is canvas idle?
isIdle :: CanvasState -> Boolean
isIdle state = state.interactionMode == ModeIdle

-- | Is panning in progress?
isPanning :: CanvasState -> Boolean
isPanning state = state.interactionMode == ModePanning

-- | Is zooming in progress?
isZooming :: CanvasState -> Boolean
isZooming state = state.interactionMode == ModeZooming

-- | Is selecting in progress?
isSelecting :: CanvasState -> Boolean
isSelecting state = state.interactionMode == ModeSelecting

-- | Is dragging in progress?
isDragging :: CanvasState -> Boolean
isDragging state = state.interactionMode == ModeDragging

-- | Is drawing in progress?
isDrawing :: CanvasState -> Boolean
isDrawing state = state.interactionMode == ModeDrawing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // hover state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get currently hovered object.
getHoveredObject :: CanvasState -> Maybe Types.CanvasObjectId
getHoveredObject state = state.hoveredObject

-- | Set hovered object.
setHoveredObject :: Types.CanvasObjectId -> CanvasState -> CanvasState
setHoveredObject objId state = state { hoveredObject = Just objId }

-- | Clear hovered object.
clearHoveredObject :: CanvasState -> CanvasState
clearHoveredObject state = state { hoveredObject = Nothing }

-- | Check if any object is being hovered.
hasHoveredObject :: CanvasState -> Boolean
hasHoveredObject state = isJust state.hoveredObject

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // keyboard state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get keyboard state.
getKeyboardState :: CanvasState -> Keyboard.KeyboardState
getKeyboardState state = state.keyboardState

-- | Update keyboard state.
updateKeyboardState :: Keyboard.KeyboardState -> CanvasState -> CanvasState
updateKeyboardState ks state = state { keyboardState = ks }

-- | Check if Ctrl is held.
isCtrlHeld :: CanvasState -> Boolean
isCtrlHeld state = (Keyboard.stateModifiers state.keyboardState).ctrl

-- | Check if Alt is held.
isAltHeld :: CanvasState -> Boolean
isAltHeld state = (Keyboard.stateModifiers state.keyboardState).alt

-- | Check if Shift is held.
isShiftHeld :: CanvasState -> Boolean
isShiftHeld state = (Keyboard.stateModifiers state.keyboardState).shift

-- | Check if Meta (Cmd on Mac, Win on Windows) is held.
isMetaHeld :: CanvasState -> Boolean
isMetaHeld state = (Keyboard.stateModifiers state.keyboardState).meta

-- | Check if any modifier is held.
hasAnyModifier :: CanvasState -> Boolean
hasAnyModifier state = Keyboard.hasActiveModifiers state.keyboardState

-- | Get the last pressed key code (if any).
lastPressedKey :: CanvasState -> Maybe Keyboard.KeyCode
lastPressedKey state = 
  case Keyboard.stateLastEvent state.keyboardState of
    Nothing -> Nothing
    Just event -> Just (Keyboard.eventCode event)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // history operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Can undo?
canUndo :: CanvasState -> Boolean
canUndo state = not (null state.undoStack)

-- | Can redo?
canRedo :: CanvasState -> Boolean
canRedo state = not (null state.redoStack)

-- | Push current state to history.
-- |
-- | Uses cons (prepend) for O(1) stack operations.
-- | Most recent entry is at the head of the array.
pushHistory :: String -> CanvasState -> CanvasState
pushHistory label state =
  let 
    entry = 
      { objects: state.objects
      , selection: state.selection
      , label
      }
    -- Prepend new entry, then take from the beginning to enforce max size
    newUndo = take state.maxHistorySize (Array.(:) entry state.undoStack)
  in state 
    { undoStack = newUndo
    , redoStack = []  -- Clear redo on new action
    }

-- | Undo last action.
-- |
-- | Pops from undo stack (head) and pushes current state to redo stack.
undo :: CanvasState -> CanvasState
undo state = case head state.undoStack of
  Nothing -> state
  Just entry ->
    let 
      currentEntry = 
        { objects: state.objects
        , selection: state.selection
        , label: "Redo point"
        }
    in state
      { objects = entry.objects
      , selection = entry.selection
      , undoStack = dropFirst state.undoStack
      , redoStack = Array.(:) currentEntry state.redoStack
      }

-- | Redo last undone action.
-- |
-- | Pops from redo stack (head) and pushes current state to undo stack.
redo :: CanvasState -> CanvasState
redo state = case head state.redoStack of
  Nothing -> state
  Just entry ->
    let 
      currentEntry = 
        { objects: state.objects
        , selection: state.selection
        , label: "Undo point"
        }
    in state
      { objects = entry.objects
      , selection = entry.selection
      , undoStack = Array.(:) currentEntry state.undoStack
      , redoStack = dropFirst state.redoStack
      }

-- | Clear all history.
clearHistory :: CanvasState -> CanvasState
clearHistory state = state { undoStack = [], redoStack = [] }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // derived state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get objects visible in current viewport.
visibleObjects :: CanvasState -> Array Types.CanvasObject
visibleObjects state =
  let bounds = VP.viewportBoundsAt state.viewport
  in filter (objectInViewportBounds bounds) state.objects

-- | Check if a specific object is visible.
isObjectVisible :: Types.CanvasObjectId -> CanvasState -> Boolean
isObjectVisible objId state =
  case findObject objId state.objects of
    Nothing -> false
    Just obj -> 
      let bounds = VP.viewportBoundsAt state.viewport
      in objectInViewportBounds bounds obj

-- | Convert screen coordinates to canvas coordinates.
screenToCanvas :: Number -> Number -> CanvasState -> { x :: Number, y :: Number }
screenToCanvas screenX screenY state =
  let 
    zoom = VP.zoomLevel (VP.viewportZoomLevel state.viewport)
    pan = VP.viewportPan state.viewport
  in
    { x: (screenX / zoom) + pan.x
    , y: (screenY / zoom) + pan.y
    }

-- | Convert canvas coordinates to screen coordinates.
canvasToScreen :: Number -> Number -> CanvasState -> { x :: Number, y :: Number }
canvasToScreen canvasX canvasY state =
  let 
    zoom = VP.zoomLevel (VP.viewportZoomLevel state.viewport)
    pan = VP.viewportPan state.viewport
  in
    { x: (canvasX - pan.x) * zoom
    , y: (canvasY - pan.y) * zoom
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // state queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if anything is selected.
hasSelection :: CanvasState -> Boolean
hasSelection state = Types.selectionCount state.selection > 0

-- | Get selection count (re-exported for convenience).
selectionCount :: CanvasState -> Int
selectionCount state = Types.selectionCount state.selection

-- | Get current zoom as percentage.
currentZoomPercent :: CanvasState -> Number
currentZoomPercent state = VP.zoomPercentage (VP.viewportZoomLevel state.viewport)

-- | Is at minimum zoom?
isAtMinZoom :: CanvasState -> Boolean
isAtMinZoom state = VP.isMinZoom (VP.viewportZoomLevel state.viewport)

-- | Is at maximum zoom?
isAtMaxZoom :: CanvasState -> Boolean
isAtMaxZoom state = VP.isMaxZoom (VP.viewportZoomLevel state.viewport)

-- | Get total number of objects on canvas.
objectCount :: CanvasState -> Int
objectCount state = length state.objects

-- | Get undo stack depth (for UI display).
undoStackDepth :: CanvasState -> Int
undoStackDepth state = length state.undoStack

-- | Get redo stack depth (for UI display).
redoStackDepth :: CanvasState -> Int
redoStackDepth state = length state.redoStack

-- | Get object at specific index in the objects array.
-- |
-- | Index 0 is the first object. Returns Nothing if out of bounds.
objectAtIndex :: Int -> CanvasState -> Maybe Types.CanvasObject
objectAtIndex idx state = index state.objects idx

-- | Check if zoom percentage is within a specific range.
-- |
-- | Useful for UI state (e.g., showing different controls at different zoom levels).
isZoomInRange :: Number -> Number -> CanvasState -> Boolean
isZoomInRange minPercent maxPercent state =
  let zoomPercent = currentZoomPercent state
  in zoomPercent >= minPercent && zoomPercent <= maxPercent

-- | Get debug info about canvas state.
-- |
-- | Returns a human-readable string summarizing the current state.
-- | Useful for development and debugging.
stateDebugInfo :: CanvasState -> String
stateDebugInfo state =
  "Canvas[" <> show (objectCount state) <> " objects, " 
  <> "zoom: " <> show (currentZoomPercent state) <> "%, "
  <> "selection: " <> show (selectionCount state) <> ", "
  <> "undo: " <> show (undoStackDepth state) <> ", "
  <> "redo: " <> show (redoStackDepth state) <> ", "
  <> "mode: " <> show state.interactionMode <> ", "
  <> "tool: " <> (show $ state.currentTool) <> "]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all object IDs.
getAllObjectIds :: Array Types.CanvasObject -> Array Types.CanvasObjectId
getAllObjectIds objects = map Types.objectId objects

-- | Find object by ID.
findObject :: Types.CanvasObjectId -> Array Types.CanvasObject -> Maybe Types.CanvasObject
findObject targetId objects =
  head (filter (\obj -> Types.objectId obj == targetId) objects)

-- | Check if object intersects a rectangle.
objectIntersectsRect :: { x :: Number, y :: Number, width :: Number, height :: Number } -> Types.CanvasObject -> Boolean
objectIntersectsRect rect obj =
  let b = Types.objectBounds obj
  in not (b.x + b.width < rect.x || 
          rect.x + rect.width < b.x ||
          b.y + b.height < rect.y ||
          rect.y + rect.height < b.y)

-- | Check if object is within viewport bounds.
objectInViewportBounds :: VP.ViewportBounds -> Types.CanvasObject -> Boolean
objectInViewportBounds vp obj =
  let b = Types.objectBounds obj
  in VP.boundsIntersect vp 
       { left: b.x
       , top: b.y
       , right: b.x + b.width
       , bottom: b.y + b.height
       }

-- | Calculate bounding box of all objects.
calculateObjectsBounds :: Array Types.CanvasObject -> Maybe VP.ViewportBounds
calculateObjectsBounds objects =
  if null objects
    then Nothing
    else 
      let 
        getBounds = Types.objectBounds
        minX = foldMin (\obj -> (getBounds obj).x) objects
        minY = foldMin (\obj -> (getBounds obj).y) objects
        maxX = foldMax (\obj -> (getBounds obj).x + (getBounds obj).width) objects
        maxY = foldMax (\obj -> (getBounds obj).y + (getBounds obj).height) objects
      in Just { left: minX, top: minY, right: maxX, bottom: maxY }

-- | Drop first element (O(n) but semantically correct for stack operations).
-- |
-- | Used by undo/redo stacks where head is most recent.
dropFirst :: forall a. Array a -> Array a
dropFirst arr = drop 1 arr

-- | Fold to find minimum.
foldMin :: forall a. (a -> Number) -> Array a -> Number
foldMin f arr = case head arr of
  Nothing -> 0.0
  Just first -> foldl (\acc x -> min acc (f x)) (f first) arr

-- | Fold to find maximum.
foldMax :: forall a. (a -> Number) -> Array a -> Number
foldMax f arr = case head arr of
  Nothing -> 0.0
  Just first -> foldl (\acc x -> max acc (f x)) (f first) arr
