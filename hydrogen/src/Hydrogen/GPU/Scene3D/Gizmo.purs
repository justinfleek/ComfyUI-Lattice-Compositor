-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // gpu // scene3d // gizmo
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Transform Gizmo — Pure state machine for 3D manipulation handles.
-- |
-- | ## Design Philosophy
-- | Gizmos are PURE STATE MACHINES. Visual geometry is derived from state.
-- | No FFI. Drag events come in as messages, state updates purely,
-- | gizmo geometry is rendered through the standard Scene3D pipeline.
-- |
-- | ## Three.js Parity
-- | - TransformControls mode: translate/rotate/scale
-- | - Space: local/world
-- | - Axis highlighting on hover
-- | - Snapping (deferred to Phase 5)
-- |
-- | ## Cinema4D Parity
-- | - Universal gizmo (all transforms in one)
-- | - Per-axis and per-plane manipulation
-- | - Visual feedback during drag

module Hydrogen.GPU.Scene3D.Gizmo
  ( -- * Gizmo Mode
    GizmoMode
      ( TranslateMode
      , RotateMode
      , ScaleMode
      )
  
  -- * Gizmo Space
  , GizmoSpace
      ( LocalSpace
      , WorldSpace
      )
  
  -- * Axis Selection
  , GizmoAxis
      ( AxisX
      , AxisY
      , AxisZ
      , PlaneXY
      , PlaneXZ
      , PlaneYZ
      , AxisAll
      , AxisNone
      )
  
  -- * Gizmo State
  , GizmoState
  , defaultGizmoState
  
  -- * Gizmo Messages
  , GizmoMsg
      ( HoverAxis
      , StartDrag
      , UpdateDrag
      , EndDrag
      , MiddleMouseStart
      , MiddleMouseDrag
      , MiddleMouseEnd
      , DoubleTapAxis
      , DoubleTapCenter
      , SetMode
      , SetSpace
      , ToggleSpace
      , SelectObject
      , MarqueeStart
      , MarqueeUpdate
      , MarqueeEnd
      , SelectAll
      , DeselectAll
      , InvertSelection
      )
  
  -- * Selection Modifier
  , SelectModifier
      ( SelectReplace
      , SelectAdd
      , SelectToggle
      , SelectSubtract
      )
  
  -- * Update Function
  , updateGizmo
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , not
  , (-)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Set (Set)
import Data.Set as Set

import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3(Vec3), vec3, subtractVec3)
import Hydrogen.Schema.Dimension.Vector.Vec2 (Vec2, vec2)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // gizmo mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transform gizmo mode — which type of manipulation is active.
-- |
-- | Translate: Move along axis/plane
-- | Rotate: Rotate around axis
-- | Scale: Scale along axis (uniform or per-axis)
data GizmoMode
  = TranslateMode
  | RotateMode
  | ScaleMode

derive instance eqGizmoMode :: Eq GizmoMode

instance showGizmoMode :: Show GizmoMode where
  show TranslateMode = "TranslateMode"
  show RotateMode = "RotateMode"
  show ScaleMode = "ScaleMode"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // gizmo space
-- ═════════════════════════════════════════════════════════════════════════════

-- | Coordinate space for gizmo operations.
-- |
-- | LocalSpace: Gizmo axes align with object's local rotation
-- | WorldSpace: Gizmo axes align with world X/Y/Z
data GizmoSpace
  = LocalSpace
  | WorldSpace

derive instance eqGizmoSpace :: Eq GizmoSpace

instance showGizmoSpace :: Show GizmoSpace where
  show LocalSpace = "LocalSpace"
  show WorldSpace = "WorldSpace"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // gizmo axis
-- ═════════════════════════════════════════════════════════════════════════════

-- | Active axis or plane for gizmo interaction.
-- |
-- | Single axis: constrain to X, Y, or Z
-- | Plane: constrain to XY, XZ, or YZ plane
-- | All: free transform (scale uniformly, translate freely)
-- | None: no interaction active
data GizmoAxis
  = AxisX      -- Red axis
  | AxisY      -- Green axis  
  | AxisZ      -- Blue axis
  | PlaneXY    -- Blue plane (normal = Z)
  | PlaneXZ    -- Green plane (normal = Y)
  | PlaneYZ    -- Red plane (normal = X)
  | AxisAll    -- Center sphere/cube — all axes
  | AxisNone   -- No axis selected

derive instance eqGizmoAxis :: Eq GizmoAxis

instance showGizmoAxis :: Show GizmoAxis where
  show AxisX = "AxisX"
  show AxisY = "AxisY"
  show AxisZ = "AxisZ"
  show PlaneXY = "PlaneXY"
  show PlaneXZ = "PlaneXZ"
  show PlaneYZ = "PlaneYZ"
  show AxisAll = "AxisAll"
  show AxisNone = "AxisNone"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // gizmo state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete gizmo state for transform manipulation.
-- |
-- | This is pure data. All state updates happen through `updateGizmo`.
-- | The gizmo renderer reads this state to produce visual geometry.
type GizmoState =
  { mode :: GizmoMode                   -- Translate/Rotate/Scale
  , space :: GizmoSpace                 -- Local/World coordinates
  , hoveredAxis :: GizmoAxis            -- Which axis is under cursor
  , activeAxis :: GizmoAxis             -- Which axis is being dragged
  , isDragging :: Boolean               -- Is a drag in progress?
  , dragStartWorld :: Vec3 Number       -- World position at drag start
  , dragCurrentWorld :: Vec3 Number     -- Current world position during drag
  , gizmoPosition :: Vec3 Number        -- Where to render the gizmo (object center)
  , gizmoScale :: Number                -- Visual scale (for screen-space sizing)
  -- Selection state
  , selectedObjects :: Set Int          -- Indices of selected objects
  , hoveredObject :: Maybe Int          -- Object under cursor (for highlight)
  -- Marquee selection state
  , isMarqueeActive :: Boolean          -- Is box select in progress?
  , marqueeStart :: Vec2 Number         -- Screen-space start of marquee
  , marqueeEnd :: Vec2 Number           -- Screen-space end of marquee
  -- Middle mouse state (for camera passthrough)
  , isMiddleMouseDrag :: Boolean        -- Middle mouse dragging?
  , middleMouseStart :: Vec3 Number     -- Middle mouse drag start
  }

-- | Default gizmo state — translate mode, world space, nothing selected.
defaultGizmoState :: GizmoState
defaultGizmoState =
  { mode: TranslateMode
  , space: WorldSpace
  , hoveredAxis: AxisNone
  , activeAxis: AxisNone
  , isDragging: false
  , dragStartWorld: vec3 0.0 0.0 0.0
  , dragCurrentWorld: vec3 0.0 0.0 0.0
  , gizmoPosition: vec3 0.0 0.0 0.0
  , gizmoScale: 1.0
  -- Selection
  , selectedObjects: Set.empty
  , hoveredObject: Nothing
  -- Marquee
  , isMarqueeActive: false
  , marqueeStart: vec2 0.0 0.0
  , marqueeEnd: vec2 0.0 0.0
  -- Middle mouse
  , isMiddleMouseDrag: false
  , middleMouseStart: vec3 0.0 0.0 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // gizmo msg
-- ═════════════════════════════════════════════════════════════════════════════

-- | Messages that update gizmo state.
-- |
-- | These map to user interactions:
-- | - Mouse hover over axis → HoverAxis
-- | - Mouse down on axis → StartDrag
-- | - Mouse move while dragging → UpdateDrag
-- | - Mouse up → EndDrag
-- | - Middle mouse → MiddleMouseDrag (pan/orbit bypass)
-- | - Double click → DoubleTap (reset/focus)
-- | - Keyboard shortcut → SetMode, ToggleSpace
data GizmoMsg
  = HoverAxis GizmoAxis                 -- Cursor entered axis region
  | StartDrag GizmoAxis (Vec3 Number)   -- Begin drag on axis at world point
  | UpdateDrag (Vec3 Number)            -- Continue drag to new world point
  | EndDrag                             -- Release drag
  | MiddleMouseStart (Vec3 Number)      -- Middle mouse down — often pan/orbit
  | MiddleMouseDrag (Vec3 Number)       -- Middle mouse move
  | MiddleMouseEnd                      -- Middle mouse up
  | DoubleTapAxis GizmoAxis             -- Double-click on axis — snap/align
  | DoubleTapCenter                     -- Double-click on center — reset transform
  | SetMode GizmoMode                   -- Switch translate/rotate/scale
  | SetSpace GizmoSpace                 -- Set local/world
  | ToggleSpace                         -- Flip between local/world
  -- Selection modifiers
  | SelectObject Int SelectModifier     -- Click object with modifier
  | MarqueeStart (Vec3 Number)          -- Begin box select
  | MarqueeUpdate (Vec3 Number)         -- Drag box select
  | MarqueeEnd SelectModifier           -- Complete box select with modifier
  | SelectAll                           -- Ctrl+A
  | DeselectAll                         -- Escape or click empty
  | InvertSelection                     -- Ctrl+I

-- | Selection modifier keys.
-- |
-- | Replace: Clear selection, select new (default click)
-- | Add: Add to selection (Shift+click)
-- | Toggle: Toggle in selection (Ctrl+click)
-- | Subtract: Remove from selection (Alt+click)
data SelectModifier
  = SelectReplace   -- Clear and select
  | SelectAdd       -- Add to existing
  | SelectToggle    -- Toggle membership
  | SelectSubtract  -- Remove from existing

derive instance eqSelectModifier :: Eq SelectModifier

instance showSelectModifier :: Show SelectModifier where
  show SelectReplace = "SelectReplace"
  show SelectAdd = "SelectAdd"
  show SelectToggle = "SelectToggle"
  show SelectSubtract = "SelectSubtract"

derive instance eqGizmoMsg :: Eq GizmoMsg

instance showGizmoMsg :: Show GizmoMsg where
  show (HoverAxis axis) = "HoverAxis(" <> show axis <> ")"
  show (StartDrag axis pos) = "StartDrag(" <> show axis <> ", " <> show pos <> ")"
  show (UpdateDrag pos) = "UpdateDrag(" <> show pos <> ")"
  show EndDrag = "EndDrag"
  show (MiddleMouseStart pos) = "MiddleMouseStart(" <> show pos <> ")"
  show (MiddleMouseDrag pos) = "MiddleMouseDrag(" <> show pos <> ")"
  show MiddleMouseEnd = "MiddleMouseEnd"
  show (DoubleTapAxis axis) = "DoubleTapAxis(" <> show axis <> ")"
  show DoubleTapCenter = "DoubleTapCenter"
  show (SetMode mode) = "SetMode(" <> show mode <> ")"
  show (SetSpace space) = "SetSpace(" <> show space <> ")"
  show ToggleSpace = "ToggleSpace"
  show (SelectObject idx modifier) = "SelectObject(" <> show idx <> ", " <> show modifier <> ")"
  show (MarqueeStart pos) = "MarqueeStart(" <> show pos <> ")"
  show (MarqueeUpdate pos) = "MarqueeUpdate(" <> show pos <> ")"
  show (MarqueeEnd modifier) = "MarqueeEnd(" <> show modifier <> ")"
  show SelectAll = "SelectAll"
  show DeselectAll = "DeselectAll"
  show InvertSelection = "InvertSelection"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // update
-- ═════════════════════════════════════════════════════════════════════════════

-- | Update gizmo state from a message.
-- |
-- | Pure function — no side effects.
updateGizmo :: GizmoMsg -> GizmoState -> GizmoState
updateGizmo msg state = case msg of
  
  -- ─────────────────────────────────────────────────────────────────────────
  -- Gizmo axis interaction
  -- ─────────────────────────────────────────────────────────────────────────
  
  HoverAxis axis ->
    -- Only update hover if not dragging
    if state.isDragging
      then state
      else state { hoveredAxis = axis }
  
  StartDrag axis worldPos ->
    state
      { activeAxis = axis
      , isDragging = true
      , dragStartWorld = worldPos
      , dragCurrentWorld = worldPos
      }
  
  UpdateDrag worldPos ->
    if state.isDragging
      then state { dragCurrentWorld = worldPos }
      else state
  
  EndDrag ->
    state
      { activeAxis = AxisNone
      , isDragging = false
      }
  
  -- ─────────────────────────────────────────────────────────────────────────
  -- Middle mouse (camera passthrough)
  -- ─────────────────────────────────────────────────────────────────────────
  
  MiddleMouseStart worldPos ->
    state
      { isMiddleMouseDrag = true
      , middleMouseStart = worldPos
      }
  
  MiddleMouseDrag _ ->
    -- State update minimal — camera controls handle the actual movement
    state
  
  MiddleMouseEnd ->
    state { isMiddleMouseDrag = false }
  
  -- ─────────────────────────────────────────────────────────────────────────
  -- Double tap actions
  -- ─────────────────────────────────────────────────────────────────────────
  
  DoubleTapAxis _ ->
    -- Double-tap on axis: snap to that axis alignment
    -- Implementation depends on what object is selected
    -- For now, just record the event — actual snap logic in application
    state
  
  DoubleTapCenter ->
    -- Double-tap on center: reset transform to identity
    -- Actual reset logic lives in application layer
    state
  
  -- ─────────────────────────────────────────────────────────────────────────
  -- Mode and space
  -- ─────────────────────────────────────────────────────────────────────────
  
  SetMode newMode ->
    state { mode = newMode }
  
  SetSpace newSpace ->
    state { space = newSpace }
  
  ToggleSpace ->
    state { space = toggleSpace state.space }
  
  -- ─────────────────────────────────────────────────────────────────────────
  -- Object selection
  -- ─────────────────────────────────────────────────────────────────────────
  
  SelectObject idx modifier ->
    state { selectedObjects = applySelectModifier idx modifier state.selectedObjects }
  
  SelectAll ->
    -- Application must provide total object count — this is a signal
    -- For now, no-op in isolation
    state
  
  DeselectAll ->
    state { selectedObjects = Set.empty }
  
  InvertSelection ->
    -- Requires knowing all object indices — application provides
    -- For now, no-op in isolation
    state
  
  -- ─────────────────────────────────────────────────────────────────────────
  -- Marquee (box) selection
  -- ─────────────────────────────────────────────────────────────────────────
  
  MarqueeStart screenPos ->
    state
      { isMarqueeActive = true
      , marqueeStart = vec2FromVec3XY screenPos
      , marqueeEnd = vec2FromVec3XY screenPos
      }
  
  MarqueeUpdate screenPos ->
    if state.isMarqueeActive
      then state { marqueeEnd = vec2FromVec3XY screenPos }
      else state
  
  MarqueeEnd _ ->
    -- Actual selection of objects in marquee happens in application
    -- (requires scene knowledge to test which objects are in the rect)
    state { isMarqueeActive = false }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Toggle between local and world space.
toggleSpace :: GizmoSpace -> GizmoSpace
toggleSpace LocalSpace = WorldSpace
toggleSpace WorldSpace = LocalSpace

-- | Apply selection modifier to update the selection set.
applySelectModifier :: Int -> SelectModifier -> Set Int -> Set Int
applySelectModifier idx modifier selection = case modifier of
  SelectReplace -> Set.singleton idx
  SelectAdd -> Set.insert idx selection
  SelectToggle -> 
    if Set.member idx selection
      then Set.delete idx selection
      else Set.insert idx selection
  SelectSubtract -> Set.delete idx selection

-- | Extract X and Y from a Vec3 as a Vec2 (for screen-space operations).
vec2FromVec3XY :: Vec3 Number -> Vec2 Number
vec2FromVec3XY (Vec3 x y _) = vec2 x y
