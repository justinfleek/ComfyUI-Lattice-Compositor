-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // spatial // gizmo
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Gizmo — Interactive 3D transform controls for spatial manipulation.
-- |
-- | ## Design Philosophy
-- |
-- | A gizmo provides visual handles for manipulating objects in 3D space,
-- | similar to transform controls in Blender, Unity, or After Effects.
-- | This is the primary interface for spatial manipulation in bento boxes
-- | and 3D widget systems.
-- |
-- | ## Gizmo Modes
-- |
-- | - **Translate**: Move along X, Y, Z axes or planes
-- | - **Rotate**: Rotate around X, Y, Z axes (shows rotation rings)
-- | - **Scale**: Scale along X, Y, Z axes or uniformly
-- |
-- | ## Interaction Model
-- |
-- | Gizmos track which handle is being manipulated:
-- | - **Axis handles**: Single-axis constraint (X, Y, or Z)
-- | - **Plane handles**: Two-axis constraint (XY, XZ, YZ)
-- | - **Center handle**: Unconstrained (translate) or uniform (scale)
-- |
-- | ## Coordinate Space
-- |
-- | Gizmos can operate in:
-- | - **Local space**: Axes aligned to object's rotation
-- | - **World space**: Axes aligned to world coordinates
-- | - **View space**: Axes aligned to camera view

module Hydrogen.Schema.Spatial.Gizmo
  ( -- * Core Types
    Gizmo(Gizmo)
  , GizmoMode(GizmoTranslate, GizmoRotate, GizmoScale)
  , GizmoSpace(SpaceLocal, SpaceWorld, SpaceView)
  , GizmoHandle(HandleNone, HandleX, HandleY, HandleZ, HandleXY, HandleXZ, HandleYZ, HandleCenter)
  
  -- * Construction
  , gizmo
  , translateGizmo
  , rotateGizmo
  , scaleGizmo
  
  -- * Mode
  , gizmoMode
  , setGizmoMode
  , cycleGizmoMode
  
  -- * Space
  , gizmoSpace
  , setGizmoSpace
  , toggleGizmoSpace
  
  -- * Handle State
  , activeHandle
  , hoveredHandle
  , setActiveHandle
  , setHoveredHandle
  , clearActiveHandle
  
  -- * Transform State
  , gizmoPosition
  , gizmoRotation
  , gizmoScale
  , setGizmoPosition
  , setGizmoRotation
  , setGizmoScale
  
  -- * Interaction
  , beginDrag
  , updateDrag
  , endDrag
  , isDragging
  , dragDelta
  
  -- * Visibility
  , gizmoVisible
  , setGizmoVisible
  , gizmoSize
  , setGizmoSize
  
  -- * Debug
  , showGizmo
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
  , (-)
  )

import Hydrogen.Schema.Dimension.Device (Pixel(Pixel))
import Hydrogen.Schema.Geometry.Shape (PixelPoint3D, pixelPoint3D, pixelOrigin3D)
import Hydrogen.Schema.Spatial.Gimbal (Gimbal, gimbalZero)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // gizmo mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | The current manipulation mode of the gizmo.
data GizmoMode
  = GizmoTranslate  -- ^ Move mode: translate along axes/planes
  | GizmoRotate     -- ^ Rotate mode: rotate around axes
  | GizmoScale      -- ^ Scale mode: scale along axes or uniformly

derive instance eqGizmoMode :: Eq GizmoMode
derive instance ordGizmoMode :: Ord GizmoMode

instance showGizmoMode :: Show GizmoMode where
  show GizmoTranslate = "(GizmoMode Translate)"
  show GizmoRotate = "(GizmoMode Rotate)"
  show GizmoScale = "(GizmoMode Scale)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // gizmo space
-- ═════════════════════════════════════════════════════════════════════════════

-- | The coordinate space for gizmo axes.
data GizmoSpace
  = SpaceLocal  -- ^ Axes aligned to object's local rotation
  | SpaceWorld  -- ^ Axes aligned to world coordinates
  | SpaceView   -- ^ Axes aligned to current camera view

derive instance eqGizmoSpace :: Eq GizmoSpace
derive instance ordGizmoSpace :: Ord GizmoSpace

instance showGizmoSpace :: Show GizmoSpace where
  show SpaceLocal = "(GizmoSpace Local)"
  show SpaceWorld = "(GizmoSpace World)"
  show SpaceView = "(GizmoSpace View)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // gizmo handle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Which part of the gizmo is being interacted with.
data GizmoHandle
  = HandleNone    -- ^ No handle selected
  | HandleX       -- ^ X-axis handle (red)
  | HandleY       -- ^ Y-axis handle (green)
  | HandleZ       -- ^ Z-axis handle (blue)
  | HandleXY      -- ^ XY-plane handle
  | HandleXZ      -- ^ XZ-plane handle
  | HandleYZ      -- ^ YZ-plane handle
  | HandleCenter  -- ^ Center handle (uniform/free)

derive instance eqGizmoHandle :: Eq GizmoHandle
derive instance ordGizmoHandle :: Ord GizmoHandle

instance showGizmoHandle :: Show GizmoHandle where
  show HandleNone = "(GizmoHandle None)"
  show HandleX = "(GizmoHandle X)"
  show HandleY = "(GizmoHandle Y)"
  show HandleZ = "(GizmoHandle Z)"
  show HandleXY = "(GizmoHandle XY)"
  show HandleXZ = "(GizmoHandle XZ)"
  show HandleYZ = "(GizmoHandle YZ)"
  show HandleCenter = "(GizmoHandle Center)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // gizmo type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete gizmo state for 3D transform manipulation.
-- |
-- | Tracks:
-- | - Current mode (translate/rotate/scale)
-- | - Coordinate space (local/world/view)
-- | - Handle interaction state
-- | - Transform values being edited
-- | - Drag state for interaction
newtype Gizmo = Gizmo
  { -- Mode and space
    mode :: GizmoMode
  , space :: GizmoSpace
  
    -- Handle state
  , active :: GizmoHandle      -- ^ Currently being dragged
  , hovered :: GizmoHandle     -- ^ Mouse is over this handle
  
    -- Transform state (what the gizmo is editing)
  , position :: PixelPoint3D   -- ^ Position in 3D pixel space
  , rotation :: Gimbal         -- ^ Rotation as gimbal (pitch/yaw/roll)
  , scale :: PixelPoint3D      -- ^ Scale factors (x, y, z)
  
    -- Drag state
  , dragging :: Boolean        -- ^ Is a drag in progress?
  , dragStart :: PixelPoint3D  -- ^ Where the drag began
  , dragCurrent :: PixelPoint3D -- ^ Current drag position
  
    -- Visual state
  , visible :: Boolean         -- ^ Is the gizmo visible?
  , size :: Pixel              -- ^ Visual size of the gizmo handles
  }

derive instance eqGizmo :: Eq Gizmo

instance showGizmoInstance :: Show Gizmo where
  show (Gizmo g) =
    "(Gizmo mode:" <> show g.mode
    <> " space:" <> show g.space
    <> " active:" <> show g.active
    <> " pos:" <> show g.position
    <> " rot:" <> show g.rotation
    <> " dragging:" <> show g.dragging
    <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a gizmo with specified mode and position.
gizmo :: GizmoMode -> PixelPoint3D -> Gizmo
gizmo mode pos = Gizmo
  { mode
  , space: SpaceLocal
  , active: HandleNone
  , hovered: HandleNone
  , position: pos
  , rotation: gimbalZero
  , scale: pixelPoint3D (Pixel 1.0) (Pixel 1.0) (Pixel 1.0)
  , dragging: false
  , dragStart: pixelOrigin3D
  , dragCurrent: pixelOrigin3D
  , visible: true
  , size: Pixel 100.0
  }

-- | Create a translate-mode gizmo at the origin.
translateGizmo :: Gizmo
translateGizmo = gizmo GizmoTranslate pixelOrigin3D

-- | Create a rotate-mode gizmo at the origin.
rotateGizmo :: Gizmo
rotateGizmo = gizmo GizmoRotate pixelOrigin3D

-- | Create a scale-mode gizmo at the origin.
scaleGizmo :: Gizmo
scaleGizmo = gizmo GizmoScale pixelOrigin3D

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the current gizmo mode.
gizmoMode :: Gizmo -> GizmoMode
gizmoMode (Gizmo g) = g.mode

-- | Set the gizmo mode.
setGizmoMode :: GizmoMode -> Gizmo -> Gizmo
setGizmoMode mode (Gizmo g) = Gizmo g { mode = mode }

-- | Cycle through gizmo modes: Translate → Rotate → Scale → Translate
cycleGizmoMode :: Gizmo -> Gizmo
cycleGizmoMode (Gizmo g) = Gizmo g { mode = nextMode g.mode }
  where
    nextMode GizmoTranslate = GizmoRotate
    nextMode GizmoRotate = GizmoScale
    nextMode GizmoScale = GizmoTranslate

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // space
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the current coordinate space.
gizmoSpace :: Gizmo -> GizmoSpace
gizmoSpace (Gizmo g) = g.space

-- | Set the coordinate space.
setGizmoSpace :: GizmoSpace -> Gizmo -> Gizmo
setGizmoSpace space (Gizmo g) = Gizmo g { space = space }

-- | Toggle between local and world space.
toggleGizmoSpace :: Gizmo -> Gizmo
toggleGizmoSpace (Gizmo g) = Gizmo g { space = toggled }
  where
    toggled = if g.space == SpaceLocal then SpaceWorld else SpaceLocal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // handle state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the currently active (being dragged) handle.
activeHandle :: Gizmo -> GizmoHandle
activeHandle (Gizmo g) = g.active

-- | Get the currently hovered handle.
hoveredHandle :: Gizmo -> GizmoHandle
hoveredHandle (Gizmo g) = g.hovered

-- | Set the active handle.
setActiveHandle :: GizmoHandle -> Gizmo -> Gizmo
setActiveHandle handle (Gizmo g) = Gizmo g { active = handle }

-- | Set the hovered handle.
setHoveredHandle :: GizmoHandle -> Gizmo -> Gizmo
setHoveredHandle handle (Gizmo g) = Gizmo g { hovered = handle }

-- | Clear the active handle (no handle selected).
clearActiveHandle :: Gizmo -> Gizmo
clearActiveHandle (Gizmo g) = Gizmo g { active = HandleNone }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transform state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the gizmo position.
gizmoPosition :: Gizmo -> PixelPoint3D
gizmoPosition (Gizmo g) = g.position

-- | Get the gizmo rotation.
gizmoRotation :: Gizmo -> Gimbal
gizmoRotation (Gizmo g) = g.rotation

-- | Get the gizmo scale.
gizmoScale :: Gizmo -> PixelPoint3D
gizmoScale (Gizmo g) = g.scale

-- | Set the gizmo position.
setGizmoPosition :: PixelPoint3D -> Gizmo -> Gizmo
setGizmoPosition pos (Gizmo g) = Gizmo g { position = pos }

-- | Set the gizmo rotation.
setGizmoRotation :: Gimbal -> Gizmo -> Gizmo
setGizmoRotation rot (Gizmo g) = Gizmo g { rotation = rot }

-- | Set the gizmo scale.
setGizmoScale :: PixelPoint3D -> Gizmo -> Gizmo
setGizmoScale s (Gizmo g) = Gizmo g { scale = s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // interaction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Begin a drag operation on the active handle.
beginDrag :: PixelPoint3D -> Gizmo -> Gizmo
beginDrag startPos (Gizmo g) = Gizmo g
  { dragging = true
  , dragStart = startPos
  , dragCurrent = startPos
  }

-- | Update the current drag position.
updateDrag :: PixelPoint3D -> Gizmo -> Gizmo
updateDrag currentPos (Gizmo g) = Gizmo g { dragCurrent = currentPos }

-- | End the drag operation.
endDrag :: Gizmo -> Gizmo
endDrag (Gizmo g) = Gizmo g
  { dragging = false
  , active = HandleNone
  }

-- | Check if a drag is in progress.
isDragging :: Gizmo -> Boolean
isDragging (Gizmo g) = g.dragging

-- | Get the delta from drag start to current position.
dragDelta :: Gizmo -> PixelPoint3D
dragDelta (Gizmo g) =
  let
    Pixel sx = g.dragStart.x
    Pixel sy = g.dragStart.y
    Pixel sz = g.dragStart.z
    Pixel cx = g.dragCurrent.x
    Pixel cy = g.dragCurrent.y
    Pixel cz = g.dragCurrent.z
  in
    pixelPoint3D (Pixel (cx - sx)) (Pixel (cy - sy)) (Pixel (cz - sz))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // visibility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if the gizmo is visible.
gizmoVisible :: Gizmo -> Boolean
gizmoVisible (Gizmo g) = g.visible

-- | Set gizmo visibility.
setGizmoVisible :: Boolean -> Gizmo -> Gizmo
setGizmoVisible vis (Gizmo g) = Gizmo g { visible = vis }

-- | Get the visual size of gizmo handles.
gizmoSize :: Gizmo -> Pixel
gizmoSize (Gizmo g) = g.size

-- | Set the visual size of gizmo handles.
setGizmoSize :: Pixel -> Gizmo -> Gizmo
setGizmoSize s (Gizmo g) = Gizmo g { size = s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // debug
-- ═════════════════════════════════════════════════════════════════════════════

-- | Debug string representation.
showGizmo :: Gizmo -> String
showGizmo (Gizmo g) =
  "(Gizmo mode:" <> show g.mode
  <> " space:" <> show g.space
  <> " active:" <> show g.active
  <> " pos:" <> show g.position
  <> " rot:" <> show g.rotation
  <> " dragging:" <> show g.dragging
  <> ")"
