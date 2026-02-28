-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // gpu // scene3d // path
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Path — 3D spline curves with fully-identified control points and handles.
-- |
-- | ## Atomic Design
-- | Every entity has its own identity (UUID5 in production):
-- | - PathId: identifies the path itself
-- | - PointId: identifies each control point
-- | - HandleId: identifies each tangent handle
-- |
-- | Handles are FIRST-CLASS entities, not just Vec3 offsets.
-- | They have selection state, gizmo interaction, constraints.
-- |
-- | ## Composition
-- | Path3D contains ControlPoints contains Handles.
-- | Each level is independently addressable and selectable.

module Hydrogen.GPU.Scene3D.Path
  ( -- * Identifiers
    PathId
  , PointId
  , HandleId
  , pathIdFromName
  , pointIdFromPath
  , handleIdIn
  , handleIdOut
  
  -- * Spline Type
  , SplineType
      ( LinearSpline
      , BezierSpline
      , CatmullRomSpline
      , HermiteSpline
      )
  
  -- * Handle Constraint
  , HandleConstraint
      ( FreeHandle
      , AlignedHandle
      , MirroredHandle
      , AutoHandle
      )
  
  -- * Handle (atomic)
  , Handle
  , handle
  
  -- * Control Point (molecule: point + handles)
  , ControlPoint
  , controlPoint
  
  -- * Path (compound: collection of points)
  , Path3D
  , emptyPath
  
  -- * Path Messages
  , PathMsg
      ( -- Path-level
        SelectPath
      , DeselectPath
      , SetSplineType
      , SetTension
      , ClosePath
      , OpenPath
      , ReversePath
        -- Point-level
      , AddPoint
      , RemovePoint
      , MovePoint
      , SelectPoint
      , DeselectPoint
      , HoverPoint
      , UnhoverPoint
        -- Handle-level
      , MoveHandle
      , SelectHandle
      , DeselectHandle
      , HoverHandle
      , UnhoverHandle
      , SetHandleConstraint
        -- Bulk operations
      , DeselectAll
      )
  
  -- * Update
  , updatePath
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
  , (<>)
  , (/=)
  , (==)
  )

import Data.Array (filter, reverse, snoc) as Array

import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // identifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Path identifier.
-- |
-- | In production: UUID5 from path content hash.
-- | Deterministic: same path content → same PathId.
newtype PathId = PathId String

derive instance eqPathId :: Eq PathId
derive instance ordPathId :: Ord PathId

instance showPathId :: Show PathId where
  show (PathId s) = "PathId(" <> s <> ")"

-- | Control point identifier.
-- |
-- | Namespaced under its parent path.
-- | In production: UUID5 from (pathId, pointIndex, position).
newtype PointId = PointId String

derive instance eqPointId :: Eq PointId
derive instance ordPointId :: Ord PointId

instance showPointId :: Show PointId where
  show (PointId s) = "PointId(" <> s <> ")"

-- | Handle identifier.
-- |
-- | Namespaced under its parent point.
-- | Distinguishes incoming vs outgoing handle.
-- | In production: UUID5 from (pointId, handleType).
newtype HandleId = HandleId String

derive instance eqHandleId :: Eq HandleId
derive instance ordHandleId :: Ord HandleId

instance showHandleId :: Show HandleId where
  show (HandleId s) = "HandleId(" <> s <> ")"

-- | Create PathId from name.
pathIdFromName :: String -> PathId
pathIdFromName name = PathId name

-- | Create PointId from path and index.
pointIdFromPath :: PathId -> Int -> PointId
pointIdFromPath (PathId p) idx = PointId (p <> ":pt:" <> show idx)

-- | Create HandleId for incoming handle.
handleIdIn :: PointId -> HandleId
handleIdIn (PointId p) = HandleId (p <> ":in")

-- | Create HandleId for outgoing handle.
handleIdOut :: PointId -> HandleId
handleIdOut (PointId p) = HandleId (p <> ":out")

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // spline type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Interpolation type between control points.
data SplineType
  = LinearSpline        -- Straight lines (handles ignored)
  | BezierSpline        -- Cubic Bezier (explicit handles)
  | CatmullRomSpline    -- Smooth through points (auto handles)
  | HermiteSpline       -- Velocity vectors at points

derive instance eqSplineType :: Eq SplineType

instance showSplineType :: Show SplineType where
  show LinearSpline = "LinearSpline"
  show BezierSpline = "BezierSpline"
  show CatmullRomSpline = "CatmullRomSpline"
  show HermiteSpline = "HermiteSpline"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // handle constraint
-- ═════════════════════════════════════════════════════════════════════════════

-- | Constraint applied to a handle's movement.
data HandleConstraint
  = FreeHandle          -- Moves independently
  | AlignedHandle       -- Stays collinear with opposite handle
  | MirroredHandle      -- Mirrors opposite handle (same length)
  | AutoHandle          -- Computed automatically, not user-editable

derive instance eqHandleConstraint :: Eq HandleConstraint

instance showHandleConstraint :: Show HandleConstraint where
  show FreeHandle = "FreeHandle"
  show AlignedHandle = "AlignedHandle"
  show MirroredHandle = "MirroredHandle"
  show AutoHandle = "AutoHandle"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // handle
-- ═════════════════════════════════════════════════════════════════════════════

-- | A tangent handle — first-class entity with its own identity.
-- |
-- | Handles define the curve tangent at a control point.
-- | Position is RELATIVE to parent control point.
type Handle =
  { id :: HandleId                    -- Unique identifier
  , offset :: Vec3 Number             -- Position relative to control point
  , constraint :: HandleConstraint    -- Movement constraint
  , selected :: Boolean               -- Is handle selected for editing?
  , hovered :: Boolean                -- Is cursor over this handle?
  , visible :: Boolean                -- Should handle be rendered?
  }

-- | Create a handle with default settings.
handle :: HandleId -> Vec3 Number -> Handle
handle hid offset =
  { id: hid
  , offset: offset
  , constraint: MirroredHandle
  , selected: false
  , hovered: false
  , visible: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // control point
-- ═════════════════════════════════════════════════════════════════════════════

-- | A control point — molecule composed of position + two handles.
-- |
-- | The point itself is selectable/hoverable independent of its handles.
type ControlPoint =
  { id :: PointId                     -- Unique identifier
  , position :: Vec3 Number           -- World position of point
  , handleIn :: Handle                -- Incoming tangent handle
  , handleOut :: Handle               -- Outgoing tangent handle
  , selected :: Boolean               -- Is point selected?
  , hovered :: Boolean                -- Is cursor over point?
  }

-- | Create a control point with zero handles.
controlPoint :: PointId -> Vec3 Number -> ControlPoint
controlPoint pid pos =
  { id: pid
  , position: pos
  , handleIn: handle (handleIdIn pid) (vec3 0.0 0.0 0.0)
  , handleOut: handle (handleIdOut pid) (vec3 0.0 0.0 0.0)
  , selected: false
  , hovered: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // path
-- ═════════════════════════════════════════════════════════════════════════════

-- | A 3D path — compound composed of ordered control points.
-- |
-- | The path itself has identity, selection state, and configuration.
type Path3D =
  { id :: PathId                      -- Unique identifier
  , name :: String                    -- Human-readable label
  , splineType :: SplineType          -- Interpolation method
  , points :: Array ControlPoint      -- Ordered control points
  , closed :: Boolean                 -- Is path a closed loop?
  , selected :: Boolean               -- Is path selected?
  , visible :: Boolean                -- Should path be rendered?
  , tension :: Number                 -- Catmull-Rom tension (0.0-1.0)
  }

-- | Create an empty path.
emptyPath :: PathId -> String -> Path3D
emptyPath pid name =
  { id: pid
  , name: name
  , splineType: BezierSpline
  , points: []
  , closed: false
  , selected: false
  , visible: true
  , tension: 0.5
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // path msg
-- ═════════════════════════════════════════════════════════════════════════════

-- | Messages for editing paths at any level of the hierarchy.
-- |
-- | Each entity (path, point, handle) has targeted messages.
-- | The message carries the entity's ID so the update knows what to modify.
data PathMsg
  -- Path-level operations
  = SelectPath
  | DeselectPath
  | SetSplineType SplineType
  | SetTension Number
  | ClosePath
  | OpenPath
  | ReversePath
  -- Point-level operations (by PointId)
  | AddPoint ControlPoint             -- Add a new point
  | RemovePoint PointId               -- Remove point by ID
  | MovePoint PointId (Vec3 Number)   -- Move point to position
  | SelectPoint PointId
  | DeselectPoint PointId
  | HoverPoint PointId
  | UnhoverPoint PointId
  -- Handle-level operations (by HandleId)
  | MoveHandle HandleId (Vec3 Number) -- Move handle to offset
  | SelectHandle HandleId
  | DeselectHandle HandleId
  | HoverHandle HandleId
  | UnhoverHandle HandleId
  | SetHandleConstraint HandleId HandleConstraint
  -- Bulk operations
  | DeselectAll                       -- Clear all selection

derive instance eqPathMsg :: Eq PathMsg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // update
-- ═════════════════════════════════════════════════════════════════════════════

-- | Update path state from a message.
-- |
-- | Pure function — routes to point/handle updates as needed.
updatePath :: PathMsg -> Path3D -> Path3D
updatePath msg path = case msg of
  
  -- Path-level
  SelectPath -> path { selected = true }
  DeselectPath -> path { selected = false }
  SetSplineType st -> path { splineType = st }
  SetTension t -> path { tension = t }
  ClosePath -> path { closed = true }
  OpenPath -> path { closed = false }
  ReversePath -> path { points = reverseArray path.points }
  
  -- Point-level
  AddPoint pt -> path { points = snoc path.points pt }
  RemovePoint pid -> path { points = filterPoints (\p -> p.id /= pid) path.points }
  MovePoint pid pos -> path { points = mapPoints (updatePointPos pid pos) path.points }
  SelectPoint pid -> path { points = mapPoints (setPointSelected pid true) path.points }
  DeselectPoint pid -> path { points = mapPoints (setPointSelected pid false) path.points }
  HoverPoint pid -> path { points = mapPoints (setPointHovered pid true) path.points }
  UnhoverPoint pid -> path { points = mapPoints (setPointHovered pid false) path.points }
  
  -- Handle-level
  MoveHandle hid offset -> path { points = mapPoints (updateHandleOffset hid offset) path.points }
  SelectHandle hid -> path { points = mapPoints (setHandleSelected hid true) path.points }
  DeselectHandle hid -> path { points = mapPoints (setHandleSelected hid false) path.points }
  HoverHandle hid -> path { points = mapPoints (setHandleHovered hid true) path.points }
  UnhoverHandle hid -> path { points = mapPoints (setHandleHovered hid false) path.points }
  SetHandleConstraint hid c -> path { points = mapPoints (setHandleConstraintById hid c) path.points }
  
  -- Bulk
  DeselectAll -> path 
    { selected = false
    , points = mapPoints deselectPointAndHandles path.points
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map over points array.
mapPoints :: (ControlPoint -> ControlPoint) -> Array ControlPoint -> Array ControlPoint
mapPoints = map

-- | Filter points array.
filterPoints :: (ControlPoint -> Boolean) -> Array ControlPoint -> Array ControlPoint
filterPoints = Array.filter

-- | Append to array.
snoc :: forall a. Array a -> a -> Array a
snoc = Array.snoc

-- | Reverse array.
reverseArray :: forall a. Array a -> Array a
reverseArray = Array.reverse

-- | Update point position if ID matches.
updatePointPos :: PointId -> Vec3 Number -> ControlPoint -> ControlPoint
updatePointPos pid pos pt = if pt.id == pid then pt { position = pos } else pt

-- | Set point selected state if ID matches.
setPointSelected :: PointId -> Boolean -> ControlPoint -> ControlPoint
setPointSelected pid sel pt = if pt.id == pid then pt { selected = sel } else pt

-- | Set point hovered state if ID matches.
setPointHovered :: PointId -> Boolean -> ControlPoint -> ControlPoint
setPointHovered pid hov pt = if pt.id == pid then pt { hovered = hov } else pt

-- | Update handle offset by HandleId.
updateHandleOffset :: HandleId -> Vec3 Number -> ControlPoint -> ControlPoint
updateHandleOffset hid offset pt =
  if pt.handleIn.id == hid then pt { handleIn = pt.handleIn { offset = offset } }
  else if pt.handleOut.id == hid then pt { handleOut = pt.handleOut { offset = offset } }
  else pt

-- | Set handle selected state by HandleId.
setHandleSelected :: HandleId -> Boolean -> ControlPoint -> ControlPoint
setHandleSelected hid sel pt =
  if pt.handleIn.id == hid then pt { handleIn = pt.handleIn { selected = sel } }
  else if pt.handleOut.id == hid then pt { handleOut = pt.handleOut { selected = sel } }
  else pt

-- | Set handle hovered state by HandleId.
setHandleHovered :: HandleId -> Boolean -> ControlPoint -> ControlPoint
setHandleHovered hid hov pt =
  if pt.handleIn.id == hid then pt { handleIn = pt.handleIn { hovered = hov } }
  else if pt.handleOut.id == hid then pt { handleOut = pt.handleOut { hovered = hov } }
  else pt

-- | Set handle constraint by HandleId.
setHandleConstraintById :: HandleId -> HandleConstraint -> ControlPoint -> ControlPoint
setHandleConstraintById hid c pt =
  if pt.handleIn.id == hid then pt { handleIn = pt.handleIn { constraint = c } }
  else if pt.handleOut.id == hid then pt { handleOut = pt.handleOut { constraint = c } }
  else pt

-- | Deselect a point and both its handles.
deselectPointAndHandles :: ControlPoint -> ControlPoint
deselectPointAndHandles pt = pt
  { selected = false
  , hovered = false
  , handleIn = pt.handleIn { selected = false, hovered = false }
  , handleOut = pt.handleOut { selected = false, hovered = false }
  }
