-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // reactive // drag-state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DragState - drag and drop interaction atoms.
-- |
-- | Models the complete drag lifecycle including source, target,
-- | preview, and drop effects for Frame.io-level file upload UX.

module Hydrogen.Schema.Reactive.DragState
  ( -- * Drag Status
    DragStatus(..)
  , isDragIdle
  , isDragging
  , isDraggedOver
  , isDropping
  -- * Drop Effect
  , DropEffect(..)
  , isCopy
  , isMove
  , isLink
  , isDropNone
  -- * Drag Type
  , DragType(..)
  , isFileDrag
  , isElementDrag
  , isTextDrag
  , isExternalDrag
  -- * Drag Position
  , DragPosition
  , dragPosition
  , originPosition
  , currentPosition
  , deltaX
  , deltaY
  , totalDistance
  -- * Drag Source (Molecule)
  , DragSource
  , dragSource
  , noDragSource
  , isDragSourceActive
  , dragSourceId
  , dragSourceData
  -- * Drop Target (Molecule)
  , DropTarget
  , dropTarget
  , noDropTarget
  , isValidTarget
  , isTargetActive
  , dropTargetId
  , acceptedTypes
  -- * Drag Preview
  , DragPreview
  , dragPreview
  , defaultPreview
  , customPreview
  , ghostPreview
  , previewOffset
  -- * Drop Zone Feedback
  , DropZoneFeedback(..)
  , isAccepting
  , isRejecting
  , isNeutral
  -- * Drag State (Compound)
  , DragState
  , dragState
  , idleDragState
  , activeDragState
  -- * State Transitions
  , startDrag
  , updateDragPosition
  , enterDropZone
  , leaveDropZone
  , drop
  , cancelDrag
  -- * Computed Properties
  , isDragActive
  , hasValidDropTarget
  , shouldShowPreview
  , previewPosition
  ) where

import Prelude

import Data.Array (elem)
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Math.Core (sqrt)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // drag status
-- ═════════════════════════════════════════════════════════════════════════════

-- | Current drag operation status
data DragStatus
  = DragIdle        -- ^ No drag in progress
  | Dragging        -- ^ Item is being dragged
  | DraggedOver     -- ^ Drag is over a valid target
  | Dropping        -- ^ Drop is in progress

derive instance eqDragStatus :: Eq DragStatus
derive instance ordDragStatus :: Ord DragStatus

instance showDragStatus :: Show DragStatus where
  show DragIdle = "idle"
  show Dragging = "dragging"
  show DraggedOver = "dragged-over"
  show Dropping = "dropping"

isDragIdle :: DragStatus -> Boolean
isDragIdle DragIdle = true
isDragIdle _ = false

isDragging :: DragStatus -> Boolean
isDragging Dragging = true
isDragging _ = false

isDraggedOver :: DragStatus -> Boolean
isDraggedOver DraggedOver = true
isDraggedOver _ = false

isDropping :: DragStatus -> Boolean
isDropping Dropping = true
isDropping _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // drop effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | DataTransfer.dropEffect values
data DropEffect
  = DropCopy   -- ^ Copy data
  | DropMove   -- ^ Move data
  | DropLink   -- ^ Create link
  | DropNone   -- ^ No drop allowed

derive instance eqDropEffect :: Eq DropEffect
derive instance ordDropEffect :: Ord DropEffect

instance showDropEffect :: Show DropEffect where
  show DropCopy = "copy"
  show DropMove = "move"
  show DropLink = "link"
  show DropNone = "none"

isCopy :: DropEffect -> Boolean
isCopy DropCopy = true
isCopy _ = false

isMove :: DropEffect -> Boolean
isMove DropMove = true
isMove _ = false

isLink :: DropEffect -> Boolean
isLink DropLink = true
isLink _ = false

isDropNone :: DropEffect -> Boolean
isDropNone DropNone = true
isDropNone _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // drag type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of content being dragged
data DragType
  = FileDrag      -- ^ File(s) from filesystem
  | ElementDrag   -- ^ DOM element within page
  | TextDrag      -- ^ Text selection
  | ExternalDrag  -- ^ Content from another application

derive instance eqDragType :: Eq DragType
derive instance ordDragType :: Ord DragType

instance showDragType :: Show DragType where
  show FileDrag = "file"
  show ElementDrag = "element"
  show TextDrag = "text"
  show ExternalDrag = "external"

isFileDrag :: DragType -> Boolean
isFileDrag FileDrag = true
isFileDrag _ = false

isElementDrag :: DragType -> Boolean
isElementDrag ElementDrag = true
isElementDrag _ = false

isTextDrag :: DragType -> Boolean
isTextDrag TextDrag = true
isTextDrag _ = false

isExternalDrag :: DragType -> Boolean
isExternalDrag ExternalDrag = true
isExternalDrag _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // drag position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Position tracking during drag
type DragPosition =
  { originX :: Number      -- ^ Starting X position
  , originY :: Number      -- ^ Starting Y position
  , currentX :: Number     -- ^ Current X position
  , currentY :: Number     -- ^ Current Y position
  }

-- | Create drag position
dragPosition :: Number -> Number -> Number -> Number -> DragPosition
dragPosition ox oy cx cy =
  { originX: ox
  , originY: oy
  , currentX: cx
  , currentY: cy
  }

-- | Get origin position
originPosition :: DragPosition -> { x :: Number, y :: Number }
originPosition p = { x: p.originX, y: p.originY }

-- | Get current position
currentPosition :: DragPosition -> { x :: Number, y :: Number }
currentPosition p = { x: p.currentX, y: p.currentY }

-- | Get horizontal delta
deltaX :: DragPosition -> Number
deltaX p = p.currentX - p.originX

-- | Get vertical delta
deltaY :: DragPosition -> Number
deltaY p = p.currentY - p.originY

-- | Get total distance traveled
totalDistance :: DragPosition -> Number
totalDistance p = sqrt (deltaX p * deltaX p + deltaY p * deltaY p)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // drag source molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Source element being dragged
type DragSource =
  { id :: Maybe String           -- ^ Source element ID
  , dragType :: DragType         -- ^ Type of drag
  , data :: Maybe String         -- ^ Serialized drag data
  , allowedEffects :: Array DropEffect
  , active :: Boolean
  }

-- | Create drag source
dragSource :: String -> DragType -> Maybe String -> Array DropEffect -> DragSource
dragSource id dragType sourceData effects =
  { id: Just id
  , dragType
  , data: sourceData
  , allowedEffects: effects
  , active: true
  }

-- | No active drag source
noDragSource :: DragSource
noDragSource =
  { id: Nothing
  , dragType: ElementDrag
  , data: Nothing
  , allowedEffects: []
  , active: false
  }

-- | Is drag source currently active?
isDragSourceActive :: DragSource -> Boolean
isDragSourceActive ds = ds.active

-- | Get drag source ID
dragSourceId :: DragSource -> Maybe String
dragSourceId ds = ds.id

-- | Get drag source data
dragSourceData :: DragSource -> Maybe String
dragSourceData ds = ds.data

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // drop target molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drop target configuration
type DropTarget =
  { id :: Maybe String           -- ^ Target element ID
  , accepts :: Array DragType    -- ^ Accepted drag types
  , effect :: DropEffect         -- ^ Effect to apply on drop
  , active :: Boolean            -- ^ Currently being dragged over
  , valid :: Boolean             -- ^ Can accept current drag
  }

-- | Create drop target
dropTarget :: String -> Array DragType -> DropEffect -> DropTarget
dropTarget id accepts effect =
  { id: Just id
  , accepts
  , effect
  , active: false
  , valid: false
  }

-- | No active drop target
noDropTarget :: DropTarget
noDropTarget =
  { id: Nothing
  , accepts: []
  , effect: DropNone
  , active: false
  , valid: false
  }

-- | Can target accept the drag type?
isValidTarget :: DragType -> DropTarget -> Boolean
isValidTarget dragType target = elem dragType target.accepts

-- | Is target currently active?
isTargetActive :: DropTarget -> Boolean
isTargetActive target = target.active

-- | Get drop target ID
dropTargetId :: DropTarget -> Maybe String
dropTargetId target = target.id

-- | Get accepted types
acceptedTypes :: DropTarget -> Array DragType
acceptedTypes target = target.accepts

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // drag preview
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drag preview configuration
type DragPreview =
  { useDefault :: Boolean        -- ^ Use browser default preview
  , customElement :: Maybe String -- ^ Custom preview element ID
  , offsetX :: Number            -- ^ Offset from cursor X
  , offsetY :: Number            -- ^ Offset from cursor Y
  , opacity :: Number            -- ^ Preview opacity (0-1)
  , scale :: Number              -- ^ Preview scale
  }

-- | Create drag preview
dragPreview :: Boolean -> Maybe String -> Number -> Number -> DragPreview
dragPreview useDefault customElement offsetX offsetY =
  { useDefault
  , customElement
  , offsetX
  , offsetY
  , opacity: 0.7
  , scale: 1.0
  }

-- | Default browser preview
defaultPreview :: DragPreview
defaultPreview = dragPreview true Nothing 0.0 0.0

-- | Custom element preview
customPreview :: String -> Number -> Number -> DragPreview
customPreview elementId offsetX offsetY = dragPreview false (Just elementId) offsetX offsetY

-- | Ghost preview (semi-transparent copy)
ghostPreview :: DragPreview
ghostPreview = defaultPreview { opacity = 0.5 }

-- | Get preview offset
previewOffset :: DragPreview -> { x :: Number, y :: Number }
previewOffset p = { x: p.offsetX, y: p.offsetY }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // drop zone feedback
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual feedback for drop zone
data DropZoneFeedback
  = DropZoneAccepting   -- ^ Zone will accept drop
  | DropZoneRejecting   -- ^ Zone will reject drop
  | DropZoneNeutral     -- ^ No feedback (not hovering)

derive instance eqDropZoneFeedback :: Eq DropZoneFeedback
derive instance ordDropZoneFeedback :: Ord DropZoneFeedback

instance showDropZoneFeedback :: Show DropZoneFeedback where
  show DropZoneAccepting = "accepting"
  show DropZoneRejecting = "rejecting"
  show DropZoneNeutral = "neutral"

isAccepting :: DropZoneFeedback -> Boolean
isAccepting DropZoneAccepting = true
isAccepting _ = false

isRejecting :: DropZoneFeedback -> Boolean
isRejecting DropZoneRejecting = true
isRejecting _ = false

isNeutral :: DropZoneFeedback -> Boolean
isNeutral DropZoneNeutral = true
isNeutral _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // drag state compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete drag and drop state
type DragState =
  { status :: DragStatus
  , source :: DragSource
  , target :: DropTarget
  , position :: Maybe DragPosition
  , preview :: DragPreview
  , feedback :: DropZoneFeedback
  }

-- | Create drag state
dragState :: DragStatus -> DragSource -> DropTarget -> DragState
dragState status source target =
  { status
  , source
  , target
  , position: Nothing
  , preview: defaultPreview
  , feedback: DropZoneNeutral
  }

-- | Idle drag state (no drag in progress)
idleDragState :: DragState
idleDragState = dragState DragIdle noDragSource noDropTarget

-- | Create active drag state
activeDragState :: DragSource -> DragPosition -> DragState
activeDragState source pos = (dragState Dragging source noDropTarget)
  { position = Just pos }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // state transitions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Start a drag operation
startDrag :: DragSource -> Number -> Number -> DragState -> DragState
startDrag source x y _ =
  { status: Dragging
  , source: source { active = true }
  , target: noDropTarget
  , position: Just (dragPosition x y x y)
  , preview: defaultPreview
  , feedback: DropZoneNeutral
  }

-- | Update drag position
updateDragPosition :: Number -> Number -> DragState -> DragState
updateDragPosition x y ds = case ds.position of
  Nothing -> ds
  Just pos -> ds { position = Just (pos { currentX = x, currentY = y }) }

-- | Enter a drop zone
enterDropZone :: DropTarget -> DragState -> DragState
enterDropZone target ds =
  let valid = isValidTarget ds.source.dragType target
      feedback = if valid then DropZoneAccepting else DropZoneRejecting
  in ds
    { status = DraggedOver
    , target = target { active = true, valid = valid }
    , feedback = feedback
    }

-- | Leave a drop zone
leaveDropZone :: DragState -> DragState
leaveDropZone ds = ds
  { status = Dragging
  , target = noDropTarget
  , feedback = DropZoneNeutral
  }

-- | Execute drop
drop :: DragState -> DragState
drop ds = ds
  { status = Dropping
  , target = ds.target { active = false }
  }

-- | Cancel drag operation
cancelDrag :: DragState -> DragState
cancelDrag _ = idleDragState

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // computed properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is a drag operation active?
isDragActive :: DragState -> Boolean
isDragActive ds = not (isDragIdle ds.status)

-- | Is there a valid drop target?
hasValidDropTarget :: DragState -> Boolean
hasValidDropTarget ds = ds.target.valid

-- | Should show drag preview?
shouldShowPreview :: DragState -> Boolean
shouldShowPreview ds = isDragging ds.status || isDraggedOver ds.status

-- | Get preview position
previewPosition :: DragState -> Maybe { x :: Number, y :: Number }
previewPosition ds = case ds.position of
  Nothing -> Nothing
  Just pos -> Just 
    { x: pos.currentX + ds.preview.offsetX
    , y: pos.currentY + ds.preview.offsetY
    }
