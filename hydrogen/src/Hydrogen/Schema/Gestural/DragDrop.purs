-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // gestural // drag-drop
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DragDrop - drag and drop interaction patterns.
-- |
-- | Models the complete drag-and-drop lifecycle per HTML5 Drag and Drop API.
-- | Supports drag sources, drop targets, transfer data, and visual feedback.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Data.Maybe (Maybe)
-- | - Gestural.Pointer (PointerPosition)
-- |
-- | ## Dependents
-- | - Component.Sortable (reorderable lists)
-- | - Component.Timeline (timeline editing)
-- | - Component.FileUpload (file drop zones)

module Hydrogen.Schema.Gestural.DragDrop
  ( -- * Drag Phase
    DragPhase(DragIdle, DragPending, DragActive, DragOver, DragComplete, DragCancelled)
  , isDragIdle
  , isDragActive
  , isDragOver
  , isDragComplete
  , isDragCancelled
    -- * Drop Effect
  , DropEffect(DropNone, DropCopy, DropMove, DropLink)
  , dropEffectFromString
  , dropEffectToString
  , allowsEffect
    -- * Drag Source
  , DragSource
  , dragSource
  , sourceId
  , sourceData
  , sourceEffects
  , sourcePreview
    -- * Drop Target
  , DropTarget
  , dropTarget
  , targetId
  , targetAccepts
  , targetEffect
  , isValidTarget
    -- * Drag Preview
  , DragPreview(PreviewElement, PreviewGhost, PreviewCustom, PreviewNone)
  , hasPreview
    -- * Transfer Data
  , TransferData
  , emptyTransfer
  , setTransferText
  , setTransferHtml
  , setTransferJson
  , setTransferFiles
  , getTransferText
  , getTransferHtml
  , getTransferJson
  , hasTransferType
    -- * Drag Offset
  , DragOffset
  , dragOffset
  , offsetFromPointer
  , applyOffset
    -- * Drag State
  , DragState
  , initialDragState
  , startDrag
  , updateDragPosition
  , enterTarget
  , leaveTarget
  , completeDrag
  , cancelDrag
  , currentPhase
  , currentPosition
  , currentTarget
  , dragDelta
  , dragDistance
  ) where

import Prelude

import Data.Array (elem)
import Data.Maybe (Maybe(Just, Nothing), isJust)
import Hydrogen.Math.Core (sqrt)
import Hydrogen.Schema.Gestural.Pointer (PointerPosition, clientX, clientY)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // drag // phase
-- ═════════════════════════════════════════════════════════════════════════════

-- | Phase of the drag operation
data DragPhase
  = DragIdle       -- ^ No drag in progress
  | DragPending    -- ^ Pointer down, waiting for threshold
  | DragActive     -- ^ Drag in progress
  | DragOver       -- ^ Over a valid drop target
  | DragComplete   -- ^ Successfully dropped
  | DragCancelled  -- ^ Drag was cancelled

derive instance eqDragPhase :: Eq DragPhase
derive instance ordDragPhase :: Ord DragPhase

instance showDragPhase :: Show DragPhase where
  show DragIdle = "idle"
  show DragPending = "pending"
  show DragActive = "active"
  show DragOver = "over"
  show DragComplete = "complete"
  show DragCancelled = "cancelled"

-- | Is drag idle?
isDragIdle :: DragPhase -> Boolean
isDragIdle DragIdle = true
isDragIdle _ = false

-- | Is drag active (including over target)?
isDragActive :: DragPhase -> Boolean
isDragActive DragActive = true
isDragActive DragOver = true
isDragActive _ = false

-- | Is over a drop target?
isDragOver :: DragPhase -> Boolean
isDragOver DragOver = true
isDragOver _ = false

-- | Did drag complete successfully?
isDragComplete :: DragPhase -> Boolean
isDragComplete DragComplete = true
isDragComplete _ = false

-- | Was drag cancelled?
isDragCancelled :: DragPhase -> Boolean
isDragCancelled DragCancelled = true
isDragCancelled _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // drop // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect of the drop operation
data DropEffect
  = DropNone    -- ^ Drop not allowed
  | DropCopy    -- ^ Copy data to target
  | DropMove    -- ^ Move data to target
  | DropLink    -- ^ Create link to data

derive instance eqDropEffect :: Eq DropEffect
derive instance ordDropEffect :: Ord DropEffect

instance showDropEffect :: Show DropEffect where
  show DropNone = "none"
  show DropCopy = "copy"
  show DropMove = "move"
  show DropLink = "link"

-- | Parse drop effect from string
dropEffectFromString :: String -> DropEffect
dropEffectFromString "copy" = DropCopy
dropEffectFromString "move" = DropMove
dropEffectFromString "link" = DropLink
dropEffectFromString _ = DropNone

-- | Convert drop effect to string
dropEffectToString :: DropEffect -> String
dropEffectToString = show

-- | Check if effect is allowed by list
allowsEffect :: Array DropEffect -> DropEffect -> Boolean
allowsEffect allowed effect = elem effect allowed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // drag // source
-- ═════════════════════════════════════════════════════════════════════════════

-- | Source element being dragged
type DragSource =
  { id :: String                    -- ^ Unique identifier
  , dataType :: String              -- ^ Type of data (e.g., "item", "file")
  , data :: TransferData            -- ^ Data being transferred
  , allowedEffects :: Array DropEffect  -- ^ Allowed drop effects
  , preview :: DragPreview          -- ^ Visual preview type
  }

-- | Create drag source
dragSource :: String -> String -> TransferData -> Array DropEffect -> DragSource
dragSource id dataType transferData allowedEffects =
  { id
  , dataType
  , data: transferData
  , allowedEffects
  , preview: PreviewGhost
  }

-- | Get source ID
sourceId :: DragSource -> String
sourceId ds = ds.id

-- | Get source data
sourceData :: DragSource -> TransferData
sourceData ds = ds.data

-- | Get allowed effects
sourceEffects :: DragSource -> Array DropEffect
sourceEffects ds = ds.allowedEffects

-- | Get preview type
sourcePreview :: DragSource -> DragPreview
sourcePreview ds = ds.preview

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // drop // target
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drop target element
type DropTarget =
  { id :: String                   -- ^ Unique identifier
  , acceptTypes :: Array String    -- ^ Accepted data types
  , dropEffect :: DropEffect       -- ^ Effect when dropped here
  }

-- | Create drop target
dropTarget :: String -> Array String -> DropEffect -> DropTarget
dropTarget id acceptTypes dropEffect = { id, acceptTypes, dropEffect }

-- | Get target ID
targetId :: DropTarget -> String
targetId dt = dt.id

-- | Get accepted types
targetAccepts :: DropTarget -> Array String
targetAccepts dt = dt.acceptTypes

-- | Get drop effect
targetEffect :: DropTarget -> DropEffect
targetEffect dt = dt.dropEffect

-- | Check if target accepts source
isValidTarget :: DropTarget -> DragSource -> Boolean
isValidTarget target source =
  elem source.dataType target.acceptTypes
  && allowsEffect source.allowedEffects target.dropEffect

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // drag // preview
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of drag preview
data DragPreview
  = PreviewElement   -- ^ Clone of dragged element
  | PreviewGhost     -- ^ Semi-transparent ghost
  | PreviewCustom    -- ^ Custom preview element
  | PreviewNone      -- ^ No preview (cursor only)

derive instance eqDragPreview :: Eq DragPreview

instance showDragPreview :: Show DragPreview where
  show PreviewElement = "element"
  show PreviewGhost = "ghost"
  show PreviewCustom = "custom"
  show PreviewNone = "none"

-- | Does preview have visual?
hasPreview :: DragPreview -> Boolean
hasPreview PreviewNone = false
hasPreview _ = true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // transfer // data
-- ═════════════════════════════════════════════════════════════════════════════

-- | Data being transferred during drag
type TransferData =
  { text :: Maybe String       -- ^ Plain text
  , html :: Maybe String       -- ^ HTML content
  , json :: Maybe String       -- ^ JSON data
  , files :: Array String      -- ^ File references
  , custom :: Array { key :: String, value :: String }  -- ^ Custom MIME types
  }

-- | Empty transfer data
emptyTransfer :: TransferData
emptyTransfer =
  { text: Nothing
  , html: Nothing
  , json: Nothing
  , files: []
  , custom: []
  }

-- | Set plain text data
setTransferText :: String -> TransferData -> TransferData
setTransferText t td = td { text = Just t }

-- | Set HTML data
setTransferHtml :: String -> TransferData -> TransferData
setTransferHtml h td = td { html = Just h }

-- | Set JSON data
setTransferJson :: String -> TransferData -> TransferData
setTransferJson j td = td { json = Just j }

-- | Set file references
setTransferFiles :: Array String -> TransferData -> TransferData
setTransferFiles f td = td { files = f }

-- | Get plain text
getTransferText :: TransferData -> Maybe String
getTransferText td = td.text

-- | Get HTML
getTransferHtml :: TransferData -> Maybe String
getTransferHtml td = td.html

-- | Get JSON
getTransferJson :: TransferData -> Maybe String
getTransferJson td = td.json

-- | Check if transfer has type
hasTransferType :: String -> TransferData -> Boolean
hasTransferType "text/plain" td = isJust td.text
hasTransferType "text/html" td = isJust td.html
hasTransferType "application/json" td = isJust td.json
hasTransferType _ _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // drag // offset
-- ═════════════════════════════════════════════════════════════════════════════

-- | Offset from pointer to drag preview origin
type DragOffset =
  { x :: Number    -- ^ Horizontal offset
  , y :: Number    -- ^ Vertical offset
  }

-- | Create drag offset
dragOffset :: Number -> Number -> DragOffset
dragOffset x y = { x, y }

-- | Calculate offset from pointer to element origin
offsetFromPointer :: PointerPosition -> Number -> Number -> DragOffset
offsetFromPointer pos elementX elementY =
  { x: clientX pos - elementX
  , y: clientY pos - elementY
  }

-- | Apply offset to position
applyOffset :: DragOffset -> PointerPosition -> { x :: Number, y :: Number }
applyOffset offset pos =
  { x: clientX pos - offset.x
  , y: clientY pos - offset.y
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // drag // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete drag and drop state
type DragState =
  { phase :: DragPhase                  -- ^ Current phase
  , source :: Maybe DragSource          -- ^ Item being dragged
  , target :: Maybe DropTarget          -- ^ Current drop target
  , startPosition :: Maybe PointerPosition  -- ^ Where drag started
  , currentPosition :: Maybe PointerPosition  -- ^ Current pointer position
  , offset :: DragOffset                -- ^ Offset from pointer to preview
  , timestamp :: Number                 -- ^ Last update timestamp
  }

-- | Initial drag state
initialDragState :: DragState
initialDragState =
  { phase: DragIdle
  , source: Nothing
  , target: Nothing
  , startPosition: Nothing
  , currentPosition: Nothing
  , offset: dragOffset 0.0 0.0
  , timestamp: 0.0
  }

-- | Start a drag operation
startDrag :: DragSource -> PointerPosition -> DragOffset -> Number -> DragState -> DragState
startDrag source pos offset ts _ =
  { phase: DragActive
  , source: Just source
  , target: Nothing
  , startPosition: Just pos
  , currentPosition: Just pos
  , offset
  , timestamp: ts
  }

-- | Update drag position
updateDragPosition :: PointerPosition -> Number -> DragState -> DragState
updateDragPosition pos ts ds =
  ds { currentPosition = Just pos, timestamp = ts }

-- | Enter a drop target
enterTarget :: DropTarget -> DragState -> DragState
enterTarget target ds = case ds.source of
  Just src | isValidTarget target src ->
    ds { phase = DragOver, target = Just target }
  _ -> ds

-- | Leave current drop target
leaveTarget :: DragState -> DragState
leaveTarget ds =
  ds { phase = DragActive, target = Nothing }

-- | Complete the drag (drop)
completeDrag :: Number -> DragState -> DragState
completeDrag ts ds =
  ds { phase = DragComplete, timestamp = ts }

-- | Cancel the drag
cancelDrag :: Number -> DragState -> DragState
cancelDrag ts ds =
  ds { phase = DragCancelled, target = Nothing, timestamp = ts }

-- | Get current phase
currentPhase :: DragState -> DragPhase
currentPhase ds = ds.phase

-- | Get current position
currentPosition :: DragState -> Maybe PointerPosition
currentPosition ds = ds.currentPosition

-- | Get current target
currentTarget :: DragState -> Maybe DropTarget
currentTarget ds = ds.target

-- | Calculate drag delta from start
dragDelta :: DragState -> { x :: Number, y :: Number }
dragDelta ds = case ds.startPosition, ds.currentPosition of
  Just start, Just current ->
    { x: clientX current - clientX start
    , y: clientY current - clientY start
    }
  _, _ -> { x: 0.0, y: 0.0 }

-- | Calculate drag distance
dragDistance :: DragState -> Number
dragDistance ds =
  let delta = dragDelta ds
  in sqrt (delta.x * delta.x + delta.y * delta.y)
