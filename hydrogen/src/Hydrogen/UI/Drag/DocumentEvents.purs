-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // ui // drag // document-events
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Document-Level Drag Event Handling
-- |
-- | Provides utilities for handling mouse drag operations that need to
-- | continue even when the mouse leaves the originating element. This is
-- | essential for professional drag interactions in curve editors,
-- | scrubable inputs, and other precision controls.
-- |
-- | ## Problem
-- |
-- | Element-level mouse events stop firing when the cursor leaves the element.
-- | This causes drag operations to "stick" or behave erratically when users
-- | drag quickly or outside the element bounds.
-- |
-- | ## Solution
-- |
-- | Attach mousemove and mouseup listeners to the document during drag,
-- | then remove them when the drag ends. This captures all mouse movement
-- | regardless of cursor position.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.UI.Drag.DocumentEvents as Drag
-- |
-- | -- In handleAction:
-- | HandleMouseDown event -> do
-- |   Drag.startDrag
-- |     { onMove: \x y -> HandleDragMove x y
-- |     , onEnd: HandleDragEnd
-- |     }
-- | ```
module Hydrogen.UI.Drag.DocumentEvents
  ( -- * Types
    DragCallbacks
  , DragState
  , DragHandle
  
  -- * Operations
  , startDrag
  , stopDrag
  
  -- * Accessors
  , getClientX
  , getClientY
  , getMovementX
  , getMovementY
  ) where

import Prelude

import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Callbacks invoked during drag operations
type DragCallbacks =
  { onMove :: Number -> Number -> Effect Unit   -- clientX, clientY
  , onEnd :: Effect Unit                         -- drag ended
  }

-- | Internal drag state
type DragState =
  { isActive :: Boolean
  , startX :: Number
  , startY :: Number
  , currentX :: Number
  , currentY :: Number
  }

-- | Handle returned by startDrag, used to stop the drag
foreign import data DragHandle :: Type

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // ffi
-- ═════════════════════════════════════════════════════════════════════════════

-- | Start listening for document-level mouse events
-- | Returns a handle that must be used to stop the drag
foreign import startDragImpl :: 
  (Number -> Number -> Effect Unit) ->  -- onMove callback
  Effect Unit ->                         -- onEnd callback
  Effect DragHandle

-- | Stop listening for document-level mouse events
foreign import stopDragImpl :: DragHandle -> Effect Unit

-- | Get clientX from the last mouse event
foreign import getClientXImpl :: DragHandle -> Effect Number

-- | Get clientY from the last mouse event
foreign import getClientYImpl :: DragHandle -> Effect Number

-- | Get movementX from the last mouse event (delta since last event)
foreign import getMovementXImpl :: DragHandle -> Effect Number

-- | Get movementY from the last mouse event (delta since last event)
foreign import getMovementYImpl :: DragHandle -> Effect Number

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Start a document-level drag operation
-- |
-- | Attaches mousemove and mouseup listeners to the document.
-- | Returns a DragHandle that must be passed to stopDrag when done.
startDrag :: DragCallbacks -> Effect DragHandle
startDrag callbacks = startDragImpl callbacks.onMove callbacks.onEnd

-- | Stop a document-level drag operation
-- |
-- | Removes the document-level listeners. Should be called in onEnd
-- | callback or when component unmounts.
stopDrag :: DragHandle -> Effect Unit
stopDrag = stopDragImpl

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the current clientX position
getClientX :: DragHandle -> Effect Number
getClientX = getClientXImpl

-- | Get the current clientY position
getClientY :: DragHandle -> Effect Number
getClientY = getClientYImpl

-- | Get the X movement since the last event
getMovementX :: DragHandle -> Effect Number
getMovementX = getMovementXImpl

-- | Get the Y movement since the last event
getMovementY :: DragHandle -> Effect Number
getMovementY = getMovementYImpl
