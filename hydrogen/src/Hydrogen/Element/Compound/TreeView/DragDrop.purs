-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // tree-view // drag-drop
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView DragDrop — Drag and drop logic for tree reordering.
-- |
-- | ## Design Philosophy
-- |
-- | Tree drag-drop extends Schema.Gestural.DragDrop with tree-specific logic:
-- |
-- | - Nodes can be dropped before, after, or inside other nodes
-- | - Drop validation prevents dropping a node into its own descendants
-- | - Visual drop indicators show where the node will land
-- |
-- | ## Schema Integration
-- |
-- | This module uses Schema atoms:
-- | - DragPhase, DropEffect from Schema.Gestural.DragDrop
-- | - DropPosition from TreeView.Types
-- |
-- | ## Drop Position Semantics
-- |
-- | | Position    | Result                                    |
-- | |-------------|-------------------------------------------|
-- | | DropBefore  | Insert as previous sibling of target      |
-- | | DropAfter   | Insert as next sibling of target          |
-- | | DropInside  | Insert as last child of target            |
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Types (NodeId, DropPosition)
-- | - TreeView.State (DragState)
-- | - TreeView.Node (Tree, ancestry queries)
-- | - Schema.Gestural.DragDrop (DragPhase, DropEffect)

module Hydrogen.Element.Compound.TreeView.DragDrop
  ( -- * Drag Operations
    canStartDrag
  , startNodeDrag
  , updateNodeDrag
  , endNodeDrag
  , cancelNodeDrag
  
  -- * Drop Validation
  , canDropOn
  , computeDropPosition
  , isValidDrop
  
  -- * Drop Operations
  , performDrop
  , moveNodeTo
  
  -- * Drop Indicator
  , DropIndicator
  , dropIndicator
  , indicatorTarget
  , indicatorPosition
  , indicatorDepth
  , noIndicator
  , hasIndicator
  
  -- * Drag State Queries
  , isDraggingNode
  , getDraggedNode
  , getDropTarget
  , getCurrentDropPosition
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (==)
  , (/=)
  , (<)
  , (>)
  , (&&)
  , not
  , otherwise
  )

import Data.Maybe (Maybe(Just, Nothing), isJust)

import Hydrogen.Element.Compound.TreeView.Types
  ( NodeId
  , DropPosition(DropBefore, DropAfter, DropInside)
  , Depth
  , rootDepth
  )

import Hydrogen.Element.Compound.TreeView.State
  ( DragState
  , beginDrag
  , updateDragOver
  , endDrag
  , isDragging
  , getDragSource
  , getDragTarget
  , getDragPosition
  )

import Hydrogen.Element.Compound.TreeView.Node
  ( Tree
  , TreeNode
  , nodeId
  , nodeDisabled
  , isDescendantOf
  , parentNode
  , moveNode
  , getNode
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // drag operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a node can be dragged
-- |
-- | A node can be dragged if:
-- | - Dragging is enabled on the tree
-- | - The node is not disabled
canStartDrag :: Boolean -> TreeNode -> Boolean
canStartDrag draggingEnabled node =
  draggingEnabled && not (nodeDisabled node)

-- | Start dragging a node
startNodeDrag :: NodeId -> DragState
startNodeDrag = beginDrag

-- | Update drag position over a target node
updateNodeDrag :: NodeId -> DropPosition -> DragState -> DragState
updateNodeDrag = updateDragOver

-- | End the drag operation (drop)
-- |
-- | Returns the updated drag state (now idle).
endNodeDrag :: DragState -> DragState
endNodeDrag = endDrag

-- | Cancel the drag operation
cancelNodeDrag :: DragState -> DragState
cancelNodeDrag = endDrag

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // drop validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a source node can be dropped on a target
-- |
-- | A drop is invalid if:
-- | - Source equals target (dropping on self)
-- | - Target is a descendant of source (would create cycle)
-- | - Target node is disabled
canDropOn :: Tree -> NodeId -> NodeId -> Boolean
canDropOn tree sourceId targetId =
  sourceId /= targetId
  && not (isDescendantOf targetId sourceId tree)
  && not (isTargetDisabled tree targetId)

-- | Check if target node is disabled
isTargetDisabled :: Tree -> NodeId -> Boolean
isTargetDisabled tree targetId =
  case getNodeFromTree tree targetId of
    Nothing -> true  -- Node doesn't exist = can't drop
    Just node -> nodeDisabled node

-- | Compute drop position based on vertical offset
-- |
-- | Given where the cursor is relative to the target node's bounds:
-- | - Top 25%: DropBefore
-- | - Middle 50%: DropInside (if target can have children)
-- | - Bottom 25%: DropAfter
-- |
-- | If target cannot have children (is a leaf), only Before/After are used.
computeDropPosition :: 
  Number ->     -- ^ Y offset within target bounds (0.0 = top, 1.0 = bottom)
  Boolean ->    -- ^ Can target have children?
  DropPosition
computeDropPosition yOffset canHaveChildren
  | yOffset < 0.25 = DropBefore
  | yOffset > 0.75 = DropAfter
  | canHaveChildren = DropInside
  | yOffset < 0.5 = DropBefore
  | otherwise = DropAfter

-- | Check if current drag state represents a valid drop
isValidDrop :: Tree -> DragState -> Boolean
isValidDrop tree state =
  case getDragSource state, getDragTarget state of
    Just sourceId, Just targetId -> canDropOn tree sourceId targetId
    _, _ -> false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // drop operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Perform the drop operation
-- |
-- | Returns the updated tree with the node moved to its new position.
performDrop :: DragState -> Tree -> Tree
performDrop state tree =
  case getDragSource state, getDragTarget state, getDragPosition state of
    Just sourceId, Just targetId, Just position ->
      if canDropOn tree sourceId targetId
        then moveNodeTo sourceId targetId position tree
        else tree
    _, _, _ -> tree

-- | Move a node to a new position in the tree
-- |
-- | Handles the three drop positions:
-- | - DropBefore: Move to same parent as target, insert before target
-- | - DropAfter: Move to same parent as target, insert after target
-- | - DropInside: Move to become child of target
moveNodeTo :: NodeId -> NodeId -> DropPosition -> Tree -> Tree
moveNodeTo sourceId targetId position tree =
  case position of
    DropInside ->
      -- Move as child of target
      moveNode sourceId (Just targetId) tree
    
    DropBefore ->
      -- Move as sibling of target (before)
      -- New parent is target's parent
      case parentNode targetId tree of
        Nothing -> moveNode sourceId Nothing tree  -- Target is root, source becomes root
        Just parent -> moveNode sourceId (Just (nodeId parent)) tree
    
    DropAfter ->
      -- Move as sibling of target (after)
      -- Same as DropBefore for parent determination
      case parentNode targetId tree of
        Nothing -> moveNode sourceId Nothing tree  -- Target is root, source becomes root
        Just parent -> moveNode sourceId (Just (nodeId parent)) tree

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // drop indicator
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual indicator showing where a drop will occur
-- |
-- | Used by the renderer to draw drop feedback (line or highlight).
type DropIndicator =
  { target :: Maybe NodeId        -- ^ Target node
  , position :: Maybe DropPosition  -- ^ Where relative to target
  , depth :: Depth                -- ^ Depth for indentation
  , visible :: Boolean            -- ^ Whether to show indicator
  }

-- | Create a drop indicator
dropIndicator :: NodeId -> DropPosition -> Depth -> DropIndicator
dropIndicator target position depth =
  { target: Just target
  , position: Just position
  , depth: depth
  , visible: true
  }

-- | Get indicator target
indicatorTarget :: DropIndicator -> Maybe NodeId
indicatorTarget di = di.target

-- | Get indicator position
indicatorPosition :: DropIndicator -> Maybe DropPosition
indicatorPosition di = di.position

-- | Get indicator depth
indicatorDepth :: DropIndicator -> Depth
indicatorDepth di = di.depth

-- | No drop indicator (hidden)
noIndicator :: DropIndicator
noIndicator =
  { target: Nothing
  , position: Nothing
  , depth: rootDepth
  , visible: false
  }

-- | Check if indicator is visible
hasIndicator :: DropIndicator -> Boolean
hasIndicator di = di.visible && isJust di.target

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // drag state queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if currently dragging a node
isDraggingNode :: DragState -> Boolean
isDraggingNode = isDragging

-- | Get the node being dragged
getDraggedNode :: DragState -> Maybe NodeId
getDraggedNode = getDragSource

-- | Get the current drop target
getDropTarget :: DragState -> Maybe NodeId
getDropTarget = getDragTarget

-- | Get the current drop position
getCurrentDropPosition :: DragState -> Maybe DropPosition
getCurrentDropPosition = getDragPosition

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get a node from the tree by ID
getNodeFromTree :: Tree -> NodeId -> Maybe TreeNode
getNodeFromTree tree nid = getNode nid tree
