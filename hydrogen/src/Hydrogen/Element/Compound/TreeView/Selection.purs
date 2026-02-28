-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // element // treeview // selection
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Selection — Selection logic for tree components.
-- |
-- | ## Design Philosophy
-- |
-- | Tree selection extends the Schema's selection primitives to handle
-- | hierarchical structures. Key behaviors:
-- |
-- | - Single/Multi selection modes (from Schema.Reactive.SelectionState)
-- | - Hierarchical checkbox propagation (check parent → check all children)
-- | - Indeterminate state computation (mixed children → parent indeterminate)
-- | - Range selection in flattened visible order
-- |
-- | ## Schema Integration
-- |
-- | This module uses Schema atoms:
-- | - SelectionMode from Schema.Reactive.SelectionState
-- | - HierarchicalStatus for checkbox tri-state
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Types (NodeId, SelectionMode, CheckState)
-- | - TreeView.State (SelectedState, CheckedState)
-- | - TreeView.Node (Tree, node queries)
-- | - Schema.Reactive.SelectionState (HierarchicalStatus)

module Hydrogen.Element.Compound.TreeView.Selection
  ( -- * Selection Operations
    handleSelect
  , handleDeselect
  , handleToggleSelect
  , handleSelectRange
  , handleSelectAll
  , handleSelectSubtree
  , handleClearSelection
  
  -- * Checkbox Operations
  , handleCheck
  , handleUncheck
  , handleToggleCheck
  , handleCheckSubtree
  , handleClearChecked
  , propagateCheckToChildren
  , propagateCheckToParent
  , recomputeAllCheckStates
  
  -- * Hierarchical Status
  , nodeHierarchicalStatus
  , checkStateToHierarchical
  , hierarchicalToCheckState
  
  -- * Selection Queries
  , isNodeSelected
  , isNodeChecked
  , getSelectedNodes
  , getCheckedNodes
  , getPartiallyCheckedNodes
  
  -- * Tree Traversal
  , subtreeNodes
  , getParentNodeId
  , isRootNode
  , getParentNode
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( Ordering
  , compare
  , (==)
  , (+)
  , (<)
  , map
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.Foldable (foldl)

import Hydrogen.Element.Compound.TreeView.Types
  ( NodeId
  , SelectionMode(SingleSelect, MultiSelect, NoSelect)
  , CheckState(Unchecked, Checked, Indeterminate)
  )

import Hydrogen.Element.Compound.TreeView.State
  ( SelectedState
  , CheckedState
  , emptySelected
  , isSelected
  , selectNode
  , deselectNode
  , clearSelection
  , selectedNodes
  , getCheckState
  , setCheckState
  , emptyChecked
  )

import Hydrogen.Element.Compound.TreeView.Node
  ( Tree
  , TreeNode
  , childNodes
  , parentNode
  , descendantNodes
  , ancestorNodes
  , nodeId
  , nodeParent
  , treeNodes
  )

import Hydrogen.Schema.Reactive.SelectionState
  ( HierarchicalStatus(FullySelected, PartiallySelected, NotSelected)
  , computeParentStatus
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // selection operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle selecting a node based on selection mode
-- |
-- | In SingleSelect mode, this clears previous selection first.
-- | In MultiSelect mode, this adds to selection.
-- | In NoSelect mode, this is a no-op.
handleSelect :: 
  SelectionMode -> 
  NodeId -> 
  SelectedState -> 
  SelectedState
handleSelect mode nid state =
  case mode of
    NoSelect -> state
    SingleSelect -> selectNode nid (clearSelection state)
    MultiSelect -> selectNode nid state

-- | Handle deselecting a node
handleDeselect :: NodeId -> SelectedState -> SelectedState
handleDeselect = deselectNode

-- | Toggle node selection (select if unselected, deselect if selected)
handleToggleSelect :: 
  SelectionMode -> 
  NodeId -> 
  SelectedState -> 
  SelectedState
handleToggleSelect mode nid state =
  case mode of
    NoSelect -> state
    SingleSelect ->
      if isSelected nid state
        then deselectNode nid state
        else selectNode nid (clearSelection state)
    MultiSelect ->
      if isSelected nid state
        then deselectNode nid state
        else selectNode nid state

-- | Select a range of nodes (for Shift+click)
-- |
-- | Selects all visible nodes between anchor and target.
-- | The anchor is typically the last selected node.
handleSelectRange :: 
  Array NodeId ->  -- ^ Visible node IDs in order
  NodeId ->        -- ^ Anchor node
  NodeId ->        -- ^ Target node
  SelectedState -> 
  SelectedState
handleSelectRange visibleIds anchor target state =
  let
    anchorIdx = Array.findIndex (\nid -> nid == anchor) visibleIds
    targetIdx = Array.findIndex (\nid -> nid == target) visibleIds
  in
    case anchorIdx, targetIdx of
      Just ai, Just ti ->
        let
          startIdx = if ai < ti then ai else ti
          endIdx = if ai < ti then ti else ai
          rangeIds = Array.slice startIdx (endIdx + 1) visibleIds
        in
          foldl (\s nid -> selectNode nid s) state rangeIds
      _, _ -> state

-- | Select all nodes in tree
handleSelectAll :: Tree -> SelectedState -> SelectedState
handleSelectAll tree _ =
  let
    allIds = map nodeId (allTreeNodes tree)
  in
    foldl (\s nid -> selectNode nid s) emptySelected allIds

-- | Select an entire subtree (node and all descendants)
-- |
-- | Useful for "select branch" operations in file managers, etc.
handleSelectSubtree :: 
  Tree -> 
  TreeNode -> 
  SelectedState -> 
  SelectedState
handleSelectSubtree tree node state =
  let
    nodes = subtreeNodes tree node
    nodeIds = map nodeId nodes
  in
    foldl (\s nid -> selectNode nid s) state nodeIds

-- | Clear all selections
handleClearSelection :: SelectedState -> SelectedState
handleClearSelection = clearSelection

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // checkbox operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check a node (set to Checked state)
handleCheck :: NodeId -> CheckedState -> CheckedState
handleCheck nid = setCheckState nid Checked

-- | Uncheck a node (set to Unchecked state)
handleUncheck :: NodeId -> CheckedState -> CheckedState
handleUncheck nid = setCheckState nid Unchecked

-- | Toggle node checkbox
-- |
-- | Unchecked → Checked
-- | Checked → Unchecked
-- | Indeterminate → Checked
handleToggleCheck :: NodeId -> CheckedState -> CheckedState
handleToggleCheck nid state =
  case getCheckState nid state of
    Unchecked -> setCheckState nid Checked state
    Checked -> setCheckState nid Unchecked state
    Indeterminate -> setCheckState nid Checked state

-- | Check an entire subtree (node and all descendants)
-- |
-- | Useful for "check all in folder" operations.
-- | Does NOT propagate to parents — call propagateCheckToParent separately
-- | if you need to update ancestor indeterminate states.
handleCheckSubtree :: 
  Tree -> 
  TreeNode -> 
  CheckState -> 
  CheckedState -> 
  CheckedState
handleCheckSubtree tree node targetState state =
  let
    nodes = subtreeNodes tree node
    nodeIds = map nodeId nodes
  in
    foldl (\s nid -> setCheckState nid targetState s) state nodeIds

-- | Clear all checkbox states (uncheck everything)
handleClearChecked :: CheckedState -> CheckedState
handleClearChecked _ = emptyChecked

-- | Propagate check state to all descendants
-- |
-- | When a parent is checked/unchecked, all children should match.
propagateCheckToChildren :: 
  NodeId -> 
  CheckState -> 
  Tree -> 
  CheckedState -> 
  CheckedState
propagateCheckToChildren nid targetState tree state =
  let
    descendants = descendantNodes nid tree
    descendantIds = map nodeId descendants
  in
    foldl (\s did -> setCheckState did targetState s) state descendantIds

-- | Propagate check state to ancestors
-- |
-- | After changing a node's state, recompute all ancestors' states.
-- | Ancestors become:
-- | - Checked if all children are Checked
-- | - Unchecked if all children are Unchecked  
-- | - Indeterminate otherwise
propagateCheckToParent :: 
  NodeId -> 
  Tree -> 
  CheckedState -> 
  CheckedState
propagateCheckToParent nid tree state =
  let
    ancestors = ancestorNodes nid tree
  in
    foldl (recomputeNodeCheckState tree) state ancestors

-- | Recompute a single node's check state from its children
-- |
-- | Uses Schema's computeParentStatus for hierarchical logic.
recomputeNodeCheckState :: 
  Tree -> 
  CheckedState -> 
  TreeNode -> 
  CheckedState
recomputeNodeCheckState tree state node =
  let
    nid = nodeId node
    children = childNodes nid tree
    -- Convert children's CheckStates to HierarchicalStatus for Schema computation
    childStatuses = map (\c -> checkStateToHierarchical (getCheckState (nodeId c) state)) children
    
    newState = 
      if Array.null children
        then getCheckState nid state  -- Leaf: keep current
        else hierarchicalToCheckState (computeParentStatus childStatuses)
  in
    setCheckState nid newState state

-- | Recompute all check states in the tree
-- |
-- | Useful after bulk operations or initial load.
recomputeAllCheckStates :: Tree -> CheckedState -> CheckedState
recomputeAllCheckStates tree state =
  let
    -- Process bottom-up (leaves first, then parents)
    nodes = allTreeNodes tree
    sorted = Array.sortBy (compareByDepth tree) nodes
  in
    foldl (recomputeNodeCheckState tree) state sorted

-- | Compare nodes by depth (deeper nodes first for bottom-up processing)
compareByDepth :: Tree -> TreeNode -> TreeNode -> Ordering
compareByDepth tree a b =
  let
    depthA = Array.length (ancestorNodes (nodeId a) tree)
    depthB = Array.length (ancestorNodes (nodeId b) tree)
  in
    -- Reverse order: deeper nodes come first
    compare depthB depthA

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // hierarchical status
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get hierarchical selection status for a node
-- |
-- | Maps the node's CheckState to Schema's HierarchicalStatus.
nodeHierarchicalStatus :: NodeId -> CheckedState -> HierarchicalStatus
nodeHierarchicalStatus nid state =
  checkStateToHierarchical (getCheckState nid state)

-- | Convert TreeView CheckState to Schema HierarchicalStatus
checkStateToHierarchical :: CheckState -> HierarchicalStatus
checkStateToHierarchical Checked = FullySelected
checkStateToHierarchical Unchecked = NotSelected
checkStateToHierarchical Indeterminate = PartiallySelected

-- | Convert Schema HierarchicalStatus to TreeView CheckState
hierarchicalToCheckState :: HierarchicalStatus -> CheckState
hierarchicalToCheckState FullySelected = Checked
hierarchicalToCheckState NotSelected = Unchecked
hierarchicalToCheckState PartiallySelected = Indeterminate

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // selection queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a node is selected
isNodeSelected :: NodeId -> SelectedState -> Boolean
isNodeSelected = isSelected

-- | Check if a node is checked (fully checked, not indeterminate)
isNodeChecked :: NodeId -> CheckedState -> Boolean
isNodeChecked nid state = getCheckState nid state == Checked

-- | Get all selected node IDs
getSelectedNodes :: SelectedState -> Array NodeId
getSelectedNodes = selectedNodes

-- | Get all fully checked node IDs
getCheckedNodes :: Tree -> CheckedState -> Array NodeId
getCheckedNodes tree state =
  let
    nodes = allTreeNodes tree
  in
    map nodeId (Array.filter (\n -> getCheckState (nodeId n) state == Checked) nodes)

-- | Get all partially checked (indeterminate) node IDs
getPartiallyCheckedNodes :: Tree -> CheckedState -> Array NodeId
getPartiallyCheckedNodes tree state =
  let
    nodes = allTreeNodes tree
  in
    map nodeId (Array.filter (\n -> getCheckState (nodeId n) state == Indeterminate) nodes)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all nodes in the tree (flattened)
allTreeNodes :: Tree -> Array TreeNode
allTreeNodes = treeNodes

-- | Get all nodes in a subtree rooted at the given node
subtreeNodes :: Tree -> TreeNode -> Array TreeNode
subtreeNodes tree node =
  let
    nid = nodeId node
    children = childNodes nid tree
  in
    Array.cons node (Array.concatMap (subtreeNodes tree) children)

-- | Get the parent node ID of a node, if it has one.
-- |
-- | Returns Nothing for root nodes.
getParentNodeId :: TreeNode -> Maybe NodeId
getParentNodeId node = 
  case nodeParent node of
    Nothing -> Nothing
    Just pid -> Just pid

-- | Check if a node is a root node (has no parent).
-- |
-- | Root nodes have no parent in the tree hierarchy.
isRootNode :: TreeNode -> Boolean
isRootNode node =
  case nodeParent node of
    Nothing -> true
    Just _ -> false

-- | Get the parent TreeNode from a NodeId.
-- |
-- | Returns Nothing if the node has no parent (is a root node).
getParentNode :: NodeId -> Tree -> Maybe TreeNode
getParentNode nid tree = parentNode nid tree
