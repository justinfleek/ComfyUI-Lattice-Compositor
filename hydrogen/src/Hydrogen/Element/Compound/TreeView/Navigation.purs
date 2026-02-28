-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // treeview // navigation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Navigation — Keyboard navigation for accessible tree components.
-- |
-- | ## Design Philosophy
-- |
-- | Tree navigation follows WAI-ARIA TreeView patterns:
-- | - Up/Down: Move through visible nodes in document order
-- | - Left: Collapse node or move to parent
-- | - Right: Expand node or move to first child
-- | - Home/End: Jump to first/last visible node
-- |
-- | ## Architecture
-- |
-- | Navigation is computed purely from:
-- | - The tree structure (Node.Tree)
-- | - The expanded state (which nodes are visible)
-- | - The current focus
-- |
-- | The result is a new NodeId to focus, or an action to perform.
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Types (NodeId, TreeViewMsg)
-- | - TreeView.State (ExpandedState, FocusState)
-- | - TreeView.Node (Tree, node queries)

module Hydrogen.Element.Compound.TreeView.Navigation
  ( -- * Visible Node List
    visibleNodes
  , visibleNodeIds
  
  -- * Navigation Computations
  , navigateUp
  , navigateDown
  , navigateLeft
  , navigateRight
  , navigateHome
  , navigateEnd
  
  -- * Navigation Result
  , NavResult
      ( FocusNode
      , ExpandNode
      , CollapseNode
      , NoOp
      )
  , applyNavResult
  
  -- * Type-ahead Search
  , findByPrefix
  , findNextByPrefix
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (==)
  , (<>)
  , (+)
  , (-)
  , (>=)
  , (<)
  , map
  , not
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String.CodeUnits (take, length) as String
import Data.String.Common (toLower) as String

import Hydrogen.Element.Compound.TreeView.Types
  ( NodeId
  )

import Hydrogen.Element.Compound.TreeView.State
  ( ExpandedState
  , FocusState
  , isExpanded
  , setExpanded
  , getFocusedNode
  , focusOn
  )

import Hydrogen.Element.Compound.TreeView.Node
  ( Tree
  , TreeNode
  , rootNodes
  , childNodes
  , parentNode
  , nodeId
  , nodeLabel
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // visible node list
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all visible nodes in document order
-- |
-- | A node is visible if all its ancestors are expanded.
-- | This is the list the user sees and can navigate through.
visibleNodes :: Tree -> ExpandedState -> Array TreeNode
visibleNodes tree expanded =
  let
    roots = rootNodes tree
  in
    Array.concatMap (visibleSubtree tree expanded) roots

-- | Internal: Get visible subtree rooted at a node
visibleSubtree :: Tree -> ExpandedState -> TreeNode -> Array TreeNode
visibleSubtree tree expanded node =
  let
    nid = nodeId node
    children = childNodes nid tree
    visibleChildren =
      if isExpanded nid expanded
        then Array.concatMap (visibleSubtree tree expanded) children
        else []
  in
    Array.cons node visibleChildren

-- | Get just the NodeIds of visible nodes
visibleNodeIds :: Tree -> ExpandedState -> Array NodeId
visibleNodeIds tree expanded = map nodeId (visibleNodes tree expanded)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // navigation result
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of a navigation computation
-- |
-- | Navigation can result in:
-- | - Moving focus to a different node
-- | - Expanding a node (then optionally moving focus)
-- | - Collapsing a node
-- | - No operation (at boundary, can't navigate further)
data NavResult
  = FocusNode NodeId           -- ^ Move focus to this node
  | ExpandNode NodeId          -- ^ Expand this node
  | CollapseNode NodeId        -- ^ Collapse this node
  | NoOp                       -- ^ Nothing to do

derive instance eqNavResult :: Eq NavResult

instance showNavResult :: Show NavResult where
  show (FocusNode nid) = "FocusNode(" <> show nid <> ")"
  show (ExpandNode nid) = "ExpandNode(" <> show nid <> ")"
  show (CollapseNode nid) = "CollapseNode(" <> show nid <> ")"
  show NoOp = "NoOp"

-- | Apply a navigation result to state
-- |
-- | Returns updated focus state and expanded state.
applyNavResult ::
  NavResult ->
  FocusState ->
  ExpandedState ->
  { focus :: FocusState, expanded :: ExpandedState }
applyNavResult result focus expanded =
  case result of
    FocusNode nid ->
      { focus: focusOn nid, expanded: expanded }
    ExpandNode nid ->
      { focus: focusOn nid, expanded: setExpanded nid true expanded }
    CollapseNode nid ->
      { focus: focus, expanded: setExpanded nid false expanded }
    NoOp ->
      { focus: focus, expanded: expanded }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // navigation computations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Navigate up (previous visible node)
-- |
-- | Moves to the previous node in document order.
-- | At first node, returns NoOp.
navigateUp :: Tree -> ExpandedState -> FocusState -> NavResult
navigateUp tree expanded focus =
  case getFocusedNode focus of
    Nothing ->
      -- No focus: focus the last visible node
      case Array.last (visibleNodeIds tree expanded) of
        Nothing -> NoOp
        Just lastId -> FocusNode lastId
    Just currentId ->
      let
        visible = visibleNodeIds tree expanded
        currentIndex = Array.findIndex (\nid -> nid == currentId) visible
      in
        case currentIndex of
          Nothing -> NoOp  -- Current node not visible?
          Just idx ->
            if idx < 1
              then NoOp  -- Already at first
              else
                case Array.index visible (idx - 1) of
                  Nothing -> NoOp
                  Just prevId -> FocusNode prevId

-- | Navigate down (next visible node)
-- |
-- | Moves to the next node in document order.
-- | At last node, returns NoOp.
navigateDown :: Tree -> ExpandedState -> FocusState -> NavResult
navigateDown tree expanded focus =
  case getFocusedNode focus of
    Nothing ->
      -- No focus: focus the first visible node
      case Array.head (visibleNodeIds tree expanded) of
        Nothing -> NoOp
        Just firstId -> FocusNode firstId
    Just currentId ->
      let
        visible = visibleNodeIds tree expanded
        visibleLen = Array.length visible
        currentIndex = Array.findIndex (\nid -> nid == currentId) visible
      in
        case currentIndex of
          Nothing -> NoOp  -- Current node not visible?
          Just idx ->
            if idx >= visibleLen - 1
              then NoOp  -- Already at last
              else
                case Array.index visible (idx + 1) of
                  Nothing -> NoOp
                  Just nextId -> FocusNode nextId

-- | Navigate left (collapse or go to parent)
-- |
-- | If node is expanded: collapse it.
-- | If node is collapsed or leaf: move to parent.
-- | At root with no expansion: NoOp.
navigateLeft :: Tree -> ExpandedState -> FocusState -> NavResult
navigateLeft tree expanded focus =
  case getFocusedNode focus of
    Nothing -> NoOp
    Just currentId ->
      if isExpanded currentId expanded
        then CollapseNode currentId
        else
          case parentNode currentId tree of
            Nothing -> NoOp  -- At root
            Just parent -> FocusNode (nodeId parent)

-- | Navigate right (expand or go to first child)
-- |
-- | If node is collapsed and has children: expand it.
-- | If node is expanded: move to first child.
-- | If leaf node: NoOp.
navigateRight :: Tree -> ExpandedState -> FocusState -> NavResult
navigateRight tree expanded focus =
  case getFocusedNode focus of
    Nothing -> NoOp
    Just currentId ->
      let
        children = childNodes currentId tree
        hasChildren = not (Array.null children)
        isExp = isExpanded currentId expanded
      in
        if not hasChildren
          then NoOp  -- Leaf node
          else if isExp
            then
              -- Already expanded: move to first child
              case Array.head children of
                Nothing -> NoOp
                Just firstChild -> FocusNode (nodeId firstChild)
            else
              -- Collapsed: expand it
              ExpandNode currentId

-- | Navigate home (first visible node)
navigateHome :: Tree -> ExpandedState -> NavResult
navigateHome tree expanded =
  case Array.head (visibleNodeIds tree expanded) of
    Nothing -> NoOp
    Just firstId -> FocusNode firstId

-- | Navigate end (last visible node)
navigateEnd :: Tree -> ExpandedState -> NavResult
navigateEnd tree expanded =
  case Array.last (visibleNodeIds tree expanded) of
    Nothing -> NoOp
    Just lastId -> FocusNode lastId

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // type-ahead search
-- ═════════════════════════════════════════════════════════════════════════════

-- | Find the first visible node whose label starts with a prefix
-- |
-- | Case-insensitive prefix match.
findByPrefix :: String -> Tree -> ExpandedState -> Maybe NodeId
findByPrefix prefix tree expanded =
  let
    lowerPrefix = String.toLower prefix
    prefixLen = String.length prefix
    visible = visibleNodes tree expanded
    
    matchesPrefix :: TreeNode -> Boolean
    matchesPrefix node =
      String.toLower (String.take prefixLen (nodeLabel node)) == lowerPrefix
  in
    map nodeId (Array.find matchesPrefix visible)

-- | Find the next visible node matching prefix after current focus
-- |
-- | Wraps around to the beginning if needed.
findNextByPrefix :: String -> Tree -> ExpandedState -> FocusState -> Maybe NodeId
findNextByPrefix prefix tree expanded focus =
  let
    lowerPrefix = String.toLower prefix
    prefixLen = String.length prefix
    visible = visibleNodes tree expanded
    
    matchesPrefix :: TreeNode -> Boolean
    matchesPrefix node =
      String.toLower (String.take prefixLen (nodeLabel node)) == lowerPrefix
    
    currentId = getFocusedNode focus
    
    -- Find all matching nodes
    matching = Array.filter matchesPrefix visible
    matchingIds = map nodeId matching
    
    -- Find index of current in matching list
    currentMatchIdx = case currentId of
      Nothing -> Nothing
      Just cid -> Array.findIndex (\nid -> nid == cid) matchingIds
  in
    case Array.length matchingIds of
      0 -> Nothing
      1 -> Array.head matchingIds
      len ->
        case currentMatchIdx of
          Nothing -> Array.head matchingIds
          Just idx ->
            let nextIdx = if idx >= len - 1 then 0 else idx + 1
            in Array.index matchingIds nextIdx
