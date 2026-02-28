-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // treeview // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView State — Runtime state management for the tree view.
-- |
-- | ## Design Philosophy
-- |
-- | State is pure data describing the tree at a point in time.
-- | State transitions are pure functions: State -> Msg -> State.
-- | The runtime renders state to DOM; no mutation here.
-- |
-- | ## State Components
-- |
-- | - Expanded node set (which nodes are expanded)
-- | - Selected node set (which nodes are selected)
-- | - Checked node map (checkbox states)
-- | - Focus state (keyboard navigation)
-- | - Drag state (drag and drop)
-- | - Search state (filter query)
-- | - Loading state (lazy-loaded nodes)
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Types (NodeId, CheckState, DropPosition, SelectionMode)

module Hydrogen.Element.Compound.TreeView.State
  ( -- * Expanded State
    ExpandedState
  , emptyExpanded
  , isExpanded
  , setExpanded
  , toggleExpanded
  , expandAll
  , collapseAll
  , expandedCount
  
  -- * Selected State
  , SelectedState
  , emptySelected
  , isSelected
  , selectNode
  , deselectNode
  , toggleSelected
  , clearSelection
  , selectAll
  , selectedNodes
  , selectedCount
  
  -- * Checked State
  , CheckedState
  , emptyChecked
  , getCheckState
  , setCheckState
  , toggleCheckState
  , clearChecked
  , checkedNodes
  , checkedCount
  
  -- * Focus State
  , FocusState
  , noFocus
  , focusOn
  , getFocusedNode
  , hasFocus
  , clearFocusState
  
  -- * Drag State
  , DragState
  , noDrag
  , beginDrag
  , updateDragOver
  , endDrag
  , isDragging
  , getDragSource
  , getDragTarget
  , getDragPosition
  
  -- * Search State
  , SearchState
  , emptySearch
  , setSearchQuery
  , getSearchQuery
  , hasSearchQuery
  , clearSearch
  
  -- * Loading State
  , LoadingState
  , emptyLoading
  , isLoading
  , setLoading
  , clearLoading
  , loadingNodes
  
  -- * Edit State
  , EditState
  , noEdit
  , beginEditState
  , updateEditBuffer
  , getEditingNode
  , getEditBuffer
  , isEditing
  , isEditingNode
  , clearEditState
  
  -- * Hover State
  , HoverState
  , noHover
  , setHover
  , getHoveredNode
  , isHovering
  , isHoveringNode
  , clearHover
  
  -- * Complete Tree State
  , TreeViewState
  , initialState
  , withSelectionMode
  , withCheckable
  , withDraggable
  , withSearchable
  , withEditable
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
  , (&&)
  , not
  , map
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.Set (Set)
import Data.Set as Set
import Data.Map (Map)
import Data.Map as Map
import Data.Tuple (Tuple, fst, snd)

import Hydrogen.Element.Compound.TreeView.Types
  ( NodeId
  , unwrapNodeId
  , CheckState(Unchecked, Checked, Indeterminate)
  , DropPosition
  , SelectionMode(SingleSelect)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // expanded state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set of expanded node IDs
-- |
-- | Tracks which nodes have their children visible.
newtype ExpandedState = ExpandedState (Set NodeId)

derive instance eqExpandedState :: Eq ExpandedState

instance showExpandedState :: Show ExpandedState where
  show (ExpandedState s) = "Expanded(" <> show (Set.size s) <> " nodes)"

-- | Empty expanded state (all collapsed)
emptyExpanded :: ExpandedState
emptyExpanded = ExpandedState Set.empty

-- | Check if a node is expanded
isExpanded :: NodeId -> ExpandedState -> Boolean
isExpanded nid (ExpandedState s) = Set.member nid s

-- | Set a node's expanded state
setExpanded :: NodeId -> Boolean -> ExpandedState -> ExpandedState
setExpanded nid expanded (ExpandedState s) =
  if expanded
    then ExpandedState (Set.insert nid s)
    else ExpandedState (Set.delete nid s)

-- | Toggle a node's expanded state
toggleExpanded :: NodeId -> ExpandedState -> ExpandedState
toggleExpanded nid state =
  setExpanded nid (not (isExpanded nid state)) state

-- | Expand all nodes (given a list of all node IDs)
expandAll :: Array NodeId -> ExpandedState -> ExpandedState
expandAll nids _ = ExpandedState (Set.fromFoldable nids)

-- | Collapse all nodes
collapseAll :: ExpandedState -> ExpandedState
collapseAll _ = emptyExpanded

-- | Count of expanded nodes
expandedCount :: ExpandedState -> Int
expandedCount (ExpandedState s) = Set.size s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // selected state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set of selected node IDs
-- |
-- | Tracks which nodes are currently selected.
-- | In SingleSelect mode, only one node can be selected.
newtype SelectedState = SelectedState (Set NodeId)

derive instance eqSelectedState :: Eq SelectedState

instance showSelectedState :: Show SelectedState where
  show (SelectedState s) = "Selected(" <> show (Set.size s) <> " nodes)"

-- | Empty selection state
emptySelected :: SelectedState
emptySelected = SelectedState Set.empty

-- | Check if a node is selected
isSelected :: NodeId -> SelectedState -> Boolean
isSelected nid (SelectedState s) = Set.member nid s

-- | Select a node (adds to selection)
selectNode :: NodeId -> SelectedState -> SelectedState
selectNode nid (SelectedState s) = SelectedState (Set.insert nid s)

-- | Deselect a node
deselectNode :: NodeId -> SelectedState -> SelectedState
deselectNode nid (SelectedState s) = SelectedState (Set.delete nid s)

-- | Toggle a node's selection state
toggleSelected :: NodeId -> SelectedState -> SelectedState
toggleSelected nid state =
  if isSelected nid state
    then deselectNode nid state
    else selectNode nid state

-- | Clear all selections
clearSelection :: SelectedState -> SelectedState
clearSelection _ = emptySelected

-- | Select all nodes (given a list of all node IDs)
selectAll :: Array NodeId -> SelectedState -> SelectedState
selectAll nids _ = SelectedState (Set.fromFoldable nids)

-- | Get all selected node IDs as array
selectedNodes :: SelectedState -> Array NodeId
selectedNodes (SelectedState s) = Set.toUnfoldable s

-- | Count of selected nodes
selectedCount :: SelectedState -> Int
selectedCount (SelectedState s) = Set.size s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // checked state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map of node IDs to check states
-- |
-- | For checkable trees. Nodes not in the map are Unchecked.
newtype CheckedState = CheckedState (Map NodeId CheckState)

derive instance eqCheckedState :: Eq CheckedState

instance showCheckedState :: Show CheckedState where
  show (CheckedState m) = "Checked(" <> show (Map.size m) <> " entries)"

-- | Empty checked state (all unchecked)
emptyChecked :: CheckedState
emptyChecked = CheckedState Map.empty

-- | Get a node's check state (defaults to Unchecked)
getCheckState :: NodeId -> CheckedState -> CheckState
getCheckState nid (CheckedState m) =
  case Map.lookup nid m of
    Just cs -> cs
    Nothing -> Unchecked

-- | Set a node's check state
setCheckState :: NodeId -> CheckState -> CheckedState -> CheckedState
setCheckState nid cs (CheckedState m) =
  case cs of
    Unchecked -> CheckedState (Map.delete nid m)
    _ -> CheckedState (Map.insert nid cs m)

-- | Toggle a node's check state
toggleCheckState :: NodeId -> CheckedState -> CheckedState
toggleCheckState nid state =
  let
    current = getCheckState nid state
    next = case current of
      Unchecked -> Checked
      Checked -> Unchecked
      Indeterminate -> Checked
  in
    setCheckState nid next state

-- | Clear all check states
clearChecked :: CheckedState -> CheckedState
clearChecked _ = emptyChecked

-- | Get all checked node IDs as array (only fully checked, not indeterminate)
checkedNodes :: CheckedState -> Array NodeId
checkedNodes (CheckedState m) =
  map fst (Array.filter isCheckedEntry (Map.toUnfoldable m))
  where
    isCheckedEntry :: Tuple NodeId CheckState -> Boolean
    isCheckedEntry t = snd t == Checked

-- | Count of checked nodes
checkedCount :: CheckedState -> Int
checkedCount state = Array.length (checkedNodes state)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // focus state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Current keyboard focus state
-- |
-- | Tracks which node has keyboard focus for navigation.
newtype FocusState = FocusState (Maybe NodeId)

derive instance eqFocusState :: Eq FocusState

instance showFocusState :: Show FocusState where
  show (FocusState Nothing) = "Focus(none)"
  show (FocusState (Just nid)) = "Focus(" <> unwrapNodeId nid <> ")"

-- | No focus state
noFocus :: FocusState
noFocus = FocusState Nothing

-- | Set focus to a specific node
focusOn :: NodeId -> FocusState
focusOn nid = FocusState (Just nid)

-- | Get the currently focused node
getFocusedNode :: FocusState -> Maybe NodeId
getFocusedNode (FocusState mnid) = mnid

-- | Check if any node has focus
hasFocus :: FocusState -> Boolean
hasFocus (FocusState mnid) = 
  case mnid of
    Just _ -> true
    Nothing -> false

-- | Clear focus
clearFocusState :: FocusState -> FocusState
clearFocusState _ = noFocus

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // drag state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drag and drop state
-- |
-- | Tracks active drag operations.
type DragState =
  { dragging :: Boolean
  , sourceNode :: Maybe NodeId
  , targetNode :: Maybe NodeId
  , position :: Maybe DropPosition
  }

-- | No active drag
noDrag :: DragState
noDrag =
  { dragging: false
  , sourceNode: Nothing
  , targetNode: Nothing
  , position: Nothing
  }

-- | Begin dragging a node
beginDrag :: NodeId -> DragState
beginDrag nid =
  { dragging: true
  , sourceNode: Just nid
  , targetNode: Nothing
  , position: Nothing
  }

-- | Update drag over state
updateDragOver :: NodeId -> DropPosition -> DragState -> DragState
updateDragOver target pos state =
  state
    { targetNode = Just target
    , position = Just pos
    }

-- | End drag operation
endDrag :: DragState -> DragState
endDrag _ = noDrag

-- | Check if currently dragging
isDragging :: DragState -> Boolean
isDragging state = state.dragging

-- | Get the drag source node
getDragSource :: DragState -> Maybe NodeId
getDragSource state = state.sourceNode

-- | Get the drag target node
getDragTarget :: DragState -> Maybe NodeId
getDragTarget state = state.targetNode

-- | Get the drop position
getDragPosition :: DragState -> Maybe DropPosition
getDragPosition state = state.position

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // search state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Search/filter state
-- |
-- | Tracks the current search query for filtering visible nodes.
newtype SearchState = SearchState String

derive instance eqSearchState :: Eq SearchState

instance showSearchState :: Show SearchState where
  show (SearchState q) = "Search(\"" <> q <> "\")"

-- | Empty search state
emptySearch :: SearchState
emptySearch = SearchState ""

-- | Set the search query
setSearchQuery :: String -> SearchState
setSearchQuery = SearchState

-- | Get the current search query
getSearchQuery :: SearchState -> String
getSearchQuery (SearchState q) = q

-- | Check if there's an active search query
hasSearchQuery :: SearchState -> Boolean
hasSearchQuery (SearchState q) = not (q == "")

-- | Clear the search query
clearSearch :: SearchState -> SearchState
clearSearch _ = emptySearch

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // loading state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set of nodes currently loading children
-- |
-- | For lazy-loaded trees, tracks which nodes are fetching children.
newtype LoadingState = LoadingState (Set NodeId)

derive instance eqLoadingState :: Eq LoadingState

instance showLoadingState :: Show LoadingState where
  show (LoadingState s) = "Loading(" <> show (Set.size s) <> " nodes)"

-- | Empty loading state
emptyLoading :: LoadingState
emptyLoading = LoadingState Set.empty

-- | Check if a node is loading
isLoading :: NodeId -> LoadingState -> Boolean
isLoading nid (LoadingState s) = Set.member nid s

-- | Set a node as loading
setLoading :: NodeId -> Boolean -> LoadingState -> LoadingState
setLoading nid loading (LoadingState s) =
  if loading
    then LoadingState (Set.insert nid s)
    else LoadingState (Set.delete nid s)

-- | Clear loading state for a node
clearLoading :: NodeId -> LoadingState -> LoadingState
clearLoading nid state = setLoading nid false state

-- | Get all loading node IDs
loadingNodes :: LoadingState -> Array NodeId
loadingNodes (LoadingState s) = Set.toUnfoldable s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // edit state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State for inline label editing
-- |
-- | Tracks which node is being edited and the current edit buffer.
-- | The buffer holds the in-progress text, separate from the node's actual label.
type EditState =
  { editingNode :: Maybe NodeId    -- ^ Node currently being edited (if any)
  , editBuffer :: String           -- ^ Current text in the edit field
  , originalValue :: String        -- ^ Original value before edit (for cancel)
  }

-- | No active edit
noEdit :: EditState
noEdit =
  { editingNode: Nothing
  , editBuffer: ""
  , originalValue: ""
  }

-- | Begin editing a node
-- |
-- | Stores the original value so it can be restored on cancel.
beginEditState :: NodeId -> String -> EditState
beginEditState nid originalLabel =
  { editingNode: Just nid
  , editBuffer: originalLabel
  , originalValue: originalLabel
  }

-- | Update the edit buffer
updateEditBuffer :: String -> EditState -> EditState
updateEditBuffer newText state = state { editBuffer = newText }

-- | Get the node being edited (if any)
getEditingNode :: EditState -> Maybe NodeId
getEditingNode state = state.editingNode

-- | Get the current edit buffer text
getEditBuffer :: EditState -> String
getEditBuffer state = state.editBuffer

-- | Check if any node is being edited
isEditing :: EditState -> Boolean
isEditing state = case state.editingNode of
  Just _ -> true
  Nothing -> false

-- | Check if a specific node is being edited
isEditingNode :: NodeId -> EditState -> Boolean
isEditingNode nid state = state.editingNode == Just nid

-- | Clear the edit state (cancel or confirm)
clearEditState :: EditState -> EditState
clearEditState _ = noEdit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // hover state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State for mouse hover tracking
-- |
-- | Tracks which node the mouse is currently over.
-- | Used for hover effects and action button visibility.
newtype HoverState = HoverState (Maybe NodeId)

derive instance eqHoverState :: Eq HoverState

instance showHoverState :: Show HoverState where
  show (HoverState Nothing) = "Hover(none)"
  show (HoverState (Just nid)) = "Hover(" <> show nid <> ")"

-- | No node hovered
noHover :: HoverState
noHover = HoverState Nothing

-- | Set the hovered node
setHover :: NodeId -> HoverState
setHover nid = HoverState (Just nid)

-- | Get the currently hovered node (if any)
getHoveredNode :: HoverState -> Maybe NodeId
getHoveredNode (HoverState m) = m

-- | Check if any node is being hovered
isHovering :: HoverState -> Boolean
isHovering (HoverState m) = case m of
  Just _ -> true
  Nothing -> false

-- | Check if a specific node is being hovered
isHoveringNode :: NodeId -> HoverState -> Boolean
isHoveringNode nid (HoverState m) = m == Just nid

-- | Clear the hover state
clearHover :: HoverState -> HoverState
clearHover _ = noHover

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // tree view state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete tree view runtime state
-- |
-- | This compound aggregates all state needed to render the tree.
type TreeViewState =
  { expanded :: ExpandedState
  , selected :: SelectedState
  , checked :: CheckedState
  , focus :: FocusState
  , drag :: DragState
  , search :: SearchState
  , loading :: LoadingState
  , edit :: EditState
  , hover :: HoverState
  
  -- Configuration (set at creation, rarely changes)
  , selectionMode :: SelectionMode
  , checkable :: Boolean
  , draggable :: Boolean
  , searchable :: Boolean
  , editable :: Boolean
  }

-- | Create initial tree view state
initialState :: TreeViewState
initialState =
  { expanded: emptyExpanded
  , selected: emptySelected
  , checked: emptyChecked
  , focus: noFocus
  , drag: noDrag
  , search: emptySearch
  , loading: emptyLoading
  , edit: noEdit
  , hover: noHover
  
  , selectionMode: SingleSelect
  , checkable: false
  , draggable: false
  , searchable: false
  , editable: false
  }

-- | Set selection mode
withSelectionMode :: SelectionMode -> TreeViewState -> TreeViewState
withSelectionMode mode state = state { selectionMode = mode }

-- | Enable/disable checkboxes
withCheckable :: Boolean -> TreeViewState -> TreeViewState
withCheckable c state = state { checkable = c }

-- | Enable/disable drag and drop
withDraggable :: Boolean -> TreeViewState -> TreeViewState
withDraggable d state = state { draggable = d }

-- | Enable/disable search
withSearchable :: Boolean -> TreeViewState -> TreeViewState
withSearchable s state = state { searchable = s }

-- | Enable/disable inline editing
withEditable :: Boolean -> TreeViewState -> TreeViewState
withEditable e state = state { editable = e }
