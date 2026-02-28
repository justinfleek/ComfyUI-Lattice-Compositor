-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // treeview // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Types — Core type definitions for the TreeView compound.
-- |
-- | ## Architecture
-- |
-- | This module defines the atomic and molecular types that compose into
-- | tree view state and configuration. No rendering logic — pure types.
-- |
-- | ## Type Hierarchy
-- |
-- | **Atoms** (bounded primitives):
-- | - NodeId, Depth, SelectionMode, CheckState, DropPosition
-- |
-- | **Molecules** (composed atoms):
-- | - NodeIcon, TreePath
-- |
-- | **Compounds** (full configurations):
-- | - TreeViewConfig (assembled from molecules)
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Data.Maybe (Maybe)

module Hydrogen.Element.Compound.TreeView.Types
  ( -- * Node Identifier
    NodeId
  , nodeId
  , unwrapNodeId
  , rootNodeId
  
  -- * Depth
  , Depth
  , depth
  , unwrapDepth
  , rootDepth
  , incrementDepth
  
  -- * Selection Mode
  , SelectionMode
      ( SingleSelect
      , MultiSelect
      , NoSelect
      )
  
  -- * Check State
  , CheckState
      ( Unchecked
      , Checked
      , Indeterminate
      )
  , toggleCheckState
  , isChecked
  , isIndeterminate
  
  -- * Drop Position
  , DropPosition
      ( DropBefore
      , DropAfter
      , DropInside
      )
  
  -- * Node Icon
  , NodeIcon
      ( IconFolder
      , IconFolderOpen
      , IconFile
      , IconFileText
      , IconFileCode
      , IconFileImage
      , IconFileVideo
      , IconFileAudio
      , IconFileArchive
      , IconFileConfig
      , IconDatabase
      , IconGit
      , IconPackage
      , IconCustom
      )
  , iconToEmoji
  , iconToAria
  
  -- * Tree Path
  , TreePath
  , treePath
  , unwrapTreePath
  , emptyPath
  , appendToPath
  , parentPath
  , isAncestorOf
  , isDescendantOf
  , pathDepth
  
  -- * Messages
  , TreeViewMsg
      ( ToggleExpand
      , SelectNode
      , DeselectNode
      , ToggleCheck
      , SetFocus
      , ClearFocus
      , BeginDrag
      , EndDrag
      , DragOver
      , DropNode
      , LoadChildren
      , SearchChange
      , NavigateUp
      , NavigateDown
      , NavigateLeft
      , NavigateRight
      , NavigateHome
      , NavigateEnd
      , ActivateNode
      -- Edit messages
      , BeginEdit
      , UpdateEditBuffer
      , ConfirmEdit
      , CancelEdit
      -- Hover messages
      , SetHover
      , ClearHover
      )
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (<>)
  , (-)
  , (+)
  , (>=)
  , (<)
  , (&&)
  , not
  , map
  , max
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String.Common (joinWith) as String

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // node id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a tree node
-- |
-- | NodeIds are opaque strings that uniquely identify nodes within a tree.
-- | They should be stable across re-renders for proper state management.
newtype NodeId = NodeId String

derive instance eqNodeId :: Eq NodeId
derive instance ordNodeId :: Ord NodeId

instance showNodeId :: Show NodeId where
  show (NodeId s) = "NodeId(" <> s <> ")"

-- | Create a node ID from a string
nodeId :: String -> NodeId
nodeId = NodeId

-- | Extract the string value from a NodeId
unwrapNodeId :: NodeId -> String
unwrapNodeId (NodeId s) = s

-- | The root node ID (empty string represents root)
rootNodeId :: NodeId
rootNodeId = NodeId ""

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // depth
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tree depth level (0 = root level)
-- |
-- | Depth is used for indentation calculations and keyboard navigation.
-- | Always non-negative.
newtype Depth = Depth Int

derive instance eqDepth :: Eq Depth
derive instance ordDepth :: Ord Depth

instance showDepth :: Show Depth where
  show (Depth d) = "Depth(" <> show d <> ")"

-- | Create a depth value, clamped to non-negative
depth :: Int -> Depth
depth d = Depth (max 0 d)

-- | Extract the integer value from a Depth
unwrapDepth :: Depth -> Int
unwrapDepth (Depth d) = d

-- | Root level depth (0)
rootDepth :: Depth
rootDepth = Depth 0

-- | Increment depth by one level
incrementDepth :: Depth -> Depth
incrementDepth (Depth d) = Depth (d + 1)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // selection mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Selection behavior for the tree
-- |
-- | - SingleSelect: Only one node can be selected at a time
-- | - MultiSelect: Multiple nodes can be selected (Ctrl+click, Shift+click)
-- | - NoSelect: Selection is disabled
data SelectionMode
  = SingleSelect
  | MultiSelect
  | NoSelect

derive instance eqSelectionMode :: Eq SelectionMode
derive instance ordSelectionMode :: Ord SelectionMode

instance showSelectionMode :: Show SelectionMode where
  show SingleSelect = "single"
  show MultiSelect = "multi"
  show NoSelect = "none"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // check state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Checkbox state for checkable trees
-- |
-- | - Unchecked: Not selected
-- | - Checked: Fully selected
-- | - Indeterminate: Partially selected (some children checked)
data CheckState
  = Unchecked
  | Checked
  | Indeterminate

derive instance eqCheckState :: Eq CheckState
derive instance ordCheckState :: Ord CheckState

instance showCheckState :: Show CheckState where
  show Unchecked = "unchecked"
  show Checked = "checked"
  show Indeterminate = "indeterminate"

-- | Toggle between checked and unchecked states
-- | Indeterminate becomes checked when toggled
toggleCheckState :: CheckState -> CheckState
toggleCheckState Unchecked = Checked
toggleCheckState Checked = Unchecked
toggleCheckState Indeterminate = Checked

-- | Check if state is fully checked
isChecked :: CheckState -> Boolean
isChecked Checked = true
isChecked Unchecked = false
isChecked Indeterminate = false

-- | Check if state is indeterminate
isIndeterminate :: CheckState -> Boolean
isIndeterminate Indeterminate = true
isIndeterminate Checked = false
isIndeterminate Unchecked = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // drop position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Position for drag-and-drop operations
-- |
-- | - DropBefore: Insert before the target node (same level)
-- | - DropAfter: Insert after the target node (same level)
-- | - DropInside: Insert as child of the target node
data DropPosition
  = DropBefore
  | DropAfter
  | DropInside

derive instance eqDropPosition :: Eq DropPosition
derive instance ordDropPosition :: Ord DropPosition

instance showDropPosition :: Show DropPosition where
  show DropBefore = "before"
  show DropAfter = "after"
  show DropInside = "inside"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // node icon
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual icons for tree nodes
-- |
-- | Built-in icons cover common file system and development use cases.
-- | CustomIcon allows arbitrary emoji or icon class.
data NodeIcon
  = IconFolder
  | IconFolderOpen
  | IconFile
  | IconFileText
  | IconFileCode
  | IconFileImage
  | IconFileVideo
  | IconFileAudio
  | IconFileArchive
  | IconFileConfig
  | IconDatabase
  | IconGit
  | IconPackage
  | IconCustom String

derive instance eqNodeIcon :: Eq NodeIcon

instance showNodeIcon :: Show NodeIcon where
  show IconFolder = "folder"
  show IconFolderOpen = "folder-open"
  show IconFile = "file"
  show IconFileText = "file-text"
  show IconFileCode = "file-code"
  show IconFileImage = "file-image"
  show IconFileVideo = "file-video"
  show IconFileAudio = "file-audio"
  show IconFileArchive = "file-archive"
  show IconFileConfig = "file-config"
  show IconDatabase = "database"
  show IconGit = "git"
  show IconPackage = "package"
  show (IconCustom s) = "custom(" <> s <> ")"

-- | Convert icon to emoji representation for rendering
iconToEmoji :: NodeIcon -> String
iconToEmoji IconFolder = "📁"
iconToEmoji IconFolderOpen = "📂"
iconToEmoji IconFile = "📄"
iconToEmoji IconFileText = "📝"
iconToEmoji IconFileCode = "💻"
iconToEmoji IconFileImage = "🖼"
iconToEmoji IconFileVideo = "🎬"
iconToEmoji IconFileAudio = "🎵"
iconToEmoji IconFileArchive = "📦"
iconToEmoji IconFileConfig = "⚙"
iconToEmoji IconDatabase = "🗄"
iconToEmoji IconGit = "🔀"
iconToEmoji IconPackage = "📦"
iconToEmoji (IconCustom s) = s

-- | Convert icon to ARIA label for accessibility
iconToAria :: NodeIcon -> String
iconToAria IconFolder = "Folder"
iconToAria IconFolderOpen = "Open folder"
iconToAria IconFile = "File"
iconToAria IconFileText = "Text file"
iconToAria IconFileCode = "Code file"
iconToAria IconFileImage = "Image file"
iconToAria IconFileVideo = "Video file"
iconToAria IconFileAudio = "Audio file"
iconToAria IconFileArchive = "Archive file"
iconToAria IconFileConfig = "Configuration file"
iconToAria IconDatabase = "Database"
iconToAria IconGit = "Git repository"
iconToAria IconPackage = "Package"
iconToAria (IconCustom _) = "Item"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // tree path
-- ═════════════════════════════════════════════════════════════════════════════

-- | Path to a node in the tree (sequence of node IDs from root)
-- |
-- | TreePath enables:
-- | - Efficient ancestor/descendant checks
-- | - Path-based node lookup
-- | - Breadcrumb rendering
newtype TreePath = TreePath (Array NodeId)

derive instance eqTreePath :: Eq TreePath
derive instance ordTreePath :: Ord TreePath

instance showTreePath :: Show TreePath where
  show (TreePath ids) = "Path(" <> String.joinWith "/" (map unwrapNodeId ids) <> ")"

-- | Create a tree path from an array of node IDs
treePath :: Array NodeId -> TreePath
treePath = TreePath

-- | Extract the array of node IDs from a TreePath
unwrapTreePath :: TreePath -> Array NodeId
unwrapTreePath (TreePath ids) = ids

-- | Empty path (root level)
emptyPath :: TreePath
emptyPath = TreePath []

-- | Append a node ID to a path
appendToPath :: NodeId -> TreePath -> TreePath
appendToPath nid (TreePath ids) = TreePath (Array.snoc ids nid)

-- | Get the parent path (remove last segment)
parentPath :: TreePath -> Maybe TreePath
parentPath (TreePath ids) = 
  case Array.init ids of
    Just parent -> Just (TreePath parent)
    Nothing -> Nothing

-- | Check if one path is an ancestor of another
isAncestorOf :: TreePath -> TreePath -> Boolean
isAncestorOf (TreePath ancestor) (TreePath descendant) =
  let ancestorLen = Array.length ancestor
      descendantLen = Array.length descendant
  in ancestorLen < descendantLen && Array.take ancestorLen descendant == ancestor

-- | Check if one path is a descendant of another
isDescendantOf :: TreePath -> TreePath -> Boolean
isDescendantOf descendant ancestor = isAncestorOf ancestor descendant

-- | Get the depth of a path (number of segments)
pathDepth :: TreePath -> Depth
pathDepth (TreePath ids) = Depth (Array.length ids)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // messages
-- ═════════════════════════════════════════════════════════════════════════════

-- | Messages the TreeView can produce
-- |
-- | These are the only ways to interact with tree view state.
-- | The update function in the application handles these messages.
data TreeViewMsg
  = ToggleExpand NodeId                                -- ^ Toggle expand/collapse
  | SelectNode NodeId                                  -- ^ Select a node
  | DeselectNode NodeId                                -- ^ Deselect a node
  | ToggleCheck NodeId                                 -- ^ Toggle checkbox
  | SetFocus NodeId                                    -- ^ Set keyboard focus
  | ClearFocus                                         -- ^ Clear keyboard focus
  | BeginDrag NodeId                                   -- ^ Start dragging a node
  | EndDrag                                            -- ^ End drag operation
  | DragOver NodeId DropPosition                       -- ^ Dragging over a node
  | DropNode NodeId NodeId DropPosition                -- ^ Drop source onto target
  | LoadChildren NodeId                                -- ^ Request lazy load
  | SearchChange String                                -- ^ Search query changed
  | NavigateUp                                         -- ^ Arrow up key
  | NavigateDown                                       -- ^ Arrow down key
  | NavigateLeft                                       -- ^ Arrow left (collapse)
  | NavigateRight                                      -- ^ Arrow right (expand)
  | NavigateHome                                       -- ^ Home key (first node)
  | NavigateEnd                                        -- ^ End key (last node)
  | ActivateNode NodeId                                -- ^ Enter/Space on node
  -- Inline edit messages
  | BeginEdit NodeId                                   -- ^ Start editing a node label
  | UpdateEditBuffer String                            -- ^ Update the edit text buffer
  | ConfirmEdit                                        -- ^ Confirm edit (Enter key)
  | CancelEdit                                         -- ^ Cancel edit (Escape key)
  -- Hover messages
  | SetHover NodeId                                    -- ^ Mouse entered a node
  | ClearHover                                         -- ^ Mouse left the tree

derive instance eqTreeViewMsg :: Eq TreeViewMsg

instance showTreeViewMsg :: Show TreeViewMsg where
  show (ToggleExpand nid) = "ToggleExpand(" <> show nid <> ")"
  show (SelectNode nid) = "SelectNode(" <> show nid <> ")"
  show (DeselectNode nid) = "DeselectNode(" <> show nid <> ")"
  show (ToggleCheck nid) = "ToggleCheck(" <> show nid <> ")"
  show (SetFocus nid) = "SetFocus(" <> show nid <> ")"
  show ClearFocus = "ClearFocus"
  show (BeginDrag nid) = "BeginDrag(" <> show nid <> ")"
  show EndDrag = "EndDrag"
  show (DragOver nid pos) = "DragOver(" <> show nid <> ", " <> show pos <> ")"
  show (DropNode src tgt pos) = "DropNode(" <> show src <> " -> " <> show tgt <> ", " <> show pos <> ")"
  show (LoadChildren nid) = "LoadChildren(" <> show nid <> ")"
  show (SearchChange q) = "SearchChange(" <> q <> ")"
  show NavigateUp = "NavigateUp"
  show NavigateDown = "NavigateDown"
  show NavigateLeft = "NavigateLeft"
  show NavigateRight = "NavigateRight"
  show NavigateHome = "NavigateHome"
  show NavigateEnd = "NavigateEnd"
  show (ActivateNode nid) = "ActivateNode(" <> show nid <> ")"
  show (BeginEdit nid) = "BeginEdit(" <> show nid <> ")"
  show (UpdateEditBuffer text) = "UpdateEditBuffer(\"" <> text <> "\")"
  show ConfirmEdit = "ConfirmEdit"
  show CancelEdit = "CancelEdit"
  show (SetHover nid) = "SetHover(" <> show nid <> ")"
  show ClearHover = "ClearHover"
