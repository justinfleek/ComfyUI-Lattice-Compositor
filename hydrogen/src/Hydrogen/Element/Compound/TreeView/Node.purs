-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // treeview // node
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Node — Data structure and operations for tree nodes.
-- |
-- | ## Architecture
-- |
-- | Nodes are the fundamental building block of trees. Each node contains:
-- | - Identity (NodeId)
-- | - Display data (label, icon)
-- | - Structural data (children, parent reference)
-- | - Metadata (disabled, has lazy children, etc.)
-- |
-- | ## Non-Recursive Design
-- |
-- | Nodes do NOT contain child Node values directly. Instead, children are
-- | referenced by NodeId and looked up in a flat map. This enables:
-- | - Efficient updates (O(1) lookup)
-- | - Easy serialization
-- | - No infinite recursion concerns
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Types (NodeId, NodeIcon, CheckState, Depth, TreePath)

module Hydrogen.Element.Compound.TreeView.Node
  ( -- * Node Data
    TreeNode
  , treeNode
  , nodeId
  , nodeLabel
  , nodeIcon
  , nodeChildren
  , nodeParent
  , nodeDisabled
  , nodeHasChildren
  
  -- * Node Builders
  , node
  , leafNode
  , branchNode
  , withLabel
  , withIcon
  , withChildren
  , withParent
  , withDisabled
  , markHasChildren
  
  -- * Tree Structure
  , Tree
  , emptyTree
  , insertNode
  , removeNode
  , getNode
  , hasNode
  , updateNode
  , treeNodes
  , treeSize
  
  -- * Tree Queries
  , rootNodes
  , childNodes
  , parentNode
  , ancestorNodes
  , descendantNodes
  , siblingNodes
  , nodeDepth
  , nodePath
  
  -- * Tree Operations
  , moveNode
  , isAncestorOf
  , isDescendantOf
  , flattenTree
  , filterTree
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (==)
  , (/=)
  , (<>)
  , (||)
  , not
  , map
  , flip
  , (<<<)
  , bind
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing), isJust)
import Data.Map (Map)
import Data.Map as Map
import Data.Foldable (foldl)

import Hydrogen.Element.Compound.TreeView.Types
  ( NodeId
  , NodeIcon
  , Depth
  , incrementDepth
  , rootDepth
  , TreePath
  , appendToPath
  , emptyPath
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // tree node
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single node in the tree
-- |
-- | Contains all data needed to render and interact with the node.
-- | Children are referenced by ID, not embedded directly.
type TreeNode =
  { id :: NodeId                    -- ^ Unique identifier
  , label :: String                 -- ^ Display text
  , icon :: Maybe NodeIcon          -- ^ Optional icon
  , children :: Array NodeId        -- ^ Child node IDs (ordered)
  , parent :: Maybe NodeId          -- ^ Parent node ID (Nothing for root)
  , disabled :: Boolean             -- ^ Whether node is interactive
  , hasChildren :: Boolean          -- ^ True if has (or may have) children
  }

-- | Create a tree node with full specification
treeNode ::
  { id :: NodeId
  , label :: String
  , icon :: Maybe NodeIcon
  , children :: Array NodeId
  , parent :: Maybe NodeId
  , disabled :: Boolean
  , hasChildren :: Boolean
  } -> TreeNode
treeNode spec = spec

-- | Get node's ID
nodeId :: TreeNode -> NodeId
nodeId n = n.id

-- | Get node's label
nodeLabel :: TreeNode -> String
nodeLabel n = n.label

-- | Get node's icon
nodeIcon :: TreeNode -> Maybe NodeIcon
nodeIcon n = n.icon

-- | Get node's children IDs
nodeChildren :: TreeNode -> Array NodeId
nodeChildren n = n.children

-- | Get node's parent ID
nodeParent :: TreeNode -> Maybe NodeId
nodeParent n = n.parent

-- | Check if node is disabled
nodeDisabled :: TreeNode -> Boolean
nodeDisabled n = n.disabled

-- | Check if node has (or may have) children
nodeHasChildren :: TreeNode -> Boolean
nodeHasChildren n = n.hasChildren || not (Array.null n.children)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // node builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a basic node with just ID and label
node :: NodeId -> String -> TreeNode
node nid lbl =
  { id: nid
  , label: lbl
  , icon: Nothing
  , children: []
  , parent: Nothing
  , disabled: false
  , hasChildren: false
  }

-- | Create a leaf node (no children)
leafNode :: NodeId -> String -> TreeNode
leafNode = node

-- | Create a branch node (has children)
branchNode :: NodeId -> String -> Array NodeId -> TreeNode
branchNode nid lbl childIds =
  (node nid lbl) { children = childIds, hasChildren = true }

-- | Set node's label
withLabel :: String -> TreeNode -> TreeNode
withLabel lbl n = n { label = lbl }

-- | Set node's icon
withIcon :: NodeIcon -> TreeNode -> TreeNode
withIcon ico n = n { icon = Just ico }

-- | Set node's children
withChildren :: Array NodeId -> TreeNode -> TreeNode
withChildren childIds n = n { children = childIds, hasChildren = true }

-- | Set node's parent
withParent :: NodeId -> TreeNode -> TreeNode
withParent pid n = n { parent = Just pid }

-- | Set node's disabled state
withDisabled :: Boolean -> TreeNode -> TreeNode
withDisabled d n = n { disabled = d }

-- | Mark node as having children (for lazy loading)
markHasChildren :: Boolean -> TreeNode -> TreeNode
markHasChildren has n = n { hasChildren = has }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // tree structure
-- ═════════════════════════════════════════════════════════════════════════════

-- | A tree is a map from NodeId to TreeNode
-- |
-- | This flat structure enables O(1) lookup and update.
newtype Tree = Tree (Map NodeId TreeNode)

derive instance eqTree :: Eq Tree

instance showTree :: Show Tree where
  show (Tree m) = "Tree(" <> show (Map.size m) <> " nodes)"

-- | Empty tree
emptyTree :: Tree
emptyTree = Tree Map.empty

-- | Insert a node into the tree
-- |
-- | If a node with the same ID exists, it is replaced.
insertNode :: TreeNode -> Tree -> Tree
insertNode n (Tree m) = Tree (Map.insert n.id n m)

-- | Remove a node from the tree
-- |
-- | Note: This does NOT remove children or update parent references.
-- | Use moveNode for structural changes.
removeNode :: NodeId -> Tree -> Tree
removeNode nid (Tree m) = Tree (Map.delete nid m)

-- | Get a node by ID
getNode :: NodeId -> Tree -> Maybe TreeNode
getNode nid (Tree m) = Map.lookup nid m

-- | Check if a node exists
hasNode :: NodeId -> Tree -> Boolean
hasNode nid (Tree m) = Map.member nid m

-- | Update a node in the tree
updateNode :: NodeId -> (TreeNode -> TreeNode) -> Tree -> Tree
updateNode nid f (Tree m) = Tree (Map.update (Just <<< f) nid m)

-- | Get all nodes as array
treeNodes :: Tree -> Array TreeNode
treeNodes (Tree m) = Array.fromFoldable (Map.values m)

-- | Get tree size (number of nodes)
treeSize :: Tree -> Int
treeSize (Tree m) = Map.size m

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // tree queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all root nodes (nodes without a parent)
rootNodes :: Tree -> Array TreeNode
rootNodes tree =
  Array.filter (\n -> not (isJust n.parent)) (treeNodes tree)

-- | Get children of a node
childNodes :: NodeId -> Tree -> Array TreeNode
childNodes nid tree =
  case getNode nid tree of
    Nothing -> []
    Just n -> Array.mapMaybe (flip getNode tree) n.children

-- | Get parent of a node
parentNode :: NodeId -> Tree -> Maybe TreeNode
parentNode nid tree = do
  n <- getNode nid tree
  pid <- n.parent
  getNode pid tree

-- | Get all ancestors of a node (parent, grandparent, etc.)
ancestorNodes :: NodeId -> Tree -> Array TreeNode
ancestorNodes nid tree = go nid []
  where
    go :: NodeId -> Array TreeNode -> Array TreeNode
    go currentId acc =
      case parentNode currentId tree of
        Nothing -> acc
        Just p -> go p.id (Array.snoc acc p)

-- | Get all descendants of a node (children, grandchildren, etc.)
descendantNodes :: NodeId -> Tree -> Array TreeNode
descendantNodes nid tree =
  case getNode nid tree of
    Nothing -> []
    Just _ ->
      let
        children = childNodes nid tree
        childDescendants = Array.concatMap (\c -> descendantNodes c.id tree) children
      in
        children <> childDescendants

-- | Get siblings of a node (same parent, excluding self)
siblingNodes :: NodeId -> Tree -> Array TreeNode
siblingNodes nid tree =
  case getNode nid tree of
    Nothing -> []
    Just n ->
      case n.parent of
        Nothing ->
          -- Root node: siblings are other root nodes
          Array.filter (\r -> r.id /= nid) (rootNodes tree)
        Just pid ->
          -- Has parent: siblings are parent's other children
          Array.filter (\c -> c.id /= nid) (childNodes pid tree)

-- | Calculate depth of a node in the tree
nodeDepth :: NodeId -> Tree -> Depth
nodeDepth nid tree = go nid rootDepth
  where
    go :: NodeId -> Depth -> Depth
    go currentId currentDepth =
      case parentNode currentId tree of
        Nothing -> currentDepth
        Just p -> go p.id (incrementDepth currentDepth)

-- | Calculate full path to a node
nodePath :: NodeId -> Tree -> TreePath
nodePath nid tree =
  let
    ancestors = ancestorNodes nid tree
    ancestorIds = map (\n -> n.id) (Array.reverse ancestors)
  in
    case getNode nid tree of
      Nothing -> emptyPath
      Just _ -> foldl (flip appendToPath) emptyPath (Array.snoc ancestorIds nid)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // tree operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Move a node to a new parent
-- |
-- | Updates both the node's parent reference and the old/new parent's children.
moveNode :: NodeId -> Maybe NodeId -> Tree -> Tree
moveNode nid newParent tree =
  case getNode nid tree of
    Nothing -> tree
    Just n ->
      let
        -- Remove from old parent's children
        tree1 = case n.parent of
          Nothing -> tree
          Just oldPid -> updateNode oldPid (removeChild nid) tree
        
        -- Update node's parent
        tree2 = updateNode nid (\nd -> nd { parent = newParent }) tree1
        
        -- Add to new parent's children
        tree3 = case newParent of
          Nothing -> tree2
          Just newPid -> updateNode newPid (addChild nid) tree2
      in
        tree3
  where
    removeChild :: NodeId -> TreeNode -> TreeNode
    removeChild childId nd = nd { children = Array.filter (\c -> c /= childId) nd.children }
    
    addChild :: NodeId -> TreeNode -> TreeNode
    addChild childId nd = nd { children = Array.snoc nd.children childId }

-- | Check if one node is an ancestor of another
isAncestorOf :: NodeId -> NodeId -> Tree -> Boolean
isAncestorOf ancestorId descendantId tree =
  let
    ancestors = ancestorNodes descendantId tree
  in
    Array.any (\a -> a.id == ancestorId) ancestors

-- | Check if one node is a descendant of another
isDescendantOf :: NodeId -> NodeId -> Tree -> Boolean
isDescendantOf descendantId ancestorId tree =
  isAncestorOf ancestorId descendantId tree

-- | Flatten tree to array in depth-first order
-- |
-- | Useful for keyboard navigation and rendering.
flattenTree :: Tree -> Array TreeNode
flattenTree tree =
  let
    roots = rootNodes tree
  in
    Array.concatMap (flattenNode tree) roots
  where
    flattenNode :: Tree -> TreeNode -> Array TreeNode
    flattenNode t n =
      let
        children = childNodes n.id t
        flatChildren = Array.concatMap (flattenNode t) children
      in
        Array.cons n flatChildren

-- | Filter tree nodes by predicate
-- |
-- | Returns nodes matching predicate and their ancestors (to maintain structure).
filterTree :: (TreeNode -> Boolean) -> Tree -> Array TreeNode
filterTree predicate tree =
  let
    matching = Array.filter predicate (treeNodes tree)
    matchingIds = map (\n -> n.id) matching
    
    -- Get ancestors of matching nodes
    ancestorIds = Array.concatMap (\nid -> map (\a -> a.id) (ancestorNodes nid tree)) matchingIds
    
    -- Combine and deduplicate
    allIds = Array.nub (matchingIds <> ancestorIds)
  in
    Array.mapMaybe (\nid -> getNode nid tree) allIds
