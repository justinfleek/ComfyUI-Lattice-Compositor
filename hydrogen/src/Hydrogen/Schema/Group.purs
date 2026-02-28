-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // schema // group
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Group — Hierarchical grouping for Schema entities.
-- |
-- | ## Purpose
-- |
-- | At billion-agent scale, entities need to be organized into hierarchies:
-- | - Color palettes with semantic groupings (primary, secondary, accent)
-- | - Typography scales (heading, body, caption)
-- | - Component libraries (atoms, molecules, compounds)
-- |
-- | Groups provide:
-- | 1. **Hierarchical organization** — Parent-child relationships
-- | 2. **Named collections** — Human/agent-readable labels
-- | 3. **Ordered members** — Deterministic traversal order
-- | 4. **UUID5 identity** — Content-addressed group IDs
-- |
-- | ## Design
-- |
-- | Groups form a forest (multiple roots allowed). Each group:
-- | - Has a unique ID (deterministic from path)
-- | - Has a name (human-readable)
-- | - Contains ordered items
-- | - May have a parent group
-- |
-- | ## Invariants
-- |
-- | 1. **Acyclic**: A group cannot be its own ancestor
-- | 2. **Unique paths**: Each path through the hierarchy is unique
-- | 3. **Determinism**: Same structure → same UUIDs
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | -- Create a color palette hierarchy
-- | let palette = groupWithChildren "colors" "Brand Colors"
-- |       [ leaf "primary" "Primary" [swatch1, swatch2]
-- |       , leaf "secondary" "Secondary" [swatch3]
-- |       , groupWithChildren "accents" "Accents"
-- |           [ leaf "warm" "Warm" [orange, red]
-- |           , leaf "cool" "Cool" [blue, teal]
-- |           ]
-- |       ]
-- | ```

module Hydrogen.Schema.Group
  ( -- * Core Types
    Group
  , GroupId
  , GroupRecord
  
  -- * Construction
  , mkGroup
  , leaf
  , groupWithChildren
  , emptyGroup
  
  -- * Accessors
  , groupId
  , groupName
  , groupSlug
  , groupItems
  , groupChildren
  , groupParent
  , unwrapGroup
  
  -- * Modification
  , addItem
  , addItems
  , removeItem
  , addChild
  , removeChild
  , setGroupName
  , setParent
  
  -- * Traversal
  , allItems
  , allGroups
  , ancestors
  , descendants
  , groupDepth
  , groupPath
  , pathString
  
  -- * Queries
  , isEmpty
  , isLeaf
  , isRoot
  , hasItem
  , findGroup
  , findItem
  
  -- * Forest Operations
  , Forest
  , emptyForest
  , addRoot
  , removeRoot
  , forestRoots
  , forestAllItems
  , forestAllGroups
  , findGroupInForest
  
  -- * GroupId Utilities
  , unwrapGroupId
  , makeGroupId
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , map
  , ($)
  , (+)
  , (&&)
  , (||)
  , (==)
  , (/=)
  , (<>)
  )

import Data.Array (length, index, foldl, snoc, filter, concatMap, null, cons, head, findIndex) as Array
import Data.Maybe (Maybe(Just, Nothing), isNothing, isJust)

import Hydrogen.Schema.Attestation.UUID5 as UUID5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // group id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deterministic identifier for a group.
-- |
-- | Generated from the group's path in the hierarchy.
-- | Same path → same GroupId (always).
newtype GroupId = GroupId String

derive instance eqGroupId :: Eq GroupId
derive instance ordGroupId :: Ord GroupId

instance showGroupId :: Show GroupId where
  show (GroupId gid) = "group:" <> gid

-- | Namespace for group UUIDs
nsGroup :: UUID5.UUID5
nsGroup = UUID5.uuid5 UUID5.nsElement "hydrogen.schema.group"

-- | Create GroupId from path components
makeGroupId :: Array String -> GroupId
makeGroupId pathComponents =
  let 
    pathStr = Array.foldl (\acc s -> if acc == "" then s else acc <> "/" <> s) "" pathComponents
    uuid = UUID5.uuid5 nsGroup pathStr
  in GroupId (UUID5.toString uuid)

-- | Unwrap GroupId to string
unwrapGroupId :: GroupId -> String
unwrapGroupId (GroupId gid) = gid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // group
-- ═════════════════════════════════════════════════════════════════════════════

-- | The internal record structure of a group.
type GroupRecord a =
  { id :: GroupId
  , name :: String
  , slug :: String
  , items :: Array a
  , children :: Array (Group a)
  , parent :: Maybe GroupId
  }

-- | A hierarchical group of items.
-- |
-- | Groups can contain:
-- | - Ordered items of type `a`
-- | - Child groups (forming a tree)
-- |
-- | The group's ID is deterministically derived from its path.
newtype Group a = Group (GroupRecord a)

derive instance eqGroup :: Eq a => Eq (Group a)

instance showGroup :: Show a => Show (Group a) where
  show (Group g) = "Group(" <> g.name <> ")"

-- | Unwrap a group to access its record
unwrapGroup :: forall a. Group a -> GroupRecord a
unwrapGroup (Group g) = g

-- | Create an empty group with a name
-- |
-- | The slug is used for path construction.
-- | The ID is derived from the slug path.
emptyGroup :: forall a. String -> String -> Group a
emptyGroup slug name = Group
  { id: makeGroupId [slug]
  , name: name
  , slug: slug
  , items: []
  , children: []
  , parent: Nothing
  }

-- | Create a leaf group (no children, has items)
leaf :: forall a. String -> String -> Array a -> Group a
leaf slug name items = Group
  { id: makeGroupId [slug]
  , name: name
  , slug: slug
  , items: items
  , children: []
  , parent: Nothing
  }

-- | Create a group with a name (convenience for creating branch groups)
mkGroup :: forall a. String -> String -> Group a
mkGroup = emptyGroup

-- | Create a group with children (automatically sets parent references)
groupWithChildren :: forall a. String -> String -> Array (Group a) -> Group a
groupWithChildren slug name childGroups =
  let
    parentId = makeGroupId [slug]
    updatedChildren = map (setChildParent parentId slug) childGroups
  in Group
    { id: parentId
    , name: name
    , slug: slug
    , items: []
    , children: updatedChildren
    , parent: Nothing
    }

-- | Set a child's parent and update its ID based on parent path
setChildParent :: forall a. GroupId -> String -> Group a -> Group a
setChildParent pid parentSlug (Group child) =
  let
    newPath = [parentSlug, child.slug]
    newId = makeGroupId newPath
    updatedChildren = map (setChildParent newId (parentSlug <> "/" <> child.slug)) child.children
  in Group (child { id = newId, parent = Just pid, children = updatedChildren })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the group's ID
groupId :: forall a. Group a -> GroupId
groupId (Group g) = g.id

-- | Get the group's name
groupName :: forall a. Group a -> String
groupName (Group g) = g.name

-- | Get the group's slug
groupSlug :: forall a. Group a -> String
groupSlug (Group g) = g.slug

-- | Get the group's items
groupItems :: forall a. Group a -> Array a
groupItems (Group g) = g.items

-- | Get the group's children
groupChildren :: forall a. Group a -> Array (Group a)
groupChildren (Group g) = g.children

-- | Get the group's parent ID
groupParent :: forall a. Group a -> Maybe GroupId
groupParent (Group g) = g.parent

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // modification
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add an item to a group
addItem :: forall a. a -> Group a -> Group a
addItem item (Group g) = Group (g { items = Array.snoc g.items item })

-- | Add multiple items to a group
addItems :: forall a. Array a -> Group a -> Group a
addItems items (Group g) = Group (g { items = Array.foldl (\acc i -> Array.snoc acc i) g.items items })

-- | Remove an item from a group (by equality)
removeItem :: forall a. Eq a => a -> Group a -> Group a
removeItem item (Group g) = Group (g { items = Array.filter (\i -> i /= item) g.items })

-- | Add a child group
addChild :: forall a. Group a -> Group a -> Group a
addChild (Group child) (Group parent) =
  let
    childWithParent = Group (child { parent = Just parent.id })
  in
    Group (parent { children = Array.snoc parent.children childWithParent })

-- | Remove a child group by ID
removeChild :: forall a. GroupId -> Group a -> Group a
removeChild childId (Group parent) =
  Group (parent { children = Array.filter (\c -> groupId c /= childId) parent.children })

-- | Set the group's name
setGroupName :: forall a. String -> Group a -> Group a
setGroupName name (Group g) = Group (g { name = name })

-- | Set the group's parent (for tree restructuring)
setParent :: forall a. Maybe GroupId -> Group a -> Group a
setParent pid (Group g) = Group (g { parent = pid })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // traversal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all items in a group and its descendants
allItems :: forall a. Group a -> Array a
allItems (Group g) =
  let
    childItems = Array.concatMap allItems g.children
  in
    Array.foldl (\acc i -> Array.snoc acc i) g.items childItems

-- | Get all groups in the tree (this group and all descendants)
allGroups :: forall a. Group a -> Array (Group a)
allGroups grp =
  let
    (Group g) = grp
    childGroups = Array.concatMap allGroups g.children
  in
    Array.cons grp childGroups

-- | Get the ancestor chain (parent, grandparent, ..., root)
-- |
-- | Requires the full forest to traverse upward.
ancestors :: forall a. Group a -> Forest a -> Array (Group a)
ancestors (Group g) forest =
  case g.parent of
    Nothing -> []
    Just pid ->
      case findGroupInForest pid forest of
        Nothing -> []
        Just parent -> Array.cons parent (ancestors parent forest)

-- | Get all descendant groups
descendants :: forall a. Group a -> Array (Group a)
descendants (Group g) = Array.concatMap allGroups g.children

-- | Get the depth of a group in the hierarchy (0 = root)
groupDepth :: forall a. Group a -> Forest a -> Int
groupDepth grp forest = Array.length (ancestors grp forest)

-- | Get the path from root to this group
groupPath :: forall a. Group a -> Forest a -> Array (Group a)
groupPath grp forest =
  let ancs = ancestors grp forest
  in Array.snoc (reverseArray ancs) grp

-- | Get the path as a string (slug/slug/slug)
pathString :: forall a. Group a -> Forest a -> String
pathString grp forest =
  let 
    pathGroups = groupPath grp forest
    slugs = map groupSlug pathGroups
  in
    Array.foldl (\acc s -> if acc == "" then s else acc <> "/" <> s) "" slugs

-- | Reverse an array (helper)
reverseArray :: forall b. Array b -> Array b
reverseArray arr =
  Array.foldl (\acc item -> Array.cons item acc) [] arr

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a group has no items
isEmpty :: forall a. Group a -> Boolean
isEmpty (Group g) = Array.null g.items

-- | Check if a group is a leaf (no children)
isLeaf :: forall a. Group a -> Boolean
isLeaf (Group g) = Array.null g.children

-- | Check if a group is a root (no parent)
isRoot :: forall a. Group a -> Boolean
isRoot (Group g) = isNothing g.parent

-- | Check if a group contains an item
hasItem :: forall a. Eq a => a -> Group a -> Boolean
hasItem item (Group g) = isJust (Array.findIndex (\i -> i == item) g.items)

-- | Find a group by ID in a tree
findGroup :: forall a. GroupId -> Group a -> Maybe (Group a)
findGroup targetId grp =
  let (Group g) = grp
  in if g.id == targetId
     then Just grp
     else findInChildren g.children
  where
    findInChildren :: Array (Group a) -> Maybe (Group a)
    findInChildren children =
      case Array.head children of
        Nothing -> Nothing
        Just child ->
          case findGroup targetId child of
            Just found -> Just found
            Nothing -> findInChildren (Array.filter (\c -> groupId c /= groupId child) children)

-- | Find an item by predicate in a group and its descendants
findItem :: forall a. (a -> Boolean) -> Group a -> Maybe a
findItem pred (Group g) =
  case Array.findIndex pred g.items of
    Just idx -> Array.index g.items idx
    Nothing -> findInChildren g.children
  where
    findInChildren :: Array (Group a) -> Maybe a
    findInChildren children =
      case Array.head children of
        Nothing -> Nothing
        Just child ->
          case findItem pred child of
            Just found -> Just found
            Nothing -> findInChildren (Array.filter (\c -> groupId c /= groupId child) children)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // forest operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | A forest is a collection of root groups.
-- |
-- | Multiple independent trees can exist in a forest.
type Forest a = Array (Group a)

-- | Empty forest
emptyForest :: forall a. Forest a
emptyForest = []

-- | Add a root group to the forest
addRoot :: forall a. Group a -> Forest a -> Forest a
addRoot grp forest = Array.snoc forest (setParent Nothing grp)

-- | Remove a root group from the forest
removeRoot :: forall a. GroupId -> Forest a -> Forest a
removeRoot gid forest = Array.filter (\grp -> groupId grp /= gid) forest

-- | Get all root groups in the forest
forestRoots :: forall a. Forest a -> Array (Group a)
forestRoots forest = forest

-- | Get all items in the entire forest
forestAllItems :: forall a. Forest a -> Array a
forestAllItems forest = Array.concatMap allItems forest

-- | Get all groups in the entire forest
forestAllGroups :: forall a. Forest a -> Array (Group a)
forestAllGroups forest = Array.concatMap allGroups forest

-- | Find a group by ID anywhere in the forest
findGroupInForest :: forall a. GroupId -> Forest a -> Maybe (Group a)
findGroupInForest gid forest =
  case Array.head forest of
    Nothing -> Nothing
    Just root ->
      case findGroup gid root of
        Just found -> Just found
        Nothing -> findGroupInForest gid (Array.filter (\grp -> groupId grp /= groupId root) forest)
