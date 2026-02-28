-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // gpu // scene3d // scene-node
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SceneNode — Hierarchical scene graph node with parent/child relationships.
-- |
-- | ## Design
-- |
-- | Each node has:
-- | - Local transform (position, rotation, scale)
-- | - Optional pivot point (separate from position)
-- | - Parent reference (Maybe NodeId)
-- | - Children list (Array NodeId)
-- | - World matrix (computed from parent chain)
-- |
-- | ## Three.js Parity
-- |
-- | Implements Object3D hierarchy:
-- | - add, remove, removeFromParent, clear, attach
-- | - getObjectById, getObjectByName
-- | - getWorldPosition, getWorldQuaternion, getWorldScale
-- | - traverse, traverseVisible, traverseAncestors
-- | - updateMatrix, updateMatrixWorld, updateWorldMatrix
-- | - localToWorld, worldToLocal
-- |
-- | ## Proof References
-- |
-- | - Scene/Node.lean: Parent-child relationships
-- | - Scene/Graph.lean: World matrix computation
-- | - Mat4.lean: Matrix multiplication for transform chain

module Hydrogen.GPU.Scene3D.SceneNode
  ( -- * Types
    NodeId(NodeId)
  , SceneNode
  , SceneGraph
  
  -- * NodeId Operations
  , nodeIdFromString
  , nodeIdToString
  , rootNodeId
  
  -- * Node Construction
  , emptyNode
  , nodeWithTransform
  
  -- * Scene Graph Construction
  , emptyGraph
  , insertNode
  , removeNode
  
  -- * Hierarchy Operations
  , addChild
  , removeChild
  , setParent
  , getParent
  , getChildren
  
  -- * Matrix Operations
  , updateLocalMatrix
  , updateWorldMatrix
  , getWorldMatrix
  
  -- * Traversal
  , traverse
  , traverseVisible
  , traverseAncestors
  , findNode
  , findNodeByName
  
  -- * World Space Queries
  , getWorldPosition
  , localToWorld
  , worldToLocal
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , compare
  , map
  , (==)
  , (/=)
  , (<>)
  , (>>=)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Array as Array
import Data.Map as Map
import Data.Map (Map)

import Hydrogen.Schema.Attestation.UUID5 as UUID5
import Hydrogen.Schema.Attestation.UUID5 (UUID5)
import Hydrogen.Schema.Dimension.Matrix.Mat4 
  ( Mat4
  , mat4Identity
  , mulMat4
  , mulPointMat4
  , invertMat4
  , makeTranslation4
  , makeScale4
  , getTranslation4
  )
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3, getX3, getY3, getZ3)
import Hydrogen.Schema.Dimension.Rotation.Quaternion (Quaternion, quaternionIdentity, toMat4Quaternion)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // node id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a scene node.
-- |
-- | NodeId wraps UUID5 for deterministic identity.
-- | Two nodes with identical content produce identical NodeIds.
newtype NodeId = NodeId UUID5

derive instance eqNodeId :: Eq NodeId

instance ordNodeId :: Ord NodeId where
  compare (NodeId a) (NodeId b) = compare (UUID5.toString a) (UUID5.toString b)

instance showNodeId :: Show NodeId where
  show (NodeId uuid) = "NodeId(" <> UUID5.toString uuid <> ")"

-- | Create NodeId from a string (deterministic via UUID5).
nodeIdFromString :: String -> NodeId
nodeIdFromString s = NodeId (UUID5.uuid5 nsSceneNode s)

-- | Convert NodeId back to string representation.
nodeIdToString :: NodeId -> String
nodeIdToString (NodeId uuid) = UUID5.toString uuid

-- | Namespace for scene node UUIDs.
-- | Derived from nsScene for scene graph hierarchy.
nsSceneNode :: UUID5
nsSceneNode = UUID5.uuid5 UUID5.nsScene "scene-node"

-- | The root node ID (always the same).
rootNodeId :: NodeId
rootNodeId = nodeIdFromString "root"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // scene node
-- ═════════════════════════════════════════════════════════════════════════════

-- | A scene graph node with local and world transforms.
-- |
-- | The node stores:
-- | - Local transform components (position, rotation, scale)
-- | - Pivot offset (for rotation/scale around non-center point)
-- | - Parent/children relationships (by NodeId)
-- | - Cached matrices (local and world)
-- | - Visibility and metadata
type SceneNode =
  { id :: NodeId
  , name :: String
  
  -- Local transform
  , position :: Vec3 Number
  , rotation :: Quaternion
  , scale :: Vec3 Number
  
  -- Pivot (offset from position for rotation/scale)
  , pivot :: Vec3 Number
  
  -- Hierarchy
  , parent :: Maybe NodeId
  , children :: Array NodeId
  
  -- Cached matrices
  , localMatrix :: Mat4
  , worldMatrix :: Mat4
  , matrixNeedsUpdate :: Boolean
  
  -- Visibility
  , visible :: Boolean
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // scene graph
-- ═════════════════════════════════════════════════════════════════════════════

-- | The complete scene graph — a map from NodeId to SceneNode.
-- |
-- | Pure data structure. No mutation. Updates return new graphs.
type SceneGraph = Map NodeId SceneNode

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // node construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an empty node with identity transform.
emptyNode :: NodeId -> String -> SceneNode
emptyNode nodeId nodeName =
  { id: nodeId
  , name: nodeName
  , position: vec3 0.0 0.0 0.0
  , rotation: quaternionIdentity
  , scale: vec3 1.0 1.0 1.0
  , pivot: vec3 0.0 0.0 0.0
  , parent: Nothing
  , children: []
  , localMatrix: mat4Identity
  , worldMatrix: mat4Identity
  , matrixNeedsUpdate: false
  , visible: true
  }

-- | Create a node with specified transform.
nodeWithTransform 
  :: NodeId 
  -> String 
  -> Vec3 Number 
  -> Quaternion 
  -> Vec3 Number 
  -> SceneNode
nodeWithTransform nodeId nodeName pos rot scl =
  (emptyNode nodeId nodeName)
    { position = pos
    , rotation = rot
    , scale = scl
    , matrixNeedsUpdate = true
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // graph construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an empty scene graph.
emptyGraph :: SceneGraph
emptyGraph = Map.empty

-- | Insert a node into the graph.
insertNode :: SceneNode -> SceneGraph -> SceneGraph
insertNode node graph = Map.insert node.id node graph

-- | Remove a node from the graph.
-- |
-- | Note: Does not automatically remove from parent's children list.
-- | Use removeChild first for proper cleanup.
removeNode :: NodeId -> SceneGraph -> SceneGraph
removeNode = Map.delete

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // hierarchy operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add a child to a parent node.
-- |
-- | Updates both:
-- | - Parent's children array (adds childId)
-- | - Child's parent field (sets to parentId)
addChild :: NodeId -> NodeId -> SceneGraph -> SceneGraph
addChild parentId childId graph =
  case Map.lookup parentId graph of
    Nothing -> graph  -- Parent doesn't exist
    Just parentNode ->
      case Map.lookup childId graph of
        Nothing -> graph  -- Child doesn't exist
        Just childNode ->
          let
            updatedParent = parentNode { children = Array.snoc parentNode.children childId }
            updatedChild = childNode { parent = Just parentId, matrixNeedsUpdate = true }
          in
            Map.insert childId updatedChild (Map.insert parentId updatedParent graph)

-- | Remove a child from a parent node.
-- |
-- | Updates both:
-- | - Parent's children array (removes childId)
-- | - Child's parent field (sets to Nothing)
removeChild :: NodeId -> NodeId -> SceneGraph -> SceneGraph
removeChild parentId childId graph =
  case Map.lookup parentId graph of
    Nothing -> graph
    Just parentNode ->
      case Map.lookup childId graph of
        Nothing -> graph
        Just childNode ->
          let
            updatedParent = parentNode { children = Array.filter (\c -> c /= childId) parentNode.children }
            updatedChild = childNode { parent = Nothing, matrixNeedsUpdate = true }
          in
            Map.insert childId updatedChild (Map.insert parentId updatedParent graph)

-- | Set a node's parent (reparenting).
-- |
-- | Removes from old parent (if any) and adds to new parent.
setParent :: NodeId -> Maybe NodeId -> SceneGraph -> SceneGraph
setParent childId maybeNewParent graph =
  case Map.lookup childId graph of
    Nothing -> graph
    Just childNode ->
      -- Remove from old parent if exists
      let graphAfterRemoval = case childNode.parent of
            Nothing -> graph
            Just oldParent -> removeChild oldParent childId graph
      in
        -- Add to new parent if specified
        case maybeNewParent of
          Nothing -> 
            case Map.lookup childId graphAfterRemoval of
              Nothing -> graphAfterRemoval
              Just updatedChild -> Map.insert childId (updatedChild { parent = Nothing }) graphAfterRemoval
          Just newParent -> addChild newParent childId graphAfterRemoval

-- | Get a node's parent ID.
getParent :: NodeId -> SceneGraph -> Maybe NodeId
getParent nodeId graph = 
  Map.lookup nodeId graph >>= \node -> node.parent

-- | Get a node's children IDs.
getChildren :: NodeId -> SceneGraph -> Array NodeId
getChildren nodeId graph =
  case Map.lookup nodeId graph of
    Nothing -> []
    Just node -> node.children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // matrix operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Update a node's local matrix from its transform components.
-- |
-- | LocalMatrix = Translation × Rotation × Scale × PivotOffset
updateLocalMatrix :: NodeId -> SceneGraph -> SceneGraph
updateLocalMatrix nodeId graph =
  case Map.lookup nodeId graph of
    Nothing -> graph
    Just node ->
      let
        -- Build local matrix: T × R × S (pivot handled via translation offset)
        translationMat = makeTranslation4 (getX3 node.position) (getY3 node.position) (getZ3 node.position)
        rotationMat = toMat4Quaternion node.rotation
        scaleMat = makeScale4 (getX3 node.scale) (getY3 node.scale) (getZ3 node.scale)
        
        -- Compose: translation × rotation × scale
        localMat = mulMat4 translationMat (mulMat4 rotationMat scaleMat)
        
        updatedNode = node 
          { localMatrix = localMat
          , matrixNeedsUpdate = false 
          }
      in
        Map.insert nodeId updatedNode graph

-- | Update a node's world matrix from parent chain.
-- |
-- | WorldMatrix = ParentWorldMatrix × LocalMatrix
-- |
-- | If node has no parent, WorldMatrix = LocalMatrix.
updateWorldMatrix :: NodeId -> SceneGraph -> SceneGraph
updateWorldMatrix nodeId graph =
  case Map.lookup nodeId graph of
    Nothing -> graph
    Just node ->
      let
        -- Ensure local matrix is up to date
        graphWithLocal = if node.matrixNeedsUpdate 
          then updateLocalMatrix nodeId graph 
          else graph
        
        -- Get the updated node
        updatedLocalNode = case Map.lookup nodeId graphWithLocal of
          Nothing -> node  -- Shouldn't happen
          Just n -> n
        
        -- Compute world matrix
        worldMat = case updatedLocalNode.parent of
          Nothing -> updatedLocalNode.localMatrix  -- No parent: world = local
          Just parentId ->
            case Map.lookup parentId graphWithLocal of
              Nothing -> updatedLocalNode.localMatrix  -- Parent missing: use local
              Just parentNode -> mulMat4 parentNode.worldMatrix updatedLocalNode.localMatrix
        
        finalNode = updatedLocalNode { worldMatrix = worldMat }
      in
        Map.insert nodeId finalNode graphWithLocal

-- | Get a node's world matrix.
getWorldMatrix :: NodeId -> SceneGraph -> Maybe Mat4
getWorldMatrix nodeId graph = 
  map (\node -> node.worldMatrix) (Map.lookup nodeId graph)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // traversal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Traverse all descendants of a node (depth-first).
-- |
-- | The function is called for each node, including the starting node.
-- | Three.js parity: Object3D.traverse
traverse :: forall a. NodeId -> (SceneNode -> a -> a) -> a -> SceneGraph -> a
traverse nodeId fn initial graph =
  case Map.lookup nodeId graph of
    Nothing -> initial
    Just node ->
      let
        -- Apply function to this node
        afterSelf = fn node initial
        -- Recursively traverse children
        afterChildren = Array.foldl 
          (\acc childId -> traverse childId fn acc graph) 
          afterSelf 
          node.children
      in
        afterChildren

-- | Traverse all visible descendants of a node.
-- |
-- | Only visits nodes where visible = true.
-- | Three.js parity: Object3D.traverseVisible
traverseVisible :: forall a. NodeId -> (SceneNode -> a -> a) -> a -> SceneGraph -> a
traverseVisible nodeId fn initial graph =
  case Map.lookup nodeId graph of
    Nothing -> initial
    Just node ->
      if node.visible
        then
          let
            afterSelf = fn node initial
            afterChildren = Array.foldl
              (\acc childId -> traverseVisible childId fn acc graph)
              afterSelf
              node.children
          in
            afterChildren
        else initial  -- Skip invisible nodes and their children

-- | Traverse all ancestors of a node (toward root).
-- |
-- | Does NOT include the starting node.
-- | Three.js parity: Object3D.traverseAncestors
traverseAncestors :: forall a. NodeId -> (SceneNode -> a -> a) -> a -> SceneGraph -> a
traverseAncestors nodeId fn initial graph =
  case Map.lookup nodeId graph of
    Nothing -> initial
    Just node ->
      case node.parent of
        Nothing -> initial  -- No parent, done
        Just parentId ->
          case Map.lookup parentId graph of
            Nothing -> initial  -- Parent doesn't exist
            Just parentNode ->
              let afterParent = fn parentNode initial
              in traverseAncestors parentId fn afterParent graph

-- | Find a node by its ID.
findNode :: NodeId -> SceneGraph -> Maybe SceneNode
findNode = Map.lookup

-- | Find a node by name (searches from a starting node).
-- |
-- | Returns the first node with matching name, or Nothing.
-- | Three.js parity: Object3D.getObjectByName
findNodeByName :: NodeId -> String -> SceneGraph -> Maybe SceneNode
findNodeByName startId targetName graph =
  traverse startId checkName Nothing graph
  where
    checkName :: SceneNode -> Maybe SceneNode -> Maybe SceneNode
    checkName node acc = case acc of
      Just _ -> acc  -- Already found
      Nothing -> if node.name == targetName then Just node else Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // world space queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get a node's world position (translation component of world matrix).
-- |
-- | Three.js parity: Object3D.getWorldPosition
getWorldPosition :: NodeId -> SceneGraph -> Maybe (Vec3 Number)
getWorldPosition nodeId graph =
  map (\mat -> getTranslation4 mat) (getWorldMatrix nodeId graph)

-- | Transform a local point to world space.
-- |
-- | Three.js parity: Object3D.localToWorld
localToWorld :: NodeId -> Vec3 Number -> SceneGraph -> Maybe (Vec3 Number)
localToWorld nodeId localPoint graph =
  case getWorldMatrix nodeId graph of
    Nothing -> Nothing
    Just worldMat -> Just (mulPointMat4 worldMat localPoint)

-- | Transform a world point to local space.
-- |
-- | Three.js parity: Object3D.worldToLocal
worldToLocal :: NodeId -> Vec3 Number -> SceneGraph -> Maybe (Vec3 Number)
worldToLocal nodeId worldPoint graph =
  case getWorldMatrix nodeId graph of
    Nothing -> Nothing
    Just worldMat ->
      case invertMat4 worldMat of
        Nothing -> Nothing  -- Matrix not invertible (degenerate)
        Just invWorld -> Just (mulPointMat4 invWorld worldPoint)

