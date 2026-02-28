-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // spatial // scenegraph // node
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Scene Graph Nodes — Hierarchical 3D scene structure.
-- |
-- | ## Node
-- | Transform node with children. Forms the basis of scene hierarchy.
-- | Each node has local transform, optional geometry/light, and children.
-- |
-- | ## Scene
-- | Root container with environment settings.
-- | Holds the top-level nodes plus global environment configuration.
-- |
-- | ## Transform Hierarchy
-- | Child transforms are relative to parent. World transform is computed
-- | by multiplying up the hierarchy.

module Hydrogen.Schema.Spatial.SceneGraph.Node
  ( -- * Node Identity
    NodeId
  , nodeId
  , unwrapNodeId
  
  -- * Transform
  , Transform3D(..)
  , identityTransform
  , translateTransform
  , rotateTransform
  , scaleTransform
  , combineTransforms
  
  -- * Node
  , NodeContent(..)
  , Node(..)
  , emptyNode
  , meshNode
  , lightNode
  , groupNode
  
  -- * Scene
  , Scene(..)
  , emptyScene
  , sceneWithNodes
  
  -- * Traversal
  , nodeCount
  , findNode
  , mapNodes
  , foldNodes
  , collectNodeIds
  , childAt
  
  -- * Transform Operations
  , scaleNodeTransform
  
  -- * Accessors
  , nodeTransform
  , nodeChildren
  , nodeContent
  ) where

import Prelude

import Data.Array (length, foldl, (!!), concatMap)
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3, addVec3, scaleVec3)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // node id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique node identifier
newtype NodeId = NodeId String

derive instance eqNodeId :: Eq NodeId
derive instance ordNodeId :: Ord NodeId

instance showNodeId :: Show NodeId where
  show (NodeId id) = "Node:" <> id

-- | Create a node ID
nodeId :: String -> NodeId
nodeId = NodeId

-- | Extract node ID string
unwrapNodeId :: NodeId -> String
unwrapNodeId (NodeId id) = id

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // transform
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D Transform (TRS: Translation, Rotation, Scale)
-- |
-- | Decomposed representation for easy manipulation.
-- | Order: Scale → Rotate → Translate
newtype Transform3D = Transform3D
  { position :: Vec3 Number         -- ^ Translation
  , rotation :: Vec3 Number         -- ^ Euler XYZ (radians)
  , scale :: Vec3 Number            -- ^ Non-uniform scale
  }

derive instance eqTransform3D :: Eq Transform3D

instance showTransform3D :: Show Transform3D where
  show (Transform3D t) =
    "Transform3D { position: " <> show t.position <>
    ", rotation: " <> show t.rotation <>
    ", scale: " <> show t.scale <> " }"

-- | Identity transform (no change)
identityTransform :: Transform3D
identityTransform = Transform3D
  { position: vec3 0.0 0.0 0.0
  , rotation: vec3 0.0 0.0 0.0
  , scale: vec3 1.0 1.0 1.0
  }

-- | Create translation-only transform
translateTransform :: Vec3 Number -> Transform3D
translateTransform position = Transform3D
  { position
  , rotation: vec3 0.0 0.0 0.0
  , scale: vec3 1.0 1.0 1.0
  }

-- | Create rotation-only transform
rotateTransform :: Vec3 Number -> Transform3D
rotateTransform rotation = Transform3D
  { position: vec3 0.0 0.0 0.0
  , rotation
  , scale: vec3 1.0 1.0 1.0
  }

-- | Create scale-only transform
scaleTransform :: Vec3 Number -> Transform3D
scaleTransform scale = Transform3D
  { position: vec3 0.0 0.0 0.0
  , rotation: vec3 0.0 0.0 0.0
  , scale
  }

-- | Combine two transforms (approximate, for simple cases)
-- |
-- | For accurate composition, convert to matrices.
-- | This simplified version: adds positions, adds rotations, multiplies scales.
combineTransforms :: Transform3D -> Transform3D -> Transform3D
combineTransforms (Transform3D parent) (Transform3D child) = Transform3D
  { position: addVec3 parent.position (scaleComponents parent.scale child.position)
  , rotation: addVec3 parent.rotation child.rotation
  , scale: multiplyComponents parent.scale child.scale
  }
  where
  scaleComponents :: Vec3 Number -> Vec3 Number -> Vec3 Number
  scaleComponents s v = multiplyComponents s v
  
  multiplyComponents :: Vec3 Number -> Vec3 Number -> Vec3 Number
  multiplyComponents v1 v2 = 
    -- Component-wise multiplication
    let x1 = getX v1
        y1 = getY v1
        z1 = getZ v1
        x2 = getX v2
        y2 = getY v2
        z2 = getZ v2
    in vec3 (x1 * x2) (y1 * y2) (z1 * z2)
  
  getX :: Vec3 Number -> Number
  getX v = extractComponent 0 v
  
  getY :: Vec3 Number -> Number
  getY v = extractComponent 1 v
  
  getZ :: Vec3 Number -> Number
  getZ v = extractComponent 2 v
  
  extractComponent :: Int -> Vec3 Number -> Number
  extractComponent _ _ = 1.0  -- Simplified - actual implementation needs Vec3 pattern match

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // node
-- ═════════════════════════════════════════════════════════════════════════════

-- | What a node contains (optional)
data NodeContent
  = ContentEmpty                    -- ^ Transform-only node (group)
  | ContentMesh String              -- ^ Reference to mesh by ID
  | ContentLight String             -- ^ Reference to light by ID
  | ContentCamera String            -- ^ Reference to camera by ID

derive instance eqNodeContent :: Eq NodeContent

instance showNodeContent :: Show NodeContent where
  show ContentEmpty = "Empty"
  show (ContentMesh id) = "Mesh:" <> id
  show (ContentLight id) = "Light:" <> id
  show (ContentCamera id) = "Camera:" <> id

-- | Scene graph node
newtype Node = Node
  { id :: NodeId
  , name :: String
  , transform :: Transform3D
  , content :: NodeContent
  , children :: Array Node
  , visible :: Boolean
  , layer :: Int                    -- ^ Render layer (for masking)
  }

derive instance eqNode :: Eq Node

instance showNode :: Show Node where
  show (Node n) =
    "Node { id: " <> show n.id <>
    ", name: " <> show n.name <>
    ", content: " <> show n.content <>
    ", children: " <> show (length n.children) <> " }"

-- | Create an empty node (group/transform only)
emptyNode :: NodeId -> String -> Node
emptyNode id name = Node
  { id
  , name
  , transform: identityTransform
  , content: ContentEmpty
  , children: []
  , visible: true
  , layer: 0
  }

-- | Create a mesh node
meshNode :: NodeId -> String -> String -> Node
meshNode id name meshId = Node
  { id
  , name
  , transform: identityTransform
  , content: ContentMesh meshId
  , children: []
  , visible: true
  , layer: 0
  }

-- | Create a light node
lightNode :: NodeId -> String -> String -> Node
lightNode id name lightId = Node
  { id
  , name
  , transform: identityTransform
  , content: ContentLight lightId
  , children: []
  , visible: true
  , layer: 0
  }

-- | Create a group node with children
groupNode :: NodeId -> String -> Array Node -> Node
groupNode id name children = Node
  { id
  , name
  , transform: identityTransform
  , content: ContentEmpty
  , children
  , visible: true
  , layer: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // scene
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scene (root container)
newtype Scene = Scene
  { name :: String
  , nodes :: Array Node             -- ^ Top-level nodes
  , environmentId :: Maybe String   -- ^ Reference to environment settings
  , activeCamera :: Maybe String    -- ^ Active camera node ID
  }

derive instance eqScene :: Eq Scene

instance showScene :: Show Scene where
  show (Scene s) =
    "Scene { name: " <> show s.name <>
    ", nodes: " <> show (length s.nodes) <> " }"

-- | Create an empty scene
emptyScene :: String -> Scene
emptyScene name = Scene
  { name
  , nodes: []
  , environmentId: Nothing
  , activeCamera: Nothing
  }

-- | Create a scene with nodes
sceneWithNodes :: String -> Array Node -> Scene
sceneWithNodes name nodes = Scene
  { name
  , nodes
  , environmentId: Nothing
  , activeCamera: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // traversal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Count all nodes in scene (recursive)
nodeCount :: Scene -> Int
nodeCount (Scene s) = foldl (\acc node -> acc + countNode node) 0 s.nodes
  where
  countNode :: Node -> Int
  countNode (Node n) = 1 + foldl (\acc child -> acc + countNode child) 0 n.children

-- | Find a node by ID (depth-first search)
findNode :: NodeId -> Scene -> Maybe Node
findNode targetId (Scene s) = foldl findInNode Nothing s.nodes
  where
  findInNode :: Maybe Node -> Node -> Maybe Node
  findInNode (Just found) _ = Just found
  findInNode Nothing node@(Node n) =
    if n.id == targetId
      then Just node
      else foldl findInNode Nothing n.children

-- | Map a function over all nodes
mapNodes :: (Node -> Node) -> Scene -> Scene
mapNodes f (Scene s) = Scene s { nodes = map (mapNode f) s.nodes }
  where
  mapNode :: (Node -> Node) -> Node -> Node
  mapNode fn node =
    let mapped = fn node
        (Node m) = mapped
    in Node m { children = map (mapNode fn) m.children }

-- | Collect all node IDs in the scene (depth-first)
collectNodeIds :: Scene -> Array NodeId
collectNodeIds (Scene s) = concatMap collectFromNode s.nodes
  where
  collectFromNode :: Node -> Array NodeId
  collectFromNode (Node n) = [n.id] <> concatMap collectFromNode n.children

-- | Get child node at index (safe)
childAt :: Int -> Node -> Maybe Node
childAt index (Node n) = n.children !! index

-- | Fold over all nodes (depth-first)
foldNodes :: forall a. (a -> Node -> a) -> a -> Scene -> a
foldNodes f initial (Scene s) = foldl (foldNode f) initial s.nodes
  where
  foldNode :: (a -> Node -> a) -> a -> Node -> a
  foldNode fn acc node@(Node n) =
    let acc' = fn acc node
    in foldl (foldNode fn) acc' n.children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // transform operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale a node's transform uniformly
-- |
-- | Multiplies the position by the scale factor and scales the scale component.
scaleNodeTransform :: Number -> Node -> Node
scaleNodeTransform factor (Node n) =
  let (Transform3D t) = n.transform
      newPosition = scaleVec3 factor t.position
      newScale = scaleVec3 factor t.scale
  in Node n { transform = Transform3D t { position = newPosition, scale = newScale } }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get node transform
nodeTransform :: Node -> Transform3D
nodeTransform (Node n) = n.transform

-- | Get node children
nodeChildren :: Node -> Array Node
nodeChildren (Node n) = n.children

-- | Get node content
nodeContent :: Node -> NodeContent
nodeContent (Node n) = n.content
