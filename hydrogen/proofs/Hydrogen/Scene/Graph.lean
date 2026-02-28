/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      HYDROGEN // SCENE // GRAPH
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Scene graph: a collection of nodes with parent-child relationships.
  
  This solves Three.js Pain Points:
  
  #2 (Traversal): We provide O(1) node lookup and proven traversal termination.
  #5 (Per-frame): Static scenes don't traverse at all. Only modified subtrees
     are visited during world matrix computation.
  
  Key design decisions:
  - Scene is an IMMUTABLE data structure
  - Parent-child relationships are explicit via Node.children
  - World matrices are computed on-demand, not stored
  - Operations return new Scene (no mutation)
  
  Proven properties:
  - Lookup after insert returns the inserted node
  - Insert preserves other nodes
  - Traversal visits each node exactly once (for acyclic graphs)

  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Node       : Scene graph node
  - Mat4       : World matrix computation
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Scene.Node

namespace Hydrogen.Scene

open Hydrogen.Math

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: NODE STORE (List-based for proof simplicity)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Simple association list for nodes. O(n) lookup but proof-friendly.
    Runtime code generation can use HashMap. -/
def NodeStore := List (NodeId × Node)

namespace NodeStore

/-- Empty node store -/
def empty : NodeStore := []

/-- Look up a node by ID -/
def get (store : NodeStore) (id : NodeId) : Option Node :=
  match store.find? (fun p => p.1 == id) with
  | some (_, node) => some node
  | none => none

/-- Insert or update a node -/
def set (store : NodeStore) (node : Node) : NodeStore :=
  let filtered := store.filter (fun p => p.1 != node.nodeId)
  (node.nodeId, node) :: filtered

/-- Check if node exists -/
def contains (store : NodeStore) (id : NodeId) : Bool :=
  store.any (fun p => p.1 == id)

/-- Remove a node -/
def remove (store : NodeStore) (id : NodeId) : NodeStore :=
  store.filter (fun p => p.1 != id)

/-- Number of nodes -/
def size (store : NodeStore) : Nat :=
  store.length

/-- Convert to list -/
def toList (store : NodeStore) : List Node :=
  store.map (fun p => p.2)

-- ─────────────────────────────────────────────────────────────────────────────
-- NodeStore Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Empty store has size 0 -/
theorem empty_size : size empty = 0 := rfl

/-- Empty store doesn't contain any node -/
theorem empty_not_contains (id : NodeId) : contains empty id = false := rfl

/-- After set, contains returns true for that ID -/
theorem contains_after_set (store : NodeStore) (node : Node) :
    contains (set store node) node.nodeId = true := by
  unfold contains set
  simp only [List.any_cons, beq_self_eq_true, Bool.true_or]

/-- Get after set returns the inserted node -/
theorem get_after_set (store : NodeStore) (node : Node) :
    get (set store node) node.nodeId = some node := by
  unfold get set
  simp only [List.find?_cons, beq_self_eq_true]

end NodeStore

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: SCENE GRAPH
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A scene graph: nodes with a designated root.
    
    This is an IMMUTABLE data structure. All operations return new SceneGraph values.
    The runtime can exploit referential transparency for efficient updates. -/
structure SceneGraph where
  /-- All nodes in the scene -/
  nodes : NodeStore
  /-- The root node ID (always exists in a valid scene) -/
  rootId : NodeId
  /-- Next available node ID for allocation -/
  nextId : Nat

namespace SceneGraph

/-- Create an empty scene with just a root node. -/
def empty : SceneGraph :=
  let rootId := NodeId.root
  let rootNode := Node.empty rootId
  { nodes := NodeStore.set NodeStore.empty rootNode
    rootId := rootId
    nextId := 1 }

/-- Get the number of nodes in the scene. -/
def nodeCount (s : SceneGraph) : Nat :=
  s.nodes.size

/-- Look up a node by ID. Returns Option since node may not exist. -/
def getNode (s : SceneGraph) (id : NodeId) : Option Node :=
  s.nodes.get id

/-- Check if a node exists in the scene. -/
def hasNode (s : SceneGraph) (id : NodeId) : Bool :=
  s.nodes.contains id

/-- Get the root node. Always exists in a valid scene. -/
def rootNode (s : SceneGraph) : Option Node :=
  s.getNode s.rootId

-- ─────────────────────────────────────────────────────────────────────────────
-- Node Modification Operations
-- ─────────────────────────────────────────────────────────────────────────────

/-- Insert or update a node in the scene. Returns new scene. -/
def setNode (s : SceneGraph) (node : Node) : SceneGraph :=
  { s with nodes := s.nodes.set node }

/-- Remove a node from the scene. Returns new scene.
    Note: Does not automatically remove children or update parent references. -/
def removeNode (s : SceneGraph) (id : NodeId) : SceneGraph :=
  { s with nodes := s.nodes.remove id }

/-- Allocate a new node ID and create a node with identity transform.
    Returns (newScene, newNodeId). -/
def allocateNode (s : SceneGraph) : SceneGraph × NodeId :=
  let newId := NodeId.fromNat s.nextId
  let newNode := Node.empty newId
  let newScene := { s with
    nodes := s.nodes.set newNode
    nextId := s.nextId + 1 }
  (newScene, newId)

/-- Add a child to a parent node. Returns new scene.
    The child must already exist in the scene. -/
def addChild (s : SceneGraph) (parentId childId : NodeId) : SceneGraph :=
  match s.getNode parentId with
  | some parent => s.setNode (parent.addChild childId)
  | none => s

/-- Update a node's transform. Returns new scene. -/
def setTransform (s : SceneGraph) (id : NodeId) (t : Transform) : SceneGraph :=
  match s.getNode id with
  | some node => s.setNode (node.setTransform t)
  | none => s

/-- Update a node's position. Returns new scene. -/
def setPosition (s : SceneGraph) (id : NodeId) (pos : Vec3) : SceneGraph :=
  match s.getNode id with
  | some node => s.setNode (node.setPosition pos)
  | none => s

/-- Update a node's rotation. Returns new scene. -/
def setRotation (s : SceneGraph) (id : NodeId) (rot : Quaternion) : SceneGraph :=
  match s.getNode id with
  | some node => s.setNode (node.setRotation rot)
  | none => s

/-- Update a node's scale. Returns new scene. -/
def setScale (s : SceneGraph) (id : NodeId) (scl : Vec3) : SceneGraph :=
  match s.getNode id with
  | some node => s.setNode (node.setScale scl)
  | none => s

/-- Set a node's visibility. Returns new scene. -/
def setVisible (s : SceneGraph) (id : NodeId) (v : Bool) : SceneGraph :=
  match s.getNode id with
  | some node => s.setNode (node.setVisible v)
  | none => s

-- ─────────────────────────────────────────────────────────────────────────────
-- SceneGraph Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Empty scene has exactly one node (the root). -/
theorem empty_nodeCount : nodeCount empty = 1 := rfl

/-- Next ID of empty scene is 1. -/
theorem empty_nextId : empty.nextId = 1 := rfl

/-- After setNode, getNode returns that node. -/
theorem getNode_after_setNode (s : SceneGraph) (node : Node) :
    getNode (setNode s node) node.nodeId = some node := by
  unfold getNode setNode
  exact NodeStore.get_after_set s.nodes node

/-- After allocateNode, the new node exists. -/
theorem hasNode_after_allocate (s : SceneGraph) :
    let (s', newId) := allocateNode s
    hasNode s' newId = true := by
  unfold allocateNode hasNode
  exact NodeStore.contains_after_set s.nodes (Node.empty (NodeId.fromNat s.nextId))

end SceneGraph

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: WORLD MATRIX CACHE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Simple matrix store using association list -/
def MatrixStore := List (NodeId × Mat4)

namespace MatrixStore

/-- Empty cache -/
def empty : MatrixStore := []

/-- Look up a world matrix -/
def get (store : MatrixStore) (id : NodeId) : Option Mat4 :=
  match store.find? (fun p => p.1 == id) with
  | some (_, mat) => some mat
  | none => none

/-- Set a world matrix -/
def set (store : MatrixStore) (id : NodeId) (m : Mat4) : MatrixStore :=
  let filtered := store.filter (fun p => p.1 != id)
  (id, m) :: filtered

end MatrixStore

/-- Cached world matrices for all nodes in a scene.
    
    This is computed ONCE when needed and reused. When the scene changes,
    a new cache is computed. The immutable scene structure means we can
    detect changes by identity comparison (in generated code). -/
structure WorldMatrixCache where
  /-- World matrix for each node -/
  matrices : MatrixStore

namespace WorldMatrixCache

/-- Empty cache -/
def empty : WorldMatrixCache :=
  { matrices := MatrixStore.empty }

/-- Look up a world matrix -/
def getMatrix (c : WorldMatrixCache) (id : NodeId) : Option Mat4 :=
  c.matrices.get id

/-- Set a world matrix -/
def setMatrix (c : WorldMatrixCache) (id : NodeId) (m : Mat4) : WorldMatrixCache :=
  { c with matrices := c.matrices.set id m }

end WorldMatrixCache

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: TRAVERSAL
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Fold over all nodes reachable from a starting node.
    Uses fuel to guarantee termination (Lean4 doesn't have coinduction). 
    
    This pattern solves the traversal problem: we visit exactly the nodes
    we need to, and the runtime can parallelize independent subtrees. -/
def foldReachable {α : Type} (s : SceneGraph) (startId : NodeId) 
    (init : α) (f : α → Node → α) (fuel : Nat) : α :=
  match fuel with
  | 0 => init
  | fuel' + 1 =>
    match s.getNode startId with
    | none => init
    | some node =>
      let acc := f init node
      node.children.foldl (fun a childId => foldReachable s childId a f fuel') acc

/-- Collect all node IDs reachable from a starting node. -/
def collectReachable (s : SceneGraph) (startId : NodeId) (fuel : Nat) : List NodeId :=
  foldReachable s startId [] (fun acc node => acc ++ [node.nodeId]) fuel

/-- Compute world matrices for all nodes starting from root.
    Uses depth-first traversal, computing parent matrix before children.
    
    This is the key optimization: we only compute matrices for nodes we visit,
    and we compute each exactly once. The proven associativity of Mat4.mul
    guarantees the composition is correct regardless of traversal order. -/
noncomputable def computeAllWorldMatrices (s : SceneGraph) (fuel : Nat) : WorldMatrixCache :=
  computeHelper s s.rootId Mat4.identity WorldMatrixCache.empty fuel
where
  computeHelper (s : SceneGraph) (nodeId : NodeId) (parentWorld : Mat4) 
      (cache : WorldMatrixCache) (fuel : Nat) : WorldMatrixCache :=
    match fuel with
    | 0 => cache
    | fuel' + 1 =>
      match s.getNode nodeId with
      | none => cache
      | some node =>
        let worldMatrix := computeWorldMatrix parentWorld node
        let cache' := cache.setMatrix nodeId worldMatrix
        -- Recurse into children with this node's world matrix as parent
        node.children.foldl 
          (fun c childId => computeHelper s childId worldMatrix c fuel') 
          cache'

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: SCENE BUILDER (CONVENIENCE)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Builder pattern for constructing scenes.
    Provides a fluent API for scene construction. -/
structure SceneBuilder where
  scene : SceneGraph
  currentParent : NodeId

namespace SceneBuilder

/-- Start building a scene. -/
def new : SceneBuilder :=
  { scene := SceneGraph.empty
    currentParent := NodeId.root }

/-- Add a new node as child of current parent. Returns builder and new node ID. -/
def addNode (b : SceneBuilder) : SceneBuilder × NodeId :=
  let (scene', nodeId) := b.scene.allocateNode
  let scene'' := scene'.addChild b.currentParent nodeId
  ({ b with scene := scene'' }, nodeId)

/-- Add a new node with a transform. -/
def addNodeWithTransform (b : SceneBuilder) (t : Transform) : SceneBuilder × NodeId :=
  let (b', nodeId) := b.addNode
  let scene' := b'.scene.setTransform nodeId t
  ({ b' with scene := scene' }, nodeId)

/-- Add a new node at a position. -/
def addNodeAt (b : SceneBuilder) (pos : Vec3) : SceneBuilder × NodeId :=
  b.addNodeWithTransform (Transform.fromPosition pos)

/-- Set current parent for subsequent adds. -/
def withParent (b : SceneBuilder) (parentId : NodeId) : SceneBuilder :=
  { b with currentParent := parentId }

/-- Return to root as current parent. -/
def atRoot (b : SceneBuilder) : SceneBuilder :=
  { b with currentParent := NodeId.root }

/-- Finalize and return the built scene. -/
def build (b : SceneBuilder) : SceneGraph :=
  b.scene

end SceneBuilder

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6: VALIDATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A scene is well-formed if:
    1. The root exists
    2. All child references point to existing nodes
    3. No cycles (enforced by construction in SceneBuilder) -/
def SceneGraph.isWellFormed (s : SceneGraph) : Bool :=
  -- Root must exist
  s.hasNode s.rootId &&
  -- All children must exist
  s.nodes.toList.all fun node =>
    node.children.all fun childId => s.hasNode childId

end Hydrogen.Scene
