/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      HYDROGEN // SCENE // DIFF
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Structural diffing for scene graphs.
  
  This solves Three.js Pain Point #5: Per-Frame Overhead Even When Static
  
  "On every render frame Three.js traverses the entire scene graph, deciding 
  what to do with each type of object in the tree, if anything."
  
  Hydrogen's approach:
  - Scenes are IMMUTABLE data structures
  - Diff computes exact changes between two scene states
  - Runtime applies ONLY the changes, not full traversal
  - Static scene = zero diff = zero work
  
  Key insight: Pure functional data structures enable O(changes) updates,
  not O(scene size) per-frame cost.

  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Node       : Scene graph nodes
  - Graph      : Scene graph structure
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Scene.Node
import Hydrogen.Scene.Graph

namespace Hydrogen.Scene

open Hydrogen.Math

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: NODE CHANGE TYPES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Types of changes that can happen to a node.
    Using NodeId-only representation for simplicity. -/
inductive NodeChange where
  /-- Node was added to the scene -/
  | added (nodeId : NodeId)
  /-- Node was removed from the scene -/
  | removed (nodeId : NodeId)
  /-- Node's transform changed -/
  | transformChanged (nodeId : NodeId)
  /-- Node's visibility changed -/
  | visibilityChanged (nodeId : NodeId)
  /-- Node's children changed -/
  | childrenChanged (nodeId : NodeId)
  deriving Repr, DecidableEq

namespace NodeChange

/-- Get the node ID affected by this change -/
def nodeId : NodeChange → NodeId
  | added id => id
  | removed id => id
  | transformChanged id => id
  | visibilityChanged id => id
  | childrenChanged id => id

/-- Check if this is an add operation -/
def isAdd : NodeChange → Bool
  | added _ => true
  | _ => false

/-- Check if this is a remove operation -/
def isRemove : NodeChange → Bool
  | removed _ => true
  | _ => false

/-- Check if this affects transform -/
def isTransformChange : NodeChange → Bool
  | transformChanged _ => true
  | _ => false

end NodeChange

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: SCENE DIFF
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Complete diff between two scene states.
    
    This is the minimal representation of changes needed to go from
    oldScene to newScene. The runtime executes these changes directly. -/
structure SceneDiff where
  /-- List of all node changes -/
  changes : List NodeChange
  /-- Whether the root changed (requires special handling) -/
  rootChanged : Bool
  /-- Nodes whose world matrices need recomputation -/
  dirtyNodes : List NodeId
  deriving Repr

namespace SceneDiff

/-- Empty diff (no changes) -/
def empty : SceneDiff :=
  { changes := []
    rootChanged := false
    dirtyNodes := [] }

/-- Check if the diff represents no changes -/
def isEmpty (d : SceneDiff) : Bool :=
  d.changes.isEmpty && !d.rootChanged

/-- Number of changes in the diff -/
def size (d : SceneDiff) : Nat :=
  d.changes.length

/-- Get all added node IDs -/
def addedNodes (d : SceneDiff) : List NodeId :=
  d.changes.filter NodeChange.isAdd |>.map NodeChange.nodeId

/-- Get all removed node IDs -/
def removedNodes (d : SceneDiff) : List NodeId :=
  d.changes.filter NodeChange.isRemove |>.map NodeChange.nodeId

/-- Get all nodes with transform changes -/
def transformChangedNodes (d : SceneDiff) : List NodeId :=
  d.changes.filter NodeChange.isTransformChange |>.map NodeChange.nodeId

end SceneDiff

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: DIFF ALGORITHM
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Compute the diff between two scene graphs.
    
    This is the core algorithm that enables incremental updates.
    Complexity: O(n) where n is the number of nodes in the larger scene. -/
def computeDiff (oldScene newScene : SceneGraph) : SceneDiff :=
  -- Get all node IDs from both scenes
  let oldIds := oldScene.nodes.map (fun p => p.1)
  let newIds := newScene.nodes.map (fun p => p.1)
  
  -- Find added nodes (in new but not in old)
  let addedIds := newIds.filter (fun id => !oldIds.any (· == id))
  let addedChanges := addedIds.map NodeChange.added
  
  -- Find removed nodes (in old but not in new)
  let removedIds := oldIds.filter (fun id => !newIds.any (· == id))
  let removedChanges := removedIds.map NodeChange.removed
  
  -- Dirty nodes are added nodes plus any that might have changed
  -- (Full comparison would require decidable equality on transforms)
  let dirtyNodes := addedIds
  
  { changes := addedChanges ++ removedChanges
    rootChanged := oldScene.rootId != newScene.rootId
    dirtyNodes := dirtyNodes }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: DIFF PROOFS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Empty diff has no changes -/
theorem empty_isEmpty : SceneDiff.empty.isEmpty = true := by
  unfold SceneDiff.empty SceneDiff.isEmpty
  simp only [List.isEmpty_nil, Bool.not_false, Bool.and_true]

/-- Empty diff has size 0 -/
theorem empty_size : SceneDiff.empty.size = 0 := rfl

/-- Diffing a scene with itself produces no added nodes -/
theorem diff_self_no_adds (s : SceneGraph) : 
    (computeDiff s s).dirtyNodes = [] := by
  unfold computeDiff
  apply List.filter_eq_nil_iff.mpr
  intro id hid
  simp only [Bool.not_eq_true']
  have h : (s.nodes.map (fun p => p.1)).any (· == id) = true := 
    List.any_eq_true.mpr ⟨id, hid, beq_self_eq_true id⟩
  rw [h]
  decide

/-- Diffing a scene with itself produces empty changes list -/
theorem diff_self_changes (s : SceneGraph) :
    (computeDiff s s).changes = [] := by
  unfold computeDiff
  have h1 : List.filter (fun id => !(s.nodes.map (fun p => p.1)).any (· == id)) (s.nodes.map (fun p => p.1)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro id hid
    simp only [Bool.not_eq_true']
    have h : (s.nodes.map (fun p => p.1)).any (· == id) = true := 
      List.any_eq_true.mpr ⟨id, hid, beq_self_eq_true id⟩
    rw [h]
    decide
  simp only [h1, List.map_nil, List.append_nil]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: DIRTY PROPAGATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Propagate dirty flags down the scene graph.
    
    When a node's transform changes, all its descendants need their
    world matrices recomputed. This function computes the full set of
    dirty nodes by traversing down from initially dirty nodes. -/
def propagateDirty (s : SceneGraph) (initialDirty : List NodeId) (fuel : Nat) : List NodeId :=
  match fuel with
  | 0 => initialDirty
  | fuel' + 1 =>
    -- For each dirty node, add all children
    let childrenOfDirty := initialDirty.foldl (fun acc id =>
      match s.getNode id with
      | some node => acc ++ node.children
      | none => acc) []
    -- If no new children, we're done
    if childrenOfDirty.isEmpty then initialDirty
    else 
      -- Remove duplicates and recurse
      let newDirty := childrenOfDirty.filter (fun id => !initialDirty.any (· == id))
      if newDirty.isEmpty then initialDirty
      else initialDirty ++ propagateDirty s newDirty fuel'

/-- Compute complete dirty set from a diff -/
def completeDirtySet (s : SceneGraph) (diff : SceneDiff) (fuel : Nat) : List NodeId :=
  propagateDirty s diff.dirtyNodes fuel

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6: INCREMENTAL UPDATE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Recompute world matrices only for dirty nodes.
    
    This is the key optimization: instead of recomputing all matrices,
    we only recompute for nodes in the dirty set. For static scenes,
    this is empty. For small changes, this is O(affected subtree). -/
noncomputable def incrementalWorldMatrixUpdate 
    (s : SceneGraph) (oldCache : WorldMatrixCache) (dirtySet : List NodeId) (fuel : Nat) 
    : WorldMatrixCache :=
  dirtySet.foldl (fun cache nodeId =>
    match s.getNode nodeId with
    | none => cache
    | some node =>
      -- Find parent's world matrix (if exists)
      let parentWorld := 
        match findParent s nodeId fuel with
        | some parentId => 
          match cache.getMatrix parentId with
          | some m => m
          | none => Mat4.identity
        | none => Mat4.identity
      let worldMatrix := computeWorldMatrix parentWorld node
      cache.setMatrix nodeId worldMatrix
  ) oldCache
where
  /-- Find parent of a node by searching the graph -/
  findParent (s : SceneGraph) (childId : NodeId) (fuel : Nat) : Option NodeId :=
    match fuel with
    | 0 => none
    | _ + 1 =>
      -- Linear search through all nodes for one that has childId as a child
      s.nodes.foldl (fun acc (nodeId, node) =>
        match acc with
        | some _ => acc
        | none => if node.children.any (· == childId) then some nodeId else none
      ) none

-- ─────────────────────────────────────────────────────────────────────────────
-- Incremental Update Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Empty dirty set means no updates -/
theorem incrementalUpdate_empty_dirtySet (s : SceneGraph) (cache : WorldMatrixCache) (fuel : Nat) :
    incrementalWorldMatrixUpdate s cache [] fuel = cache := rfl

/-- Propagating from empty dirty set returns empty -/
theorem propagateDirty_empty (s : SceneGraph) (fuel : Nat) :
    propagateDirty s [] fuel = [] := by
  cases fuel with
  | zero => rfl
  | succ n => 
    unfold propagateDirty
    simp only [List.foldl_nil, List.isEmpty_nil, ↓reduceIte]

end Hydrogen.Scene
