/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       HYDROGEN // SCENE // NODE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Scene graph node with transform and dirty tracking.
  
  This solves Three.js Pain Point #2: "By default, Three.js takes a brute-force
  approach to calculating the world matrices of objects: on every frame it 
  traverses the entire scene graph and for each Object3D it both composes a 
  local transform matrix and multiplies it with the parent to get its 
  worldMatrix."
  
  Our approach:
  - Transforms are IMMUTABLE data
  - World matrices are computed LAZILY with caching
  - Dirty tracking is STRUCTURAL (new value = new identity)
  - Proven: composing transforms is associative (Mat4.mul_assoc)
  - Proven: identity transform is neutral (Mat4.mul_identity_left/right)

  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Mat4        : 4×4 transformation matrices
  - Vec3        : 3D position vectors  
  - Quaternion  : Rotation representation
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Math.Mat4
import Hydrogen.Math.Vec3
import Hydrogen.Math.Quaternion

namespace Hydrogen.Scene

open Hydrogen.Math

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: LOCAL TRANSFORM
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Local transform: position, rotation (quaternion), scale.
    This is the TRS decomposition used by game engines.
    Order of application: Scale → Rotate → Translate (SRT)
    
    Note: rotation should be a unit quaternion for correct behavior.
    The type system doesn't enforce this; runtime normalizes. -/
structure Transform where
  position : Vec3
  rotation : Quaternion
  scale : Vec3

namespace Transform

/-- Identity transform: no translation, no rotation, uniform scale of 1. -/
def identity : Transform where
  position := Vec3.zero
  rotation := Quaternion.identity
  scale := Vec3.mk 1 1 1

/-- Create transform from just position. -/
def fromPosition (pos : Vec3) : Transform where
  position := pos
  rotation := Quaternion.identity
  scale := Vec3.mk 1 1 1

/-- Create transform from position and rotation. -/
def fromPositionRotation (pos : Vec3) (rot : Quaternion) : Transform where
  position := pos
  rotation := rot
  scale := Vec3.mk 1 1 1

/-- Create transform from all components. -/
def fromPRS (pos : Vec3) (rot : Quaternion) (scl : Vec3) : Transform :=
  { position := pos, rotation := rot, scale := scl }

/-- Convert transform to 4×4 matrix.
    Applies in order: Scale → Rotate → Translate -/
noncomputable def toMat4 (t : Transform) : Mat4 :=
  let s := Mat4.makeScale t.scale.x t.scale.y t.scale.z
  let r := Quaternion.toMat4 t.rotation
  let tr := Mat4.makeTranslation t.position.x t.position.y t.position.z
  -- T * R * S: when applied to vector, does S first, then R, then T
  Mat4.mul tr (Mat4.mul r s)

-- ─────────────────────────────────────────────────────────────────────────────
-- Transform Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Identity transform produces identity matrix. -/
theorem identity_toMat4 : toMat4 identity = Mat4.identity := by
  unfold toMat4 identity
  simp only [Vec3.zero]
  -- Scale of (1,1,1) is identity
  rw [Mat4.makeScale_one]
  -- Identity quaternion produces identity rotation
  rw [Quaternion.toMat4_identity]
  -- Translation of (0,0,0) is identity
  rw [Mat4.makeTranslation_zero]
  -- identity * identity = identity
  rw [Mat4.mul_identity_right, Mat4.mul_identity_right]

/-- Setting position updates the position field. -/
theorem withPosition_position (t : Transform) (p : Vec3) :
    { t with position := p }.position = p := rfl

/-- Setting rotation updates the rotation field. -/
theorem withRotation_rotation (t : Transform) (r : Quaternion) :
    { t with rotation := r }.rotation = r := rfl

/-- Setting scale updates the scale field. -/
theorem withScale_scale (t : Transform) (s : Vec3) :
    { t with scale := s }.scale = s := rfl

end Transform

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: NODE IDENTITY
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Unique identifier for scene nodes.
    Using Nat for simplicity; in practice would be UUID5. -/
structure NodeId where
  id : Nat
  deriving Repr, DecidableEq, Hashable

namespace NodeId

/-- Root node always has ID 0. -/
def root : NodeId := ⟨0⟩

/-- Create a node ID from a natural number. -/
def fromNat (n : Nat) : NodeId := ⟨n⟩

/-- Two node IDs are equal iff their underlying values are equal. -/
theorem eq_iff_id_eq (a b : NodeId) : a = b ↔ a.id = b.id := by
  constructor
  · intro h; rw [h]
  · intro h; cases a; cases b; simp only [mk.injEq]; exact h

end NodeId

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: SCENE NODE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A scene node: identity, local transform, and children.
    
    Key design decisions:
    - Nodes are IMMUTABLE. Changing a transform creates a new node.
    - Children are stored by reference (NodeId), not inline.
    - World matrix is COMPUTED, not stored (no stale cache possible).
    - Dirty tracking is STRUCTURAL: different value = different identity.
    
    This eliminates Three.js's mutable worldMatrix + matrixWorldNeedsUpdate
    pattern that causes bugs and performance issues. -/
structure Node where
  nodeId : NodeId
  transform : Transform
  children : List NodeId
  visible : Bool := true

namespace Node

/-- Create a node with identity transform and no children. -/
def empty (id : NodeId) : Node where
  nodeId := id
  transform := Transform.identity
  children := []
  visible := true

/-- Create a node with a transform. -/
def withTransform (id : NodeId) (t : Transform) : Node where
  nodeId := id
  transform := t
  children := []
  visible := true

/-- Add a child to a node. Returns new node (immutable). -/
def addChild (n : Node) (childId : NodeId) : Node :=
  { n with children := n.children ++ [childId] }

/-- Remove a child from a node. Returns new node (immutable). -/
def removeChild (n : Node) (childId : NodeId) : Node :=
  { n with children := n.children.filter (· ≠ childId) }

/-- Check if node has a specific child. -/
def hasChild (n : Node) (childId : NodeId) : Bool :=
  n.children.any (· == childId)

/-- Set the local transform. Returns new node (immutable). -/
def setTransform (n : Node) (t : Transform) : Node :=
  { n with transform := t }

/-- Set position. Returns new node (immutable). -/
def setPosition (n : Node) (pos : Vec3) : Node :=
  { n with transform := { n.transform with position := pos } }

/-- Set rotation. Returns new node (immutable). -/
def setRotation (n : Node) (rot : Quaternion) : Node :=
  { n with transform := { n.transform with rotation := rot } }

/-- Set scale. Returns new node (immutable). -/
def setScale (n : Node) (scl : Vec3) : Node :=
  { n with transform := { n.transform with scale := scl } }

/-- Set visibility. Returns new node (immutable). -/
def setVisible (n : Node) (v : Bool) : Node :=
  { n with visible := v }

/-- Get the local transformation matrix. -/
noncomputable def localMatrix (n : Node) : Mat4 :=
  Transform.toMat4 n.transform

-- ─────────────────────────────────────────────────────────────────────────────
-- Node Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Empty node has identity transform. -/
theorem empty_transform (id : NodeId) : 
    (empty id).transform = Transform.identity := rfl

/-- Empty node has no children. -/
theorem empty_children (id : NodeId) : 
    (empty id).children = [] := rfl

/-- Empty node is visible. -/
theorem empty_visible (id : NodeId) : 
    (empty id).visible = true := rfl

/-- Adding a child preserves node ID. -/
theorem addChild_preserves_id (n : Node) (childId : NodeId) :
    (addChild n childId).nodeId = n.nodeId := rfl

/-- Adding a child preserves transform. -/
theorem addChild_preserves_transform (n : Node) (childId : NodeId) :
    (addChild n childId).transform = n.transform := rfl

/-- Adding then checking child returns true. -/
theorem hasChild_after_add (n : Node) (childId : NodeId) :
    hasChild (addChild n childId) childId = true := by
  unfold hasChild addChild
  simp only [List.any_append, List.any_cons, beq_self_eq_true, Bool.true_or,
    List.any_nil, Bool.or_true]

/-- Setting transform updates transform field. -/
theorem setTransform_transform (n : Node) (t : Transform) :
    (setTransform n t).transform = t := rfl

/-- Setting transform preserves node ID. -/
theorem setTransform_preserves_id (n : Node) (t : Transform) :
    (setTransform n t).nodeId = n.nodeId := rfl

/-- Setting transform preserves children. -/
theorem setTransform_preserves_children (n : Node) (t : Transform) :
    (setTransform n t).children = n.children := rfl

/-- Empty node has identity local matrix. -/
theorem empty_localMatrix (id : NodeId) :
    localMatrix (empty id) = Mat4.identity := by
  unfold localMatrix
  rw [empty_transform]
  exact Transform.identity_toMat4

end Node

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: WORLD MATRIX COMPUTATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Compute world matrix given parent's world matrix.
    
    Key insight: This is a PURE FUNCTION. No mutation. No caching.
    The runtime can memoize based on structural equality.
    
    Proven: Mat4.mul_assoc ensures we can cache intermediate results
    correctly. The composition (grandparent * parent * child) equals
    ((grandparent * parent) * child) by associativity. -/
noncomputable def computeWorldMatrix (parentWorld : Mat4) (node : Node) : Mat4 :=
  Mat4.mul parentWorld (Node.localMatrix node)

/-- World matrix of root node equals its local matrix. -/
theorem worldMatrix_root (n : Node) :
    computeWorldMatrix Mat4.identity n = Node.localMatrix n := by
  unfold computeWorldMatrix
  rw [Mat4.mul_identity_left]

/-- World matrix computation is associative with parent chain.
    If we have grandparent → parent → child, then:
    worldMatrix(grandparentWorld, parent) gives parentWorld
    worldMatrix(parentWorld, child) gives childWorld
    
    This equals: worldMatrix(worldMatrix(grandparentWorld, parent), child)
    Which equals: grandparentWorld * parentLocal * childLocal
    
    By associativity, this is well-defined regardless of grouping. -/
theorem worldMatrix_chain (grandparentWorld : Mat4) (parent child : Node) :
    computeWorldMatrix (computeWorldMatrix grandparentWorld parent) child =
    Mat4.mul grandparentWorld (Mat4.mul (Node.localMatrix parent) (Node.localMatrix child)) := by
  unfold computeWorldMatrix
  rw [Mat4.mul_assoc]

/-- Identity transform node doesn't change parent's world matrix. -/
theorem worldMatrix_identity_child (parentWorld : Mat4) (id : NodeId) :
    computeWorldMatrix parentWorld (Node.empty id) = parentWorld := by
  unfold computeWorldMatrix
  rw [Node.empty_localMatrix, Mat4.mul_identity_right]

end Hydrogen.Scene
