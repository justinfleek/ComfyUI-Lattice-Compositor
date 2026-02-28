/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                   HYDROGEN // SCENE // RESOURCE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Automatic resource lifecycle management.
  
  This solves Three.js Pain Point #1: Memory Leaks / Manual Disposal Hell
  
  "Three.js creates for specific objects like geometries or materials WebGL 
  related entities like buffers or shader programs, which are not released 
  automatically by GC."
  
  Hydrogen's approach:
  - Resources are PURE DATA describing what's needed
  - ResourceSet tracks all resources referenced by a scene
  - Runtime allocates resources when needed, releases when unused
  - Diffing two scenes yields exact add/remove resource operations
  - No manual dispose() calls, no memory leaks by construction
  
  Key insight: In a pure functional architecture, resource lifecycle is
  determined by DATA REACHABILITY, not manual tracking.

  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - None (self-contained resource types)
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.Tactic

namespace Hydrogen.Scene

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: RESOURCE IDENTIFIERS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Unique identifier for a resource.
    In practice, this would be UUID5 derived from resource content.
    Same content = same ResourceId (content-addressable). -/
structure ResourceId where
  id : Nat
  deriving Repr, DecidableEq, Hashable

namespace ResourceId

/-- Create a resource ID from a natural number. -/
def fromNat (n : Nat) : ResourceId := ⟨n⟩

/-- Equality is decidable. -/
theorem eq_iff_id_eq (a b : ResourceId) : a = b ↔ a.id = b.id := by
  constructor
  · intro h; rw [h]
  · intro h; cases a; cases b; simp only [mk.injEq]; exact h

end ResourceId

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: RESOURCE TYPES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Geometry data description.
    This is PURE DATA describing vertex layout, not GPU buffers. -/
structure GeometryDesc where
  /-- Resource identifier (content-derived) -/
  resourceId : ResourceId
  /-- Number of vertices -/
  vertexCount : Nat
  /-- Number of indices (0 for non-indexed) -/
  indexCount : Nat
  /-- Has position attribute -/
  hasPosition : Bool := true
  /-- Has normal attribute -/
  hasNormal : Bool := false
  /-- Has UV coordinates -/
  hasUV : Bool := false
  /-- Has vertex colors -/
  hasColor : Bool := false
  deriving Repr, DecidableEq

/-- Texture data description.
    This is PURE DATA describing texture properties, not GPU textures. -/
structure TextureDesc where
  /-- Resource identifier (content-derived) -/
  resourceId : ResourceId
  /-- Width in pixels -/
  width : Nat
  /-- Height in pixels -/
  height : Nat
  /-- Has alpha channel -/
  hasAlpha : Bool := false
  /-- Use mipmaps -/
  useMipmaps : Bool := true
  deriving Repr, DecidableEq

/-- Material data description.
    This is PURE DATA describing material properties, not shaders. -/
structure MaterialDesc where
  /-- Resource identifier (content-derived) -/
  resourceId : ResourceId
  /-- Base color texture (optional) -/
  colorTexture : Option ResourceId := none
  /-- Normal map texture (optional) -/
  normalTexture : Option ResourceId := none
  /-- Metallic-roughness texture (optional) -/
  metallicRoughnessTexture : Option ResourceId := none
  /-- Is transparent -/
  transparent : Bool := false
  /-- Double-sided rendering -/
  doubleSided : Bool := false
  deriving Repr, DecidableEq

/-- Shader program description.
    This is PURE DATA describing shader properties. -/
structure ShaderDesc where
  /-- Resource identifier (content-derived) -/
  resourceId : ResourceId
  /-- Vertex shader source hash -/
  vertexShaderHash : Nat
  /-- Fragment shader source hash -/
  fragmentShaderHash : Nat
  deriving Repr, DecidableEq

/-- Union of all resource types.
    Each variant carries its descriptor. -/
inductive Resource where
  | geometry (desc : GeometryDesc)
  | texture (desc : TextureDesc)
  | material (desc : MaterialDesc)
  | shader (desc : ShaderDesc)
  deriving Repr, DecidableEq

namespace Resource

/-- Get the resource ID from any resource type. -/
def resourceId : Resource → ResourceId
  | geometry d => d.resourceId
  | texture d => d.resourceId
  | material d => d.resourceId
  | shader d => d.resourceId

/-- Get the kind of resource as a string (for debugging). -/
def kind : Resource → String
  | geometry _ => "geometry"
  | texture _ => "texture"
  | material _ => "material"
  | shader _ => "shader"

end Resource

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: RESOURCE SET
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A set of resources referenced by a scene.
    Implemented as a list for proof simplicity. -/
def ResourceSet := List Resource

namespace ResourceSet

/-- Empty resource set -/
def empty : ResourceSet := []

/-- Add a resource to the set (idempotent by resource ID) -/
def add (set : ResourceSet) (r : Resource) : ResourceSet :=
  if set.any (fun r' => r'.resourceId == r.resourceId) then set
  else r :: set

/-- Remove a resource from the set by ID -/
def remove (set : ResourceSet) (id : ResourceId) : ResourceSet :=
  set.filter (fun r => r.resourceId != id)

/-- Check if a resource is in the set -/
def contains (set : ResourceSet) (id : ResourceId) : Bool :=
  set.any (fun r => r.resourceId == id)

/-- Get a resource by ID -/
def get (set : ResourceSet) (id : ResourceId) : Option Resource :=
  set.find? (fun r => r.resourceId == id)

/-- Number of resources -/
def size (set : ResourceSet) : Nat :=
  set.length

/-- Get all resource IDs -/
def ids (set : ResourceSet) : List ResourceId :=
  set.map Resource.resourceId

/-- Union of two resource sets -/
def union (a b : ResourceSet) : ResourceSet :=
  b.foldl add a

/-- Difference: resources in `a` but not in `b` -/
def diff (a b : ResourceSet) : ResourceSet :=
  a.filter (fun r => !b.contains r.resourceId)

/-- Intersection: resources in both sets -/
def inter (a b : ResourceSet) : ResourceSet :=
  a.filter (fun r => b.contains r.resourceId)

-- ─────────────────────────────────────────────────────────────────────────────
-- ResourceSet Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Empty set has size 0 -/
theorem empty_size : size empty = 0 := rfl

/-- Empty set doesn't contain any resource -/
theorem empty_not_contains (id : ResourceId) : contains empty id = false := rfl

/-- After add, contains returns true -/
theorem contains_after_add (set : ResourceSet) (r : Resource) :
    contains (add set r) r.resourceId = true := by
  unfold add contains
  split
  · assumption
  · simp only [List.any_cons, beq_self_eq_true, Bool.true_or]

/-- Add is idempotent -/
theorem add_idempotent (set : ResourceSet) (r : Resource) :
    add (add set r) r = add set r := by
  unfold add
  split <;> simp only [List.any_cons, beq_self_eq_true, Bool.true_or, ite_true]

/-- Diff with self is empty -/
theorem diff_self (set : ResourceSet) : diff set set = [] := by
  unfold diff contains
  induction set with
  | nil => rfl
  | cons hd tl _ih =>
    rw [List.filter_cons]
    simp only [List.any_cons, beq_self_eq_true, Bool.true_or, Bool.not_true]
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    have h : (tl.any fun r => r.resourceId == x.resourceId) = true := by
      apply List.any_eq_true.mpr
      exact ⟨x, hx, beq_self_eq_true x.resourceId⟩
    simp only [h, Bool.or_true, Bool.not_true]
    decide

/-- Diff with empty is self -/
theorem diff_empty (set : ResourceSet) : diff set empty = set := by
  unfold diff contains empty
  simp only [List.any_nil, Bool.not_false, List.filter_true]

end ResourceSet

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: RESOURCE DELTA
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Delta between two resource sets.
    This is the minimal set of operations to transition from old to new state.
    
    THE KEY INSIGHT: This is what enables automatic resource management.
    Runtime compares old scene's resources with new scene's resources,
    gets exact list of what to allocate and what to release. -/
structure ResourceDelta where
  /-- Resources to allocate (in new but not old) -/
  toAllocate : ResourceSet
  /-- Resources to release (in old but not new) -/
  toRelease : ResourceSet
  /-- Resources that remain (in both) -/
  unchanged : ResourceSet

namespace ResourceDelta

/-- Compute delta from old set to new set -/
def compute (oldSet newSet : ResourceSet) : ResourceDelta :=
  { toAllocate := ResourceSet.diff newSet oldSet
    toRelease := ResourceSet.diff oldSet newSet
    unchanged := ResourceSet.inter oldSet newSet }

/-- Empty delta (no changes) -/
def empty : ResourceDelta :=
  { toAllocate := []
    toRelease := []
    unchanged := [] }

/-- Check if delta represents no changes -/
def isNoOp (d : ResourceDelta) : Bool :=
  d.toAllocate.size == 0 && d.toRelease.size == 0

-- ─────────────────────────────────────────────────────────────────────────────
-- ResourceDelta Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Delta of a set with itself has no allocations or releases -/
theorem compute_self_is_noop (set : ResourceSet) :
    (compute set set).toAllocate = [] ∧ (compute set set).toRelease = [] := by
  unfold compute
  constructor
  · exact ResourceSet.diff_self set
  · exact ResourceSet.diff_self set

/-- Delta from empty to a set allocates all resources -/
theorem compute_from_empty (set : ResourceSet) :
    (compute [] set).toAllocate = set := by
  unfold compute
  exact ResourceSet.diff_empty set

/-- Delta from a set to empty releases all resources -/
theorem compute_to_empty (set : ResourceSet) :
    (compute set []).toRelease = set := by
  unfold compute
  exact ResourceSet.diff_empty set

end ResourceDelta

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: RENDERABLE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A renderable object: geometry + material.
    This is what gets attached to scene nodes. -/
structure Renderable where
  /-- Geometry resource ID -/
  geometry : ResourceId
  /-- Material resource ID -/
  material : ResourceId
  /-- Shader override (optional, uses material's default otherwise) -/
  shader : Option ResourceId := none
  deriving Repr, DecidableEq

namespace Renderable

/-- Get all resource IDs referenced by a renderable -/
def resourceIds (r : Renderable) : List ResourceId :=
  [r.geometry, r.material] ++ r.shader.toList

end Renderable

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6: RESOURCE REGISTRY
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A registry of all resources available to a scene.
    Resources are registered here, then referenced by ID in renderables.
    
    This pattern enables:
    - Resource sharing (same geometry used by many objects)
    - Deferred loading (register ID, load data later)
    - Hot reloading (replace resource data, same ID) -/
structure ResourceRegistry where
  /-- All registered resources -/
  resources : ResourceSet
  /-- Next ID for auto-allocation -/
  nextId : Nat

namespace ResourceRegistry

/-- Empty registry -/
def empty : ResourceRegistry :=
  { resources := ResourceSet.empty
    nextId := 0 }

/-- Register a resource -/
def register (reg : ResourceRegistry) (r : Resource) : ResourceRegistry :=
  { reg with resources := reg.resources.add r }

/-- Allocate a new resource ID -/
def allocateId (reg : ResourceRegistry) : ResourceRegistry × ResourceId :=
  let id := ResourceId.fromNat reg.nextId
  ({ reg with nextId := reg.nextId + 1 }, id)

/-- Get a resource by ID -/
def get (reg : ResourceRegistry) (id : ResourceId) : Option Resource :=
  reg.resources.get id

/-- Check if a resource is registered -/
def contains (reg : ResourceRegistry) (id : ResourceId) : Bool :=
  reg.resources.contains id

/-- Get all resource IDs -/
def ids (reg : ResourceRegistry) : List ResourceId :=
  reg.resources.ids

/-- Number of registered resources -/
def size (reg : ResourceRegistry) : Nat :=
  reg.resources.size

end ResourceRegistry

end Hydrogen.Scene
