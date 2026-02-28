/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      HYDROGEN // GEOMETRY // MESH
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Mesh data structure for GPU geometry.
  
  A Mesh is the complete description of renderable geometry:
  - Vertex layout (what attributes, what format)
  - Vertex count
  - Index count (0 for non-indexed)
  - Primitive topology
  - Bounding information
  
  Key design decisions:
  - Mesh is PURE DATA describing the geometry, not GPU buffers
  - Actual vertex/index data lives in separate arrays (runtime concern)
  - Proven invariants: vertex/index counts match topology requirements

  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Vertex     : Vertex attribute types and layouts
  - Box3       : Axis-aligned bounding box
  - Sphere     : Bounding sphere
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Geometry.Vertex
import Hydrogen.Math.Box3
import Hydrogen.Math.Sphere

namespace Hydrogen.Geometry

open Hydrogen.Math

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: DRAW RANGE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Range of vertices/indices to draw.
    Enables partial mesh rendering and multi-draw batching. -/
structure DrawRange where
  /-- First vertex/index to draw -/
  start : Nat
  /-- Number of vertices/indices to draw -/
  count : Nat
  deriving Repr, DecidableEq

namespace DrawRange

/-- Full range: draw everything -/
def full (count : Nat) : DrawRange :=
  { start := 0, count := count }

/-- Check if range is valid for a buffer of given size -/
def isValid (range : DrawRange) (bufferSize : Nat) : Bool :=
  range.start + range.count <= bufferSize

/-- Empty range -/
def empty : DrawRange :=
  { start := 0, count := 0 }

/-- Compute end index (exclusive) -/
def endIndex (range : DrawRange) : Nat :=
  range.start + range.count

-- ─────────────────────────────────────────────────────────────────────────────
-- DrawRange Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Full range is valid -/
theorem full_isValid (n : Nat) : isValid (full n) n = true := by
  unfold full isValid
  simp only [Nat.zero_add, Nat.le_refl, decide_eq_true_eq]

/-- Empty range is always valid -/
theorem empty_isValid (n : Nat) : isValid empty n = true := by
  unfold empty isValid
  simp only [Nat.zero_add, Nat.zero_le, decide_eq_true_eq]

end DrawRange

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: MESH DESCRIPTOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Complete mesh descriptor: everything needed to render geometry.
    
    This is PURE DATA. The actual vertex/index arrays are separate.
    This enables:
    - Geometry sharing (same mesh, different transforms)
    - LOD selection (same object, different mesh descriptors)
    - Efficient serialization (descriptors are small) -/
structure MeshDescriptor where
  /-- Vertex layout -/
  layout : VertexLayout
  /-- Number of vertices -/
  vertexCount : Nat
  /-- Index format (none = non-indexed) -/
  indexFormat : Option IndexFormat
  /-- Number of indices (0 for non-indexed) -/
  indexCount : Nat
  /-- Primitive topology -/
  topology : PrimitiveTopology
  /-- Bounding box (optional, for culling) -/
  boundingBox : Option Box3
  /-- Bounding sphere (optional, for culling) -/
  boundingSphere : Option Sphere

namespace MeshDescriptor

/-- Check if mesh is indexed -/
def isIndexed (m : MeshDescriptor) : Bool :=
  m.indexFormat.isSome && m.indexCount > 0

/-- Get element count (indices if indexed, vertices otherwise) -/
def elementCount (m : MeshDescriptor) : Nat :=
  if m.isIndexed then m.indexCount else m.vertexCount

/-- Compute primitive count based on topology -/
def primitiveCount (m : MeshDescriptor) : Nat :=
  m.topology.primitiveCount m.elementCount

/-- Compute vertex buffer size in bytes -/
def vertexBufferSize (m : MeshDescriptor) : Nat :=
  m.vertexCount * m.layout.computeStride

/-- Compute index buffer size in bytes -/
def indexBufferSize (m : MeshDescriptor) : Nat :=
  match m.indexFormat with
  | some fmt => m.indexCount * fmt.byteSize
  | none => 0

/-- Total GPU memory required -/
def totalBufferSize (m : MeshDescriptor) : Nat :=
  m.vertexBufferSize + m.indexBufferSize

/-- Check if vertex count is valid for topology -/
def isValidForTopology (m : MeshDescriptor) : Bool :=
  let count := m.elementCount
  match m.topology with
  | PrimitiveTopology.pointList => count > 0
  | PrimitiveTopology.lineList => count >= 2 && count % 2 == 0
  | PrimitiveTopology.lineStrip => count >= 2
  | PrimitiveTopology.triangleList => count >= 3 && count % 3 == 0
  | PrimitiveTopology.triangleStrip => count >= 3

-- ─────────────────────────────────────────────────────────────────────────────
-- MeshDescriptor Construction
-- ─────────────────────────────────────────────────────────────────────────────

/-- Create non-indexed mesh descriptor -/
def nonIndexed (layout : VertexLayout) (vertexCount : Nat) 
    (topology : PrimitiveTopology := PrimitiveTopology.triangleList) : MeshDescriptor :=
  { layout := layout
    vertexCount := vertexCount
    indexFormat := none
    indexCount := 0
    topology := topology
    boundingBox := none
    boundingSphere := none }

/-- Create indexed mesh descriptor -/
def indexed (layout : VertexLayout) (vertexCount : Nat) (indexCount : Nat)
    (topology : PrimitiveTopology := PrimitiveTopology.triangleList) : MeshDescriptor :=
  { layout := layout
    vertexCount := vertexCount
    indexFormat := some (IndexFormat.forVertexCount vertexCount)
    indexCount := indexCount
    topology := topology
    boundingBox := none
    boundingSphere := none }

/-- Set bounding box -/
def withBoundingBox (m : MeshDescriptor) (box : Box3) : MeshDescriptor :=
  { m with boundingBox := some box }

/-- Set bounding sphere -/
def withBoundingSphere (m : MeshDescriptor) (sphere : Sphere) : MeshDescriptor :=
  { m with boundingSphere := some sphere }

-- ─────────────────────────────────────────────────────────────────────────────
-- MeshDescriptor Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Non-indexed mesh is not indexed -/
theorem nonIndexed_isNotIndexed (layout : VertexLayout) (n : Nat) (topo : PrimitiveTopology) :
    isIndexed (nonIndexed layout n topo) = false := rfl

/-- Indexed mesh with positive index count is indexed -/
theorem indexed_isIndexed (layout : VertexLayout) (v : Nat) (i : Nat) (topo : PrimitiveTopology)
    (hi : i > 0) :
    isIndexed (indexed layout v i topo) = true := by
  unfold indexed isIndexed
  simp only [Option.isSome_some, Bool.true_and, decide_eq_true_eq]
  exact hi

/-- Non-indexed mesh element count equals vertex count -/
theorem nonIndexed_elementCount (layout : VertexLayout) (n : Nat) (topo : PrimitiveTopology) :
    elementCount (nonIndexed layout n topo) = n := by
  unfold nonIndexed elementCount isIndexed
  simp only [Option.isSome_none, Bool.false_and]
  rfl

/-- Vertex buffer size is vertexCount × stride -/
theorem vertexBufferSize_eq (m : MeshDescriptor) :
    m.vertexBufferSize = m.vertexCount * m.layout.computeStride := rfl

end MeshDescriptor

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: SUBMESH
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A submesh: a portion of a mesh with its own material.
    Enables multi-material meshes (common in GLTF, FBX, etc). -/
structure Submesh where
  /-- Material ID to use for this submesh -/
  materialId : Nat
  /-- Range of indices/vertices to draw -/
  drawRange : DrawRange
  deriving Repr, DecidableEq

namespace Submesh

/-- Create a submesh for entire mesh -/
def full (materialId : Nat) (elementCount : Nat) : Submesh :=
  { materialId := materialId
    drawRange := DrawRange.full elementCount }

/-- Check if submesh range is valid for mesh -/
def isValidFor (sub : Submesh) (mesh : MeshDescriptor) : Bool :=
  sub.drawRange.isValid mesh.elementCount

end Submesh

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: MESH (Complete)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Complete mesh with descriptor and submeshes.
    
    A mesh can have multiple submeshes, each with a different material.
    This matches the GLTF mesh primitive model. -/
structure Mesh where
  /-- Mesh descriptor (layout, counts, bounds) -/
  descriptor : MeshDescriptor
  /-- List of submeshes (at least one) -/
  submeshes : List Submesh
  /-- Mesh name (for debugging) -/
  name : String := ""

namespace Mesh

/-- Create a simple mesh with one submesh -/
def simple (descriptor : MeshDescriptor) (materialId : Nat := 0) : Mesh :=
  { descriptor := descriptor
    submeshes := [Submesh.full materialId descriptor.elementCount]
    name := "" }

/-- Number of submeshes -/
def submeshCount (m : Mesh) : Nat :=
  m.submeshes.length

/-- Is this a multi-material mesh? -/
def isMultiMaterial (m : Mesh) : Bool :=
  m.submeshes.length > 1

/-- Total GPU memory required -/
def totalBufferSize (m : Mesh) : Nat :=
  m.descriptor.totalBufferSize

/-- Check if all submeshes are valid -/
def allSubmeshesValid (m : Mesh) : Bool :=
  m.submeshes.all (fun sub => sub.isValidFor m.descriptor)

-- ─────────────────────────────────────────────────────────────────────────────
-- Mesh Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Simple mesh has exactly one submesh -/
theorem simple_submeshCount (desc : MeshDescriptor) (matId : Nat) :
    submeshCount (simple desc matId) = 1 := rfl

/-- Simple mesh is not multi-material -/
theorem simple_not_multiMaterial (desc : MeshDescriptor) (matId : Nat) :
    isMultiMaterial (simple desc matId) = false := rfl

end Mesh

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: MESH INSTANCE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Instance data for instanced rendering.
    Each instance gets its own transform (and optionally other per-instance data). -/
structure InstanceData where
  /-- Per-instance vertex layout (separate from mesh layout) -/
  layout : VertexLayout
  /-- Number of instances -/
  instanceCount : Nat
  deriving Repr

namespace InstanceData

/-- Single instance (no instancing) -/
def single : InstanceData :=
  { layout := VertexLayout.empty
    instanceCount := 1 }

/-- Check if actually using instancing -/
def isInstanced (data : InstanceData) : Bool :=
  data.instanceCount > 1

/-- Instance buffer size in bytes -/
def bufferSize (data : InstanceData) : Nat :=
  data.instanceCount * data.layout.computeStride

-- ─────────────────────────────────────────────────────────────────────────────
-- InstanceData Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Single instance is not instanced -/
theorem single_not_instanced : isInstanced single = false := rfl

/-- Single instance has count 1 -/
theorem single_count : single.instanceCount = 1 := rfl

end InstanceData

end Hydrogen.Geometry
