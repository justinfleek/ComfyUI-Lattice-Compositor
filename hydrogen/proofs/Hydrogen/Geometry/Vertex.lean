/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    HYDROGEN // GEOMETRY // VERTEX
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Vertex attribute types for GPU geometry.
  
  This module defines the fundamental vertex data structures that describe
  how geometry data is laid out in memory. WebGPU/GPU pipelines need exact
  knowledge of vertex layouts for shader binding.
  
  Key design decisions:
  - Attributes are PURE DATA describing layouts, not actual buffers
  - Stride and offset are computed, not hardcoded
  - Type system encodes valid attribute combinations
  - Proofs ensure stride calculations are correct

  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Vec2, Vec3, Vec4 : Vector types for attribute data
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Math.Vec2
import Hydrogen.Math.Vec3
import Hydrogen.Math.Vec4

namespace Hydrogen.Geometry

open Hydrogen.Math

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: ATTRIBUTE TYPES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Scalar types supported for vertex attributes.
    Maps directly to WebGPU/WGSL types. -/
inductive ScalarType where
  | float32   -- f32 (4 bytes)
  | float16   -- f16 (2 bytes, requires feature)
  | int32     -- i32 (4 bytes)
  | int16     -- i16 (2 bytes)
  | int8      -- i8 (1 byte)
  | uint32    -- u32 (4 bytes)
  | uint16    -- u16 (2 bytes)
  | uint8     -- u8 (1 byte)
  deriving Repr, DecidableEq

namespace ScalarType

/-- Size of scalar type in bytes -/
def byteSize : ScalarType → Nat
  | float32 => 4
  | float16 => 2
  | int32 => 4
  | int16 => 2
  | int8 => 1
  | uint32 => 4
  | uint16 => 2
  | uint8 => 1

/-- Alignment requirement for scalar type in bytes -/
def alignment : ScalarType → Nat
  | float32 => 4
  | float16 => 2
  | int32 => 4
  | int16 => 2
  | int8 => 1
  | uint32 => 4
  | uint16 => 2
  | uint8 => 1

end ScalarType

/-- Vector dimension for vertex attributes -/
inductive VecDimension where
  | scalar  -- 1 component
  | vec2    -- 2 components
  | vec3    -- 3 components
  | vec4    -- 4 components
  deriving Repr, DecidableEq

namespace VecDimension

/-- Number of components -/
def componentCount : VecDimension → Nat
  | scalar => 1
  | vec2 => 2
  | vec3 => 3
  | vec4 => 4

end VecDimension

/-- Complete vertex attribute format: scalar type × dimension -/
structure AttributeFormat where
  scalarType : ScalarType
  dimension : VecDimension
  deriving Repr, DecidableEq

namespace AttributeFormat

/-- Common formats -/
def float1 : AttributeFormat := ⟨ScalarType.float32, VecDimension.scalar⟩
def float2 : AttributeFormat := ⟨ScalarType.float32, VecDimension.vec2⟩
def float3 : AttributeFormat := ⟨ScalarType.float32, VecDimension.vec3⟩
def float4 : AttributeFormat := ⟨ScalarType.float32, VecDimension.vec4⟩

def uint8x4 : AttributeFormat := ⟨ScalarType.uint8, VecDimension.vec4⟩
def uint16x2 : AttributeFormat := ⟨ScalarType.uint16, VecDimension.vec2⟩

/-- Size of attribute in bytes -/
def byteSize (f : AttributeFormat) : Nat :=
  f.scalarType.byteSize * f.dimension.componentCount

/-- Alignment of attribute in bytes -/
def alignment (f : AttributeFormat) : Nat :=
  f.scalarType.alignment

-- ─────────────────────────────────────────────────────────────────────────────
-- AttributeFormat Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- float3 is 12 bytes -/
theorem float3_byteSize : float3.byteSize = 12 := rfl

/-- float4 is 16 bytes -/
theorem float4_byteSize : float4.byteSize = 16 := rfl

/-- float2 is 8 bytes -/
theorem float2_byteSize : float2.byteSize = 8 := rfl

/-- Byte size is always positive -/
theorem byteSize_pos (f : AttributeFormat) : f.byteSize > 0 := by
  unfold byteSize
  cases f.scalarType <;> cases f.dimension <;> decide

end AttributeFormat

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: VERTEX ATTRIBUTES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Semantic meaning of a vertex attribute.
    Used for automatic shader binding. -/
inductive AttributeSemantic where
  | position      -- POSITION: vertex position in local space
  | normal        -- NORMAL: surface normal vector
  | tangent       -- TANGENT: tangent vector for normal mapping
  | texcoord0     -- TEXCOORD_0: primary UV coordinates
  | texcoord1     -- TEXCOORD_1: secondary UV (lightmaps, etc)
  | color0        -- COLOR_0: vertex color
  | joints0       -- JOINTS_0: bone indices for skinning
  | weights0      -- WEIGHTS_0: bone weights for skinning
  | custom (name : String)  -- Custom attribute
  deriving Repr, DecidableEq

namespace AttributeSemantic

/-- Shader location for built-in semantics (WebGPU convention) -/
def location : AttributeSemantic → Nat
  | position => 0
  | normal => 1
  | tangent => 2
  | texcoord0 => 3
  | texcoord1 => 4
  | color0 => 5
  | joints0 => 6
  | weights0 => 7
  | custom _ => 8  -- Custom attributes start at 8

/-- Expected format for semantic (for validation) -/
def expectedFormat : AttributeSemantic → Option AttributeFormat
  | position => some AttributeFormat.float3
  | normal => some AttributeFormat.float3
  | tangent => some AttributeFormat.float4  -- w is handedness
  | texcoord0 => some AttributeFormat.float2
  | texcoord1 => some AttributeFormat.float2
  | color0 => some AttributeFormat.float4
  | joints0 => some ⟨ScalarType.uint16, VecDimension.vec4⟩
  | weights0 => some AttributeFormat.float4
  | custom _ => none  -- No validation for custom

end AttributeSemantic

/-- A single vertex attribute descriptor -/
structure VertexAttribute where
  /-- Semantic meaning -/
  semantic : AttributeSemantic
  /-- Data format -/
  format : AttributeFormat
  /-- Byte offset within the vertex (for interleaved) -/
  offset : Nat
  deriving Repr, DecidableEq

namespace VertexAttribute

/-- Size of this attribute in bytes -/
def byteSize (attr : VertexAttribute) : Nat :=
  attr.format.byteSize

/-- Shader location for this attribute -/
def location (attr : VertexAttribute) : Nat :=
  attr.semantic.location

end VertexAttribute

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: VERTEX LAYOUT
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Step mode for vertex buffer (per-vertex vs per-instance) -/
inductive StepMode where
  | vertex    -- Advance for each vertex
  | instance  -- Advance for each instance
  deriving Repr, DecidableEq

/-- Complete vertex layout: list of attributes with computed stride -/
structure VertexLayout where
  /-- List of attributes -/
  attributes : List VertexAttribute
  /-- Step mode -/
  stepMode : StepMode := StepMode.vertex
  deriving Repr, DecidableEq

namespace VertexLayout

/-- Compute stride (total bytes per vertex) from attributes -/
def computeStride (layout : VertexLayout) : Nat :=
  layout.attributes.foldl (fun acc attr => max acc (attr.offset + attr.byteSize)) 0

/-- Number of attributes -/
def attributeCount (layout : VertexLayout) : Nat :=
  layout.attributes.length

/-- Empty layout -/
def empty : VertexLayout :=
  { attributes := []
    stepMode := StepMode.vertex }

/-- Check if layout has a specific semantic -/
def hasSemantic (layout : VertexLayout) (sem : AttributeSemantic) : Bool :=
  layout.attributes.any (fun attr => attr.semantic == sem)

/-- Get attribute by semantic -/
def getAttribute (layout : VertexLayout) (sem : AttributeSemantic) : Option VertexAttribute :=
  layout.attributes.find? (fun attr => attr.semantic == sem)

-- ─────────────────────────────────────────────────────────────────────────────
-- Common Vertex Layouts
-- ─────────────────────────────────────────────────────────────────────────────

/-- Position only (12 bytes per vertex) -/
def positionOnly : VertexLayout :=
  { attributes := [
      { semantic := AttributeSemantic.position
        format := AttributeFormat.float3
        offset := 0 }
    ] }

/-- Position + Normal (24 bytes per vertex) -/
def positionNormal : VertexLayout :=
  { attributes := [
      { semantic := AttributeSemantic.position
        format := AttributeFormat.float3
        offset := 0 },
      { semantic := AttributeSemantic.normal
        format := AttributeFormat.float3
        offset := 12 }
    ] }

/-- Position + Normal + UV (32 bytes per vertex) -/
def positionNormalUV : VertexLayout :=
  { attributes := [
      { semantic := AttributeSemantic.position
        format := AttributeFormat.float3
        offset := 0 },
      { semantic := AttributeSemantic.normal
        format := AttributeFormat.float3
        offset := 12 },
      { semantic := AttributeSemantic.texcoord0
        format := AttributeFormat.float2
        offset := 24 }
    ] }

/-- Position + Normal + UV + Tangent (48 bytes per vertex) -/
def positionNormalUVTangent : VertexLayout :=
  { attributes := [
      { semantic := AttributeSemantic.position
        format := AttributeFormat.float3
        offset := 0 },
      { semantic := AttributeSemantic.normal
        format := AttributeFormat.float3
        offset := 12 },
      { semantic := AttributeSemantic.texcoord0
        format := AttributeFormat.float2
        offset := 24 },
      { semantic := AttributeSemantic.tangent
        format := AttributeFormat.float4
        offset := 32 }
    ] }

-- ─────────────────────────────────────────────────────────────────────────────
-- VertexLayout Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Empty layout has stride 0 -/
theorem empty_stride : computeStride empty = 0 := rfl

/-- Position-only layout has stride 12 -/
theorem positionOnly_stride : computeStride positionOnly = 12 := rfl

/-- Position+Normal layout has stride 24 -/
theorem positionNormal_stride : computeStride positionNormal = 24 := rfl

/-- Position+Normal+UV layout has stride 32 -/
theorem positionNormalUV_stride : computeStride positionNormalUV = 32 := rfl

/-- Position+Normal+UV+Tangent layout has stride 48 -/
theorem positionNormalUVTangent_stride : computeStride positionNormalUVTangent = 48 := rfl

/-- positionOnly has position attribute -/
theorem positionOnly_hasPosition : hasSemantic positionOnly AttributeSemantic.position = true := rfl

/-- positionNormal has both position and normal -/
theorem positionNormal_hasPositionAndNormal : 
    hasSemantic positionNormal AttributeSemantic.position = true ∧
    hasSemantic positionNormal AttributeSemantic.normal = true := by
  constructor <;> rfl

end VertexLayout

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: INDEX TYPES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Index buffer format -/
inductive IndexFormat where
  | uint16  -- 2 bytes, max 65535 vertices
  | uint32  -- 4 bytes, max 4 billion vertices
  deriving Repr, DecidableEq

namespace IndexFormat

/-- Size of index in bytes -/
def byteSize : IndexFormat → Nat
  | uint16 => 2
  | uint32 => 4

/-- Maximum vertex index supported -/
def maxIndex : IndexFormat → Nat
  | uint16 => 65535
  | uint32 => 4294967295

/-- Choose appropriate index format based on vertex count -/
def forVertexCount (vertexCount : Nat) : IndexFormat :=
  if vertexCount <= 65535 then uint16 else uint32

-- ─────────────────────────────────────────────────────────────────────────────
-- IndexFormat Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- uint16 is 2 bytes -/
theorem uint16_byteSize : uint16.byteSize = 2 := rfl

/-- uint32 is 4 bytes -/
theorem uint32_byteSize : uint32.byteSize = 4 := rfl

/-- Small vertex counts use uint16 -/
theorem forVertexCount_small : forVertexCount 1000 = uint16 := rfl

/-- Large vertex counts use uint32 -/
theorem forVertexCount_large : forVertexCount 100000 = uint32 := rfl

end IndexFormat

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: PRIMITIVE TOPOLOGY
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Primitive topology: how vertices are assembled into primitives -/
inductive PrimitiveTopology where
  | pointList      -- Each vertex is a point
  | lineList       -- Every 2 vertices form a line
  | lineStrip      -- Connected line segments
  | triangleList   -- Every 3 vertices form a triangle
  | triangleStrip  -- Connected triangles (shared edges)
  deriving Repr, DecidableEq

namespace PrimitiveTopology

/-- Vertices per primitive (for list topologies) -/
def verticesPerPrimitive : PrimitiveTopology → Nat
  | pointList => 1
  | lineList => 2
  | lineStrip => 2  -- First line is 2, each additional is 1
  | triangleList => 3
  | triangleStrip => 3  -- First triangle is 3, each additional is 1

/-- Compute primitive count from vertex/index count -/
def primitiveCount (topo : PrimitiveTopology) (vertexCount : Nat) : Nat :=
  match topo with
  | pointList => vertexCount
  | lineList => vertexCount / 2
  | lineStrip => if vertexCount >= 2 then vertexCount - 1 else 0
  | triangleList => vertexCount / 3
  | triangleStrip => if vertexCount >= 3 then vertexCount - 2 else 0

-- ─────────────────────────────────────────────────────────────────────────────
-- PrimitiveTopology Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Triangle list: 6 vertices = 2 triangles -/
theorem triangleList_primitiveCount_6 : primitiveCount triangleList 6 = 2 := rfl

/-- Triangle strip: 5 vertices = 3 triangles -/
theorem triangleStrip_primitiveCount_5 : primitiveCount triangleStrip 5 = 3 := rfl

/-- Line list: 4 vertices = 2 lines -/
theorem lineList_primitiveCount_4 : primitiveCount lineList 4 = 2 := rfl

end PrimitiveTopology

end Hydrogen.Geometry
