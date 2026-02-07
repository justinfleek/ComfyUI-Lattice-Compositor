/-
  Lattice.Effects.Core - Effect and EffectInstance types

  Part of Effects module. Max 500 lines.

  Source: ui/src/types/effects.ts (lines 64-101, 148-207)
-/

import Lattice.Primitives
import Lattice.Enums
import Lattice.Effects.Enums
import Lattice.Effects.Parameters
import Lattice.MeshWarp

namespace Lattice.Effects.Core

open Lattice.Primitives
open Lattice.Enums
open Lattice.Effects.Enums
open Lattice.Effects.Parameters
open Lattice.MeshWarp

/-! ## Effect (Legacy) -/

/-- Effect with inline parameters (legacy structure) -/
structure Effect where
  id : NonEmptyString
  name : NonEmptyString
  category : EffectCategory
  enabled : Bool
  expanded : Bool
  parameters : Array EffectParameter
  fragmentShader : Option String
  deriving Repr

/-! ## Effect Instance -/

/-- Effect instance stored on a layer (parameters are animatable property IDs) -/
structure EffectInstance where
  id : NonEmptyString
  effectKey : NonEmptyString        -- Key into effect definitions (e.g., "gaussian-blur")
  name : NonEmptyString
  category : EffectCategory
  enabled : Bool
  expanded : Bool
  parameters : Array NonEmptyString  -- AnimatableProperty IDs
  deriving Repr

/-! ## Mesh Deform Effect Instance -/

/-- Mesh deform effect instance with puppet pins -/
structure MeshDeformEffectInstance extends EffectInstance where
  pins : Array WarpPin
  cachedMeshId : Option NonEmptyString  -- Reference to cached mesh
  meshDirty : Bool
  deriving Repr

/-! ## Effect Definition -/

/-- Effect definition (template for creating effect instances) -/
structure EffectDefinition where
  name : NonEmptyString
  category : EffectCategory
  description : String
  parameters : Array EffectParameterDef
  fragmentShader : Option String
  deriving Repr

/-! ## Effect Category Info -/

/-- Effect category information for UI -/
structure EffectCategoryInfo where
  label : NonEmptyString
  icon : String
  description : String
  deriving Repr

/-! ## Effect Creation -/

/-- Create effect instance from definition (returns just the structure, not full instance) -/
structure CreateEffectInstance where
  effectKey : NonEmptyString
  layerId : NonEmptyString
  deriving Repr

/-! ## Effect Update -/

/-- Update effect instance -/
structure UpdateEffectInstance where
  enabled : Option Bool
  expanded : Option Bool
  parameters : Option (Array NonEmptyString)
  deriving Repr

/-! ## Mesh Deform Creation -/

/-- Create mesh deform effect instance -/
structure CreateMeshDeformEffectInstance where
  layerId : NonEmptyString
  triangleCount : Nat
  expansion : Float
  alphaThreshold : Nat
  h_triangle_count_ge_50 : triangleCount ≥ 50
  h_triangle_count_le_1000 : triangleCount ≤ 1000
  h_expansion_ge_0 : expansion ≥ 0
  h_expansion_le_50 : expansion ≤ 50
  h_expansion_finite : expansion.isFinite
  h_alpha_le_255 : alphaThreshold ≤ 255
  deriving Repr

/-! ## Type Guards -/

/-- Check if effect instance is a mesh deform effect -/
def EffectInstance.isMeshDeform (e : EffectInstance) : Bool :=
  e.effectKey.val == "mesh-deform"

/-! ## Effect Constants -/

/-- Mesh deform effect key -/
def meshDeformEffectKey : NonEmptyString :=
  ⟨"mesh-deform", by decide⟩

/-! ## Default Values -/

/-- Default mesh deform triangle count -/
def defaultTriangleCount : Nat := 200

/-- Default mesh deform expansion -/
def defaultExpansion : Float := 3.0

/-- Default mesh deform alpha threshold -/
def defaultAlphaThreshold : Nat := 128

/-! ## Effect Instance Helpers -/

/-- Get parameter count for effect instance -/
def EffectInstance.parameterCount (e : EffectInstance) : Nat :=
  e.parameters.size

/-- Check if effect instance has parameters -/
def EffectInstance.hasParameters (e : EffectInstance) : Bool :=
  e.parameters.size > 0

/-! ## Mesh Deform Helpers -/

/-- Get pin count for mesh deform effect -/
def MeshDeformEffectInstance.pinCount (e : MeshDeformEffectInstance) : Nat :=
  e.pins.size

/-- Check if mesh deform needs rebuild -/
def MeshDeformEffectInstance.needsRebuild (e : MeshDeformEffectInstance) : Bool :=
  e.meshDirty || e.cachedMeshId.isNone

/-- Mark mesh as dirty -/
def MeshDeformEffectInstance.markDirty (e : MeshDeformEffectInstance) : MeshDeformEffectInstance :=
  { e with meshDirty := true }

/-- Mark mesh as clean -/
def MeshDeformEffectInstance.markClean (e : MeshDeformEffectInstance) (meshId : NonEmptyString) : MeshDeformEffectInstance :=
  { e with meshDirty := false, cachedMeshId := some meshId }

end Lattice.Effects.Core
