/-
  Lattice.MeshWarp - Mesh warp deformation types

  Refactored from: ui/src/types/meshWarp.ts (279 lines)
  Single file under 500 lines.

  Provides vector skinning-style deformation for spline layers,
  allowing organic animation by manipulating control pins.
-/

import Lattice.Primitives

namespace Lattice.MeshWarp

open Lattice.Primitives

/-! ## Pin Type Enum -/

/-- Type of warp pin -/
inductive WarpPinType where
  | position   -- Deform pin: Move mesh vertices by animating position
  | rotation   -- Rotation pin: Rotate around fixed point (legacy, use 'bend')
  | starch     -- Stiffness pin: Define rigid areas that resist deformation
  | overlap    -- Overlap pin: Control depth/z-order during deformation
  | bend       -- Bend pin: Rotation + scale at joints (position is fixed reference)
  | advanced   -- Advanced pin: Full transform control (position + rotation + scale)
  deriving Repr, BEq, DecidableEq

/-! ## Weight Method Enum -/

/-- Method for calculating pin influence weights -/
inductive WarpWeightMethod where
  | inverseDistance  -- Standard 1/d^n falloff
  | heatDiffusion    -- Heat equation simulation
  | radialBasis      -- RBF interpolation
  | bounded          -- Bounded biharmonic weights
  deriving Repr, BEq, DecidableEq

/-! ## Warp Pin -/

/-- A control pin for mesh warp deformation -/
structure WarpPin where
  id : NonEmptyString
  name : NonEmptyString
  pinType : WarpPinType
  position : NonEmptyString  -- AnimatableProperty ID for position
  radius : Float             -- Influence radius in pixels
  stiffness : Float          -- Stiffness/rigidity (0-1)
  rotation : NonEmptyString  -- AnimatableProperty ID for rotation
  scale : NonEmptyString     -- AnimatableProperty ID for scale
  depth : Float              -- Pin depth/priority
  selected : Bool
  inFront : Option NonEmptyString  -- AnimatableProperty ID for overlap depth
  -- Proofs
  radius_positive : radius > 0
  radius_finite : radius.isFinite
  stiffness_ge_0 : stiffness ≥ 0
  stiffness_le_1 : stiffness ≤ 1
  stiffness_finite : stiffness.isFinite
  depth_finite : depth.isFinite
  deriving Repr

/-! ## Pin Rest State -/

/-- Initial/rest state of a pin (before animation) -/
structure WarpPinRestState where
  pinId : NonEmptyString
  positionX : Float
  positionY : Float
  rotation : Float
  scale : Float
  inFront : Option Float
  -- Proofs
  positionX_finite : positionX.isFinite
  positionY_finite : positionY.isFinite
  rotation_finite : rotation.isFinite
  scale_finite : scale.isFinite
  deriving Repr

/-! ## Warp Mesh -/

/-- A triangulated mesh for warp deformation -/
structure WarpMesh where
  layerId : NonEmptyString
  pins : Array WarpPin
  triangulation : Array Nat        -- Triangle indices (triplets)
  weights : Array Float            -- Pin influence weights per vertex
  originalVertices : Array Float   -- Original (undeformed) vertex positions
  pinRestStates : Array WarpPinRestState
  vertexCount : Nat
  dirty : Bool
  -- Proof that triangulation indices are valid triplets
  h_triangles_mod_3 : triangulation.size % 3 = 0
  deriving Repr

/-! ## Deformation Result -/

/-- Control point with handles (for path reconstruction) -/
structure DeformedControlPoint where
  x : Float
  y : Float
  inHandleX : Float
  inHandleY : Float
  outHandleX : Float
  outHandleY : Float
  x_finite : x.isFinite
  y_finite : y.isFinite
  inHandleX_finite : inHandleX.isFinite
  inHandleY_finite : inHandleY.isFinite
  outHandleX_finite : outHandleX.isFinite
  outHandleY_finite : outHandleY.isFinite
  deriving Repr

/-- Result of deforming a mesh -/
structure WarpDeformationResult where
  vertices : Array Float
  controlPoints : Array DeformedControlPoint
  deriving Repr

/-! ## Weight Options -/

/-- Options for weight calculation -/
structure WarpWeightOptions where
  method : WarpWeightMethod
  falloffPower : Float       -- Falloff power for inverse-distance (typically 2)
  normalize : Bool           -- Whether to normalize weights to sum to 1
  minWeight : Float          -- Minimum weight threshold
  -- Proofs
  falloffPower_positive : falloffPower > 0
  falloffPower_finite : falloffPower.isFinite
  minWeight_ge_0 : minWeight ≥ 0
  minWeight_finite : minWeight.isFinite
  deriving Repr

/-! ## Default Values -/

/-- Default weight calculation options -/
def defaultWeightOptions : WarpWeightOptions :=
  ⟨WarpWeightMethod.inverseDistance, 2.0, true, 0.001,
   by decide, by decide, by decide, by decide⟩

/-! ## Pin Type Helpers -/

/-- Check if pin type uses position animation -/
def WarpPinType.usesPositionAnimation : WarpPinType → Bool
  | position => true
  | advanced => true
  | _ => false

/-- Check if pin type uses rotation animation -/
def WarpPinType.usesRotationAnimation : WarpPinType → Bool
  | rotation => true
  | bend => true
  | advanced => true
  | _ => false

/-- Check if pin type uses scale animation -/
def WarpPinType.usesScaleAnimation : WarpPinType → Bool
  | bend => true
  | advanced => true
  | _ => false

/-- Check if pin type uses stiffness -/
def WarpPinType.usesStiffness : WarpPinType → Bool
  | starch => true
  | _ => false

/-- Check if pin type uses overlap depth -/
def WarpPinType.usesOverlap : WarpPinType → Bool
  | overlap => true
  | _ => false

/-- Get default stiffness for pin type -/
def WarpPinType.defaultStiffness : WarpPinType → Float
  | starch => 1.0
  | _ => 0.0

end Lattice.MeshWarp
