/-
  Lattice.Masks - Layer masks and track mattes

  Single file under 500 lines.

  Refactored from: ui/src/types/masks.ts (270 lines)
-/

import Lattice.Primitives
import Lattice.Enums

namespace Lattice.Masks

open Lattice.Primitives
open Lattice.Enums

/-! ## Matte Type -/

/-- Matte source types (uses layer above as matte source) -/
inductive MatteType where
  | none           -- No matte source
  | alpha          -- Use alpha channel of matte layer
  | alphaInverted  -- Invert alpha of matte layer
  | luma           -- Use luminance of matte layer
  | lumaInverted   -- Invert luminance of matte layer
  deriving Repr, BEq, DecidableEq

/-! ## Mask Mode -/

/-- Mask mode determines how multiple masks combine -/
inductive MaskModeCombine where
  | add        -- Union of masks (default)
  | subtract   -- Subtract this mask from previous
  | intersect  -- Intersection with previous
  | lighten    -- Max of mask values
  | darken     -- Min of mask values
  | difference -- Absolute difference
  | none       -- Mask is disabled
  deriving Repr, BEq, DecidableEq

/-! ## Mask Vertex -/

/-- Mask vertex with bezier handles -/
structure MaskVertex where
  x : Float
  y : Float
  inTangentX : Float
  inTangentY : Float
  outTangentX : Float
  outTangentY : Float
  x_finite : x.isFinite
  y_finite : y.isFinite
  inTangentX_finite : inTangentX.isFinite
  inTangentY_finite : inTangentY.isFinite
  outTangentX_finite : outTangentX.isFinite
  outTangentY_finite : outTangentY.isFinite
  deriving Repr

/-! ## Mask Path -/

/-- Mask path - collection of bezier vertices forming a shape -/
structure MaskPath where
  closed : Bool
  vertices : Array MaskVertex
  deriving Repr

/-! ## Layer Mask -/

/-- Layer mask - bezier path that clips layer content -/
structure LayerMask where
  id : NonEmptyString
  name : NonEmptyString
  enabled : Bool
  locked : Bool
  mode : MaskModeCombine
  inverted : Bool
  pathPropertyId : NonEmptyString      -- AnimatableProperty ID for path
  opacityPropertyId : NonEmptyString   -- AnimatableProperty ID (0-100)
  featherPropertyId : NonEmptyString   -- AnimatableProperty ID (pixels)
  featherXPropertyId : Option NonEmptyString  -- Optional horizontal feather
  featherYPropertyId : Option NonEmptyString  -- Optional vertical feather
  expansionPropertyId : NonEmptyString -- AnimatableProperty ID (expand/contract)
  color : NonEmptyString               -- Hex color for UI visualization
  deriving Repr

/-! ## Smart Constructors -/

/-- Create a mask vertex at position with no tangents -/
def mkCornerVertex (x y : Float) (hx : x.isFinite) (hy : y.isFinite) : MaskVertex :=
  { x, y,
    inTangentX := 0, inTangentY := 0,
    outTangentX := 0, outTangentY := 0,
    x_finite := hx, y_finite := hy,
    inTangentX_finite := by decide,
    inTangentY_finite := by decide,
    outTangentX_finite := by decide,
    outTangentY_finite := by decide }

/-- Kappa constant for bezier circle approximation -/
def bezierKappa : Float := 0.5522847498

/-! ## Mask Validation -/

/-- Check if mask path has minimum vertices -/
def MaskPath.isValid (p : MaskPath) : Bool :=
  p.vertices.size >= 3 || (!p.closed && p.vertices.size >= 2)

/-- Get vertex count -/
def MaskPath.vertexCount (p : MaskPath) : Nat :=
  p.vertices.size

/-! ## Default Values -/

/-- Default mask color (yellow) -/
def defaultMaskColor : String := "#FFFF00"

/-- Default ellipse mask color (cyan) -/
def defaultEllipseMaskColor : String := "#00FFFF"

/-! ## Mask Helpers -/

/-- Check if layer mask is active -/
def LayerMask.isActive (m : LayerMask) : Bool :=
  m.enabled && m.mode != MaskModeCombine.none

/-- Check if mask has feather -/
def LayerMask.hasFeather (m : LayerMask) : Bool :=
  m.featherXPropertyId.isSome || m.featherYPropertyId.isSome

end Lattice.Masks
