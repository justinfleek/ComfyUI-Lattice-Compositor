/-
  Lattice.Shapes.Primitives - Shape primitive types

  Part of Shapes module. Max 500 lines.

  Source: ui/src/types/shapes.ts (lines 16-56)
-/

import Lattice.Primitives
import Lattice.Shapes.Enums

namespace Lattice.Shapes.Primitives

open Lattice.Primitives
open Lattice.Shapes.Enums

/-! ## Base Types -/

/-- Bezier vertex with handles (relative to point) -/
structure BezierVertex where
  point : Vec2
  inHandle : Vec2   -- Relative to point
  outHandle : Vec2  -- Relative to point
  deriving Repr

/-- A bezier path (can be open or closed) -/
structure BezierPath where
  vertices : Array BezierVertex
  closed : Bool
  deriving Repr

/-- Proof that path has at least 2 vertices for valid path -/
structure ValidBezierPath extends BezierPath where
  h_min_vertices : vertices.size ≥ 2

/-! ## Color Types -/

/-- RGBA Color with proofs -/
structure ShapeColor where
  r : Nat  -- 0-255
  g : Nat  -- 0-255
  b : Nat  -- 0-255
  a : Float -- 0-1
  r_le_255 : r ≤ 255
  g_le_255 : g ≤ 255
  b_le_255 : b ≤ 255
  a_ge_0 : a ≥ 0
  a_le_1 : a ≤ 1
  a_finite : a.isFinite
  deriving Repr

/-- Smart constructor for ShapeColor -/
def ShapeColor.ofRGBA (r g b : Nat) (a : Float) : Option ShapeColor :=
  if hr : r ≤ 255 then
    if hg : g ≤ 255 then
      if hb : b ≤ 255 then
        if ha0 : a ≥ 0 then
          if ha1 : a ≤ 1 then
            if haf : a.isFinite then
              some ⟨r, g, b, a, hr, hg, hb, ha0, ha1, haf⟩
            else none
          else none
        else none
      else none
    else none
  else none

/-- Default white color -/
def ShapeColor.white : ShapeColor :=
  ⟨255, 255, 255, 1.0, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Default black color -/
def ShapeColor.black : ShapeColor :=
  ⟨0, 0, 0, 1.0, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## Gradient Types -/

/-- Gradient stop with position proof -/
structure GradientStop where
  position : Float  -- 0-1
  color : ShapeColor
  pos_ge_0 : position ≥ 0
  pos_le_1 : position ≤ 1
  pos_finite : position.isFinite
  deriving Repr

/-- Smart constructor for GradientStop -/
def GradientStop.ofPositionColor (pos : Float) (color : ShapeColor) : Option GradientStop :=
  if hp0 : pos ≥ 0 then
    if hp1 : pos ≤ 1 then
      if hpf : pos.isFinite then
        some ⟨pos, color, hp0, hp1, hpf⟩
      else none
    else none
  else none

/-- Gradient definition -/
structure GradientDef where
  gradientType : GradientType
  stops : Array GradientStop
  startPoint : Vec2  -- Normalized 0-1
  endPoint : Vec2    -- For linear: end point, for radial: edge point
  highlightLength : Option Float  -- Radial only: 0-100
  highlightAngle : Option Float   -- Radial only: degrees
  h_min_stops : stops.size ≥ 2
  deriving Repr

/-! ## Animatable Shape Property -/

/-- Animatable property reference (ID-based) -/
structure AnimatablePropertyRef where
  id : NonEmptyString
  deriving Repr

/-! ## Transform Types -/

/-- Shape transform -/
structure ShapeTransformData where
  anchorPoint : Vec2
  position : Vec2
  scale : Vec2        -- Percentage (100 = 100%)
  rotation : Float    -- Degrees
  skew : Float        -- Degrees
  skewAxis : Float    -- Degrees
  opacity : Float     -- 0-100%
  rotation_finite : rotation.isFinite
  skew_finite : skew.isFinite
  skewAxis_finite : skewAxis.isFinite
  opacity_ge_0 : opacity ≥ 0
  opacity_le_100 : opacity ≤ 100
  opacity_finite : opacity.isFinite
  deriving Repr

/-- Default shape transform -/
def ShapeTransformData.default : ShapeTransformData :=
  let v2_zero : Vec2 := ⟨0, 0, by decide, by decide⟩
  let v2_scale : Vec2 := ⟨100, 100, by decide, by decide⟩
  ⟨v2_zero, v2_zero, v2_scale, 0, 0, 0, 100,
   by decide, by decide, by decide,
   by decide, by decide, by decide⟩

end Lattice.Shapes.Primitives
