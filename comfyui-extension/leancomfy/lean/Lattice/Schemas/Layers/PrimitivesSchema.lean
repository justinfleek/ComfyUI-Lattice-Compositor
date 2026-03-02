/-
  Lattice.Schemas.Layers.PrimitivesSchema - Layer primitive enums and types

  Foundational layer data types: blend modes, vectors, colors.

  Source: ui/src/schemas/layers/primitives-schema.ts
-/

namespace Lattice.Schemas.Layers.PrimitivesSchema

--------------------------------------------------------------------------------
-- Blend Mode
--------------------------------------------------------------------------------

/-- Blend modes for layer compositing -/
inductive BlendMode where
  | normal
  | multiply
  | screen
  | overlay
  | darken
  | lighten
  | colorDodge
  | colorBurn
  | hardLight
  | softLight
  | difference
  | exclusion
  | hue
  | saturation
  | color
  | luminosity
  | add
  | subtract
  | divide
  | classicColorDodge
  | classicColorBurn
  | stencilAlpha
  | stencilLuma
  | silhouetteAlpha
  | silhouetteLuma
  | behind
  | alphaAdd
  | dissolve
  deriving Repr, DecidableEq, Inhabited

def BlendMode.fromString : String → Option BlendMode
  | "normal" => some BlendMode.normal
  | "multiply" => some BlendMode.multiply
  | "screen" => some BlendMode.screen
  | "overlay" => some BlendMode.overlay
  | "darken" => some BlendMode.darken
  | "lighten" => some BlendMode.lighten
  | "color-dodge" => some BlendMode.colorDodge
  | "color-burn" => some BlendMode.colorBurn
  | "hard-light" => some BlendMode.hardLight
  | "soft-light" => some BlendMode.softLight
  | "difference" => some BlendMode.difference
  | "exclusion" => some BlendMode.exclusion
  | "hue" => some BlendMode.hue
  | "saturation" => some BlendMode.saturation
  | "color" => some BlendMode.color
  | "luminosity" => some BlendMode.luminosity
  | "add" => some BlendMode.add
  | "subtract" => some BlendMode.subtract
  | "divide" => some BlendMode.divide
  | "classic-color-dodge" => some BlendMode.classicColorDodge
  | "classic-color-burn" => some BlendMode.classicColorBurn
  | "stencil-alpha" => some BlendMode.stencilAlpha
  | "stencil-luma" => some BlendMode.stencilLuma
  | "silhouette-alpha" => some BlendMode.silhouetteAlpha
  | "silhouette-luma" => some BlendMode.silhouetteLuma
  | "behind" => some BlendMode.behind
  | "alpha-add" => some BlendMode.alphaAdd
  | "dissolve" => some BlendMode.dissolve
  | _ => none

def BlendMode.toString : BlendMode → String
  | BlendMode.normal => "normal"
  | BlendMode.multiply => "multiply"
  | BlendMode.screen => "screen"
  | BlendMode.overlay => "overlay"
  | BlendMode.darken => "darken"
  | BlendMode.lighten => "lighten"
  | BlendMode.colorDodge => "color-dodge"
  | BlendMode.colorBurn => "color-burn"
  | BlendMode.hardLight => "hard-light"
  | BlendMode.softLight => "soft-light"
  | BlendMode.difference => "difference"
  | BlendMode.exclusion => "exclusion"
  | BlendMode.hue => "hue"
  | BlendMode.saturation => "saturation"
  | BlendMode.color => "color"
  | BlendMode.luminosity => "luminosity"
  | BlendMode.add => "add"
  | BlendMode.subtract => "subtract"
  | BlendMode.divide => "divide"
  | BlendMode.classicColorDodge => "classic-color-dodge"
  | BlendMode.classicColorBurn => "classic-color-burn"
  | BlendMode.stencilAlpha => "stencil-alpha"
  | BlendMode.stencilLuma => "stencil-luma"
  | BlendMode.silhouetteAlpha => "silhouette-alpha"
  | BlendMode.silhouetteLuma => "silhouette-luma"
  | BlendMode.behind => "behind"
  | BlendMode.alphaAdd => "alpha-add"
  | BlendMode.dissolve => "dissolve"

--------------------------------------------------------------------------------
-- Quality Mode
--------------------------------------------------------------------------------

/-- Quality modes for rendering -/
inductive QualityMode where
  | draft
  | best
  deriving Repr, DecidableEq, Inhabited

def QualityMode.fromString : String → Option QualityMode
  | "draft" => some QualityMode.draft
  | "best" => some QualityMode.best
  | _ => none

def QualityMode.toString : QualityMode → String
  | QualityMode.draft => "draft"
  | QualityMode.best => "best"

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

/-- 2D vector -/
structure Vec2 where
  x : Float
  y : Float
  deriving Repr, DecidableEq, Inhabited

/-- 3D vector -/
structure Vec3 where
  x : Float
  y : Float
  z : Float
  deriving Repr, DecidableEq, Inhabited

/-- 2D or 3D position with optional z -/
structure Position2DOr3D where
  x : Float
  y : Float
  z : Option Float
  deriving Repr, DecidableEq, Inhabited

/-- RGBA color with values 0-1 -/
structure RGBAColor where
  r : Float
  g : Float
  b : Float
  a : Float
  deriving Repr, DecidableEq, Inhabited

/-- RGBA color with values 0-255 -/
structure RGBA255Color where
  r : Nat
  g : Nat
  b : Nat
  a : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Rectangle with x, y, width, height -/
structure Rect where
  x : Float
  y : Float
  width : Float
  height : Float
  deriving Repr, DecidableEq, Inhabited

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

def isValidVec2 (v : Vec2) : Bool :=
  v.x.isFinite && v.y.isFinite

def isValidVec3 (v : Vec3) : Bool :=
  v.x.isFinite && v.y.isFinite && v.z.isFinite

def isValidPosition2DOr3D (p : Position2DOr3D) : Bool :=
  p.x.isFinite && p.y.isFinite &&
  match p.z with
  | some z => z.isFinite
  | none => true

def isValidRGBAColor (c : RGBAColor) : Bool :=
  c.r >= 0 && c.r <= 1 &&
  c.g >= 0 && c.g <= 1 &&
  c.b >= 0 && c.b <= 1 &&
  c.a >= 0 && c.a <= 1

def isValidRGBA255Color (c : RGBA255Color) : Bool :=
  c.r <= 255 && c.g <= 255 && c.b <= 255 && c.a <= 255

def isValidRect (r : Rect) : Bool :=
  r.x.isFinite && r.y.isFinite &&
  r.width >= 0 && r.width.isFinite &&
  r.height >= 0 && r.height.isFinite

end Lattice.Schemas.Layers.PrimitivesSchema
