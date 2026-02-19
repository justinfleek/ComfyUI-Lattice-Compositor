/-
  Lattice.Schemas.LayerStyles.LayerStylesSchema

  Layer styles enums (glow, bevel, stroke, gradient overlay, etc.).

  Source: ui/src/schemas/layerStyles/layerStyles-schema.ts
-/

namespace Lattice.Schemas.LayerStyles.LayerStylesSchema

--------------------------------------------------------------------------------
-- Gradient Type
--------------------------------------------------------------------------------

/-- Gradient type options -/
inductive GradientType where
  | linear
  | radial
  deriving Repr, DecidableEq, Inhabited

def gradientTypeFromString : String → Option GradientType
  | "linear" => some .linear
  | "radial" => some .radial
  | _ => Option.none

def gradientTypeToString : GradientType → String
  | .linear => "linear"
  | .radial => "radial"

--------------------------------------------------------------------------------
-- Glow Technique
--------------------------------------------------------------------------------

/-- Glow technique options -/
inductive GlowTechnique where
  | softer
  | precise
  deriving Repr, DecidableEq, Inhabited

def glowTechniqueFromString : String → Option GlowTechnique
  | "softer" => some .softer
  | "precise" => some .precise
  | _ => Option.none

def glowTechniqueToString : GlowTechnique → String
  | .softer => "softer"
  | .precise => "precise"

--------------------------------------------------------------------------------
-- Inner Glow Source
--------------------------------------------------------------------------------

/-- Inner glow source options -/
inductive InnerGlowSource where
  | center
  | edge
  deriving Repr, DecidableEq, Inhabited

def innerGlowSourceFromString : String → Option InnerGlowSource
  | "center" => some .center
  | "edge" => some .edge
  | _ => Option.none

def innerGlowSourceToString : InnerGlowSource → String
  | .center => "center"
  | .edge => "edge"

--------------------------------------------------------------------------------
-- Bevel Style
--------------------------------------------------------------------------------

/-- Bevel style options -/
inductive BevelStyle where
  | outer_bevel
  | inner_bevel
  | emboss
  | pillow_emboss
  | stroke_emboss
  deriving Repr, DecidableEq, Inhabited

def bevelStyleFromString : String → Option BevelStyle
  | "outer-bevel" => some .outer_bevel
  | "inner-bevel" => some .inner_bevel
  | "emboss" => some .emboss
  | "pillow-emboss" => some .pillow_emboss
  | "stroke-emboss" => some .stroke_emboss
  | _ => Option.none

def bevelStyleToString : BevelStyle → String
  | .outer_bevel => "outer-bevel"
  | .inner_bevel => "inner-bevel"
  | .emboss => "emboss"
  | .pillow_emboss => "pillow-emboss"
  | .stroke_emboss => "stroke-emboss"

--------------------------------------------------------------------------------
-- Bevel Technique
--------------------------------------------------------------------------------

/-- Bevel technique options -/
inductive BevelTechnique where
  | smooth
  | chisel_hard
  | chisel_soft
  deriving Repr, DecidableEq, Inhabited

def bevelTechniqueFromString : String → Option BevelTechnique
  | "smooth" => some .smooth
  | "chisel-hard" => some .chisel_hard
  | "chisel-soft" => some .chisel_soft
  | _ => Option.none

def bevelTechniqueToString : BevelTechnique → String
  | .smooth => "smooth"
  | .chisel_hard => "chisel-hard"
  | .chisel_soft => "chisel-soft"

--------------------------------------------------------------------------------
-- Bevel Direction
--------------------------------------------------------------------------------

/-- Bevel direction options -/
inductive BevelDirection where
  | up
  | down
  deriving Repr, DecidableEq, Inhabited

def bevelDirectionFromString : String → Option BevelDirection
  | "up" => some .up
  | "down" => some .down
  | _ => Option.none

def bevelDirectionToString : BevelDirection → String
  | .up => "up"
  | .down => "down"

--------------------------------------------------------------------------------
-- Gradient Overlay Type
--------------------------------------------------------------------------------

/-- Gradient overlay type options -/
inductive GradientOverlayType where
  | linear
  | radial
  | angle
  | reflected
  | diamond
  deriving Repr, DecidableEq, Inhabited

def gradientOverlayTypeFromString : String → Option GradientOverlayType
  | "linear" => some .linear
  | "radial" => some .radial
  | "angle" => some .angle
  | "reflected" => some .reflected
  | "diamond" => some .diamond
  | _ => Option.none

def gradientOverlayTypeToString : GradientOverlayType → String
  | .linear => "linear"
  | .radial => "radial"
  | .angle => "angle"
  | .reflected => "reflected"
  | .diamond => "diamond"

--------------------------------------------------------------------------------
-- Stroke Position
--------------------------------------------------------------------------------

/-- Stroke position options -/
inductive StrokePosition where
  | outside
  | inside
  | center
  deriving Repr, DecidableEq, Inhabited

def strokePositionFromString : String → Option StrokePosition
  | "outside" => some .outside
  | "inside" => some .inside
  | "center" => some .center
  | _ => Option.none

def strokePositionToString : StrokePosition → String
  | .outside => "outside"
  | .inside => "inside"
  | .center => "center"

--------------------------------------------------------------------------------
-- Stroke Fill Type
--------------------------------------------------------------------------------

/-- Stroke fill type options -/
inductive StrokeFillType where
  | color
  | gradient
  | pattern
  deriving Repr, DecidableEq, Inhabited

def strokeFillTypeFromString : String → Option StrokeFillType
  | "color" => some .color
  | "gradient" => some .gradient
  | "pattern" => some .pattern
  | _ => Option.none

def strokeFillTypeToString : StrokeFillType → String
  | .color => "color"
  | .gradient => "gradient"
  | .pattern => "pattern"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def MAX_GRADIENT_STOPS : Nat := 100
def MIN_GRADIENT_STOPS : Nat := 2
def MAX_CONTOUR_POINTS : Nat := 1000
def MIN_CONTOUR_POINTS : Nat := 2
def MAX_RGB : Nat := 255
def MIN_RGB : Nat := 0

end Lattice.Schemas.LayerStyles.LayerStylesSchema
