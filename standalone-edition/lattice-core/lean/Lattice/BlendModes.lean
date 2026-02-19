/-
  Lattice.BlendModes - Industry standard blend modes

  Max 500 lines.

  Source: ui/src/types/blendModes.ts (121 lines)
-/

import Lattice.Primitives

namespace Lattice.BlendModes

open Lattice.Primitives

/-! ## Blend Mode -/

/-- Industry standard blend modes organized by category -/
inductive BlendMode where
  -- Normal
  | normal
  | dissolve
  -- Darken
  | darken
  | multiply
  | colorBurn
  | linearBurn
  | darkerColor
  -- Lighten
  | lighten
  | screen
  | colorDodge
  | linearDodge
  | lighterColor
  | add
  -- Contrast
  | overlay
  | softLight
  | hardLight
  | vividLight
  | linearLight
  | pinLight
  | hardMix
  -- Inversion
  | difference
  | exclusion
  | subtract
  | divide
  -- Component (HSL)
  | hue
  | saturation
  | color
  | luminosity
  -- Utility/Advanced
  | stencilAlpha
  | stencilLuma
  | silhouetteAlpha
  | silhouetteLuma
  | alphaAdd
  | luminescentPremul
  -- Classic (legacy)
  | classicColorBurn
  | classicColorDodge
  deriving Repr, BEq, DecidableEq

/-! ## Blend Mode Category -/

/-- Blend mode category for UI organization -/
inductive BlendModeCategory where
  | normal
  | darken
  | lighten
  | contrast
  | inversion
  | component
  | utility
  deriving Repr, BEq, DecidableEq

/-! ## Category Functions -/

/-- Get the category for a blend mode -/
def BlendMode.category : BlendMode → BlendModeCategory
  -- Normal
  | .normal => BlendModeCategory.normal
  | .dissolve => BlendModeCategory.normal
  -- Darken
  | .darken => BlendModeCategory.darken
  | .multiply => BlendModeCategory.darken
  | .colorBurn => BlendModeCategory.darken
  | .linearBurn => BlendModeCategory.darken
  | .darkerColor => BlendModeCategory.darken
  -- Lighten
  | .lighten => BlendModeCategory.lighten
  | .screen => BlendModeCategory.lighten
  | .colorDodge => BlendModeCategory.lighten
  | .linearDodge => BlendModeCategory.lighten
  | .lighterColor => BlendModeCategory.lighten
  | .add => BlendModeCategory.lighten
  -- Contrast
  | .overlay => BlendModeCategory.contrast
  | .softLight => BlendModeCategory.contrast
  | .hardLight => BlendModeCategory.contrast
  | .vividLight => BlendModeCategory.contrast
  | .linearLight => BlendModeCategory.contrast
  | .pinLight => BlendModeCategory.contrast
  | .hardMix => BlendModeCategory.contrast
  -- Inversion
  | .difference => BlendModeCategory.inversion
  | .exclusion => BlendModeCategory.inversion
  | .subtract => BlendModeCategory.inversion
  | .divide => BlendModeCategory.inversion
  -- Component
  | .hue => BlendModeCategory.component
  | .saturation => BlendModeCategory.component
  | .color => BlendModeCategory.component
  | .luminosity => BlendModeCategory.component
  -- Utility
  | .stencilAlpha => BlendModeCategory.utility
  | .stencilLuma => BlendModeCategory.utility
  | .silhouetteAlpha => BlendModeCategory.utility
  | .silhouetteLuma => BlendModeCategory.utility
  | .alphaAdd => BlendModeCategory.utility
  | .luminescentPremul => BlendModeCategory.utility
  -- Classic (legacy) - categorized as darken/lighten equivalents
  | .classicColorBurn => BlendModeCategory.darken
  | .classicColorDodge => BlendModeCategory.lighten

/-- Get all blend modes in a category -/
def BlendModeCategory.modes : BlendModeCategory → Array BlendMode
  | .normal => #[.normal, .dissolve]
  | .darken => #[.darken, .multiply, .colorBurn, .linearBurn, .darkerColor]
  | .lighten => #[.lighten, .screen, .colorDodge, .linearDodge, .lighterColor, .add]
  | .contrast => #[.overlay, .softLight, .hardLight, .vividLight, .linearLight, .pinLight, .hardMix]
  | .inversion => #[.difference, .exclusion, .subtract, .divide]
  | .component => #[.hue, .saturation, .color, .luminosity]
  | .utility => #[.stencilAlpha, .stencilLuma, .silhouetteAlpha, .silhouetteLuma, .alphaAdd, .luminescentPremul]

/-- Get all blend modes -/
def allBlendModes : Array BlendMode :=
  #[
    -- Normal
    .normal, .dissolve,
    -- Darken
    .darken, .multiply, .colorBurn, .linearBurn, .darkerColor,
    -- Lighten
    .lighten, .screen, .colorDodge, .linearDodge, .lighterColor, .add,
    -- Contrast
    .overlay, .softLight, .hardLight, .vividLight, .linearLight, .pinLight, .hardMix,
    -- Inversion
    .difference, .exclusion, .subtract, .divide,
    -- Component
    .hue, .saturation, .color, .luminosity,
    -- Utility
    .stencilAlpha, .stencilLuma, .silhouetteAlpha, .silhouetteLuma, .alphaAdd, .luminescentPremul,
    -- Classic
    .classicColorBurn, .classicColorDodge
  ]

end Lattice.BlendModes
