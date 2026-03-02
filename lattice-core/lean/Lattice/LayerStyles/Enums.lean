/-
  Lattice.LayerStyles.Enums - Layer style enumerations

  Part of LayerStyles module. Max 500 lines.

  Source: ui/src/types/layerStyles.ts (lines 113-373)
-/

import Lattice.Primitives
import Lattice.Enums

namespace Lattice.LayerStyles.Enums

open Lattice.Primitives
open Lattice.Enums

/-! ## Glow Technique -/

/-- Glow rendering technique -/
inductive GlowTechnique where
  | softer
  | precise
  deriving Repr, BEq, DecidableEq

/-! ## Inner Glow Source -/

/-- Where inner glow originates from -/
inductive InnerGlowSource where
  | center
  | edge
  deriving Repr, BEq, DecidableEq

/-! ## Bevel Style -/

/-- Bevel style type -/
inductive BevelStyle where
  | outerBevel    -- Bevel on outside edge
  | innerBevel    -- Bevel on inside edge
  | emboss        -- Raised emboss
  | pillowEmboss  -- Sunken edges
  | strokeEmboss  -- Bevel on stroke
  deriving Repr, BEq, DecidableEq

/-! ## Bevel Technique -/

/-- Bevel rendering technique -/
inductive BevelTechnique where
  | smooth
  | chiselHard
  | chiselSoft
  deriving Repr, BEq, DecidableEq

/-! ## Bevel Direction -/

/-- Bevel direction -/
inductive BevelDirection where
  | up
  | down
  deriving Repr, BEq, DecidableEq

/-! ## Gradient Overlay Type -/

/-- Gradient overlay style type -/
inductive GradientOverlayType where
  | linear
  | radial
  | angle
  | reflected
  | diamond
  deriving Repr, BEq, DecidableEq

/-! ## Stroke Position -/

/-- Stroke position relative to edge -/
inductive StrokePosition where
  | outside
  | inside
  | center
  deriving Repr, BEq, DecidableEq

/-! ## Stroke Fill Type -/

/-- Stroke fill type -/
inductive StrokeFillType where
  | color
  | gradient
  | pattern
  deriving Repr, BEq, DecidableEq

/-! ## Style Order -/

/-- Layer style render order (back to front) -/
inductive StyleOrder where
  | dropShadow      -- 1. Behind layer
  | innerShadow     -- 2. Inside layer
  | outerGlow       -- 3. Behind layer
  | innerGlow       -- 4. Inside layer
  | bevelEmboss     -- 5. 3D appearance
  | satin           -- 6. Internal shading
  | colorOverlay    -- 7. Solid fill
  | gradientOverlay -- 8. Gradient fill
  | patternOverlay  -- 9. Pattern fill
  | stroke          -- 10. Outline
  deriving Repr, BEq, DecidableEq

/-! ## Style Order Index -/

/-- Get render order index (0 = first/back) -/
def StyleOrder.index : StyleOrder → Nat
  | dropShadow => 0
  | innerShadow => 1
  | outerGlow => 2
  | innerGlow => 3
  | bevelEmboss => 4
  | satin => 5
  | colorOverlay => 6
  | gradientOverlay => 7
  | patternOverlay => 8
  | stroke => 9

end Lattice.LayerStyles.Enums
