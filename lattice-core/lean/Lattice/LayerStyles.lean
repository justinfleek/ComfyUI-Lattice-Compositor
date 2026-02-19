/-
  Lattice.LayerStyles - Layer styles (shadows, glows, bevels, etc.)

  Main module that re-exports all layer style sub-modules.

  Refactored from: ui/src/types/layerStyles.ts (722 lines)
  Split into 2 modules under 500 lines each:
    - LayerStyles/Enums.lean (~120 lines)
    - LayerStyles/Core.lean (~300 lines)
  Total: ~420 lines across 3 files
-/

import Lattice.LayerStyles.Enums
import Lattice.LayerStyles.Core

namespace Lattice.LayerStyles

-- Re-export enums
export Lattice.LayerStyles.Enums (
  GlowTechnique InnerGlowSource
  BevelStyle BevelTechnique BevelDirection
  GradientOverlayType StrokePosition StrokeFillType
  StyleOrder
)

-- Re-export core types
export Lattice.LayerStyles.Core (
  StyleRGBA StyleGradientStop StyleGradientType StyleGradientDef
  ContourPoint ContourCurve
  BaseStyleFields
  DropShadowStyle InnerShadowStyle
  OuterGlowStyle InnerGlowStyle
  BevelEmbossStyle SatinStyle ColorOverlayStyle
  GradientOverlayStyle StrokeStyleDef
  ChannelBlendRange StyleBlendingOptions
  LayerStyles GlobalLightSettings
)

end Lattice.LayerStyles
