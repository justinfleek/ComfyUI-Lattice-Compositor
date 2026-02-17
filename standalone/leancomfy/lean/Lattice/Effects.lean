/-
  Lattice.Effects - Effect system types

  Main module that re-exports all effect sub-modules.

  Refactored from: ui/src/types/effects.ts (3339 lines)
  Split into 4 modules under 500 lines each:
    - Effects/Enums.lean (~280 lines)
    - Effects/Parameters.lean (~200 lines)
    - Effects/Core.lean (~180 lines)
    - Effects/Presets.lean (~180 lines)
  Total: ~840 lines across 5 files (avg 168 lines each)
-/

import Lattice.Effects.Enums
import Lattice.Effects.Parameters
import Lattice.Effects.Core
import Lattice.Effects.Presets

namespace Lattice.Effects

-- Re-export enums
export Lattice.Effects.Enums (
  EffectParameterType EffectAnimatableType
  BlurDimension RadialBlurType AntialiasingQuality RampShape WarpStyle
  DisplacementMapType DisplacementChannel EdgeBehavior
  GlowCompositeMode GlowColorsMode ColorLooping
  FalloffMode TonemapMode BloomBlendMode
  FractalType NoiseType EchoOperator TimeResolution
  PinFalloff TurbulentDisplaceType PinningMode
  ScanlinesDirection RGBSplitBlendMode
  PixelSortDirection SortByCriterion
  HalftoneColorMode DitherMethod DitherMatrixSize
  EffectColorChannel HSLChannel
)

-- Re-export parameters
export Lattice.Effects.Parameters (
  EffectPoint2D EffectPoint3D EffectRGBA CurvePoint
  EffectParameterValue DropdownOption
  EffectParameterDef EffectParameter
  mkNumberValue mkPoint2DValue mkPoint3DValue mkColorValue
  defaultNumberValue defaultPoint2DValue defaultPoint3DValue
  defaultColorValue defaultBlackValue
)

-- Re-export core
export Lattice.Effects.Core (
  Effect EffectInstance MeshDeformEffectInstance
  EffectDefinition EffectCategoryInfo
  CreateEffectInstance UpdateEffectInstance
  CreateMeshDeformEffectInstance
  meshDeformEffectKey defaultTriangleCount defaultExpansion defaultAlphaThreshold
)

-- Re-export presets
export Lattice.Effects.Presets (
  PresetCategory PresetBezierHandle PresetKeyframe
  PresetPropertyAnimation AnimationPreset
  mkLinearKeyframe mkEaseInOutKeyframe
  zeroOpacity fullOpacity zeroScale fullScale
  overshootScale undershootScale centerPosition offScreenRight
  zeroRotation fullRotation
)

end Lattice.Effects
