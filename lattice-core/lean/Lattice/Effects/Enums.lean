/-
  Lattice.Effects.Enums - Effect-specific enumerations

  Part of Effects module. Max 500 lines.

  Source: ui/src/types/effects.ts (lines 10-117)
-/

import Lattice.Primitives
import Lattice.Enums

namespace Lattice.Effects.Enums

open Lattice.Primitives
open Lattice.Enums

/-! ## Effect Parameter Type -/

/-- Type of effect parameter (determines UI widget and value type) -/
inductive EffectParameterType where
  | number     -- Numeric slider/input
  | color      -- Color picker (RGBA)
  | point      -- 2D point picker
  | point3D    -- 3D point picker
  | angle      -- Angle dial
  | checkbox   -- Boolean toggle
  | dropdown   -- Select menu
  | layer      -- Layer reference picker
  | string     -- Text input
  | curve      -- Bezier curve editor
  | data       -- Arbitrary JSON data
  deriving Repr, BEq, DecidableEq

/-- Animatable property type for effect parameters -/
inductive EffectAnimatableType where
  | number
  | position
  | color
  | enum
  | vector3
  deriving Repr, BEq, DecidableEq

/-- Get animatable type from parameter type -/
def EffectParameterType.toAnimatableType : EffectParameterType → EffectAnimatableType
  | number => EffectAnimatableType.number
  | angle => EffectAnimatableType.number
  | point => EffectAnimatableType.position
  | point3D => EffectAnimatableType.vector3
  | color => EffectAnimatableType.color
  | checkbox => EffectAnimatableType.enum
  | dropdown => EffectAnimatableType.enum
  | layer => EffectAnimatableType.enum
  | string => EffectAnimatableType.enum
  | curve => EffectAnimatableType.enum
  | data => EffectAnimatableType.enum

/-! ## Blur Dimension -/

/-- Blur direction -/
inductive BlurDimension where
  | both
  | horizontal
  | vertical
  deriving Repr, BEq, DecidableEq

/-! ## Radial Blur Type -/

/-- Type of radial blur -/
inductive RadialBlurType where
  | spin
  | zoom
  deriving Repr, BEq, DecidableEq

/-! ## Antialiasing Quality -/

/-- Antialiasing quality level -/
inductive AntialiasingQuality where
  | low
  | medium
  | high
  deriving Repr, BEq, DecidableEq

/-! ## Ramp Shape -/

/-- Gradient ramp shape -/
inductive RampShape where
  | linear
  | radial
  deriving Repr, BEq, DecidableEq

/-! ## Warp Style -/

/-- Warp distortion style -/
inductive WarpStyle where
  | arc
  | arcLower
  | arcUpper
  | arch
  | bulge
  | shellLower
  | shellUpper
  | flag
  | wave
  | fish
  | rise
  | fisheye
  | inflate
  | squeeze
  | twist
  deriving Repr, BEq, DecidableEq

/-! ## Displacement Map Type -/

/-- Type of displacement map -/
inductive DisplacementMapType where
  | layer
  | noise
  | gradientH
  | gradientV
  | radial
  | sineH
  | sineV
  | checker
  deriving Repr, BEq, DecidableEq

/-! ## Displacement Channel -/

/-- Channel to use for displacement -/
inductive DisplacementChannel where
  | red
  | green
  | blue
  | alpha
  | luminance
  | off
  deriving Repr, BEq, DecidableEq

/-! ## Edge Behavior -/

/-- Edge behavior for effects -/
inductive EdgeBehavior where
  | off      -- Clip
  | tiles    -- Wrap pixels
  | mirror   -- Mirror pixels
  deriving Repr, BEq, DecidableEq

/-! ## Composite Mode -/

/-- How to composite glow with original -/
inductive GlowCompositeMode where
  | onTop
  | behind
  | none
  deriving Repr, BEq, DecidableEq

/-! ## Glow Colors Mode -/

/-- Glow color source -/
inductive GlowColorsMode where
  | original
  | ab  -- A & B colors
  deriving Repr, BEq, DecidableEq

/-! ## Color Looping -/

/-- Color looping mode for glow -/
inductive ColorLooping where
  | none
  | sawtoothAB
  | sawtoothBA
  | triangle
  deriving Repr, BEq, DecidableEq

/-! ## Falloff Mode -/

/-- Falloff calculation mode -/
inductive FalloffMode where
  | inverseSquare  -- Cinematic
  | gaussian       -- Standard
  | exponential
  deriving Repr, BEq, DecidableEq

/-! ## Tonemap Mode -/

/-- Tonemapping algorithm -/
inductive TonemapMode where
  | none
  | aces
  | reinhard
  | hable  -- Uncharted 2
  deriving Repr, BEq, DecidableEq

/-! ## Bloom Blend Mode -/

/-- Blend mode for bloom effect -/
inductive BloomBlendMode where
  | add
  | screen
  | overlay
  | softLight
  deriving Repr, BEq, DecidableEq

/-! ## Fractal Type -/

/-- Fractal noise type -/
inductive FractalType where
  | basic
  | turbulentBasic
  | softLinear
  | turbulentSoft
  deriving Repr, BEq, DecidableEq

/-! ## Noise Type -/

/-- Noise interpolation type -/
inductive NoiseType where
  | block
  | linear
  | softLinear
  | spline
  deriving Repr, BEq, DecidableEq

/-! ## Echo Operator -/

/-- Blend operator for echo effect -/
inductive EchoOperator where
  | add
  | screen
  | maximum
  | minimum
  | compositeBack
  | compositeFront
  | blend
  deriving Repr, BEq, DecidableEq

/-! ## Time Resolution -/

/-- Time resolution for time displacement -/
inductive TimeResolution where
  | frame
  | half
  | quarter
  deriving Repr, BEq, DecidableEq

/-! ## Pin Falloff -/

/-- Falloff method for mesh deform pins -/
inductive PinFalloff where
  | inverseDistance
  | radialBasis
  deriving Repr, BEq, DecidableEq

/-! ## Turbulent Displacement Type -/

/-- Type of turbulent displacement -/
inductive TurbulentDisplaceType where
  | turbulent
  | bulge
  | twist
  | turbulentSmoother
  | horizontal
  | vertical
  | cross
  deriving Repr, BEq, DecidableEq

/-! ## Pinning Mode -/

/-- Pinning mode for turbulent displace -/
inductive PinningMode where
  | none
  | all
  | horizontal
  | vertical
  deriving Repr, BEq, DecidableEq

/-! ## Scanlines Direction -/

/-- Direction of scanlines -/
inductive ScanlinesDirection where
  | horizontal
  | vertical
  deriving Repr, BEq, DecidableEq

/-! ## RGB Split Blend Mode -/

/-- Blend mode for RGB split -/
inductive RGBSplitBlendMode where
  | screen
  | add
  | normal
  deriving Repr, BEq, DecidableEq

/-! ## Pixel Sort Direction -/

/-- Direction for pixel sorting -/
inductive PixelSortDirection where
  | horizontal
  | vertical
  deriving Repr, BEq, DecidableEq

/-! ## Sort By Criterion -/

/-- Criterion for pixel sorting -/
inductive SortByCriterion where
  | saturation
  | brightness
  | hue
  deriving Repr, BEq, DecidableEq

/-! ## Halftone Color Mode -/

/-- Color mode for halftone effect -/
inductive HalftoneColorMode where
  | grayscale
  | rgb
  | cmyk
  deriving Repr, BEq, DecidableEq

/-! ## Dither Method -/

/-- Dithering algorithm -/
inductive DitherMethod where
  | ordered        -- Bayer
  | floydSteinberg
  | atkinson
  deriving Repr, BEq, DecidableEq

/-! ## Dither Matrix Size -/

/-- Matrix size for ordered dithering -/
inductive DitherMatrixSize where
  | size2x2
  | size4x4
  | size8x8
  deriving Repr, BEq, DecidableEq

/-! ## LUT Color Channel -/

/-- Color channel for effects -/
inductive EffectColorChannel where
  | rgb
  | red
  | green
  | blue
  | alpha
  deriving Repr, BEq, DecidableEq

/-! ## HSL Channel -/

/-- Channel for hue/saturation effects -/
inductive HSLChannel where
  | master
  | reds
  | yellows
  | greens
  | cyans
  | blues
  | magentas
  deriving Repr, BEq, DecidableEq

end Lattice.Effects.Enums
