/-
  Lattice.Services.ColorSpace.TransferFunctions - Gamma/Transfer Functions

  Pure transfer functions for color space conversions:
  - sRGB gamma encoding/decoding
  - Simple power-law gamma
  - Linearization and gamma application

  Source: ui/src/services/colorManagement/ColorProfileService.ts
-/

namespace Lattice.Services.ColorSpace.TransferFunctions

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- RGB triplet (0-1 normalized) -/
structure RGB where
  r : Float
  g : Float
  b : Float
  deriving Repr, Inhabited, BEq

/-- Color space gamma type -/
inductive GammaType where
  | linear        -- No gamma (linear)
  | sRGB          -- sRGB transfer function
  | power (γ : Float)  -- Simple power-law gamma
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

/-- sRGB linear threshold for encoding -/
def srgbLinearThreshold : Float := 0.0031308

/-- sRGB linear threshold for decoding -/
def srgbDecodeThreshold : Float := 0.04045

/-- sRGB linear scale factor -/
def srgbLinearScale : Float := 12.92

/-- sRGB gamma exponent -/
def srgbGamma : Float := 2.4

/-- sRGB offset constant -/
def srgbOffset : Float := 0.055

/-- sRGB scale constant -/
def srgbScale : Float := 1.055

--------------------------------------------------------------------------------
-- sRGB Transfer Functions
--------------------------------------------------------------------------------

/-- sRGB transfer function: linearize a single value.

    Maps sRGB-encoded value to linear light value.
    Uses piecewise function: linear near black, power for rest. -/
def sRGBToLinear (value : Float) : Float :=
  if value <= srgbDecodeThreshold then
    value / srgbLinearScale
  else
    Float.pow ((value + srgbOffset) / srgbScale) srgbGamma

/-- sRGB inverse transfer: apply gamma to linear value.

    Maps linear light value to sRGB-encoded value. -/
def linearToSRGB (value : Float) : Float :=
  if value <= srgbLinearThreshold then
    value * srgbLinearScale
  else
    srgbScale * Float.pow value (1.0 / srgbGamma) - srgbOffset

--------------------------------------------------------------------------------
-- Simple Power-Law Gamma
--------------------------------------------------------------------------------

/-- Apply gamma expansion (linearize) with power law.

    value^gamma -/
def gammaToLinear (value : Float) (gamma : Float) : Float :=
  Float.pow (Float.max 0.0 value) gamma

/-- Apply gamma compression with power law.

    value^(1/gamma) -/
def linearToGamma (value : Float) (gamma : Float) : Float :=
  if gamma == 0.0 then value  -- Prevent division by zero
  else Float.pow (Float.max 0.0 value) (1.0 / gamma)

--------------------------------------------------------------------------------
-- RGB Operations
--------------------------------------------------------------------------------

/-- Apply function to each RGB component -/
def mapRGB (f : Float → Float) (rgb : RGB) : RGB :=
  { r := f rgb.r, g := f rgb.g, b := f rgb.b }

/-- Linearize RGB based on gamma type -/
def linearizeRGB (rgb : RGB) (gammaType : GammaType) : RGB :=
  match gammaType with
  | .linear => rgb
  | .sRGB => mapRGB sRGBToLinear rgb
  | .power γ => mapRGB (gammaToLinear · γ) rgb

/-- Apply gamma to linear RGB -/
def applyGammaRGB (rgb : RGB) (gammaType : GammaType) : RGB :=
  match gammaType with
  | .linear => rgb
  | .sRGB => mapRGB linearToSRGB rgb
  | .power γ => mapRGB (linearToGamma · γ) rgb

--------------------------------------------------------------------------------
-- Common Gamma Values
--------------------------------------------------------------------------------

/-- sRGB gamma type -/
def gammaSRGB : GammaType := .sRGB

/-- Linear gamma type -/
def gammaLinear : GammaType := .linear

/-- Wide-Gamut RGB gamma (2.2) -/
def gammaWideGamut : GammaType := .power 2.2

/-- ProPhoto RGB gamma (1.8) -/
def gammaProPhoto : GammaType := .power 1.8

/-- Rec. 709 gamma (2.4) -/
def gammaRec709 : GammaType := .power 2.4

/-- Rec. 2020 gamma (2.4) -/
def gammaRec2020 : GammaType := .power 2.4

--------------------------------------------------------------------------------
-- Clamping
--------------------------------------------------------------------------------

/-- Clamp value to [0, 1] range -/
def clamp01 (v : Float) : Float :=
  Float.max 0.0 (Float.min 1.0 v)

/-- Clamp RGB to [0, 1] range -/
def clampRGB (rgb : RGB) : RGB :=
  mapRGB clamp01 rgb

--------------------------------------------------------------------------------
-- Conversion Helpers
--------------------------------------------------------------------------------

/-- Convert 8-bit value (0-255) to normalized (0-1) -/
def from8bit (v : UInt8) : Float :=
  v.toNat.toFloat / 255.0

/-- Convert normalized (0-1) to 8-bit (0-255) -/
def to8bit (v : Float) : UInt8 :=
  let clamped := clamp01 v
  (clamped * 255.0).toUInt64.toUInt8

/-- Create RGB from 8-bit values -/
def rgb8 (r g b : UInt8) : RGB :=
  { r := from8bit r, g := from8bit g, b := from8bit b }

/-- Convert RGB to 8-bit tuple -/
def toRGB8 (rgb : RGB) : UInt8 × UInt8 × UInt8 :=
  (to8bit rgb.r, to8bit rgb.g, to8bit rgb.b)

end Lattice.Services.ColorSpace.TransferFunctions
