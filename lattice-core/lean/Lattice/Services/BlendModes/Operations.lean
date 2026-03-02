/-
  Lattice.Services.BlendModes.Operations - Blend mode operations

  Pure math functions implementing individual blend mode formulas.
  All operations work on 0-255 channel values.

  Source: ui/src/services/blendModes.ts (lines 150-361)
-/

import Lattice.Services.BlendModes.ColorSpace

namespace Lattice.Services.BlendModes.Operations

open Lattice.Services.BlendModes.ColorSpace

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

/-- Clamp value to 0-255 range -/
def clamp (value : Float) : Float :=
  Float.max 0.0 (Float.min 255.0 (Float.round value))

--------------------------------------------------------------------------------
-- Basic Blend Modes
--------------------------------------------------------------------------------

/-- Normal blend (returns blend value) -/
def blendNormal (_base blend : Float) : Float := blend

/-- Multiply: (Base * Blend) / 255 -/
def blendMultiply (base blend : Float) : Float :=
  (base * blend) / 255.0

/-- Screen: 255 - ((255 - Base) * (255 - Blend)) / 255 -/
def blendScreen (base blend : Float) : Float :=
  255.0 - ((255.0 - base) * (255.0 - blend)) / 255.0

/-- Overlay: Multiply if base < 128, Screen otherwise -/
def blendOverlay (base blend : Float) : Float :=
  if base < 128.0 then
    (2.0 * base * blend) / 255.0
  else
    255.0 - (2.0 * (255.0 - base) * (255.0 - blend)) / 255.0

/-- Darken: min(Base, Blend) -/
def blendDarken (base blend : Float) : Float :=
  Float.min base blend

/-- Lighten: max(Base, Blend) -/
def blendLighten (base blend : Float) : Float :=
  Float.max base blend

/-- Color Dodge: Base / (1 - Blend/255) * 255 -/
def blendColorDodge (base blend : Float) : Float :=
  if blend >= 255.0 then 255.0
  else clamp ((base * 255.0) / (255.0 - blend))

/-- Color Burn: 255 - (255 - Base) / (Blend/255) -/
def blendColorBurn (base blend : Float) : Float :=
  if blend <= 0.0 then 0.0
  else clamp (255.0 - ((255.0 - base) * 255.0) / blend)

/-- Hard Light: Overlay with base and blend swapped -/
def blendHardLight (base blend : Float) : Float :=
  if blend < 128.0 then
    (2.0 * base * blend) / 255.0
  else
    255.0 - (2.0 * (255.0 - base) * (255.0 - blend)) / 255.0

/-- Soft Light: Pegtop formula -/
def blendSoftLight (base blend : Float) : Float :=
  let b := base / 255.0
  let s := blend / 255.0
  let result := (1.0 - 2.0 * s) * b * b + 2.0 * s * b
  clamp (result * 255.0)

/-- Difference: |Base - Blend| -/
def blendDifference (base blend : Float) : Float :=
  Float.abs (base - blend)

/-- Exclusion: Base + Blend - 2 * Base * Blend / 255 -/
def blendExclusion (base blend : Float) : Float :=
  base + blend - (2.0 * base * blend) / 255.0

/-- Add (Linear Dodge): min(255, Base + Blend) -/
def blendAdd (base blend : Float) : Float :=
  Float.min 255.0 (base + blend)

--------------------------------------------------------------------------------
-- Extended Blend Modes
--------------------------------------------------------------------------------

/-- Linear Burn: Base + Blend - 255 -/
def blendLinearBurn (base blend : Float) : Float :=
  clamp (base + blend - 255.0)

/-- Vivid Light: Color Burn if blend <= 128, Color Dodge otherwise -/
def blendVividLight (base blend : Float) : Float :=
  if blend <= 128.0 then
    -- Color Burn variation
    if blend == 0.0 then 0.0
    else clamp (255.0 - ((255.0 - base) * 255.0) / (2.0 * blend))
  else
    -- Color Dodge variation
    let adjusted := 2.0 * (blend - 128.0)
    if adjusted >= 255.0 then 255.0
    else clamp ((base * 255.0) / (255.0 - adjusted))

/-- Linear Light: Linear Burn if blend <= 128, Linear Dodge otherwise -/
def blendLinearLight (base blend : Float) : Float :=
  if blend <= 128.0 then
    clamp (base + 2.0 * blend - 255.0)
  else
    clamp (base + 2.0 * (blend - 128.0))

/-- Pin Light: Darken if blend <= 128, Lighten otherwise -/
def blendPinLight (base blend : Float) : Float :=
  if blend <= 128.0 then
    Float.min base (2.0 * blend)
  else
    Float.max base (2.0 * (blend - 128.0))

/-- Hard Mix: 0 or 255 based on Vivid Light threshold -/
def blendHardMix (base blend : Float) : Float :=
  let vivid := blendVividLight base blend
  if vivid < 128.0 then 0.0 else 255.0

/-- Subtract: Base - Blend -/
def blendSubtract (base blend : Float) : Float :=
  clamp (base - blend)

/-- Divide: Base / Blend * 256 -/
def blendDivide (base blend : Float) : Float :=
  if blend == 0.0 then 255.0
  else clamp ((base * 256.0) / blend)

--------------------------------------------------------------------------------
-- Luminance-Based Blend Modes
--------------------------------------------------------------------------------

/-- Darker Color: Return color with lower luminance -/
def blendDarkerColor (baseR baseG baseB blendR blendG blendB : Float) : RGB :=
  let baseLum := getLuminance baseR baseG baseB
  let blendLum := getLuminance blendR blendG blendB
  if baseLum < blendLum then
    { r := baseR, g := baseG, b := baseB }
  else
    { r := blendR, g := blendG, b := blendB }

/-- Lighter Color: Return color with higher luminance -/
def blendLighterColor (baseR baseG baseB blendR blendG blendB : Float) : RGB :=
  let baseLum := getLuminance baseR baseG baseB
  let blendLum := getLuminance blendR blendG blendB
  if baseLum > blendLum then
    { r := baseR, g := baseG, b := baseB }
  else
    { r := blendR, g := blendG, b := blendB }

--------------------------------------------------------------------------------
-- HSL Component Blend Modes
--------------------------------------------------------------------------------

/-- Hue blend: Take hue from blend, saturation and luminance from base -/
def blendHue (baseR baseG baseB blendR blendG blendB : Float) : RGB :=
  let baseHsl := rgbToHsl baseR baseG baseB
  let blendHsl := rgbToHsl blendR blendG blendB
  hslToRgb { h := blendHsl.h, s := baseHsl.s, l := baseHsl.l }

/-- Saturation blend: Take saturation from blend, hue and luminance from base -/
def blendSaturation (baseR baseG baseB blendR blendG blendB : Float) : RGB :=
  let baseHsl := rgbToHsl baseR baseG baseB
  let blendHsl := rgbToHsl blendR blendG blendB
  hslToRgb { h := baseHsl.h, s := blendHsl.s, l := baseHsl.l }

/-- Color blend: Take hue and saturation from blend, luminance from base -/
def blendColor (baseR baseG baseB blendR blendG blendB : Float) : RGB :=
  let baseHsl := rgbToHsl baseR baseG baseB
  let blendHsl := rgbToHsl blendR blendG blendB
  hslToRgb { h := blendHsl.h, s := blendHsl.s, l := baseHsl.l }

/-- Luminosity blend: Take luminance from blend, hue and saturation from base -/
def blendLuminosity (baseR baseG baseB blendR blendG blendB : Float) : RGB :=
  let baseHsl := rgbToHsl baseR baseG baseB
  let blendHsl := rgbToHsl blendR blendG blendB
  hslToRgb { h := baseHsl.h, s := baseHsl.s, l := blendHsl.l }

--------------------------------------------------------------------------------
-- Alpha Blend Modes
--------------------------------------------------------------------------------

/-- Stencil Alpha: Multiply base alpha by blend alpha -/
def blendStencilAlpha (baseA blendA : Float) : Float :=
  Float.round ((baseA / 255.0) * (blendA / 255.0) * 255.0)

/-- Stencil Luma: Multiply base alpha by blend luminance -/
def blendStencilLuma (baseA blendR blendG blendB : Float) : Float :=
  let blendLum := getLuminance blendR blendG blendB / 255.0
  Float.round ((baseA / 255.0) * blendLum * 255.0)

/-- Silhouette Alpha: base * (1 - blend alpha) -/
def blendSilhouetteAlpha (baseA blendA : Float) : Float :=
  Float.round ((baseA / 255.0) * (1.0 - blendA / 255.0) * 255.0)

/-- Silhouette Luma: base * (1 - blend luminance) -/
def blendSilhouetteLuma (baseA blendR blendG blendB : Float) : Float :=
  let blendLum := getLuminance blendR blendG blendB / 255.0
  Float.round ((baseA / 255.0) * (1.0 - blendLum) * 255.0)

/-- Alpha Add: min(255, baseA + blendA) -/
def blendAlphaAdd (baseA blendA : Float) : Float :=
  clamp (baseA + blendA)

end Lattice.Services.BlendModes.Operations
