/-
  Lattice.Services.ColorCorrection.Adjustments - Pixel Adjustment Formulas

  Pure mathematical functions for color adjustment calculations:
  - Brightness/Contrast formulas
  - Levels mapping
  - Exposure calculation
  - Vibrance with skin protection

  All functions are total (no partial def) and deterministic.

  Source: ui/src/services/effects/colorRenderer.ts
-/

namespace Lattice.Services.ColorCorrection.Adjustments

--------------------------------------------------------------------------------
-- Brightness & Contrast
--------------------------------------------------------------------------------

/-- Calculate the contrast factor using the standard formula.

    Standard formula: (259 * (contrast * 255 + 255)) / (255 * (259 - contrast * 255))

    This formula maps contrast in -1..1 to a multiplier that:
    - At 0: returns 1.0 (no change)
    - At 1: returns very high value (maximum contrast)
    - At -1: returns very low value (minimum contrast)

    @param contrast Contrast value in -1..1 range
    @return Contrast multiplier factor -/
def contrastFactor (contrast : Float) : Float :=
  let c255 := contrast * 255.0
  (259.0 * (c255 + 255.0)) / (255.0 * (259.0 - c255))

/-- Calculate legacy contrast factor (simpler linear formula).

    Legacy formula: 1 + contrast

    @param contrast Contrast value in -1..1 range
    @return Simple contrast multiplier -/
def contrastFactorLegacy (contrast : Float) : Float :=
  1.0 + contrast

/-- Apply brightness and contrast to a single channel value.

    Formula:
    1. Add brightness: v' = v + brightness * 255
    2. Apply contrast: v'' = factor * (v' - 128) + 128

    @param value Input value (0-255)
    @param brightness Brightness adjustment (-1 to 1)
    @param factor Contrast factor (from contrastFactor function)
    @return Adjusted value (clamped to 0-255) -/
def applyBrightnessContrast (value brightness factor : Float) : Float :=
  let withBrightness := value + brightness * 255.0
  let withContrast := factor * (withBrightness - 128.0) + 128.0
  Float.max 0.0 (Float.min 255.0 withContrast)

--------------------------------------------------------------------------------
-- Levels
--------------------------------------------------------------------------------

/-- Apply levels adjustment to a single value.

    Formula:
    1. Input mapping: v' = (v - inputBlack) / (inputWhite - inputBlack)
    2. Gamma: v'' = v' ^ (1/gamma)
    3. Output mapping: v''' = outputBlack + v'' * (outputWhite - outputBlack)

    @param value Input value (0-255)
    @param inputBlack Input black point (0-255)
    @param inputWhite Input white point (0-255)
    @param gamma Gamma correction (0.01-10)
    @param outputBlack Output black point (0-255)
    @param outputWhite Output white point (0-255)
    @return Adjusted value (clamped to 0-255) -/
def applyLevels (value inputBlack inputWhite gamma outputBlack outputWhite : Float) : Float :=
  let inputRange := inputWhite - inputBlack
  -- Handle edge case of zero range
  let normalized := if inputRange < 0.01
                    then 0.0
                    else (value - inputBlack) / inputRange

  -- Clamp to 0-1 before gamma
  let clamped := Float.max 0.0 (Float.min 1.0 normalized)

  -- Apply gamma correction (gamma > 0 guaranteed by caller)
  let gammaInv := 1.0 / gamma
  let gammaCorrected := Float.pow clamped gammaInv

  -- Map to output range
  let outputRange := outputWhite - outputBlack
  let output := outputBlack + gammaCorrected * outputRange

  Float.max 0.0 (Float.min 255.0 output)

--------------------------------------------------------------------------------
-- Exposure
--------------------------------------------------------------------------------

/-- Apply photographic exposure adjustment.

    Formula:
    1. Exposure: v' = v * 2^exposure
    2. Offset: v'' = v' + offset
    3. Gamma: v''' = v'' ^ (1/gamma)

    @param value Normalized input value (0-1)
    @param exposure Exposure in stops (-5 to 5)
    @param offset Value offset (-1 to 1)
    @param gamma Gamma correction (0.1-10)
    @return Adjusted normalized value (clamped to 0-1) -/
def applyExposure (value exposure offset gamma : Float) : Float :=
  -- Apply exposure (2^exposure multiplier)
  let exposureMultiplier := Float.pow 2.0 exposure
  let withExposure := value * exposureMultiplier

  -- Apply offset
  let withOffset := withExposure + offset

  -- Clamp before gamma
  let clamped := Float.max 0.0 (Float.min 1.0 withOffset)

  -- Apply gamma (gamma > 0 guaranteed by caller)
  let gammaInv := 1.0 / gamma
  Float.pow clamped gammaInv

--------------------------------------------------------------------------------
-- Vibrance
--------------------------------------------------------------------------------

/-- Calculate skin protection factor.

    Skin tones (orange-ish colors) should be less affected by vibrance.
    This computes how "skin-like" a color is based on RGB ratios.

    Skin tones typically have R ≈ 0.8, G ≈ 0.5, B ≈ 0.3 (normalized).

    @param r Normalized red (0-1)
    @param g Normalized green (0-1)
    @param b Normalized blue (0-1)
    @return Protection factor (0-1, higher = more skin-like) -/
def skinProtection (r g b : Float) : Float :=
  let distance := Float.abs (r - 0.8) * 2.0 +
                  Float.abs (g - 0.5) * 2.0 +
                  Float.abs (b - 0.3) * 3.0
  1.0 - Float.max 0.0 (Float.min 1.0 distance)

/-- Calculate adaptive vibrance adjustment.

    Vibrance boosts less saturated colors more, and protects skin tones.

    @param currentSaturation Current color saturation (0-1)
    @param skinProtectionFactor Skin protection (0-1)
    @param vibrance Vibrance setting (-1 to 1)
    @return Vibrance adjustment amount -/
def vibranceAmount (currentSaturation skinProtectionFactor vibrance : Float) : Float :=
  vibrance * (1.0 - currentSaturation) * (1.0 - skinProtectionFactor * 0.5)

/-- Apply vibrance and saturation to RGB values.

    @param r Red (0-1)
    @param g Green (0-1)
    @param b Blue (0-1)
    @param lum Luminance (0-1)
    @param satAdjust Combined saturation adjustment factor
    @return (r', g', b') adjusted values (clamped to 0-1) -/
def applySaturationAdjustment (r g b lum satAdjust : Float) : Float × Float × Float :=
  let r' := lum + (r - lum) * satAdjust
  let g' := lum + (g - lum) * satAdjust
  let b' := lum + (b - lum) * satAdjust
  ( Float.max 0.0 (Float.min 1.0 r')
  , Float.max 0.0 (Float.min 1.0 g')
  , Float.max 0.0 (Float.min 1.0 b')
  )

--------------------------------------------------------------------------------
-- Color Balance
--------------------------------------------------------------------------------

/-- Calculate tonal weight for shadows (dark regions).

    Weight peaks at luminance 0, falls off by luminance 0.33.

    @param luminance Normalized luminance (0-1)
    @return Shadow weight (0-1) -/
def shadowWeight (luminance : Float) : Float :=
  Float.max 0.0 (1.0 - luminance * 3.0)

/-- Calculate tonal weight for highlights (bright regions).

    Weight peaks at luminance 1, falls off by luminance 0.67.

    @param luminance Normalized luminance (0-1)
    @return Highlight weight (0-1) -/
def highlightWeight (luminance : Float) : Float :=
  Float.max 0.0 ((luminance - 0.67) * 3.0)

/-- Calculate tonal weight for midtones.

    Midtones = 1 - shadows - highlights, peaks at luminance 0.5.

    @param shadowW Shadow weight
    @param highlightW Highlight weight
    @return Midtone weight (0-1) -/
def midtoneWeight (shadowW highlightW : Float) : Float :=
  1.0 - shadowW - highlightW

--------------------------------------------------------------------------------
-- Posterize
--------------------------------------------------------------------------------

/-- Calculate posterized value for a given number of levels.

    @param value Input value (0-255)
    @param levels Number of output levels (2-256)
    @return Posterized value (0-255) -/
def posterize (value : Float) (levels : Nat) : Float :=
  if levels < 2 then value
  else
    let levelsF := Float.ofNat levels
    let step := 255.0 / (levelsF - 1.0)
    let level := Float.round ((value / 255.0) * (levelsF - 1.0))
    Float.round (level * step)

--------------------------------------------------------------------------------
-- Threshold
--------------------------------------------------------------------------------

/-- Apply binary threshold to luminance.

    @param luminance Input luminance (0-255)
    @param threshold Threshold value (0-255)
    @return 0 or 255 -/
def threshold (luminance threshold : Float) : Float :=
  if luminance >= threshold then 255.0 else 0.0

end Lattice.Services.ColorCorrection.Adjustments
