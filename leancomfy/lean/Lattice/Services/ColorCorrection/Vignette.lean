/-
  Lattice.Services.ColorCorrection.Vignette - Vignette Effect Math

  Pure mathematical functions for vignette effect calculations:
  - Distance from center
  - Smoothstep interpolation
  - Vignette falloff

  All functions are total (no partial def) and deterministic.

  Source: ui/src/services/effects/colorRenderer.ts (lines 1544-1628)
-/

namespace Lattice.Services.ColorCorrection.Vignette

--------------------------------------------------------------------------------
-- Smoothstep
--------------------------------------------------------------------------------

/-- Smoothstep interpolation function.

    Provides smooth Hermite interpolation between 0 and 1.

    Formula: smoothstep(t) = t² × (3 - 2t)

    Properties:
    - smoothstep(0) = 0
    - smoothstep(1) = 1
    - First derivative is 0 at both endpoints

    @param t Input value (typically 0-1)
    @return Smoothed value -/
def smoothstep (t : Float) : Float :=
  t * t * (3.0 - 2.0 * t)

/-- Clamped smoothstep for values outside 0-1.

    @param edge0 Lower edge
    @param edge1 Upper edge
    @param x Input value
    @return Clamped smoothstep result -/
def smoothstepClamped (edge0 edge1 x : Float) : Float :=
  let range := edge1 - edge0
  let t := if range < 0.0001
           then 0.0
           else Float.max 0.0 (Float.min 1.0 ((x - edge0) / range))
  smoothstep t

--------------------------------------------------------------------------------
-- Distance Calculations
--------------------------------------------------------------------------------

/-- Calculate normalized distance from center of image.

    @param x Pixel X coordinate
    @param y Pixel Y coordinate
    @param centerX Image center X
    @param centerY Image center Y
    @param maxDist Maximum distance (corner distance)
    @param aspectX X aspect ratio adjustment (≥1 stretches horizontally)
    @param aspectY Y aspect ratio adjustment (≥1 stretches vertically)
    @return Normalized distance (0-1, where 1 is at corners) -/
def normalizedDistance (x y centerX centerY maxDist aspectX aspectY : Float) : Float :=
  let dx := (x - centerX) * aspectX
  let dy := (y - centerY) * aspectY
  let dist := Float.sqrt (dx * dx + dy * dy)
  if maxDist < 0.0001 then 0.0 else dist / maxDist

/-- Calculate max distance from center to corner.

    @param width Image width
    @param height Image height
    @return Distance from center to corner -/
def maxDistanceFromCenter (width height : Float) : Float :=
  let cx := width / 2.0
  let cy := height / 2.0
  Float.sqrt (cx * cx + cy * cy)

--------------------------------------------------------------------------------
-- Vignette Calculation
--------------------------------------------------------------------------------

/-- Calculate aspect ratio adjustments from roundness parameter.

    Roundness controls the vignette shape:
    - Negative: horizontal ellipse
    - Zero: circle
    - Positive: vertical ellipse

    @param roundness Roundness value (-1 to 1)
    @return (aspectX, aspectY) adjustments -/
def aspectFromRoundness (roundness : Float) : Float × Float :=
  let aspectX := 1.0 + (if roundness > 0.0 then roundness * 0.5 else 0.0)
  let aspectY := 1.0 + (if roundness < 0.0 then -roundness * 0.5 else 0.0)
  (aspectX, aspectY)

/-- Calculate vignette factor for a single pixel.

    The factor determines how much to darken/lighten the pixel.

    @param dist Normalized distance from center (0-1)
    @param midpoint Where falloff starts (0-1)
    @param feather Edge softness (0.01-1)
    @return Vignette factor (0-1, where 1 is full vignette effect) -/
def vignetteFactor (dist midpoint feather : Float) : Float :=
  if dist <= midpoint then
    0.0  -- Inside midpoint, no vignette
  else
    -- Calculate falloff using smoothstep
    let range := 1.0 - midpoint + 0.001  -- Avoid division by zero
    let t := (dist - midpoint) / range
    let smoothT := smoothstep t
    -- Apply feather as power curve
    let safeFeather := Float.max 0.01 feather
    Float.pow smoothT (1.0 / safeFeather)

/-- Apply vignette to a pixel value.

    @param value Input pixel value (0-255)
    @param factor Vignette factor (0-1)
    @param amount Vignette amount (-1 to 1, negative = lighten edges)
    @return Adjusted pixel value (0-255) -/
def applyVignette (value factor amount : Float) : Float :=
  let multiplier := 1.0 - factor * amount
  Float.max 0.0 (Float.min 255.0 (value * multiplier))

--------------------------------------------------------------------------------
-- Complete Vignette Calculation
--------------------------------------------------------------------------------

/-- Calculate vignette for a complete pixel.

    Combines all steps: distance, aspect ratio, factor, and application.

    @param x Pixel X coordinate
    @param y Pixel Y coordinate
    @param width Image width
    @param height Image height
    @param amount Vignette intensity (-1 to 1)
    @param midpoint Falloff start (0-1)
    @param roundness Shape (-1 to 1)
    @param feather Edge softness (0.01-1)
    @return Vignette multiplier for this pixel -/
def vignetteMultiplier
    (x y width height : Float)
    (amount midpoint roundness feather : Float) : Float :=
  let centerX := width / 2.0
  let centerY := height / 2.0
  let maxDist := maxDistanceFromCenter width height
  let (aspectX, aspectY) := aspectFromRoundness roundness

  let dist := normalizedDistance x y centerX centerY maxDist aspectX aspectY
  let factor := vignetteFactor dist midpoint feather

  1.0 - factor * amount

end Lattice.Services.ColorCorrection.Vignette
