/-
  Lattice.Services.Blur.Sharpen - Unsharp Mask Mathematics

  Pure mathematical functions for image sharpening:
  - Unsharp mask formula
  - High-pass filter simulation
  - Threshold application

  Unsharp masking: sharpened = original + amount * (original - blurred)

  Source: ui/src/services/effects/blurRenderer.ts (lines 1476-1487)
-/

namespace Lattice.Services.Blur.Sharpen

--------------------------------------------------------------------------------
-- Unsharp Mask
--------------------------------------------------------------------------------

/-- Apply unsharp mask formula to a single value.

    Formula: sharpened = original + amount * (original - blurred)

    This enhances edges by amplifying the difference between
    original and blurred (which represents high-frequency detail).

    @param original Original pixel value (0-255)
    @param blurred Blurred pixel value (0-255)
    @param amount Sharpening amount (0-5, where 1 = 100%)
    @return Sharpened value (clamped to 0-255) -/
def unsharpMask (original blurred amount : Float) : Float :=
  let difference := original - blurred
  let sharpened := original + difference * amount
  Float.max 0.0 (Float.min 255.0 sharpened)

/-- Calculate the difference (high-pass) component.

    This represents the edge/detail information that will be amplified.

    @param original Original value
    @param blurred Blurred value
    @return Difference (can be negative) -/
def highPassComponent (original blurred : Float) : Float :=
  original - blurred

--------------------------------------------------------------------------------
-- Threshold Application
--------------------------------------------------------------------------------

/-- Check if difference exceeds threshold.

    Thresholding prevents sharpening of subtle noise/texture.

    @param original Original value
    @param blurred Blurred value
    @param threshold Minimum difference to sharpen
    @return True if should be sharpened -/
def exceedsThreshold (original blurred threshold : Float) : Bool :=
  Float.abs (original - blurred) >= threshold

/-- Apply unsharp mask with threshold.

    Only applies sharpening when the difference exceeds threshold.

    @param original Original pixel value
    @param blurred Blurred pixel value
    @param amount Sharpening amount
    @param threshold Minimum difference to sharpen
    @return Sharpened value (or original if below threshold) -/
def unsharpMaskWithThreshold (original blurred amount threshold : Float) : Float :=
  if exceedsThreshold original blurred threshold
  then unsharpMask original blurred amount
  else original

--------------------------------------------------------------------------------
-- Amount Conversion
--------------------------------------------------------------------------------

/-- Convert percentage amount to multiplier.

    100% = 1.0 multiplier (normal sharpening)
    200% = 2.0 multiplier (aggressive sharpening)

    @param percent Amount as percentage (0-500)
    @return Multiplier (0-5) -/
def percentToMultiplier (percent : Float) : Float :=
  percent / 100.0

/-- Clamp amount to valid range.

    @param amount Raw amount
    @return Clamped amount (0-5) -/
def clampAmount (amount : Float) : Float :=
  Float.max 0.0 (Float.min 5.0 amount)

--------------------------------------------------------------------------------
-- Edge Detection Estimation
--------------------------------------------------------------------------------

/-- Estimate edge strength at a pixel.

    This is a simplified measure based on how different
    the pixel is from its blurred neighborhood.

    @param original Original value
    @param blurred Blurred value
    @return Edge strength (0-255) -/
def edgeStrength (original blurred : Float) : Float :=
  Float.abs (original - blurred)

/-- Check if pixel is likely on an edge.

    @param original Original value
    @param blurred Blurred value
    @param edgeThreshold Minimum difference to consider as edge
    @return True if on edge -/
def isEdgePixel (original blurred edgeThreshold : Float) : Bool :=
  edgeStrength original blurred >= edgeThreshold

--------------------------------------------------------------------------------
-- Adaptive Sharpening
--------------------------------------------------------------------------------

/-- Calculate adaptive sharpening amount based on local contrast.

    Areas with more contrast (edges) get less additional sharpening
    to prevent over-sharpening. Flat areas get more.

    @param original Original value
    @param blurred Blurred value
    @param baseAmount Base sharpening amount
    @return Adapted amount -/
def adaptiveAmount (original blurred baseAmount : Float) : Float :=
  let contrast := edgeStrength original blurred
  let contrastNorm := Float.min 1.0 (contrast / 128.0)  -- Normalize to 0-1
  -- Reduce amount for high contrast areas
  baseAmount * (1.0 - contrastNorm * 0.5)

end Lattice.Services.Blur.Sharpen
