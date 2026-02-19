/-
  Lattice.Services.Stylize.SortMetrics - Pixel Sorting Value Calculations

  Pure mathematical functions for computing pixel sort metrics:
  - Brightness (average RGB)
  - Saturation (HSL-based)
  - Hue (from RGB)

  Used by pixel sort effect to determine sorting order within intervals.

  Source: ui/src/services/effects/stylizeRenderer.ts (lines 73-96)
-/

namespace Lattice.Services.Stylize.SortMetrics

--------------------------------------------------------------------------------
-- Sort Metric Types
--------------------------------------------------------------------------------

/-- Sort metric type for pixel sorting -/
inductive SortBy
  | brightness   -- Average of RGB
  | saturation   -- HSL saturation
  | hue          -- HSL hue in degrees
deriving Repr, BEq, Inhabited

--------------------------------------------------------------------------------
-- Brightness
--------------------------------------------------------------------------------

/-- Calculate brightness as average of RGB channels.

    @param r Red channel (0-255 normalized to 0-1)
    @param g Green channel (0-255 normalized to 0-1)
    @param b Blue channel (0-255 normalized to 0-1)
    @return Brightness value in [0, 1] -/
def brightness (r g b : Float) : Float :=
  (r + g + b) / 3.0

--------------------------------------------------------------------------------
-- Saturation
--------------------------------------------------------------------------------

/-- Calculate HSL saturation from RGB.

    Saturation = (max - min) / (2 - max - min)  if L > 0.5
                (max - min) / (max + min)       otherwise

    @param r Red channel (0-1)
    @param g Green channel (0-1)
    @param b Blue channel (0-1)
    @return Saturation value in [0, 1] -/
def saturation (r g b : Float) : Float :=
  let maxVal := Float.max r (Float.max g b)
  let minVal := Float.min r (Float.min g b)
  if maxVal = minVal then 0.0
  else
    let l := (maxVal + minVal) / 2.0
    if l > 0.5 then
      (maxVal - minVal) / (2.0 - maxVal - minVal)
    else
      (maxVal - minVal) / (maxVal + minVal)

--------------------------------------------------------------------------------
-- Hue
--------------------------------------------------------------------------------

/-- Calculate hue from RGB in degrees [0, 360).

    Uses standard RGB to hue conversion.

    @param r Red channel (0-1)
    @param g Green channel (0-1)
    @param b Blue channel (0-1)
    @return Hue in degrees [0, 360) -/
def hue (r g b : Float) : Float :=
  let maxVal := Float.max r (Float.max g b)
  let minVal := Float.min r (Float.min g b)
  if maxVal = minVal then 0.0
  else
    let delta := maxVal - minVal
    let h := if maxVal = r then
               (g - b) / delta
             else if maxVal = g then
               2.0 + (b - r) / delta
             else
               4.0 + (r - g) / delta
    let hDeg := h * 60.0
    -- Normalize to [0, 360)
    if hDeg < 0.0 then hDeg + 360.0 else hDeg

--------------------------------------------------------------------------------
-- Sort Value Dispatcher
--------------------------------------------------------------------------------

/-- Get sort value for a pixel based on sorting criterion.

    @param sortBy Which metric to use for sorting
    @param r Red channel (0-1)
    @param g Green channel (0-1)
    @param b Blue channel (0-1)
    @return Sort value (higher = different position in sort order) -/
def getSortValue (sortBy : SortBy) (r g b : Float) : Float :=
  match sortBy with
  | SortBy.brightness => brightness r g b
  | SortBy.saturation => saturation r g b
  | SortBy.hue => hue r g b

--------------------------------------------------------------------------------
-- Interval Detection
--------------------------------------------------------------------------------

/-- Check if pixel difference exceeds threshold for interval boundary.

    Used to determine where to break sorting intervals.

    @param sortVal1 Sort value of first pixel
    @param sortVal2 Sort value of second pixel
    @param threshold Edge detection threshold [0, 1]
    @param smoothing Interval boundary smoothness [0, 1]
    @return True if difference exceeds adjusted threshold -/
def isIntervalBoundary (sortVal1 sortVal2 threshold smoothing : Float) : Bool :=
  let diff := Float.abs (sortVal2 - sortVal1)
  let adjustedThreshold := threshold * (1.0 - smoothing)
  diff > adjustedThreshold

end Lattice.Services.Stylize.SortMetrics
