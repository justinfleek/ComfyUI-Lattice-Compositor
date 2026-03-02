/-
  Lattice.Services.Stylize.Halftone - Halftone Pattern Mathematics

  Pure mathematical functions for halftone effect:
  - RGB to CMYK conversion
  - Dot size calculation from brightness
  - CMYK angle offsets

  Source: ui/src/services/effects/stylizeRenderer.ts (lines 642-788)
-/

namespace Lattice.Services.Stylize.Halftone

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- CMYK color values -/
structure CMYK where
  c : Float   -- Cyan [0, 1]
  m : Float   -- Magenta [0, 1]
  y : Float   -- Yellow [0, 1]
  k : Float   -- Key/Black [0, 1]
deriving Repr, Inhabited

/-- Halftone color mode -/
inductive ColorMode
  | grayscale   -- Single black dots
  | rgb         -- Separate RGB dot layers
  | cmyk        -- Print-style CMYK dots
deriving Repr, BEq, Inhabited

--------------------------------------------------------------------------------
-- RGB to CMYK Conversion
--------------------------------------------------------------------------------

/-- Convert RGB to CMYK color space.

    K (black) = 1 - max(R, G, B)
    C = (1 - R - K) / (1 - K)   if K < 1
    M = (1 - G - K) / (1 - K)   if K < 1
    Y = (1 - B - K) / (1 - K)   if K < 1

    @param r Red channel (0-1)
    @param g Green channel (0-1)
    @param b Blue channel (0-1)
    @return CMYK values -/
def rgbToCMYK (r g b : Float) : CMYK :=
  let k := 1.0 - Float.max r (Float.max g b)
  if k >= 1.0 then
    { c := 0.0, m := 0.0, y := 0.0, k := 1.0 }
  else
    let invK := 1.0 - k
    { c := (1.0 - r - k) / invK
    , m := (1.0 - g - k) / invK
    , y := (1.0 - b - k) / invK
    , k := k }

--------------------------------------------------------------------------------
-- Dot Size Calculation
--------------------------------------------------------------------------------

/-- Calculate halftone dot radius from brightness.

    For grayscale: darker areas have larger dots (inverse brightness).
    For color: dot size proportional to channel value.

    @param value Brightness or channel value (0-1)
    @param dotSize Maximum dot diameter
    @param invert True for grayscale (dark = big), False for color
    @return Dot radius -/
def dotRadius (value dotSize : Float) (invert : Bool) : Float :=
  let normalized := if invert then 1.0 - value else value
  (normalized * dotSize) / 2.0

/-- Calculate brightness from RGB.

    @param r Red (0-1)
    @param g Green (0-1)
    @param b Blue (0-1)
    @return Brightness (0-1) -/
def brightness (r g b : Float) : Float :=
  (r + g + b) / 3.0

/-- Calculate grayscale dot radius from RGB.

    @param r Red (0-1)
    @param g Green (0-1)
    @param b Blue (0-1)
    @param dotSize Maximum dot diameter
    @return Dot radius (inverse brightness) -/
def grayscaleDotRadius (r g b dotSize : Float) : Float :=
  let b := brightness r g b
  dotRadius b dotSize true

--------------------------------------------------------------------------------
-- CMYK Angle Offsets
--------------------------------------------------------------------------------

/-- Standard CMYK screen angles to minimize moiré.

    Traditional print angles:
    - Cyan: 15°
    - Magenta: 75°
    - Yellow: 0°
    - Black: 45°

    @param channel Which CMYK channel (0=C, 1=M, 2=Y, 3=K)
    @return Angle in degrees -/
def cmykAngle (channel : Nat) : Float :=
  match channel with
  | 0 => 15.0   -- Cyan
  | 1 => 75.0   -- Magenta
  | 2 => 0.0    -- Yellow
  | 3 => 45.0   -- Black
  | _ => 0.0

/-- Convert angle from degrees to radians.

    @param degrees Angle in degrees
    @return Angle in radians -/
def degreesToRadians (degrees : Float) : Float :=
  degrees * Float.pi / 180.0

/-- Calculate dot center offset for CMYK channel.

    Each channel is slightly offset to create traditional rosette pattern.

    @param channel Channel index (0=C, 1=M, 2=Y, 3=K)
    @param dotSize Dot spacing
    @return (dx, dy) offset -/
def cmykDotOffset (channel : Nat) (dotSize : Float) : Float × Float :=
  let angle := degreesToRadians (cmykAngle channel)
  let offset := dotSize * 0.1
  (Float.cos angle * offset, Float.sin angle * offset)

--------------------------------------------------------------------------------
-- Pattern Rotation
--------------------------------------------------------------------------------

/-- Rotate a point around the image center.

    Used to apply overall pattern rotation angle.

    @param x Point X
    @param y Point Y
    @param centerX Center X
    @param centerY Center Y
    @param angle Rotation angle in radians
    @return (rotatedX, rotatedY) -/
def rotatePoint (x y centerX centerY angle : Float) : Float × Float :=
  let dx := x - centerX
  let dy := y - centerY
  let cosA := Float.cos angle
  let sinA := Float.sin angle
  ( cosA * dx - sinA * dy + centerX
  , sinA * dx + cosA * dy + centerY )

end Lattice.Services.Stylize.Halftone
