/-
  Lattice.Services.Stylize.EdgeDetection - Edge Detection Mathematics

  Pure mathematical functions for edge detection:
  - Sobel operator kernels
  - Gradient magnitude calculation
  - Emboss direction vectors

  Source: ui/src/services/effects/stylizeRenderer.ts (lines 1065-1210)
-/

namespace Lattice.Services.Stylize.EdgeDetection

--------------------------------------------------------------------------------
-- Sobel Kernels
--------------------------------------------------------------------------------

/-- Sobel X kernel for horizontal gradient detection.

    3x3 convolution kernel:
    [-1  0  1]
    [-2  0  2]
    [-1  0  1]

    @param kx Kernel X offset (-1, 0, or 1)
    @param ky Kernel Y offset (-1, 0, or 1)
    @return Kernel weight -/
def sobelX (kx ky : Int) : Int :=
  let col := kx + 1  -- 0, 1, 2
  let row := ky + 1  -- 0, 1, 2
  -- Row 0: -1, 0, 1
  -- Row 1: -2, 0, 2
  -- Row 2: -1, 0, 1
  match row with
  | 0 => if col = 0 then -1 else if col = 1 then 0 else 1
  | 1 => if col = 0 then -2 else if col = 1 then 0 else 2
  | 2 => if col = 0 then -1 else if col = 1 then 0 else 1
  | _ => 0

/-- Sobel Y kernel for vertical gradient detection.

    3x3 convolution kernel:
    [-1 -2 -1]
    [ 0  0  0]
    [ 1  2  1]

    @param kx Kernel X offset (-1, 0, or 1)
    @param ky Kernel Y offset (-1, 0, or 1)
    @return Kernel weight -/
def sobelY (kx ky : Int) : Int :=
  let col := kx + 1  -- 0, 1, 2
  let row := ky + 1  -- 0, 1, 2
  -- Row 0: -1, -2, -1
  -- Row 1:  0,  0,  0
  -- Row 2:  1,  2,  1
  match row with
  | 0 => if col = 0 then -1 else if col = 1 then -2 else -1
  | 1 => 0
  | 2 => if col = 0 then 1 else if col = 1 then 2 else 1
  | _ => 0

/-- Get both Sobel kernel values at a position.

    @param kx Kernel X offset (-1, 0, or 1)
    @param ky Kernel Y offset (-1, 0, or 1)
    @return (sobelX, sobelY) weights -/
def sobelWeights (kx ky : Int) : Int × Int :=
  (sobelX kx ky, sobelY kx ky)

--------------------------------------------------------------------------------
-- Gradient Calculation
--------------------------------------------------------------------------------

/-- Calculate gradient magnitude from X and Y components.

    magnitude = sqrt(gx² + gy²)

    @param gx X gradient component
    @param gy Y gradient component
    @return Gradient magnitude -/
def gradientMagnitude (gx gy : Float) : Float :=
  Float.sqrt (gx * gx + gy * gy)

/-- Calculate gradient direction in radians.

    @param gx X gradient component
    @param gy Y gradient component
    @return Angle in radians [-π, π] -/
def gradientDirection (gx gy : Float) : Float :=
  Float.atan2 gy gx

/-- Apply inversion to edge magnitude.

    Inverted edges show bright on dark instead of dark on bright.

    @param magnitude Edge magnitude
    @param invert Whether to invert
    @return Adjusted magnitude -/
def applyInversion (magnitude : Float) (invert : Bool) : Float :=
  if invert then 255.0 - magnitude else magnitude

/-- Blend edge magnitude with original pixel value.

    @param edgeMag Edge magnitude (0-255)
    @param original Original pixel value (0-255)
    @param blend Blend factor (0 = all edge, 1 = all original)
    @return Blended value -/
def blendWithOriginal (edgeMag original blend : Float) : Float :=
  let result := edgeMag * (1.0 - blend) + original * blend
  Float.min 255.0 result

--------------------------------------------------------------------------------
-- Emboss
--------------------------------------------------------------------------------

/-- Calculate emboss sample offset from light direction.

    @param directionDeg Light direction in degrees
    @param height Emboss depth
    @return (dx, dy) sample offset -/
def embossOffset (directionDeg height : Float) : Int × Int :=
  let direction := directionDeg * Float.pi / 180.0
  let dx := Float.round (Float.cos direction * height)
  let dy := Float.round (Float.sin direction * height)
  (Float.toUInt64 dx |>.toNat |> Int.ofNat, Float.toUInt64 dy |>.toNat |> Int.ofNat)

/-- Calculate emboss value from sample difference.

    Emboss creates relief effect by comparing offset pixels.
    Result is centered at 128 (gray).

    @param sample1 First sample value
    @param sample2 Second sample value (opposite offset)
    @param factor Intensity factor (amount / 100)
    @return Embossed value centered at 128 -/
def embossValue (sample1 sample2 factor : Float) : Float :=
  let diff := (sample1 - sample2) * factor
  Float.max 0.0 (Float.min 255.0 (128.0 + diff))

--------------------------------------------------------------------------------
-- Kernel Index Helpers
--------------------------------------------------------------------------------

/-- Convert kernel offset (-1, 0, 1) to flat index (0-8).

    Layout: 0 1 2
            3 4 5
            6 7 8

    @param kx X offset (-1, 0, 1)
    @param ky Y offset (-1, 0, 1)
    @return Flat index (0-8) -/
def kernelIndex (kx ky : Int) : Nat :=
  let row := (ky + 1).toNat
  let col := (kx + 1).toNat
  row * 3 + col

end Lattice.Services.Stylize.EdgeDetection
