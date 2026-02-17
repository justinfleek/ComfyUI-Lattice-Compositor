/-
  Lattice.Services.Distort.Warp - Warp Distortion Mathematics

  Pure mathematical functions for warp distortions:
  - Arc warp (bend along parabola)
  - Bulge warp (inflate/deflate)
  - Wave warp (sinusoidal displacement)
  - Fisheye warp (barrel/pincushion)
  - Twist warp (rotational distortion)

  Source: ui/src/services/effects/distortRenderer.ts (lines 273-407)
-/

namespace Lattice.Services.Distort.Warp

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Warp style type -/
inductive WarpStyle
  | arc       -- Bend along parabolic curve
  | bulge     -- Inflate/deflate from center
  | wave      -- Sinusoidal displacement
  | fisheye   -- Barrel/pincushion distortion
  | twist     -- Rotational swirl
deriving Repr, BEq, Inhabited

/-- Warp result: displaced source coordinates -/
structure WarpResult where
  srcX : Float
  srcY : Float
deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Coordinate Normalization
--------------------------------------------------------------------------------

/-- Normalize pixel coordinate to -1 to 1 range.

    @param coord Pixel coordinate (x or y)
    @param center Center coordinate (width/2 or height/2)
    @return Normalized coordinate in [-1, 1] -/
def normalizeCoord (coord center : Float) : Float :=
  if center < 0.0001 then 0.0
  else (coord - center) / center

--------------------------------------------------------------------------------
-- Arc Warp
--------------------------------------------------------------------------------

/-- Calculate arc warp displacement.

    Arc warp bends the image along a parabolic curve.
    Displacement is proportional to ny² (stronger at top/bottom).

    @param x Pixel X
    @param nx Normalized X (-1 to 1)
    @param ny Normalized Y (-1 to 1)
    @param centerX Image center X
    @param bend Bend amount (-1 to 1, from -100 to 100 percent)
    @return Displaced X coordinate -/
def arcWarpX (x nx ny centerX bend : Float) : Float :=
  let arcBend := bend * ny * ny
  x + arcBend * centerX * nx

--------------------------------------------------------------------------------
-- Bulge Warp
--------------------------------------------------------------------------------

/-- Calculate bulge warp displacement.

    Bulge warp inflates or deflates the image from center.
    Inside unit circle, pixels are scaled toward/away from center.

    @param x Pixel X
    @param y Pixel Y
    @param centerX Center X
    @param centerY Center Y
    @param r Distance from center (normalized)
    @param bend Bend amount (-1 to 1)
    @return (srcX, srcY) displaced coordinates -/
def bulgeWarp (x y centerX centerY r bend : Float) : WarpResult :=
  if r >= 1.0 then
    { srcX := x, srcY := y }
  else
    let factor := 1.0 + bend * (1.0 - r * r)
    -- Avoid division by zero
    let safeFactor := if Float.abs factor < 0.0001 then 0.0001 else factor
    { srcX := centerX + (x - centerX) / safeFactor
    , srcY := centerY + (y - centerY) / safeFactor }

--------------------------------------------------------------------------------
-- Wave Warp
--------------------------------------------------------------------------------

/-- Calculate wave warp displacement.

    Wave warp applies sinusoidal displacement in both directions.

    @param x Pixel X
    @param y Pixel Y
    @param nx Normalized X
    @param ny Normalized Y
    @param width Image width
    @param height Image height
    @param bend Wave amplitude (-1 to 1)
    @return (srcX, srcY) displaced coordinates -/
def waveWarp (x y nx ny width height bend : Float) : WarpResult :=
  let waveAmplitude := bend * 0.1  -- 10% of dimension at full bend
  { srcX := x + Float.sin (ny * Float.pi * 2.0) * waveAmplitude * width
  , srcY := y + Float.sin (nx * Float.pi * 2.0) * waveAmplitude * height }

--------------------------------------------------------------------------------
-- Fisheye Warp
--------------------------------------------------------------------------------

/-- Calculate fisheye warp displacement.

    Fisheye applies barrel (bend > 0) or pincushion (bend < 0) distortion.
    Uses polar coordinates with power function on radius.

    @param x Pixel X
    @param y Pixel Y
    @param nx Normalized X
    @param ny Normalized Y
    @param centerX Center X
    @param centerY Center Y
    @param r Distance from center (normalized)
    @param bend Bend amount (-1 to 1)
    @return (srcX, srcY) displaced coordinates -/
def fisheyeWarp (x y nx ny centerX centerY r bend : Float) : WarpResult :=
  if r <= 0.0 || r >= 1.0 then
    { srcX := x, srcY := y }
  else
    let theta := Float.atan2 ny nx
    -- Power distortion: r^(1 + bend)
    let newR := Float.pow r (1.0 + bend)
    { srcX := centerX + newR * Float.cos theta * centerX
    , srcY := centerY + newR * Float.sin theta * centerY }

--------------------------------------------------------------------------------
-- Twist Warp
--------------------------------------------------------------------------------

/-- Calculate twist warp displacement.

    Twist warp rotates pixels around center, with rotation angle
    decreasing with distance (stronger twist at center).

    @param x Pixel X
    @param y Pixel Y
    @param nx Normalized X
    @param ny Normalized Y
    @param centerX Center X
    @param centerY Center Y
    @param r Distance from center (normalized)
    @param bend Twist amount (-1 to 1, maps to rotation in radians)
    @return (srcX, srcY) displaced coordinates -/
def twistWarp (x y nx ny centerX centerY r bend : Float) : WarpResult :=
  let angle := bend * Float.pi * (1.0 - r)
  let cosA := Float.cos angle
  let sinA := Float.sin angle
  { srcX := centerX + (nx * cosA - ny * sinA) * centerX
  , srcY := centerY + (nx * sinA + ny * cosA) * centerY }

--------------------------------------------------------------------------------
-- Combined Warp
--------------------------------------------------------------------------------

/-- Apply warp distortion based on style.

    @param style Warp style
    @param x Pixel X
    @param y Pixel Y
    @param width Image width
    @param height Image height
    @param bend Bend amount (-1 to 1)
    @return (srcX, srcY) displaced coordinates -/
def applyWarp (style : WarpStyle) (x y width height bend : Float) : WarpResult :=
  let centerX := width / 2.0
  let centerY := height / 2.0
  let nx := normalizeCoord x centerX
  let ny := normalizeCoord y centerY
  let r := Float.sqrt (nx * nx + ny * ny)

  match style with
  | WarpStyle.arc =>
    { srcX := arcWarpX x nx ny centerX bend, srcY := y }
  | WarpStyle.bulge =>
    bulgeWarp x y centerX centerY r bend
  | WarpStyle.wave =>
    waveWarp x y nx ny width height bend
  | WarpStyle.fisheye =>
    fisheyeWarp x y nx ny centerX centerY r bend
  | WarpStyle.twist =>
    twistWarp x y nx ny centerX centerY r bend

--------------------------------------------------------------------------------
-- Horizontal/Vertical Distortion
--------------------------------------------------------------------------------

/-- Apply additional horizontal and vertical distortion.

    @param srcX Current source X
    @param srcY Current source Y
    @param nx Normalized X
    @param ny Normalized Y
    @param centerX Center X
    @param centerY Center Y
    @param hDistort Horizontal distortion (-1 to 1)
    @param vDistort Vertical distortion (-1 to 1)
    @return (srcX, srcY) with additional distortion -/
def applyHVDistortion (srcX srcY nx ny centerX centerY hDistort vDistort : Float) : WarpResult :=
  { srcX := srcX + hDistort * centerX * (1.0 - ny * ny)
  , srcY := srcY + vDistort * centerY * (1.0 - nx * nx) }

end Lattice.Services.Distort.Warp
