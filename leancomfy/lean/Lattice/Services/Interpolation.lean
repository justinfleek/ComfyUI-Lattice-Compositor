/-
  Lattice.Services.Interpolation - Pure interpolation functions

  Pure math functions for keyframe interpolation.
  Handles bezier curves, linear interpolation, and color blending.

  Source: ui/src/services/interpolation.ts (pure math portions)
-/

namespace Lattice.Services.Interpolation

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- 2D vector -/
structure Vec2 where
  x : Float
  y : Float
  deriving Repr, Inhabited

/-- 3D vector -/
structure Vec3 where
  x : Float
  y : Float
  z : Float
  deriving Repr, Inhabited

/-- RGB color with components 0-255 -/
structure Color where
  r : Float
  g : Float
  b : Float
  a : Float  -- Alpha, 0-255
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Linear Interpolation
--------------------------------------------------------------------------------

/-- Linear interpolation between two numbers -/
def lerp (a b t : Float) : Float :=
  a + (b - a) * t

/-- Safe linear interpolation (handles extreme values) -/
def safeLerp (a b t : Float) : Float :=
  let result := lerp a b t
  if Float.isNaN result || Float.isInf result then
    if t < 0.5 then a else b
  else
    result

/-- Interpolate Vec2 -/
def lerpVec2 (a b : Vec2) (t : Float) : Vec2 :=
  { x := safeLerp a.x b.x t, y := safeLerp a.y b.y t }

/-- Interpolate Vec3 -/
def lerpVec3 (a b : Vec3) (t : Float) : Vec3 :=
  { x := safeLerp a.x b.x t
  , y := safeLerp a.y b.y t
  , z := safeLerp a.z b.z t }

--------------------------------------------------------------------------------
-- Bezier Curve Math
--------------------------------------------------------------------------------

/-- Cubic bezier point calculation
    p0, p1, p2, p3 are control points (p0 and p3 are endpoints) -/
def bezierPoint (t p0 p1 p2 p3 : Float) : Float :=
  let mt := 1.0 - t
  mt * mt * mt * p0 +
  3.0 * mt * mt * t * p1 +
  3.0 * mt * t * t * p2 +
  t * t * t * p3

/-- Cubic bezier derivative -/
def bezierDerivative (t p0 p1 p2 p3 : Float) : Float :=
  let mt := 1.0 - t
  3.0 * mt * mt * (p1 - p0) +
  6.0 * mt * t * (p2 - p1) +
  3.0 * t * t * (p3 - p2)

/-- Find t for given x using Newton-Raphson iteration -/
def solveBezierX (x x1 x2 : Float) (maxIter : Nat := 8) : Float :=
  let epsilon := 1e-6
  let rec go (guessT : Float) (iter : Nat) : Float :=
    match iter with
    | 0 => guessT
    | n + 1 =>
      let currentX := bezierPoint guessT 0.0 x1 x2 1.0
      let error := currentX - x
      if Float.abs error < epsilon then guessT
      else
        let slope := bezierDerivative guessT 0.0 x1 x2 1.0
        if Float.abs slope < epsilon then guessT
        else
          let newT := guessT - error / slope
          let clampedT := Float.max 0.0 (Float.min 1.0 newT)
          go clampedT n
  go x maxIter

/-- Cubic bezier easing
    Given normalized control points (x1,y1) and (x2,y2) in 0-1 space,
    returns the eased value for linear time t -/
def cubicBezierEasing (t x1 y1 x2 y2 : Float) : Float :=
  let solvedT := solveBezierX t x1 x2
  bezierPoint solvedT 0.0 y1 y2 1.0

--------------------------------------------------------------------------------
-- Color Interpolation
--------------------------------------------------------------------------------

/-- Parse hex digit to number (0-15), returns 0 for invalid -/
private def hexDigitToInt (c : Char) : Float :=
  if c >= '0' && c <= '9' then (c.toNat - '0'.toNat).toFloat
  else if c >= 'a' && c <= 'f' then (c.toNat - 'a'.toNat + 10).toFloat
  else if c >= 'A' && c <= 'F' then (c.toNat - 'A'.toNat + 10).toFloat
  else 0.0

/-- Parse two hex chars to byte value -/
private def parseHexByte (h1 h2 : Char) : Float :=
  hexDigitToInt h1 * 16.0 + hexDigitToInt h2

/-- Create color from 6-digit hex string (without #) -/
def colorFromHex6 (s : String) : Color :=
  if s.length < 6 then { r := 0, g := 0, b := 0, a := 255 }
  else
    let chars := s.toList
    match chars with
    | r1 :: r2 :: g1 :: g2 :: b1 :: b2 :: rest =>
      let a := match rest with
        | a1 :: a2 :: _ => parseHexByte a1 a2
        | _ => 255.0
      { r := parseHexByte r1 r2
      , g := parseHexByte g1 g2
      , b := parseHexByte b1 b2
      , a := a }
    | _ => { r := 0, g := 0, b := 0, a := 255 }

/-- Expand 3/4 char hex to 6/8 char -/
def expandShortHex (s : String) : String :=
  let chars := s.toList
  match chars with
  | [r, g, b] => String.mk [r, r, g, g, b, b]
  | [r, g, b, a] => String.mk [r, r, g, g, b, b, a, a]
  | _ => s

/-- Normalize hex color string (remove #, expand short form) -/
def normalizeHex (hex : String) : String :=
  let s := if hex.startsWith "#" then hex.drop 1 else hex
  if s.length == 3 || s.length == 4 then expandShortHex s
  else s

/-- Interpolate between two colors -/
def lerpColor (c1 c2 : Color) (t : Float) : Color :=
  { r := Float.round (safeLerp c1.r c2.r t)
  , g := Float.round (safeLerp c1.g c2.g t)
  , b := Float.round (safeLerp c1.b c2.b t)
  , a := Float.round (safeLerp c1.a c2.a t) }

/-- Convert color to hex string -/
def colorToHex (c : Color) (includeAlpha : Bool := false) : String :=
  let toHex2 (n : Float) : String :=
    let clamped := Float.max 0.0 (Float.min 255.0 n)
    let i := clamped.toUInt8.toNat
    let hi := i / 16
    let lo := i % 16
    let hexDigit (d : Nat) : Char :=
      if d < 10 then Char.ofNat ('0'.toNat + d)
      else Char.ofNat ('a'.toNat + d - 10)
    String.mk [hexDigit hi, hexDigit lo]
  let rgb := "#" ++ toHex2 c.r ++ toHex2 c.g ++ toHex2 c.b
  if includeAlpha then rgb ++ toHex2 c.a else rgb

--------------------------------------------------------------------------------
-- Easing Presets (normalized bezier control points)
--------------------------------------------------------------------------------

/-- Easing preset with normalized 0-1 control points -/
structure EasingPreset where
  outX : Float  -- Out handle X
  outY : Float  -- Out handle Y
  inX : Float   -- In handle X
  inY : Float   -- In handle Y
  deriving Repr, Inhabited

/-- Linear easing -/
def easeLinear : EasingPreset := ⟨0.33, 0.33, 0.33, 0.33⟩

/-- Ease in (slow start) -/
def easeIn : EasingPreset := ⟨0.42, 0.0, 0.33, 0.33⟩

/-- Ease out (slow end) -/
def easeOut : EasingPreset := ⟨0.33, 0.33, 0.58, 1.0⟩

/-- Ease in-out (slow start and end) -/
def easeInOut : EasingPreset := ⟨0.42, 0.0, 0.58, 1.0⟩

/-- Ease out with overshoot -/
def easeOutBack : EasingPreset := ⟨0.33, 0.33, 0.34, 1.56⟩

/-- Apply easing preset to a ratio (0-1) -/
def applyEasingPreset (ratio : Float) (preset : EasingPreset) : Float :=
  let t := Float.max 0.0 (Float.min 1.0 ratio)
  -- Convert preset to bezier control points
  let x1 := preset.outX
  let y1 := preset.outY
  let x2 := 1.0 - preset.inX
  let y2 := 1.0 - preset.inY
  cubicBezierEasing t x1 y1 x2 y2

--------------------------------------------------------------------------------
-- Binary Search for Keyframes
--------------------------------------------------------------------------------

/-- Binary search to find index where arr[i] <= value < arr[i+1]
    Returns index in range [0, length-2] -/
def findKeyframeIndex (frames : Array Float) (frame : Float) : Nat :=
  if frames.size < 2 then 0
  else
    let rec binarySearch (low high : Nat) : Nat :=
      if low > high then Nat.min low (frames.size - 2)
      else
        let mid := (low + high) / 2
        match frames.get? mid, frames.get? (mid + 1) with
        | some midFrame, some nextFrame =>
          if frame >= midFrame && frame <= nextFrame then mid
          else if frame < midFrame then
            if mid == 0 then 0
            else binarySearch low (mid - 1)
          else binarySearch (mid + 1) high
        | _, _ => Nat.min low (frames.size - 2)
    binarySearch 0 (frames.size - 2)

end Lattice.Services.Interpolation
