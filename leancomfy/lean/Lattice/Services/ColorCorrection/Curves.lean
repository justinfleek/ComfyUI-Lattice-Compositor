/-
  Lattice.Services.ColorCorrection.Curves - Curve Interpolation Functions

  Pure mathematical functions for curve-based color adjustment:
  - Cubic Bezier evaluation
  - Catmull-Rom tangent calculation
  - S-curve generation
  - Lift curve generation

  All functions are total (no partial def) and deterministic.

  Source: ui/src/services/effects/colorRenderer.ts (lines 468-705)
-/

namespace Lattice.Services.ColorCorrection.Curves

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- A point on a curve -/
structure CurvePoint where
  x : Float  -- Input value (0-255)
  y : Float  -- Output value (0-255)
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Cubic Bezier
--------------------------------------------------------------------------------

/-- Evaluate a cubic Bezier curve at parameter t.

    Formula: B(t) = (1-t)³P₀ + 3(1-t)²tP₁ + 3(1-t)t²P₂ + t³P₃

    @param p0 Start point value
    @param p1 First control point value
    @param p2 Second control point value
    @param p3 End point value
    @param t Parameter (0-1)
    @return Interpolated value -/
def cubicBezier (p0 p1 p2 p3 t : Float) : Float :=
  let t2 := t * t
  let t3 := t2 * t
  let mt := 1.0 - t
  let mt2 := mt * mt
  let mt3 := mt2 * mt
  mt3 * p0 + 3.0 * mt2 * t * p1 + 3.0 * mt * t2 * p2 + t3 * p3

--------------------------------------------------------------------------------
-- Catmull-Rom Tangent
--------------------------------------------------------------------------------

/-- Calculate Catmull-Rom tangent for a curve segment.

    For a point P₁ between P₀ and P₂, the tangent is:
    tangent = (P₂.y - P₀.y) / (P₂.x - P₀.x) * (P₂.x - P₁.x)

    This creates smooth curves that pass through control points.

    @param prevY Y value of previous point (or current if first)
    @param prevX X value of previous point
    @param nextY Y value of next point (or current if last)
    @param nextX X value of next point
    @param segmentWidth Width of current segment (next.x - current.x)
    @return Tangent scaled to segment width -/
def catmullRomTangent (prevY prevX nextY nextX segmentWidth : Float) : Float :=
  let dx := nextX - prevX
  if dx < 0.0001 then 0.0
  else ((nextY - prevY) / dx) * segmentWidth

--------------------------------------------------------------------------------
-- Curve Interpolation
--------------------------------------------------------------------------------

/-- Linear interpolation parameter for a value in a segment.

    @param value Input value
    @param segmentStart Start of segment
    @param segmentEnd End of segment
    @return Parameter t in 0-1 (clamped) -/
def segmentParameter (value segmentStart segmentEnd : Float) : Float :=
  let range := segmentEnd - segmentStart
  if range < 0.0001 then 0.0
  else
    let t := (value - segmentStart) / range
    Float.max 0.0 (Float.min 1.0 t)

/-- Evaluate a curve at a given input value using cubic interpolation.

    Uses Catmull-Rom tangents for smooth interpolation between points.

    @param points Sorted curve points (by x value)
    @param pointCount Number of points
    @param segmentIndex Index of segment containing the value
    @param inputValue The input value (0-255)
    @param getPointX Function to get x value at index
    @param getPointY Function to get y value at index
    @return Output value (0-255, clamped) -/
def evaluateCurveSegment
    (p0x p0y p1x p1y : Float)
    (hasPrev : Bool) (prevX prevY : Float)
    (hasNext : Bool) (nextX nextY : Float)
    (t : Float) : Float :=
  -- Calculate tangents using Catmull-Rom
  let tangent0 := if hasPrev
                  then catmullRomTangent prevY prevX p1y p1x (p1x - p0x)
                  else 0.0
  let tangent1 := if hasNext
                  then catmullRomTangent p0y p0x nextY nextX (p1x - p0x)
                  else 0.0

  -- Control points for cubic Bezier
  let cp1y := p0y + tangent0 / 3.0
  let cp2y := p1y - tangent1 / 3.0

  -- Evaluate cubic Bezier
  let result := cubicBezier p0y cp1y cp2y p1y t

  -- Clamp to valid range
  Float.max 0.0 (Float.min 255.0 result)

--------------------------------------------------------------------------------
-- Preset Curve Generators
--------------------------------------------------------------------------------

/-- Create an S-curve for contrast adjustment.

    S-curves darken shadows and brighten highlights, increasing contrast.

    @param amount Curve intensity (0-1, where 0.5 is moderate)
    @return Array of 5 curve points forming an S-curve -/
def createSCurve (amount : Float) : Array CurvePoint :=
  let midPoint : Float := 128.0
  let adjustment := amount * 50.0

  #[ { x := 0.0,   y := 0.0 }
   , { x := 64.0,  y := Float.max 0.0 (64.0 - adjustment) }
   , { x := midPoint, y := midPoint }
   , { x := 192.0, y := Float.min 255.0 (192.0 + adjustment) }
   , { x := 255.0, y := 255.0 }
   ]

/-- Create a lift curve for shadow/highlight adjustment.

    Lift curves raise the black point and/or lower the white point.

    @param shadowLift Amount to lift shadows (0-128)
    @param highlightLift Amount to lift highlights (negative = lower, -127 to 0)
    @return Array of 3 curve points -/
def createLiftCurve (shadowLift highlightLift : Float) : Array CurvePoint :=
  #[ { x := 0.0,   y := Float.max 0.0 (Float.min 128.0 shadowLift) }
   , { x := 128.0, y := 128.0 }
   , { x := 255.0, y := Float.max 128.0 (Float.min 255.0 (255.0 + highlightLift)) }
   ]

--------------------------------------------------------------------------------
-- LUT Building Helpers
--------------------------------------------------------------------------------

/-- Build identity curve (input = output).

    @return Array of 2 points representing identity -/
def identityCurve : Array CurvePoint :=
  #[ { x := 0.0, y := 0.0 }
   , { x := 255.0, y := 255.0 }
   ]

/-- Clamp a float to valid 8-bit range and round.

    @param value Input value
    @return Clamped and rounded value (0-255) -/
def clampToUint8 (value : Float) : Float :=
  Float.round (Float.max 0.0 (Float.min 255.0 value))

end Lattice.Services.ColorCorrection.Curves
