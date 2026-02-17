/-
  Lattice.Services.LayerStyles.AngleOffset - Angle to Offset Conversion

  Pure mathematical functions for layer style positioning:
  - Angle to X/Y offset (for shadows, bevels)
  - Photoshop-style angle convention (0° = right, 90° = up)

  Source: ui/src/services/effects/layerStyleRenderer.ts (lines 119-129)
-/

namespace Lattice.Services.LayerStyles.AngleOffset

--------------------------------------------------------------------------------
-- Angle Conventions
--------------------------------------------------------------------------------

/-- Convert degrees to radians.

    @param degrees Angle in degrees
    @return Angle in radians -/
def degreesToRadians (degrees : Float) : Float :=
  degrees * Float.pi / 180.0

/-- Photoshop angle offset: 0° = right, 90° = up (counter-clockwise).

    The Photoshop convention uses 0° = right (east), with angles
    increasing counter-clockwise. We subtract 90° to align
    with the standard mathematical convention where 0° = right.

    @param angleDeg Angle in degrees (Photoshop convention)
    @return Adjusted angle in radians -/
def photoshopAngleToRad (angleDeg : Float) : Float :=
  degreesToRadians (angleDeg - 90.0)

--------------------------------------------------------------------------------
-- Offset Calculation
--------------------------------------------------------------------------------

/-- Calculate X offset from angle and distance.

    Uses Photoshop convention: 0° = right, 90° = up.

    @param angleDeg Angle in degrees
    @param distance Distance in pixels
    @return X offset (positive = right) -/
def offsetX (angleDeg distance : Float) : Float :=
  let angleRad := photoshopAngleToRad angleDeg
  Float.cos angleRad * distance

/-- Calculate Y offset from angle and distance.

    Uses Photoshop convention: 0° = right, 90° = up.
    Y is negated because screen Y increases downward.

    @param angleDeg Angle in degrees
    @param distance Distance in pixels
    @return Y offset (positive = down in screen coordinates) -/
def offsetY (angleDeg distance : Float) : Float :=
  let angleRad := photoshopAngleToRad angleDeg
  -(Float.sin angleRad * distance)

/-- Calculate both X and Y offsets from angle and distance.

    @param angleDeg Angle in degrees (Photoshop convention)
    @param distance Distance in pixels
    @return (offsetX, offsetY) tuple -/
def angleToOffset (angleDeg distance : Float) : Float × Float :=
  (offsetX angleDeg distance, offsetY angleDeg distance)

--------------------------------------------------------------------------------
-- Inverse Operations
--------------------------------------------------------------------------------

/-- Calculate angle from X/Y offsets.

    @param x X offset
    @param y Y offset (screen coordinates, positive = down)
    @return Angle in degrees (Photoshop convention) -/
def offsetToAngle (x y : Float) : Float :=
  let angleRad := Float.atan2 (-y) x
  let angleDeg := angleRad * 180.0 / Float.pi
  angleDeg + 90.0

/-- Calculate distance from X/Y offsets.

    @param x X offset
    @param y Y offset
    @return Distance in pixels -/
def offsetToDistance (x y : Float) : Float :=
  Float.sqrt (x * x + y * y)

--------------------------------------------------------------------------------
-- Global Light
--------------------------------------------------------------------------------

/-- Apply global light angle if enabled.

    @param localAngle Local angle setting
    @param globalAngle Global light angle
    @param useGlobal Whether to use global light
    @return Resolved angle in degrees -/
def resolveAngle (localAngle globalAngle : Float) (useGlobal : Bool) : Float :=
  if useGlobal then globalAngle else localAngle

end Lattice.Services.LayerStyles.AngleOffset
