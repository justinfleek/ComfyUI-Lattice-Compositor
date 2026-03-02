/-
  Lattice.Services.LayerStyles.BevelLighting - Bevel/Emboss Lighting Math

  Pure mathematical functions for bevel and emboss lighting:
  - Light direction vector from angle and altitude
  - Surface normal from alpha gradients
  - Lambertian diffuse lighting (dot product)

  Source: ui/src/services/effects/layerStyleRenderer.ts (lines 570-696)
-/

namespace Lattice.Services.LayerStyles.BevelLighting

--------------------------------------------------------------------------------
-- Light Direction
--------------------------------------------------------------------------------

/-- Calculate light direction X component.

    Uses Photoshop convention: angle measured from vertical.

    @param angleDeg Light angle in degrees (0° = up, 90° = right)
    @return X component of light direction (normalized) -/
def lightX (angleDeg : Float) : Float :=
  let angleRad := (angleDeg - 90.0) * Float.pi / 180.0
  Float.cos angleRad

/-- Calculate light direction Y component.

    Y is negated for screen coordinates (positive = down).

    @param angleDeg Light angle in degrees
    @return Y component of light direction (normalized) -/
def lightY (angleDeg : Float) : Float :=
  let angleRad := (angleDeg - 90.0) * Float.pi / 180.0
  -(Float.sin angleRad)

/-- Calculate light direction Z component from altitude.

    @param altitudeDeg Altitude angle in degrees (0° = horizontal, 90° = overhead)
    @return Z component of light direction -/
def lightZ (altitudeDeg : Float) : Float :=
  Float.sin (altitudeDeg * Float.pi / 180.0)

/-- Calculate full light direction vector.

    @param angleDeg Angle in degrees
    @param altitudeDeg Altitude in degrees
    @return (lightX, lightY, lightZ) unit vector -/
def lightDirection (angleDeg altitudeDeg : Float) : Float × Float × Float :=
  (lightX angleDeg, lightY angleDeg, lightZ altitudeDeg)

--------------------------------------------------------------------------------
-- Surface Normal from Gradients
--------------------------------------------------------------------------------

/-- Calculate alpha gradient in X direction.

    Uses central difference: (right - left) / 2.

    @param leftAlpha Alpha at (x-1, y), normalized to [0, 1]
    @param rightAlpha Alpha at (x+1, y), normalized to [0, 1]
    @return X gradient -/
def gradientX (leftAlpha rightAlpha : Float) : Float :=
  rightAlpha - leftAlpha

/-- Calculate alpha gradient in Y direction.

    Uses central difference: (bottom - top) / 2.

    @param topAlpha Alpha at (x, y-1), normalized to [0, 1]
    @param bottomAlpha Alpha at (x, y+1), normalized to [0, 1]
    @return Y gradient -/
def gradientY (topAlpha bottomAlpha : Float) : Float :=
  bottomAlpha - topAlpha

/-- Calculate surface normal X component from gradient.

    @param gradX X gradient from alpha
    @param size Bevel size (controls steepness)
    @param depth Depth factor (0-1)
    @return Normal X component (unnormalized) -/
def normalX (gradX size depth : Float) : Float :=
  -gradX * size * depth

/-- Calculate surface normal Y component from gradient.

    @param gradY Y gradient from alpha
    @param size Bevel size (controls steepness)
    @param depth Depth factor (0-1)
    @return Normal Y component (unnormalized) -/
def normalY (gradY size depth : Float) : Float :=
  -gradY * size * depth

/-- Calculate surface normal Z component.

    Always 1.0 (pointing toward viewer).

    @return Normal Z component -/
def normalZ : Float := 1.0

/-- Calculate normalized surface normal length.

    @param nx Normal X
    @param ny Normal Y
    @param nz Normal Z
    @return Length of normal vector -/
def normalLength (nx ny nz : Float) : Float :=
  Float.sqrt (nx * nx + ny * ny + nz * nz)

--------------------------------------------------------------------------------
-- Lighting Calculation
--------------------------------------------------------------------------------

/-- Calculate dot product for Lambertian lighting.

    @param nx Normal X (unnormalized)
    @param ny Normal Y (unnormalized)
    @param nz Normal Z (unnormalized)
    @param lx Light X
    @param ly Light Y
    @param lz Light Z
    @return Dot product (negative = shadow, positive = highlight) -/
def lightingDot (nx ny nz lx ly lz : Float) : Float :=
  let len := normalLength nx ny nz
  if len < 0.0001 then 0.0
  else
    (nx / len) * lx + (ny / len) * ly + (nz / len) * lz

/-- Calculate highlight intensity from dot product.

    @param dot Lighting dot product
    @param opacity Highlight opacity (0-1)
    @param pixelAlpha Original pixel alpha (0-1)
    @return Highlight intensity for alpha channel (0-255) -/
def highlightIntensity (dot opacity pixelAlpha : Float) : Float :=
  if dot > 0.0 then
    Float.min 255.0 (dot * opacity * pixelAlpha * 255.0)
  else
    0.0

/-- Calculate shadow intensity from dot product.

    @param dot Lighting dot product
    @param opacity Shadow opacity (0-1)
    @param pixelAlpha Original pixel alpha (0-1)
    @return Shadow intensity for alpha channel (0-255) -/
def shadowIntensity (dot opacity pixelAlpha : Float) : Float :=
  if dot < 0.0 then
    Float.min 255.0 ((-dot) * opacity * pixelAlpha * 255.0)
  else
    0.0

--------------------------------------------------------------------------------
-- Full Bevel Calculation
--------------------------------------------------------------------------------

/-- Calculate bevel lighting for a single pixel.

    @param leftAlpha Alpha at (x-1, y) normalized
    @param rightAlpha Alpha at (x+1, y) normalized
    @param topAlpha Alpha at (x, y-1) normalized
    @param bottomAlpha Alpha at (x, y+1) normalized
    @param pixelAlpha Alpha at (x, y) normalized
    @param size Bevel size
    @param depth Bevel depth (0-1)
    @param angleDeg Light angle
    @param altitudeDeg Light altitude
    @return (highlightAmount, shadowAmount) in [0, 1] -/
def bevelLighting (leftAlpha rightAlpha topAlpha bottomAlpha pixelAlpha : Float)
    (size depth angleDeg altitudeDeg : Float) : Float × Float :=
  -- Calculate gradients
  let gradX := gradientX leftAlpha rightAlpha
  let gradY := gradientY topAlpha bottomAlpha

  -- Calculate normal
  let nx := normalX gradX size depth
  let ny := normalY gradY size depth
  let nz := normalZ

  -- Calculate light direction
  let (lx, ly, lz) := lightDirection angleDeg altitudeDeg

  -- Calculate lighting
  let dot := lightingDot nx ny nz lx ly lz

  -- Separate into highlight and shadow
  if dot > 0.0 then
    (dot * pixelAlpha, 0.0)   -- Highlight
  else
    (0.0, (-dot) * pixelAlpha)  -- Shadow

end Lattice.Services.LayerStyles.BevelLighting
