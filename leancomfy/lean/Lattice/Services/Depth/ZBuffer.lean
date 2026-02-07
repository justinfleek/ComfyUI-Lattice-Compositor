/-
  Lattice.Services.Depth.ZBuffer - Z-Buffer Operations

  Pure mathematical functions for depth buffer operations:
  - Z-buffer initialization
  - Depth testing (closer wins)
  - Layer depth sorting
  - Screen bounds calculation
  - Uniform depth fill
  - Circular splat rendering

  Source: ui/src/services/export/depthRenderer.ts (lines 45-511)
-/

namespace Lattice.Services.Depth.ZBuffer

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Screen bounds rectangle. -/
structure ScreenBounds where
  x : Float
  y : Float
  width : Float
  height : Float
  deriving Repr

/-- Camera position in 3D. -/
structure CameraPosition where
  x : Float
  y : Float
  z : Float
  deriving Repr

/-- Layer transform data. -/
structure LayerTransform where
  positionX : Float
  positionY : Float
  positionZ : Float
  scaleX : Float
  scaleY : Float
  anchorX : Float
  anchorY : Float
  deriving Repr

/-- Depth render result. -/
structure DepthResult where
  minDepth : Float
  maxDepth : Float
  deriving Repr

--------------------------------------------------------------------------------
-- Z-Buffer Initialization
--------------------------------------------------------------------------------

/-- Initial depth value (far clip). -/
def initDepth (farClip : Float) : Float := farClip

/-- Initial min/max for tracking (opposite extremes). -/
def initialMinMax : Float × Float := (Float.inf, -Float.inf)

--------------------------------------------------------------------------------
-- Depth Testing
--------------------------------------------------------------------------------

/-- Test if new depth is closer (smaller) than current. -/
def isCloser (newDepth currentDepth : Float) : Bool :=
  newDepth < currentDepth

/-- Update depth buffer value: keep closer depth. -/
def updateDepth (newDepth currentDepth : Float) : Float :=
  if isCloser newDepth currentDepth then newDepth else currentDepth

/-- Update min/max tracking. -/
def updateMinMax (depth : Float) (minD maxD : Float) : Float × Float :=
  (Float.min minD depth, Float.max maxD depth)

--------------------------------------------------------------------------------
-- Layer Depth Calculation
--------------------------------------------------------------------------------

/-- Calculate relative depth from camera.
    relativeDepth = |layerZ - cameraZ| -/
def relativeDepth (layerZ cameraZ : Float) : Float :=
  Float.abs (layerZ - cameraZ)

/-- Clamp depth to clip range [nearClip, farClip]. -/
def clampToClipRange (depth nearClip farClip : Float) : Float :=
  Float.max nearClip (Float.min farClip depth)

/-- Full depth calculation: layer Z → clamped relative depth. -/
def calculateLayerDepth (layerZ cameraZ nearClip farClip : Float) : Float :=
  let relative := relativeDepth layerZ cameraZ
  clampToClipRange relative nearClip farClip

--------------------------------------------------------------------------------
-- Screen Bounds Calculation
--------------------------------------------------------------------------------

/-- Calculate final layer dimensions with scale. -/
def scaledDimensions (layerWidth layerHeight scaleX scaleY : Float) : Float × Float :=
  (layerWidth * scaleX, layerHeight * scaleY)

/-- Convert compositor coords (origin = center) to screen coords (origin = top-left). -/
def toScreenCoords (posX posY : Float)
                   (finalWidth finalHeight : Float)
                   (anchorX anchorY : Float)
                   (screenWidth screenHeight : Float) : Float × Float :=
  let screenX := posX - finalWidth * anchorX + screenWidth / 2.0
  let screenY := posY - finalHeight * anchorY + screenHeight / 2.0
  (screenX, screenY)

/-- Clip bounds to screen. -/
def clipToScreen (screenX screenY finalWidth finalHeight : Float)
                 (screenWidth screenHeight : Float) : Option ScreenBounds :=
  let clippedX := Float.max 0.0 (Float.min screenWidth screenX)
  let clippedY := Float.max 0.0 (Float.min screenHeight screenY)
  let clippedWidth := Float.max 0.0
    (Float.min (screenWidth - clippedX) (finalWidth - (clippedX - screenX)))
  let clippedHeight := Float.max 0.0
    (Float.min (screenHeight - clippedY) (finalHeight - (clippedY - screenY)))
  if clippedWidth <= 0.0 || clippedHeight <= 0.0 then none
  else some { x := clippedX, y := clippedY, width := clippedWidth, height := clippedHeight }

/-- Full screen bounds calculation. -/
def calculateScreenBounds (transform : LayerTransform)
                          (layerWidth layerHeight : Float)
                          (screenWidth screenHeight : Float) : Option ScreenBounds :=
  let (finalWidth, finalHeight) := scaledDimensions layerWidth layerHeight transform.scaleX transform.scaleY
  let (screenX, screenY) := toScreenCoords transform.positionX transform.positionY
                                           finalWidth finalHeight
                                           transform.anchorX transform.anchorY
                                           screenWidth screenHeight
  clipToScreen screenX screenY finalWidth finalHeight screenWidth screenHeight

--------------------------------------------------------------------------------
-- Pixel Index Calculation
--------------------------------------------------------------------------------

/-- Calculate linear pixel index from 2D coordinates. -/
def pixelIndex (x y width : Nat) : Nat := y * width + x

/-- Check if coordinates are within bounds. -/
def inBounds (x y width height : Nat) : Bool :=
  x < width && y < height

/-- Calculate bounds for rectangular fill. -/
def fillBounds (bounds : ScreenBounds) (screenWidth screenHeight : Nat) :
               Nat × Nat × Nat × Nat :=
  let startX := bounds.x.toUInt32.toNat
  let startY := bounds.y.toUInt32.toNat
  let endX := Nat.min screenWidth ((bounds.x + bounds.width).ceil.toUInt32.toNat)
  let endY := Nat.min screenHeight ((bounds.y + bounds.height).ceil.toUInt32.toNat)
  (startX, startY, endX, endY)

--------------------------------------------------------------------------------
-- Circular Splat (for Particles)
--------------------------------------------------------------------------------

/-- Check if point is within circular radius (for particle splats). -/
def inCircle (dx dy radius : Int) : Bool :=
  dx * dx + dy * dy <= radius * radius

/-- Calculate particle splat radius from size. -/
def splatRadius (particleSize : Float) : Nat :=
  let half := particleSize / 2.0
  if half < 1.0 then 1 else half.toUInt32.toNat

--------------------------------------------------------------------------------
-- Depth Map Sampling
--------------------------------------------------------------------------------

/-- Sample depth from depth map at UV coordinates.
    Maps bounds-relative position to depth map coordinates. -/
def sampleDepthCoords (localX localY : Float)
                      (boundsWidth boundsHeight : Float)
                      (depthWidth depthHeight : Nat) : Nat × Nat :=
  let sampleX := ((localX / boundsWidth) * depthWidth.toFloat).toUInt32.toNat
  let sampleY := ((localY / boundsHeight) * depthHeight.toFloat).toUInt32.toNat
  (Nat.min sampleX (depthWidth - 1), Nat.min sampleY (depthHeight - 1))

/-- Convert uint8 depth to normalized [0, 1]. -/
def uint8ToNormalized (value : Nat) : Float := value.toFloat / 255.0

/-- Convert normalized depth to world units. -/
def normalizedToWorld (normalized nearClip farClip : Float) : Float :=
  nearClip + normalized * (farClip - nearClip)

--------------------------------------------------------------------------------
-- Result Validation
--------------------------------------------------------------------------------

/-- Validate and normalize min/max depth result.
    Handles empty scenes and ensures minDepth <= maxDepth. -/
def validateDepthResult (minD maxD farClip : Float) : DepthResult :=
  -- Handle uninitialized (empty scene)
  let (min', max') :=
    if !minD.isFinite || !maxD.isFinite then (farClip, farClip)
    else (minD, maxD)
  -- Ensure invariant: minDepth <= maxDepth
  if min' > max' then { minDepth := max', maxDepth := min' }
  else { minDepth := min', maxDepth := max' }

end Lattice.Services.Depth.ZBuffer
