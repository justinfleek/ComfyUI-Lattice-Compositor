/-
  Lattice.Services.Depth.DepthFill - Depth Buffer Filling

  Pure functions for filling depth buffers from different sources:
  - Depthflow layer depth map sampling
  - Particle circular splat rendering
  - Uniform depth fill for solid layers
  - Z-buffer depth testing

  Source: ui/src/services/export/depthRenderer.ts (lines 336-511)
-/

namespace Lattice.Services.Depth.DepthFill

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Screen bounds for depth fill operations. -/
structure FillBounds where
  x : Float
  y : Float
  width : Float
  height : Float
  deriving Repr

/-- Particle data for depth rendering. -/
structure ParticleData where
  x : Float
  y : Float
  z : Float
  size : Float
  deriving Repr

/-- Camera data for depth calculations. -/
structure CameraData where
  positionZ : Float
  deriving Repr

/-- Depth buffer state (dimensions and reference to buffer). -/
structure DepthBufferInfo where
  width : Nat
  height : Nat
  nearClip : Float
  farClip : Float
  deriving Repr

--------------------------------------------------------------------------------
-- Depth Sampling
--------------------------------------------------------------------------------

/-- Calculate sample coordinates from depth map.
    Maps screen position to depth map position. -/
def calculateSampleCoords (x y boundsWidth boundsHeight : Float)
                          (depthWidth depthHeight : Nat) : Nat × Nat :=
  let sampleX := ((x / boundsWidth) * depthWidth.toFloat).toUInt32.toNat
  let sampleY := ((y / boundsHeight) * depthHeight.toFloat).toUInt32.toNat
  (sampleX, sampleY)

/-- Convert sample coordinates to linear index. -/
def sampleToIndex (sampleX sampleY depthWidth : Nat) : Nat :=
  sampleY * depthWidth + sampleX

/-- Normalize Uint8 depth value to [0, 1]. -/
def normalizeUint8Depth (value : UInt8) : Float :=
  value.toFloat / 255.0

/-- Convert normalized depth to world units.
    worldDepth = nearClip + normalized * (farClip - nearClip) -/
def normalizedToWorldDepth (normalized nearClip farClip : Float) : Float :=
  nearClip + normalized * (farClip - nearClip)

/-- Screen bounds check for depth fill. -/
def isInScreenBounds (screenX screenY : Int) (screenWidth screenHeight : Nat) : Bool :=
  screenX >= 0 && screenX < screenWidth.toInt &&
  screenY >= 0 && screenY < screenHeight.toInt

/-- Calculate buffer index from screen coordinates. -/
def screenToBufferIndex (screenX screenY screenWidth : Nat) : Nat :=
  screenY * screenWidth + screenX

--------------------------------------------------------------------------------
-- Depthflow Sampling Logic
--------------------------------------------------------------------------------

/-- Parameters for depthflow sampling. -/
structure DepthflowParams where
  bounds : FillBounds
  depthWidth : Nat
  depthHeight : Nat
  nearClip : Float
  farClip : Float
  deriving Repr

/-- Calculate depthflow sample position for a screen pixel. -/
def depthflowSamplePosition (localX localY : Float) (params : DepthflowParams)
    : Nat × Nat :=
  calculateSampleCoords localX localY
                        params.bounds.width params.bounds.height
                        params.depthWidth params.depthHeight

/-- Calculate screen position from local bounds position. -/
def boundsToScreen (boundsX boundsY localX localY : Float) : Int × Int :=
  ((boundsX + localX).toUInt32.toInt, (boundsY + localY).toUInt32.toInt)

/-- Determine if depth should be written (z-buffer test).
    Closer depth wins (smaller value). -/
def shouldWriteDepth (newDepth existingDepth : Float) : Bool :=
  newDepth < existingDepth

--------------------------------------------------------------------------------
-- Particle Depth Logic
--------------------------------------------------------------------------------

/-- Calculate particle depth relative to camera. -/
def particleRelativeDepth (particleZ cameraZ : Float) : Float :=
  Float.abs (particleZ - cameraZ)

/-- Clamp depth to clip range. -/
def clampDepthToClipRange (depth nearClip farClip : Float) : Float :=
  Float.max nearClip (Float.min farClip depth)

/-- Calculate particle radius in pixels. -/
def particleRadius (size : Float) : Nat :=
  Nat.max 1 (size / 2.0).toUInt32.toNat

/-- Check if point is inside circular splat. -/
def isInsideCircle (dx dy radius : Int) : Bool :=
  dx * dx + dy * dy <= radius * radius

/-- Generate splat pixel offsets for a given radius.
    Returns array of (dx, dy) pairs inside the circle. -/
def generateSplatOffsets (radius : Nat) : Array (Int × Int) :=
  let r := radius.toInt
  let mut offsets : Array (Int × Int) := #[]
  for dy in [-r:r+1] do
    for dx in [-r:r+1] do
      if isInsideCircle dx dy r then
        offsets := offsets.push (dx, dy)
  offsets

/-- Validate particle has finite coordinates. -/
def isValidParticle (p : ParticleData) : Bool :=
  p.x.isFinite && p.y.isFinite && p.z.isFinite

/-- Calculate particle screen position (integer). -/
def particleScreenPosition (p : ParticleData) : Int × Int :=
  (p.x.toUInt32.toInt, p.y.toUInt32.toInt)

--------------------------------------------------------------------------------
-- Uniform Depth Fill Logic
--------------------------------------------------------------------------------

/-- Calculate fill region from bounds.
    Returns (startX, startY, endX, endY). -/
def calculateFillRegion (bounds : FillBounds) (screenWidth screenHeight : Nat)
    : Nat × Nat × Nat × Nat :=
  let startX := bounds.x.toUInt32.toNat
  let startY := bounds.y.toUInt32.toNat
  let endX := Nat.min screenWidth ((bounds.x + bounds.width).ceil.toUInt32.toNat)
  let endY := Nat.min screenHeight ((bounds.y + bounds.height).ceil.toUInt32.toNat)
  (startX, startY, endX, endY)

/-- Check if layer is opaque enough for depth write.
    Uses threshold of 0.5 for depth buffer. -/
def isOpaqueEnoughForDepth (opacity : Float) : Bool :=
  opacity > 0.5

/-- Generate pixel coordinates for uniform fill region.
    Returns array of (x, y) pairs. -/
def generateFillPixels (startX startY endX endY : Nat) : Array (Nat × Nat) :=
  let mut pixels : Array (Nat × Nat) := #[]
  for y in [startY:endY] do
    for x in [startX:endX] do
      pixels := pixels.push (x, y)
  pixels

--------------------------------------------------------------------------------
-- Depth Buffer Operations
--------------------------------------------------------------------------------

/-- Initialize depth buffer value (far clip). -/
def initDepthValue (farClip : Float) : Float :=
  farClip

/-- Calculate min/max depth range from written values. -/
def updateDepthRange (currentMin currentMax writtenDepth : Float) : Float × Float :=
  (Float.min currentMin writtenDepth, Float.max currentMax writtenDepth)

/-- Validate depth range invariant: min <= max. -/
def validateDepthRange (minDepth maxDepth : Float) : Float × Float :=
  if minDepth > maxDepth then (maxDepth, minDepth)
  else (minDepth, maxDepth)

/-- Handle empty scene (no layers updated depth). -/
def handleEmptyScene (minDepth maxDepth farClip : Float) : Float × Float :=
  if !minDepth.isFinite || !maxDepth.isFinite then
    (farClip, farClip)
  else
    validateDepthRange minDepth maxDepth

--------------------------------------------------------------------------------
-- Float32 Precision
--------------------------------------------------------------------------------

/-- Round to Float32 precision for buffer consistency.
    Note: Lean4 Float is already 64-bit, this simulates fround behavior. -/
def toFloat32Precision (value : Float) : Float :=
  -- In a real implementation, this would use Float32 representation
  -- For now, we return the value as-is (Lean4 doesn't have native Float32)
  value

/-- Prepare clip values with Float32 precision. -/
def prepareClipValues (nearClip farClip : Float) : Float × Float :=
  (toFloat32Precision nearClip, toFloat32Precision farClip)

end Lattice.Services.Depth.DepthFill
