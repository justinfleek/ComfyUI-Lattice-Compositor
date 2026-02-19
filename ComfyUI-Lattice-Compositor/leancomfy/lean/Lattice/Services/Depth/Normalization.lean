/-
  Lattice.Services.Depth.Normalization - Depth Value Normalization

  Pure mathematical functions for depth map processing:
  - Depth normalization to [0, 1] range
  - Bit depth conversion (8-bit, 16-bit, 32-bit)
  - Depth inversion (near/far swap)

  Source: ui/src/services/export/depthRenderer.ts (lines 600-676)
-/

namespace Lattice.Services.Depth.Normalization

--------------------------------------------------------------------------------
-- Depth Range Normalization
--------------------------------------------------------------------------------

/-- Calculate safe depth range, avoiding division by zero.
    Returns 1.0 if minDepth == maxDepth. -/
def safeDepthRange (minDepth maxDepth : Float) : Float :=
  let range := maxDepth - minDepth
  if range <= 0.0 then 1.0 else range

/-- Normalize depth value to [0, 1] range.
    0 = minDepth, 1 = maxDepth -/
def normalizeDepth (depth minDepth maxDepth : Float) : Float :=
  let range := safeDepthRange minDepth maxDepth
  (depth - minDepth) / range

/-- Clamp normalized value to [0, 1]. -/
def clampNormalized (value : Float) : Float :=
  if value < 0.0 then 0.0
  else if value > 1.0 then 1.0
  else value

/-- Invert depth: converts near=low/far=high to near=high/far=low.
    Used for AI depth models that expect near=bright, far=dark. -/
def invertDepth (normalized : Float) : Float :=
  1.0 - clampNormalized normalized

--------------------------------------------------------------------------------
-- Bit Depth Conversion
--------------------------------------------------------------------------------

/-- Convert normalized [0, 1] to 8-bit [0, 255]. -/
def toUint8 (normalized : Float) : Nat :=
  let clamped := clampNormalized normalized
  (clamped * 255.0).toUInt32.toNat

/-- Convert normalized [0, 1] to 16-bit [0, 65535]. -/
def toUint16 (normalized : Float) : Nat :=
  let clamped := clampNormalized normalized
  (clamped * 65535.0).toUInt32.toNat

/-- Convert 8-bit [0, 255] to normalized [0, 1]. -/
def fromUint8 (value : Nat) : Float :=
  value.toFloat / 255.0

/-- Convert 16-bit [0, 65535] to normalized [0, 1]. -/
def fromUint16 (value : Nat) : Float :=
  value.toFloat / 65535.0

--------------------------------------------------------------------------------
-- Metric Depth Conversion
--------------------------------------------------------------------------------

/-- Convert normalized depth to world units.
    worldDepth = nearClip + normalized * (farClip - nearClip) -/
def toWorldDepth (normalized nearClip farClip : Float) : Float :=
  nearClip + clampNormalized normalized * (farClip - nearClip)

/-- Convert world depth to normalized [0, 1].
    Inverse of toWorldDepth. -/
def fromWorldDepth (worldDepth nearClip farClip : Float) : Float :=
  if farClip <= nearClip then 0.0
  else clampNormalized ((worldDepth - nearClip) / (farClip - nearClip))

/-- Scale normalized depth by far clip (for non-normalized formats). -/
def scaleByFarClip (normalized farClip : Float) : Float :=
  clampNormalized normalized * farClip

--------------------------------------------------------------------------------
-- Complete Depth Conversion Pipeline
--------------------------------------------------------------------------------

/-- Full depth conversion: world → normalized → inverted (optional) → quantized.
    This matches the convertDepthToFormat pipeline. -/
def convertDepth (depth minDepth maxDepth : Float)
                 (invert : Bool) (bitDepth : Nat) : Nat :=
  let normalized := normalizeDepth depth minDepth maxDepth
  let clamped := clampNormalized normalized
  let inverted := if invert then invertDepth clamped else clamped
  match bitDepth with
  | 8 => toUint8 inverted
  | 16 => toUint16 inverted
  | _ => toUint16 inverted  -- Default to 16-bit

/-- Depth comparison for z-buffer: returns true if newDepth is closer (smaller). -/
def isCloser (newDepth currentDepth : Float) : Bool :=
  newDepth < currentDepth

/-- Depth buffer update: return closer depth. -/
def depthBufferUpdate (newDepth currentDepth : Float) : Float :=
  if isCloser newDepth currentDepth then newDepth else currentDepth

end Lattice.Services.Depth.Normalization
