/-
  Lattice.Services.CoordinateConversion - Coordinate conversion math

  Functions for converting between coordinate spaces and calculating
  orientations. Pure math without side effects.

  Source: ui/src/services/expressions/coordinateConversion.ts
-/

namespace Lattice.Services.CoordinateConversion

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

/-- Pi constant -/
def pi : Float := 3.14159265358979323846

/-- Convert degrees to radians -/
def degToRad (deg : Float) : Float :=
  deg * pi / 180.0

/-- Convert radians to degrees -/
def radToDeg (rad : Float) : Float :=
  rad * 180.0 / pi

--------------------------------------------------------------------------------
-- 3D Point Type
--------------------------------------------------------------------------------

/-- 3D point -/
structure Point3D where
  x : Float
  y : Float
  z : Float
  deriving Repr, Inhabited

/-- Create Point3D with default z=0 -/
def Point3D.fromXY (x y : Float) : Point3D :=
  ⟨x, y, 0⟩

--------------------------------------------------------------------------------
-- Rotation Result
--------------------------------------------------------------------------------

/-- Euler rotation angles in degrees -/
structure EulerRotation where
  pitch : Float  -- X rotation
  yaw : Float    -- Y rotation
  roll : Float   -- Z rotation
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- lookAt - Calculate rotation to face a target
--------------------------------------------------------------------------------

/-- Calculate rotation to face from one point to another.
    Returns rotation angles [pitch, yaw, roll] in degrees.
    Uses Y-up, Z-forward convention. -/
def lookAt (from_ to : Point3D) : EulerRotation :=
  let dx := to.x - from_.x
  let dy := to.y - from_.y
  let dz := to.z - from_.z

  -- Calculate yaw (Y rotation) from XZ plane
  let yaw := radToDeg (Float.atan2 dx dz)

  -- Calculate pitch (X rotation) from horizontal distance
  let dist := Float.sqrt (dx * dx + dz * dz)
  let pitch := radToDeg (-(Float.atan2 dy dist))

  -- No roll calculation (stays at 0)
  ⟨pitch, yaw, 0⟩

/-- Calculate rotation from velocity/tangent vector -/
def orientToTangent (tangent : Point3D) : EulerRotation :=
  let dx := if tangent.x.isFinite then tangent.x else 0
  let dy := if tangent.y.isFinite then tangent.y else 0
  let dz := if tangent.z.isFinite then tangent.z else 1  -- Default forward

  let yaw := radToDeg (Float.atan2 dx dz)
  let dist := Float.sqrt (dx * dx + dz * dz)
  let pitch := radToDeg (-(Float.atan2 dy dist))

  ⟨pitch, yaw, 0⟩

--------------------------------------------------------------------------------
-- Layer Transform
--------------------------------------------------------------------------------

/-- Layer transform properties -/
structure LayerTransform where
  position : Point3D
  scale : Point3D     -- As percentages (100 = 1.0)
  rotation : Point3D  -- Euler angles in degrees
  anchor : Point3D
  deriving Repr

/-- Default transform (identity) -/
def LayerTransform.identity : LayerTransform :=
  { position := ⟨0, 0, 0⟩
  , scale := ⟨100, 100, 100⟩
  , rotation := ⟨0, 0, 0⟩
  , anchor := ⟨0, 0, 0⟩ }

--------------------------------------------------------------------------------
-- Coordinate Conversion (Single Layer, No Parent)
--------------------------------------------------------------------------------

/-- Apply rotation around Z axis -/
def rotateZ (x y z : Float) (angle : Float) : Point3D :=
  let rad := degToRad angle
  let cosA := Float.cos rad
  let sinA := Float.sin rad
  ⟨x * cosA - y * sinA, x * sinA + y * cosA, z⟩

/-- Apply rotation around Y axis -/
def rotateY (p : Point3D) (angle : Float) : Point3D :=
  let rad := degToRad angle
  let cosA := Float.cos rad
  let sinA := Float.sin rad
  ⟨p.x * cosA + p.z * sinA, p.y, -p.x * sinA + p.z * cosA⟩

/-- Apply rotation around X axis -/
def rotateX (p : Point3D) (angle : Float) : Point3D :=
  let rad := degToRad angle
  let cosA := Float.cos rad
  let sinA := Float.sin rad
  ⟨p.x, p.y * cosA - p.z * sinA, p.y * sinA + p.z * cosA⟩

/-- Convert point from layer space to composition space (single layer).
    Applies: anchor offset → scale → rotation (ZYX order) → position -/
def toCompSingle (point : Point3D) (transform : LayerTransform) : Point3D :=
  -- Apply anchor offset
  let x := point.x - transform.anchor.x
  let y := point.y - transform.anchor.y
  let z := point.z - transform.anchor.z

  -- Apply scale (percentage to multiplier)
  let x := x * transform.scale.x / 100
  let y := y * transform.scale.y / 100
  let z := z * transform.scale.z / 100

  -- Apply rotation (Z, then Y, then X - matching AE order)
  let rotated := rotateZ x y z transform.rotation.z
  let rotated := rotateY rotated transform.rotation.y
  let rotated := rotateX rotated transform.rotation.x

  -- Apply position offset
  ⟨rotated.x + transform.position.x,
   rotated.y + transform.position.y,
   rotated.z + transform.position.z⟩

/-- Safe divide with fallback -/
def safeDivide (num denom fallback : Float) : Float :=
  if denom == 0 || !denom.isFinite then fallback
  else
    let result := num / denom
    if result.isFinite then result else fallback

/-- Convert point from composition space to layer space (single layer).
    Applies: position → inverse rotation (XYZ order) → inverse scale → anchor -/
def fromCompSingle (point : Point3D) (transform : LayerTransform) : Point3D :=
  -- Subtract position
  let x := point.x - transform.position.x
  let y := point.y - transform.position.y
  let z := point.z - transform.position.z

  -- Inverse rotation (X, then Y, then Z - reverse order, negative angles)
  let rotated := rotateX ⟨x, y, z⟩ (-transform.rotation.x)
  let rotated := rotateY rotated (-transform.rotation.y)
  let rotated := rotateZ rotated.x rotated.y rotated.z (-transform.rotation.z)

  -- Inverse scale (divide, with safety)
  let sx := transform.scale.x / 100
  let sy := transform.scale.y / 100
  let sz := transform.scale.z / 100
  let x := safeDivide rotated.x sx rotated.x  -- If scale=0, preserve coordinate
  let y := safeDivide rotated.y sy rotated.y
  let z := safeDivide rotated.z sz rotated.z

  -- Add anchor
  ⟨x + transform.anchor.x,
   y + transform.anchor.y,
   z + transform.anchor.z⟩

--------------------------------------------------------------------------------
-- Coordinate Conversion with Parent Chain
--------------------------------------------------------------------------------

/-- Maximum parent depth to prevent infinite loops -/
def maxParentDepth : Nat := 50

/-- Convert to composition space with parent chain -/
def toComp (point : Point3D) (transforms : List LayerTransform) : Point3D :=
  let rec go (p : Point3D) (ts : List LayerTransform) (depth : Nat) : Point3D :=
    match ts, depth with
    | [], _ => p
    | _, 0 => p  -- Max depth reached
    | t :: rest, n + 1 =>
      let transformed := toCompSingle p t
      go transformed rest n
  go point transforms maxParentDepth

/-- Convert from composition space with parent chain -/
def fromComp (point : Point3D) (transforms : List LayerTransform) : Point3D :=
  let rec go (p : Point3D) (ts : List LayerTransform) (depth : Nat) : Point3D :=
    match ts, depth with
    | [], _ => p
    | _, 0 => p  -- Max depth reached
    | t :: rest, n + 1 =>
      -- First recurse to parent, then apply this transform's inverse
      let parentTransformed := go p rest n
      fromCompSingle parentTransformed t
  go point transforms.reverse maxParentDepth

--------------------------------------------------------------------------------
-- Aliases for 3D Context
--------------------------------------------------------------------------------

/-- Convert to world space (alias for toComp) -/
def toWorld (point : Point3D) (transforms : List LayerTransform) : Point3D :=
  toComp point transforms

/-- Convert from world space (alias for fromComp) -/
def fromWorld (point : Point3D) (transforms : List LayerTransform) : Point3D :=
  fromComp point transforms

end Lattice.Services.CoordinateConversion
