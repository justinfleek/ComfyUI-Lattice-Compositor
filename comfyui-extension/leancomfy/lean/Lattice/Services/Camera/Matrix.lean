/-
  Lattice.Services.Camera.Matrix - Camera Matrix Computations

  Pure functions for camera matrix calculations:
  - View matrix (camera transform inverse)
  - Projection matrix (perspective)
  - World-to-camera (w2c) matrix
  - Rotation matrix composition

  Source: ui/src/services/export/cameraExportFormats.ts (lines 167-286, 782-861)
-/

namespace Lattice.Services.Camera.Matrix

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- 3D vector. -/
structure Vec3 where
  x : Float
  y : Float
  z : Float
  deriving Repr

/-- 4x4 matrix stored as array of rows. -/
abbrev Mat4 := Array (Array Float)

/-- 3x4 matrix for w2c transforms. -/
abbrev Mat3x4 := Array (Array Float)

/-- Interpolated camera state (from Interpolation module). -/
structure InterpolatedCamera where
  position : Vec3
  rotation : Vec3
  focalLength : Float
  zoom : Float
  focusDistance : Float
  deriving Repr

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

/-- Default near clip plane. -/
def defaultNearClip : Float := 0.1

/-- Default far clip plane. -/
def defaultFarClip : Float := 1000.0

/-- Default film size (36mm full frame). -/
def defaultFilmSize : Float := 36.0

/-- Standard focal length (50mm). -/
def standardFocalLength : Float := 50.0

/-- Pi constant. -/
def pi : Float := 3.14159265358979323846

--------------------------------------------------------------------------------
-- Angle Conversion
--------------------------------------------------------------------------------

/-- Convert degrees to radians. -/
def degreesToRadians (degrees : Float) : Float :=
  degrees * pi / 180.0

/-- Convert radians to degrees. -/
def radiansToDegrees (radians : Float) : Float :=
  radians * 180.0 / pi

--------------------------------------------------------------------------------
-- Focal Length to FOV
--------------------------------------------------------------------------------

/-- Convert focal length (mm) to field of view (radians).
    FOV = 2 * atan(filmSize / (2 * focalLength)) -/
def focalLengthToFOV (focalLength filmSize : Float) : Float :=
  let safeFocal := if focalLength > 0.0 then focalLength else standardFocalLength
  2.0 * Float.atan (filmSize / (2.0 * safeFocal))

/-- Convert field of view (radians) to focal length (mm). -/
def fovToFocalLength (fovRadians filmSize : Float) : Float :=
  filmSize / (2.0 * Float.tan (fovRadians / 2.0))

--------------------------------------------------------------------------------
-- Trigonometric Helpers
--------------------------------------------------------------------------------

/-- Compute sin and cos of angle in radians. -/
def sinCos (radians : Float) : Float × Float :=
  (Float.sin radians, Float.cos radians)

--------------------------------------------------------------------------------
-- View Matrix Computation
--------------------------------------------------------------------------------

/-- Compute 4x4 view matrix from camera state.
    View matrix = inverse of camera transform.
    For orthonormal rotation, inverse is transpose.
    Translation is -R^T * position. -/
def computeViewMatrix (cam : InterpolatedCamera) : Mat4 :=
  -- Guard against invalid values, use 0 as fallback
  let rotX := if cam.rotation.x.isFinite then cam.rotation.x else 0.0
  let rotY := if cam.rotation.y.isFinite then cam.rotation.y else 0.0
  let rotZ := if cam.rotation.z.isFinite then cam.rotation.z else 0.0
  let posX := if cam.position.x.isFinite then cam.position.x else 0.0
  let posY := if cam.position.y.isFinite then cam.position.y else 0.0
  let posZ := if cam.position.z.isFinite then cam.position.z else 0.0

  -- Convert degrees to radians
  let rx := degreesToRadians rotX
  let ry := degreesToRadians rotY
  let rz := degreesToRadians rotZ

  -- Trigonometric values
  let (sinX, cosX) := sinCos rx
  let (sinY, cosY) := sinCos ry
  let (sinZ, cosZ) := sinCos rz

  -- Combined rotation (Y * X * Z order)
  let r00 := cosY * cosZ + sinY * sinX * sinZ
  let r01 := -cosY * sinZ + sinY * sinX * cosZ
  let r02 := sinY * cosX

  let r10 := cosX * sinZ
  let r11 := cosX * cosZ
  let r12 := -sinX

  let r20 := -sinY * cosZ + cosY * sinX * sinZ
  let r21 := sinY * sinZ + cosY * sinX * cosZ
  let r22 := cosY * cosX

  -- Translation = -R^T * position
  let tx := -(r00 * posX + r10 * posY + r20 * posZ)
  let ty := -(r01 * posX + r11 * posY + r21 * posZ)
  let tz := -(r02 * posX + r12 * posY + r22 * posZ)

  #[
    #[r00, r01, r02, tx],
    #[r10, r11, r12, ty],
    #[r20, r21, r22, tz],
    #[0.0, 0.0, 0.0, 1.0]
  ]

--------------------------------------------------------------------------------
-- Projection Matrix Computation
--------------------------------------------------------------------------------

/-- Compute perspective projection matrix.
    Uses vertical FOV derived from focal length. -/
def computeProjectionMatrix (cam : InterpolatedCamera)
                            (aspectRatio nearClip farClip : Float) : Mat4 :=
  -- Validate inputs
  let validAspect := if aspectRatio > 0.0 && aspectRatio.isFinite then aspectRatio else 1.0
  let validNear := if nearClip > 0.0 && nearClip.isFinite then nearClip else defaultNearClip
  let validFar := if farClip > validNear && farClip.isFinite then farClip else defaultFarClip
  let validFocal := if cam.focalLength > 0.0 && cam.focalLength.isFinite
                    then cam.focalLength else standardFocalLength

  -- Calculate FOV from focal length (36mm film)
  let fovRad := focalLengthToFOV validFocal defaultFilmSize
  let tanHalfFov := Float.tan (fovRad / 2.0)

  -- Handle edge case where tan could be very small
  let f := if tanHalfFov > 0.001 then 1.0 / tanHalfFov else 1000.0
  let nf := 1.0 / (validNear - validFar)

  #[
    #[f / validAspect, 0.0, 0.0, 0.0],
    #[0.0, f, 0.0, 0.0],
    #[0.0, 0.0, (validFar + validNear) * nf, 2.0 * validFar * validNear * nf],
    #[0.0, 0.0, -1.0, 0.0]
  ]

--------------------------------------------------------------------------------
-- World-to-Camera Matrix
--------------------------------------------------------------------------------

/-- Compute 3x4 world-to-camera (w2c) matrix.
    w2c transforms world coordinates to camera coordinates.
    w2c rotation = transpose of c2w rotation.
    w2c translation = -R^T * t -/
def computeW2CMatrix (cam : InterpolatedCamera) : Mat3x4 :=
  -- Guard against invalid values
  let rotX := if cam.rotation.x.isFinite then cam.rotation.x else 0.0
  let rotY := if cam.rotation.y.isFinite then cam.rotation.y else 0.0
  let rotZ := if cam.rotation.z.isFinite then cam.rotation.z else 0.0
  let posX := if cam.position.x.isFinite then cam.position.x else 0.0
  let posY := if cam.position.y.isFinite then cam.position.y else 0.0
  let posZ := if cam.position.z.isFinite then cam.position.z else 0.0

  -- Convert degrees to radians
  let rx := degreesToRadians rotX
  let ry := degreesToRadians rotY
  let rz := degreesToRadians rotZ

  -- Trigonometric values
  let (sinX, cosX) := sinCos rx
  let (sinY, cosY) := sinCos ry
  let (sinZ, cosZ) := sinCos rz

  -- Combined rotation (Y * X * Z order) for c2w
  let r00 := cosY * cosZ + sinY * sinX * sinZ
  let r01 := -cosY * sinZ + sinY * sinX * cosZ
  let r02 := sinY * cosX

  let r10 := cosX * sinZ
  let r11 := cosX * cosZ
  let r12 := -sinX

  let r20 := -sinY * cosZ + cosY * sinX * sinZ
  let r21 := sinY * sinZ + cosY * sinX * cosZ
  let r22 := cosY * cosX

  -- w2c rotation (transpose of c2w rotation)
  let w2c_r00 := r00; let w2c_r01 := r10; let w2c_r02 := r20
  let w2c_r10 := r01; let w2c_r11 := r11; let w2c_r12 := r21
  let w2c_r20 := r02; let w2c_r21 := r12; let w2c_r22 := r22

  -- w2c translation = -R^T * t
  let tx := -(w2c_r00 * posX + w2c_r01 * posY + w2c_r02 * posZ)
  let ty := -(w2c_r10 * posX + w2c_r11 * posY + w2c_r12 * posZ)
  let tz := -(w2c_r20 * posX + w2c_r21 * posY + w2c_r22 * posZ)

  #[
    #[w2c_r00, w2c_r01, w2c_r02, tx],
    #[w2c_r10, w2c_r11, w2c_r12, ty],
    #[w2c_r20, w2c_r21, w2c_r22, tz]
  ]

/-- Flatten 3x4 matrix to 12-element array (row-major). -/
def flattenMat3x4 (m : Mat3x4) : Array Float :=
  #[m[0]![0]!, m[0]![1]!, m[0]![2]!, m[0]![3]!,
    m[1]![0]!, m[1]![1]!, m[1]![2]!, m[1]![3]!,
    m[2]![0]!, m[2]![1]!, m[2]![2]!, m[2]![3]!]

--------------------------------------------------------------------------------
-- Identity Matrix
--------------------------------------------------------------------------------

/-- 4x4 identity matrix. -/
def identityMat4 : Mat4 :=
  #[
    #[1.0, 0.0, 0.0, 0.0],
    #[0.0, 1.0, 0.0, 0.0],
    #[0.0, 0.0, 1.0, 0.0],
    #[0.0, 0.0, 0.0, 1.0]
  ]

end Lattice.Services.Camera.Matrix
