-- | Lattice.Services.Export.CameraExport.Matrix - Camera matrix computations
-- |
-- | Computes view matrices, projection matrices, and world-to-camera transforms
-- | for various camera export formats.
-- |
-- | Source: ui/src/services/export/cameraExportFormats.ts

module Lattice.Services.Export.CameraExport.Matrix
  ( -- * Matrix Computation
    computeViewMatrix
  , computeProjectionMatrix
  , computeW2CMatrix
  , computeW2CMatrixFlat
    -- * Utilities
  , focalLengthToFOV
  , degreesToRadians
  ) where

import Prelude
import Data.Number (cos, sin, tan, pi, atan, isFinite)
import Data.Maybe (Maybe(..))

import Lattice.Services.Export.CameraExport.Types (InterpolatedCamera, Vec3)

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

-- | Default film size (36mm full frame)
defaultFilmSize :: Number
defaultFilmSize = 36.0

-- | Default near clip plane
defaultNearClip :: Number
defaultNearClip = 0.1

-- | Default far clip plane
defaultFarClip :: Number
defaultFarClip = 1000.0

-- ────────────────────────────────────────────────────────────────────────────
-- Matrix Types
-- ────────────────────────────────────────────────────────────────────────────

-- | 4x4 matrix as nested arrays
type Matrix4x4 = Array (Array Number)

-- | 3x4 matrix as nested arrays
type Matrix3x4 = Array (Array Number)

-- ────────────────────────────────────────────────────────────────────────────
-- Conversion Utilities
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert degrees to radians
degreesToRadians :: Number -> Number
degreesToRadians deg = deg * pi / 180.0

-- | Convert focal length to field of view (radians)
focalLengthToFOV :: Number -> Number -> Number
focalLengthToFOV focalLength filmSize =
  let
    -- Guard against invalid focal length
    validFocal = if focalLength > 0.0 then focalLength else 50.0
    validFilm = if filmSize > 0.0 then filmSize else defaultFilmSize
  in
    2.0 * atan (validFilm / (2.0 * validFocal))

-- ────────────────────────────────────────────────────────────────────────────
-- View Matrix
-- ────────────────────────────────────────────────────────────────────────────

-- | Compute 4x4 view matrix from camera state
-- |
-- | The view matrix transforms world coordinates to camera coordinates.
-- | Uses Y * X * Z rotation order.
computeViewMatrix :: InterpolatedCamera -> Matrix4x4
computeViewMatrix cam =
  let
    { position, rotation } = cam

    -- Guard against NaN/Infinity - use 0 as fallback
    rotX = guardFinite rotation.x
    rotY = guardFinite rotation.y
    rotZ = guardFinite rotation.z
    posX = guardFinite position.x
    posY = guardFinite position.y
    posZ = guardFinite position.z

    -- Convert degrees to radians
    rx = degreesToRadians rotX
    ry = degreesToRadians rotY
    rz = degreesToRadians rotZ

    -- Rotation components
    cosX = cos rx
    sinX = sin rx
    cosY = cos ry
    sinY = sin ry
    cosZ = cos rz
    sinZ = sin rz

    -- Combined rotation (Y * X * Z order)
    r00 = cosY * cosZ + sinY * sinX * sinZ
    r01 = -cosY * sinZ + sinY * sinX * cosZ
    r02 = sinY * cosX

    r10 = cosX * sinZ
    r11 = cosX * cosZ
    r12 = -sinX

    r20 = -sinY * cosZ + cosY * sinX * sinZ
    r21 = sinY * sinZ + cosY * sinX * cosZ
    r22 = cosY * cosX

    -- View matrix = inverse of camera transform
    -- For orthonormal rotation, inverse is transpose
    -- Translation is -R^T * position
    tx = -(r00 * posX + r10 * posY + r20 * posZ)
    ty = -(r01 * posX + r11 * posY + r21 * posZ)
    tz = -(r02 * posX + r12 * posY + r22 * posZ)
  in
    [ [r00, r01, r02, tx]
    , [r10, r11, r12, ty]
    , [r20, r21, r22, tz]
    , [0.0, 0.0, 0.0, 1.0]
    ]

-- ────────────────────────────────────────────────────────────────────────────
-- Projection Matrix
-- ────────────────────────────────────────────────────────────────────────────

-- | Compute projection matrix
-- |
-- | Creates a perspective projection matrix from camera properties.
computeProjectionMatrix
  :: InterpolatedCamera
  -> Number  -- ^ Aspect ratio (width / height)
  -> Number  -- ^ Near clip plane
  -> Number  -- ^ Far clip plane
  -> Matrix4x4
computeProjectionMatrix cam aspectRatio nearClip farClip =
  let
    -- Validate inputs
    validAspect = if aspectRatio > 0.0 then aspectRatio else 1.0
    validNear = if nearClip > 0.0 then nearClip else defaultNearClip
    validFar = if farClip > validNear then farClip else defaultFarClip
    validFocal = if cam.focalLength > 0.0 then cam.focalLength else 50.0

    -- Compute FOV from focal length
    fovRad = focalLengthToFOV validFocal defaultFilmSize
    tanHalfFov = tan (fovRad / 2.0)

    -- Handle edge case where tanHalfFov is very small
    f = if tanHalfFov > 0.001 then 1.0 / tanHalfFov else 1000.0
    nf = 1.0 / (validNear - validFar)
  in
    [ [f / validAspect, 0.0, 0.0, 0.0]
    , [0.0, f, 0.0, 0.0]
    , [0.0, 0.0, (validFar + validNear) * nf, 2.0 * validFar * validNear * nf]
    , [0.0, 0.0, -1.0, 0.0]
    ]

-- ────────────────────────────────────────────────────────────────────────────
-- World-to-Camera Matrix
-- ────────────────────────────────────────────────────────────────────────────

-- | Compute 3x4 world-to-camera (w2c) matrix
-- |
-- | The w2c matrix transforms world coordinates to camera coordinates.
-- | It's the inverse of the camera-to-world (c2w) matrix.
computeW2CMatrix :: InterpolatedCamera -> Matrix3x4
computeW2CMatrix cam =
  let
    { position, rotation } = cam

    -- Guard against NaN/Infinity
    rotX = guardFinite rotation.x
    rotY = guardFinite rotation.y
    rotZ = guardFinite rotation.z
    posX = guardFinite position.x
    posY = guardFinite position.y
    posZ = guardFinite position.z

    -- Convert degrees to radians
    rx = degreesToRadians rotX
    ry = degreesToRadians rotY
    rz = degreesToRadians rotZ

    -- Rotation components
    cosX = cos rx
    sinX = sin rx
    cosY = cos ry
    sinY = sin ry
    cosZ = cos rz
    sinZ = sin rz

    -- Combined rotation (Y * X * Z order) - this gives R for c2w
    r00 = cosY * cosZ + sinY * sinX * sinZ
    r01 = -cosY * sinZ + sinY * sinX * cosZ
    r02 = sinY * cosX

    r10 = cosX * sinZ
    r11 = cosX * cosZ
    r12 = -sinX

    r20 = -sinY * cosZ + cosY * sinX * sinZ
    r21 = sinY * sinZ + cosY * sinX * cosZ
    r22 = cosY * cosX

    -- For w2c, rotation is transposed (R^T)
    w2c_r00 = r00
    w2c_r01 = r10
    w2c_r02 = r20
    w2c_r10 = r01
    w2c_r11 = r11
    w2c_r12 = r21
    w2c_r20 = r02
    w2c_r21 = r12
    w2c_r22 = r22

    -- w2c translation = -R^T * t
    tx = -(w2c_r00 * posX + w2c_r01 * posY + w2c_r02 * posZ)
    ty = -(w2c_r10 * posX + w2c_r11 * posY + w2c_r12 * posZ)
    tz = -(w2c_r20 * posX + w2c_r21 * posY + w2c_r22 * posZ)
  in
    [ [w2c_r00, w2c_r01, w2c_r02, tx]
    , [w2c_r10, w2c_r11, w2c_r12, ty]
    , [w2c_r20, w2c_r21, w2c_r22, tz]
    ]

-- | Compute w2c matrix as flat array (12 elements, row-major)
-- |
-- | Format: [r00, r01, r02, tx, r10, r11, r12, ty, r20, r21, r22, tz]
computeW2CMatrixFlat :: InterpolatedCamera -> Array Number
computeW2CMatrixFlat cam =
  let
    w2c = computeW2CMatrix cam
  in
    flattenMatrix3x4 w2c

-- | Flatten 3x4 matrix to array (row-major)
flattenMatrix3x4 :: Matrix3x4 -> Array Number
flattenMatrix3x4 m = case m of
  [row0, row1, row2] ->
    row0 <> row1 <> row2
  _ ->
    -- Fallback: identity-like flat array
    [1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0]

-- ────────────────────────────────────────────────────────────────────────────
-- Utilities
-- ────────────────────────────────────────────────────────────────────────────

-- | Guard against NaN/Infinity - return 0 if not finite
guardFinite :: Number -> Number
guardFinite n = if isFinite n then n else 0.0
