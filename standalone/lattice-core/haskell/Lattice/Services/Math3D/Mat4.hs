{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Services.Math3D.Mat4
Description : 4x4 Matrix operations
Copyright   : (c) Lattice, 2026
License     : MIT

Pure math functions for 4x4 matrix manipulation.
Column-major order for GPU compatibility.

Source: ui/src/services/math3d.ts
-}

module Lattice.Services.Math3D.Mat4
  ( -- * Types
    Mat4(..)
  , InvertResult(..)
    -- * Constructors
  , identity, zeroMat
    -- * Basic Operations
  , multiply
    -- * Transform Matrices
  , translate, scaleMat, scaleUniform
  , rotateX, rotateY, rotateZ
    -- * Projection Matrices
  , perspective, orthographic
    -- * View Matrix
  , lookAt
    -- * Transform Application
  , transformPoint, transformDirection
    -- * Matrix Operations
  , determinant, invert, transposeMat
    -- * Conversion
  , toArray
  ) where

import GHC.Generics (Generic)
import Lattice.Services.Math3D.Vec3 (Vec3(..))
import qualified Lattice.Services.Math3D.Vec3 as V

-- ────────────────────────────────────────────────────────────────────────────
-- Mat4 Type (Column-Major, GPU-compatible)
-- ────────────────────────────────────────────────────────────────────────────

-- | 4x4 Matrix in column-major order
data Mat4 = Mat4
  { m00 :: Double, m10 :: Double, m20 :: Double, m30 :: Double  -- Column 0
  , m01 :: Double, m11 :: Double, m21 :: Double, m31 :: Double  -- Column 1
  , m02 :: Double, m12 :: Double, m22 :: Double, m32 :: Double  -- Column 2
  , m03 :: Double, m13 :: Double, m23 :: Double, m33 :: Double  -- Column 3
  } deriving stock (Eq, Show, Generic)

-- | Inversion result type
data InvertResult
  = InvertSuccess Mat4
  | SingularMatrix
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Constructors
-- ────────────────────────────────────────────────────────────────────────────

-- | Identity matrix
identity :: Mat4
identity = Mat4
  1 0 0 0
  0 1 0 0
  0 0 1 0
  0 0 0 1

-- | Zero matrix
zeroMat :: Mat4
zeroMat = Mat4
  0 0 0 0
  0 0 0 0
  0 0 0 0
  0 0 0 0

-- ────────────────────────────────────────────────────────────────────────────
-- Basic Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Matrix multiplication
multiply :: Mat4 -> Mat4 -> Mat4
multiply a b = Mat4
  (m00 a*m00 b + m01 a*m10 b + m02 a*m20 b + m03 a*m30 b)
  (m10 a*m00 b + m11 a*m10 b + m12 a*m20 b + m13 a*m30 b)
  (m20 a*m00 b + m21 a*m10 b + m22 a*m20 b + m23 a*m30 b)
  (m30 a*m00 b + m31 a*m10 b + m32 a*m20 b + m33 a*m30 b)

  (m00 a*m01 b + m01 a*m11 b + m02 a*m21 b + m03 a*m31 b)
  (m10 a*m01 b + m11 a*m11 b + m12 a*m21 b + m13 a*m31 b)
  (m20 a*m01 b + m21 a*m11 b + m22 a*m21 b + m23 a*m31 b)
  (m30 a*m01 b + m31 a*m11 b + m32 a*m21 b + m33 a*m31 b)

  (m00 a*m02 b + m01 a*m12 b + m02 a*m22 b + m03 a*m32 b)
  (m10 a*m02 b + m11 a*m12 b + m12 a*m22 b + m13 a*m32 b)
  (m20 a*m02 b + m21 a*m12 b + m22 a*m22 b + m23 a*m32 b)
  (m30 a*m02 b + m31 a*m12 b + m32 a*m22 b + m33 a*m32 b)

  (m00 a*m03 b + m01 a*m13 b + m02 a*m23 b + m03 a*m33 b)
  (m10 a*m03 b + m11 a*m13 b + m12 a*m23 b + m13 a*m33 b)
  (m20 a*m03 b + m21 a*m13 b + m22 a*m23 b + m23 a*m33 b)
  (m30 a*m03 b + m31 a*m13 b + m32 a*m23 b + m33 a*m33 b)

-- ────────────────────────────────────────────────────────────────────────────
-- Transform Matrices
-- ────────────────────────────────────────────────────────────────────────────

-- | Translation matrix
translate :: Vec3 -> Mat4
translate v = Mat4
  1 0 0 0
  0 1 0 0
  0 0 1 0
  (x v) (y v) (z v) 1

-- | Scale matrix
scaleMat :: Vec3 -> Mat4
scaleMat s = Mat4
  (x s) 0 0 0
  0 (y s) 0 0
  0 0 (z s) 0
  0 0 0 1

-- | Uniform scale matrix
scaleUniform :: Double -> Mat4
scaleUniform s = Mat4
  s 0 0 0
  0 s 0 0
  0 0 s 0
  0 0 0 1

-- | Rotation around X axis
rotateX :: Double -> Mat4
rotateX angle = Mat4
  1 0 0 0
  0 c s 0
  0 (-s) c 0
  0 0 0 1
  where
    c = cos angle
    s = sin angle

-- | Rotation around Y axis
rotateY :: Double -> Mat4
rotateY angle = Mat4
  c 0 (-s) 0
  0 1 0 0
  s 0 c 0
  0 0 0 1
  where
    c = cos angle
    s = sin angle

-- | Rotation around Z axis
rotateZ :: Double -> Mat4
rotateZ angle = Mat4
  c s 0 0
  (-s) c 0 0
  0 0 1 0
  0 0 0 1
  where
    c = cos angle
    s = sin angle

-- ────────────────────────────────────────────────────────────────────────────
-- Projection Matrices
-- ────────────────────────────────────────────────────────────────────────────

-- | Perspective projection matrix
perspective :: Double -> Double -> Double -> Double -> Mat4
perspective fovY aspect near far = Mat4
  (f / aspect) 0 0 0
  0 f 0 0
  0 0 ((far + near) * nf) (-1)
  0 0 (2.0 * far * near * nf) 0
  where
    f = 1.0 / tan (fovY / 2.0)
    nf = 1.0 / (near - far)

-- | Orthographic projection matrix
orthographic :: Double -> Double -> Double -> Double -> Double -> Double -> Mat4
orthographic left right bottom top near far = Mat4
  (2.0 * w) 0 0 0
  0 (2.0 * h) 0 0
  0 0 (-2.0 * p) 0
  (-(right + left) * w) (-(top + bottom) * h) (-(far + near) * p) 1
  where
    w = 1.0 / (right - left)
    h = 1.0 / (top - bottom)
    p = 1.0 / (far - near)

-- ────────────────────────────────────────────────────────────────────────────
-- View Matrix
-- ────────────────────────────────────────────────────────────────────────────

-- | Look-at view matrix
lookAt :: Vec3 -> Vec3 -> Vec3 -> Mat4
lookAt eye target up = Mat4
  (x xAxis) (x yAxis) (x zAxis) 0
  (y xAxis) (y yAxis) (y zAxis) 0
  (z xAxis) (z yAxis) (z zAxis) 0
  (-V.dot xAxis eye) (-V.dot yAxis eye) (-V.dot zAxis eye) 1
  where
    zAxis = V.normalize (V.sub eye target)
    xAxis = V.normalize (V.cross up zAxis)
    yAxis = V.cross zAxis xAxis

-- ────────────────────────────────────────────────────────────────────────────
-- Transform Application
-- ────────────────────────────────────────────────────────────────────────────

-- | Transform a point (applies translation)
transformPoint :: Mat4 -> Vec3 -> Vec3
transformPoint m p =
  let w = m30 m * x p + m31 m * y p + m32 m * z p + m33 m
      invW = if w == 0.0 then 1.0 else 1.0 / w
  in Vec3
       ((m00 m * x p + m01 m * y p + m02 m * z p + m03 m) * invW)
       ((m10 m * x p + m11 m * y p + m12 m * z p + m13 m) * invW)
       ((m20 m * x p + m21 m * y p + m22 m * z p + m23 m) * invW)

-- | Transform a direction (ignores translation)
transformDirection :: Mat4 -> Vec3 -> Vec3
transformDirection m v = Vec3
  (m00 m * x v + m01 m * y v + m02 m * z v)
  (m10 m * x v + m11 m * y v + m12 m * z v)
  (m20 m * x v + m21 m * y v + m22 m * z v)

-- ────────────────────────────────────────────────────────────────────────────
-- Matrix Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Compute determinant
determinant :: Mat4 -> Double
determinant m =
  let aa = m00 m; bb = m01 m; cc = m02 m; dd = m03 m
      ee = m10 m; ff = m11 m; gg = m12 m; hh = m13 m
      ii = m20 m; jj = m21 m; kk = m22 m; ll = m23 m
      mm = m30 m; nn = m31 m; oo = m32 m; pp = m33 m

      kp_lo = kk*pp - ll*oo
      jp_ln = jj*pp - ll*nn
      jo_kn = jj*oo - kk*nn
      ip_lm = ii*pp - ll*mm
      io_km = ii*oo - kk*mm
      in_jm = ii*nn - jj*mm
  in aa*(ff*kp_lo - gg*jp_ln + hh*jo_kn) -
     bb*(ee*kp_lo - gg*ip_lm + hh*io_km) +
     cc*(ee*jp_ln - ff*ip_lm + hh*in_jm) -
     dd*(ee*jo_kn - ff*io_km + gg*in_jm)

-- | Invert matrix
invert :: Mat4 -> InvertResult
invert m
  | det == 0.0 = SingularMatrix
  | otherwise = InvertSuccess $ Mat4
      (c00 * invDet) (c01 * invDet) (c02 * invDet) (c03 * invDet)
      (c10 * invDet) (c11 * invDet) (c12 * invDet) (c13 * invDet)
      (c20 * invDet) (c21 * invDet) (c22 * invDet) (c23 * invDet)
      (c30 * invDet) (c31 * invDet) (c32 * invDet) (c33 * invDet)
  where
    det = determinant m
    invDet = 1.0 / det

    aa = m00 m; bb = m01 m; cc = m02 m; dd = m03 m
    ee = m10 m; ff = m11 m; gg = m12 m; hh = m13 m
    ii = m20 m; jj = m21 m; kk = m22 m; ll = m23 m
    mm' = m30 m; nn = m31 m; oo = m32 m; pp = m33 m

    c00 = ff*(kk*pp - ll*oo) - gg*(jj*pp - ll*nn) + hh*(jj*oo - kk*nn)
    c01 = -(ee*(kk*pp - ll*oo) - gg*(ii*pp - ll*mm') + hh*(ii*oo - kk*mm'))
    c02 = ee*(jj*pp - ll*nn) - ff*(ii*pp - ll*mm') + hh*(ii*nn - jj*mm')
    c03 = -(ee*(jj*oo - kk*nn) - ff*(ii*oo - kk*mm') + gg*(ii*nn - jj*mm'))

    c10 = -(bb*(kk*pp - ll*oo) - cc*(jj*pp - ll*nn) + dd*(jj*oo - kk*nn))
    c11 = aa*(kk*pp - ll*oo) - cc*(ii*pp - ll*mm') + dd*(ii*oo - kk*mm')
    c12 = -(aa*(jj*pp - ll*nn) - bb*(ii*pp - ll*mm') + dd*(ii*nn - jj*mm'))
    c13 = aa*(jj*oo - kk*nn) - bb*(ii*oo - kk*mm') + cc*(ii*nn - jj*mm')

    c20 = bb*(gg*pp - hh*oo) - cc*(ff*pp - hh*nn) + dd*(ff*oo - gg*nn)
    c21 = -(aa*(gg*pp - hh*oo) - cc*(ee*pp - hh*mm') + dd*(ee*oo - gg*mm'))
    c22 = aa*(ff*pp - hh*nn) - bb*(ee*pp - hh*mm') + dd*(ee*nn - ff*mm')
    c23 = -(aa*(ff*oo - gg*nn) - bb*(ee*oo - gg*mm') + cc*(ee*nn - ff*mm'))

    c30 = -(bb*(gg*ll - hh*kk) - cc*(ff*ll - hh*jj) + dd*(ff*kk - gg*jj))
    c31 = aa*(gg*ll - hh*kk) - cc*(ee*ll - hh*ii) + dd*(ee*kk - gg*ii)
    c32 = -(aa*(ff*ll - hh*jj) - bb*(ee*ll - hh*ii) + dd*(ee*jj - ff*ii))
    c33 = aa*(ff*kk - gg*jj) - bb*(ee*kk - gg*ii) + cc*(ee*jj - ff*ii)

-- | Transpose matrix
transposeMat :: Mat4 -> Mat4
transposeMat m = Mat4
  (m00 m) (m01 m) (m02 m) (m03 m)
  (m10 m) (m11 m) (m12 m) (m13 m)
  (m20 m) (m21 m) (m22 m) (m23 m)
  (m30 m) (m31 m) (m32 m) (m33 m)

-- ────────────────────────────────────────────────────────────────────────────
-- Conversion
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert to flat array (column-major)
toArray :: Mat4 -> [Double]
toArray m =
  [ m00 m, m10 m, m20 m, m30 m
  , m01 m, m11 m, m21 m, m31 m
  , m02 m, m12 m, m22 m, m32 m
  , m03 m, m13 m, m23 m, m33 m
  ]
