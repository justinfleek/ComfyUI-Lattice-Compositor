-- | Lattice.Services.Math3D.Mat4 - 4x4 Matrix operations
-- |
-- | Pure math functions for 4x4 matrix manipulation.
-- | Column-major order for GPU compatibility.
-- |
-- | Source: ui/src/services/math3d.ts

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

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Math (cos, sin, tan) as Math
import Lattice.Services.Math3D.Vec3 (Vec3(..))
import Lattice.Services.Math3D.Vec3 as V

--------------------------------------------------------------------------------
-- Mat4 Type (Column-Major, GPU-compatible)
--------------------------------------------------------------------------------

-- | 4x4 Matrix in column-major order
newtype Mat4 = Mat4
  { m00 :: Number, m10 :: Number, m20 :: Number, m30 :: Number  -- Column 0
  , m01 :: Number, m11 :: Number, m21 :: Number, m31 :: Number  -- Column 1
  , m02 :: Number, m12 :: Number, m22 :: Number, m32 :: Number  -- Column 2
  , m03 :: Number, m13 :: Number, m23 :: Number, m33 :: Number  -- Column 3
  }

derive instance Generic Mat4 _
derive newtype instance Eq Mat4
instance Show Mat4 where show = genericShow

-- | Inversion result type
data InvertResult
  = InvertSuccess Mat4
  | SingularMatrix

derive instance Eq InvertResult
derive instance Generic InvertResult _
instance Show InvertResult where show = genericShow

--------------------------------------------------------------------------------
-- Constructors
--------------------------------------------------------------------------------

-- | Identity matrix
identity :: Mat4
identity = Mat4
  { m00: 1.0, m10: 0.0, m20: 0.0, m30: 0.0
  , m01: 0.0, m11: 1.0, m21: 0.0, m31: 0.0
  , m02: 0.0, m12: 0.0, m22: 1.0, m32: 0.0
  , m03: 0.0, m13: 0.0, m23: 0.0, m33: 1.0
  }

-- | Zero matrix
zeroMat :: Mat4
zeroMat = Mat4
  { m00: 0.0, m10: 0.0, m20: 0.0, m30: 0.0
  , m01: 0.0, m11: 0.0, m21: 0.0, m31: 0.0
  , m02: 0.0, m12: 0.0, m22: 0.0, m32: 0.0
  , m03: 0.0, m13: 0.0, m23: 0.0, m33: 0.0
  }

--------------------------------------------------------------------------------
-- Basic Operations
--------------------------------------------------------------------------------

-- | Matrix multiplication
multiply :: Mat4 -> Mat4 -> Mat4
multiply (Mat4 a) (Mat4 b) = Mat4
  { m00: a.m00*b.m00 + a.m01*b.m10 + a.m02*b.m20 + a.m03*b.m30
  , m10: a.m10*b.m00 + a.m11*b.m10 + a.m12*b.m20 + a.m13*b.m30
  , m20: a.m20*b.m00 + a.m21*b.m10 + a.m22*b.m20 + a.m23*b.m30
  , m30: a.m30*b.m00 + a.m31*b.m10 + a.m32*b.m20 + a.m33*b.m30

  , m01: a.m00*b.m01 + a.m01*b.m11 + a.m02*b.m21 + a.m03*b.m31
  , m11: a.m10*b.m01 + a.m11*b.m11 + a.m12*b.m21 + a.m13*b.m31
  , m21: a.m20*b.m01 + a.m21*b.m11 + a.m22*b.m21 + a.m23*b.m31
  , m31: a.m30*b.m01 + a.m31*b.m11 + a.m32*b.m21 + a.m33*b.m31

  , m02: a.m00*b.m02 + a.m01*b.m12 + a.m02*b.m22 + a.m03*b.m32
  , m12: a.m10*b.m02 + a.m11*b.m12 + a.m12*b.m22 + a.m13*b.m32
  , m22: a.m20*b.m02 + a.m21*b.m12 + a.m22*b.m22 + a.m23*b.m32
  , m32: a.m30*b.m02 + a.m31*b.m12 + a.m32*b.m22 + a.m33*b.m32

  , m03: a.m00*b.m03 + a.m01*b.m13 + a.m02*b.m23 + a.m03*b.m33
  , m13: a.m10*b.m03 + a.m11*b.m13 + a.m12*b.m23 + a.m13*b.m33
  , m23: a.m20*b.m03 + a.m21*b.m13 + a.m22*b.m23 + a.m23*b.m33
  , m33: a.m30*b.m03 + a.m31*b.m13 + a.m32*b.m23 + a.m33*b.m33
  }

--------------------------------------------------------------------------------
-- Transform Matrices
--------------------------------------------------------------------------------

-- | Translation matrix
translate :: Vec3 -> Mat4
translate (Vec3 v) = Mat4
  { m00: 1.0, m10: 0.0, m20: 0.0, m30: 0.0
  , m01: 0.0, m11: 1.0, m21: 0.0, m31: 0.0
  , m02: 0.0, m12: 0.0, m22: 1.0, m32: 0.0
  , m03: v.x, m13: v.y, m23: v.z, m33: 1.0
  }

-- | Scale matrix
scaleMat :: Vec3 -> Mat4
scaleMat (Vec3 s) = Mat4
  { m00: s.x, m10: 0.0, m20: 0.0, m30: 0.0
  , m01: 0.0, m11: s.y, m21: 0.0, m31: 0.0
  , m02: 0.0, m12: 0.0, m22: s.z, m32: 0.0
  , m03: 0.0, m13: 0.0, m23: 0.0, m33: 1.0
  }

-- | Uniform scale matrix
scaleUniform :: Number -> Mat4
scaleUniform s = Mat4
  { m00: s, m10: 0.0, m20: 0.0, m30: 0.0
  , m01: 0.0, m11: s, m21: 0.0, m31: 0.0
  , m02: 0.0, m12: 0.0, m22: s, m32: 0.0
  , m03: 0.0, m13: 0.0, m23: 0.0, m33: 1.0
  }

-- | Rotation around X axis
rotateX :: Number -> Mat4
rotateX angle = Mat4
  { m00: 1.0, m10: 0.0, m20: 0.0, m30: 0.0
  , m01: 0.0, m11: c, m21: s, m31: 0.0
  , m02: 0.0, m12: -s, m22: c, m32: 0.0
  , m03: 0.0, m13: 0.0, m23: 0.0, m33: 1.0
  }
  where
    c = Math.cos angle
    s = Math.sin angle

-- | Rotation around Y axis
rotateY :: Number -> Mat4
rotateY angle = Mat4
  { m00: c, m10: 0.0, m20: -s, m30: 0.0
  , m01: 0.0, m11: 1.0, m21: 0.0, m31: 0.0
  , m02: s, m12: 0.0, m22: c, m32: 0.0
  , m03: 0.0, m13: 0.0, m23: 0.0, m33: 1.0
  }
  where
    c = Math.cos angle
    s = Math.sin angle

-- | Rotation around Z axis
rotateZ :: Number -> Mat4
rotateZ angle = Mat4
  { m00: c, m10: s, m20: 0.0, m30: 0.0
  , m01: -s, m11: c, m21: 0.0, m31: 0.0
  , m02: 0.0, m12: 0.0, m22: 1.0, m32: 0.0
  , m03: 0.0, m13: 0.0, m23: 0.0, m33: 1.0
  }
  where
    c = Math.cos angle
    s = Math.sin angle

--------------------------------------------------------------------------------
-- Projection Matrices
--------------------------------------------------------------------------------

-- | Perspective projection matrix
perspective :: Number -> Number -> Number -> Number -> Mat4
perspective fovY aspect near far = Mat4
  { m00: f / aspect, m10: 0.0, m20: 0.0, m30: 0.0
  , m01: 0.0, m11: f, m21: 0.0, m31: 0.0
  , m02: 0.0, m12: 0.0, m22: (far + near) * nf, m32: -1.0
  , m03: 0.0, m13: 0.0, m23: 2.0 * far * near * nf, m33: 0.0
  }
  where
    f = 1.0 / Math.tan (fovY / 2.0)
    nf = 1.0 / (near - far)

-- | Orthographic projection matrix
orthographic :: Number -> Number -> Number -> Number -> Number -> Number -> Mat4
orthographic left right bottom top near far = Mat4
  { m00: 2.0 * w, m10: 0.0, m20: 0.0, m30: 0.0
  , m01: 0.0, m11: 2.0 * h, m21: 0.0, m31: 0.0
  , m02: 0.0, m12: 0.0, m22: -2.0 * p, m32: 0.0
  , m03: -(right + left) * w, m13: -(top + bottom) * h, m23: -(far + near) * p, m33: 1.0
  }
  where
    w = 1.0 / (right - left)
    h = 1.0 / (top - bottom)
    p = 1.0 / (far - near)

--------------------------------------------------------------------------------
-- View Matrix
--------------------------------------------------------------------------------

-- | Look-at view matrix
lookAt :: Vec3 -> Vec3 -> Vec3 -> Mat4
lookAt eye target up = Mat4
  { m00: V.getX xAxis, m10: V.getX yAxis, m20: V.getX zAxis, m30: 0.0
  , m01: V.getY xAxis, m11: V.getY yAxis, m21: V.getY zAxis, m31: 0.0
  , m02: V.getZ xAxis, m12: V.getZ yAxis, m22: V.getZ zAxis, m32: 0.0
  , m03: -V.dot xAxis eye, m13: -V.dot yAxis eye, m23: -V.dot zAxis eye, m33: 1.0
  }
  where
    zAxis = V.normalize (V.sub eye target)
    xAxis = V.normalize (V.cross up zAxis)
    yAxis = V.cross zAxis xAxis

--------------------------------------------------------------------------------
-- Transform Application
--------------------------------------------------------------------------------

-- | Transform a point (applies translation)
transformPoint :: Mat4 -> Vec3 -> Vec3
transformPoint (Mat4 m) (Vec3 p) =
  let w = m.m30 * p.x + m.m31 * p.y + m.m32 * p.z + m.m33
      invW = if w == 0.0 then 1.0 else 1.0 / w
  in Vec3
       { x: (m.m00 * p.x + m.m01 * p.y + m.m02 * p.z + m.m03) * invW
       , y: (m.m10 * p.x + m.m11 * p.y + m.m12 * p.z + m.m13) * invW
       , z: (m.m20 * p.x + m.m21 * p.y + m.m22 * p.z + m.m23) * invW
       }

-- | Transform a direction (ignores translation)
transformDirection :: Mat4 -> Vec3 -> Vec3
transformDirection (Mat4 m) (Vec3 v) = Vec3
  { x: m.m00 * v.x + m.m01 * v.y + m.m02 * v.z
  , y: m.m10 * v.x + m.m11 * v.y + m.m12 * v.z
  , z: m.m20 * v.x + m.m21 * v.y + m.m22 * v.z
  }

--------------------------------------------------------------------------------
-- Matrix Operations
--------------------------------------------------------------------------------

-- | Compute determinant
determinant :: Mat4 -> Number
determinant (Mat4 m) =
  let kp_lo = m.m22*m.m33 - m.m23*m.m32
      jp_ln = m.m21*m.m33 - m.m23*m.m31
      jo_kn = m.m21*m.m32 - m.m22*m.m31
      ip_lm = m.m20*m.m33 - m.m23*m.m30
      io_km = m.m20*m.m32 - m.m22*m.m30
      in_jm = m.m20*m.m31 - m.m21*m.m30
  in m.m00*(m.m11*kp_lo - m.m12*jp_ln + m.m13*jo_kn) -
     m.m01*(m.m10*kp_lo - m.m12*ip_lm + m.m13*io_km) +
     m.m02*(m.m10*jp_ln - m.m11*ip_lm + m.m13*in_jm) -
     m.m03*(m.m10*jo_kn - m.m11*io_km + m.m12*in_jm)

-- | Invert matrix
invert :: Mat4 -> InvertResult
invert mat@(Mat4 m)
  | det == 0.0 = SingularMatrix
  | otherwise = InvertSuccess $ Mat4
      { m00: c00 * invDet, m10: c01 * invDet, m20: c02 * invDet, m30: c03 * invDet
      , m01: c10 * invDet, m11: c11 * invDet, m21: c12 * invDet, m31: c13 * invDet
      , m02: c20 * invDet, m12: c21 * invDet, m22: c22 * invDet, m32: c23 * invDet
      , m03: c30 * invDet, m13: c31 * invDet, m23: c32 * invDet, m33: c33 * invDet
      }
  where
    det = determinant mat
    invDet = 1.0 / det

    c00 = m.m11*(m.m22*m.m33 - m.m23*m.m32) - m.m12*(m.m21*m.m33 - m.m23*m.m31) + m.m13*(m.m21*m.m32 - m.m22*m.m31)
    c01 = -(m.m10*(m.m22*m.m33 - m.m23*m.m32) - m.m12*(m.m20*m.m33 - m.m23*m.m30) + m.m13*(m.m20*m.m32 - m.m22*m.m30))
    c02 = m.m10*(m.m21*m.m33 - m.m23*m.m31) - m.m11*(m.m20*m.m33 - m.m23*m.m30) + m.m13*(m.m20*m.m31 - m.m21*m.m30)
    c03 = -(m.m10*(m.m21*m.m32 - m.m22*m.m31) - m.m11*(m.m20*m.m32 - m.m22*m.m30) + m.m12*(m.m20*m.m31 - m.m21*m.m30))

    c10 = -(m.m01*(m.m22*m.m33 - m.m23*m.m32) - m.m02*(m.m21*m.m33 - m.m23*m.m31) + m.m03*(m.m21*m.m32 - m.m22*m.m31))
    c11 = m.m00*(m.m22*m.m33 - m.m23*m.m32) - m.m02*(m.m20*m.m33 - m.m23*m.m30) + m.m03*(m.m20*m.m32 - m.m22*m.m30)
    c12 = -(m.m00*(m.m21*m.m33 - m.m23*m.m31) - m.m01*(m.m20*m.m33 - m.m23*m.m30) + m.m03*(m.m20*m.m31 - m.m21*m.m30))
    c13 = m.m00*(m.m21*m.m32 - m.m22*m.m31) - m.m01*(m.m20*m.m32 - m.m22*m.m30) + m.m02*(m.m20*m.m31 - m.m21*m.m30)

    c20 = m.m01*(m.m12*m.m33 - m.m13*m.m32) - m.m02*(m.m11*m.m33 - m.m13*m.m31) + m.m03*(m.m11*m.m32 - m.m12*m.m31)
    c21 = -(m.m00*(m.m12*m.m33 - m.m13*m.m32) - m.m02*(m.m10*m.m33 - m.m13*m.m30) + m.m03*(m.m10*m.m32 - m.m12*m.m30))
    c22 = m.m00*(m.m11*m.m33 - m.m13*m.m31) - m.m01*(m.m10*m.m33 - m.m13*m.m30) + m.m03*(m.m10*m.m31 - m.m11*m.m30)
    c23 = -(m.m00*(m.m11*m.m32 - m.m12*m.m31) - m.m01*(m.m10*m.m32 - m.m12*m.m30) + m.m02*(m.m10*m.m31 - m.m11*m.m30))

    c30 = -(m.m01*(m.m12*m.m23 - m.m13*m.m22) - m.m02*(m.m11*m.m23 - m.m13*m.m21) + m.m03*(m.m11*m.m22 - m.m12*m.m21))
    c31 = m.m00*(m.m12*m.m23 - m.m13*m.m22) - m.m02*(m.m10*m.m23 - m.m13*m.m20) + m.m03*(m.m10*m.m22 - m.m12*m.m20)
    c32 = -(m.m00*(m.m11*m.m23 - m.m13*m.m21) - m.m01*(m.m10*m.m23 - m.m13*m.m20) + m.m03*(m.m10*m.m21 - m.m11*m.m20))
    c33 = m.m00*(m.m11*m.m22 - m.m12*m.m21) - m.m01*(m.m10*m.m22 - m.m12*m.m20) + m.m02*(m.m10*m.m21 - m.m11*m.m20)

-- | Transpose matrix
transposeMat :: Mat4 -> Mat4
transposeMat (Mat4 m) = Mat4
  { m00: m.m00, m10: m.m01, m20: m.m02, m30: m.m03
  , m01: m.m10, m11: m.m11, m21: m.m12, m31: m.m13
  , m02: m.m20, m12: m.m21, m22: m.m22, m32: m.m23
  , m03: m.m30, m13: m.m31, m23: m.m32, m33: m.m33
  }

--------------------------------------------------------------------------------
-- Conversion
--------------------------------------------------------------------------------

-- | Convert to flat array (column-major)
toArray :: Mat4 -> Array Number
toArray (Mat4 m) =
  [ m.m00, m.m10, m.m20, m.m30
  , m.m01, m.m11, m.m21, m.m31
  , m.m02, m.m12, m.m22, m.m32
  , m.m03, m.m13, m.m23, m.m33
  ]
