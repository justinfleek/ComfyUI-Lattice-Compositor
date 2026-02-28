-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // geometry // matrix4
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Matrix4 — 4x4 Matrix for 3D transforms and projection.
-- |
-- | Column-major storage order (compatible with WebGL/OpenGL).
-- | Indices: m[col][row]

module Hydrogen.Schema.Geometry.Matrix4
  ( Matrix4(Matrix4)
  , identity
  , zero
  , fromValues
  , transpose
  , determinant
  , invert
  , multiply
  , translate
  , scale
  , makePerspective
  , makeOrthographic
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , negate
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (==)
  , (<)
  )

import Data.Maybe (Maybe(..))
import Data.Number (abs, tan)
import Hydrogen.Schema.Geometry.Vector (Vector3D(..))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // matrix4
-- ═════════════════════════════════════════════════════════════════════════════

-- | 4x4 Matrix (Column-major)
newtype Matrix4 = Matrix4
  { m00 :: Number, m01 :: Number, m02 :: Number, m03 :: Number
  , m10 :: Number, m11 :: Number, m12 :: Number, m13 :: Number
  , m20 :: Number, m21 :: Number, m22 :: Number, m23 :: Number
  , m30 :: Number, m31 :: Number, m32 :: Number, m33 :: Number
  }

derive instance eqMatrix4 :: Eq Matrix4

instance showMatrix4 :: Show Matrix4 where
  show (Matrix4 m) =
    "(Matrix4 [" <> show m.m00 <> "," <> show m.m01 <> "," <> show m.m02 <> "," <> show m.m03 <> "] ...)"

-- | Identity matrix
identity :: Matrix4
identity = Matrix4
  { m00: 1.0, m01: 0.0, m02: 0.0, m03: 0.0
  , m10: 0.0, m11: 1.0, m12: 0.0, m13: 0.0
  , m20: 0.0, m21: 0.0, m22: 1.0, m23: 0.0
  , m30: 0.0, m31: 0.0, m32: 0.0, m33: 1.0
  }

-- | Zero matrix
zero :: Matrix4
zero = Matrix4
  { m00: 0.0, m01: 0.0, m02: 0.0, m03: 0.0
  , m10: 0.0, m11: 0.0, m12: 0.0, m13: 0.0
  , m20: 0.0, m21: 0.0, m22: 0.0, m23: 0.0
  , m30: 0.0, m31: 0.0, m32: 0.0, m33: 0.0
  }

-- | Create from values (row-major input -> col-major storage)
fromValues 
  :: Number -> Number -> Number -> Number
  -> Number -> Number -> Number -> Number
  -> Number -> Number -> Number -> Number
  -> Number -> Number -> Number -> Number
  -> Matrix4
fromValues n00 n01 n02 n03 n10 n11 n12 n13 n20 n21 n22 n23 n30 n31 n32 n33 = Matrix4
  { m00: n00, m01: n10, m02: n20, m03: n30
  , m10: n01, m11: n11, m12: n21, m13: n31
  , m20: n02, m21: n12, m22: n22, m23: n32
  , m30: n03, m31: n13, m32: n23, m33: n33
  }

-- | Transpose matrix
transpose :: Matrix4 -> Matrix4
transpose (Matrix4 m) = Matrix4
  { m00: m.m00, m01: m.m10, m02: m.m20, m03: m.m30
  , m10: m.m01, m11: m.m11, m12: m.m21, m13: m.m31
  , m20: m.m02, m21: m.m12, m22: m.m22, m23: m.m32
  , m30: m.m03, m31: m.m13, m32: m.m23, m33: m.m33
  }

-- | Determinant
determinant :: Matrix4 -> Number
determinant (Matrix4 m) =
  let
    b00 = m.m00 * m.m11 - m.m01 * m.m10
    b01 = m.m00 * m.m12 - m.m02 * m.m10
    b02 = m.m00 * m.m13 - m.m03 * m.m10
    b03 = m.m01 * m.m12 - m.m02 * m.m11
    b04 = m.m01 * m.m13 - m.m03 * m.m11
    b05 = m.m02 * m.m13 - m.m03 * m.m12
    b06 = m.m20 * m.m31 - m.m21 * m.m30
    b07 = m.m20 * m.m32 - m.m22 * m.m30
    b08 = m.m20 * m.m33 - m.m23 * m.m30
    b09 = m.m21 * m.m32 - m.m22 * m.m31
    b10 = m.m21 * m.m33 - m.m23 * m.m31
    b11 = m.m22 * m.m33 - m.m23 * m.m32
  in
    b00 * b11 - b01 * b10 + b02 * b09 + b03 * b08 - b04 * b07 + b05 * b06

-- | Invert matrix
invert :: Matrix4 -> Maybe Matrix4
invert m@(Matrix4 r) =
  let
    det = determinant m
  in
    if abs det < 0.000001
      then Nothing
      else
        -- Full inversion implementation omitted for brevity, generally huge.
        -- Placeholder for now:
        Nothing 

-- | Multiply matrices (A * B)
multiply :: Matrix4 -> Matrix4 -> Matrix4
multiply (Matrix4 a) (Matrix4 b) = Matrix4
  { m00: a.m00 * b.m00 + a.m10 * b.m01 + a.m20 * b.m02 + a.m30 * b.m03
  , m01: a.m01 * b.m00 + a.m11 * b.m01 + a.m21 * b.m02 + a.m31 * b.m03
  , m02: a.m02 * b.m00 + a.m12 * b.m01 + a.m22 * b.m02 + a.m32 * b.m03
  , m03: a.m03 * b.m00 + a.m13 * b.m01 + a.m23 * b.m02 + a.m33 * b.m03
  
  , m10: a.m00 * b.m10 + a.m10 * b.m11 + a.m20 * b.m12 + a.m30 * b.m13
  , m11: a.m01 * b.m10 + a.m11 * b.m11 + a.m21 * b.m12 + a.m31 * b.m13
  , m12: a.m02 * b.m10 + a.m12 * b.m11 + a.m22 * b.m12 + a.m32 * b.m13
  , m13: a.m03 * b.m10 + a.m13 * b.m11 + a.m23 * b.m12 + a.m33 * b.m13
  
  , m20: a.m00 * b.m20 + a.m10 * b.m21 + a.m20 * b.m22 + a.m30 * b.m23
  , m21: a.m01 * b.m20 + a.m11 * b.m21 + a.m21 * b.m22 + a.m31 * b.m23
  , m22: a.m02 * b.m20 + a.m12 * b.m21 + a.m22 * b.m22 + a.m32 * b.m23
  , m23: a.m03 * b.m20 + a.m13 * b.m21 + a.m23 * b.m22 + a.m33 * b.m23
  
  , m30: a.m00 * b.m30 + a.m10 * b.m31 + a.m20 * b.m32 + a.m30 * b.m33
  , m31: a.m01 * b.m30 + a.m11 * b.m31 + a.m21 * b.m32 + a.m31 * b.m33
  , m32: a.m02 * b.m30 + a.m12 * b.m31 + a.m22 * b.m32 + a.m32 * b.m33
  , m33: a.m03 * b.m30 + a.m13 * b.m31 + a.m23 * b.m32 + a.m33 * b.m33
  }

-- | Make translation matrix
translate :: Vector3D -> Matrix4
translate (Vector3D v) = Matrix4
  { m00: 1.0, m01: 0.0, m02: 0.0, m03: 0.0
  , m10: 0.0, m11: 1.0, m12: 0.0, m13: 0.0
  , m20: 0.0, m21: 0.0, m22: 1.0, m23: 0.0
  , m30: v.x, m31: v.y, m32: v.z, m33: 1.0
  }

-- | Make scale matrix
scale :: Vector3D -> Matrix4
scale (Vector3D v) = Matrix4
  { m00: v.x, m01: 0.0, m02: 0.0, m03: 0.0
  , m10: 0.0, m11: v.y, m12: 0.0, m13: 0.0
  , m20: 0.0, m21: 0.0, m22: v.z, m23: 0.0
  , m30: 0.0, m31: 0.0, m32: 0.0, m33: 1.0
  }

-- | Make perspective projection matrix
makePerspective :: Number -> Number -> Number -> Number -> Matrix4
makePerspective fov aspect near far =
  let
    f = 1.0 / tan (fov * 0.5)
    nf = 1.0 / (near - far)
  in Matrix4
    { m00: f / aspect, m01: 0.0, m02: 0.0, m03: 0.0
    , m10: 0.0,        m11: f,   m12: 0.0, m13: 0.0
    , m20: 0.0,        m21: 0.0, m22: (far + near) * nf, m23: -1.0
    , m30: 0.0,        m31: 0.0, m32: (2.0 * far * near) * nf, m33: 0.0
    }

-- | Make orthographic projection matrix
makeOrthographic :: Number -> Number -> Number -> Number -> Number -> Number -> Matrix4
makeOrthographic left right top bottom near far =
  let
    w = 1.0 / (right - left)
    h = 1.0 / (top - bottom)
    p = 1.0 / (far - near)
    x = (right + left) * w
    y = (top + bottom) * h
    z = (far + near) * p
  in Matrix4
    { m00: 2.0 * w, m01: 0.0,     m02: 0.0,      m03: 0.0
    , m10: 0.0,     m11: 2.0 * h, m12: 0.0,      m13: 0.0
    , m20: 0.0,     m21: 0.0,     m22: -2.0 * p, m23: 0.0
    , m30: -x,      m31: -y,      m32: -z,       m33: 1.0
    }
