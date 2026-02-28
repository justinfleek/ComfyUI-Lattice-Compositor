-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // geometry // matrix3
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Matrix3 — 3x3 Matrix for 2D transforms and 3D rotations.
-- |
-- | Column-major storage order (compatible with WebGL/OpenGL).
-- | Indices: m[col][row]
-- |
-- | [ m00 m10 m20 ]
-- | [ m01 m11 m21 ]
-- | [ m02 m12 m22 ]

module Hydrogen.Schema.Geometry.Matrix3
  ( Matrix3(Matrix3)
  , identity
  , zero
  , fromValues
  , transpose
  , determinant
  , invert
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
import Data.Number (abs)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // matrix3
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3x3 Matrix (Column-major)
newtype Matrix3 = Matrix3
  { m00 :: Number, m01 :: Number, m02 :: Number
  , m10 :: Number, m11 :: Number, m12 :: Number
  , m20 :: Number, m21 :: Number, m22 :: Number
  }

derive instance eqMatrix3 :: Eq Matrix3

instance showMatrix3 :: Show Matrix3 where
  show (Matrix3 m) =
    "(Matrix3 [" <> show m.m00 <> "," <> show m.m01 <> "," <> show m.m02 <> "] " <>
              "[" <> show m.m10 <> "," <> show m.m11 <> "," <> show m.m12 <> "] " <>
              "[" <> show m.m20 <> "," <> show m.m21 <> "," <> show m.m22 <> "])"

-- | Identity matrix
identity :: Matrix3
identity = Matrix3
  { m00: 1.0, m01: 0.0, m02: 0.0
  , m10: 0.0, m11: 1.0, m12: 0.0
  , m20: 0.0, m21: 0.0, m22: 1.0
  }

-- | Zero matrix
zero :: Matrix3
zero = Matrix3
  { m00: 0.0, m01: 0.0, m02: 0.0
  , m10: 0.0, m11: 0.0, m12: 0.0
  , m20: 0.0, m21: 0.0, m22: 0.0
  }

-- | Create from values (row-major input converted to column-major storage)
fromValues 
  :: Number -> Number -> Number
  -> Number -> Number -> Number
  -> Number -> Number -> Number
  -> Matrix3
fromValues n00 n01 n02 n10 n11 n12 n20 n21 n22 = Matrix3
  { m00: n00, m01: n10, m02: n20  -- Transposed for col-major storage
  , m10: n01, m11: n11, m12: n21
  , m20: n02, m21: n12, m22: n22
  }

-- | Transpose matrix
transpose :: Matrix3 -> Matrix3
transpose (Matrix3 m) = Matrix3
  { m00: m.m00, m01: m.m10, m02: m.m20
  , m10: m.m01, m11: m.m11, m12: m.m21
  , m20: m.m02, m21: m.m12, m22: m.m22
  }

-- | Determinant
determinant :: Matrix3 -> Number
determinant (Matrix3 m) =
  let
    a = m.m00 * (m.m11 * m.m22 - m.m21 * m.m12)
    b = m.m10 * (m.m01 * m.m22 - m.m21 * m.m02)
    c = m.m20 * (m.m01 * m.m12 - m.m11 * m.m02)
  in
    a - b + c

-- | Invert matrix
invert :: Matrix3 -> Maybe Matrix3
invert m@(Matrix3 r) =
  let
    det = determinant m
  in
    if abs det < 0.000001
      then Nothing
      else
        let
          invDet = 1.0 / det
          
          m00 = (r.m11 * r.m22 - r.m21 * r.m12) * invDet
          m01 = (r.m21 * r.m02 - r.m01 * r.m22) * invDet
          m02 = (r.m01 * r.m12 - r.m11 * r.m02) * invDet
          
          m10 = (r.m20 * r.m12 - r.m10 * r.m22) * invDet
          m11 = (r.m00 * r.m22 - r.m20 * r.m02) * invDet
          m12 = (r.m10 * r.m02 - r.m00 * r.m12) * invDet
          
          m20 = (r.m10 * r.m21 - r.m20 * r.m11) * invDet
          m21 = (r.m20 * r.m01 - r.m00 * r.m21) * invDet
          m22 = (r.m00 * r.m11 - r.m10 * r.m01) * invDet
        in
          Just (Matrix3
            { m00, m01, m02
            , m10, m11, m12
            , m20, m21, m22
            })
