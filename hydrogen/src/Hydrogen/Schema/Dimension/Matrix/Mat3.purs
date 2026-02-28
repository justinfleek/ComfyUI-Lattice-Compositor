-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // dimension // matrix // mat3
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 3x3 Matrix type for 2D transforms and normal transformations.
-- |
-- | ## Proof References
-- | All operations correspond to proven theorems in `proofs/Hydrogen/Math/Mat3.lean`:
-- | - mul_assoc: Matrix multiplication is associative
-- | - mul_identity: I × A = A × I = A
-- | - transpose_involutive: (Aᵀ)ᵀ = A
-- | - transpose_mul: (AB)ᵀ = BᵀAᵀ
-- | - det_identity: det(I) = 1
-- | - det_mul: det(AB) = det(A) × det(B)
-- |
-- | ## Applications
-- | - Normal transformation: N' = (M⁻¹)ᵀ × N
-- | - 2D transforms (with homogeneous coords)
-- | - Rotation matrices (3D)
-- | - Upper-left 3×3 of Mat4
-- |
-- | ## Storage Order
-- | Row-major: m[row][col]
-- | | m00 m01 m02 |
-- | | m10 m11 m12 |
-- | | m20 m21 m22 |

module Hydrogen.Schema.Dimension.Matrix.Mat3
  ( -- * Type
    Mat3(Mat3)
  
  -- * Constructors
  , mat3
  , mat3Identity
  , mat3Zero
  , mat3Diagonal
  , mat3UniformScale
  
  -- * Basic Operations
  , addMat3
  , subtractMat3
  , scaleMat3
  , negateMat3
  , transposeMat3
  
  -- * Matrix Multiplication
  , mulMat3
  , mulVec3Mat3
  
  -- * Determinant
  , detMat3
  , isInvertibleMat3
  
  -- * Inverse
  , inverseMat3
  
  -- * Rotation Matrices
  , makeRotationX3
  , makeRotationY3
  , makeRotationZ3
  , makeScale3
  
  -- * Accessors
  , getElementMat3
  , getRowMat3
  , getColumnMat3
  ) where

import Prelude
  ( class Eq
  , class Show
  , negate
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (==)
  , (/=)
  , (<>)
  )

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3(Vec3), vec3)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3×3 matrix stored in row-major order
-- | 
-- | | m00 m01 m02 |
-- | | m10 m11 m12 |
-- | | m20 m21 m22 |
data Mat3 = Mat3
  Number Number Number  -- Row 0: m00 m01 m02
  Number Number Number  -- Row 1: m10 m11 m12
  Number Number Number  -- Row 2: m20 m21 m22

derive instance eqMat3 :: Eq Mat3

instance showMat3 :: Show Mat3 where
  show (Mat3 m00 m01 m02 m10 m11 m12 m20 m21 m22) =
    "Mat3(\n  " <> show m00 <> ", " <> show m01 <> ", " <> show m02 <> "\n  "
               <> show m10 <> ", " <> show m11 <> ", " <> show m12 <> "\n  "
               <> show m20 <> ", " <> show m21 <> ", " <> show m22 <> "\n)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a 3x3 matrix from elements (row-major order)
mat3 
  :: Number -> Number -> Number
  -> Number -> Number -> Number
  -> Number -> Number -> Number
  -> Mat3
mat3 = Mat3

-- | Identity matrix
-- | Proof reference: Mat3.lean identity, mul_identity_left, mul_identity_right
mat3Identity :: Mat3
mat3Identity = Mat3
  1.0 0.0 0.0
  0.0 1.0 0.0
  0.0 0.0 1.0

-- | Zero matrix
-- | Proof reference: Mat3.lean zero, mul_zero_left, mul_zero_right
mat3Zero :: Mat3
mat3Zero = Mat3
  0.0 0.0 0.0
  0.0 0.0 0.0
  0.0 0.0 0.0

-- | Diagonal matrix
-- | Proof reference: Mat3.lean diagonal, det_diagonal
mat3Diagonal :: Number -> Number -> Number -> Mat3
mat3Diagonal d0 d1 d2 = Mat3
  d0  0.0 0.0
  0.0 d1  0.0
  0.0 0.0 d2

-- | Uniform scale matrix
-- | Proof reference: Mat3.lean uniformScale, uniformScale_one
mat3UniformScale :: Number -> Mat3
mat3UniformScale s = mat3Diagonal s s s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // basic operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Matrix addition
addMat3 :: Mat3 -> Mat3 -> Mat3
addMat3 (Mat3 a00 a01 a02 a10 a11 a12 a20 a21 a22)
        (Mat3 b00 b01 b02 b10 b11 b12 b20 b21 b22) = Mat3
  (a00 + b00) (a01 + b01) (a02 + b02)
  (a10 + b10) (a11 + b11) (a12 + b12)
  (a20 + b20) (a21 + b21) (a22 + b22)

-- | Matrix subtraction
subtractMat3 :: Mat3 -> Mat3 -> Mat3
subtractMat3 (Mat3 a00 a01 a02 a10 a11 a12 a20 a21 a22)
             (Mat3 b00 b01 b02 b10 b11 b12 b20 b21 b22) = Mat3
  (a00 - b00) (a01 - b01) (a02 - b02)
  (a10 - b10) (a11 - b11) (a12 - b12)
  (a20 - b20) (a21 - b21) (a22 - b22)

-- | Scalar multiplication
-- | Proof reference: Mat3.lean scale, transpose_scale
scaleMat3 :: Number -> Mat3 -> Mat3
scaleMat3 s (Mat3 m00 m01 m02 m10 m11 m12 m20 m21 m22) = Mat3
  (s * m00) (s * m01) (s * m02)
  (s * m10) (s * m11) (s * m12)
  (s * m20) (s * m21) (s * m22)

-- | Negation
negateMat3 :: Mat3 -> Mat3
negateMat3 (Mat3 m00 m01 m02 m10 m11 m12 m20 m21 m22) = Mat3
  (negate m00) (negate m01) (negate m02)
  (negate m10) (negate m11) (negate m12)
  (negate m20) (negate m21) (negate m22)

-- | Matrix transpose
-- | Proof reference: Mat3.lean transpose, transpose_involutive, transpose_mul
transposeMat3 :: Mat3 -> Mat3
transposeMat3 (Mat3 m00 m01 m02 m10 m11 m12 m20 m21 m22) = Mat3
  m00 m10 m20
  m01 m11 m21
  m02 m12 m22

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // matrix multiplication
-- ═════════════════════════════════════════════════════════════════════════════

-- | Matrix multiplication: C = A × B
-- | Proof reference: Mat3.lean mul, mul_assoc, mul_identity_left, mul_identity_right
mulMat3 :: Mat3 -> Mat3 -> Mat3
mulMat3 (Mat3 a00 a01 a02 a10 a11 a12 a20 a21 a22)
        (Mat3 b00 b01 b02 b10 b11 b12 b20 b21 b22) = Mat3
  -- Row 0
  (a00 * b00 + a01 * b10 + a02 * b20)
  (a00 * b01 + a01 * b11 + a02 * b21)
  (a00 * b02 + a01 * b12 + a02 * b22)
  -- Row 1
  (a10 * b00 + a11 * b10 + a12 * b20)
  (a10 * b01 + a11 * b11 + a12 * b21)
  (a10 * b02 + a11 * b12 + a12 * b22)
  -- Row 2
  (a20 * b00 + a21 * b10 + a22 * b20)
  (a20 * b01 + a21 * b11 + a22 * b21)
  (a20 * b02 + a21 * b12 + a22 * b22)

-- | Matrix-vector multiplication: v' = M × v
-- | Proof reference: Mat3.lean mulVec, mulVec_identity, mulVec_mul
mulVec3Mat3 :: Mat3 -> Vec3 Number -> Vec3 Number
mulVec3Mat3 (Mat3 m00 m01 m02 m10 m11 m12 m20 m21 m22) (Vec3 x y z) = vec3
  (m00 * x + m01 * y + m02 * z)
  (m10 * x + m11 * y + m12 * z)
  (m20 * x + m21 * y + m22 * z)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // determinant
-- ═════════════════════════════════════════════════════════════════════════════

-- | Determinant using Sarrus' rule / cofactor expansion
-- | Proof reference: Mat3.lean det, det_identity, det_mul, det_transpose
detMat3 :: Mat3 -> Number
detMat3 (Mat3 m00 m01 m02 m10 m11 m12 m20 m21 m22) =
  m00 * (m11 * m22 - m12 * m21) -
  m01 * (m10 * m22 - m12 * m20) +
  m02 * (m10 * m21 - m11 * m20)

-- | Check if matrix is invertible (determinant non-zero)
-- | Proof reference: Mat3.lean Invertible
isInvertibleMat3 :: Mat3 -> Boolean
isInvertibleMat3 m = detMat3 m /= 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // inverse
-- ═════════════════════════════════════════════════════════════════════════════

-- | Matrix inverse using cofactor/adjugate method
-- | M⁻¹ = adj(M) / det(M)
-- | Returns identity if matrix is singular (det = 0)
-- | Proof reference: Mat3.lean inverse, mul_inverse, inverse_mul
inverseMat3 :: Mat3 -> Mat3
inverseMat3 m@(Mat3 m00 m01 m02 m10 m11 m12 m20 m21 m22) =
  let d = detMat3 m
  in if d == 0.0 then mat3Identity
  else
    let
      -- Cofactors
      c00 = m11 * m22 - m12 * m21
      c01 = negate (m10 * m22 - m12 * m20)
      c02 = m10 * m21 - m11 * m20
      c10 = negate (m01 * m22 - m02 * m21)
      c11 = m00 * m22 - m02 * m20
      c12 = negate (m00 * m21 - m01 * m20)
      c20 = m01 * m12 - m02 * m11
      c21 = negate (m00 * m12 - m02 * m10)
      c22 = m00 * m11 - m01 * m10
      invDet = 1.0 / d
    -- Adjugate is transpose of cofactor matrix, scaled by 1/det
    in Mat3
      (invDet * c00) (invDet * c10) (invDet * c20)
      (invDet * c01) (invDet * c11) (invDet * c21)
      (invDet * c02) (invDet * c12) (invDet * c22)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // rotation matrices
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotation about X axis
-- | Proof reference: Mat3.lean makeRotationX, det_makeRotationX, makeRotationX_zero
makeRotationX3 :: Number -> Mat3
makeRotationX3 angle =
  let c = Math.cos angle
      s = Math.sin angle
  in Mat3
    1.0 0.0 0.0
    0.0 c   (negate s)
    0.0 s   c

-- | Rotation about Y axis
-- | Proof reference: Mat3.lean makeRotationY, det_makeRotationY, makeRotationY_zero
makeRotationY3 :: Number -> Mat3
makeRotationY3 angle =
  let c = Math.cos angle
      s = Math.sin angle
  in Mat3
    c   0.0 s
    0.0 1.0 0.0
    (negate s) 0.0 c

-- | Rotation about Z axis
-- | Proof reference: Mat3.lean makeRotationZ, det_makeRotationZ, makeRotationZ_zero
makeRotationZ3 :: Number -> Mat3
makeRotationZ3 angle =
  let c = Math.cos angle
      s = Math.sin angle
  in Mat3
    c   (negate s) 0.0
    s   c          0.0
    0.0 0.0        1.0

-- | Scale matrix
-- | Proof reference: Mat3.lean makeScale, det_makeScale
makeScale3 :: Number -> Number -> Number -> Mat3
makeScale3 sx sy sz = mat3Diagonal sx sy sz

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get element at row, column (0-indexed)
-- | Returns 0.0 for out-of-bounds indices
getElementMat3 :: Int -> Int -> Mat3 -> Number
getElementMat3 row col (Mat3 m00 m01 m02 m10 m11 m12 m20 m21 m22) =
  case row of
    0 -> case col of
      0 -> m00
      1 -> m01
      2 -> m02
      _ -> 0.0
    1 -> case col of
      0 -> m10
      1 -> m11
      2 -> m12
      _ -> 0.0
    2 -> case col of
      0 -> m20
      1 -> m21
      2 -> m22
      _ -> 0.0
    _ -> 0.0

-- | Get row as Vec3
getRowMat3 :: Int -> Mat3 -> Vec3 Number
getRowMat3 row (Mat3 m00 m01 m02 m10 m11 m12 m20 m21 m22) =
  case row of
    0 -> vec3 m00 m01 m02
    1 -> vec3 m10 m11 m12
    2 -> vec3 m20 m21 m22
    _ -> vec3 0.0 0.0 0.0

-- | Get column as Vec3
getColumnMat3 :: Int -> Mat3 -> Vec3 Number
getColumnMat3 col (Mat3 m00 m01 m02 m10 m11 m12 m20 m21 m22) =
  case col of
    0 -> vec3 m00 m10 m20
    1 -> vec3 m01 m11 m21
    2 -> vec3 m02 m12 m22
    _ -> vec3 0.0 0.0 0.0
