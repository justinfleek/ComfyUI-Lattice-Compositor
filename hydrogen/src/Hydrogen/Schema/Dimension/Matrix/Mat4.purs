-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // dimension // matrix // mat4
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 4x4 Matrix type — THE critical type for 3D graphics.
-- |
-- | ## Proof References
-- | All operations correspond to proven theorems in `proofs/Hydrogen/Math/Mat4.lean`:
-- | - mul_assoc: Matrix multiplication is associative
-- | - mul_identity_left/right: I × A = A × I = A
-- | - transpose_involutive: (Aᵀ)ᵀ = A
-- | - transpose_mul: (AB)ᵀ = BᵀAᵀ
-- | - det_identity: det(I) = 1
-- | - det_mul: det(AB) = det(A) × det(B)
-- |
-- | ## Applications
-- | - Model matrices (object placement)
-- | - View matrices (camera)
-- | - Projection matrices (perspective/ortho)
-- | - MVP = Projection × View × Model
-- |
-- | ## Storage Order
-- | Column-major (matching WebGL/WebGPU conventions):
-- | | m00 m10 m20 m30 |
-- | | m01 m11 m21 m31 |
-- | | m02 m12 m22 m32 |
-- | | m03 m13 m23 m33 |
-- |
-- | Column vectors:
-- | - col0 = (m00, m01, m02, m03) — X basis
-- | - col1 = (m10, m11, m12, m13) — Y basis
-- | - col2 = (m20, m21, m22, m23) — Z basis
-- | - col3 = (m30, m31, m32, m33) — Translation

module Hydrogen.Schema.Dimension.Matrix.Mat4
  ( -- * Type
    Mat4(Mat4)
  
  -- * Constructors
  , mat4
  , mat4Identity
  , mat4Zero
  , mat4FromColumns
  , mat4FromRows
  
  -- * Basic Operations
  , addMat4
  , subtractMat4
  , scaleMat4
  , negateMat4
  , transposeMat4
  
  -- * Matrix Multiplication
  , mulMat4
  , mulVec4Mat4
  , mulPointMat4
  , mulDirectionMat4
  
  -- * Determinant and Inverse
  , detMat4
  , isInvertibleMat4
  , invertMat4
  
  -- * Transform Constructors
  , makeTranslation4
  , makeScale4
  , makeRotationX4
  , makeRotationY4
  , makeRotationZ4
  
  -- * Projection Matrices
  , makePerspective
  , makeOrthographic
  , makeLookAt
  
  -- * Accessors
  , getElementMat4
  , getColumnMat4
  , getTranslation4
  , setTranslation4
  
  -- * Conversion
  , toArray16
  , fromArray16
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
  , (&&)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3(Vec3), vec3, normalizeVec3, crossVec3, subtractVec3, dotVec3)
import Hydrogen.Schema.Dimension.Vector.Vec4 (Vec4(Vec4), vec4)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | 4×4 matrix stored in column-major order (matching WebGL/WebGPU)
-- | 
-- | Memory layout as 16 consecutive numbers (column by column):
-- | [m00, m01, m02, m03, m10, m11, m12, m13, m20, m21, m22, m23, m30, m31, m32, m33]
data Mat4 = Mat4
  -- Column 0
  Number Number Number Number
  -- Column 1
  Number Number Number Number
  -- Column 2
  Number Number Number Number
  -- Column 3
  Number Number Number Number

derive instance eqMat4 :: Eq Mat4

instance showMat4 :: Show Mat4 where
  show (Mat4 m00 m01 m02 m03 m10 m11 m12 m13 m20 m21 m22 m23 m30 m31 m32 m33) =
    "Mat4(\n  " 
      <> show m00 <> ", " <> show m10 <> ", " <> show m20 <> ", " <> show m30 <> "\n  "
      <> show m01 <> ", " <> show m11 <> ", " <> show m21 <> ", " <> show m31 <> "\n  "
      <> show m02 <> ", " <> show m12 <> ", " <> show m22 <> ", " <> show m32 <> "\n  "
      <> show m03 <> ", " <> show m13 <> ", " <> show m23 <> ", " <> show m33 <> "\n)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a 4x4 matrix from elements (column-major order)
mat4 
  :: Number -> Number -> Number -> Number  -- Column 0
  -> Number -> Number -> Number -> Number  -- Column 1
  -> Number -> Number -> Number -> Number  -- Column 2
  -> Number -> Number -> Number -> Number  -- Column 3
  -> Mat4
mat4 = Mat4

-- | Identity matrix
-- | Proof reference: Mat4.lean identity, mul_identity_left, mul_identity_right
mat4Identity :: Mat4
mat4Identity = Mat4
  1.0 0.0 0.0 0.0
  0.0 1.0 0.0 0.0
  0.0 0.0 1.0 0.0
  0.0 0.0 0.0 1.0

-- | Zero matrix
-- | Proof reference: Mat4.lean zero, mul_zero_left, mul_zero_right
mat4Zero :: Mat4
mat4Zero = Mat4
  0.0 0.0 0.0 0.0
  0.0 0.0 0.0 0.0
  0.0 0.0 0.0 0.0
  0.0 0.0 0.0 0.0

-- | Create matrix from 4 column vectors
mat4FromColumns :: Vec4 Number -> Vec4 Number -> Vec4 Number -> Vec4 Number -> Mat4
mat4FromColumns (Vec4 c0x c0y c0z c0w) (Vec4 c1x c1y c1z c1w)
                (Vec4 c2x c2y c2z c2w) (Vec4 c3x c3y c3z c3w) =
  Mat4 c0x c0y c0z c0w c1x c1y c1z c1w c2x c2y c2z c2w c3x c3y c3z c3w

-- | Create matrix from 4 row vectors
mat4FromRows :: Vec4 Number -> Vec4 Number -> Vec4 Number -> Vec4 Number -> Mat4
mat4FromRows (Vec4 r0x r0y r0z r0w) (Vec4 r1x r1y r1z r1w)
             (Vec4 r2x r2y r2z r2w) (Vec4 r3x r3y r3z r3w) =
  Mat4 r0x r1x r2x r3x r0y r1y r2y r3y r0z r1z r2z r3z r0w r1w r2w r3w

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // basic operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Matrix addition
addMat4 :: Mat4 -> Mat4 -> Mat4
addMat4 (Mat4 a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33)
        (Mat4 b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33) = Mat4
  (a00 + b00) (a01 + b01) (a02 + b02) (a03 + b03)
  (a10 + b10) (a11 + b11) (a12 + b12) (a13 + b13)
  (a20 + b20) (a21 + b21) (a22 + b22) (a23 + b23)
  (a30 + b30) (a31 + b31) (a32 + b32) (a33 + b33)

-- | Matrix subtraction
subtractMat4 :: Mat4 -> Mat4 -> Mat4
subtractMat4 (Mat4 a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33)
             (Mat4 b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33) = Mat4
  (a00 - b00) (a01 - b01) (a02 - b02) (a03 - b03)
  (a10 - b10) (a11 - b11) (a12 - b12) (a13 - b13)
  (a20 - b20) (a21 - b21) (a22 - b22) (a23 - b23)
  (a30 - b30) (a31 - b31) (a32 - b32) (a33 - b33)

-- | Scalar multiplication
-- | Proof reference: Mat4.lean scale, scale_mul_left, scale_mul_right
scaleMat4 :: Number -> Mat4 -> Mat4
scaleMat4 s (Mat4 m00 m01 m02 m03 m10 m11 m12 m13 m20 m21 m22 m23 m30 m31 m32 m33) = Mat4
  (s * m00) (s * m01) (s * m02) (s * m03)
  (s * m10) (s * m11) (s * m12) (s * m13)
  (s * m20) (s * m21) (s * m22) (s * m23)
  (s * m30) (s * m31) (s * m32) (s * m33)

-- | Negation
negateMat4 :: Mat4 -> Mat4
negateMat4 (Mat4 m00 m01 m02 m03 m10 m11 m12 m13 m20 m21 m22 m23 m30 m31 m32 m33) = Mat4
  (negate m00) (negate m01) (negate m02) (negate m03)
  (negate m10) (negate m11) (negate m12) (negate m13)
  (negate m20) (negate m21) (negate m22) (negate m23)
  (negate m30) (negate m31) (negate m32) (negate m33)

-- | Matrix transpose
-- | Proof reference: Mat4.lean transpose, transpose_involutive, transpose_mul
transposeMat4 :: Mat4 -> Mat4
transposeMat4 (Mat4 m00 m01 m02 m03 m10 m11 m12 m13 m20 m21 m22 m23 m30 m31 m32 m33) = Mat4
  m00 m10 m20 m30
  m01 m11 m21 m31
  m02 m12 m22 m32
  m03 m13 m23 m33

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // matrix multiplication
-- ═════════════════════════════════════════════════════════════════════════════

-- | Matrix multiplication: C = A × B
-- | Proof reference: Mat4.lean mul, mul_assoc
mulMat4 :: Mat4 -> Mat4 -> Mat4
mulMat4 (Mat4 a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33)
        (Mat4 b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33) =
  let
    -- Result column 0
    r00 = a00 * b00 + a10 * b01 + a20 * b02 + a30 * b03
    r01 = a01 * b00 + a11 * b01 + a21 * b02 + a31 * b03
    r02 = a02 * b00 + a12 * b01 + a22 * b02 + a32 * b03
    r03 = a03 * b00 + a13 * b01 + a23 * b02 + a33 * b03
    -- Result column 1
    r10 = a00 * b10 + a10 * b11 + a20 * b12 + a30 * b13
    r11 = a01 * b10 + a11 * b11 + a21 * b12 + a31 * b13
    r12 = a02 * b10 + a12 * b11 + a22 * b12 + a32 * b13
    r13 = a03 * b10 + a13 * b11 + a23 * b12 + a33 * b13
    -- Result column 2
    r20 = a00 * b20 + a10 * b21 + a20 * b22 + a30 * b23
    r21 = a01 * b20 + a11 * b21 + a21 * b22 + a31 * b23
    r22 = a02 * b20 + a12 * b21 + a22 * b22 + a32 * b23
    r23 = a03 * b20 + a13 * b21 + a23 * b22 + a33 * b23
    -- Result column 3
    r30 = a00 * b30 + a10 * b31 + a20 * b32 + a30 * b33
    r31 = a01 * b30 + a11 * b31 + a21 * b32 + a31 * b33
    r32 = a02 * b30 + a12 * b31 + a22 * b32 + a32 * b33
    r33 = a03 * b30 + a13 * b31 + a23 * b32 + a33 * b33
  in Mat4 r00 r01 r02 r03 r10 r11 r12 r13 r20 r21 r22 r23 r30 r31 r32 r33

-- | Transform a Vec4 by matrix
mulVec4Mat4 :: Mat4 -> Vec4 Number -> Vec4 Number
mulVec4Mat4 (Mat4 m00 m01 m02 m03 m10 m11 m12 m13 m20 m21 m22 m23 m30 m31 m32 m33)
            (Vec4 x y z w) = vec4
  (m00 * x + m10 * y + m20 * z + m30 * w)
  (m01 * x + m11 * y + m21 * z + m31 * w)
  (m02 * x + m12 * y + m22 * z + m32 * w)
  (m03 * x + m13 * y + m23 * z + m33 * w)

-- | Transform a point (w=1, affected by translation)
mulPointMat4 :: Mat4 -> Vec3 Number -> Vec3 Number
mulPointMat4 (Mat4 m00 m01 m02 _ m10 m11 m12 _ m20 m21 m22 _ m30 m31 m32 _)
             (Vec3 x y z) = vec3
  (m00 * x + m10 * y + m20 * z + m30)
  (m01 * x + m11 * y + m21 * z + m31)
  (m02 * x + m12 * y + m22 * z + m32)

-- | Transform a direction (w=0, NOT affected by translation)
mulDirectionMat4 :: Mat4 -> Vec3 Number -> Vec3 Number
mulDirectionMat4 (Mat4 m00 m01 m02 _ m10 m11 m12 _ m20 m21 m22 _ _ _ _ _)
                 (Vec3 x y z) = vec3
  (m00 * x + m10 * y + m20 * z)
  (m01 * x + m11 * y + m21 * z)
  (m02 * x + m12 * y + m22 * z)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // determinant
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3×3 determinant helper (for cofactor expansion)
det3 :: Number -> Number -> Number -> Number -> Number -> Number -> Number -> Number -> Number -> Number
det3 a b c d e f g h i =
  a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)

-- | Determinant using Laplace expansion along first row
-- | Proof reference: Mat4.lean det, det_identity, det_mul, det_transpose
detMat4 :: Mat4 -> Number
detMat4 (Mat4 m00 m01 m02 m03 m10 m11 m12 m13 m20 m21 m22 m23 m30 m31 m32 m33) =
  let
    c00 = det3 m11 m21 m31 m12 m22 m32 m13 m23 m33
    c10 = det3 m01 m21 m31 m02 m22 m32 m03 m23 m33
    c20 = det3 m01 m11 m31 m02 m12 m32 m03 m13 m33
    c30 = det3 m01 m11 m21 m02 m12 m22 m03 m13 m23
  in m00 * c00 - m10 * c10 + m20 * c20 - m30 * c30

-- | Check if matrix is invertible (determinant non-zero)
-- | Proof reference: Mat4.lean IsInvertible
isInvertibleMat4 :: Mat4 -> Boolean
isInvertibleMat4 m = detMat4 m /= 0.0

-- | Matrix inverse using adjugate/determinant method
-- | Returns Nothing if matrix is singular (det = 0)
-- | Proof reference: Mat4.lean inv, inv_mul_self, mul_inv_self
-- |
-- | Formula: A⁻¹ = adj(A) / det(A)
-- | where adj(A) is the adjugate (transpose of cofactor matrix)
invertMat4 :: Mat4 -> Maybe Mat4
invertMat4 (Mat4 m00 m01 m02 m03 m10 m11 m12 m13 m20 m21 m22 m23 m30 m31 m32 m33) =
  let
    -- Compute 2x2 determinants for cofactors
    s0 = m00 * m11 - m10 * m01
    s1 = m00 * m12 - m10 * m02
    s2 = m00 * m13 - m10 * m03
    s3 = m01 * m12 - m11 * m02
    s4 = m01 * m13 - m11 * m03
    s5 = m02 * m13 - m12 * m03
    c5 = m22 * m33 - m32 * m23
    c4 = m21 * m33 - m31 * m23
    c3 = m21 * m32 - m31 * m22
    c2 = m20 * m33 - m30 * m23
    c1 = m20 * m32 - m30 * m22
    c0 = m20 * m31 - m30 * m21
    
    -- Determinant via Laplace expansion
    det = s0 * c5 - s1 * c4 + s2 * c3 + s3 * c2 - s4 * c1 + s5 * c0
  in
    if det == 0.0
      then Nothing
      else
        let
          invDet = 1.0 / det
          -- Adjugate matrix elements (transposed cofactors)
          r00 = ( m11 * c5 - m12 * c4 + m13 * c3) * invDet
          r01 = (negate m01 * c5 + m02 * c4 - m03 * c3) * invDet
          r02 = ( m31 * s5 - m32 * s4 + m33 * s3) * invDet
          r03 = (negate m21 * s5 + m22 * s4 - m23 * s3) * invDet
          r10 = (negate m10 * c5 + m12 * c2 - m13 * c1) * invDet
          r11 = ( m00 * c5 - m02 * c2 + m03 * c1) * invDet
          r12 = (negate m30 * s5 + m32 * s2 - m33 * s1) * invDet
          r13 = ( m20 * s5 - m22 * s2 + m23 * s1) * invDet
          r20 = ( m10 * c4 - m11 * c2 + m13 * c0) * invDet
          r21 = (negate m00 * c4 + m01 * c2 - m03 * c0) * invDet
          r22 = ( m30 * s4 - m31 * s2 + m33 * s0) * invDet
          r23 = (negate m20 * s4 + m21 * s2 - m23 * s0) * invDet
          r30 = (negate m10 * c3 + m11 * c1 - m12 * c0) * invDet
          r31 = ( m00 * c3 - m01 * c1 + m02 * c0) * invDet
          r32 = (negate m30 * s3 + m31 * s1 - m32 * s0) * invDet
          r33 = ( m20 * s3 - m21 * s1 + m22 * s0) * invDet
        in Just (Mat4 r00 r01 r02 r03 r10 r11 r12 r13 r20 r21 r22 r23 r30 r31 r32 r33)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // transform constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translation matrix
-- | Proof reference: Mat4.lean makeTranslation, makeTranslation_zero, makeTranslation_mul
makeTranslation4 :: Number -> Number -> Number -> Mat4
makeTranslation4 tx ty tz = Mat4
  1.0 0.0 0.0 0.0
  0.0 1.0 0.0 0.0
  0.0 0.0 1.0 0.0
  tx  ty  tz  1.0

-- | Scale matrix
-- | Proof reference: Mat4.lean makeScale, makeScale_one, makeScale_mul
makeScale4 :: Number -> Number -> Number -> Mat4
makeScale4 sx sy sz = Mat4
  sx  0.0 0.0 0.0
  0.0 sy  0.0 0.0
  0.0 0.0 sz  0.0
  0.0 0.0 0.0 1.0

-- | Rotation around X axis (radians)
-- | Proof reference: Mat4.lean makeRotationX, det_makeRotationX, makeRotationX_zero
makeRotationX4 :: Number -> Mat4
makeRotationX4 angle =
  let c = Math.cos angle
      s = Math.sin angle
  in Mat4
    1.0 0.0 0.0 0.0
    0.0 c   s   0.0
    0.0 (negate s) c 0.0
    0.0 0.0 0.0 1.0

-- | Rotation around Y axis (radians)
-- | Proof reference: Mat4.lean makeRotationY, det_makeRotationY, makeRotationY_zero
makeRotationY4 :: Number -> Mat4
makeRotationY4 angle =
  let c = Math.cos angle
      s = Math.sin angle
  in Mat4
    c   0.0 (negate s) 0.0
    0.0 1.0 0.0        0.0
    s   0.0 c          0.0
    0.0 0.0 0.0        1.0

-- | Rotation around Z axis (radians)
-- | Proof reference: Mat4.lean makeRotationZ, det_makeRotationZ, makeRotationZ_zero
makeRotationZ4 :: Number -> Mat4
makeRotationZ4 angle =
  let c = Math.cos angle
      s = Math.sin angle
  in Mat4
    c   s   0.0 0.0
    (negate s) c 0.0 0.0
    0.0 0.0 1.0 0.0
    0.0 0.0 0.0 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // projection matrices
-- ═════════════════════════════════════════════════════════════════════════════

-- | Perspective projection matrix
-- | fov: vertical field of view in radians
-- | aspect: width/height ratio
-- | near: near clipping plane
-- | far: far clipping plane
makePerspective :: Number -> Number -> Number -> Number -> Mat4
makePerspective fov aspect near far =
  let
    f = 1.0 / Math.tan (fov / 2.0)
    nf = 1.0 / (near - far)
  in Mat4
    (f / aspect) 0.0 0.0                    0.0
    0.0          f   0.0                    0.0
    0.0          0.0 ((far + near) * nf)    (negate 1.0)
    0.0          0.0 (2.0 * far * near * nf) 0.0

-- | Orthographic projection matrix
makeOrthographic :: Number -> Number -> Number -> Number -> Number -> Number -> Mat4
makeOrthographic left right bottom top near far =
  let
    lr = 1.0 / (left - right)
    bt = 1.0 / (bottom - top)
    nf = 1.0 / (near - far)
  in Mat4
    (negate 2.0 * lr)        0.0                      0.0             0.0
    0.0                      (negate 2.0 * bt)        0.0             0.0
    0.0                      0.0                      (2.0 * nf)      0.0
    ((left + right) * lr)    ((top + bottom) * bt)    ((far + near) * nf) 1.0

-- | Look-at view matrix
-- | eye: camera position
-- | target: point to look at
-- | up: world up vector
makeLookAt :: Vec3 Number -> Vec3 Number -> Vec3 Number -> Mat4
makeLookAt eye target up =
  let
    zAxis = normalizeVec3 (subtractVec3 eye target)
    xAxis = normalizeVec3 (crossVec3 up zAxis)
    yAxis = crossVec3 zAxis xAxis
    Vec3 xx xy xz = xAxis
    Vec3 yx yy yz = yAxis
    Vec3 zx zy zz = zAxis
    dx = negate (dotVec3 xAxis eye)
    dy = negate (dotVec3 yAxis eye)
    dz = negate (dotVec3 zAxis eye)
  in Mat4
    xx yx zx 0.0
    xy yy zy 0.0
    xz yz zz 0.0
    dx dy dz 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get element at column, row (0-indexed)
getElementMat4 :: Int -> Int -> Mat4 -> Number
getElementMat4 col row (Mat4 m00 m01 m02 m03 m10 m11 m12 m13 m20 m21 m22 m23 m30 m31 m32 m33) =
  case col of
    0 -> case row of
      0 -> m00
      1 -> m01
      2 -> m02
      3 -> m03
      _ -> 0.0
    1 -> case row of
      0 -> m10
      1 -> m11
      2 -> m12
      3 -> m13
      _ -> 0.0
    2 -> case row of
      0 -> m20
      1 -> m21
      2 -> m22
      3 -> m23
      _ -> 0.0
    3 -> case row of
      0 -> m30
      1 -> m31
      2 -> m32
      3 -> m33
      _ -> 0.0
    _ -> 0.0

-- | Get column as Vec4
getColumnMat4 :: Int -> Mat4 -> Vec4 Number
getColumnMat4 col (Mat4 m00 m01 m02 m03 m10 m11 m12 m13 m20 m21 m22 m23 m30 m31 m32 m33) =
  case col of
    0 -> vec4 m00 m01 m02 m03
    1 -> vec4 m10 m11 m12 m13
    2 -> vec4 m20 m21 m22 m23
    3 -> vec4 m30 m31 m32 m33
    _ -> vec4 0.0 0.0 0.0 0.0

-- | Get translation component (column 3, rows 0-2)
getTranslation4 :: Mat4 -> Vec3 Number
getTranslation4 (Mat4 _ _ _ _ _ _ _ _ _ _ _ _ m30 m31 m32 _) = vec3 m30 m31 m32

-- | Set translation component
setTranslation4 :: Vec3 Number -> Mat4 -> Mat4
setTranslation4 (Vec3 tx ty tz) (Mat4 m00 m01 m02 m03 m10 m11 m12 m13 m20 m21 m22 m23 _ _ _ m33) =
  Mat4 m00 m01 m02 m03 m10 m11 m12 m13 m20 m21 m22 m23 tx ty tz m33

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to 16-element array (column-major, for WebGL)
toArray16 :: Mat4 -> Array Number
toArray16 (Mat4 m00 m01 m02 m03 m10 m11 m12 m13 m20 m21 m22 m23 m30 m31 m32 m33) =
  [m00, m01, m02, m03, m10, m11, m12, m13, m20, m21, m22, m23, m30, m31, m32, m33]

-- | Create from 16-element array (column-major)
-- | Returns Nothing if array has wrong length
fromArray16 :: Array Number -> Maybe Mat4
fromArray16 arr = case arr of
  [m00, m01, m02, m03, m10, m11, m12, m13, m20, m21, m22, m23, m30, m31, m32, m33] ->
    Just (Mat4 m00 m01 m02 m03 m10 m11 m12 m13 m20 m21 m22 m23 m30 m31 m32 m33)
  _ -> Nothing
