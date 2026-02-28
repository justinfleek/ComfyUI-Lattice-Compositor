-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // gpu // webgpu // scene3d // geometry // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Core types and utility functions for mesh generation.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Scene3D.Geometry.Core
  ( -- Mesh data type
    MeshData
  , emptyMeshData
    -- Utility functions
  , combineMeshData
  , combineTwoMeshes
  , generateGridIndices
  , clampNumber
  , normalizeVec3
    -- Constants
  , pi
  , degToRad
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Nothing))
import Hydrogen.Math.Core (sqrt)
import Hydrogen.Schema.Dimension.Vector.Vec2 (Vec2)
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3, getX3, getY3, getZ3)
import Hydrogen.Schema.Dimension.Vector.Vec4 (Vec4)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- MESH DATA TYPE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generated mesh data. Pure vertex/index arrays ready for GPU upload.
-- |
-- | INVARIANTS (matching Lean proofs):
-- | - Array.length positions == vertex count from proof
-- | - Array.length indices == index count from proof
-- | - Array.length indices `mod` 3 == 0 (always triangles)
-- | - All normals have length ≈ 1.0
type MeshData =
  { positions :: Array (Vec3 Number)
  , normals :: Array (Vec3 Number)
  , uvs :: Array (Vec2 Number)
  , indices :: Array Int
  , tangents :: Maybe (Array (Vec4 Number))
  }

-- | Empty mesh data.
emptyMeshData :: MeshData
emptyMeshData =
  { positions: []
  , normals: []
  , uvs: []
  , indices: []
  , tangents: Nothing
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- UTILITY FUNCTIONS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate grid indices for a subdivided quad.
generateGridIndices :: Int -> Int -> Int -> Array Int
generateGridIndices widthSegs heightSegs stride = do
  iy <- Array.range 0 (heightSegs - 1)
  ix <- Array.range 0 (widthSegs - 1)
  let
    a = iy * stride + ix
    b = iy * stride + ix + 1
    c = (iy + 1) * stride + ix + 1
    d = (iy + 1) * stride + ix
  [a, b, d, b, c, d]

-- | Combine multiple mesh data into one.
combineMeshData :: Array MeshData -> MeshData
combineMeshData = foldl combineTwoMeshes emptyMeshData

-- | Combine two mesh data, offsetting indices of the second.
combineTwoMeshes :: MeshData -> MeshData -> MeshData
combineTwoMeshes a b =
  let
    offset = Array.length a.positions
    offsetIndices = map (_ + offset) b.indices
  in
    { positions: a.positions <> b.positions
    , normals: a.normals <> b.normals
    , uvs: a.uvs <> b.uvs
    , indices: a.indices <> offsetIndices
    , tangents: Nothing
    }

-- | Clamp a number to a range.
clampNumber :: Number -> Number -> Number -> Number
clampNumber minVal maxVal x
  | x < minVal = minVal
  | x > maxVal = maxVal
  | otherwise = x

-- | Normalize a Vec3 to unit length. Returns zero vector if input is zero.
normalizeVec3 :: Vec3 Number -> Vec3 Number
normalizeVec3 v =
  let
    x = getX3 v
    y = getY3 v
    z = getZ3 v
    len = sqrt (x * x + y * y + z * z)
  in
    if len > 0.0
      then vec3 (x / len) (y / len) (z / len)
      else vec3 0.0 0.0 0.0

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- CONSTANTS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pi :: Number
pi = 3.141592653589793

degToRad :: Number
degToRad = pi / 180.0
