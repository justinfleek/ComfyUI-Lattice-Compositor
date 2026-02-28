-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // gpu // webgpu // scene3d // geometry // count
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Vertex and index count formulas matching Lean proofs.
-- See: proofs/Hydrogen/Geometry/Primitives.lean
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Scene3D.Geometry.Count
  ( planeVertexCount
  , planeIndexCount
  , boxVertexCount
  , boxIndexCount
  , sphereVertexCount
  , sphereIndexCount
  ) where

import Prelude

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- VERTEX/INDEX COUNTS (matching Lean proofs)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Plane vertex count.
-- | From Primitives.lean: vertexCount = (widthSegments + 1) * (heightSegments + 1)
planeVertexCount :: Int -> Int -> Int
planeVertexCount widthSegs heightSegs = (widthSegs + 1) * (heightSegs + 1)

-- | Plane index count.
-- | From Primitives.lean: indexCount = widthSegments * heightSegments * 6
planeIndexCount :: Int -> Int -> Int
planeIndexCount widthSegs heightSegs = widthSegs * heightSegs * 6

-- | Box vertex count.
-- | From Primitives.lean: 24 for unit box (4 vertices per face × 6 faces)
boxVertexCount :: Int -> Int -> Int -> Int
boxVertexCount widthSegs heightSegs depthSegs =
  2 * (widthSegs + 1) * (heightSegs + 1) +
  2 * (depthSegs + 1) * (heightSegs + 1) +
  2 * (widthSegs + 1) * (depthSegs + 1)

-- | Box index count.
-- | From Primitives.lean: 36 for unit box
boxIndexCount :: Int -> Int -> Int -> Int
boxIndexCount widthSegs heightSegs depthSegs =
  2 * widthSegs * heightSegs * 6 +
  2 * depthSegs * heightSegs * 6 +
  2 * widthSegs * depthSegs * 6

-- | Sphere vertex count.
-- | From Primitives.lean: (widthSegments + 1) * (heightSegments + 1)
sphereVertexCount :: Int -> Int -> Int
sphereVertexCount widthSegs heightSegs = (widthSegs + 1) * (heightSegs + 1)

-- | Sphere index count.
-- | From Primitives.lean: widthSegments * heightSegments * 6
sphereIndexCount :: Int -> Int -> Int
sphereIndexCount widthSegs heightSegs = widthSegs * heightSegs * 6
