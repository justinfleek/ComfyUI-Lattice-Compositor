-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--               // hydrogen // gpu // webgpu // scene3d // geometry // platonic
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Platonic solid generators: Icosahedron, Octahedron, Tetrahedron, Dodecahedron.
-- With subdivision support for geodesic sphere approximations.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Scene3D.Geometry.Platonic
  ( generateIcosahedron
  , generateOctahedron
  , generateTetrahedron
  , generateDodecahedron
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.GPU.Scene3D.Mesh
  ( DodecahedronMeshParams
  , IcosahedronMeshParams
  , OctahedronMeshParams
  , TetrahedronMeshParams
  )
import Hydrogen.GPU.WebGPU.Scene3D.Geometry.Core
  ( MeshData
  , clampNumber
  , normalizeVec3
  , pi
  )
import Hydrogen.Math.Core (sqrt)
import Hydrogen.Schema.Dimension.Physical.SI (unwrapMeter)
import Hydrogen.Schema.Dimension.Vector.Vec2 (Vec2, vec2)
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3, scaleVec3, getX3, getY3, getZ3)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- PLATONIC SOLIDS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate an icosahedron (20-faced regular polyhedron).
-- |
-- | The icosahedron is defined by 12 vertices and 20 triangular faces.
-- | Detail level controls subdivision: 0 = 20 triangles, n = 20 × 4^n triangles.
-- |
-- | Golden ratio: φ = (1 + √5) / 2 ≈ 1.618
-- | Vertices lie at (0, ±1, ±φ) and cyclic permutations.
generateIcosahedron :: IcosahedronMeshParams -> MeshData
generateIcosahedron params =
  let
    radius = unwrapMeter params.radius
    detail = params.detail
    
    -- Golden ratio
    phi = (1.0 + sqrt 5.0) / 2.0
    
    -- Normalize to unit sphere, then scale
    len = sqrt (1.0 + phi * phi)
    a = 1.0 / len
    b = phi / len
    
    -- 12 vertices of icosahedron (normalized, then scaled)
    basePositions =
      [ vec3 (-a) b 0.0, vec3 a b 0.0, vec3 (-a) (-b) 0.0, vec3 a (-b) 0.0
      , vec3 0.0 (-a) b, vec3 0.0 a b, vec3 0.0 (-a) (-b), vec3 0.0 a (-b)
      , vec3 b 0.0 (-a), vec3 b 0.0 a, vec3 (-b) 0.0 (-a), vec3 (-b) 0.0 a
      ]
    
    -- 20 triangular faces (CCW winding, outward normals)
    baseFaces =
      [ [0, 11, 5], [0, 5, 1], [0, 1, 7], [0, 7, 10], [0, 10, 11]
      , [1, 5, 9], [5, 11, 4], [11, 10, 2], [10, 7, 6], [7, 1, 8]
      , [3, 9, 4], [3, 4, 2], [3, 2, 6], [3, 6, 8], [3, 8, 9]
      , [4, 9, 5], [2, 4, 11], [6, 2, 10], [8, 6, 7], [9, 8, 1]
      ]
    
    -- Subdivide if detail > 0
    subdivided = subdividePolyhedron basePositions baseFaces detail
    
    -- Scale to radius and compute normals
    scaledPositions = map (scaleVec3 radius) subdivided.positions
    
    -- For a sphere-like polyhedron, normal = normalized position
    computedNormals = map normalizeVec3 subdivided.positions
    
    -- Simple UV mapping: spherical projection
    computedUvs = map sphericalUV subdivided.positions
  in
    { positions: scaledPositions
    , normals: computedNormals
    , uvs: computedUvs
    , indices: subdivided.indices
    , tangents: Nothing
    }

-- | Generate an octahedron (8-faced regular polyhedron).
-- |
-- | The octahedron has 6 vertices at (±1, 0, 0), (0, ±1, 0), (0, 0, ±1)
-- | and 8 triangular faces.
generateOctahedron :: OctahedronMeshParams -> MeshData
generateOctahedron params =
  let
    radius = unwrapMeter params.radius
    detail = params.detail
    
    -- 6 vertices of octahedron (unit)
    basePositions =
      [ vec3 1.0 0.0 0.0, vec3 (-1.0) 0.0 0.0
      , vec3 0.0 1.0 0.0, vec3 0.0 (-1.0) 0.0
      , vec3 0.0 0.0 1.0, vec3 0.0 0.0 (-1.0)
      ]
    
    -- 8 triangular faces (CCW winding)
    baseFaces =
      [ [0, 2, 4], [0, 4, 3], [0, 3, 5], [0, 5, 2]
      , [1, 2, 5], [1, 5, 3], [1, 3, 4], [1, 4, 2]
      ]
    
    subdivided = subdividePolyhedron basePositions baseFaces detail
    scaledPositions = map (scaleVec3 radius) subdivided.positions
    computedNormals = map normalizeVec3 subdivided.positions
    computedUvs = map sphericalUV subdivided.positions
  in
    { positions: scaledPositions
    , normals: computedNormals
    , uvs: computedUvs
    , indices: subdivided.indices
    , tangents: Nothing
    }

-- | Generate a tetrahedron (4-faced regular polyhedron).
-- |
-- | The simplest Platonic solid with 4 vertices and 4 triangular faces.
generateTetrahedron :: TetrahedronMeshParams -> MeshData
generateTetrahedron params =
  let
    radius = unwrapMeter params.radius
    detail = params.detail
    
    -- 4 vertices of tetrahedron (inscribed in unit sphere)
    -- Using coordinates that place centroid at origin
    a = 1.0 / sqrt 3.0
    b = sqrt (2.0 / 3.0)
    c = sqrt (2.0 / 9.0)
    d = sqrt (8.0 / 9.0)
    
    basePositions =
      [ vec3 0.0 1.0 0.0
      , vec3 d (-a) 0.0
      , vec3 (-c) (-a) b
      , vec3 (-c) (-a) (-b)
      ]
    
    -- 4 triangular faces (CCW winding)
    baseFaces =
      [ [0, 1, 2], [0, 2, 3], [0, 3, 1], [1, 3, 2]
      ]
    
    subdivided = subdividePolyhedron basePositions baseFaces detail
    scaledPositions = map (scaleVec3 radius) subdivided.positions
    computedNormals = map normalizeVec3 subdivided.positions
    computedUvs = map sphericalUV subdivided.positions
  in
    { positions: scaledPositions
    , normals: computedNormals
    , uvs: computedUvs
    , indices: subdivided.indices
    , tangents: Nothing
    }

-- | Generate a dodecahedron (12-faced regular polyhedron).
-- |
-- | The dodecahedron has 20 vertices and 12 pentagonal faces.
-- | We triangulate each pentagon into 5 triangles (60 total).
generateDodecahedron :: DodecahedronMeshParams -> MeshData
generateDodecahedron params =
  let
    radius = unwrapMeter params.radius
    detail = params.detail
    
    -- Golden ratio
    phi = (1.0 + sqrt 5.0) / 2.0
    invPhi = 1.0 / phi
    
    -- 20 vertices of dodecahedron (normalized)
    -- Cube vertices: (±1, ±1, ±1)
    -- Rectangle vertices: (0, ±φ, ±1/φ), (±1/φ, 0, ±φ), (±φ, ±1/φ, 0)
    basePositions =
      [ -- Cube vertices (8)
        vec3 1.0 1.0 1.0, vec3 1.0 1.0 (-1.0), vec3 1.0 (-1.0) 1.0, vec3 1.0 (-1.0) (-1.0)
      , vec3 (-1.0) 1.0 1.0, vec3 (-1.0) 1.0 (-1.0), vec3 (-1.0) (-1.0) 1.0, vec3 (-1.0) (-1.0) (-1.0)
        -- Rectangle vertices (12)
      , vec3 0.0 phi invPhi, vec3 0.0 phi (-invPhi), vec3 0.0 (-phi) invPhi, vec3 0.0 (-phi) (-invPhi)
      , vec3 invPhi 0.0 phi, vec3 (-invPhi) 0.0 phi, vec3 invPhi 0.0 (-phi), vec3 (-invPhi) 0.0 (-phi)
      , vec3 phi invPhi 0.0, vec3 phi (-invPhi) 0.0, vec3 (-phi) invPhi 0.0, vec3 (-phi) (-invPhi) 0.0
      ]
    
    -- Normalize all positions to unit sphere
    normalizedPositions = map normalizeVec3 basePositions
    
    -- 12 pentagonal faces, each triangulated into 5 triangles (fan from center)
    -- We create a center vertex for each pentagon
    baseFaces =
      [ [0, 16, 1, 9, 8], [0, 8, 4, 13, 12], [0, 12, 2, 17, 16]
      , [1, 16, 17, 3, 14], [1, 14, 15, 5, 9], [2, 12, 13, 6, 10]
      , [2, 10, 11, 3, 17], [3, 11, 7, 15, 14], [4, 8, 9, 5, 18]
      , [4, 18, 19, 6, 13], [5, 15, 7, 19, 18], [6, 19, 7, 11, 10]
      ]
    
    -- Triangulate pentagons and apply subdivision
    triangulated = triangulatePentagons normalizedPositions baseFaces
    subdivided = subdividePolyhedron triangulated.positions triangulated.faces detail
    scaledPositions = map (scaleVec3 radius) subdivided.positions
    computedNormals = map normalizeVec3 subdivided.positions
    computedUvs = map sphericalUV subdivided.positions
  in
    { positions: scaledPositions
    , normals: computedNormals
    , uvs: computedUvs
    , indices: subdivided.indices
    , tangents: Nothing
    }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- POLYHEDRON HELPERS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Subdivide a polyhedron by splitting each triangle into 4.
-- |
-- | Each subdivision level multiplies triangle count by 4.
-- | Vertices are projected back to unit sphere.
subdividePolyhedron 
  :: Array (Vec3 Number) 
  -> Array (Array Int) 
  -> Int 
  -> { positions :: Array (Vec3 Number), indices :: Array Int }
subdividePolyhedron positions faces detail =
  if detail <= 0 then
    { positions
    , indices: Array.concatMap identity faces
    }
  else
    let
      subdivided = subdivideFaces positions faces
    in
      subdividePolyhedron subdivided.positions subdivided.faces (detail - 1)

-- | Single level of face subdivision.
subdivideFaces 
  :: Array (Vec3 Number) 
  -> Array (Array Int) 
  -> { positions :: Array (Vec3 Number), faces :: Array (Array Int) }
subdivideFaces positions faces =
  -- For each triangle, create 4 new triangles
  -- by adding midpoint vertices on each edge
  foldl subdivideSingleFace { positions, faces: [] } faces

-- | Subdivide a single triangular face.
subdivideSingleFace
  :: { positions :: Array (Vec3 Number), faces :: Array (Array Int) }
  -> Array Int
  -> { positions :: Array (Vec3 Number), faces :: Array (Array Int) }
subdivideSingleFace acc face =
  case face of
    [i0, i1, i2] ->
      let
        p0 = getVec3At acc.positions i0
        p1 = getVec3At acc.positions i1
        p2 = getVec3At acc.positions i2
        
        -- Midpoints (normalized to unit sphere)
        m01 = normalizeVec3 (midpoint p0 p1)
        m12 = normalizeVec3 (midpoint p1 p2)
        m20 = normalizeVec3 (midpoint p2 p0)
        
        -- Add new vertices
        baseIdx = Array.length acc.positions
        newPositions = acc.positions <> [m01, m12, m20]
        i01 = baseIdx
        i12 = baseIdx + 1
        i20 = baseIdx + 2
        
        -- 4 new triangles
        newFaces = acc.faces <> 
          [ [i0, i01, i20]
          , [i01, i1, i12]
          , [i20, i12, i2]
          , [i01, i12, i20]
          ]
      in
        { positions: newPositions, faces: newFaces }
    _ -> acc  -- Not a triangle, skip

-- | Triangulate pentagonal faces into triangles using fan method.
triangulatePentagons
  :: Array (Vec3 Number)
  -> Array (Array Int)
  -> { positions :: Array (Vec3 Number), faces :: Array (Array Int) }
triangulatePentagons positions pentagons =
  foldl triangulateSinglePentagon { positions, faces: [] } pentagons

-- | Triangulate a single pentagon by adding center vertex.
triangulateSinglePentagon
  :: { positions :: Array (Vec3 Number), faces :: Array (Array Int) }
  -> Array Int
  -> { positions :: Array (Vec3 Number), faces :: Array (Array Int) }
triangulateSinglePentagon acc pentagon =
  case pentagon of
    [i0, i1, i2, i3, i4] ->
      let
        p0 = getVec3At acc.positions i0
        p1 = getVec3At acc.positions i1
        p2 = getVec3At acc.positions i2
        p3 = getVec3At acc.positions i3
        p4 = getVec3At acc.positions i4
        
        -- Center of pentagon (average of vertices, then normalized)
        cx = (getX3 p0 + getX3 p1 + getX3 p2 + getX3 p3 + getX3 p4) / 5.0
        cy = (getY3 p0 + getY3 p1 + getY3 p2 + getY3 p3 + getY3 p4) / 5.0
        cz = (getZ3 p0 + getZ3 p1 + getZ3 p2 + getZ3 p3 + getZ3 p4) / 5.0
        center = normalizeVec3 (vec3 cx cy cz)
        
        centerIdx = Array.length acc.positions
        newPositions = acc.positions <> [center]
        
        -- 5 triangles from center to each edge
        newFaces = acc.faces <>
          [ [centerIdx, i0, i1]
          , [centerIdx, i1, i2]
          , [centerIdx, i2, i3]
          , [centerIdx, i3, i4]
          , [centerIdx, i4, i0]
          ]
      in
        { positions: newPositions, faces: newFaces }
    _ -> acc  -- Not a pentagon, skip

-- | Get Vec3 at index, or zero vector.
getVec3At :: Array (Vec3 Number) -> Int -> Vec3 Number
getVec3At arr i = case Array.index arr i of
  Just v -> v
  Nothing -> vec3 0.0 0.0 0.0

-- | Compute midpoint of two vectors.
midpoint :: Vec3 Number -> Vec3 Number -> Vec3 Number
midpoint a b = vec3 
  ((getX3 a + getX3 b) / 2.0)
  ((getY3 a + getY3 b) / 2.0)
  ((getZ3 a + getZ3 b) / 2.0)

-- | Spherical UV mapping from normalized position.
sphericalUV :: Vec3 Number -> Vec2 Number
sphericalUV v =
  let
    x = getX3 v
    y = getY3 v
    z = getZ3 v
    
    -- U: atan2(z, x) mapped to [0, 1]
    -- V: asin(y) mapped to [0, 1]
    u = 0.5 + atan2 z x / (2.0 * pi)
    vVal = 0.5 + asin (clampNumber (-1.0) 1.0 y) / pi
  in
    vec2 u vVal

-- | Arc tangent of y/x, handling quadrants.
atan2 :: Number -> Number -> Number
atan2 y x =
  let
    rawAtan = if x > 0.0 then atan (y / x)
              else if x < 0.0 && y >= 0.0 then atan (y / x) + pi
              else if x < 0.0 && y < 0.0 then atan (y / x) - pi
              else if x == 0.0 && y > 0.0 then pi / 2.0
              else if x == 0.0 && y < 0.0 then (-pi) / 2.0
              else 0.0  -- x == 0 && y == 0
  in
    rawAtan

-- | Arc sine function (Taylor series approximation).
asin :: Number -> Number
asin x =
  -- Polynomial approximation for asin in [-1, 1]
  -- asin(x) ≈ x + x³/6 + 3x⁵/40 + 15x⁷/336 for |x| < 1
  let
    x2 = x * x
    x3 = x2 * x
    x5 = x3 * x2
    x7 = x5 * x2
  in
    x + x3 / 6.0 + 3.0 * x5 / 40.0 + 15.0 * x7 / 336.0

-- | Arc tangent function (approximation).
atan :: Number -> Number
atan x =
  -- For |x| <= 1: atan(x) ≈ x - x³/3 + x⁵/5 - x⁷/7
  -- For |x| > 1: atan(x) = π/2 - atan(1/x) if x > 0
  if x > 1.0 then pi / 2.0 - atanSmall (1.0 / x)
  else if x < (-1.0) then (-pi) / 2.0 - atanSmall (1.0 / x)
  else atanSmall x
  where
    atanSmall :: Number -> Number
    atanSmall t =
      let
        t2 = t * t
        t3 = t2 * t
        t5 = t3 * t2
        t7 = t5 * t2
      in
        t - t3 / 3.0 + t5 / 5.0 - t7 / 7.0
