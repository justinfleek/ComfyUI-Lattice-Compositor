-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // gpu // webgpu // scene3d // geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Procedural mesh generation. Pure functions that produce vertex data.
--
-- LEADER MODULE: Re-exports from submodules for API stability.
--
-- Submodules:
-- - Core: MeshData type, utility functions
-- - Count: Vertex/index count formulas (matching Lean proofs)
-- - Basic: Plane, Box generators
-- - Curved: Sphere, Cylinder, Cone, Circle, Ring, Torus, Capsule
-- - Platonic: Icosahedron, Octahedron, Tetrahedron, Dodecahedron
-- - Procedural: TorusKnot, Lathe
--
-- MATHEMATICAL FOUNDATIONS:
-- Vertex/index count formulas are proven correct in:
--   proofs/Hydrogen/Geometry/Primitives.lean
--
-- INVARIANTS:
-- - All normals are unit length
-- - All indices form valid triangles (counterclockwise winding)
-- - UV coordinates are in [0, 1] range
-- - Vertex counts match Lean proofs exactly
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Scene3D.Geometry
  ( -- Core types
    module Core
    -- Count functions
  , module Count
    -- Basic generators
  , module Basic
    -- Curved generators
  , module Curved
    -- Platonic solids
  , module Platonic
    -- Procedural generators
  , module Procedural
    -- Main dispatcher
  , generateMesh
  ) where

import Hydrogen.GPU.Scene3D.Mesh
  ( Mesh3D
      ( BoxMesh3D
      , SphereMesh3D
      , CylinderMesh3D
      , ConeMesh3D
      , PlaneMesh3D
      , TorusMesh3D
      , TorusKnotMesh3D
      , RingMesh3D
      , CircleMesh3D
      , CapsuleMesh3D
      , IcosahedronMesh3D
      , OctahedronMesh3D
      , TetrahedronMesh3D
      , DodecahedronMesh3D
      , LatheMesh3D
      , ExtrudeMesh3D
      , BufferGeometry3D
      )
  )

import Hydrogen.GPU.WebGPU.Scene3D.Geometry.Core
  ( MeshData
  , emptyMeshData
  , combineMeshData
  ) as Core

import Hydrogen.GPU.WebGPU.Scene3D.Geometry.Count
  ( planeVertexCount
  , planeIndexCount
  , boxVertexCount
  , boxIndexCount
  , sphereVertexCount
  , sphereIndexCount
  ) as Count

import Hydrogen.GPU.WebGPU.Scene3D.Geometry.Basic
  ( generatePlane
  , generateBox
  ) as Basic

import Hydrogen.GPU.WebGPU.Scene3D.Geometry.Curved
  ( generateSphere
  , generateCylinder
  , generateCone
  , generateCircle
  , generateRing
  , generateTorus
  , generateCapsule
  ) as Curved

import Hydrogen.GPU.WebGPU.Scene3D.Geometry.Platonic
  ( generateIcosahedron
  , generateOctahedron
  , generateTetrahedron
  , generateDodecahedron
  ) as Platonic

import Hydrogen.GPU.WebGPU.Scene3D.Geometry.Procedural
  ( generateTorusKnot
  , generateLathe
  ) as Procedural

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- MAIN GENERATOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate mesh data from any Mesh3D type.
generateMesh :: Mesh3D -> Core.MeshData
generateMesh = case _ of
  BoxMesh3D params -> Basic.generateBox params
  SphereMesh3D params -> Curved.generateSphere params
  CylinderMesh3D params -> Curved.generateCylinder params
  ConeMesh3D params -> Curved.generateCone params
  PlaneMesh3D params -> Basic.generatePlane params
  TorusMesh3D params -> Curved.generateTorus params
  RingMesh3D params -> Curved.generateRing params
  CircleMesh3D params -> Curved.generateCircle params
  CapsuleMesh3D params -> Curved.generateCapsule params
  -- Platonic solids
  IcosahedronMesh3D params -> Platonic.generateIcosahedron params
  OctahedronMesh3D params -> Platonic.generateOctahedron params
  TetrahedronMesh3D params -> Platonic.generateTetrahedron params
  DodecahedronMesh3D params -> Platonic.generateDodecahedron params
  -- Procedural
  TorusKnotMesh3D params -> Procedural.generateTorusKnot params
  LatheMesh3D params -> Procedural.generateLathe params
  -- Not yet implemented
  ExtrudeMesh3D _ -> Core.emptyMeshData
  BufferGeometry3D _ -> Core.emptyMeshData
