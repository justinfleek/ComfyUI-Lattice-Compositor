-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // gpu // scene3d
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Scene3D — Pure Data Description of 3D Scenes
-- |
-- | This is the **leader module** that re-exports all Scene3D sub-modules.
-- | Import this module to get the complete 3D scene vocabulary.
-- |
-- | ## Sub-Modules
-- | - `Scene3D.Position` — Position3D (picometer precision), Direction3D
-- | - `Scene3D.Camera` — Perspective and orthographic cameras
-- | - `Scene3D.Background` — Solid, gradient, and environment backgrounds
-- | - `Scene3D.Light` — Ambient, directional, point, spot, hemisphere lights
-- | - `Scene3D.Material` — Basic, standard PBR, physical PBR materials
-- | - `Scene3D.Mesh` — All geometry primitives and buffer geometry
-- | - `Scene3D.Transform` — Transform parameters and clip planes
-- | - `Scene3D.Grid` — GridScale (Planck to Parsec), Grid3D, Axes3D
-- | - `Scene3D.Core` — SceneCommand, Scene3D type, PickId, buffer operations
-- | - `Scene3D.Identity` — UUID5 deterministic identity for all types
-- |
-- | ## Design Principles
-- |
-- | 1. **Flat, not nested**: Arrays of commands, not scene graphs
-- | 2. **Immediate mode**: Each frame is a complete description
-- | 3. **Schema atoms only**: All parameters use bounded Schema types
-- | 4. **GPU-native**: Commands map directly to WebGL2/WebGPU operations
-- | 5. **Pick buffer ready**: Every interactive mesh carries a PickId
-- |
-- | ## Coordinate System
-- |
-- | Right-handed (OpenGL/WebGL convention):
-- | - X: positive to the right
-- | - Y: positive upward  
-- | - Z: positive toward the viewer (out of screen)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.GPU.Scene3D as S3D
-- |
-- | myScene :: S3D.Scene3D MyMsg
-- | myScene = S3D.emptyScene
-- |   # S3D.withCamera (S3D.perspectiveCamera cameraParams)
-- |   # S3D.withBackground (S3D.solidBackground backgroundColor)
-- |   # S3D.withLight (S3D.ambientLight3D ambientParams)
-- |   # S3D.withMesh meshParams
-- | ```

module Hydrogen.GPU.Scene3D
  ( -- * Re-exports from Position
    module Position
  
  -- * Re-exports from Camera
  , module Camera
  
  -- * Re-exports from Background
  , module Background
  
  -- * Re-exports from Light
  , module Light
  
  -- * Re-exports from Material
  , module Material
  
  -- * Re-exports from Mesh
  , module Mesh
  
  -- * Re-exports from Transform
  , module Transform
  
  -- * Re-exports from Grid
  , module Grid
  
  -- * Re-exports from Core
  , module Core
  
  -- * Re-exports from Identity
  , module Identity
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.GPU.Scene3D.Position
  ( Position3D(Position3D)
  , position3D
  , zeroPosition3D
  , getPositionX
  , getPositionY
  , getPositionZ
  , addPosition3D
  , translatePosition3D
  , positionToMeters
  , Direction3D(Direction3D)
  , direction3D
  , normalizeToDirection
  , directionX
  , directionY
  , directionZ
  , negativeX
  , negativeY
  , negativeZ
  ) as Position

import Hydrogen.GPU.Scene3D.Camera
  ( Camera3D
      ( PerspectiveCamera3D
      , OrthographicCamera3D
      )
  , PerspectiveCameraParams
  , perspectiveCamera
  , OrthographicCameraParams
  , orthographicCamera
  ) as Camera

import Hydrogen.GPU.Scene3D.Background
  ( Background3D
      ( SolidBackground
      , GradientBackground
      , EnvironmentBackground
      )
  , EnvironmentMap
  , solidBackground
  , gradientBackground
  ) as Background

import Hydrogen.GPU.Scene3D.Light
  ( Light3D
      ( AmbientLight3D
      , DirectionalLight3D
      , PointLight3D
      , SpotLight3D
      , HemisphereLight3D
      )
  , AmbientLightParams
  , ambientLight3D
  , DirectionalLightParams
  , directionalLight3D
  , PointLightParams
  , pointLight3D
  , SpotLightParams
  , spotLight3D
  , HemisphereLightParams
  , hemisphereLight3D
  ) as Light

import Hydrogen.GPU.Scene3D.Material
  ( Material3D
      ( BasicMaterial3D
      , StandardMaterial3D
      , PhysicalMaterial3D
      )
  , BasicMaterialParams
  , basicMaterial3D
  , StandardMaterialParams
  , standardMaterial3D
  , PhysicalMaterialParams
  , physicalMaterial3D
  ) as Material

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
  , BoxMeshParams
  , boxMesh3D
  , SphereMeshParams
  , sphereMesh3D
  , CylinderMeshParams
  , cylinderMesh3D
  , ConeMeshParams
  , coneMesh3D
  , PlaneMeshParams
  , planeMesh3D
  , TorusMeshParams
  , torusMesh3D
  , TorusKnotMeshParams
  , torusKnotMesh3D
  , RingMeshParams
  , ringMesh3D
  , CircleMeshParams
  , circleMesh3D
  , CapsuleMeshParams
  , capsuleMesh3D
  , IcosahedronMeshParams
  , icosahedronMesh3D
  , OctahedronMeshParams
  , octahedronMesh3D
  , TetrahedronMeshParams
  , tetrahedronMesh3D
  , DodecahedronMeshParams
  , dodecahedronMesh3D
  , LatheMeshParams
  , latheMesh3D
  , Point2DProfile
  , ExtrudeMeshParams
  , extrudeMesh3D
  , Shape2D
  , BufferGeometryParams
  , bufferGeometry3D
  , VertexAttribute
      ( PositionAttr
      , NormalAttr
      , UVAttr
      , ColorAttr
      , TangentAttr
      , CustomAttr
      )
  , AttributeData
  , IndexData
  , DrawGroup
  , MeshParams
  , PickId3D
  , pickId3D
  , unwrapPickId3D
  ) as Mesh

import Hydrogen.GPU.Scene3D.Transform
  ( Transform3DParams
  , transform3DParams
  , identityTransform3D
  , ClipPlane3D
  ) as Transform

import Hydrogen.GPU.Scene3D.Grid
  ( GridScale
      ( ScalePlanck
      , ScaleFemtometer
      , ScalePicometer
      , ScaleAngstrom
      , ScaleNanometer
      , ScaleMicrometer
      , ScaleMillimeter
      , ScaleCentimeter
      , ScaleMeter
      , ScaleKilometer
      , ScaleMegameter
      , ScaleAU
      , ScaleLightYear
      , ScaleParsec
      )
  , gridScaleToMeters
  , gridScaleName
  , Grid3D(Grid3D)
  , Grid3DParams
  , grid3D
  , Axes3D(Axes3D)
  , Axes3DParams
  , axes3D
  ) as Grid

import Hydrogen.GPU.Scene3D.Core
  ( Scene3D
  , SceneCommand
      ( SetCamera
      , SetBackground
      , AddLight
      , DrawMesh
      , DrawGrid
      , DrawAxes
      , PushTransform
      , PopTransform
      , SetClipPlane
      , ClearClipPlane
      , Noop3D
      )
  , SceneBuffer
  , emptyScene
  , withCamera
  , withBackground
  , withLight
  , withMesh
  , setCamera
  , setBackground
  , addLight
  , drawMesh
  , drawGrid
  , drawAxes
  , pushTransform
  , popTransform
  , emptyBuffer3D
  , singleton3D
  , append3D
  , concat3D
  , flattenScene
  ) as Core

import Hydrogen.GPU.Scene3D.Identity
  ( positionId
  , meshId
  , boxMeshId
  , sphereMeshId
  , cylinderMeshId
  , coneMeshId
  , planeMeshId
  , torusMeshId
  , torusKnotMeshId
  , ringMeshId
  , circleMeshId
  , capsuleMeshId
  , icosahedronMeshId
  , octahedronMeshId
  , tetrahedronMeshId
  , dodecahedronMeshId
  , materialId
  , basicMaterialId
  , standardMaterialId
  , physicalMaterialId
  , lightId
  , cameraId
  ) as Identity
