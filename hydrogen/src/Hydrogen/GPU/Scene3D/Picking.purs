-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // gpu // scene3d // picking
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Picking — Scene-level ray intersection for object selection.
-- |
-- | ## Pipeline
-- | 1. Mouse event → NDC coordinates
-- | 2. rayFromCamera → Ray in world space
-- | 3. intersectScene → sorted list of SceneHit
-- | 4. Application handles hit (onClick, onHover callbacks)
-- |
-- | ## Three.js Parity
-- | - Raycaster.intersectObjects (recursive scene traversal)

module Hydrogen.GPU.Scene3D.Picking
  ( -- * Scene Hit Type
    SceneHit
    
  -- * Mesh Intersection
  , intersectMesh
  
  -- * Scene Intersection
  , intersectScene
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( negate
  , compare
  , map
  , (+)
  , (-)
  , (*)
  , (/)
  , (<$>)
  )

import Data.Array (sortBy, mapWithIndex, catMaybes)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.GPU.Scene3D.Mesh 
  ( PickId3D
  , Mesh3D
      ( BoxMesh3D
      , SphereMesh3D
      , PlaneMesh3D
      , CylinderMesh3D
      , ConeMesh3D
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
import Hydrogen.GPU.Scene3D.Raycaster 
  ( Intersection
  , intersectionPoint
  , intersectionDistance
  , intersectSphere3D
  , intersectBox3D
  , intersectPlane3D
  )
import Hydrogen.GPU.Scene3D.Core (Scene3D)
import Hydrogen.Schema.Dimension.Physical.SI (unwrapMeter)
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3)
import Hydrogen.Schema.Geometry.Ray (Ray)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // scene hit
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of a scene-level raycast hit.
-- |
-- | Contains intersection geometry plus application-level data:
-- | - The intersection point, distance, normal, UV (from Intersection)
-- | - The mesh index in the scene
-- | - The pick ID (if assigned)
-- | - The message callbacks (onClick, onHover)
-- |
-- | Sorted by distance for multi-hit scenarios.
type SceneHit :: Type -> Type
type SceneHit msg =
  { intersection :: Intersection        -- Geometric hit data
  , meshIndex :: Int                    -- Index in scene.meshes array
  , pickId :: Maybe PickId3D            -- Unique ID for GPU picking
  , worldPosition :: Vec3 Number        -- Hit point in world space
  , onClick :: Maybe msg                -- Callback if mesh was clicked
  , onHover :: Maybe msg                -- Callback if mesh was hovered
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // mesh intersection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Intersect a ray with a mesh geometry (at origin, unscaled).
-- |
-- | This tests ray intersection against the mesh's LOCAL geometry.
-- | The caller is responsible for transforming the ray into local space
-- | or transforming the result back to world space.
-- |
-- | Returns the intersection if the ray hits the geometry.
-- |
-- | ## Supported Geometries
-- | - BoxMesh3D: Uses AABB test
-- | - SphereMesh3D: Uses sphere test
-- | - PlaneMesh3D: Uses infinite plane test (practical for floor picking)
-- |
-- | ## Unsupported (returns Nothing)
-- | - Cylinder, Cone, Torus, etc.: Require more complex intersection math
-- | - BufferGeometry: Would require triangle-by-triangle testing
-- |
-- | Three.js parity: Raycaster.intersectObject for basic primitives
intersectMesh :: Ray -> Mesh3D -> Maybe Intersection
intersectMesh r mesh = case mesh of
  
  BoxMesh3D params ->
    let
      -- Box centered at origin, extends from -half to +half
      hw = unwrapMeter params.width / 2.0
      hh = unwrapMeter params.height / 2.0
      hd = unwrapMeter params.depth / 2.0
      boxMin = vec3 (negate hw) (negate hh) (negate hd)
      boxMax = vec3 hw hh hd
    in
      intersectBox3D r boxMin boxMax
  
  SphereMesh3D params ->
    let
      radius = unwrapMeter params.radius
      center = vec3 0.0 0.0 0.0  -- Sphere at origin
    in
      intersectSphere3D r center radius
  
  PlaneMesh3D _ ->
    -- Plane in XZ at Y=0, normal pointing up (+Y)
    let
      planeNormal = vec3 0.0 1.0 0.0
      planeConstant = 0.0  -- Passes through origin
    in
      intersectPlane3D r planeNormal planeConstant
  
  -- Geometries requiring more complex math — not yet implemented
  CylinderMesh3D _ -> Nothing
  ConeMesh3D _ -> Nothing
  TorusMesh3D _ -> Nothing
  TorusKnotMesh3D _ -> Nothing
  RingMesh3D _ -> Nothing
  CircleMesh3D _ -> Nothing
  CapsuleMesh3D _ -> Nothing
  IcosahedronMesh3D _ -> Nothing
  OctahedronMesh3D _ -> Nothing
  TetrahedronMesh3D _ -> Nothing
  DodecahedronMesh3D _ -> Nothing
  LatheMesh3D _ -> Nothing
  ExtrudeMesh3D _ -> Nothing
  BufferGeometry3D _ -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // scene intersection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Intersect a ray with all meshes in a scene.
-- |
-- | Returns a list of hits sorted by distance (nearest first).
-- | Each hit includes the mesh index and its callbacks (onClick, onHover).
-- |
-- | ## Usage
-- | ```purescript
-- | case intersectScene ray scene of
-- |   [] -> -- No hits
-- |   (hit : _) -> 
-- |     -- hit.onClick contains the message to dispatch
-- |     case hit.onClick of
-- |       Just msg -> dispatch msg
-- |       Nothing -> -- Mesh has no click handler
-- | ```
-- |
-- | ## Current Limitations
-- | - Does NOT account for mesh transforms (position, rotation, scale)
-- | - Does NOT handle nested groups
-- | - Only tests geometry at origin
-- |
-- | For proper transform support, the ray should be transformed into
-- | each mesh's local coordinate system before intersection.
-- |
-- | Three.js parity: Raycaster.intersectObjects
intersectScene :: forall msg. Ray -> Scene3D msg -> Array (SceneHit msg)
intersectScene r scene =
  let
    -- Test each mesh with its index
    testMesh idx meshParams =
      case intersectMesh r meshParams.geometry of
        Nothing -> Nothing
        Just intersection ->
          Just
            { intersection: intersection
            , meshIndex: idx
            , pickId: meshParams.pickId
            , worldPosition: intersectionPoint intersection
            , onClick: meshParams.onClick
            , onHover: meshParams.onHover
            }
    
    -- Get all hits with indices
    allHits = catMaybes (mapWithIndex testMesh scene.meshes)
    
    -- Sort by distance (nearest first)
    compareDistance a b = compare 
      (intersectionDistance a.intersection)
      (intersectionDistance b.intersection)
  in
    sortBy compareDistance allHits
