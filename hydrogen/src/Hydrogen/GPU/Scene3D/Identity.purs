-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // gpu // scene3d // identity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Scene3D Identity — Deterministic UUID5 derivation for 3D scene elements.
-- |
-- | ## Why Deterministic Identity?
-- |
-- | At billion-agent scale, agents need reproducible identity:
-- | - Same mesh parameters → same UUID5 (always)
-- | - Two agents creating identical geometry get identical UUIDs
-- | - Enables deterministic caching, diffing, and distribution
-- | - Full algebraic reasoning about 3D scene identity
-- |
-- | ## Naming Convention
-- |
-- | Each type serializes to a canonical string format:
-- | - Position3D: "position:x:y:z" (picometer values)
-- | - BoxMesh: "box:w:h:d:ws:hs:ds" (dimensions and segments)
-- | - Material: "standard:r:g:b:a:rough:metal:..." (all parameters)
-- |
-- | The canonical string is then hashed with the appropriate namespace
-- | to produce the UUID5.
-- |
-- | ## Proof Reference
-- |
-- | Determinism: `proofs/Hydrogen/Identity/UUID5.lean`
-- | - uuid5_deterministic: same input → same output
-- | - uuid5_collision_resistant: different input → different output (high prob)

module Hydrogen.GPU.Scene3D.Identity
  ( -- * Position Identity
    positionId
  
  -- * Mesh Identity
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
  
  -- * Material Identity
  , materialId
  , basicMaterialId
  , standardMaterialId
  , physicalMaterialId
  
  -- * Light Identity
  , lightId
  
  -- * Camera Identity
  , cameraId
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  )

import Hydrogen.Schema.Attestation.UUID5 as UUID5
import Hydrogen.Schema.Attestation.UUID5 (UUID5)

import Hydrogen.GPU.Scene3D.Position (Position3D(Position3D))
import Hydrogen.GPU.Scene3D.Camera
  ( Camera3D(PerspectiveCamera3D, OrthographicCamera3D)
  , PerspectiveCameraParams
  , OrthographicCameraParams
  )
import Hydrogen.GPU.Scene3D.Light
  ( Light3D
      ( AmbientLight3D
      , DirectionalLight3D
      , PointLight3D
      , SpotLight3D
      , HemisphereLight3D
      )
  )
import Hydrogen.GPU.Scene3D.Material
  ( Material3D(BasicMaterial3D, StandardMaterial3D, PhysicalMaterial3D)
  , BasicMaterialParams
  , StandardMaterialParams
  , PhysicalMaterialParams
  )
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
  , SphereMeshParams
  , CylinderMeshParams
  , ConeMeshParams
  , PlaneMeshParams
  , TorusMeshParams
  , TorusKnotMeshParams
  , RingMeshParams
  , CircleMeshParams
  , CapsuleMeshParams
  , IcosahedronMeshParams
  , OctahedronMeshParams
  , TetrahedronMeshParams
  , DodecahedronMeshParams
  )

import Hydrogen.Schema.Dimension.Physical.Atomic (unwrapPicometer)
import Hydrogen.Schema.Dimension.Physical.SI (unwrapMeter)
import Hydrogen.Schema.Geometry.Angle (unwrapDegrees)
import Hydrogen.Schema.Color.RGB (RGBA)
import Hydrogen.Schema.Color.RGB as RGB

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // position identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Derive UUID5 from Position3D.
-- |
-- | Two positions with identical picometer values produce identical UUIDs.
-- | Format: "position:x:y:z" where x, y, z are picometer values.
positionId :: Position3D -> UUID5
positionId (Position3D p) =
  let
    canonical = "position:" 
      <> show (unwrapPicometer p.x) <> ":"
      <> show (unwrapPicometer p.y) <> ":"
      <> show (unwrapPicometer p.z)
  in
    UUID5.uuid5 UUID5.nsPosition canonical

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // mesh identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Derive UUID5 from any Mesh3D.
-- |
-- | Dispatches to the appropriate mesh-specific function.
meshId :: Mesh3D -> UUID5
meshId (BoxMesh3D params) = boxMeshId params
meshId (SphereMesh3D params) = sphereMeshId params
meshId (CylinderMesh3D params) = cylinderMeshId params
meshId (ConeMesh3D params) = coneMeshId params
meshId (PlaneMesh3D params) = planeMeshId params
meshId (TorusMesh3D params) = torusMeshId params
meshId (TorusKnotMesh3D params) = torusKnotMeshId params
meshId (RingMesh3D params) = ringMeshId params
meshId (CircleMesh3D params) = circleMeshId params
meshId (CapsuleMesh3D params) = capsuleMeshId params
meshId (IcosahedronMesh3D params) = icosahedronMeshId params
meshId (OctahedronMesh3D params) = octahedronMeshId params
meshId (TetrahedronMesh3D params) = tetrahedronMeshId params
meshId (DodecahedronMesh3D params) = dodecahedronMeshId params
meshId (LatheMesh3D _params) = UUID5.uuid5 UUID5.nsMesh "lathe:procedural"
meshId (ExtrudeMesh3D _params) = UUID5.uuid5 UUID5.nsMesh "extrude:procedural"
meshId (BufferGeometry3D _params) = UUID5.uuid5 UUID5.nsMesh "buffer:custom"

-- | Box mesh identity.
-- |
-- | Format: "box:w:h:d:ws:hs:ds"
boxMeshId :: BoxMeshParams -> UUID5
boxMeshId p =
  let
    canonical = "box:"
      <> show (unwrapMeter p.width) <> ":"
      <> show (unwrapMeter p.height) <> ":"
      <> show (unwrapMeter p.depth) <> ":"
      <> show p.widthSegments <> ":"
      <> show p.heightSegments <> ":"
      <> show p.depthSegments
  in
    UUID5.uuid5 UUID5.nsMesh canonical

-- | Sphere mesh identity.
-- |
-- | Format: "sphere:r:ws:hs:phiS:phiL:thetaS:thetaL"
sphereMeshId :: SphereMeshParams -> UUID5
sphereMeshId p =
  let
    canonical = "sphere:"
      <> show (unwrapMeter p.radius) <> ":"
      <> show p.widthSegments <> ":"
      <> show p.heightSegments <> ":"
      <> show (unwrapDegrees p.phiStart) <> ":"
      <> show (unwrapDegrees p.phiLength) <> ":"
      <> show (unwrapDegrees p.thetaStart) <> ":"
      <> show (unwrapDegrees p.thetaLength)
  in
    UUID5.uuid5 UUID5.nsMesh canonical

-- | Cylinder mesh identity.
-- |
-- | Format: "cylinder:rt:rb:h:rs:hs:open:thetaS:thetaL"
cylinderMeshId :: CylinderMeshParams -> UUID5
cylinderMeshId p =
  let
    canonical = "cylinder:"
      <> show (unwrapMeter p.radiusTop) <> ":"
      <> show (unwrapMeter p.radiusBottom) <> ":"
      <> show (unwrapMeter p.height) <> ":"
      <> show p.radialSegments <> ":"
      <> show p.heightSegments <> ":"
      <> show p.openEnded <> ":"
      <> show (unwrapDegrees p.thetaStart) <> ":"
      <> show (unwrapDegrees p.thetaLength)
  in
    UUID5.uuid5 UUID5.nsMesh canonical

-- | Cone mesh identity.
-- |
-- | Format: "cone:r:h:rs:hs:open:thetaS:thetaL"
coneMeshId :: ConeMeshParams -> UUID5
coneMeshId p =
  let
    canonical = "cone:"
      <> show (unwrapMeter p.radius) <> ":"
      <> show (unwrapMeter p.height) <> ":"
      <> show p.radialSegments <> ":"
      <> show p.heightSegments <> ":"
      <> show p.openEnded <> ":"
      <> show (unwrapDegrees p.thetaStart) <> ":"
      <> show (unwrapDegrees p.thetaLength)
  in
    UUID5.uuid5 UUID5.nsMesh canonical

-- | Plane mesh identity.
-- |
-- | Format: "plane:w:h:ws:hs"
planeMeshId :: PlaneMeshParams -> UUID5
planeMeshId p =
  let
    canonical = "plane:"
      <> show (unwrapMeter p.width) <> ":"
      <> show (unwrapMeter p.height) <> ":"
      <> show p.widthSegments <> ":"
      <> show p.heightSegments
  in
    UUID5.uuid5 UUID5.nsMesh canonical

-- | Torus mesh identity.
-- |
-- | Format: "torus:r:t:rs:ts:arc"
torusMeshId :: TorusMeshParams -> UUID5
torusMeshId p =
  let
    canonical = "torus:"
      <> show (unwrapMeter p.radius) <> ":"
      <> show (unwrapMeter p.tube) <> ":"
      <> show p.radialSegments <> ":"
      <> show p.tubularSegments <> ":"
      <> show (unwrapDegrees p.arc)
  in
    UUID5.uuid5 UUID5.nsMesh canonical

-- | Torus knot mesh identity.
-- |
-- | Format: "torusknot:r:t:ts:rs:p:q"
torusKnotMeshId :: TorusKnotMeshParams -> UUID5
torusKnotMeshId p =
  let
    canonical = "torusknot:"
      <> show (unwrapMeter p.radius) <> ":"
      <> show (unwrapMeter p.tube) <> ":"
      <> show p.tubularSegments <> ":"
      <> show p.radialSegments <> ":"
      <> show p.p <> ":"
      <> show p.q
  in
    UUID5.uuid5 UUID5.nsMesh canonical

-- | Ring mesh identity.
-- |
-- | Format: "ring:ir:or:ts:ps:start:len"
ringMeshId :: RingMeshParams -> UUID5
ringMeshId p =
  let
    canonical = "ring:"
      <> show (unwrapMeter p.innerRadius) <> ":"
      <> show (unwrapMeter p.outerRadius) <> ":"
      <> show p.thetaSegments <> ":"
      <> show p.phiSegments <> ":"
      <> show (unwrapDegrees p.thetaStart) <> ":"
      <> show (unwrapDegrees p.thetaLength)
  in
    UUID5.uuid5 UUID5.nsMesh canonical

-- | Circle mesh identity.
-- |
-- | Format: "circle:r:s:start:len"
circleMeshId :: CircleMeshParams -> UUID5
circleMeshId p =
  let
    canonical = "circle:"
      <> show (unwrapMeter p.radius) <> ":"
      <> show p.segments <> ":"
      <> show (unwrapDegrees p.thetaStart) <> ":"
      <> show (unwrapDegrees p.thetaLength)
  in
    UUID5.uuid5 UUID5.nsMesh canonical

-- | Capsule mesh identity.
-- |
-- | Format: "capsule:r:l:cs:rs"
capsuleMeshId :: CapsuleMeshParams -> UUID5
capsuleMeshId p =
  let
    canonical = "capsule:"
      <> show (unwrapMeter p.radius) <> ":"
      <> show (unwrapMeter p.length) <> ":"
      <> show p.capSegments <> ":"
      <> show p.radialSegments
  in
    UUID5.uuid5 UUID5.nsMesh canonical

-- | Icosahedron mesh identity.
-- |
-- | Format: "icosahedron:r:d"
icosahedronMeshId :: IcosahedronMeshParams -> UUID5
icosahedronMeshId p =
  let
    canonical = "icosahedron:"
      <> show (unwrapMeter p.radius) <> ":"
      <> show p.detail
  in
    UUID5.uuid5 UUID5.nsMesh canonical

-- | Octahedron mesh identity.
-- |
-- | Format: "octahedron:r:d"
octahedronMeshId :: OctahedronMeshParams -> UUID5
octahedronMeshId p =
  let
    canonical = "octahedron:"
      <> show (unwrapMeter p.radius) <> ":"
      <> show p.detail
  in
    UUID5.uuid5 UUID5.nsMesh canonical

-- | Tetrahedron mesh identity.
-- |
-- | Format: "tetrahedron:r:d"
tetrahedronMeshId :: TetrahedronMeshParams -> UUID5
tetrahedronMeshId p =
  let
    canonical = "tetrahedron:"
      <> show (unwrapMeter p.radius) <> ":"
      <> show p.detail
  in
    UUID5.uuid5 UUID5.nsMesh canonical

-- | Dodecahedron mesh identity.
-- |
-- | Format: "dodecahedron:r:d"
dodecahedronMeshId :: DodecahedronMeshParams -> UUID5
dodecahedronMeshId p =
  let
    canonical = "dodecahedron:"
      <> show (unwrapMeter p.radius) <> ":"
      <> show p.detail
  in
    UUID5.uuid5 UUID5.nsMesh canonical

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // material identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Derive UUID5 from any Material3D.
materialId :: Material3D -> UUID5
materialId (BasicMaterial3D params) = basicMaterialId params
materialId (StandardMaterial3D params) = standardMaterialId params
materialId (PhysicalMaterial3D params) = physicalMaterialId params

-- | Basic material identity.
-- |
-- | Format: "basic:r:g:b:a:opacity:transparent:wireframe"
basicMaterialId :: BasicMaterialParams -> UUID5
basicMaterialId p =
  let
    canonical = "basic:"
      <> rgbaCanonical p.color <> ":"
      <> show p.opacity <> ":"
      <> show p.transparent <> ":"
      <> show p.wireframe
  in
    UUID5.uuid5 UUID5.nsMaterial canonical

-- | Standard PBR material identity.
-- |
-- | Format: "standard:color:rough:metal:emissive:emissiveI:opacity:transparent:wireframe"
standardMaterialId :: StandardMaterialParams -> UUID5
standardMaterialId p =
  let
    canonical = "standard:"
      <> rgbaCanonical p.color <> ":"
      <> show p.roughness <> ":"
      <> show p.metalness <> ":"
      <> rgbaCanonical p.emissive <> ":"
      <> show p.emissiveIntensity <> ":"
      <> show p.opacity <> ":"
      <> show p.transparent <> ":"
      <> show p.wireframe
  in
    UUID5.uuid5 UUID5.nsMaterial canonical

-- | Physical PBR material identity.
-- |
-- | Format: "physical:color:rough:metal:clearcoat:ccrough:ior:trans:thick:emissive:emissiveI:opacity:transparent"
physicalMaterialId :: PhysicalMaterialParams -> UUID5
physicalMaterialId p =
  let
    canonical = "physical:"
      <> rgbaCanonical p.color <> ":"
      <> show p.roughness <> ":"
      <> show p.metalness <> ":"
      <> show p.clearcoat <> ":"
      <> show p.clearcoatRoughness <> ":"
      <> show p.ior <> ":"
      <> show p.transmission <> ":"
      <> show (unwrapMeter p.thickness) <> ":"
      <> rgbaCanonical p.emissive <> ":"
      <> show p.emissiveIntensity <> ":"
      <> show p.opacity <> ":"
      <> show p.transparent
  in
    UUID5.uuid5 UUID5.nsMaterial canonical

-- | Canonical string for RGBA color.
rgbaCanonical :: RGBA -> String
rgbaCanonical c =
  let rec = RGB.rgbaToRecord c
  in show rec.r <> "," 
    <> show rec.g <> "," 
    <> show rec.b <> "," 
    <> show rec.a

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // light identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Derive UUID5 from any Light3D.
-- |
-- | Each light type includes all its parameters in the canonical string.
lightId :: Light3D -> UUID5
lightId (AmbientLight3D p) =
  let
    canonical = "ambient:" <> rgbaCanonical p.color <> ":" <> show p.intensity
  in
    UUID5.uuid5 UUID5.nsLight canonical
    
lightId (DirectionalLight3D p) =
  let
    canonical = "directional:" 
      <> rgbaCanonical p.color <> ":"
      <> show p.intensity <> ":"
      <> show p.castShadow <> ":"
      <> show p.shadowMapSize <> ":"
      <> show p.shadowBias
  in
    UUID5.uuid5 UUID5.nsLight canonical
    
lightId (PointLight3D p) =
  let
    canonical = "point:"
      <> rgbaCanonical p.color <> ":"
      <> show p.intensity <> ":"
      <> show (unwrapMeter p.distance) <> ":"
      <> show p.decay <> ":"
      <> show p.castShadow
  in
    UUID5.uuid5 UUID5.nsLight canonical
    
lightId (SpotLight3D p) =
  let
    canonical = "spot:"
      <> rgbaCanonical p.color <> ":"
      <> show p.intensity <> ":"
      <> show (unwrapMeter p.distance) <> ":"
      <> show (unwrapDegrees p.angle) <> ":"
      <> show p.penumbra <> ":"
      <> show p.decay <> ":"
      <> show p.castShadow
  in
    UUID5.uuid5 UUID5.nsLight canonical
    
lightId (HemisphereLight3D p) =
  let
    canonical = "hemisphere:"
      <> rgbaCanonical p.skyColor <> ":"
      <> rgbaCanonical p.groundColor <> ":"
      <> show p.intensity
  in
    UUID5.uuid5 UUID5.nsLight canonical

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // camera identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Derive UUID5 from any Camera3D.
cameraId :: Camera3D -> UUID5
cameraId (PerspectiveCamera3D p) = perspectiveCameraId p
cameraId (OrthographicCamera3D p) = orthographicCameraId p

-- | Perspective camera identity.
perspectiveCameraId :: PerspectiveCameraParams -> UUID5
perspectiveCameraId p =
  let
    canonical = "perspective:"
      <> show (unwrapDegrees p.fov) <> ":"
      <> show (unwrapMeter p.near) <> ":"
      <> show (unwrapMeter p.far) <> ":"
      <> show p.aspect
  in
    UUID5.uuid5 UUID5.nsCamera canonical

-- | Orthographic camera identity.
orthographicCameraId :: OrthographicCameraParams -> UUID5
orthographicCameraId p =
  let
    canonical = "orthographic:"
      <> show (unwrapMeter p.left) <> ":"
      <> show (unwrapMeter p.right) <> ":"
      <> show (unwrapMeter p.top) <> ":"
      <> show (unwrapMeter p.bottom) <> ":"
      <> show (unwrapMeter p.near) <> ":"
      <> show (unwrapMeter p.far) <> ":"
      <> show p.zoom
  in
    UUID5.uuid5 UUID5.nsCamera canonical
