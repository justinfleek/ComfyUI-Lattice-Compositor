-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // gpu // webgpu // scene3d // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Scene3D Renderer — The core interpreter.
--
-- Takes pure Scene3D data, produces RenderCommands (also pure data).
-- RenderCommands are then executed against the GPU via Device.purs FFI.
--
-- ARCHITECTURE:
-- Scene3D (pure data)
--     ↓ extractRenderState
-- RenderState (camera matrices, sorted meshes, light uniforms)
--     ↓ generateRenderCommands
-- Array RenderCommand (pure draw call descriptions)
--     ↓ (executed by runtime via Device.purs FFI)
-- GPU pixels
--
-- NO MUTATION. NO FFI IN THIS MODULE. PURE FUNCTIONS ONLY.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Scene3D.Render
  ( -- Render commands (pure data)
    RenderCommand
      ( ClearCommand
      , SetPipelineCommand
      , SetBindGroupCommand
      , SetVertexBufferCommand
      , SetIndexBufferCommand
      , DrawIndexedCommand
      , DrawCommand
      )
    -- Command parameter types
  , ClearParams
  , DrawIndexedParams
  , DrawParams
  , IndexFormat(Uint16, Uint32)
  , BufferRef(BufferRef)
  , BindGroupData
    -- Render state (extracted from Scene3D)
  , RenderState
  , extractRenderState
    -- Command generation
  , generateRenderCommands
  , generateShadowCommands
  , generatePickCommands
    -- Frame uniforms
  , FrameUniforms
  , computeFrameUniforms
    -- Object uniforms
  , ObjectUniforms
  , computeObjectUniforms
    -- Light uniforms
  , LightUniforms
  , LightData
  , computeLightUniforms
    -- Material uniforms
  , MaterialUniforms
  , computeMaterialUniforms
    -- Mesh batching
  , RenderBatch
  , batchByMaterial
    -- Utilities
  , sortByDepth
  , frustumCull
    -- Transform utilities
  , computeEulerRotation
  , identityTransform
  ) where

import Prelude
  ( class Eq
  , Ordering(LT, GT, EQ)
  , map
  , negate
  , ($)
  , (*)
  , (+)
  , (-)
  , (/)
  , (<)
  , (<>)
  , (==)
  , (>)
  , (>=)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.GPU.Scene3D.Core (Scene3D)
import Hydrogen.GPU.Scene3D.Camera
  ( Camera3D
      ( PerspectiveCamera3D
      , OrthographicCamera3D
      )
  )
import Hydrogen.GPU.Scene3D.Background
  ( Background3D
      ( SolidBackground
      , GradientBackground
      , EnvironmentBackground
      )
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
  ( Material3D
      ( BasicMaterial3D
      , StandardMaterial3D
      , PhysicalMaterial3D
      )
  )
import Hydrogen.GPU.Scene3D.Mesh (MeshParams)
import Hydrogen.GPU.Scene3D.Position (Position3D, Direction3D(Direction3D), positionToMeters)
import Hydrogen.Schema.Dimension.Rotation.Quaternion (Quaternion, toMat4Quaternion)
import Hydrogen.GPU.WebGPU.Pipeline
  ( PipelineKey
  , pipelineKeyFromMaterial
  )
import Hydrogen.GPU.WebGPU.Scene3D.Geometry (MeshData, generateMesh)
import Hydrogen.Schema.Color.RGB (RGBA, rgbaToRecord)
import Hydrogen.Schema.Dimension.Physical.SI (unwrapMeter)
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3, getX3, getY3, getZ3, subtractVec3, normalizeVec3)
import Hydrogen.Schema.Dimension.Vector.Vec4 (Vec4, vec4, getX4, getY4, getZ4, getW4)
import Hydrogen.Schema.Geometry.Angle (unwrapDegrees)
import Hydrogen.Schema.Dimension.Matrix.Mat4
  ( Mat4
  , mat4Identity
  , makePerspective
  , makeOrthographic
  , makeLookAt
  , makeTranslation4
  , makeRotationX4
  , makeRotationY4
  , makeRotationZ4
  , makeScale4
  , mulMat4
  , transposeMat4
  , invertMat4
  , toArray16
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- RENDER COMMANDS (PURE DATA)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | A single GPU render command.
-- | Pure data describing what to do — executed by runtime.
data RenderCommand
  = ClearCommand ClearParams
  | SetPipelineCommand PipelineKey
  | SetBindGroupCommand Int BindGroupData
  | SetVertexBufferCommand Int BufferRef
  | SetIndexBufferCommand BufferRef IndexFormat
  | DrawIndexedCommand DrawIndexedParams
  | DrawCommand DrawParams

derive instance eqRenderCommand :: Eq RenderCommand

-- | Clear parameters.
type ClearParams =
  { color :: Vec4 Number
  , depth :: Number
  , stencil :: Int
  }

-- | Draw indexed parameters.
type DrawIndexedParams =
  { indexCount :: Int
  , instanceCount :: Int
  , firstIndex :: Int
  , baseVertex :: Int
  , firstInstance :: Int
  }

-- | Draw (non-indexed) parameters.
type DrawParams =
  { vertexCount :: Int
  , instanceCount :: Int
  , firstVertex :: Int
  , firstInstance :: Int
  }

-- | Index format.
data IndexFormat = Uint16 | Uint32

derive instance eqIndexFormat :: Eq IndexFormat

-- | Buffer reference (ID for runtime to resolve).
newtype BufferRef = BufferRef Int

derive instance eqBufferRef :: Eq BufferRef

-- | Bind group data.
type BindGroupData =
  { uniforms :: Array Number
  , textures :: Array Int
  , samplers :: Array Int
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- RENDER STATE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Render state extracted from Scene3D.
-- | Contains computed matrices and sorted/batched meshes.
type RenderState msg =
  { frameUniforms :: FrameUniforms
  , lightUniforms :: LightUniforms
  , batches :: Array (RenderBatch msg)
  , clearColor :: Vec4 Number
  , skybox :: Maybe Int  -- Skybox texture ID if present
  }

-- | Extract render state from a Scene3D.
extractRenderState :: forall msg. Scene3D msg -> RenderState msg
extractRenderState scene =
  { frameUniforms: computeFrameUniforms scene.camera
  , lightUniforms: computeLightUniforms scene.lights
  , batches: batchByMaterial scene.meshes
  , clearColor: backgroundToClearColor scene.background
  , skybox: backgroundToSkybox scene.background
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- FRAME UNIFORMS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Frame-level uniforms (updated once per frame).
-- | Matches WGSL FrameUniforms struct.
type FrameUniforms =
  { viewMatrix :: Mat4
  , projectionMatrix :: Mat4
  , viewProjectionMatrix :: Mat4
  , cameraPosition :: Vec3 Number
  , time :: Number
  }

-- | Compute frame uniforms from camera.
computeFrameUniforms :: Camera3D -> FrameUniforms
computeFrameUniforms camera =
  let
    viewMatrix = computeViewMatrix camera
    projectionMatrix = computeProjectionMatrix camera
    viewProjectionMatrix = mulMat4 projectionMatrix viewMatrix
    cameraPosition = getCameraPosition camera
  in
    { viewMatrix
    , projectionMatrix
    , viewProjectionMatrix
    , cameraPosition
    , time: 0.0  -- Set by runtime
    }

-- | Compute view matrix from camera.
computeViewMatrix :: Camera3D -> Mat4
computeViewMatrix = case _ of
  PerspectiveCamera3D params ->
    let
      pos = unwrapPosition3D params.position
      target = unwrapPosition3D params.target
      up = unwrapDirection3D params.up
    in
      makeLookAt pos target up
  
  OrthographicCamera3D params ->
    let
      pos = unwrapPosition3D params.position
      target = unwrapPosition3D params.target
      up = unwrapDirection3D params.up
    in
      makeLookAt pos target up

-- | Compute projection matrix from camera.
computeProjectionMatrix :: Camera3D -> Mat4
computeProjectionMatrix = case _ of
  PerspectiveCamera3D params ->
    let
      fov = unwrapDegrees params.fov
      aspect = params.aspect
      near = unwrapMeter params.near
      far = unwrapMeter params.far
    in
      makePerspective fov aspect near far
  
  OrthographicCamera3D params ->
    let
      left = unwrapMeter params.left
      right = unwrapMeter params.right
      top = unwrapMeter params.top
      bottom = unwrapMeter params.bottom
      near = unwrapMeter params.near
      far = unwrapMeter params.far
    in
      makeOrthographic left right bottom top near far

-- | Get camera world position.
getCameraPosition :: Camera3D -> Vec3 Number
getCameraPosition = case _ of
  PerspectiveCamera3D params -> unwrapPosition3D params.position
  OrthographicCamera3D params -> unwrapPosition3D params.position

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- LIGHT UNIFORMS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Light uniforms (matches WGSL LightUniforms struct).
type LightUniforms =
  { ambientColor :: Vec3 Number
  , numLights :: Int
  , lights :: Array LightData
  }

-- | Single light data (matches WGSL Light struct).
type LightData =
  { position :: Vec3 Number
  , lightType :: Int  -- 0 = directional, 1 = point, 2 = spot
  , color :: Vec3 Number
  , intensity :: Number
  , direction :: Vec3 Number
  , range :: Number
  , innerConeAngle :: Number
  , outerConeAngle :: Number
  }

-- | Compute light uniforms from light array.
computeLightUniforms :: Array Light3D -> LightUniforms
computeLightUniforms lights =
  let
    ambientColor = extractAmbientColor lights
    nonAmbientLights = Array.filter (\l -> not (isAmbientLight l)) lights
    lightData = map lightToData nonAmbientLights
  in
    { ambientColor
    , numLights: Array.length lightData
    , lights: lightData
    }

-- | Check if light is ambient.
isAmbientLight :: Light3D -> Boolean
isAmbientLight = case _ of
  AmbientLight3D _ -> true
  HemisphereLight3D _ -> true
  _ -> false

-- | Extract combined ambient color from lights.
extractAmbientColor :: Array Light3D -> Vec3 Number
extractAmbientColor lights =
  foldl addAmbient (vec3 0.0 0.0 0.0) lights
  where
    addAmbient acc light = case light of
      AmbientLight3D params ->
        let c = rgbaToVec3 params.color
            i = params.intensity
        in vec3 
          (vecX acc + vecX c * i)
          (vecY acc + vecY c * i)
          (vecZ acc + vecZ c * i)
      HemisphereLight3D params ->
        let sky = rgbaToVec3 params.skyColor
            ground = rgbaToVec3 params.groundColor
            i = params.intensity
            avg = vec3 
              ((vecX sky + vecX ground) / 2.0 * i)
              ((vecY sky + vecY ground) / 2.0 * i)
              ((vecZ sky + vecZ ground) / 2.0 * i)
        in vec3 
          (vecX acc + vecX avg)
          (vecY acc + vecY avg)
          (vecZ acc + vecZ avg)
      _ -> acc

-- | Convert Light3D to LightData.
lightToData :: Light3D -> LightData
lightToData = case _ of
  DirectionalLight3D params ->
    { position: vec3 0.0 0.0 0.0
    , lightType: 0
    , color: rgbaToVec3 params.color
    , intensity: params.intensity
    , direction: unwrapDirection3D params.direction
    , range: 0.0
    , innerConeAngle: 0.0
    , outerConeAngle: 0.0
    }
  
  PointLight3D params ->
    { position: unwrapPosition3D params.position
    , lightType: 1
    , color: rgbaToVec3 params.color
    , intensity: params.intensity
    , direction: vec3 0.0 0.0 0.0
    , range: unwrapMeter params.distance
    , innerConeAngle: 0.0
    , outerConeAngle: 0.0
    }
  
  SpotLight3D params ->
    let
      posVec = unwrapPosition3D params.position
      targetVec = unwrapPosition3D params.target
      -- Direction from position toward target (normalized)
      dirVec = normalizeVec3 (subtractVec3 targetVec posVec)
    in
      { position: posVec
      , lightType: 2
      , color: rgbaToVec3 params.color
      , intensity: params.intensity
      , direction: dirVec
      , range: unwrapMeter params.distance
      , innerConeAngle: unwrapDegrees params.angle * 0.8  -- Inner cone slightly smaller
      , outerConeAngle: unwrapDegrees params.angle
      }
  
  -- Ambient lights don't produce LightData (handled separately)
  AmbientLight3D _ -> emptyLightData
  HemisphereLight3D _ -> emptyLightData

emptyLightData :: LightData
emptyLightData =
  { position: vec3 0.0 0.0 0.0
  , lightType: 0
  , color: vec3 0.0 0.0 0.0
  , intensity: 0.0
  , direction: vec3 0.0 0.0 0.0
  , range: 0.0
  , innerConeAngle: 0.0
  , outerConeAngle: 0.0
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- OBJECT UNIFORMS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Per-object uniforms (matches WGSL ObjectUniforms struct).
type ObjectUniforms =
  { modelMatrix :: Mat4
  , normalMatrix :: Mat4  -- transpose(inverse(modelMatrix)) for correct normals
  }

-- | Compute object uniforms from mesh parameters.
computeObjectUniforms :: forall msg. MeshParams msg -> ObjectUniforms
computeObjectUniforms mesh =
  let
    modelMatrix = computeModelMatrix mesh
    normalMatrix = computeNormalMatrix modelMatrix
  in
    { modelMatrix
    , normalMatrix
    }

-- | Compute model matrix from mesh transform.
-- | Model = Translation × Rotation × Scale
computeModelMatrix :: forall msg. MeshParams msg -> Mat4
computeModelMatrix mesh =
  let
    pos = unwrapPosition3D mesh.position
    
    -- Extract rotation quaternion for matrix conversion
    rot :: Quaternion
    rot = mesh.rotation
    
    scl :: Vec3 Number
    scl = mesh.scale
    
    translateMat = makeTranslation4 (vecX pos) (vecY pos) (vecZ pos)
    rotateMat = toMat4Quaternion rot
    scaleMat = makeScale4 (vecX scl) (vecY scl) (vecZ scl)
  in
    -- T × R × S (standard TRS order)
    mulMat4 translateMat (mulMat4 rotateMat scaleMat)

-- | Compute normal matrix (transpose of inverse of model matrix).
-- | Required for correct normal transformation with non-uniform scaling.
-- | Falls back to transpose if matrix is singular (shouldn't happen for valid transforms).
computeNormalMatrix :: Mat4 -> Mat4
computeNormalMatrix modelMatrix =
  case invertMat4 modelMatrix of
    Just inverted -> transposeMat4 inverted
    Nothing -> transposeMat4 modelMatrix  -- Fallback for singular matrices

-- | Compute rotation matrix from Euler angles (XYZ order).
-- | 
-- | For most cases, use Quaternion rotation via computeModelMatrix.
-- | This function is provided for interop with systems that use Euler angles.
computeEulerRotation :: Number -> Number -> Number -> Mat4
computeEulerRotation rx ry rz =
  let
    rotX = makeRotationX4 rx
    rotY = makeRotationY4 ry
    rotZ = makeRotationZ4 rz
  in
    -- XYZ order: apply Z, then Y, then X (right-to-left multiplication)
    mulMat4 rotX (mulMat4 rotY rotZ)

-- | Identity matrix for transforms.
-- | 
-- | Use when no transformation is needed.
identityTransform :: Mat4
identityTransform = mat4Identity

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- MATERIAL UNIFORMS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Material uniforms (matches WGSL MaterialUniforms struct).
type MaterialUniforms =
  { baseColor :: Vec4 Number
  , emissive :: Vec3 Number
  , metallic :: Number
  , roughness :: Number
  , emissiveIntensity :: Number
  }

-- | Compute material uniforms from Material3D.
computeMaterialUniforms :: Material3D -> MaterialUniforms
computeMaterialUniforms = case _ of
  BasicMaterial3D params ->
    { baseColor: rgbaToVec4 params.color
    , emissive: vec3 0.0 0.0 0.0
    , metallic: 0.0
    , roughness: 1.0
    , emissiveIntensity: 0.0
    }
  
  StandardMaterial3D params ->
    { baseColor: rgbaToVec4 params.color
    , emissive: rgbaToVec3 params.emissive
    , metallic: params.metalness
    , roughness: params.roughness
    , emissiveIntensity: params.emissiveIntensity
    }
  
  PhysicalMaterial3D params ->
    { baseColor: rgbaToVec4 params.color
    , emissive: rgbaToVec3 params.emissive
    , metallic: params.metalness
    , roughness: params.roughness
    , emissiveIntensity: params.emissiveIntensity
    }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- RENDER BATCHING
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | A render batch groups meshes by pipeline.
-- | Same pipeline = one state change, multiple draw calls.
type RenderBatch msg =
  { pipelineKey :: PipelineKey
  , meshes :: Array (MeshParams msg)
  }

-- | Batch meshes by material (same material = same pipeline).
batchByMaterial :: forall msg. Array (MeshParams msg) -> Array (RenderBatch msg)
batchByMaterial meshes =
  let
    -- Group by pipeline key
    grouped = groupBy (\m -> pipelineKeyFromMaterial m.material) meshes
  in
    map (\{ key, items } -> { pipelineKey: key, meshes: items }) grouped

-- Simple groupBy implementation
groupBy :: forall a k. Eq k => (a -> k) -> Array a -> Array { key :: k, items :: Array a }
groupBy keyFn arr = foldl insertItem [] arr
  where
    insertItem groups item =
      let key = keyFn item
      in case findGroup key groups of
        Just idx -> updateAt idx (\g -> g { items = Array.snoc g.items item }) groups
        Nothing -> Array.snoc groups { key, items: [item] }
    
    findGroup :: k -> Array { key :: k, items :: Array a } -> Maybe Int
    findGroup k groups = findIndex (\g -> g.key == k) groups
    
    findIndex :: forall b. (b -> Boolean) -> Array b -> Maybe Int
    findIndex pred xs = go 0 xs
      where
        go _ [] = Nothing
        go i arr' = case Array.head arr' of
          Nothing -> Nothing
          Just x -> if pred x then Just i else go (i + 1) (Array.drop 1 arr')
    
    updateAt :: forall b. Int -> (b -> b) -> Array b -> Array b
    updateAt idx f xs = case Array.index xs idx of
      Nothing -> xs
      Just x -> case Array.updateAt idx (f x) xs of
        Nothing -> xs
        Just updated -> updated

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- COMMAND GENERATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate render commands from Scene3D.
generateRenderCommands :: forall msg. Scene3D msg -> Array RenderCommand
generateRenderCommands scene =
  let
    state = extractRenderState scene
    clearCmd = ClearCommand
      { color: state.clearColor
      , depth: 1.0
      , stencil: 0
      }
    batchCmds = Array.concatMap (generateBatchCommands state) state.batches
  in
    [clearCmd] <> batchCmds

-- | Generate commands for a single batch.
generateBatchCommands :: forall msg. RenderState msg -> RenderBatch msg -> Array RenderCommand
generateBatchCommands state batch =
  let
    pipelineCmd = SetPipelineCommand batch.pipelineKey
    frameBindCmd = SetBindGroupCommand 0 (frameUniformsToBindGroup state.frameUniforms)
    lightBindCmd = SetBindGroupCommand 3 (lightUniformsToBindGroup state.lightUniforms)
    meshCmds = Array.concatMap (generateMeshCommands state) batch.meshes
  in
    [pipelineCmd, frameBindCmd, lightBindCmd] <> meshCmds

-- | Generate commands for a single mesh.
generateMeshCommands :: forall msg. RenderState msg -> MeshParams msg -> Array RenderCommand
generateMeshCommands _state mesh =
  let
    objectUniforms = computeObjectUniforms mesh
    materialUniforms = computeMaterialUniforms mesh.material
    
    -- Generate geometry data from mesh descriptor
    meshData :: MeshData
    meshData = generateMesh mesh.geometry
    
    materialBindCmd = SetBindGroupCommand 1 (materialUniformsToBindGroup materialUniforms)
    objectBindCmd = SetBindGroupCommand 2 (objectUniformsToBindGroup objectUniforms)
    vertexCmd = SetVertexBufferCommand 0 (BufferRef 0)  -- Runtime resolves
    indexCmd = SetIndexBufferCommand (BufferRef 0) Uint16
    drawCmd = DrawIndexedCommand
      { indexCount: Array.length meshData.indices
      , instanceCount: 1
      , firstIndex: 0
      , baseVertex: 0
      , firstInstance: 0
      }
  in
    [materialBindCmd, objectBindCmd, vertexCmd, indexCmd, drawCmd]

-- | Generate shadow pass commands.
generateShadowCommands :: forall msg. Scene3D msg -> Array RenderCommand
generateShadowCommands _scene =
  -- Shadow pass uses depth-only pipeline
  -- For each shadow-casting light, render all meshes from light's POV
  []  -- Implement when shadow mapping is needed

-- | Generate pick pass commands.
generatePickCommands :: forall msg. Scene3D msg -> Array RenderCommand
generatePickCommands _scene =
  -- Pick pass uses pick pipeline, outputs object IDs
  []  -- Implement when picking is needed

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- BIND GROUP SERIALIZATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

frameUniformsToBindGroup :: FrameUniforms -> BindGroupData
frameUniformsToBindGroup u =
  { uniforms: mat4ToArray u.viewProjectionMatrix 
      <> vec3ToArray u.cameraPosition 
      <> [u.time]
  , textures: []
  , samplers: []
  }

lightUniformsToBindGroup :: LightUniforms -> BindGroupData
lightUniformsToBindGroup u =
  { uniforms: vec3ToArray u.ambientColor 
      <> [toNumber u.numLights]
      <> Array.concatMap lightDataToArray u.lights
  , textures: []
  , samplers: []
  }

materialUniformsToBindGroup :: MaterialUniforms -> BindGroupData
materialUniformsToBindGroup u =
  { uniforms: vec4ToArray u.baseColor
      <> vec3ToArray u.emissive
      <> [u.metallic, u.roughness, u.emissiveIntensity]
  , textures: []
  , samplers: []
  }

objectUniformsToBindGroup :: ObjectUniforms -> BindGroupData
objectUniformsToBindGroup u =
  { uniforms: mat4ToArray u.modelMatrix <> mat4ToArray u.normalMatrix
  , textures: []
  , samplers: []
  }

lightDataToArray :: LightData -> Array Number
lightDataToArray l =
  vec3ToArray l.position
    <> [toNumber l.lightType]
    <> vec3ToArray l.color
    <> [l.intensity]
    <> vec3ToArray l.direction
    <> [l.range, l.innerConeAngle, l.outerConeAngle]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- CULLING AND SORTING
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Sort meshes by depth (back to front for transparency).
sortByDepth :: forall msg. Vec3 Number -> Array (MeshParams msg) -> Array (MeshParams msg)
sortByDepth cameraPos meshes =
  Array.sortBy compareDepth meshes
  where
    compareDepth a b =
      let
        distA = distanceSquared cameraPos (unwrapPosition3D a.position)
        distB = distanceSquared cameraPos (unwrapPosition3D b.position)
      in
        -- Sort far to near for correct alpha blending
        if distA > distB then LT else if distA < distB then GT else EQ
    
    distanceSquared p1 p2 =
      let
        dx = vecX p1 - vecX p2
        dy = vecY p1 - vecY p2
        dz = vecZ p1 - vecZ p2
      in
        dx * dx + dy * dy + dz * dz

-- | Frustum cull meshes (remove meshes outside view frustum).
-- |
-- | Tests mesh center against near/far planes using camera depth.
-- | Full implementation would extract 6 frustum planes from viewProjection.
frustumCull :: forall msg. FrameUniforms -> Array (MeshParams msg) -> Array (MeshParams msg)
frustumCull frameUniforms meshes =
  Array.filter (isInFrustum frameUniforms) meshes

-- | Test if mesh center is within frustum depth range.
isInFrustum :: forall msg. FrameUniforms -> MeshParams msg -> Boolean
isInFrustum frameUniforms mesh =
  let
    -- Get mesh position in world space
    meshPos = unwrapPosition3D mesh.position
    meshX = vecX meshPos
    meshY = vecY meshPos  
    meshZ = vecZ meshPos
    
    -- Transform to view space using view matrix
    viewMat = frameUniforms.viewMatrix
    viewArr = toArray16 viewMat
    
    -- Manual transform: viewZ = row 2 dot (meshX, meshY, meshZ, 1)
    -- View space Z (negated because camera looks down -Z)
    viewZ = negate $ 
      getViewElement viewArr 2 * meshX +
      getViewElement viewArr 6 * meshY +
      getViewElement viewArr 10 * meshZ +
      getViewElement viewArr 14
    
    -- Check against near/far (approximate - assumes reasonable bounding sphere)
    boundingRadius = 10.0  -- Conservative estimate; real impl would compute from mesh
  in
    viewZ + boundingRadius >= 0.1 -- Near plane check
    
-- | Get element from 16-element matrix array.
getViewElement :: Array Number -> Int -> Number
getViewElement arr idx = 
  case Array.index arr idx of
    Just n -> n
    Nothing -> 0.0

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- UTILITY FUNCTIONS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

backgroundToClearColor :: Background3D -> Vec4 Number
backgroundToClearColor = case _ of
  SolidBackground color -> rgbaToVec4 color
  GradientBackground topColor _ _ -> rgbaToVec4 topColor
  EnvironmentBackground _ -> vec4 0.0 0.0 0.0 1.0  -- Environment map renders over clear

backgroundToSkybox :: Background3D -> Maybe Int
backgroundToSkybox = case _ of
  EnvironmentBackground envMap -> Just envMap.cubeMapId
  _ -> Nothing

rgbaToVec3 :: RGBA -> Vec3 Number
rgbaToVec3 color =
  let c = rgbaToRecord color
  in vec3 (toNumber c.r / 255.0) (toNumber c.g / 255.0) (toNumber c.b / 255.0)

rgbaToVec4 :: RGBA -> Vec4 Number
rgbaToVec4 color =
  let c = rgbaToRecord color
  in vec4 
    (toNumber c.r / 255.0) 
    (toNumber c.g / 255.0) 
    (toNumber c.b / 255.0) 
    (toNumber c.a / 255.0)

vec3ToArray :: Vec3 Number -> Array Number
vec3ToArray v = [vecX v, vecY v, vecZ v]

vec4ToArray :: Vec4 Number -> Array Number
vec4ToArray v = [vecX4 v, vecY4 v, vecZ4 v, vecW4 v]

mat4ToArray :: Mat4 -> Array Number
mat4ToArray = toArray16

-- Vec3 accessors
vecX :: Vec3 Number -> Number
vecX = getX3

vecY :: Vec3 Number -> Number
vecY = getY3

vecZ :: Vec3 Number -> Number
vecZ = getZ3

-- Vec4 accessors
vecX4 :: Vec4 Number -> Number
vecX4 = getX4

vecY4 :: Vec4 Number -> Number
vecY4 = getY4

vecZ4 :: Vec4 Number -> Number
vecZ4 = getZ4

vecW4 :: Vec4 Number -> Number
vecW4 = getW4

-- Boolean negation
not :: Boolean -> Boolean
not true = false
not false = true

-- Position/Direction unwrap helpers
unwrapPosition3D :: Position3D -> Vec3 Number
unwrapPosition3D pos =
  let m = positionToMeters pos
  in vec3 m.x m.y m.z

unwrapDirection3D :: Direction3D -> Vec3 Number
unwrapDirection3D (Direction3D v) = v
