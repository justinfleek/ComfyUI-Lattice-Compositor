# WebGPU Runtime Architecture

> Pure data in, GPU commands out. No JavaScript runtime. No mutable state.

## Status: DESIGN DOCUMENT — Implementation Phase

---

## The Vision

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                                                                             │
│   Haskell Backend (truth)                                                   │
│         ↓                                                                   │
│     Pure Data (Element, Scene3D, DrawCommand)                               │
│         ↓                                                                   │
│   PureScript Translation Layer (typed, explicit, composable)                │
│         ↓                                                                   │
│     WebGPU Runtime (minimal interpreter)                                    │
│         ↓                                                                   │
│     GPU (pixels)                                                            │
│                                                                             │
│   JavaScript exists ONLY at brand ingestion/export boundaries.              │
│   Everything else is pure data flowing through typed transformations.       │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

At billion-agent scale, bottlenecks come from:
1. **Mutable state** — agents stepping on each other's data
2. **Implicit dependencies** — hidden coupling between components
3. **Runtime interpretation** — parsing/evaluating at render time
4. **Non-determinism** — same input producing different output

The WebGPU runtime eliminates all of these by being a **pure interpreter**:
- Input: `Scene3D msg` or `CommandBuffer msg` (pure data)
- Output: GPU commands (deterministic)
- State: None (stateless function)

---

## Current Infrastructure

### What Exists (Pure Data Layer)

| Module | Lines | Description |
|--------|-------|-------------|
| `GPU/Binary.purs` | 1,072 | Wire format with v1/v2 opcodes |
| `GPU/DrawCommand.purs` | 1,054 | Complete GPU primitive vocabulary |
| `GPU/Flatten.purs` | 358 | Element → CommandBuffer |
| `GPU/GlyphConvert.purs` | 237 | Typography → DrawCommand |
| `GPU/Index.purs` | 282 | Bounded identity types |
| `GPU/Scene3D/` | 2,421 | Complete 3D scene description |
| **Total** | **5,424** | Pure data definitions |

### What's Missing (Runtime)

| Module | Purpose | Status |
|--------|---------|--------|
| `GPU/WebGPU/` | Actual GPU execution | **EMPTY** |

The `WebGPU/` directory is where the runtime lives. This document specifies its architecture.

---

## Architecture Overview

```
src/Hydrogen/GPU/WebGPU/
├── Types.purs           -- Core WebGPU type wrappers
├── Device.purs          -- GPU device initialization
├── Buffer.purs          -- Buffer management
├── Texture.purs         -- Texture management
├── Sampler.purs         -- Sampler states
├── Shader.purs          -- WGSL shader compilation
├── Pipeline.purs        -- Render pipeline creation
├── BindGroup.purs       -- Resource binding
├── Pass.purs            -- Render pass encoding
├── Render.purs          -- Command dispatch
├── Pick.purs            -- GPU-based hit testing
├── Scene3D/
│   ├── Geometry.purs    -- Procedural mesh generation
│   ├── Material.purs    -- Material → shader mapping
│   ├── Light.purs       -- Light data → uniforms
│   └── Render.purs      -- Scene3D interpreter
└── Typography/
    ├── Atlas.purs       -- SDF font texture atlas
    ├── Tessellation.purs-- Path → triangle conversion
    └── Glyph.purs       -- Glyph rendering

```

---

## Module Specifications

### 1. Types.purs — WebGPU Type Wrappers

Pure PureScript types wrapping WebGPU concepts. No FFI here — these are the vocabulary.

```purescript
module Hydrogen.GPU.WebGPU.Types
  ( -- Device types
    GPUDeviceDescriptor
  , GPUAdapterDescriptor
  , GPUQueueDescriptor
  , GPULimits
  , GPUFeatureName(..)
    -- Buffer types
  , GPUBufferDescriptor
  , GPUBufferUsage(..)
  , GPUMapMode(..)
    -- Texture types
  , GPUTextureDescriptor
  , GPUTextureFormat(..)
  , GPUTextureUsage(..)
  , GPUTextureDimension(..)
  , GPUTextureViewDescriptor
    -- Sampler types
  , GPUSamplerDescriptor
  , GPUAddressMode(..)
  , GPUFilterMode(..)
  , GPUCompareFunction(..)
    -- Shader types
  , GPUShaderModuleDescriptor
  , WGSLSource
    -- Pipeline types
  , GPURenderPipelineDescriptor
  , GPUVertexState
  , GPUFragmentState
  , GPUPrimitiveState
  , GPUDepthStencilState
  , GPUMultisampleState
  , GPUVertexBufferLayout
  , GPUVertexAttribute
  , GPUVertexFormat(..)
  , GPUVertexStepMode(..)
  , GPUPrimitiveTopology(..)
  , GPUCullMode(..)
  , GPUFrontFace(..)
    -- Bind group types
  , GPUBindGroupLayoutDescriptor
  , GPUBindGroupDescriptor
  , GPUBindGroupLayoutEntry
  , GPUBindGroupEntry
  , GPUBufferBindingType(..)
  , GPUShaderStage(..)
    -- Render pass types
  , GPURenderPassDescriptor
  , GPURenderPassColorAttachment
  , GPURenderPassDepthStencilAttachment
  , GPULoadOp(..)
  , GPUStoreOp(..)
    -- Draw types
  , DrawCall(..)
  , DrawIndexedCall(..)
  , DrawIndirectCall(..)
  ) where
```

**Key Design Decisions:**
- All types are pure PureScript records/ADTs
- No `foreign import data` here — those live in Device.purs
- Complete coverage of WebGPU spec vocabulary
- Explicit constructors for all enums (no strings)

### 2. Device.purs — GPU Device Initialization

The **only** FFI boundary for WebGPU. Everything else is pure.

```purescript
module Hydrogen.GPU.WebGPU.Device
  ( -- Foreign types (opaque)
    GPUDevice
  , GPUAdapter
  , GPUQueue
  , GPUCanvasContext
    -- Initialization
  , requestAdapter
  , requestDevice
  , configureCanvas
    -- Device queries
  , getLimits
  , getFeatures
  , hasFeature
    -- Error handling
  , DeviceError(..)
  , onUncapturedError
  , onDeviceLost
  ) where

import Effect (Effect)
import Effect.Aff (Aff)
import Data.Either (Either)

-- | Request a GPU adapter. May fail if WebGPU unavailable.
requestAdapter :: GPUAdapterDescriptor -> Aff (Either DeviceError GPUAdapter)

-- | Request a device from an adapter. May fail on limits.
requestDevice :: GPUAdapter -> GPUDeviceDescriptor -> Aff (Either DeviceError GPUDevice)

-- | Configure a canvas for WebGPU rendering.
configureCanvas :: GPUDevice -> CanvasElement -> GPUCanvasConfiguration -> Effect GPUCanvasContext

-- | Get device limits (max texture size, max bind groups, etc.)
getLimits :: GPUDevice -> GPULimits

-- | Check if device supports a feature.
hasFeature :: GPUDevice -> GPUFeatureName -> Boolean
```

**FFI Surface:**
```javascript
// Device.js — THE ONLY JAVASCRIPT IN THE RUNTIME
export const requestAdapterImpl = () => navigator.gpu.requestAdapter();
export const requestDeviceImpl = (adapter) => (desc) => adapter.requestDevice(desc);
export const configureCanvasImpl = (device) => (canvas) => (config) => () => {
  const ctx = canvas.getContext('webgpu');
  ctx.configure({ device, ...config });
  return ctx;
};
```

**Why Minimal FFI:**
- Fewer JavaScript lines = fewer bugs
- Pure PureScript handles all data transformation
- FFI is auditable (one small file)

### 3. Buffer.purs — Buffer Management

Pure buffer operations. The runtime manages GPU memory.

```purescript
module Hydrogen.GPU.WebGPU.Buffer
  ( -- Buffer creation
    createBuffer
  , createVertexBuffer
  , createIndexBuffer
  , createUniformBuffer
  , createStorageBuffer
    -- Buffer operations
  , writeBuffer
  , readBuffer
  , mapBuffer
  , unmapBuffer
  , destroyBuffer
    -- Typed buffer helpers
  , Float32Buffer
  , Uint16Buffer
  , Uint32Buffer
  , createFloat32Buffer
  , createUint16Buffer
  , createUint32Buffer
    -- Buffer pools (reuse)
  , BufferPool
  , createPool
  , allocateFromPool
  , releaseToPool
  , flushPool
  ) where

-- | Create a buffer with specific usage flags.
createBuffer :: GPUDevice -> GPUBufferDescriptor -> Effect GPUBuffer

-- | Write data to a buffer (mapped or via queue).
writeBuffer :: GPUDevice -> GPUBuffer -> Int -> ArrayBuffer -> Effect Unit

-- | Create a buffer pool for efficient reuse.
-- | Pools eliminate allocation overhead in render loops.
createPool :: GPUDevice -> GPUBufferUsage -> Int -> Effect BufferPool

-- | Allocate a buffer from the pool. Returns existing if available.
allocateFromPool :: BufferPool -> Int -> Effect GPUBuffer
```

**Buffer Pool Strategy:**
```
Frame N:
  [Buffer A: in use] [Buffer B: in use] [Buffer C: free]
  
Frame N+1:
  [Buffer A: free] [Buffer B: free] [Buffer C: in use]
  
No allocations after warmup — all buffers recycled.
```

### 4. Texture.purs — Texture Management

```purescript
module Hydrogen.GPU.WebGPU.Texture
  ( -- Texture creation
    createTexture
  , createTextureFromImage
  , createDepthTexture
  , createRenderTexture
    -- Texture operations
  , writeTexture
  , copyTextureToTexture
  , copyTextureToBuffer
    -- Texture views
  , createTextureView
  , createCubeMapView
  , createArrayView
    -- Texture atlas
  , TextureAtlas
  , createAtlas
  , allocateRegion
  , uploadToRegion
  , getRegionUV
    -- Mipmaps
  , generateMipmaps
  ) where

-- | Texture atlas for efficient batching.
-- | Stores multiple images in one texture, returns UV coordinates.
type TextureAtlas =
  { texture :: GPUTexture
  , regions :: Map AtlasRegionId AtlasRegion
  , allocator :: BinPacker
  }

-- | Allocate a region in the atlas. Returns UV bounds.
allocateRegion :: TextureAtlas -> Size2D -> Effect (Maybe AtlasRegionId)
```

### 5. Shader.purs — WGSL Shader Compilation

Shaders are **pure data** — WGSL source strings composed from templates.

```purescript
module Hydrogen.GPU.WebGPU.Shader
  ( -- Shader modules
    createShaderModule
  , ShaderModule
    -- Shader source (pure data)
  , WGSLSource
  , vertexShader
  , fragmentShader
    -- Shader composition
  , ShaderTemplate
  , applyTemplate
    -- Built-in shaders
  , basicVertexShader
  , basicFragmentShader
  , pbrVertexShader
  , pbrFragmentShader
  , shadowVertexShader
  , shadowFragmentShader
  , pickVertexShader
  , pickFragmentShader
  , sdfTextVertexShader
  , sdfTextFragmentShader
  ) where

-- | WGSL source code (pure String wrapper for type safety)
newtype WGSLSource = WGSLSource String

-- | Basic unlit shader
basicVertexShader :: WGSLSource
basicVertexShader = WGSLSource """
struct Uniforms {
  viewProjection: mat4x4<f32>,
  model: mat4x4<f32>,
}

@group(0) @binding(0) var<uniform> uniforms: Uniforms;

struct VertexInput {
  @location(0) position: vec3<f32>,
  @location(1) normal: vec3<f32>,
  @location(2) uv: vec2<f32>,
}

struct VertexOutput {
  @builtin(position) position: vec4<f32>,
  @location(0) normal: vec3<f32>,
  @location(1) uv: vec2<f32>,
}

@vertex
fn main(input: VertexInput) -> VertexOutput {
  var output: VertexOutput;
  output.position = uniforms.viewProjection * uniforms.model * vec4<f32>(input.position, 1.0);
  output.normal = (uniforms.model * vec4<f32>(input.normal, 0.0)).xyz;
  output.uv = input.uv;
  return output;
}
"""

-- | PBR metallic-roughness fragment shader
pbrFragmentShader :: WGSLSource
pbrFragmentShader = WGSLSource """
// ... full PBR implementation with:
// - GGX normal distribution
// - Smith geometry function  
// - Fresnel-Schlick approximation
// - Cook-Torrance BRDF
// - IBL (image-based lighting)
// - Shadow sampling
"""
```

**Shader as Pure Data:**
- Shaders are WGSL strings embedded in PureScript
- No runtime shader compilation from external files
- Type-safe template composition
- Same shader = same output (deterministic)

### 6. Pipeline.purs — Render Pipeline Creation

```purescript
module Hydrogen.GPU.WebGPU.Pipeline
  ( -- Pipeline creation
    createRenderPipeline
  , createComputePipeline
    -- Pipeline layouts
  , createPipelineLayout
  , createBindGroupLayout
    -- Cached pipelines
  , PipelineCache
  , createPipelineCache
  , getPipeline
  , getPipelineByMaterial
    -- Standard pipelines
  , basicPipeline
  , pbrPipeline
  , shadowPipeline
  , pickPipeline
  , sdfTextPipeline
  , wireframePipeline
  ) where

-- | Pipeline cache key based on material properties.
-- | Same material properties = same pipeline (reuse).
data PipelineKey
  = BasicPipelineKey BasicMaterialKey
  | PBRPipelineKey PBRMaterialKey
  | ShadowPipelineKey
  | PickPipelineKey
  | WireframePipelineKey

-- | Get or create a pipeline from cache.
getPipeline :: PipelineCache -> PipelineKey -> Effect GPURenderPipeline
```

**Pipeline Caching Strategy:**
```
Material properties → PipelineKey → Hash → Cache lookup
                                         ↓
                               Cache hit? → Return cached pipeline
                                         ↓
                               Cache miss? → Create, cache, return
```

### 7. BindGroup.purs — Resource Binding

```purescript
module Hydrogen.GPU.WebGPU.BindGroup
  ( -- Bind group creation
    createBindGroup
  , createBindGroupLayout
    -- Standard layouts
  , frameBindGroupLayout      -- Group 0: camera, scene globals
  , materialBindGroupLayout   -- Group 1: material properties
  , objectBindGroupLayout     -- Group 2: per-object transforms
  , lightBindGroupLayout      -- Group 3: lighting data
    -- Bind group builders
  , BindGroupBuilder
  , newBindGroupBuilder
  , addUniformBuffer
  , addStorageBuffer
  , addTexture
  , addSampler
  , buildBindGroup
  ) where

-- | Bind group layout for frame-level uniforms.
-- | Updated once per frame.
frameBindGroupLayout :: GPUBindGroupLayoutDescriptor
frameBindGroupLayout =
  { entries:
      [ { binding: 0
        , visibility: GPUShaderStage.Vertex <> GPUShaderStage.Fragment
        , buffer: { type: GPUBufferBindingType.Uniform }
        }
      ]
  , label: Just "Frame Uniforms"
  }

-- | Frame uniforms structure (matches WGSL)
type FrameUniforms =
  { viewMatrix :: Mat4
  , projectionMatrix :: Mat4
  , viewProjectionMatrix :: Mat4
  , cameraPosition :: Vec3 Number
  , time :: Number
  , padding :: Number  -- Alignment
  }
```

### 8. Pass.purs — Render Pass Encoding

```purescript
module Hydrogen.GPU.WebGPU.Pass
  ( -- Pass types
    RenderPass
  , ShadowPass
  , PickPass
    -- Pass creation
  , beginRenderPass
  , beginShadowPass
  , beginPickPass
  , endPass
    -- Pass operations
  , setPipeline
  , setBindGroup
  , setVertexBuffer
  , setIndexBuffer
  , draw
  , drawIndexed
  , drawInstanced
    -- Multi-pass rendering
  , PassSequence
  , shadowThenColor
  , colorThenPick
  , fullSequence
  ) where

-- | Full render sequence for a frame.
-- | Shadow → Color → Pick (if needed)
fullSequence :: Scene3D msg -> GPUDevice -> Effect (CommandBuffer msg)
fullSequence scene device = do
  -- Shadow pass (for shadow-casting lights)
  shadowCommands <- for scene.lights \light ->
    when (lightCastsShadow light) $
      renderShadowPass device scene light
      
  -- Color pass (main render)
  colorCommands <- renderColorPass device scene
  
  -- Pick pass (if any interactive meshes)
  pickCommands <- when (hasPickTargets scene) $
    renderPickPass device scene
    
  pure $ concat [shadowCommands, colorCommands, pickCommands]
```

### 9. Render.purs — Command Dispatch

The core interpreter. Consumes pure data, emits GPU commands.

```purescript
module Hydrogen.GPU.WebGPU.Render
  ( -- Main entry point
    render
  , renderFrame
    -- Render targets
  , RenderTarget
  , canvasTarget
  , textureTarget
    -- Render context (read-only state)
  , RenderContext
  , createContext
    -- Low-level dispatch
  , dispatchDrawCommand
  , dispatchCommandBuffer
  ) where

-- | Render a Scene3D to a target.
-- | This is the main entry point.
render :: forall msg. GPUDevice -> RenderTarget -> Scene3D msg -> Effect Unit

-- | Render context contains GPU resources but NO mutable state.
-- | Created once, reused every frame.
type RenderContext =
  { device :: GPUDevice
  , pipelineCache :: PipelineCache
  , bufferPool :: BufferPool
  , textureAtlas :: TextureAtlas
  , bindGroupCache :: BindGroupCache
  }

-- | Render a single frame.
renderFrame :: forall msg. RenderContext -> Scene3D msg -> Effect FrameResult

-- | Dispatch a DrawCommand to the GPU.
dispatchDrawCommand :: RenderContext -> GPURenderPassEncoder -> DrawCommand msg -> Effect Unit
dispatchDrawCommand ctx encoder cmd = case cmd of
  DrawRect params -> do
    setPipeline encoder ctx.rectPipeline
    setBindGroup encoder 0 (rectBindGroup ctx params)
    draw encoder 6 1 0 0  -- Two triangles
    
  DrawMesh params -> do
    let pipelineKey = materialToPipelineKey params.material
    pipeline <- getPipeline ctx.pipelineCache pipelineKey
    setPipeline encoder pipeline
    setBindGroup encoder 0 ctx.frameBindGroup
    setBindGroup encoder 1 (materialBindGroup ctx params.material)
    setBindGroup encoder 2 (objectBindGroup ctx params)
    setVertexBuffer encoder 0 (meshVertexBuffer ctx params.geometry)
    setIndexBuffer encoder (meshIndexBuffer ctx params.geometry) GPUIndexFormat.Uint16
    drawIndexed encoder (meshIndexCount params.geometry) 1 0 0 0
    
  -- ... other commands
```

### 10. Pick.purs — GPU-Based Hit Testing

```purescript
module Hydrogen.GPU.WebGPU.Pick
  ( -- Pick buffer
    PickBuffer
  , createPickBuffer
  , renderToPickBuffer
  , readPickId
    -- Pick result
  , PickResult(..)
  , pickAt
  ) where

-- | Pick buffer for GPU-based hit testing.
type PickBuffer =
  { texture :: GPUTexture
  , readbackBuffer :: GPUBuffer
  , width :: Int
  , height :: Int
  }

-- | Render scene to pick buffer (color-coded IDs).
renderToPickBuffer :: RenderContext -> PickBuffer -> Scene3D msg -> Effect Unit

-- | Read pick ID at screen coordinates.
-- | Returns the PickId3D of the mesh at (x, y), or Nothing.
readPickId :: PickBuffer -> Int -> Int -> Aff (Maybe PickId3D)

-- | Complete pick operation: render + read.
pickAt :: RenderContext -> Scene3D msg -> Int -> Int -> Aff (Maybe msg)
pickAt ctx scene x y = do
  renderToPickBuffer ctx ctx.pickBuffer scene
  maybePickId <- readPickId ctx.pickBuffer x y
  pure $ maybePickId >>= \pickId ->
    findMsgByPickId scene pickId
```

---

## Scene3D Rendering Pipeline

### Geometry Generation (Scene3D/Geometry.purs)

Procedural mesh generation from Mesh3D types.

```purescript
module Hydrogen.GPU.WebGPU.Scene3D.Geometry
  ( -- Mesh generation
    generateMesh
  , MeshData
    -- Primitive generators
  , generateBox
  , generateSphere
  , generateCylinder
  , generateCone
  , generatePlane
  , generateTorus
  , generateTorusKnot
  , generateCapsule
  , generateIcosahedron
  , generateOctahedron
  , generateTetrahedron
  , generateDodecahedron
  , generateLathe
  , generateExtrude
    -- Buffer conversion
  , meshDataToBuffers
  ) where

-- | Generated mesh data (pure)
type MeshData =
  { positions :: Array (Vec3 Number)
  , normals :: Array (Vec3 Number)
  , uvs :: Array (Vec2 Number)
  , indices :: Array Int
  , tangents :: Maybe (Array (Vec4 Number))
  }

-- | Generate mesh data from Mesh3D.
generateMesh :: Mesh3D -> MeshData
generateMesh = case _ of
  BoxMesh3D params -> generateBox params
  SphereMesh3D params -> generateSphere params
  CylinderMesh3D params -> generateCylinder params
  -- ... all 17 mesh types

-- | Generate box geometry.
-- | 24 vertices (4 per face, unique normals)
-- | 36 indices (2 triangles per face)
generateBox :: BoxMeshParams -> MeshData
generateBox { width, height, depth, widthSegments, heightSegments, depthSegments } =
  let
    hw = unwrapMeter width / 2.0
    hh = unwrapMeter height / 2.0
    hd = unwrapMeter depth / 2.0
    
    -- Generate each face with proper normals
    front  = generateFace (vec3 0.0 0.0 1.0) hw hh hd widthSegments heightSegments
    back   = generateFace (vec3 0.0 0.0 (-1.0)) hw hh (-hd) widthSegments heightSegments
    top    = generateFace (vec3 0.0 1.0 0.0) hw hh hd widthSegments depthSegments
    bottom = generateFace (vec3 0.0 (-1.0) 0.0) hw (-hh) hd widthSegments depthSegments
    right  = generateFace (vec3 1.0 0.0 0.0) hw hh hd heightSegments depthSegments
    left   = generateFace (vec3 (-1.0) 0.0 0.0) (-hw) hh hd heightSegments depthSegments
  in
    combineMeshData [front, back, top, bottom, right, left]

-- | Generate UV sphere geometry.
-- | Vertices: (widthSegments + 1) * (heightSegments + 1)
-- | Triangles: widthSegments * heightSegments * 2
generateSphere :: SphereMeshParams -> MeshData
generateSphere { radius, widthSegments, heightSegments, phiStart, phiLength, thetaStart, thetaLength } =
  -- ... spherical coordinate generation
```

### Material Compilation (Scene3D/Material.purs)

```purescript
module Hydrogen.GPU.WebGPU.Scene3D.Material
  ( -- Material → Pipeline
    materialToPipelineKey
  , materialToBindGroup
    -- Uniform buffer data
  , BasicMaterialUniforms
  , PBRMaterialUniforms
  , PhysicalMaterialUniforms
    -- Uniform serialization
  , serializeBasicMaterial
  , serializePBRMaterial
  , serializePhysicalMaterial
  ) where

-- | PBR material uniforms (matches WGSL struct)
type PBRMaterialUniforms =
  { baseColor :: Vec4 Number      -- RGBA (premultiplied alpha)
  , emissive :: Vec3 Number       -- RGB emission
  , emissiveIntensity :: Number
  , roughness :: Number           -- [0, 1]
  , metalness :: Number           -- [0, 1]
  , opacity :: Number             -- [0, 1]
  , padding :: Number             -- 16-byte alignment
  }

-- | Serialize material to uniform buffer bytes.
serializePBRMaterial :: StandardMaterialParams -> ArrayBuffer
serializePBRMaterial params =
  let
    uniforms =
      { baseColor: rgbaToVec4 params.color
      , emissive: rgbToVec3 params.emissive
      , emissiveIntensity: params.emissiveIntensity
      , roughness: clamp 0.0 1.0 params.roughness
      , metalness: clamp 0.0 1.0 params.metalness
      , opacity: params.opacity
      , padding: 0.0
      }
  in
    serializeToFloat32Array uniforms
```

### Light Data (Scene3D/Light.purs)

```purescript
module Hydrogen.GPU.WebGPU.Scene3D.Light
  ( -- Light → Uniforms
    lightToUniform
  , lightsToUniformBuffer
    -- Light structures
  , LightUniform
  , LightArrayUniform
    -- Shadow mapping
  , lightShadowMatrix
  , createShadowMap
  ) where

-- | Light uniform structure (matches WGSL)
-- | 64 bytes per light, std140 layout
type LightUniform =
  { color :: Vec4 Number          -- RGB + intensity
  , position :: Vec4 Number       -- XYZ + type
  , direction :: Vec4 Number      -- XYZ + padding
  , params :: Vec4 Number         -- distance, decay, angle, penumbra
  }

-- | Light type encoding (in position.w)
lightTypeCode :: Light3D -> Number
lightTypeCode = case _ of
  AmbientLight3D _ -> 0.0
  DirectionalLight3D _ -> 1.0
  PointLight3D _ -> 2.0
  SpotLight3D _ -> 3.0
  HemisphereLight3D _ -> 4.0

-- | Convert Light3D to uniform data.
lightToUniform :: Light3D -> LightUniform
lightToUniform = case _ of
  DirectionalLight3D params ->
    { color: vec4 (channelToNumber params.color.r) 
                  (channelToNumber params.color.g)
                  (channelToNumber params.color.b)
                  params.intensity
    , position: vec4 0.0 0.0 0.0 1.0  -- type = directional
    , direction: vec4 (unwrapMeter params.direction.x)
                      (unwrapMeter params.direction.y)
                      (unwrapMeter params.direction.z)
                      0.0
    , params: vec4 0.0 0.0 0.0 0.0
    }
  -- ... other light types
```

### Scene3D Render (Scene3D/Render.purs)

The complete interpreter.

```purescript
module Hydrogen.GPU.WebGPU.Scene3D.Render
  ( -- Main render function
    renderScene3D
    -- Render phases
  , renderShadowPhase
  , renderColorPhase
  , renderPickPhase
    -- Frame management
  , beginFrame
  , endFrame
  ) where

-- | Render a complete Scene3D.
-- | This is the main entry point for 3D rendering.
renderScene3D :: forall msg. RenderContext -> RenderTarget -> Scene3D msg -> Effect (RenderResult msg)
renderScene3D ctx target scene = do
  -- 1. Update frame uniforms
  updateFrameUniforms ctx scene.camera
  
  -- 2. Upload light data
  uploadLights ctx scene.lights
  
  -- 3. Sort meshes for optimal batching
  let sortedMeshes = sortByMaterial scene.meshes
  
  -- 4. Shadow pass (for shadow-casting lights)
  for_ (shadowCastingLights scene.lights) \light -> do
    renderShadowPass ctx light sortedMeshes
    
  -- 5. Color pass
  encoder <- createCommandEncoder ctx.device
  colorPass <- beginRenderPass encoder target scene.background
  
  -- 5a. Set frame-level bind group
  setBindGroup colorPass 0 ctx.frameBindGroup
  setBindGroup colorPass 3 ctx.lightBindGroup
  
  -- 5b. Render all meshes, batched by material
  renderMeshes ctx colorPass sortedMeshes
  
  endPass colorPass
  
  -- 6. Submit commands
  commandBuffer <- finishEncoder encoder
  submit ctx.device.queue [commandBuffer]
  
  pure { pickMap: buildPickMap sortedMeshes }

-- | Render meshes with optimal batching.
-- | Minimizes state changes by grouping by material.
renderMeshes :: RenderContext -> GPURenderPassEncoder -> Array (MeshParams msg) -> Effect Unit
renderMeshes ctx pass meshes = do
  -- Group by material for batching
  let groups = groupBy (\a b -> materialKey a.material == materialKey b.material) meshes
  
  for_ groups \group -> do
    -- Set pipeline once per material group
    let materialParams = (head group).material
    pipeline <- getPipelineForMaterial ctx materialParams
    setPipeline pass pipeline
    
    -- Set material bind group once per group
    materialBindGroup <- getMaterialBindGroup ctx materialParams
    setBindGroup pass 1 materialBindGroup
    
    -- Render each mesh in the group
    for_ group \mesh -> do
      -- Set per-object bind group
      objectBindGroup <- getObjectBindGroup ctx mesh
      setBindGroup pass 2 objectBindGroup
      
      -- Bind geometry
      geometry <- getGeometryBuffers ctx mesh.geometry
      setVertexBuffer pass 0 geometry.vertexBuffer
      setIndexBuffer pass geometry.indexBuffer GPUIndexFormat.Uint16
      
      -- Draw
      drawIndexed pass geometry.indexCount 1 0 0 0
```

---

## Typography Rendering

### SDF Font Atlas (Typography/Atlas.purs)

```purescript
module Hydrogen.GPU.WebGPU.Typography.Atlas
  ( -- Font atlas
    FontAtlas
  , createFontAtlas
  , uploadGlyph
  , getGlyphUV
    -- Atlas management
  , AtlasPage
  , createPage
  , packGlyph
  ) where

-- | SDF font atlas using multi-channel signed distance fields.
type FontAtlas =
  { pages :: Array AtlasPage
  , glyphMap :: Map (FontId /\ GlyphId) GlyphRegion
  , texture :: GPUTexture
  , sampler :: GPUSampler
  }

-- | Get UV coordinates for a glyph.
getGlyphUV :: FontAtlas -> FontId -> GlyphId -> Maybe GlyphUV
```

### Path Tessellation (Typography/Tessellation.purs)

```purescript
module Hydrogen.GPU.WebGPU.Typography.Tessellation
  ( -- Path → Triangles
    tessellatePath
  , tessellateGlyphPath
    -- Tessellation options
  , TessellationOptions
  , defaultOptions
    -- Output
  , TessellatedPath
  ) where

-- | Tessellate a path into triangles.
-- | Uses ear clipping for simple polygons, constrained Delaunay for complex.
tessellatePath :: TessellationOptions -> Path -> TessellatedPath

-- | Tessellated output ready for GPU.
type TessellatedPath =
  { vertices :: Array (Vec2 Number)
  , indices :: Array Int
  }
```

---

## Bind Group Layout

The runtime uses a fixed bind group layout for consistency:

```
Group 0: Frame Uniforms (per-frame)
├── binding 0: Camera matrices (uniform buffer)
│   └── viewMatrix, projectionMatrix, viewProjectionMatrix, cameraPosition, time
└── binding 1: Scene globals (uniform buffer)
    └── ambientColor, fogColor, fogNear, fogFar

Group 1: Material Uniforms (per-material)
├── binding 0: Material properties (uniform buffer)
│   └── baseColor, roughness, metalness, emissive, opacity, ...
├── binding 1: Albedo texture (optional)
├── binding 2: Normal map (optional)
├── binding 3: Metallic/Roughness texture (optional)
└── binding 4: Sampler

Group 2: Object Uniforms (per-draw-call)
├── binding 0: Transform matrices (uniform buffer)
│   └── modelMatrix, normalMatrix
└── binding 1: Pick ID (uniform buffer)
    └── pickId

Group 3: Lighting (per-frame)
├── binding 0: Light array (storage buffer, read-only)
│   └── lights[MAX_LIGHTS], numLights, ambientColor
├── binding 1: Shadow map array (texture array)
├── binding 2: Shadow sampler (comparison sampler)
└── binding 3: Light matrices (storage buffer)
    └── lightSpaceMatrices[MAX_SHADOW_LIGHTS]
```

---

## Implementation Order

### Phase 1: Foundation (2-3 days)

1. **Types.purs** — Complete WebGPU type vocabulary
2. **Device.purs** — FFI for device initialization
3. **Buffer.purs** — Basic buffer management

### Phase 2: Basic Rendering (3-4 days)

4. **Shader.purs** — WGSL shaders (basic vertex/fragment)
5. **Pipeline.purs** — Render pipeline creation
6. **BindGroup.purs** — Resource binding
7. **Pass.purs** — Render pass encoding
8. **Render.purs** — Basic command dispatch

### Phase 3: Scene3D (4-5 days)

9. **Scene3D/Geometry.purs** — All 17 mesh generators
10. **Scene3D/Material.purs** — Material → shader/uniforms
11. **Scene3D/Light.purs** — Light data handling
12. **Scene3D/Render.purs** — Complete Scene3D interpreter

### Phase 4: Interaction (2-3 days)

13. **Pick.purs** — GPU-based hit testing

### Phase 5: Typography (3-4 days)

14. **Typography/Atlas.purs** — SDF font atlas
15. **Typography/Tessellation.purs** — Path tessellation
16. **Typography/Glyph.purs** — Glyph rendering

### Phase 6: Polish (2-3 days)

17. **Buffer pools** — Memory reuse
18. **Pipeline cache** — Eliminate redundant compilations
19. **Batching optimization** — Minimize draw calls

---

## Performance Targets

| Metric | Target | Notes |
|--------|--------|-------|
| Draw calls per frame | < 1000 | Via batching |
| State changes | < 100 | Via sorting by material |
| Buffer uploads | < 50 | Via pooling/caching |
| Frame time | < 16ms | 60 FPS |
| Memory overhead | < 50MB | For typical scene |

---

## What Gets Deleted

Once the WebGPU runtime is complete, we delete:

| File | Lines | Reason |
|------|-------|--------|
| `ThreeD/Scene.purs` | 1,559 | Three.js wrapper |
| `ThreeD/Scene.js` | 852 | FFI bindings |
| `ThreeD/Canvas3D.purs` | 636 | Three.js wrapper |
| `ThreeD/Canvas3D.js` | 621 | FFI bindings |
| `ThreeD/Model.purs` | 533 | GLTF via Three.js |
| `ThreeD/Model.js` | 638 | FFI bindings |
| **Total** | **4,839** | All Three.js code |

Replaced by ~3,000 lines of pure PureScript + ~100 lines of FFI.

---

## Summary

The WebGPU runtime is a **minimal interpreter** that:
1. Takes pure data (`Scene3D msg`, `CommandBuffer msg`)
2. Produces GPU commands deterministically
3. Has **one small FFI file** (`Device.js`, ~50 lines)
4. Everything else is **pure PureScript**

At billion-agent scale, this architecture ensures:
- **Determinism**: Same input → same output, always
- **Composability**: Types compose algebraically
- **Verifiability**: Lean4 proofs apply to the data layer
- **Efficiency**: Batching, pooling, caching — all pure

The Three.js wrapper (4,839 lines of JavaScript-infected code) gets replaced by a clean, typed, provable system.

---

*"The matrix has its roots in primitive arcade games, in early graphics programs and military experimentation with cranial jacks."*

— Neuromancer

---

Document Status: **DESIGN COMPLETE — Ready for Implementation**
Last Updated: 2026-02-24
