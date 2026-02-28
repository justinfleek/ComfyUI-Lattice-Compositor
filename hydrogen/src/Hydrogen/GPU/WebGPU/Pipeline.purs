-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // gpu // webgpu // pipeline
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Render pipeline construction — pure data describing GPU pipeline state.
--
-- Pipelines are expensive to create, so we cache them by key.
-- Same material properties = same pipeline = cache hit.
--
-- BIND GROUP LAYOUT:
-- - Group 0: Frame uniforms (camera, time, globals)
-- - Group 1: Material uniforms (color, roughness, etc.)
-- - Group 2: Object uniforms (model matrix, normal matrix)
-- - Group 3: Light uniforms (light array, ambient)
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Pipeline
  ( -- Pipeline keys (pure data)
    PipelineKey
      ( BasicPipelineKey
      , PBRPipelineKey
      , ShadowPipelineKey
      , PickPipelineKey
      , SkyboxPipelineKey
      , WireframePipelineKey
      , SDFTextPipelineKey
      )
    -- Material keys
  , BasicMaterialKey
  , PBRMaterialKey
    -- Pipeline descriptors (pure data)
  , basicPipelineDescriptor
  , pbrPipelineDescriptor
  , shadowPipelineDescriptor
  , pickPipelineDescriptor
  , skyboxPipelineDescriptor
  , wireframePipelineDescriptor
  , sdfTextPipelineDescriptor
    -- Bind group layouts (pure data)
  , frameBindGroupLayout
  , materialBindGroupLayout
  , objectBindGroupLayout
  , lightBindGroupLayout
    -- Vertex buffer layouts
  , standardVertexLayout
  , positionOnlyVertexLayout
  , textVertexLayout
    -- Utilities
  , pipelineKeyFromMaterial
  ) where

import Prelude
  ( class Eq
  , class Ord
  , compare
  , negate
  , (==)
  , (&&)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.GPU.Scene3D.Material
  ( Material3D
      ( BasicMaterial3D
      , StandardMaterial3D
      , PhysicalMaterial3D
      )
  )
import Hydrogen.GPU.WebGPU.Types
  ( GPURenderPipelineDescriptor
  , GPUVertexState
  , GPUFragmentState
  , GPUPrimitiveState
  , GPUDepthStencilState
  , GPUMultisampleState
  , GPUVertexBufferLayout
  , GPUVertexAttribute
  , GPUVertexFormat
      ( Float32x2
      , Float32x3
      , Float32x4
      )
  , GPUVertexStepMode(StepVertex)
  , GPUPrimitiveTopology(TriangleList)
  , GPUCullMode(CullBack, CullNone)
  , GPUFrontFace(FrontCCW)
  , GPUTextureFormat(BGRA8Unorm, Depth24PlusStencil8, R8Unorm, RGBA8Uint)
  , GPUCompareFunction(CompareLess, CompareAlways)
  , GPUStencilOperation(StencilKeep)
  , GPUBlendState
  , GPUBlendComponent
  , GPUBlendFactor(BlendOne, BlendZero, BlendSrcAlpha, BlendOneMinusSrcAlpha)
  , GPUBlendOperation(BlendAdd)
  , GPUColorWriteMask(WriteAll)
  , GPUColorTargetState
  , GPUBindGroupLayoutDescriptor
  , GPUBindGroupLayoutEntry
  , GPUBufferBindingType(BufferUniform)
  , GPUShaderStage(StageVertex, StageFragment)
  )


-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- PIPELINE KEYS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pipeline cache key. Same key = same pipeline.
-- | Used for O(1) pipeline lookup at render time.
data PipelineKey
  = BasicPipelineKey BasicMaterialKey
  | PBRPipelineKey PBRMaterialKey
  | ShadowPipelineKey
  | PickPipelineKey
  | SkyboxPipelineKey
  | WireframePipelineKey
  | SDFTextPipelineKey

derive instance eqPipelineKey :: Eq PipelineKey
derive instance ordPipelineKey :: Ord PipelineKey

-- | Key for basic (unlit) materials.
-- | Only transparency affects pipeline state.
type BasicMaterialKey =
  { transparent :: Boolean
  , wireframe :: Boolean
  }

-- | Key for PBR materials.
-- | Transparency and double-sided affect pipeline state.
type PBRMaterialKey =
  { transparent :: Boolean
  , doubleSided :: Boolean
  }

-- | Derive pipeline key from material.
pipelineKeyFromMaterial :: Material3D -> PipelineKey
pipelineKeyFromMaterial = case _ of
  BasicMaterial3D params ->
    BasicPipelineKey
      { transparent: params.transparent
      , wireframe: params.wireframe
      }
  StandardMaterial3D params ->
    PBRPipelineKey
      { transparent: params.transparent
      , doubleSided: false
      }
  PhysicalMaterial3D params ->
    PBRPipelineKey
      { transparent: params.transparent
      , doubleSided: false
      }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- VERTEX BUFFER LAYOUTS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Standard vertex layout: position, normal, UV, tangent.
-- | Total stride: 12 + 12 + 8 + 16 = 48 bytes
standardVertexLayout :: GPUVertexBufferLayout
standardVertexLayout =
  { arrayStride: 48
  , stepMode: StepVertex
  , attributes:
      [ { format: Float32x3, offset: 0, shaderLocation: 0 }   -- position
      , { format: Float32x3, offset: 12, shaderLocation: 1 }  -- normal
      , { format: Float32x2, offset: 24, shaderLocation: 2 }  -- uv
      , { format: Float32x4, offset: 32, shaderLocation: 3 }  -- tangent
      ]
  }

-- | Position-only vertex layout (for shadow/pick passes).
-- | Total stride: 12 bytes
positionOnlyVertexLayout :: GPUVertexBufferLayout
positionOnlyVertexLayout =
  { arrayStride: 12
  , stepMode: StepVertex
  , attributes:
      [ { format: Float32x3, offset: 0, shaderLocation: 0 }   -- position
      ]
  }

-- | Text vertex layout: position, UV.
-- | Total stride: 12 + 8 = 20 bytes
textVertexLayout :: GPUVertexBufferLayout
textVertexLayout =
  { arrayStride: 20
  , stepMode: StepVertex
  , attributes:
      [ { format: Float32x3, offset: 0, shaderLocation: 0 }   -- position
      , { format: Float32x2, offset: 12, shaderLocation: 1 }  -- uv
      ]
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- BIND GROUP LAYOUTS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Group 0: Frame-level uniforms.
-- | Updated once per frame.
-- | Contains: viewProjection, cameraPosition, time
frameBindGroupLayout :: GPUBindGroupLayoutDescriptor
frameBindGroupLayout =
  { entries:
      [ uniformBufferEntry 0 [StageVertex, StageFragment]
      ]
  , label: Just "Frame Uniforms"
  }

-- | Group 1: Material uniforms.
-- | Updated per material.
-- | Contains: baseColor, metallic, roughness, emissive, etc.
materialBindGroupLayout :: GPUBindGroupLayoutDescriptor
materialBindGroupLayout =
  { entries:
      [ uniformBufferEntry 0 [StageVertex, StageFragment]
      ]
  , label: Just "Material Uniforms"
  }

-- | Group 2: Object uniforms.
-- | Updated per draw call.
-- | Contains: model matrix, normal matrix
objectBindGroupLayout :: GPUBindGroupLayoutDescriptor
objectBindGroupLayout =
  { entries:
      [ uniformBufferEntry 0 [StageVertex]
      ]
  , label: Just "Object Uniforms"
  }

-- | Group 3: Light uniforms.
-- | Updated when lights change.
-- | Contains: ambient color, light array
lightBindGroupLayout :: GPUBindGroupLayoutDescriptor
lightBindGroupLayout =
  { entries:
      [ uniformBufferEntry 0 [StageFragment]
      ]
  , label: Just "Light Uniforms"
  }

-- Helper to create uniform buffer entry
uniformBufferEntry :: Int -> Array GPUShaderStage -> GPUBindGroupLayoutEntry
uniformBufferEntry binding visibility =
  { binding
  , visibility
  , buffer: Just { type: BufferUniform, hasDynamicOffset: false, minBindingSize: 0 }
  , sampler: Nothing
  , texture: Nothing
  , storageTexture: Nothing
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- PIPELINE DESCRIPTORS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Basic (unlit) pipeline descriptor.
basicPipelineDescriptor :: BasicMaterialKey -> GPURenderPipelineDescriptor
basicPipelineDescriptor key =
  { label: Just "Basic Pipeline"
  , vertex: basicVertexState
  , fragment: Just (basicFragmentState key.transparent)
  , primitive: standardPrimitiveState
  , depthStencil: Just standardDepthStencilState
  , multisample: standardMultisampleState
  }

-- | PBR pipeline descriptor.
pbrPipelineDescriptor :: PBRMaterialKey -> GPURenderPipelineDescriptor
pbrPipelineDescriptor key =
  { label: Just "PBR Pipeline"
  , vertex: pbrVertexState
  , fragment: Just (pbrFragmentState key.transparent)
  , primitive: pbrPrimitiveState key.doubleSided
  , depthStencil: Just standardDepthStencilState
  , multisample: standardMultisampleState
  }

-- | Shadow map pipeline descriptor.
shadowPipelineDescriptor :: GPURenderPipelineDescriptor
shadowPipelineDescriptor =
  { label: Just "Shadow Pipeline"
  , vertex: shadowVertexState
  , fragment: Nothing  -- Depth-only, no fragment output
  , primitive: standardPrimitiveState
  , depthStencil: Just shadowDepthStencilState
  , multisample: noMultisampleState
  }

-- | GPU picking pipeline descriptor.
pickPipelineDescriptor :: GPURenderPipelineDescriptor
pickPipelineDescriptor =
  { label: Just "Pick Pipeline"
  , vertex: pickVertexState
  , fragment: Just pickFragmentState
  , primitive: standardPrimitiveState
  , depthStencil: Just standardDepthStencilState
  , multisample: noMultisampleState
  }

-- | Skybox pipeline descriptor.
skyboxPipelineDescriptor :: GPURenderPipelineDescriptor
skyboxPipelineDescriptor =
  { label: Just "Skybox Pipeline"
  , vertex: skyboxVertexState
  , fragment: Just skyboxFragmentState
  , primitive: skyboxPrimitiveState
  , depthStencil: Just skyboxDepthStencilState
  , multisample: standardMultisampleState
  }

-- | Wireframe pipeline descriptor.
wireframePipelineDescriptor :: GPURenderPipelineDescriptor
wireframePipelineDescriptor =
  { label: Just "Wireframe Pipeline"
  , vertex: wireframeVertexState
  , fragment: Just wireframeFragmentState
  , primitive: standardPrimitiveState
  , depthStencil: Just standardDepthStencilState
  , multisample: standardMultisampleState
  }

-- | SDF text pipeline descriptor.
sdfTextPipelineDescriptor :: GPURenderPipelineDescriptor
sdfTextPipelineDescriptor =
  { label: Just "SDF Text Pipeline"
  , vertex: sdfTextVertexState
  , fragment: Just sdfTextFragmentState
  , primitive: standardPrimitiveState
  , depthStencil: Just standardDepthStencilState
  , multisample: standardMultisampleState
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- VERTEX STATES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

basicVertexState :: GPUVertexState
basicVertexState =
  { entryPoint: "main"
  , buffers: [standardVertexLayout]
  , constants: []
  }

pbrVertexState :: GPUVertexState
pbrVertexState =
  { entryPoint: "main"
  , buffers: [standardVertexLayout]
  , constants: []
  }

shadowVertexState :: GPUVertexState
shadowVertexState =
  { entryPoint: "main"
  , buffers: [positionOnlyVertexLayout]
  , constants: []
  }

pickVertexState :: GPUVertexState
pickVertexState =
  { entryPoint: "main"
  , buffers: [positionOnlyVertexLayout]
  , constants: []
  }

skyboxVertexState :: GPUVertexState
skyboxVertexState =
  { entryPoint: "main"
  , buffers: [positionOnlyVertexLayout]
  , constants: []
  }

wireframeVertexState :: GPUVertexState
wireframeVertexState =
  { entryPoint: "main"
  , buffers: [standardVertexLayout]
  , constants: []
  }

sdfTextVertexState :: GPUVertexState
sdfTextVertexState =
  { entryPoint: "main"
  , buffers: [textVertexLayout]
  , constants: []
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- FRAGMENT STATES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

basicFragmentState :: Boolean -> GPUFragmentState
basicFragmentState transparent =
  { entryPoint: "main"
  , targets: [colorTarget transparent]
  , constants: []
  }

pbrFragmentState :: Boolean -> GPUFragmentState
pbrFragmentState transparent =
  { entryPoint: "main"
  , targets: [colorTarget transparent]
  , constants: []
  }

pickFragmentState :: GPUFragmentState
pickFragmentState =
  { entryPoint: "main"
  , targets: [pickColorTarget]
  , constants: []
  }

skyboxFragmentState :: GPUFragmentState
skyboxFragmentState =
  { entryPoint: "main"
  , targets: [colorTarget false]
  , constants: []
  }

wireframeFragmentState :: GPUFragmentState
wireframeFragmentState =
  { entryPoint: "main"
  , targets: [colorTarget true]
  , constants: []
  }

sdfTextFragmentState :: GPUFragmentState
sdfTextFragmentState =
  { entryPoint: "main"
  , targets: [colorTarget true]
  , constants: []
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- COLOR TARGETS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

colorTarget :: Boolean -> GPUColorTargetState
colorTarget transparent =
  { format: BGRA8Unorm
  , blend: if transparent then Just alphaBlend else Nothing
  , writeMask: [WriteAll]
  }

pickColorTarget :: GPUColorTargetState
pickColorTarget =
  { format: RGBA8Uint
  , blend: Nothing
  , writeMask: [WriteAll]
  }

alphaBlend :: GPUBlendState
alphaBlend =
  { color: alphaBlendComponent
  , alpha: alphaBlendComponent
  }

alphaBlendComponent :: GPUBlendComponent
alphaBlendComponent =
  { operation: BlendAdd
  , srcFactor: BlendSrcAlpha
  , dstFactor: BlendOneMinusSrcAlpha
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- PRIMITIVE STATES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

standardPrimitiveState :: GPUPrimitiveState
standardPrimitiveState =
  { topology: TriangleList
  , stripIndexFormat: Nothing
  , frontFace: FrontCCW
  , cullMode: CullBack
  , unclippedDepth: false
  }

pbrPrimitiveState :: Boolean -> GPUPrimitiveState
pbrPrimitiveState doubleSided =
  { topology: TriangleList
  , stripIndexFormat: Nothing
  , frontFace: FrontCCW
  , cullMode: if doubleSided then CullNone else CullBack
  , unclippedDepth: false
  }

skyboxPrimitiveState :: GPUPrimitiveState
skyboxPrimitiveState =
  { topology: TriangleList
  , stripIndexFormat: Nothing
  , frontFace: FrontCCW
  , cullMode: CullNone  -- Render inside of cube
  , unclippedDepth: false
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- DEPTH/STENCIL STATES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

standardDepthStencilState :: GPUDepthStencilState
standardDepthStencilState =
  { format: Depth24PlusStencil8
  , depthWriteEnabled: true
  , depthCompare: CompareLess
  , stencilFront: defaultStencilFace
  , stencilBack: defaultStencilFace
  , stencilReadMask: allBitsMask
  , stencilWriteMask: allBitsMask
  , depthBias: 0
  , depthBiasSlopeScale: 0.0
  , depthBiasClamp: 0.0
  }

shadowDepthStencilState :: GPUDepthStencilState
shadowDepthStencilState =
  { format: Depth24PlusStencil8
  , depthWriteEnabled: true
  , depthCompare: CompareLess
  , stencilFront: defaultStencilFace
  , stencilBack: defaultStencilFace
  , stencilReadMask: allBitsMask
  , stencilWriteMask: allBitsMask
  , depthBias: 2  -- Reduce shadow acne
  , depthBiasSlopeScale: 2.0
  , depthBiasClamp: 0.0
  }

skyboxDepthStencilState :: GPUDepthStencilState
skyboxDepthStencilState =
  { format: Depth24PlusStencil8
  , depthWriteEnabled: false  -- Don't write depth
  , depthCompare: CompareLess  -- Still test depth
  , stencilFront: defaultStencilFace
  , stencilBack: defaultStencilFace
  , stencilReadMask: allBitsMask
  , stencilWriteMask: allBitsMask
  , depthBias: 0
  , depthBiasSlopeScale: 0.0
  , depthBiasClamp: 0.0
  }

-- Default stencil face (no stencil operations)
defaultStencilFace :: { compare :: GPUCompareFunction, failOp :: GPUStencilOperation, depthFailOp :: GPUStencilOperation, passOp :: GPUStencilOperation }
defaultStencilFace =
  { compare: CompareAlways
  , failOp: StencilKeep
  , depthFailOp: StencilKeep
  , passOp: StencilKeep
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- MULTISAMPLE STATES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

standardMultisampleState :: GPUMultisampleState
standardMultisampleState =
  { count: 4
  , mask: allSamplesMask
  , alphaToCoverageEnabled: false
  }

noMultisampleState :: GPUMultisampleState
noMultisampleState =
  { count: 1
  , mask: allSamplesMask
  , alphaToCoverageEnabled: false
  }

-- All bits mask (use negate 1 which wraps to 0xFFFFFFFF in unsigned context)
allBitsMask :: Int
allBitsMask = negate 1

-- Alias for clarity in multisample context
allSamplesMask :: Int
allSamplesMask = allBitsMask
