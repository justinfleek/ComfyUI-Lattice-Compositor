-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // gpu // webgpu // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Pure PureScript types wrapping WebGPU concepts.
-- No FFI here — these are the vocabulary.
--
-- Reference: WebGPU Specification
-- https://www.w3.org/TR/webgpu/
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Types
  ( -- Adapter & Device
    GPUAdapterDescriptor
  , GPUDeviceDescriptor
  , GPUQueueDescriptor
  , GPULimits
  , GPUFeatureName(..)
  , GPUPowerPreference(..)
    -- Buffer
  , GPUBufferDescriptor
  , GPUBufferUsage(..)
  , GPUMapMode(..)
  , combineBufferUsage
  , combineMapMode
    -- Texture
  , GPUTextureDescriptor
  , GPUTextureFormat(..)
  , GPUTextureUsage(..)
  , GPUTextureDimension(..)
  , GPUTextureViewDescriptor
  , GPUTextureViewDimension(..)
  , GPUTextureAspect(..)
  , combineTextureUsage
    -- Sampler
  , GPUSamplerDescriptor
  , GPUAddressMode(..)
  , GPUFilterMode(..)
  , GPUMipmapFilterMode(..)
  , GPUCompareFunction(..)
    -- Shader
  , GPUShaderModuleDescriptor
  , WGSLSource(..)
    -- Vertex State
  , GPUVertexState
  , GPUVertexBufferLayout
  , GPUVertexAttribute
  , GPUVertexFormat(..)
  , GPUVertexStepMode(..)
    -- Primitive State
  , GPUPrimitiveState
  , GPUPrimitiveTopology(..)
  , GPUCullMode(..)
  , GPUFrontFace(..)
  , GPUIndexFormat(..)
    -- Fragment State
  , GPUFragmentState
  , GPUColorTargetState
  , GPUBlendState
  , GPUBlendComponent
  , GPUBlendFactor(..)
  , GPUBlendOperation(..)
  , GPUColorWriteMask(..)
  , combineColorWriteMask
    -- Depth/Stencil State
  , GPUDepthStencilState
  , GPUStencilFaceState
  , GPUStencilOperation(..)
    -- Multisample State
  , GPUMultisampleState
    -- Pipeline
  , GPURenderPipelineDescriptor
  , GPUComputePipelineDescriptor
  , GPUPipelineLayoutDescriptor
    -- Bind Group
  , GPUBindGroupLayoutDescriptor
  , GPUBindGroupLayoutEntry
  , GPUBindGroupDescriptor
  , GPUBindGroupEntry
  , BindGroupResourceType(..)
  , GPUBufferBindingType(..)
  , GPUSamplerBindingType(..)
  , GPUTextureSampleType(..)
  , GPUStorageTextureAccess(..)
  , GPUShaderStage(..)
  , combineShaderStage
    -- Render Pass
  , GPURenderPassDescriptor
  , GPURenderPassColorAttachment
  , GPURenderPassDepthStencilAttachment
  , GPULoadOp(..)
  , GPUStoreOp(..)
    -- Canvas Configuration
  , GPUCanvasConfiguration
  , GPUCanvasAlphaMode(..)
  ) where

import Prelude

import Data.Foldable (foldr)
import Data.Maybe (Maybe)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- ADAPTER & DEVICE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Options for requesting a GPU adapter.
type GPUAdapterDescriptor =
  { powerPreference :: Maybe GPUPowerPreference
  , forceFallbackAdapter :: Boolean
  }

-- | Power preference for adapter selection.
data GPUPowerPreference
  = LowPower
  | HighPerformance

derive instance eqGPUPowerPreference :: Eq GPUPowerPreference
derive instance ordGPUPowerPreference :: Ord GPUPowerPreference

-- | Options for requesting a GPU device.
type GPUDeviceDescriptor =
  { requiredFeatures :: Array GPUFeatureName
  , requiredLimits :: Maybe GPULimits
  , label :: Maybe String
  }

-- | Queue descriptor (currently empty in WebGPU spec).
type GPUQueueDescriptor =
  { label :: Maybe String
  }

-- | Device limits. All values are maximums or minimums as appropriate.
type GPULimits =
  { maxTextureDimension1D :: Int
  , maxTextureDimension2D :: Int
  , maxTextureDimension3D :: Int
  , maxTextureArrayLayers :: Int
  , maxBindGroups :: Int
  , maxBindGroupsPlusVertexBuffers :: Int
  , maxBindingsPerBindGroup :: Int
  , maxDynamicUniformBuffersPerPipelineLayout :: Int
  , maxDynamicStorageBuffersPerPipelineLayout :: Int
  , maxSampledTexturesPerShaderStage :: Int
  , maxSamplersPerShaderStage :: Int
  , maxStorageBuffersPerShaderStage :: Int
  , maxStorageTexturesPerShaderStage :: Int
  , maxUniformBuffersPerShaderStage :: Int
  , maxUniformBufferBindingSize :: Int
  , maxStorageBufferBindingSize :: Int
  , minUniformBufferOffsetAlignment :: Int
  , minStorageBufferOffsetAlignment :: Int
  , maxVertexBuffers :: Int
  , maxBufferSize :: Number
  , maxVertexAttributes :: Int
  , maxVertexBufferArrayStride :: Int
  , maxInterStageShaderComponents :: Int
  , maxInterStageShaderVariables :: Int
  , maxColorAttachments :: Int
  , maxColorAttachmentBytesPerSample :: Int
  , maxComputeWorkgroupStorageSize :: Int
  , maxComputeInvocationsPerWorkgroup :: Int
  , maxComputeWorkgroupSizeX :: Int
  , maxComputeWorkgroupSizeY :: Int
  , maxComputeWorkgroupSizeZ :: Int
  , maxComputeWorkgroupsPerDimension :: Int
  }

-- | Optional GPU features.
data GPUFeatureName
  = DepthClipControl
  | FeatureDepth32FloatStencil8
  | TextureCompressionBC
  | TextureCompressionETC2
  | TextureCompressionASTC
  | TimestampQuery
  | IndirectFirstInstance
  | ShaderF16
  | RG11B10UfloatRenderable
  | BGRA8UnormStorage
  | Float32Filterable

derive instance eqGPUFeatureName :: Eq GPUFeatureName
derive instance ordGPUFeatureName :: Ord GPUFeatureName

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- BUFFER
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Buffer creation descriptor.
type GPUBufferDescriptor =
  { size :: Int
  , usage :: Array GPUBufferUsage
  , mappedAtCreation :: Boolean
  , label :: Maybe String
  }

-- | Buffer usage flags (combinable).
data GPUBufferUsage
  = MapRead
  | MapWrite
  | CopySrc
  | CopyDst
  | Index
  | Vertex
  | Uniform
  | Storage
  | Indirect
  | QueryResolve

derive instance eqGPUBufferUsage :: Eq GPUBufferUsage
derive instance ordGPUBufferUsage :: Ord GPUBufferUsage

-- | Combine buffer usage flags into a bitmask.
combineBufferUsage :: Array GPUBufferUsage -> Int
combineBufferUsage = foldr (\u acc -> acc + usageToInt u) 0
  where
  usageToInt :: GPUBufferUsage -> Int
  usageToInt = case _ of
    MapRead -> 1
    MapWrite -> 2
    CopySrc -> 4
    CopyDst -> 8
    Index -> 16
    Vertex -> 32
    Uniform -> 64
    Storage -> 128
    Indirect -> 256
    QueryResolve -> 512

-- | Buffer map modes.
data GPUMapMode
  = MapModeRead
  | MapModeWrite

derive instance eqGPUMapMode :: Eq GPUMapMode
derive instance ordGPUMapMode :: Ord GPUMapMode

-- | Combine map modes into a bitmask.
combineMapMode :: Array GPUMapMode -> Int
combineMapMode = foldr (\m acc -> acc + modeToInt m) 0
  where
  modeToInt :: GPUMapMode -> Int
  modeToInt = case _ of
    MapModeRead -> 1
    MapModeWrite -> 2

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- TEXTURE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Texture creation descriptor.
type GPUTextureDescriptor =
  { size :: { width :: Int, height :: Int, depthOrArrayLayers :: Int }
  , mipLevelCount :: Int
  , sampleCount :: Int
  , dimension :: GPUTextureDimension
  , format :: GPUTextureFormat
  , usage :: Array GPUTextureUsage
  , viewFormats :: Array GPUTextureFormat
  , label :: Maybe String
  }

-- | Texture dimension.
data GPUTextureDimension
  = Dimension1D
  | Dimension2D
  | Dimension3D

derive instance eqGPUTextureDimension :: Eq GPUTextureDimension
derive instance ordGPUTextureDimension :: Ord GPUTextureDimension

-- | Texture formats (subset — add more as needed).
data GPUTextureFormat
  -- 8-bit formats
  = R8Unorm
  | R8Snorm
  | R8Uint
  | R8Sint
  -- 16-bit formats
  | R16Uint
  | R16Sint
  | R16Float
  | RG8Unorm
  | RG8Snorm
  | RG8Uint
  | RG8Sint
  -- 32-bit formats
  | R32Uint
  | R32Sint
  | R32Float
  | RG16Uint
  | RG16Sint
  | RG16Float
  | RGBA8Unorm
  | RGBA8UnormSrgb
  | RGBA8Snorm
  | RGBA8Uint
  | RGBA8Sint
  | BGRA8Unorm
  | BGRA8UnormSrgb
  -- Packed 32-bit formats
  | RGB9E5Ufloat
  | RGB10A2Uint
  | RGB10A2Unorm
  | RG11B10Ufloat
  -- 64-bit formats
  | RG32Uint
  | RG32Sint
  | RG32Float
  | RGBA16Uint
  | RGBA16Sint
  | RGBA16Float
  -- 128-bit formats
  | RGBA32Uint
  | RGBA32Sint
  | RGBA32Float
  -- Depth/stencil formats
  | Stencil8
  | Depth16Unorm
  | Depth24Plus
  | Depth24PlusStencil8
  | Depth32Float
  | Depth32FloatStencil8

derive instance eqGPUTextureFormat :: Eq GPUTextureFormat
derive instance ordGPUTextureFormat :: Ord GPUTextureFormat

-- | Texture usage flags (combinable).
data GPUTextureUsage
  = TextureCopySrc
  | TextureCopyDst
  | TextureBinding
  | StorageBinding
  | RenderAttachment

derive instance eqGPUTextureUsage :: Eq GPUTextureUsage
derive instance ordGPUTextureUsage :: Ord GPUTextureUsage

-- | Combine texture usage flags into a bitmask.
combineTextureUsage :: Array GPUTextureUsage -> Int
combineTextureUsage = foldr (\u acc -> acc + usageToInt u) 0
  where
  usageToInt :: GPUTextureUsage -> Int
  usageToInt = case _ of
    TextureCopySrc -> 1
    TextureCopyDst -> 2
    TextureBinding -> 4
    StorageBinding -> 8
    RenderAttachment -> 16

-- | Texture view descriptor.
type GPUTextureViewDescriptor =
  { format :: Maybe GPUTextureFormat
  , dimension :: Maybe GPUTextureViewDimension
  , aspect :: GPUTextureAspect
  , baseMipLevel :: Int
  , mipLevelCount :: Maybe Int
  , baseArrayLayer :: Int
  , arrayLayerCount :: Maybe Int
  , label :: Maybe String
  }

-- | Texture view dimension.
data GPUTextureViewDimension
  = View1D
  | View2D
  | View2DArray
  | ViewCube
  | ViewCubeArray
  | View3D

derive instance eqGPUTextureViewDimension :: Eq GPUTextureViewDimension
derive instance ordGPUTextureViewDimension :: Ord GPUTextureViewDimension

-- | Texture aspect.
data GPUTextureAspect
  = AspectAll
  | AspectStencilOnly
  | AspectDepthOnly

derive instance eqGPUTextureAspect :: Eq GPUTextureAspect
derive instance ordGPUTextureAspect :: Ord GPUTextureAspect

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SAMPLER
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Sampler descriptor.
type GPUSamplerDescriptor =
  { addressModeU :: GPUAddressMode
  , addressModeV :: GPUAddressMode
  , addressModeW :: GPUAddressMode
  , magFilter :: GPUFilterMode
  , minFilter :: GPUFilterMode
  , mipmapFilter :: GPUMipmapFilterMode
  , lodMinClamp :: Number
  , lodMaxClamp :: Number
  , compare :: Maybe GPUCompareFunction
  , maxAnisotropy :: Int
  , label :: Maybe String
  }

-- | Texture address mode.
data GPUAddressMode
  = ClampToEdge
  | Repeat
  | MirrorRepeat

derive instance eqGPUAddressMode :: Eq GPUAddressMode
derive instance ordGPUAddressMode :: Ord GPUAddressMode

-- | Texture filter mode.
data GPUFilterMode
  = FilterNearest
  | FilterLinear

derive instance eqGPUFilterMode :: Eq GPUFilterMode
derive instance ordGPUFilterMode :: Ord GPUFilterMode

-- | Mipmap filter mode.
data GPUMipmapFilterMode
  = MipmapNearest
  | MipmapLinear

derive instance eqGPUMipmapFilterMode :: Eq GPUMipmapFilterMode
derive instance ordGPUMipmapFilterMode :: Ord GPUMipmapFilterMode

-- | Comparison function for depth/stencil operations.
data GPUCompareFunction
  = CompareNever
  | CompareLess
  | CompareEqual
  | CompareLessEqual
  | CompareGreater
  | CompareNotEqual
  | CompareGreaterEqual
  | CompareAlways

derive instance eqGPUCompareFunction :: Eq GPUCompareFunction
derive instance ordGPUCompareFunction :: Ord GPUCompareFunction

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SHADER
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shader module descriptor.
type GPUShaderModuleDescriptor =
  { code :: WGSLSource
  , label :: Maybe String
  }

-- | WGSL source code (pure String wrapper for type safety).
newtype WGSLSource = WGSLSource String

derive instance eqWGSLSource :: Eq WGSLSource
derive instance ordWGSLSource :: Ord WGSLSource

instance showWGSLSource :: Show WGSLSource where
  show (WGSLSource s) = "(WGSLSource " <> show s <> ")"

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- VERTEX STATE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Vertex shader state.
type GPUVertexState =
  { entryPoint :: String
  , buffers :: Array GPUVertexBufferLayout
  , constants :: Array { key :: String, value :: Number }
  }

-- | Vertex buffer layout.
type GPUVertexBufferLayout =
  { arrayStride :: Int
  , stepMode :: GPUVertexStepMode
  , attributes :: Array GPUVertexAttribute
  }

-- | Vertex attribute.
type GPUVertexAttribute =
  { format :: GPUVertexFormat
  , offset :: Int
  , shaderLocation :: Int
  }

-- | Vertex attribute formats.
data GPUVertexFormat
  = Uint8x2
  | Uint8x4
  | Sint8x2
  | Sint8x4
  | Unorm8x2
  | Unorm8x4
  | Snorm8x2
  | Snorm8x4
  | Uint16x2
  | Uint16x4
  | Sint16x2
  | Sint16x4
  | Unorm16x2
  | Unorm16x4
  | Snorm16x2
  | Snorm16x4
  | Float16x2
  | Float16x4
  | Float32
  | Float32x2
  | Float32x3
  | Float32x4
  | Uint32
  | Uint32x2
  | Uint32x3
  | Uint32x4
  | Sint32
  | Sint32x2
  | Sint32x3
  | Sint32x4

derive instance eqGPUVertexFormat :: Eq GPUVertexFormat
derive instance ordGPUVertexFormat :: Ord GPUVertexFormat

-- | Vertex step mode.
data GPUVertexStepMode
  = StepVertex
  | StepInstance

derive instance eqGPUVertexStepMode :: Eq GPUVertexStepMode
derive instance ordGPUVertexStepMode :: Ord GPUVertexStepMode

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- PRIMITIVE STATE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Primitive assembly state.
type GPUPrimitiveState =
  { topology :: GPUPrimitiveTopology
  , stripIndexFormat :: Maybe GPUIndexFormat
  , frontFace :: GPUFrontFace
  , cullMode :: GPUCullMode
  , unclippedDepth :: Boolean
  }

-- | Primitive topology.
data GPUPrimitiveTopology
  = PointList
  | LineList
  | LineStrip
  | TriangleList
  | TriangleStrip

derive instance eqGPUPrimitiveTopology :: Eq GPUPrimitiveTopology
derive instance ordGPUPrimitiveTopology :: Ord GPUPrimitiveTopology

-- | Front face winding order.
data GPUFrontFace
  = FrontCCW
  | FrontCW

derive instance eqGPUFrontFace :: Eq GPUFrontFace
derive instance ordGPUFrontFace :: Ord GPUFrontFace

-- | Cull mode.
data GPUCullMode
  = CullNone
  | CullFront
  | CullBack

derive instance eqGPUCullMode :: Eq GPUCullMode
derive instance ordGPUCullMode :: Ord GPUCullMode

-- | Index format.
data GPUIndexFormat
  = IndexUint16
  | IndexUint32

derive instance eqGPUIndexFormat :: Eq GPUIndexFormat
derive instance ordGPUIndexFormat :: Ord GPUIndexFormat

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- FRAGMENT STATE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Fragment shader state.
type GPUFragmentState =
  { entryPoint :: String
  , targets :: Array GPUColorTargetState
  , constants :: Array { key :: String, value :: Number }
  }

-- | Color target state.
type GPUColorTargetState =
  { format :: GPUTextureFormat
  , blend :: Maybe GPUBlendState
  , writeMask :: Array GPUColorWriteMask
  }

-- | Blend state.
type GPUBlendState =
  { color :: GPUBlendComponent
  , alpha :: GPUBlendComponent
  }

-- | Blend component (color or alpha).
type GPUBlendComponent =
  { operation :: GPUBlendOperation
  , srcFactor :: GPUBlendFactor
  , dstFactor :: GPUBlendFactor
  }

-- | Blend factors.
data GPUBlendFactor
  = BlendZero
  | BlendOne
  | BlendSrc
  | BlendOneMinusSrc
  | BlendSrcAlpha
  | BlendOneMinusSrcAlpha
  | BlendDst
  | BlendOneMinusDst
  | BlendDstAlpha
  | BlendOneMinusDstAlpha
  | BlendSrcAlphaSaturated
  | BlendConstant
  | BlendOneMinusConstant

derive instance eqGPUBlendFactor :: Eq GPUBlendFactor
derive instance ordGPUBlendFactor :: Ord GPUBlendFactor

-- | Blend operations.
data GPUBlendOperation
  = BlendAdd
  | BlendSubtract
  | BlendReverseSubtract
  | BlendMin
  | BlendMax

derive instance eqGPUBlendOperation :: Eq GPUBlendOperation
derive instance ordGPUBlendOperation :: Ord GPUBlendOperation

-- | Color write mask flags.
data GPUColorWriteMask
  = WriteRed
  | WriteGreen
  | WriteBlue
  | WriteAlpha
  | WriteAll

derive instance eqGPUColorWriteMask :: Eq GPUColorWriteMask
derive instance ordGPUColorWriteMask :: Ord GPUColorWriteMask

-- | Combine color write masks into a bitmask.
combineColorWriteMask :: Array GPUColorWriteMask -> Int
combineColorWriteMask = foldr (\m acc -> acc + maskToInt m) 0
  where
  maskToInt :: GPUColorWriteMask -> Int
  maskToInt = case _ of
    WriteRed -> 1
    WriteGreen -> 2
    WriteBlue -> 4
    WriteAlpha -> 8
    WriteAll -> 15

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- DEPTH/STENCIL STATE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Depth/stencil state.
type GPUDepthStencilState =
  { format :: GPUTextureFormat
  , depthWriteEnabled :: Boolean
  , depthCompare :: GPUCompareFunction
  , stencilFront :: GPUStencilFaceState
  , stencilBack :: GPUStencilFaceState
  , stencilReadMask :: Int
  , stencilWriteMask :: Int
  , depthBias :: Int
  , depthBiasSlopeScale :: Number
  , depthBiasClamp :: Number
  }

-- | Stencil face state.
type GPUStencilFaceState =
  { compare :: GPUCompareFunction
  , failOp :: GPUStencilOperation
  , depthFailOp :: GPUStencilOperation
  , passOp :: GPUStencilOperation
  }

-- | Stencil operations.
data GPUStencilOperation
  = StencilKeep
  | StencilZero
  | StencilReplace
  | StencilInvert
  | StencilIncrementClamp
  | StencilDecrementClamp
  | StencilIncrementWrap
  | StencilDecrementWrap

derive instance eqGPUStencilOperation :: Eq GPUStencilOperation
derive instance ordGPUStencilOperation :: Ord GPUStencilOperation

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- MULTISAMPLE STATE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Multisample state.
type GPUMultisampleState =
  { count :: Int
  , mask :: Int
  , alphaToCoverageEnabled :: Boolean
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- PIPELINE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Render pipeline descriptor.
type GPURenderPipelineDescriptor =
  { vertex :: GPUVertexState
  , primitive :: GPUPrimitiveState
  , depthStencil :: Maybe GPUDepthStencilState
  , multisample :: GPUMultisampleState
  , fragment :: Maybe GPUFragmentState
  , label :: Maybe String
  }

-- | Compute pipeline descriptor.
type GPUComputePipelineDescriptor =
  { compute ::
      { entryPoint :: String
      , constants :: Array { key :: String, value :: Number }
      }
  , label :: Maybe String
  }

-- | Pipeline layout descriptor.
type GPUPipelineLayoutDescriptor =
  { bindGroupLayouts :: Array GPUBindGroupLayoutDescriptor
  , label :: Maybe String
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- BIND GROUP
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bind group layout descriptor.
type GPUBindGroupLayoutDescriptor =
  { entries :: Array GPUBindGroupLayoutEntry
  , label :: Maybe String
  }

-- | Bind group layout entry.
type GPUBindGroupLayoutEntry =
  { binding :: Int
  , visibility :: Array GPUShaderStage
  , buffer :: Maybe { type :: GPUBufferBindingType, hasDynamicOffset :: Boolean, minBindingSize :: Int }
  , sampler :: Maybe { type :: GPUSamplerBindingType }
  , texture :: Maybe { sampleType :: GPUTextureSampleType, viewDimension :: GPUTextureViewDimension, multisampled :: Boolean }
  , storageTexture :: Maybe { access :: GPUStorageTextureAccess, format :: GPUTextureFormat, viewDimension :: GPUTextureViewDimension }
  }

-- | Bind group descriptor.
type GPUBindGroupDescriptor =
  { entries :: Array GPUBindGroupEntry
  , label :: Maybe String
  }

-- | Bind group entry (references actual resources).
type GPUBindGroupEntry =
  { binding :: Int
  , resourceType :: BindGroupResourceType
  }

-- | Resource type for bind group entry.
data BindGroupResourceType
  = BufferResource { offset :: Int, size :: Int }
  | SamplerResource
  | TextureViewResource

derive instance eqBindGroupResourceType :: Eq BindGroupResourceType

-- | Buffer binding type.
data GPUBufferBindingType
  = BufferUniform
  | BufferStorage
  | BufferReadOnlyStorage

derive instance eqGPUBufferBindingType :: Eq GPUBufferBindingType
derive instance ordGPUBufferBindingType :: Ord GPUBufferBindingType

-- | Sampler binding type.
data GPUSamplerBindingType
  = SamplerFiltering
  | SamplerNonFiltering
  | SamplerComparison

derive instance eqGPUSamplerBindingType :: Eq GPUSamplerBindingType
derive instance ordGPUSamplerBindingType :: Ord GPUSamplerBindingType

-- | Texture sample type.
data GPUTextureSampleType
  = SampleFloat
  | SampleUnfilterableFloat
  | SampleDepth
  | SampleSint
  | SampleUint

derive instance eqGPUTextureSampleType :: Eq GPUTextureSampleType
derive instance ordGPUTextureSampleType :: Ord GPUTextureSampleType

-- | Storage texture access.
data GPUStorageTextureAccess
  = StorageWriteOnly
  | StorageReadOnly
  | StorageReadWrite

derive instance eqGPUStorageTextureAccess :: Eq GPUStorageTextureAccess
derive instance ordGPUStorageTextureAccess :: Ord GPUStorageTextureAccess

-- | Shader stage visibility.
data GPUShaderStage
  = StageVertex
  | StageFragment
  | StageCompute

derive instance eqGPUShaderStage :: Eq GPUShaderStage
derive instance ordGPUShaderStage :: Ord GPUShaderStage

-- | Combine shader stages into a bitmask.
combineShaderStage :: Array GPUShaderStage -> Int
combineShaderStage = foldr (\s acc -> acc + stageToInt s) 0
  where
  stageToInt :: GPUShaderStage -> Int
  stageToInt = case _ of
    StageVertex -> 1
    StageFragment -> 2
    StageCompute -> 4

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- RENDER PASS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Render pass descriptor.
type GPURenderPassDescriptor =
  { colorAttachments :: Array GPURenderPassColorAttachment
  , depthStencilAttachment :: Maybe GPURenderPassDepthStencilAttachment
  , timestampWrites :: Maybe { querySet :: Int, beginningOfPassWriteIndex :: Int, endOfPassWriteIndex :: Int }
  , label :: Maybe String
  }

-- | Color attachment for render pass.
type GPURenderPassColorAttachment =
  { loadOp :: GPULoadOp
  , storeOp :: GPUStoreOp
  , clearValue :: { r :: Number, g :: Number, b :: Number, a :: Number }
  }

-- | Depth/stencil attachment for render pass.
type GPURenderPassDepthStencilAttachment =
  { depthLoadOp :: Maybe GPULoadOp
  , depthStoreOp :: Maybe GPUStoreOp
  , depthClearValue :: Number
  , depthReadOnly :: Boolean
  , stencilLoadOp :: Maybe GPULoadOp
  , stencilStoreOp :: Maybe GPUStoreOp
  , stencilClearValue :: Int
  , stencilReadOnly :: Boolean
  }

-- | Load operation.
data GPULoadOp
  = LoadOpLoad
  | LoadOpClear

derive instance eqGPULoadOp :: Eq GPULoadOp
derive instance ordGPULoadOp :: Ord GPULoadOp

-- | Store operation.
data GPUStoreOp
  = StoreOpStore
  | StoreOpDiscard

derive instance eqGPUStoreOp :: Eq GPUStoreOp
derive instance ordGPUStoreOp :: Ord GPUStoreOp

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- CANVAS CONFIGURATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas configuration.
type GPUCanvasConfiguration =
  { format :: GPUTextureFormat
  , usage :: Array GPUTextureUsage
  , viewFormats :: Array GPUTextureFormat
  , colorSpace :: String
  , alphaMode :: GPUCanvasAlphaMode
  }

-- | Canvas alpha mode.
data GPUCanvasAlphaMode
  = AlphaOpaque
  | AlphaPremultiplied

derive instance eqGPUCanvasAlphaMode :: Eq GPUCanvasAlphaMode
derive instance ordGPUCanvasAlphaMode :: Ord GPUCanvasAlphaMode
