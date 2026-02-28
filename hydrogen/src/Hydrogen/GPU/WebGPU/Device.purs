-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // gpu // webgpu // device
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- GPU device initialization — THE ONLY FFI BOUNDARY for WebGPU.
--
-- All other WebGPU modules are pure PureScript. This module contains
-- the minimal FFI required to interact with the browser's WebGPU API.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Device
  ( -- Foreign types (opaque)
    GPUDevice
  , GPUAdapter
  , GPUQueue
  , GPUCanvasContext
  , GPUBuffer
  , GPUTexture
  , GPUTextureView
  , GPUSampler
  , GPUShaderModule
  , GPURenderPipeline
  , GPUComputePipeline
  , GPUBindGroup
  , GPUBindGroupLayout
  , GPUPipelineLayout
  , GPUCommandEncoder
  , GPURenderPassEncoder
  , GPUComputePassEncoder
  , GPUCommandBuffer
  , GPUQuerySet
    -- Errors
  , DeviceError(..)
  , DeviceLostReason(..)
    -- Initialization
  , isWebGPUSupported
  , requestAdapter
  , requestDevice
  , configureCanvas
  , getQueue
    -- Device info
  , getLimits
  , getFeatures
  , hasFeature
    -- Error handling
  , onUncapturedError
  , onDeviceLost
    -- Canvas operations
  , getCurrentTexture
  , getPreferredCanvasFormat
    -- Buffer operations
  , createBuffer
  , destroyBuffer
  , writeBuffer
  , mapBufferAsync
  , unmapBuffer
  , getMappedRange
    -- Texture operations
  , createTexture
  , destroyTexture
  , createTextureView
  , writeTexture
    -- Sampler operations
  , createSampler
    -- Shader operations
  , createShaderModule
    -- Pipeline operations
  , createRenderPipeline
  , createComputePipeline
  , createBindGroupLayout
  , createPipelineLayout
    -- Bind group operations
  , createBindGroup
    -- Command encoding
  , createCommandEncoder
  , finishCommandEncoder
  , beginRenderPass
  , endRenderPass
  , beginComputePass
  , endComputePass
    -- Render pass operations
  , setPipeline
  , setBindGroup
  , setVertexBuffer
  , setIndexBuffer
  , draw
  , drawIndexed
  , drawIndirect
  , setViewport
  , setScissorRect
    -- Queue operations
  , submit
  ) where

import Prelude

import Data.ArrayBuffer.Types (ArrayBuffer)
import Data.Either (Either(Left, Right))
import Data.Foldable (elem)
import Data.Maybe (Maybe(Just, Nothing))
import Effect (Effect)
import Effect.Aff (Aff, makeAff, nonCanceler)
import Effect.Exception (Error)
import Foreign (Foreign)
import Hydrogen.GPU.WebGPU.Types
  ( GPUAdapterDescriptor
  , GPUBufferDescriptor
  , GPUCanvasConfiguration
  , GPUFeatureName(..)
  , GPUIndexFormat(..)
  , GPULimits
  , GPURenderPassDescriptor
  , GPUSamplerDescriptor
  , GPUShaderModuleDescriptor
  , GPUTextureDescriptor
  , GPUTextureFormat(..)
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- FOREIGN TYPES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Opaque GPU device handle.
foreign import data GPUDevice :: Type

-- | Opaque GPU adapter handle.
foreign import data GPUAdapter :: Type

-- | Opaque GPU queue handle.
foreign import data GPUQueue :: Type

-- | Opaque canvas context handle.
foreign import data GPUCanvasContext :: Type

-- | Opaque buffer handle.
foreign import data GPUBuffer :: Type

-- | Opaque texture handle.
foreign import data GPUTexture :: Type

-- | Opaque texture view handle.
foreign import data GPUTextureView :: Type

-- | Opaque sampler handle.
foreign import data GPUSampler :: Type

-- | Opaque shader module handle.
foreign import data GPUShaderModule :: Type

-- | Opaque render pipeline handle.
foreign import data GPURenderPipeline :: Type

-- | Opaque compute pipeline handle.
foreign import data GPUComputePipeline :: Type

-- | Opaque bind group handle.
foreign import data GPUBindGroup :: Type

-- | Opaque bind group layout handle.
foreign import data GPUBindGroupLayout :: Type

-- | Opaque pipeline layout handle.
foreign import data GPUPipelineLayout :: Type

-- | Opaque command encoder handle.
foreign import data GPUCommandEncoder :: Type

-- | Opaque render pass encoder handle.
foreign import data GPURenderPassEncoder :: Type

-- | Opaque compute pass encoder handle.
foreign import data GPUComputePassEncoder :: Type

-- | Opaque command buffer handle.
foreign import data GPUCommandBuffer :: Type

-- | Opaque query set handle.
foreign import data GPUQuerySet :: Type

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- ERRORS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Errors that can occur during device initialization.
data DeviceError
  = WebGPUNotSupported
  | AdapterRequestFailed String
  | DeviceRequestFailed String
  | FeatureNotSupported GPUFeatureName
  | LimitExceeded String Int Int -- limit name, requested, maximum
  | CanvasConfigurationFailed String

derive instance eqDeviceError :: Eq DeviceError

instance showDeviceError :: Show DeviceError where
  show WebGPUNotSupported = "WebGPU is not supported in this browser"
  show (AdapterRequestFailed reason) = "Adapter request failed: " <> reason
  show (DeviceRequestFailed reason) = "Device request failed: " <> reason
  show (FeatureNotSupported _) = "Required feature not supported"
  show (LimitExceeded name requested maximum) =
    "Limit exceeded: " <> name <> " requested " <> show requested <> " but maximum is " <> show maximum
  show (CanvasConfigurationFailed reason) = "Canvas configuration failed: " <> reason

-- | Reasons for device loss.
data DeviceLostReason
  = DeviceLostUnknown
  | DeviceLostDestroyed

derive instance eqDeviceLostReason :: Eq DeviceLostReason

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- INITIALIZATION — FFI IMPLEMENTATIONS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Check if WebGPU is supported in the current environment.
foreign import isWebGPUSupportedImpl :: Effect Boolean

isWebGPUSupported :: Effect Boolean
isWebGPUSupported = isWebGPUSupportedImpl

-- | Request a GPU adapter.
foreign import requestAdapterImpl
  :: Foreign
  -> (GPUAdapter -> Effect Unit)
  -> (String -> Effect Unit)
  -> Effect Unit

requestAdapter :: GPUAdapterDescriptor -> Aff (Either DeviceError GPUAdapter)
requestAdapter desc = makeAff \callback -> do
  requestAdapterImpl
    (toForeignAdapterDesc desc)
    (\adapter -> callback (Right (Right adapter)))
    (\reason -> callback (Right (Left (AdapterRequestFailed reason))))
  pure nonCanceler

-- | Request a GPU device from an adapter.
foreign import requestDeviceImpl
  :: GPUAdapter
  -> Foreign
  -> (GPUDevice -> Effect Unit)
  -> (String -> Effect Unit)
  -> Effect Unit

requestDevice :: GPUAdapter -> { requiredFeatures :: Array String, label :: Maybe String } -> Aff (Either DeviceError GPUDevice)
requestDevice adapter desc = makeAff \callback -> do
  requestDeviceImpl
    adapter
    (toForeignDeviceDesc desc)
    (\device -> callback (Right (Right device)))
    (\reason -> callback (Right (Left (DeviceRequestFailed reason))))
  pure nonCanceler

-- | Configure a canvas element for WebGPU rendering.
foreign import configureCanvasImpl
  :: GPUDevice
  -> Foreign -- CanvasElement
  -> Foreign -- Configuration
  -> Effect (Either String GPUCanvasContext)

configureCanvas :: GPUDevice -> Foreign -> GPUCanvasConfiguration -> Effect (Either DeviceError GPUCanvasContext)
configureCanvas device canvas config = do
  result <- configureCanvasImpl device canvas (toForeignCanvasConfig config)
  pure case result of
    Left reason -> Left (CanvasConfigurationFailed reason)
    Right ctx -> Right ctx

-- | Get the queue from a device.
foreign import getQueueImpl :: GPUDevice -> Effect GPUQueue

getQueue :: GPUDevice -> Effect GPUQueue
getQueue = getQueueImpl

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- DEVICE INFO
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Get device limits.
foreign import getLimitsImpl :: GPUDevice -> Effect Foreign

getLimits :: GPUDevice -> Effect GPULimits
getLimits device = do
  raw <- getLimitsImpl device
  pure (fromForeignLimits raw)

-- | Get supported features.
foreign import getFeaturesImpl :: GPUDevice -> Effect (Array String)

getFeatures :: GPUDevice -> Effect (Array GPUFeatureName)
getFeatures device = do
  strings <- getFeaturesImpl device
  pure (map stringToFeature strings)

-- | Check if device has a specific feature.
hasFeature :: GPUDevice -> GPUFeatureName -> Effect Boolean
hasFeature device feature = do
  features <- getFeatures device
  pure (elem feature features)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- ERROR HANDLING
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Register handler for uncaptured errors.
foreign import onUncapturedErrorImpl :: GPUDevice -> (Error -> Effect Unit) -> Effect Unit

onUncapturedError :: GPUDevice -> (Error -> Effect Unit) -> Effect Unit
onUncapturedError = onUncapturedErrorImpl

-- | Register handler for device lost.
foreign import onDeviceLostImpl :: GPUDevice -> (String -> Effect Unit) -> Effect Unit

onDeviceLost :: GPUDevice -> (DeviceLostReason -> Effect Unit) -> Effect Unit
onDeviceLost device callback =
  onDeviceLostImpl device \reason ->
    callback (stringToLostReason reason)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- CANVAS OPERATIONS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Get the current texture from a canvas context.
foreign import getCurrentTextureImpl :: GPUCanvasContext -> Effect GPUTexture

getCurrentTexture :: GPUCanvasContext -> Effect GPUTexture
getCurrentTexture = getCurrentTextureImpl

-- | Get the preferred canvas format for the current system.
foreign import getPreferredCanvasFormatImpl :: Effect String

getPreferredCanvasFormat :: Effect GPUTextureFormat
getPreferredCanvasFormat = do
  formatStr <- getPreferredCanvasFormatImpl
  pure (stringToTextureFormat formatStr)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- BUFFER OPERATIONS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Create a buffer.
foreign import createBufferImpl :: GPUDevice -> Foreign -> Effect GPUBuffer

createBuffer :: GPUDevice -> GPUBufferDescriptor -> Effect GPUBuffer
createBuffer device desc = createBufferImpl device (toForeignBufferDesc desc)

-- | Destroy a buffer.
foreign import destroyBufferImpl :: GPUBuffer -> Effect Unit

destroyBuffer :: GPUBuffer -> Effect Unit
destroyBuffer = destroyBufferImpl

-- | Write data to a buffer via the queue.
foreign import writeBufferImpl :: GPUQueue -> GPUBuffer -> Int -> ArrayBuffer -> Int -> Int -> Effect Unit

writeBuffer :: GPUQueue -> GPUBuffer -> Int -> ArrayBuffer -> Effect Unit
writeBuffer queue buffer offset data_ =
  writeBufferImpl queue buffer offset data_ 0 0 -- 0 means entire buffer

-- | Map buffer for CPU access (async).
foreign import mapBufferAsyncImpl
  :: GPUBuffer
  -> Int -- mode
  -> Int -- offset
  -> Int -- size
  -> (Unit -> Effect Unit) -- onSuccess
  -> (String -> Effect Unit) -- onError
  -> Effect Unit

mapBufferAsync :: GPUBuffer -> Int -> Int -> Int -> Aff (Either String Unit)
mapBufferAsync buffer mode offset size = makeAff \callback -> do
  mapBufferAsyncImpl buffer mode offset size
    (\_ -> callback (Right (Right unit)))
    (\reason -> callback (Right (Left reason)))
  pure nonCanceler

-- | Unmap a buffer.
foreign import unmapBufferImpl :: GPUBuffer -> Effect Unit

unmapBuffer :: GPUBuffer -> Effect Unit
unmapBuffer = unmapBufferImpl

-- | Get the mapped range of a buffer.
foreign import getMappedRangeImpl :: GPUBuffer -> Int -> Int -> Effect ArrayBuffer

getMappedRange :: GPUBuffer -> Int -> Int -> Effect ArrayBuffer
getMappedRange = getMappedRangeImpl

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- TEXTURE OPERATIONS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Create a texture.
foreign import createTextureImpl :: GPUDevice -> Foreign -> Effect GPUTexture

createTexture :: GPUDevice -> GPUTextureDescriptor -> Effect GPUTexture
createTexture device desc = createTextureImpl device (toForeignTextureDesc desc)

-- | Destroy a texture.
foreign import destroyTextureImpl :: GPUTexture -> Effect Unit

destroyTexture :: GPUTexture -> Effect Unit
destroyTexture = destroyTextureImpl

-- | Create a texture view.
foreign import createTextureViewImpl :: GPUTexture -> Foreign -> Effect GPUTextureView

createTextureView :: GPUTexture -> Foreign -> Effect GPUTextureView
createTextureView = createTextureViewImpl

-- | Write data to a texture via the queue.
foreign import writeTextureImpl :: GPUQueue -> Foreign -> ArrayBuffer -> Foreign -> Foreign -> Effect Unit

writeTexture :: GPUQueue -> GPUTexture -> ArrayBuffer -> { width :: Int, height :: Int } -> Effect Unit
writeTexture queue texture data_ size =
  writeTextureImpl queue (toForeignTextureDest texture) data_ (toForeignDataLayout size) (toForeignSize size)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SAMPLER OPERATIONS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Create a sampler.
foreign import createSamplerImpl :: GPUDevice -> Foreign -> Effect GPUSampler

createSampler :: GPUDevice -> GPUSamplerDescriptor -> Effect GPUSampler
createSampler device desc = createSamplerImpl device (toForeignSamplerDesc desc)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SHADER OPERATIONS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Create a shader module from WGSL source.
foreign import createShaderModuleImpl :: GPUDevice -> Foreign -> Effect GPUShaderModule

createShaderModule :: GPUDevice -> GPUShaderModuleDescriptor -> Effect GPUShaderModule
createShaderModule device desc = createShaderModuleImpl device (toForeignShaderDesc desc)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- PIPELINE OPERATIONS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Create a render pipeline.
foreign import createRenderPipelineImpl :: GPUDevice -> Foreign -> Effect GPURenderPipeline

createRenderPipeline :: GPUDevice -> Foreign -> Effect GPURenderPipeline
createRenderPipeline = createRenderPipelineImpl

-- | Create a compute pipeline.
foreign import createComputePipelineImpl :: GPUDevice -> Foreign -> Effect GPUComputePipeline

createComputePipeline :: GPUDevice -> Foreign -> Effect GPUComputePipeline
createComputePipeline = createComputePipelineImpl

-- | Create a bind group layout.
foreign import createBindGroupLayoutImpl :: GPUDevice -> Foreign -> Effect GPUBindGroupLayout

createBindGroupLayout :: GPUDevice -> Foreign -> Effect GPUBindGroupLayout
createBindGroupLayout = createBindGroupLayoutImpl

-- | Create a pipeline layout.
foreign import createPipelineLayoutImpl :: GPUDevice -> Foreign -> Effect GPUPipelineLayout

createPipelineLayout :: GPUDevice -> Foreign -> Effect GPUPipelineLayout
createPipelineLayout = createPipelineLayoutImpl

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- BIND GROUP OPERATIONS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Create a bind group.
foreign import createBindGroupImpl :: GPUDevice -> Foreign -> Effect GPUBindGroup

createBindGroup :: GPUDevice -> Foreign -> Effect GPUBindGroup
createBindGroup = createBindGroupImpl

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- COMMAND ENCODING
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Create a command encoder.
foreign import createCommandEncoderImpl :: GPUDevice -> Effect GPUCommandEncoder

createCommandEncoder :: GPUDevice -> Effect GPUCommandEncoder
createCommandEncoder = createCommandEncoderImpl

-- | Finish encoding and get command buffer.
foreign import finishCommandEncoderImpl :: GPUCommandEncoder -> Effect GPUCommandBuffer

finishCommandEncoder :: GPUCommandEncoder -> Effect GPUCommandBuffer
finishCommandEncoder = finishCommandEncoderImpl

-- | Begin a render pass.
foreign import beginRenderPassImpl :: GPUCommandEncoder -> Foreign -> Effect GPURenderPassEncoder

beginRenderPass :: GPUCommandEncoder -> GPURenderPassDescriptor -> GPUTextureView -> Maybe GPUTextureView -> Effect GPURenderPassEncoder
beginRenderPass encoder desc colorView depthView =
  beginRenderPassImpl encoder (toForeignRenderPassDesc desc colorView depthView)

-- | End a render pass.
foreign import endRenderPassImpl :: GPURenderPassEncoder -> Effect Unit

endRenderPass :: GPURenderPassEncoder -> Effect Unit
endRenderPass = endRenderPassImpl

-- | Begin a compute pass.
foreign import beginComputePassImpl :: GPUCommandEncoder -> Effect GPUComputePassEncoder

beginComputePass :: GPUCommandEncoder -> Effect GPUComputePassEncoder
beginComputePass = beginComputePassImpl

-- | End a compute pass.
foreign import endComputePassImpl :: GPUComputePassEncoder -> Effect Unit

endComputePass :: GPUComputePassEncoder -> Effect Unit
endComputePass = endComputePassImpl

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- RENDER PASS OPERATIONS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Set the render pipeline.
foreign import setPipelineImpl :: GPURenderPassEncoder -> GPURenderPipeline -> Effect Unit

setPipeline :: GPURenderPassEncoder -> GPURenderPipeline -> Effect Unit
setPipeline = setPipelineImpl

-- | Set a bind group.
foreign import setBindGroupImpl :: GPURenderPassEncoder -> Int -> GPUBindGroup -> Effect Unit

setBindGroup :: GPURenderPassEncoder -> Int -> GPUBindGroup -> Effect Unit
setBindGroup = setBindGroupImpl

-- | Set a vertex buffer.
foreign import setVertexBufferImpl :: GPURenderPassEncoder -> Int -> GPUBuffer -> Int -> Int -> Effect Unit

setVertexBuffer :: GPURenderPassEncoder -> Int -> GPUBuffer -> Effect Unit
setVertexBuffer encoder slot buffer = setVertexBufferImpl encoder slot buffer 0 0

-- | Set the index buffer.
foreign import setIndexBufferImpl :: GPURenderPassEncoder -> GPUBuffer -> String -> Int -> Int -> Effect Unit

setIndexBuffer :: GPURenderPassEncoder -> GPUBuffer -> GPUIndexFormat -> Effect Unit
setIndexBuffer encoder buffer format =
  setIndexBufferImpl encoder buffer (indexFormatToString format) 0 0

-- | Draw primitives.
foreign import drawImpl :: GPURenderPassEncoder -> Int -> Int -> Int -> Int -> Effect Unit

draw :: GPURenderPassEncoder -> Int -> Int -> Int -> Int -> Effect Unit
draw = drawImpl

-- | Draw indexed primitives.
foreign import drawIndexedImpl :: GPURenderPassEncoder -> Int -> Int -> Int -> Int -> Int -> Effect Unit

drawIndexed :: GPURenderPassEncoder -> Int -> Int -> Int -> Int -> Int -> Effect Unit
drawIndexed = drawIndexedImpl

-- | Draw indirect.
foreign import drawIndirectImpl :: GPURenderPassEncoder -> GPUBuffer -> Int -> Effect Unit

drawIndirect :: GPURenderPassEncoder -> GPUBuffer -> Int -> Effect Unit
drawIndirect = drawIndirectImpl

-- | Set viewport.
foreign import setViewportImpl :: GPURenderPassEncoder -> Number -> Number -> Number -> Number -> Number -> Number -> Effect Unit

setViewport :: GPURenderPassEncoder -> Number -> Number -> Number -> Number -> Number -> Number -> Effect Unit
setViewport = setViewportImpl

-- | Set scissor rect.
foreign import setScissorRectImpl :: GPURenderPassEncoder -> Int -> Int -> Int -> Int -> Effect Unit

setScissorRect :: GPURenderPassEncoder -> Int -> Int -> Int -> Int -> Effect Unit
setScissorRect = setScissorRectImpl

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- QUEUE OPERATIONS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Submit command buffers to the queue.
foreign import submitImpl :: GPUQueue -> Array GPUCommandBuffer -> Effect Unit

submit :: GPUQueue -> Array GPUCommandBuffer -> Effect Unit
submit = submitImpl

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- INTERNAL HELPERS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

foreign import toForeignAdapterDesc :: GPUAdapterDescriptor -> Foreign
foreign import toForeignDeviceDesc :: { requiredFeatures :: Array String, label :: Maybe String } -> Foreign
foreign import toForeignCanvasConfig :: GPUCanvasConfiguration -> Foreign
foreign import toForeignBufferDesc :: GPUBufferDescriptor -> Foreign
foreign import toForeignTextureDesc :: GPUTextureDescriptor -> Foreign
foreign import toForeignSamplerDesc :: GPUSamplerDescriptor -> Foreign
foreign import toForeignShaderDesc :: GPUShaderModuleDescriptor -> Foreign
foreign import toForeignTextureDest :: GPUTexture -> Foreign
foreign import toForeignDataLayout :: { width :: Int, height :: Int } -> Foreign
foreign import toForeignSize :: { width :: Int, height :: Int } -> Foreign
foreign import toForeignRenderPassDesc :: GPURenderPassDescriptor -> GPUTextureView -> Maybe GPUTextureView -> Foreign

foreign import fromForeignLimits :: Foreign -> GPULimits

stringToFeature :: String -> GPUFeatureName
stringToFeature = case _ of
  "depth-clip-control" -> DepthClipControl
  "depth32float-stencil8" -> FeatureDepth32FloatStencil8
  "texture-compression-bc" -> TextureCompressionBC
  "texture-compression-etc2" -> TextureCompressionETC2
  "texture-compression-astc" -> TextureCompressionASTC
  "timestamp-query" -> TimestampQuery
  "indirect-first-instance" -> IndirectFirstInstance
  "shader-f16" -> ShaderF16
  "rg11b10ufloat-renderable" -> RG11B10UfloatRenderable
  "bgra8unorm-storage" -> BGRA8UnormStorage
  "float32-filterable" -> Float32Filterable
  _ -> DepthClipControl -- fallback

stringToLostReason :: String -> DeviceLostReason
stringToLostReason = case _ of
  "destroyed" -> DeviceLostDestroyed
  _ -> DeviceLostUnknown

stringToTextureFormat :: String -> GPUTextureFormat
stringToTextureFormat = case _ of
  "bgra8unorm" -> BGRA8Unorm
  "rgba8unorm" -> RGBA8Unorm
  "rgba8unorm-srgb" -> RGBA8UnormSrgb
  "bgra8unorm-srgb" -> BGRA8UnormSrgb
  "depth24plus" -> Depth24Plus
  "depth24plus-stencil8" -> Depth24PlusStencil8
  "depth32float" -> Depth32Float
  _ -> BGRA8Unorm -- default

indexFormatToString :: GPUIndexFormat -> String
indexFormatToString = case _ of
  IndexUint16 -> "uint16"
  IndexUint32 -> "uint32"
