{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}

-- | Foreign Function Interface to TensorRT C++ engine
-- Allows Haskell diffusion math to drive GPU inference
module Lattice.Diffusion.TensorRT.FFI
  ( -- * Engine Management
    TRTEngine
  , trtLoadEngine
  , trtBuildFromONNX
  , trtSaveEngine
  , trtFreeEngine
  
    -- * Context Management
  , TRTContext
  , trtCreateContext
  , trtFreeContext
  
    -- * Inference
  , trtSetInputShape
  , trtSetTensorAddress
  , trtEnqueue
  
    -- * Engine Info
  , trtNumIOTensors
  , trtIOTensorName
  , trtIsInput
  
    -- * CUDA Memory
  , cudaMalloc
  , cudaFree
  , cudaMemcpyHtoD
  , cudaMemcpyDtoH
  , cudaStreamCreate
  , cudaStreamDestroy
  , cudaStreamSynchronize
  
    -- * Types
  , CudaStream
  , CudaPtr
  ) where

import Foreign.Ptr (Ptr, FunPtr, nullPtr)
import Foreign.C.Types
import Foreign.C.String
import Foreign.Marshal.Alloc
import Foreign.Storable
import Data.Word

-- | Opaque TensorRT engine handle
data TRTEngineHandle
type TRTEngine = Ptr TRTEngineHandle

-- | Opaque TensorRT context handle
data TRTContextHandle
type TRTContext = Ptr TRTContextHandle

-- | CUDA stream handle
data CudaStreamHandle
type CudaStream = Ptr CudaStreamHandle

-- | CUDA device pointer
type CudaPtr = Ptr ()

--------------------------------------------------------------------------------
-- Engine Management FFI
--------------------------------------------------------------------------------

-- | Load a serialized TensorRT engine from file
foreign import ccall unsafe "lattice_trt_load_engine"
  trtLoadEngine :: CString -> IO TRTEngine

-- | Build TensorRT engine from ONNX file
-- Returns null on failure
foreign import ccall unsafe "lattice_trt_build_from_onnx"
  trtBuildFromONNX :: CString   -- ^ ONNX path
                   -> CInt      -- ^ FP16 flag
                   -> CInt      -- ^ INT8 flag
                   -> CSize     -- ^ Workspace size
                   -> IO TRTEngine

-- | Save engine to file
foreign import ccall unsafe "lattice_trt_save_engine"
  trtSaveEngine :: TRTEngine -> CString -> IO CInt

-- | Free TensorRT engine
foreign import ccall unsafe "lattice_trt_free_engine"
  trtFreeEngine :: TRTEngine -> IO ()

--------------------------------------------------------------------------------
-- Context Management FFI
--------------------------------------------------------------------------------

-- | Create execution context from engine
foreign import ccall unsafe "lattice_trt_create_context"
  trtCreateContext :: TRTEngine -> IO TRTContext

-- | Free execution context
foreign import ccall unsafe "lattice_trt_free_context"
  trtFreeContext :: TRTContext -> IO ()

--------------------------------------------------------------------------------
-- Inference FFI
--------------------------------------------------------------------------------

-- | Set input shape for dynamic dimensions
foreign import ccall unsafe "lattice_trt_set_input_shape"
  trtSetInputShape :: TRTContext
                   -> CString     -- ^ Tensor name
                   -> Ptr CInt    -- ^ Dims array
                   -> CInt        -- ^ Num dims
                   -> IO CInt

-- | Set tensor address (GPU pointer)
foreign import ccall unsafe "lattice_trt_set_tensor_address"
  trtSetTensorAddress :: TRTContext
                      -> CString  -- ^ Tensor name
                      -> CudaPtr  -- ^ GPU pointer
                      -> IO CInt

-- | Enqueue inference on CUDA stream
foreign import ccall unsafe "lattice_trt_enqueue"
  trtEnqueue :: TRTContext -> CudaStream -> IO CInt

--------------------------------------------------------------------------------
-- Engine Info FFI
--------------------------------------------------------------------------------

-- | Get number of input/output tensors
foreign import ccall unsafe "lattice_trt_num_io_tensors"
  trtNumIOTensors :: TRTEngine -> IO CInt

-- | Get tensor name by index
foreign import ccall unsafe "lattice_trt_io_tensor_name"
  trtIOTensorName :: TRTEngine -> CInt -> IO CString

-- | Check if tensor is input
foreign import ccall unsafe "lattice_trt_is_input"
  trtIsInput :: TRTEngine -> CString -> IO CInt

--------------------------------------------------------------------------------
-- CUDA Memory FFI
--------------------------------------------------------------------------------

-- | Allocate GPU memory
foreign import ccall unsafe "cudaMalloc"
  cudaMalloc :: Ptr CudaPtr -> CSize -> IO CInt

-- | Free GPU memory
foreign import ccall unsafe "cudaFree"
  cudaFree :: CudaPtr -> IO CInt

-- | Copy host to device
foreign import ccall unsafe "cudaMemcpy"
  cudaMemcpyHtoD :: CudaPtr       -- ^ Destination (device)
                 -> Ptr ()        -- ^ Source (host)
                 -> CSize         -- ^ Size in bytes
                 -> CInt          -- ^ Direction (1 = HtoD)
                 -> IO CInt

-- | Copy device to host
cudaMemcpyDtoH :: Ptr ()        -- ^ Destination (host)
               -> CudaPtr       -- ^ Source (device)
               -> CSize         -- ^ Size in bytes
               -> IO CInt
cudaMemcpyDtoH dst src size = cudaMemcpyHtoD (castPtr dst) src size 2
  where
    castPtr :: Ptr a -> CudaPtr
    castPtr = id  -- Both are Ptr ()

-- | Create CUDA stream
foreign import ccall unsafe "cudaStreamCreate"
  cudaStreamCreate :: Ptr CudaStream -> IO CInt

-- | Destroy CUDA stream
foreign import ccall unsafe "cudaStreamDestroy"
  cudaStreamDestroy :: CudaStream -> IO CInt

-- | Synchronize CUDA stream
foreign import ccall unsafe "cudaStreamSynchronize"
  cudaStreamSynchronize :: CudaStream -> IO CInt
