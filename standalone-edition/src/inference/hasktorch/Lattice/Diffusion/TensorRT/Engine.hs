{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | High-level TensorRT engine wrapper for Haskell
-- Provides safe, idiomatic interface to GPU inference
module Lattice.Diffusion.TensorRT.Engine
  ( -- * Engine Types
    Engine(..)
  , Context(..)
  , Stream(..)
  , Buffer(..)
  
    -- * Engine Operations
  , loadEngine
  , buildEngine
  , saveEngine
  , withEngine
  
    -- * Context Operations
  , createContext
  , withContext
  
    -- * Inference
  , infer
  , inferBatch
  
    -- * Buffer Management
  , allocateBuffer
  , freeBuffer
  , copyToDevice
  , copyToHost
  
    -- * Type-Level Size
  , SizedStorable(..)
  , ElemSize
  
    -- * Build Config
  , BuildConfig(..)
  , Precision(..)
  , Quantization(..)
  , WorkspaceSize(..)
  , defaultBuildConfig
  , fp16Config
  , int8Config
  
    -- * Error Handling
  , TRTError(..)
  ) where

import Lattice.Diffusion.TensorRT.FFI

import Control.Exception (Exception, throwIO)
import Control.Monad (when)
import Data.Int (Int32, Int64)
import Data.Kind (Type)
import Data.Proxy (Proxy(..))
import Data.Word (Word8, Word16, Word32, Word64)
import Foreign.Ptr
import Foreign.C.String
import Foreign.C.Types
import Foreign.Marshal.Alloc
import Foreign.Marshal.Array
import Foreign.Storable
import GHC.TypeLits (Nat, KnownNat, natVal)
import qualified Data.Vector.Storable as V
import qualified Data.Vector.Storable.Mutable as VM
import Data.Vector.Storable (Vector)

--------------------------------------------------------------------------------
-- Type-Level Element Size
--------------------------------------------------------------------------------

-- | Type family mapping Storable types to their size at the type level.
-- This allows size computation without runtime values - the compiler 
-- knows the size from the type alone, like dependent types in Lean4.
type family ElemSize (a :: Type) :: Nat where
  ElemSize Float  = 4
  ElemSize Double = 8
  ElemSize Int    = 8   -- 64-bit
  ElemSize Int32  = 4
  ElemSize Int64  = 8
  ElemSize Word   = 8
  ElemSize Word8  = 1
  ElemSize Word16 = 2
  ElemSize Word32 = 4
  ElemSize Word64 = 8
  ElemSize CFloat = 4
  ElemSize CDouble = 8

-- | Witness class connecting type-level size to value-level.
-- The constraint (KnownNat (ElemSize a)) proves at compile time that
-- we can compute the size without evaluating any value.
class (Storable a, KnownNat (ElemSize a)) => SizedStorable a where
  elemSize :: Proxy a -> Int
  elemSize _ = fromIntegral $ natVal (Proxy @(ElemSize a))

-- Instances - these are compile-time proofs that sizes are known
instance SizedStorable Float
instance SizedStorable Double
instance SizedStorable Int
instance SizedStorable Int32
instance SizedStorable Int64
instance SizedStorable Word
instance SizedStorable Word8
instance SizedStorable Word16
instance SizedStorable Word32
instance SizedStorable Word64
instance SizedStorable CFloat
instance SizedStorable CDouble

-- | TensorRT error
newtype TRTError = TRTError String
  deriving (Show, Eq)

instance Exception TRTError

-- | TensorRT engine handle
data Engine = Engine
  { enginePtr    :: !TRTEngine
  , engineInputs :: ![String]
  , engineOutputs :: ![String]
  }

-- | Execution context
newtype Context = Context { contextPtr :: TRTContext }

-- | CUDA stream
newtype Stream = Stream { streamPtr :: CudaStream }

-- | GPU buffer
data Buffer = Buffer
  { bufferPtr  :: !CudaPtr
  , bufferSize :: !Int
  }

-- | Precision mode for TensorRT inference.
-- Each constructor documents exactly what precision will be used.
data Precision
  = FP32          -- ^ Full 32-bit floating point (slowest, highest precision)
  | FP16          -- ^ 16-bit floating point (2x faster on Tensor Cores)
  | TF32          -- ^ TensorFloat-32 (FP32 range, FP16 precision)
  deriving (Show, Eq, Ord, Enum, Bounded)

-- | Quantization mode for weight compression.
-- INT8 requires calibration data for accuracy.
data Quantization
  = NoQuantization    -- ^ Keep weights in floating point
  | INT8Quantized     -- ^ 8-bit integer weights (4x memory reduction)
  | FP4Quantized      -- ^ 4-bit NVFP4 (E2M1) - requires Blackwell/Ada+
  deriving (Show, Eq, Ord, Enum, Bounded)

-- | Workspace size with explicit units - no more magic numbers.
data WorkspaceSize
  = WorkspaceMB !Int    -- ^ Size in megabytes
  | WorkspaceGB !Int    -- ^ Size in gigabytes  
  deriving (Show, Eq)

-- | Convert workspace size to bytes
workspaceBytes :: WorkspaceSize -> Int
workspaceBytes (WorkspaceMB mb) = mb * 1024 * 1024
workspaceBytes (WorkspaceGB gb) = gb * 1024 * 1024 * 1024

-- | Build configuration with explicit, self-documenting types.
-- No Bool flags - each setting is a distinct type that documents intent.
data BuildConfig = BuildConfig
  { bcPrecision    :: !Precision       -- ^ Compute precision
  , bcQuantization :: !Quantization    -- ^ Weight quantization
  , bcWorkspace    :: !WorkspaceSize   -- ^ GPU workspace for layer fusion
  } deriving (Show, Eq)

-- | Default: FP16 precision, no quantization, 1GB workspace.
-- Good balance of speed and quality for most models.
defaultBuildConfig :: BuildConfig
defaultBuildConfig = BuildConfig
  { bcPrecision    = FP16
  , bcQuantization = NoQuantization
  , bcWorkspace    = WorkspaceGB 1
  }

-- | FP16 config for maximum Tensor Core utilization.
fp16Config :: BuildConfig
fp16Config = defaultBuildConfig

-- | INT8 quantized config for inference-optimized deployment.
-- Requires calibration dataset for accurate results.
int8Config :: BuildConfig
int8Config = BuildConfig
  { bcPrecision    = FP16           -- Compute in FP16
  , bcQuantization = INT8Quantized  -- But store weights as INT8
  , bcWorkspace    = WorkspaceGB 2  -- More workspace for quantization kernels
  }

--------------------------------------------------------------------------------
-- Engine Operations
--------------------------------------------------------------------------------

-- | Load a serialized TensorRT engine
loadEngine :: FilePath -> IO (Either TRTError Engine)
loadEngine path = do
  cpath <- newCString path
  ptr <- trtLoadEngine cpath
  free cpath
  if ptr == nullPtr
    then pure $ Left $ TRTError $ "Failed to load engine: " ++ path
    else do
      (inputs, outputs) <- getIOTensors ptr
      pure $ Right Engine
        { enginePtr = ptr
        , engineInputs = inputs
        , engineOutputs = outputs
        }

-- | Build TensorRT engine from ONNX
buildEngine :: FilePath -> BuildConfig -> IO (Either TRTError Engine)
buildEngine onnxPath BuildConfig{..} = do
  cpath <- newCString onnxPath
  let fp16Flag = case bcPrecision of
        FP32 -> 0
        FP16 -> 1
        TF32 -> 0  -- TF32 handled via separate CUDA flag
      int8Flag = case bcQuantization of
        NoQuantization -> 0
        INT8Quantized  -> 1
        FP4Quantized   -> 2  -- Custom flag for NVFP4
      wsSize = fromIntegral $ workspaceBytes bcWorkspace
  ptr <- trtBuildFromONNX cpath fp16Flag int8Flag wsSize
  free cpath
  if ptr == nullPtr
    then pure $ Left $ TRTError $ "Failed to build engine from: " ++ onnxPath
    else do
      (inputs, outputs) <- getIOTensors ptr
      pure $ Right Engine
        { enginePtr = ptr
        , engineInputs = inputs
        , engineOutputs = outputs
        }

-- | Save engine to file
saveEngine :: Engine -> FilePath -> IO (Either TRTError ())
saveEngine Engine{..} path = do
  cpath <- newCString path
  result <- trtSaveEngine enginePtr cpath
  free cpath
  pure $ if result == 0
    then Right ()
    else Left $ TRTError $ "Failed to save engine to: " ++ path

-- | Use engine with automatic cleanup
withEngine :: FilePath -> (Engine -> IO a) -> IO (Either TRTError a)
withEngine path action = do
  result <- loadEngine path
  case result of
    Left err -> pure $ Left err
    Right engine -> do
      a <- action engine
      trtFreeEngine (enginePtr engine)
      pure $ Right a

-- | Get input/output tensor names
getIOTensors :: TRTEngine -> IO ([String], [String])
getIOTensors ptr = do
  numTensors <- trtNumIOTensors ptr
  let indices = [0..numTensors - 1]
  names <- mapM (getTensorName ptr) indices
  -- Pair indices with names for safe lookup
  let checkInput (i, name) = do
        cname <- newCString name
        result <- trtIsInput ptr cname
        free cname
        pure (name, result /= 0)
  pairs <- mapM checkInput (zip indices names)
  let inputs = [n | (n, True) <- pairs]
      outputs = [n | (n, False) <- pairs]
  pure (inputs, outputs)

getTensorName :: TRTEngine -> CInt -> IO String
getTensorName ptr idx = do
  cstr <- trtIOTensorName ptr idx
  peekCString cstr

--------------------------------------------------------------------------------
-- Context Operations
--------------------------------------------------------------------------------

-- | Create execution context
createContext :: Engine -> IO (Either TRTError Context)
createContext Engine{..} = do
  ptr <- trtCreateContext enginePtr
  pure $ if ptr == nullPtr
    then Left $ TRTError "Failed to create context"
    else Right $ Context ptr

-- | Use context with automatic cleanup
withContext :: Engine -> (Context -> IO a) -> IO (Either TRTError a)
withContext engine action = do
  result <- createContext engine
  case result of
    Left err -> pure $ Left err
    Right ctx -> do
      a <- action ctx
      trtFreeContext (contextPtr ctx)
      pure $ Right a

--------------------------------------------------------------------------------
-- Inference
--------------------------------------------------------------------------------

-- | Run inference with a single input/output
infer :: Context
      -> Stream
      -> [(String, Buffer)]  -- ^ Input tensors (name, buffer)
      -> [(String, Buffer)]  -- ^ Output tensors (name, buffer)
      -> IO (Either TRTError ())
infer Context{..} Stream{..} inputs outputs = do
  -- Set all tensor addresses
  let setTensor (name, Buffer{..}) = do
        cname <- newCString name
        result <- trtSetTensorAddress contextPtr cname bufferPtr
        free cname
        pure result
  
  inputResults <- mapM setTensor inputs
  outputResults <- mapM setTensor outputs
  
  if any (== 0) (inputResults ++ outputResults)
    then pure $ Left $ TRTError "Failed to set tensor addresses"
    else do
      result <- trtEnqueue contextPtr streamPtr
      pure $ if result /= 0
        then Right ()
        else Left $ TRTError "Inference failed"

-- | Run batched inference (multiple forward passes)
inferBatch :: Context -> Stream -> Int -> IO ()
inferBatch _ _ _ = pure ()  -- Placeholder for batch scheduling

--------------------------------------------------------------------------------
-- Buffer Management
--------------------------------------------------------------------------------

-- | Allocate GPU buffer
allocateBuffer :: Int -> IO (Either TRTError Buffer)
allocateBuffer size = do
  ptrRef <- malloc :: IO (Ptr CudaPtr)
  result <- cudaMalloc ptrRef (fromIntegral size)
  if result /= 0
    then do
      free ptrRef
      pure $ Left $ TRTError $ "cudaMalloc failed with error: " ++ show result
    else do
      ptr <- peek ptrRef
      free ptrRef
      pure $ Right Buffer { bufferPtr = ptr, bufferSize = size }

-- | Free GPU buffer
freeBuffer :: Buffer -> IO ()
freeBuffer Buffer{..} = do
  _ <- cudaFree bufferPtr
  pure ()

-- | Copy data from host to device.
-- Uses SizedStorable constraint to compute element size at the type level -
-- no runtime value inspection, the size is known statically from the type.
copyToDevice :: forall a. SizedStorable a => Buffer -> Vector a -> IO (Either TRTError ())
copyToDevice Buffer{..} vec = do
  let len = V.length vec
      byteSize = len * elemSize (Proxy @a)  -- Type-level size computation!
  when (byteSize > bufferSize) $
    throwIO $ TRTError "Buffer too small for data"
  V.unsafeWith vec $ \ptr -> do
    result <- cudaMemcpyHtoD bufferPtr (castPtr ptr) (fromIntegral byteSize) 1
    pure $ if result == 0
      then Right ()
      else Left $ TRTError $ "cudaMemcpy HtoD failed: " ++ show result

-- | Copy data from device to host.
-- Element size derived from type-level Nat via SizedStorable.
copyToHost :: forall a. SizedStorable a => Buffer -> Int -> IO (Either TRTError (Vector a))
copyToHost Buffer{..} numElements = do
  let byteSize = numElements * elemSize (Proxy @a)  -- Compile-time size!
  -- Create mutable vector, copy data into it, then freeze
  mvec <- VM.new numElements
  VM.unsafeWith mvec $ \ptr -> do
    result <- cudaMemcpyHtoD (castPtr ptr) bufferPtr (fromIntegral byteSize) 2
    if result == 0
      then do
        vec <- V.unsafeFreeze mvec
        pure $ Right vec
      else pure $ Left $ TRTError $ "cudaMemcpy DtoH failed: " ++ show result
