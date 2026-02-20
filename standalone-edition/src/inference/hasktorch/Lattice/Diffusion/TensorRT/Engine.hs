{-# LANGUAGE RecordWildCards #-}

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
  
    -- * Build Config
  , BuildConfig(..)
  , defaultBuildConfig
  
    -- * Error Handling
  , TRTError(..)
  ) where

import Lattice.Diffusion.TensorRT.FFI

import Control.Exception (bracket, Exception, throwIO)
import Control.Monad (when)
import Data.IORef
import Foreign.Ptr
import Foreign.C.String
import Foreign.C.Types
import Foreign.Marshal.Alloc
import Foreign.Marshal.Array
import Foreign.Storable
import qualified Data.Vector.Storable as V
import Data.Vector.Storable (Vector)

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

-- | Build configuration
data BuildConfig = BuildConfig
  { bcFP16          :: !Bool
  , bcINT8          :: !Bool
  , bcWorkspaceSize :: !Int  -- in MB
  } deriving (Show, Eq)

-- | Default build configuration
defaultBuildConfig :: BuildConfig
defaultBuildConfig = BuildConfig
  { bcFP16 = True
  , bcINT8 = False
  , bcWorkspaceSize = 1024  -- 1GB
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
  let fp16Flag = if bcFP16 then 1 else 0
      int8Flag = if bcINT8 then 1 else 0
      wsSize = fromIntegral (bcWorkspaceSize * 1024 * 1024)
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
  let isInputIO i = do
        cname <- newCString (names !! fromIntegral i)
        result <- trtIsInput ptr cname
        free cname
        pure (result /= 0)
  inputFlags <- mapM isInputIO indices
  let inputs = [n | (n, True) <- zip names inputFlags]
      outputs = [n | (n, False) <- zip names inputFlags]
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

-- | Copy data from host to device
copyToDevice :: Storable a => Buffer -> Vector a -> IO (Either TRTError ())
copyToDevice Buffer{..} vec = do
  let (fptr, len) = V.unsafeToForeignPtr0 vec
      byteSize = len * sizeOf (V.head vec)
  when (byteSize > bufferSize) $
    throwIO $ TRTError "Buffer too small for data"
  V.unsafeWith vec $ \ptr -> do
    result <- cudaMemcpyHtoD bufferPtr (castPtr ptr) (fromIntegral byteSize) 1
    pure $ if result == 0
      then Right ()
      else Left $ TRTError $ "cudaMemcpy HtoD failed: " ++ show result

-- | Copy data from device to host
copyToHost :: Storable a => Buffer -> Int -> IO (Either TRTError (Vector a))
copyToHost Buffer{..} numElements = do
  vec <- V.new numElements
  V.unsafeWith vec $ \ptr -> do
    let byteSize = numElements * sizeOf (V.head vec)
    result <- cudaMemcpyHtoD (castPtr ptr) bufferPtr (fromIntegral byteSize) 2
    pure $ if result == 0
      then Right vec
      else Left $ TRTError $ "cudaMemcpy DtoH failed: " ++ show result
