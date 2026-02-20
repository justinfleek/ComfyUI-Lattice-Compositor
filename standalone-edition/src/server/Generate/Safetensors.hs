-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // lattice-server // Generate/Safetensors
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Pure Haskell safetensors parser with memory-mapped file access.
-- Supports all standard dtypes: F32, F16, BF16, F64, I64, I32, I16, I8, U8, BOOL
--
-- Format:
--   8 bytes: header_size (little-endian u64)
--   header_size bytes: JSON header with tensor metadata
--   remaining bytes: raw tensor data (aligned)
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Generate.Safetensors
    ( -- * Types
      SafetensorsFile(..)
    , TensorHeader(..)
    , DType(..)
    , SafetensorsError(..)

      -- * Loading
    , openSafetensors
    , closeSafetensors
    , withSafetensors

      -- * Tensor Access
    , getTensorNames
    , getTensorHeader
    , getTensorData
    , getTensorDataFloat32

      -- * Utilities
    , dtypeSize
    , dtypeFromText
    , dtypeToText
    ) where

import Control.Exception (Exception, bracket, throwIO)
import Control.Monad (when)
import Data.Aeson (FromJSON(..), (.:))
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.Key as Key
import qualified Data.Aeson.KeyMap as KM
import Data.Aeson.Types (Parser, parseMaybe)
import Data.Bits (shiftL, shiftR, (.&.))
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import Data.Vector.Storable (Vector)
import qualified Data.Vector.Storable as VS
import Data.Word (Word8, Word16, Word32, Word64)
import Foreign.ForeignPtr (ForeignPtr, newForeignPtr_)
import Foreign.Ptr (Ptr, plusPtr, castPtr)
import Foreign.Storable (peek)
import GHC.Generics (Generic)
import System.IO.MMap (Mode(..), mmapFilePtr)


-- ═══════════════════════════════════════════════════════════════════════════
-- // types //
-- ═══════════════════════════════════════════════════════════════════════════

-- | Safetensors data type
data DType
    = F32       -- ^ 32-bit float
    | F16       -- ^ 16-bit float (half precision)
    | BF16      -- ^ BFloat16
    | F64       -- ^ 64-bit float (double)
    | I64       -- ^ 64-bit signed integer
    | I32       -- ^ 32-bit signed integer
    | I16       -- ^ 16-bit signed integer
    | I8        -- ^ 8-bit signed integer
    | U8        -- ^ 8-bit unsigned integer
    | BOOL      -- ^ Boolean (1 byte)
    deriving (Eq, Show, Generic)

instance FromJSON DType where
    parseJSON = Aeson.withText "DType" $ \t ->
        case dtypeFromText t of
            Just dt -> pure dt
            Nothing -> fail $ "Unknown dtype: " <> T.unpack t


-- | Tensor header metadata from safetensors
data TensorHeader = TensorHeader
    { thDtype :: DType
    , thShape :: [Int]
    , thDataOffsets :: (Int, Int)   -- (start, end) relative to data section
    } deriving (Eq, Show, Generic)

instance FromJSON TensorHeader where
    parseJSON = Aeson.withObject "TensorHeader" $ \v -> TensorHeader
        <$> v .: "dtype"
        <*> v .: "shape"
        <*> parseOffsets v
      where
        parseOffsets v = do
            offsets <- v .: "data_offsets" :: Parser [Int]
            case offsets of
                [start, end] -> pure (start, end)
                _ -> fail "data_offsets must be [start, end]"


-- | Parsed safetensors file with memory-mapped data
data SafetensorsFile = SafetensorsFile
    { stPath :: FilePath
    , stHeaderSize :: Int
    , stTensors :: Map Text TensorHeader
    , stMetadata :: Maybe (Map Text Text)
    , stDataPtr :: ForeignPtr Word8         -- Memory-mapped file data
    , stDataSize :: Int                     -- Total file size
    }

-- | Errors that can occur when loading safetensors
data SafetensorsError
    = InvalidMagic String
    | InvalidHeader String
    | InvalidJSON String
    | TensorNotFound Text
    | DtypeMismatch DType DType
    | IOError String
    deriving (Eq, Show)

instance Exception SafetensorsError


-- ═══════════════════════════════════════════════════════════════════════════
-- // loading //
-- ═══════════════════════════════════════════════════════════════════════════

-- | Open a safetensors file (memory-mapped)
openSafetensors :: FilePath -> IO SafetensorsFile
openSafetensors path = do
    -- Memory map the entire file
    (ptr, _rawSize, offset, size) <- mmapFilePtr path ReadOnly Nothing

    when (size < 8) $
        throwIO $ InvalidHeader "File too small to contain header size"

    -- Read header size (first 8 bytes, little-endian u64)
    let headerSizePtr = ptr `plusPtr` offset
    headerSizeU64 <- peekLE64 (castPtr headerSizePtr)
    let headerSize = fromIntegral headerSizeU64

    when (headerSize > size - 8) $
        throwIO $ InvalidHeader "Header size exceeds file size"

    -- Read header JSON
    let headerStart = ptr `plusPtr` (offset + 8)
    headerBytes <- BS.packCStringLen (castPtr headerStart, headerSize)

    -- Parse header JSON
    case Aeson.eitherDecodeStrict headerBytes of
        Left err -> throwIO $ InvalidJSON err
        Right obj -> do
            let (tensors, metadata) = parseHeader obj
            fptr <- newForeignPtr_ (castPtr ptr)
            pure $ SafetensorsFile
                { stPath = path
                , stHeaderSize = headerSize
                , stTensors = tensors
                , stMetadata = metadata
                , stDataPtr = fptr
                , stDataSize = size
                }
  where
    -- Parse the full header object
    parseHeader :: Aeson.Object -> (Map Text TensorHeader, Maybe (Map Text Text))
    parseHeader obj =
        let tensors = Map.fromList
                [ (Key.toText k, th)
                | (k, v) <- KM.toList obj
                , k /= "__metadata__"
                , Just th <- [parseMaybe parseJSON v]
                ]
            metadata = case KM.lookup "__metadata__" obj of
                Just (Aeson.Object m) ->
                    Just $ Map.fromList
                        [ (Key.toText k, t)
                        | (k, Aeson.String t) <- KM.toList m
                        ]
                _ -> Nothing
        in (tensors, metadata)

-- | Read little-endian u64
peekLE64 :: Ptr Word8 -> IO Word64
peekLE64 ptr = do
    b0 :: Word8 <- peek ptr
    b1 :: Word8 <- peek (ptr `plusPtr` 1)
    b2 :: Word8 <- peek (ptr `plusPtr` 2)
    b3 :: Word8 <- peek (ptr `plusPtr` 3)
    b4 :: Word8 <- peek (ptr `plusPtr` 4)
    b5 :: Word8 <- peek (ptr `plusPtr` 5)
    b6 :: Word8 <- peek (ptr `plusPtr` 6)
    b7 :: Word8 <- peek (ptr `plusPtr` 7)
    pure $! (fromIntegral b0 :: Word64)
        + (fromIntegral b1 `shiftL` 8)
        + (fromIntegral b2 `shiftL` 16)
        + (fromIntegral b3 `shiftL` 24)
        + (fromIntegral b4 `shiftL` 32)
        + (fromIntegral b5 `shiftL` 40)
        + (fromIntegral b6 `shiftL` 48)
        + (fromIntegral b7 `shiftL` 56)


-- | Close a safetensors file
-- Note: The memory-mapped region is automatically unmapped when the ForeignPtr is GC'd
closeSafetensors :: SafetensorsFile -> IO ()
closeSafetensors _ = pure ()  -- ForeignPtr handles cleanup


-- | Bracket for safe file handling
withSafetensors :: FilePath -> (SafetensorsFile -> IO a) -> IO a
withSafetensors path = bracket (openSafetensors path) closeSafetensors


-- ═══════════════════════════════════════════════════════════════════════════
-- // tensor access //
-- ═══════════════════════════════════════════════════════════════════════════

-- | Get list of tensor names
getTensorNames :: SafetensorsFile -> [Text]
getTensorNames = Map.keys . stTensors


-- | Get tensor header by name
getTensorHeader :: SafetensorsFile -> Text -> Either SafetensorsError TensorHeader
getTensorHeader sf name =
    case Map.lookup name (stTensors sf) of
        Just h -> Right h
        Nothing -> Left $ TensorNotFound name


-- | Get raw tensor data as ByteString
getTensorData :: SafetensorsFile -> Text -> IO (Either SafetensorsError ByteString)
getTensorData sf name = do
    case getTensorHeader sf name of
        Left err -> pure $ Left err
        Right hdr -> do
            let (startOffset, endOffset) = thDataOffsets hdr
            let dataStart = 8 + stHeaderSize sf + startOffset
            let len = endOffset - startOffset

            -- Use withForeignPtr to access the memory
            bs <- VS.unsafeWith (VS.unsafeFromForeignPtr0 (stDataPtr sf) (stDataSize sf)) $ \ptr -> do
                BS.packCStringLen (castPtr (ptr `plusPtr` dataStart), len)

            pure $ Right bs


-- | Get tensor data as Float32 vector
-- Converts from the source dtype to Float32
getTensorDataFloat32 :: SafetensorsFile -> Text -> IO (Either SafetensorsError (Vector Float, [Int]))
getTensorDataFloat32 sf name = do
    case getTensorHeader sf name of
        Left err -> pure $ Left err
        Right hdr -> do
            let shape = thShape hdr
            let dtype = thDtype hdr
            let (startOffset, endOffset) = thDataOffsets hdr
            let dataStart = 8 + stHeaderSize sf + startOffset
            let len = endOffset - startOffset

            -- Direct memory access for float32
            case dtype of
                F32 -> do
                    let numFloats = len `div` 4
                    vec <- VS.unsafeWith (VS.unsafeFromForeignPtr0 (stDataPtr sf) (stDataSize sf)) $ \ptr -> do
                        let floatPtr = castPtr (ptr `plusPtr` dataStart) :: Ptr Float
                        -- Create a vector from the memory
                        VS.generateM numFloats $ \i -> peek (floatPtr `plusPtr` (i * 4))
                    pure $ Right (vec, shape)

                F16 -> do
                    -- F16 requires conversion
                    let numFloats = len `div` 2
                    vec <- VS.unsafeWith (VS.unsafeFromForeignPtr0 (stDataPtr sf) (stDataSize sf)) $ \ptr -> do
                        let halfPtr = castPtr (ptr `plusPtr` dataStart) :: Ptr Word16
                        VS.generateM numFloats $ \i -> do
                            half <- peek (halfPtr `plusPtr` (i * 2))
                            pure $ halfToFloat half
                    pure $ Right (vec, shape)

                BF16 -> do
                    -- BF16 requires conversion
                    let numFloats = len `div` 2
                    vec <- VS.unsafeWith (VS.unsafeFromForeignPtr0 (stDataPtr sf) (stDataSize sf)) $ \ptr -> do
                        let bfPtr = castPtr (ptr `plusPtr` dataStart) :: Ptr Word16
                        VS.generateM numFloats $ \i -> do
                            bf <- peek (bfPtr `plusPtr` (i * 2))
                            pure $ bf16ToFloat bf
                    pure $ Right (vec, shape)

                _ -> pure $ Left $ DtypeMismatch dtype F32


-- ═══════════════════════════════════════════════════════════════════════════
-- // utilities //
-- ═══════════════════════════════════════════════════════════════════════════

-- | Get byte size of a dtype
dtypeSize :: DType -> Int
dtypeSize F32  = 4
dtypeSize F16  = 2
dtypeSize BF16 = 2
dtypeSize F64  = 8
dtypeSize I64  = 8
dtypeSize I32  = 4
dtypeSize I16  = 2
dtypeSize I8   = 1
dtypeSize U8   = 1
dtypeSize BOOL = 1


-- | Parse dtype from text
dtypeFromText :: Text -> Maybe DType
dtypeFromText "F32"  = Just F32
dtypeFromText "F16"  = Just F16
dtypeFromText "BF16" = Just BF16
dtypeFromText "F64"  = Just F64
dtypeFromText "I64"  = Just I64
dtypeFromText "I32"  = Just I32
dtypeFromText "I16"  = Just I16
dtypeFromText "I8"   = Just I8
dtypeFromText "U8"   = Just U8
dtypeFromText "BOOL" = Just BOOL
dtypeFromText _      = Nothing


-- | Convert dtype to text
dtypeToText :: DType -> Text
dtypeToText F32  = "F32"
dtypeToText F16  = "F16"
dtypeToText BF16 = "BF16"
dtypeToText F64  = "F64"
dtypeToText I64  = "I64"
dtypeToText I32  = "I32"
dtypeToText I16  = "I16"
dtypeToText I8   = "I8"
dtypeToText U8   = "U8"
dtypeToText BOOL = "BOOL"


-- ═══════════════════════════════════════════════════════════════════════════
-- // float16 conversion //
-- ═══════════════════════════════════════════════════════════════════════════

-- | Convert IEEE 754 half-precision float to single-precision
-- Using bit manipulation as in the standard conversion
halfToFloat :: Word16 -> Float
halfToFloat h =
    let sign = (h `shiftR` 15) .&. 0x1
        expo = (h `shiftR` 10) .&. 0x1F
        mant = h .&. 0x3FF
    in case expo of
        0 -> if mant == 0
             then if sign == 0 then 0.0 else -0.0
             else -- Denormalized number
                  let m = fromIntegral mant / 1024.0 * (2 ** (-14))
                  in if sign == 0 then m else -m
        31 -> if mant == 0
              then if sign == 0 then (1/0) else -(1/0)  -- Infinity
              else (0/0)  -- NaN
        _ -> -- Normalized number
             let e = fromIntegral expo - 15
                 m = 1.0 + fromIntegral mant / 1024.0
                 v = m * (2 ** e)
             in if sign == 0 then v else -v


-- | Convert BFloat16 to single-precision
-- BF16 is just the upper 16 bits of a float32
bf16ToFloat :: Word16 -> Float
bf16ToFloat bf =
    let w32 = (fromIntegral bf :: Word32) `shiftL` 16
    in castWord32ToFloat w32


-- | Reinterpret Word32 bits as Float
castWord32ToFloat :: Word32 -> Float
castWord32ToFloat w = VS.unsafeIndex vec 0
  where
    vec = VS.unsafeCast (VS.singleton w) :: Vector Float
