{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

{-|
Module      : Lattice.Services.Bridge.Protocol
Description : WebSocket-ZMQ bridge message protocol
Copyright   : (c) Lattice, 2026
License     : MIT

Defines the message types for communication between PureScript UI
and Haskell backend over WebSocket.

The protocol is request-response based with tagged message IDs for
async correlation. All heavy operations (WebGL, Canvas, IndexedDB,
WebCodecs, MIDI) are handled server-side.
-}

module Lattice.Services.Bridge.Protocol
  ( -- * Message Types
    Request(..)
  , Response(..)
  , MessageId
    -- * Operation Types
  , RenderOp(..)
  , StorageOp(..)
  , ExportOp(..)
  , MathOp(..)
    -- * Data Types
  , FrameData(..)
  , DepthBuffer(..)
  , ShaderProgram(..)
  , Uniforms(..)
  , UniformValue(..)
    -- * Encoding/Decoding
  , encodeResponse
  , decodeRequest
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Data.ByteString (ByteString)
import qualified Data.ByteString.Lazy as LBS
import Data.Aeson (FromJSON, ToJSON, encode, decode)
import Data.Word (Word32, Word64)
import Data.Int (Int32)
import qualified Data.Vector.Storable as VS

-- ────────────────────────────────────────────────────────────────────────────
-- Message ID
-- ────────────────────────────────────────────────────────────────────────────

-- | Unique message identifier for request-response correlation
type MessageId = Word64

-- ────────────────────────────────────────────────────────────────────────────
-- Request
-- ────────────────────────────────────────────────────────────────────────────

-- | Incoming request from PureScript UI
data Request
  = ReqRender !MessageId !RenderOp
  | ReqStorage !MessageId !StorageOp
  | ReqExport !MessageId !ExportOp
  | ReqMath !MessageId !MathOp
  | ReqPing !MessageId
  deriving stock (Eq, Show, Generic)

instance FromJSON Request
instance ToJSON Request

-- ────────────────────────────────────────────────────────────────────────────
-- Response
-- ────────────────────────────────────────────────────────────────────────────

-- | Outgoing response to PureScript UI
data Response
  = RespOk !MessageId
  | RespData !MessageId !ByteString
  | RespFrame !MessageId !FrameData
  | RespDepth !MessageId !DepthBuffer
  | RespNumber !MessageId !Double
  | RespNumbers !MessageId ![Double]
  | RespBool !MessageId !Bool
  | RespText !MessageId !Text
  | RespError !MessageId !Text
  | RespPong !MessageId
  deriving stock (Eq, Show, Generic)

instance FromJSON Response
instance ToJSON Response

-- ────────────────────────────────────────────────────────────────────────────
-- Render Operations (replaces WebGL/Canvas FFI)
-- ────────────────────────────────────────────────────────────────────────────

data RenderOp
  = RenderCompileShader !Text !Text           -- vertex, fragment source
  | RenderSetShader !Text                     -- shader ID
  | RenderSetUniforms !Uniforms
  | RenderFrame !Int !Int                     -- width, height
  | RenderFrameWithUniforms !Int !Int !Uniforms
  | RenderDepth !Int !Int !DepthBuffer
  | RenderDispose
  | RenderIsContextLost
  | RenderCreateCanvas !Int !Int              -- width, height
  | RenderCanvasClear !Int !Int !Int !Int     -- x, y, w, h
  | RenderCanvasGetContext2D
  deriving stock (Eq, Show, Generic)

instance FromJSON RenderOp
instance ToJSON RenderOp

-- ────────────────────────────────────────────────────────────────────────────
-- Storage Operations (replaces IndexedDB/localStorage FFI)
-- ────────────────────────────────────────────────────────────────────────────

data StorageOp
  = StorageOpen !Text !Int !Text              -- name, version, store
  | StorageClose !Text
  | StoragePut !Text !Text !ByteString        -- store, key, value
  | StorageGet !Text !Text                    -- store, key
  | StorageDelete !Text !Text                 -- store, key
  | StorageGetAll !Text                       -- store
  | StorageClear !Text                        -- store
  | StorageCount !Text                        -- store
  | StorageLocalGet !Text                     -- key
  | StorageLocalSet !Text !Text               -- key, value
  | StorageSessionGet !Text
  | StorageSessionSet !Text !Text
  deriving stock (Eq, Show, Generic)

instance FromJSON StorageOp
instance ToJSON StorageOp

-- ────────────────────────────────────────────────────────────────────────────
-- Export Operations (replaces WebCodecs/Video FFI)
-- ────────────────────────────────────────────────────────────────────────────

data ExportOp
  = ExportCreateEncoder !Text !Int !Int !Int !Int  -- codec, width, height, fps, bitrate
  | ExportEncodeFrame !ByteString !Int !Bool       -- frame data, timestamp, keyframe
  | ExportFinalize
  | ExportCancel
  | ExportGetSupportedCodecs
  | ExportCreateZip ![(Text, ByteString)]          -- [(filename, data)]
  | ExportDownload !Text !ByteString               -- filename, data
  deriving stock (Eq, Show, Generic)

instance FromJSON ExportOp
instance ToJSON ExportOp

-- ────────────────────────────────────────────────────────────────────────────
-- Math Operations (replaces pure math FFI for exact arithmetic)
-- ────────────────────────────────────────────────────────────────────────────

data MathOp
  = MathSeededRandom !Word32 !Int             -- seed, count
  | MathMulberry32Next !Word32                -- state -> (value, newState)
  | MathBitXor !Int32 !Int32
  | MathBitAnd !Int32 !Int32
  | MathBitOr !Int32 !Int32
  | MathBitShl !Int32 !Int
  | MathBitShr !Int32 !Int                    -- signed
  | MathBitZshr !Int32 !Int                   -- unsigned (zero-fill)
  | MathImul !Int32 !Int32                    -- 32-bit integer multiply
  deriving stock (Eq, Show, Generic)

instance FromJSON MathOp
instance ToJSON MathOp

-- ────────────────────────────────────────────────────────────────────────────
-- Data Types
-- ────────────────────────────────────────────────────────────────────────────

-- | RGBA frame data
data FrameData = FrameData
  { fdWidth :: !Int
  , fdHeight :: !Int
  , fdData :: !ByteString        -- RGBA bytes
  } deriving stock (Eq, Show, Generic)

instance FromJSON FrameData
instance ToJSON FrameData

-- | Depth buffer (float32 per pixel)
data DepthBuffer = DepthBuffer
  { dbWidth :: !Int
  , dbHeight :: !Int
  , dbData :: !ByteString        -- Float32 bytes (4 bytes per pixel)
  } deriving stock (Eq, Show, Generic)

instance FromJSON DepthBuffer
instance ToJSON DepthBuffer

-- | Compiled shader program reference
data ShaderProgram = ShaderProgram
  { spId :: !Text
  , spVertexSource :: !Text
  , spFragmentSource :: !Text
  } deriving stock (Eq, Show, Generic)

instance FromJSON ShaderProgram
instance ToJSON ShaderProgram

-- | Shader uniforms
data Uniforms = Uniforms
  { uValues :: ![(Text, UniformValue)]
  } deriving stock (Eq, Show, Generic)

instance FromJSON Uniforms
instance ToJSON Uniforms

-- | Uniform value types
data UniformValue
  = UFloat !Double
  | UVec2 !Double !Double
  | UVec3 !Double !Double !Double
  | UVec4 !Double !Double !Double !Double
  | UInt !Int
  | UMat4 ![Double]              -- 16 floats, column-major
  | USampler2D !Int              -- texture unit
  deriving stock (Eq, Show, Generic)

instance FromJSON UniformValue
instance ToJSON UniformValue

-- ────────────────────────────────────────────────────────────────────────────
-- Encoding/Decoding
-- ────────────────────────────────────────────────────────────────────────────

encodeResponse :: Response -> LBS.ByteString
encodeResponse = encode

decodeRequest :: LBS.ByteString -> Maybe Request
decodeRequest = decode
