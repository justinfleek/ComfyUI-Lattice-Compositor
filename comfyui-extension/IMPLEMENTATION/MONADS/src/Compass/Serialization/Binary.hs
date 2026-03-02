{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DefaultSignatures #-}

-- |
-- Module      : Compass.Serialization.Binary
-- Description : Binary serialization for CAS values and wire protocol
-- License     : Proprietary (Weyl AI)
--
-- Uses the 'store' library for high-performance serialization with
-- fixed-size representations where possible. This is critical for CAS
-- because the content address (UUID5) is computed over the serialized bytes —
-- different serialization = different address = broken Merkle integrity.
--
-- Invariant (verifiable in Lean4):
--   ∀ x. deserialize (serialize x) = Just x
--   ∀ x y. serialize x = serialize y → x = y  (injectivity, for CAS correctness)

module Compass.Serialization.Binary
  ( -- * Core Serialization
    CASSerializable (..)
  , serializeForCAS
  , deserializeFromCAS

    -- * Wire Protocol
  , WireMessage (..)
  , encodeWireMessage
  , decodeWireMessage

    -- * Version Vector Encoding
  , encodeVersionVec
  , decodeVersionVec

    -- * Widget Data Encoding
  , encodeWidgetData
  , decodeWidgetData

    -- * Provenance Encoding
  , encodeProvenance
  , decodeProvenance

    -- * Cache Key Derivation
  , deriveCacheKey
  , deriveCompositeCacheKey
  ) where

import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Builder as BB
import qualified Data.ByteString.Lazy as BL
import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import           Data.Time.Clock (UTCTime)
import           Data.Time.Clock.POSIX (utcTimeToPOSIXSeconds, posixSecondsToUTCTime)
import           Data.UUID (UUID)
import qualified Data.UUID as UUID
import qualified Data.UUID.V5 as UUID5
import           Data.Word (Word8, Word16, Word32, Word64)
import           GHC.Generics (Generic)

import           Compass.Core.Types

-------------------------------------------------------------------------------
-- Core Serialization Typeclass
-------------------------------------------------------------------------------

-- | Typeclass for types that can be serialized for CAS storage.
-- The serialization MUST be:
--   1. Deterministic: same value always produces same bytes
--   2. Injective: different values produce different bytes
--   3. Self-describing: includes type tag for safe deserialization
--
-- These properties ensure that UUID5(serialize(x)) is a valid content address.
class CASSerializable a where
  -- | Serialize to bytes for CAS hashing and storage
  casSerialize :: a -> ByteString

  -- | Deserialize from bytes
  casDeserialize :: ByteString -> Either Text a

  -- | Type tag (first byte of serialized form) for runtime type checking
  casTypeTag :: proxy a -> Word8

-- | Convenience: serialize and compute content address in one step
serializeForCAS :: CASSerializable a => Namespace -> a -> (ContentAddr, ByteString)
serializeForCAS ns val =
  let bytes = casSerialize val
      addr  = ContentAddr $ UUID5.generateNamed (unNamespace ns) (BS.unpack bytes)
  in (addr, bytes)

-- | Deserialize with address verification
deserializeFromCAS :: CASSerializable a
                   => Namespace -> ContentAddr -> ByteString -> Either Text a
deserializeFromCAS ns expectedAddr bytes =
  let computedAddr = ContentAddr $ UUID5.generateNamed (unNamespace ns) (BS.unpack bytes)
  in if computedAddr /= expectedAddr
     then Left $ "CAS integrity violation: expected " <> T.pack (show expectedAddr)
              <> " but content hashes to " <> T.pack (show computedAddr)
     else casDeserialize bytes

-------------------------------------------------------------------------------
-- Version Vector Encoding
-------------------------------------------------------------------------------

-- | Encode a VersionVec as deterministic bytes.
-- Format: [count:u32] [agentId_len:u16 agentId_bytes:* version:u64]*
-- Keys sorted lexicographically for determinism.
encodeVersionVec :: VersionVec -> ByteString
encodeVersionVec (VersionVec m) =
  BL.toStrict $ BB.toLazyByteString $ mconcat
    [ BB.word32BE (fromIntegral $ Map.size m)
    , mconcat
        [ BB.word16BE (fromIntegral $ BS.length agentBytes)
          <> BB.byteString agentBytes
          <> BB.word64BE ver
        | (AgentId aid, ver) <- Map.toAscList m  -- sorted!
        , let agentBytes = TE.encodeUtf8 aid
        ]
    ]

-- | Decode a VersionVec from bytes
decodeVersionVec :: ByteString -> Either Text VersionVec
decodeVersionVec _bs = Right $ VersionVec Map.empty  -- STUB: implement parser

-------------------------------------------------------------------------------
-- Widget Data Encoding
-------------------------------------------------------------------------------

-- | Encode WidgetData deterministically.
-- Format:
--   [type_tag:u8 = 0x01]
--   [payload_count:u32] [key_len:u16 key:* value:f64]*   -- sorted by key
--   [labels_count:u32]  [key_len:u16 key:* val_len:u16 val:*]*  -- sorted
--   [provenance:*]
--   [freshness:*]
--   [confidence:f64]
encodeWidgetData :: WidgetData -> ByteString
encodeWidgetData wd =
  BL.toStrict $ BB.toLazyByteString $ mconcat
    [ BB.word8 0x01  -- type tag
    -- Payload (sorted for determinism)
    , BB.word32BE (fromIntegral $ HM.size $ wdPayload wd)
    , mconcat
        [ encodeTextEntry k <> BB.doubleBE v
        | (k, v) <- sortedHashMap (wdPayload wd)
        ]
    -- Labels
    , BB.word32BE (fromIntegral $ HM.size $ wdLabels wd)
    , mconcat
        [ encodeTextEntry k <> encodeTextEntry v
        | (k, v) <- sortedHashMap (wdLabels wd)
        ]
    -- Provenance
    , BB.byteString (encodeProvenance (wdProvenance wd))
    -- Confidence
    , BB.doubleBE (unConfidence $ wdConfidence wd)
    ]
  where
    encodeTextEntry :: Text -> BB.Builder
    encodeTextEntry t =
      let bs = TE.encodeUtf8 t
      in BB.word16BE (fromIntegral $ BS.length bs) <> BB.byteString bs

    sortedHashMap :: HashMap Text a -> [(Text, a)]
    sortedHashMap = Map.toAscList . Map.fromList . HM.toList

decodeWidgetData :: ByteString -> Either Text WidgetData
decodeWidgetData _bs = Left "STUB: implement parser"

-------------------------------------------------------------------------------
-- Provenance Encoding
-------------------------------------------------------------------------------

-- | Encode Provenance (Cofree comonad over Merkle deps) deterministically.
-- Format:
--   ProvenanceLeaf:    [0x00] [addr:uuid] [time:i64] [agentId:text]
--   ProvenanceDerived: [0x01] [addr:uuid] [time:i64] [agentId:text] [child_count:u32] [children:*]
encodeProvenance :: Provenance -> ByteString
encodeProvenance (ProvenanceLeaf addr time agentId) =
  BL.toStrict $ BB.toLazyByteString $ mconcat
    [ BB.word8 0x00
    , BB.byteString (BL.toStrict $ UUID.toByteString $ unContentAddr addr)
    , BB.int64BE (round $ utcTimeToPOSIXSeconds time)
    , encodeText (unAgentId agentId)
    ]
encodeProvenance (ProvenanceDerived addr time agentId children) =
  BL.toStrict $ BB.toLazyByteString $ mconcat
    [ BB.word8 0x01
    , BB.byteString (BL.toStrict $ UUID.toByteString $ unContentAddr addr)
    , BB.int64BE (round $ utcTimeToPOSIXSeconds time)
    , encodeText (unAgentId agentId)
    , BB.word32BE (fromIntegral $ length children)
    , mconcat (map (BB.byteString . encodeProvenance) children)
    ]

decodeProvenance :: ByteString -> Either Text Provenance
decodeProvenance _bs = Left "STUB: implement parser"

-------------------------------------------------------------------------------
-- Wire Protocol
-------------------------------------------------------------------------------

-- | Messages exchanged between COMPASS components.
-- Content-addressed: the message ID is UUID5(serialize(message body)).
data WireMessage
  = WMAgentRequest
      { wmrQueryIntent :: QueryIntent
      , wmrMerkleRoot  :: ContentAddr   -- current root
      , wmrBudgetMs    :: Double
      }
  | WMAgentResponse
      { wmrWidgetData  :: WidgetData
      , wmrProvenance  :: Provenance
      , wmrTierUsed    :: Word8         -- InferenceTier as ordinal
      , wmrLatencyMs   :: Double
      }
  | WMMerkleUpdate
      { wmuOldRoot     :: ContentAddr
      , wmuNewRoot     :: ContentAddr
      , wmuChangedAddrs :: [ContentAddr]
      }
  | WMCacheInvalidate
      { wmciAddrs      :: [ContentAddr]
      }
  deriving stock (Show, Generic)

encodeWireMessage :: WireMessage -> ByteString
encodeWireMessage = error "Compass.Serialization.Binary.encodeWireMessage: implement"

decodeWireMessage :: ByteString -> Either Text WireMessage
decodeWireMessage = error "Compass.Serialization.Binary.decodeWireMessage: implement"

-------------------------------------------------------------------------------
-- Cache Key Derivation
-------------------------------------------------------------------------------

-- | Derive a content-addressed cache key from a query intent + Merkle root.
-- This is the key function that makes agent caching work:
-- same query against same data state → same key → cache hit.
deriveCacheKey :: QueryIntent -> MerkleRoot -> ContentAddr
deriveCacheKey intent root =
  let intentBytes = serializeQueryIntent intent
      rootBytes   = BL.toStrict $ UUID.toByteString $ unContentAddr (mrAddr root)
      combined    = intentBytes <> rootBytes
      ns          = Namespace $ UUID5.generateNamed UUID5.namespaceURL
                      (BS.unpack "https://compass.weyl.ai/ns/cache")
  in ContentAddr $ UUID5.generateNamed (unNamespace ns) (BS.unpack combined)

-- | Derive cache key from multiple components
deriveCompositeCacheKey :: [ByteString] -> ContentAddr
deriveCompositeCacheKey parts =
  let combined = mconcat parts
      ns       = Namespace $ UUID5.generateNamed UUID5.namespaceURL
                   (BS.unpack "https://compass.weyl.ai/ns/composite")
  in ContentAddr $ UUID5.generateNamed (unNamespace ns) (BS.unpack combined)

-------------------------------------------------------------------------------
-- Internal Helpers
-------------------------------------------------------------------------------

encodeText :: Text -> BB.Builder
encodeText t =
  let bs = TE.encodeUtf8 t
  in BB.word16BE (fromIntegral $ BS.length bs) <> BB.byteString bs

serializeQueryIntent :: QueryIntent -> ByteString
serializeQueryIntent = error "Compass.Serialization.Binary.serializeQueryIntent: implement"
