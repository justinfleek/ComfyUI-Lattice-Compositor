-- |
-- Module      : Lattice.Utils.Uuid5
-- Description : UUID5 (deterministic name-based UUID) implementation
--
-- Migrated from ui/src/utils/uuid5.ts
-- RFC 4122 compliant; pure SHA-1 in-module. No forbidden patterns.
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Utils.Uuid5
  ( -- Namespaces
    uuid5NamespaceDns
  , uuid5NamespaceUrl
  , uuid5NamespaceOid
  , uuid5NamespaceX500
  , latticeNamespace
  -- Core
  , uuid5
  -- Generators
  , generateLayerId
  , generateKeyframeId
  , generateCompositionId
  , generateEffectId
  , generateProjectId
  ) where

import Data.Bits (Bits(..))
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Encoding (encodeUtf8)
import Data.Word (Word32, Word8)

-- ============================================================================
-- NAMESPACES (RFC 4122)
-- ============================================================================

uuid5NamespaceDns :: Text
uuid5NamespaceDns = "6ba7b810-9dad-11d1-80b4-00c04fd430c8"

uuid5NamespaceUrl :: Text
uuid5NamespaceUrl = "6ba7b811-9dad-11d1-80b4-00c04fd430c8"

uuid5NamespaceOid :: Text
uuid5NamespaceOid = "6ba7b812-9dad-11d1-80b4-00c04fd430c8"

uuid5NamespaceX500 :: Text
uuid5NamespaceX500 = "6ba7b814-9dad-11d1-80b4-00c04fd430c8"

latticeNamespace :: Text
latticeNamespace = "a1b2c3d4-e5f6-4789-a012-3456789abcde"

-- ============================================================================
-- UUID <-> BYTES
-- ============================================================================

hexDigit :: Char -> Int
hexDigit c
  | c >= '0' && c <= '9' = fromEnum c - fromEnum '0'
  | c >= 'a' && c <= 'f' = fromEnum c - fromEnum 'a' + 10
  | c >= 'A' && c <= 'F' = fromEnum c - fromEnum 'A' + 10
  | otherwise = 0

-- | Parse UUID string (with or without hyphens) to 16 bytes (32 hex chars)
uuidToBytes :: Text -> ByteString
uuidToBytes uuid =
  let raw = T.filter (/= '-') uuid
      hex = T.take 32 (raw <> T.replicate 32 "0")
  in BS.pack [ fromIntegral (hexDigit (T.index hex i) * 16 + hexDigit (T.index hex (i + 1)))
             | i <- [0, 2 .. 30] ]

hexByte :: Word8 -> Text
hexByte b = T.pack [hexChar (fromIntegral b `div` 16), hexChar (fromIntegral b `mod` 16)]
  where hexChar n | n < 10 = toEnum (fromEnum '0' + n)
                 | otherwise = toEnum (fromEnum 'a' + n - 10)

-- | 16 bytes to UUID string (8-4-4-4-12)
bytesToUuid :: ByteString -> Text
bytesToUuid bs
  | BS.length bs /= 16 = T.pack "00000000-0000-0000-0000-000000000000"
  | otherwise =
  let seg a b = T.concat (map (hexByte . BS.index bs) [a .. b])
  in seg 0 3 <> "-" <> seg 4 5 <> "-" <> seg 6 7 <> "-" <> seg 8 9 <> "-" <> seg 10 15

-- ============================================================================
-- SHA-1 (pure, for UUID5)
-- ============================================================================

processChunk :: (Word32, Word32, Word32, Word32, Word32) -> ByteString -> (Word32, Word32, Word32, Word32, Word32)
processChunk (h0, h1, h2, h3, h4) chunk =
  let be32 i = fromIntegral (BS.index chunk i) `shiftL` 24 .|.
               fromIntegral (BS.index chunk (i+1)) `shiftL` 16 .|.
               fromIntegral (BS.index chunk (i+2)) `shiftL` 8 .|.
               fromIntegral (BS.index chunk (i+3))
      w0 = [ be32 (i*4) | i <- [0 .. 15] ]
      rotl1 x = (x `shiftL` 1) .|. (x `shiftR` 31)
      w = w0 ++ [ rotl1 (w!!(i-3) `xor` w!!(i-8) `xor` w!!(i-14) `xor` w!!(i-16)) | i <- [16 .. 79] ]
      round' i (a, b, c, d, e) =
        let (f, k) = if i < 20 then ((b .&. c) .|. (complement b .&. d), 0x5a827999)
                      else if i < 40 then (b `xor` c `xor` d, 0x6ed9eba1)
                      else if i < 60 then ((b .&. c) .|. (b .&. d) .|. (c .&. d), 0x8f1bbcdc)
                      else (b `xor` c `xor` d, 0xca62c1d6)
            rotl n x = (x `shiftL` n) .|. (x `shiftR` (32 - n))
            t = (rotl 5 a + f + e + k + w!!i) .&. 0xffffffff
        in (t, a, rotl 30 b, c, d)
      (a, b, c, d, e) = foldl (\s i -> round' i s) (h0, h1, h2, h3, h4) [0 .. 79]
  in (h0 + a, h1 + b, h2 + c, h3 + d, h4 + e)

sha1Final :: ByteString -> ByteString
sha1Final msg =
  let len = BS.length msg
      bitLen = fromIntegral len * 8 :: Word32
      padLen = ((len + 9 + 63) `div` 64) * 64
      padding = BS.concat
        [ msg
        , BS.singleton 0x80
        , BS.replicate (padLen - len - 9) 0
        , BS.pack [ 0, 0, 0, 0
                  , fromIntegral (bitLen `shiftR` 24)
                  , fromIntegral (bitLen `shiftR` 16)
                  , fromIntegral (bitLen `shiftR` 8)
                  , fromIntegral bitLen ]
        ]
      initial = (0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0)
      numChunks = BS.length padding `div` 64
      final = foldl processChunk initial [ BS.take 64 (BS.drop (i * 64) padding) | i <- [0 .. numChunks - 1] ]
      (fh0, fh1, fh2, fh3, fh4) = final
      toBytes h = BS.pack [ fromIntegral (h `shiftR` 24), fromIntegral (h `shiftR` 16), fromIntegral (h `shiftR` 8), fromIntegral h ]
  in BS.concat (map toBytes [fh0, fh1, fh2, fh3, fh4])

-- ============================================================================
-- UUID5
-- ============================================================================

-- | Generate UUID5 from name and namespace (default: latticeNamespace)
uuid5 :: Text -> Text -> Text
uuid5 name namespace =
  let nsBytes = uuidToBytes namespace
      nameBytes = encodeUtf8 name
      combined = BS.concat [nsBytes, nameBytes]
      hash = sha1Final combined
      uuidBytes = BS.take 16 hash
      b6 = BS.index uuidBytes 6
      b8 = BS.index uuidBytes 8
      modified = BS.take 6 uuidBytes
        <> BS.singleton ((b6 .&. 0x0f) .|. 0x50)
        <> BS.singleton (BS.index uuidBytes 7)
        <> BS.singleton ((b8 .&. 0x3f) .|. 0x80)
        <> BS.drop 9 uuidBytes
  in bytesToUuid modified

-- ============================================================================
-- GENERATORS
-- ============================================================================

generateLayerId :: Text -> Maybe Text -> Int -> Text
generateLayerId layerName mParentId index =
  let parentPart = case mParentId of Nothing -> "root"; Just p -> T.unpack p
      name = T.pack (T.unpack layerName ++ ":" ++ parentPart ++ ":" ++ show index)
  in uuid5 name latticeNamespace

generateKeyframeId :: Text -> Text -> Int -> Text -> Text
generateKeyframeId layerId propertyPath frame value =
  uuid5 (layerId <> ":" <> propertyPath <> ":" <> T.pack (show frame) <> ":" <> value) latticeNamespace

generateCompositionId :: Text -> Text -> Int -> Text
generateCompositionId projectId compositionName index =
  uuid5 (T.pack ("composition:" ++ T.unpack projectId ++ ":" ++ T.unpack compositionName ++ ":" ++ show index)) latticeNamespace

generateEffectId :: Text -> Text -> Int -> Text
generateEffectId layerId effectType orderIndex =
  uuid5 (layerId <> ":" <> effectType <> ":" <> T.pack (show orderIndex)) latticeNamespace

generateProjectId :: Text -> Int -> Text
generateProjectId projectName timestamp =
  uuid5 (T.pack ("project:" ++ T.unpack projectName ++ ":" ++ show timestamp)) latticeNamespace
