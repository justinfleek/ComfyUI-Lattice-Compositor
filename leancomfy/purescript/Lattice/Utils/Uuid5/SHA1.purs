-- | Lattice.Utils.Uuid5.SHA1 - SHA-1 hash implementation
-- |
-- | @module Lattice.Utils.Uuid5.SHA1
-- | @description Pure PureScript SHA-1 implementation for UUID5 generation.
-- |
-- | RFC 3174 compliant SHA-1 implementation.
-- |
-- | Source: leancomfy/lean/Lattice/Utils/Uuid5.lean

module Lattice.Utils.Uuid5.SHA1
  ( sha1
  , ByteArray
  ) where

import Prelude
import Data.Array as Array
import Data.Foldable (foldl)
import Data.Int.Bits (and, complement, or, shl, shr, xor)
import Data.Maybe (fromMaybe)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Byte array as array of ints (0-255)
type ByteArray = Array Int

-- | Word32 operations (using Int for simplicity, treating as unsigned 32-bit)
type Word32 = Int

--------------------------------------------------------------------------------
-- SHA-1 Constants
--------------------------------------------------------------------------------

-- | SHA-1 initial hash values
sha1H0 :: Word32
sha1H0 = 0x67452301

sha1H1 :: Word32
sha1H1 = (-271733879)   -- 0xEFCDAB89 as signed 32-bit

sha1H2 :: Word32
sha1H2 = (-1732584194)  -- 0x98BADCFE as signed 32-bit

sha1H3 :: Word32
sha1H3 = 0x10325476

sha1H4 :: Word32
sha1H4 = (-1009589776) -- 0xC3D2E1F0 as signed 32-bit

-- | SHA-1 round constants
sha1K :: Int -> Word32
sha1K i
  | i < 20 = 0x5A827999
  | i < 40 = 0x6ED9EBA1
  | i < 60 = (-1894007588)   -- 0x8F1BBCDC as signed 32-bit
  | otherwise = (-899497514) -- 0xCA62C1D6 as signed 32-bit

-- | SHA-1 f function
sha1F :: Int -> Word32 -> Word32 -> Word32 -> Word32
sha1F i b c d
  | i < 20 = (b `and` c) `or` ((complement b) `and` d)
  | i < 40 = b `xor` c `xor` d
  | i < 60 = (b `and` c) `or` (b `and` d) `or` (c `and` d)
  | otherwise = b `xor` c `xor` d

--------------------------------------------------------------------------------
-- Bit Operations
--------------------------------------------------------------------------------

-- | Rotate left (32-bit)
rotl32 :: Word32 -> Int -> Word32
rotl32 x n = ((x `shl` n) `or` (x `shr` (32 - n))) `and` (-1)

-- | Convert 4 bytes to Word32 (big-endian)
bytesToWord32BE :: Int -> Int -> Int -> Int -> Word32
bytesToWord32BE b0 b1 b2 b3 =
  ((b0 `and` 0xFF) `shl` 24) `or`
  ((b1 `and` 0xFF) `shl` 16) `or`
  ((b2 `and` 0xFF) `shl` 8) `or`
  (b3 `and` 0xFF)

-- | Convert Word32 to 4 bytes (big-endian)
word32ToBytesBE :: Word32 -> Array Int
word32ToBytesBE x =
  [ (x `shr` 24) `and` 0xFF
  , (x `shr` 16) `and` 0xFF
  , (x `shr` 8) `and` 0xFF
  , x `and` 0xFF
  ]

-- | Get byte from array with default 0
getByte :: ByteArray -> Int -> Int
getByte arr idx = fromMaybe 0 (Array.index arr idx)

--------------------------------------------------------------------------------
-- Padding
--------------------------------------------------------------------------------

-- | Pad message for SHA-1
sha1Pad :: ByteArray -> ByteArray
sha1Pad msg =
  let msgLen = Array.length msg
      bitLen = msgLen * 8
      -- Calculate padding: need (msgLen + 1 + padLen + 8) % 64 == 0
      padLen = ((55 - (msgLen `mod` 64) + 64) `mod` 64) + 1
      padding = [0x80] <> Array.replicate (padLen - 1) 0
      -- 64-bit big-endian length (simplified for messages < 2^32 bits)
      lenBytes =
        [ 0, 0, 0, 0  -- High 32 bits (always 0 for our use case)
        , (bitLen `shr` 24) `and` 0xFF
        , (bitLen `shr` 16) `and` 0xFF
        , (bitLen `shr` 8) `and` 0xFF
        , bitLen `and` 0xFF
        ]
  in msg <> padding <> lenBytes

--------------------------------------------------------------------------------
-- Chunk Processing
--------------------------------------------------------------------------------

-- | Process a single 512-bit chunk
sha1ProcessChunk :: ByteArray -> Int -> { h0 :: Word32, h1 :: Word32, h2 :: Word32, h3 :: Word32, h4 :: Word32 }
                 -> { h0 :: Word32, h1 :: Word32, h2 :: Word32, h3 :: Word32, h4 :: Word32 }
sha1ProcessChunk chunk offset { h0, h1, h2, h3, h4 } =
  let -- Build message schedule (80 words)
      getWord32 i =
        let idx = offset + i * 4
        in bytesToWord32BE
             (getByte chunk idx)
             (getByte chunk (idx + 1))
             (getByte chunk (idx + 2))
             (getByte chunk (idx + 3))

      -- First 16 words from chunk
      w0_15 = map getWord32 (Array.range 0 15)

      -- Extend to 80 words
      extend ws i =
        let val = (fromMaybe 0 (Array.index ws (i - 3))) `xor`
                  (fromMaybe 0 (Array.index ws (i - 8))) `xor`
                  (fromMaybe 0 (Array.index ws (i - 14))) `xor`
                  (fromMaybe 0 (Array.index ws (i - 16)))
        in ws <> [rotl32 val 1]

      w = foldl extend w0_15 (Array.range 16 79)

      -- Main loop
      step { a, b, c, d, e } i =
        let f = sha1F i b c d
            k = sha1K i
            wi = fromMaybe 0 (Array.index w i)
            temp = (rotl32 a 5 + f + e + k + wi) `and` (-1)
        in { a: temp, b: a, c: rotl32 b 30, d: c, e: d }

      result = foldl step { a: h0, b: h1, c: h2, d: h3, e: h4 } (Array.range 0 79)

  in { h0: (h0 + result.a) `and` (-1)
     , h1: (h1 + result.b) `and` (-1)
     , h2: (h2 + result.c) `and` (-1)
     , h3: (h3 + result.d) `and` (-1)
     , h4: (h4 + result.e) `and` (-1)
     }

--------------------------------------------------------------------------------
-- SHA-1 Hash
--------------------------------------------------------------------------------

-- | Compute SHA-1 hash
-- |
-- | @param input Byte array to hash
-- | @returns 20-byte SHA-1 hash
sha1 :: ByteArray -> ByteArray
sha1 input =
  let padded = sha1Pad input
      numChunks = Array.length padded / 64

      processChunks h chunkIdx =
        sha1ProcessChunk padded (chunkIdx * 64) h

      result = foldl processChunks
        { h0: sha1H0, h1: sha1H1, h2: sha1H2, h3: sha1H3, h4: sha1H4 }
        (Array.range 0 (numChunks - 1))

  in word32ToBytesBE result.h0 <>
     word32ToBytesBE result.h1 <>
     word32ToBytesBE result.h2 <>
     word32ToBytesBE result.h3 <>
     word32ToBytesBE result.h4
