-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // element // qrcode // encoding // bitstream
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | BitStream — Bit-level operations for QR code encoding.
-- |
-- | ## Design Philosophy
-- |
-- | QR codes are encoded at the bit level. This module provides:
-- | - A pure functional BitStream type
-- | - Bit manipulation operations
-- | - Conversion to/from bytes (codewords)
-- |
-- | All operations are pure — no mutation, no FFI.
-- |
-- | ## QR Encoding Process
-- |
-- | 1. Data → Segments (mode + data bits)
-- | 2. Segments → BitStream
-- | 3. BitStream + padding → Codewords
-- | 4. Codewords + Reed-Solomon → Final data
-- |
-- | ## Bit Ordering
-- |
-- | QR codes use MSB-first (most significant bit first) ordering.
-- | When we write 4 bits of value 5 (binary 0101), we write:
-- | position 0: 0, position 1: 1, position 2: 0, position 3: 1
-- |
-- | ## Dependencies
-- |
-- | - Prelude (basic operations)
-- | - Data.Array (bit storage)
-- | - Data.EuclideanRing (div, mod for bit math)

module Hydrogen.Element.Compound.QRCode.Encoding.BitStream
  ( -- * BitStream Type
    BitStream
  , empty
  , fromBits
  , fromInt
  , fromBytes
  
  -- * Basic Operations
  , append
  , length
  , getBit
  , slice
  , concat
  
  -- * Writing Bits
  , writeBit
  , writeBits
  , writeInt
  , writeByte
  , writeBytes
  
  -- * Reading Bits
  , readBit
  , readBits
  , readInt
  , readByte
  
  -- * Conversion
  , toArray
  , toBytes
  , toBinaryString
  , toHexString
  
  -- * Padding
  , padToLength
  , padToByteMultiple
  , addTerminator
  , addPadCodewords
  
  -- * Bit Constants
  , Bit
  , zero
  , one
  , bitToInt
  , intToBit
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , class Monoid
  , show
  , (<>)
  , (==)
  , (/=)
  , (&&)
  , (||)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , map
  , otherwise
  , mempty
  , compare
  , Ordering(LT, EQ, GT)
  )

import Data.Array (snoc, index, take, drop, replicate, foldl, reverse)
import Data.Array as Array
import Data.EuclideanRing (div, mod)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.String (joinWith)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // bit
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single bit (0 or 1).
newtype Bit = Bit Int

derive instance eqBit :: Eq Bit
derive instance ordBit :: Ord Bit

instance showBit :: Show Bit where
  show (Bit 0) = "0"
  show (Bit _) = "1"

-- | Bit value 0
zero :: Bit
zero = Bit 0

-- | Bit value 1
one :: Bit
one = Bit 1

-- | Convert Bit to Int (0 or 1)
bitToInt :: Bit -> Int
bitToInt (Bit b) = if b == 0 then 0 else 1

-- | Convert Int to Bit (any non-zero becomes 1)
intToBit :: Int -> Bit
intToBit n = if n == 0 then zero else one

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // bitstream
-- ═════════════════════════════════════════════════════════════════════════════

-- | A stream of bits, stored MSB-first.
-- |
-- | Internally stored as an array of Bit values.
-- | This is simple and pure, trading some memory efficiency
-- | for clarity and ease of manipulation.
newtype BitStream = BitStream (Array Bit)

derive instance eqBitStream :: Eq BitStream

instance showBitStream :: Show BitStream where
  show bs = "BitStream[" <> show (length bs) <> "](" <> toBinaryString bs <> ")"

instance semigroupBitStream :: Semigroup BitStream where
  append (BitStream a) (BitStream b) = BitStream (a <> b)

instance monoidBitStream :: Monoid BitStream where
  mempty = empty

-- | Empty bit stream
empty :: BitStream
empty = BitStream []

-- | Create from array of bits
fromBits :: Array Bit -> BitStream
fromBits = BitStream

-- | Create from an integer with specified bit count.
-- |
-- | Encodes the integer in MSB-first order.
-- | Example: fromInt 5 4 = [0,1,0,1] (5 in 4 bits)
fromInt :: Int -> Int -> BitStream
fromInt value bitCount =
  let
    bits = extractBits value bitCount []
  in
    BitStream bits
  where
    extractBits :: Int -> Int -> Array Bit -> Array Bit
    extractBits _ 0 acc = acc
    extractBits v remaining acc =
      let
        -- Extract MSB first by checking bit at position (remaining - 1)
        bitPos = remaining - 1
        bitValue = mod (div v (pow2 bitPos)) 2
        bit = intToBit bitValue
      in
        extractBits v (remaining - 1) (snoc acc bit)

-- | Create from array of bytes (8-bit values)
fromBytes :: Array Int -> BitStream
fromBytes bytes = foldl (\acc b -> append acc (fromInt b 8)) empty bytes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // basic operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Append two bit streams
append :: BitStream -> BitStream -> BitStream
append (BitStream a) (BitStream b) = BitStream (a <> b)

-- | Get length in bits
length :: BitStream -> Int
length (BitStream bits) = Array.length bits

-- | Get bit at index (0-indexed)
getBit :: Int -> BitStream -> Maybe Bit
getBit idx (BitStream bits) = index bits idx

-- | Get a slice of the bit stream
slice :: Int -> Int -> BitStream -> BitStream
slice start len (BitStream bits) =
  BitStream (take len (drop start bits))

-- | Concatenate multiple bit streams
concat :: Array BitStream -> BitStream
concat streams = foldl append empty streams

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // writing bits
-- ═════════════════════════════════════════════════════════════════════════════

-- | Write a single bit to the end
writeBit :: Bit -> BitStream -> BitStream
writeBit bit (BitStream bits) = BitStream (snoc bits bit)

-- | Write multiple bits to the end
writeBits :: Array Bit -> BitStream -> BitStream
writeBits newBits (BitStream bits) = BitStream (bits <> newBits)

-- | Write an integer as bits
writeInt :: Int -> Int -> BitStream -> BitStream
writeInt value bitCount stream = append stream (fromInt value bitCount)

-- | Write a byte (8 bits)
writeByte :: Int -> BitStream -> BitStream
writeByte value = writeInt value 8

-- | Write multiple bytes
writeBytes :: Array Int -> BitStream -> BitStream
writeBytes bytes stream = foldl (\acc b -> writeByte b acc) stream bytes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // reading bits
-- ═════════════════════════════════════════════════════════════════════════════

-- | Read a single bit at position
readBit :: Int -> BitStream -> Maybe Bit
readBit = getBit

-- | Read multiple bits starting at position
readBits :: Int -> Int -> BitStream -> Array Bit
readBits start count (BitStream bits) =
  take count (drop start bits)

-- | Read bits as an integer
readInt :: Int -> Int -> BitStream -> Maybe Int
readInt start bitCount stream =
  let
    bits = readBits start bitCount stream
  in
    if Array.length bits == bitCount
      then Just (bitsToInt bits)
      else Nothing

-- | Read a byte (8 bits) at position
readByte :: Int -> BitStream -> Maybe Int
readByte start = readInt start 8

-- | Convert array of bits to integer
bitsToInt :: Array Bit -> Int
bitsToInt bits = foldl addBit 0 bits
  where
    addBit :: Int -> Bit -> Int
    addBit acc (Bit b) = acc * 2 + b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to array of bits
toArray :: BitStream -> Array Bit
toArray (BitStream bits) = bits

-- | Convert to array of bytes.
-- |
-- | Pads with zeros if not a multiple of 8.
toBytes :: BitStream -> Array Int
toBytes stream =
  let
    padded = padToByteMultiple stream
    BitStream bits = padded
    byteCount = div (Array.length bits) 8
  in
    extractBytes bits 0 byteCount []
  where
    extractBytes :: Array Bit -> Int -> Int -> Array Int -> Array Int
    extractBytes bits idx count acc
      | idx >= count = acc
      | otherwise =
          let
            byteBits = take 8 (drop (idx * 8) bits)
            byteVal = bitsToInt byteBits
          in
            extractBytes bits (idx + 1) count (snoc acc byteVal)

-- | Convert to binary string (e.g., "01010011")
toBinaryString :: BitStream -> String
toBinaryString (BitStream bits) = joinWith "" (map show bits)

-- | Convert to hex string (e.g., "53")
toHexString :: BitStream -> String
toHexString stream =
  let
    bytes = toBytes stream
  in
    joinWith "" (map byteToHex bytes)
  where
    byteToHex :: Int -> String
    byteToHex b =
      let
        high = div b 16
        low = mod b 16
      in
        hexDigit high <> hexDigit low
    
    hexDigit :: Int -> String
    hexDigit d
      | d < 10 = show d
      | d == 10 = "A"
      | d == 11 = "B"
      | d == 12 = "C"
      | d == 13 = "D"
      | d == 14 = "E"
      | otherwise = "F"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // padding
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pad with zeros to reach target length
padToLength :: Int -> BitStream -> BitStream
padToLength targetLen (BitStream bits) =
  let
    currentLen = Array.length bits
    needed = if targetLen > currentLen then targetLen - currentLen else 0
    padding = replicate needed zero
  in
    BitStream (bits <> padding)

-- | Pad with zeros to make length a multiple of 8
padToByteMultiple :: BitStream -> BitStream
padToByteMultiple stream =
  let
    len = length stream
    remainder = mod len 8
    needed = if remainder == 0 then 0 else 8 - remainder
    padding = replicate needed zero
  in
    append stream (BitStream padding)

-- | Add terminator bits (up to 4 zeros).
-- |
-- | QR codes end data with a terminator sequence of up to 4 zero bits,
-- | but not exceeding the total capacity.
addTerminator :: Int -> BitStream -> BitStream
addTerminator maxBits stream =
  let
    currentLen = length stream
    remaining = maxBits - currentLen
    terminatorLen = if remaining >= 4 then 4 else remaining
    terminator = replicate terminatorLen zero
  in
    append stream (BitStream terminator)

-- | Add pad codewords to fill capacity.
-- |
-- | QR codes use alternating pad codewords: 0xEC, 0x11
-- | (236 and 17 in decimal)
addPadCodewords :: Int -> BitStream -> BitStream
addPadCodewords targetBits stream =
  let
    -- First pad to byte boundary
    bytePadded = padToByteMultiple stream
    currentLen = length bytePadded
    neededBits = targetBits - currentLen
    neededBytes = div neededBits 8
  in
    addPadBytes neededBytes 0 bytePadded
  where
    addPadBytes :: Int -> Int -> BitStream -> BitStream
    addPadBytes 0 _ acc = acc
    addPadBytes remaining idx acc =
      let
        -- Alternate between 0xEC (236) and 0x11 (17)
        padByte = if mod idx 2 == 0 then 236 else 17
        newAcc = writeByte padByte acc
      in
        addPadBytes (remaining - 1) (idx + 1) newAcc

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Power of 2
pow2 :: Int -> Int
pow2 n
  | n <= 0 = 1
  | n == 1 = 2
  | n == 2 = 4
  | n == 3 = 8
  | n == 4 = 16
  | n == 5 = 32
  | n == 6 = 64
  | n == 7 = 128
  | n == 8 = 256
  | n == 9 = 512
  | n == 10 = 1024
  | n == 11 = 2048
  | n == 12 = 4096
  | n == 13 = 8192
  | n == 14 = 16384
  | n == 15 = 32768
  | n == 16 = 65536
  | otherwise = 2 * pow2 (n - 1)
