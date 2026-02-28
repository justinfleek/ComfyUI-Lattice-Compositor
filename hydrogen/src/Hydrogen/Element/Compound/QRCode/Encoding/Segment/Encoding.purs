-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--           // hydrogen // element // qrcode // encoding // segment // encoding
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Mode-specific data encoding for QR segments.
-- |
-- | - Numeric: 10 bits per 3 digits
-- | - Alphanumeric: 11 bits per 2 characters
-- | - Byte: 8 bits per character
-- | - Kanji: 13 bits per character

module Hydrogen.Element.Compound.QRCode.Encoding.Segment.Encoding
  ( encodeData
  , encodeNumeric
  , encodeAlphanumeric
  , encodeByte
  , encodeKanji
  , dataBitLength
  ) where

import Prelude
  ( map
  , otherwise
  , (+)
  , (-)
  , (*)
  , (<=)
  , (>=)
  )

import Data.Array (foldl, length, index, (..))
import Data.Char (toCharCode)
import Data.EuclideanRing (div, mod)
import Data.Maybe (Maybe(Just), fromMaybe)
import Data.String.CodeUnits (toCharArray)

import Hydrogen.Element.Compound.QRCode.Types 
  ( EncodingMode(ModeNumeric, ModeAlphanumeric, ModeByte, ModeKanji, ModeECI)
  )
import Hydrogen.Element.Compound.QRCode.Encoding.BitStream as BS
import Hydrogen.Element.Compound.QRCode.Encoding.Segment.CharTable (alphanumericValue)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // data bit length
-- ═════════════════════════════════════════════════════════════════════════════

dataBitLength :: EncodingMode -> Int -> Int
dataBitLength mode charCount = case mode of
  ModeNumeric ->
    let
      groups3 = div charCount 3
      remainder = mod charCount 3
      remainderBits = case remainder of
        0 -> 0
        1 -> 4
        _ -> 7
    in
      groups3 * 10 + remainderBits
  
  ModeAlphanumeric ->
    let
      pairs = div charCount 2
      odd = mod charCount 2
    in
      pairs * 11 + odd * 6
  
  ModeByte -> charCount * 8
  ModeKanji -> charCount * 13
  ModeECI -> 8

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // encoding
-- ═════════════════════════════════════════════════════════════════════════════

encodeData :: EncodingMode -> String -> BS.BitStream
encodeData mode str = case mode of
  ModeNumeric -> encodeNumeric str
  ModeAlphanumeric -> encodeAlphanumeric str
  ModeByte -> encodeByte str
  ModeKanji -> encodeKanji str
  ModeECI -> BS.empty

encodeNumeric :: String -> BS.BitStream
encodeNumeric str =
  let
    chars = toCharArray str
    digits = map charToDigit chars
  in
    encodeNumericDigits digits BS.empty
  where
    charToDigit :: Char -> Int
    charToDigit c = toCharCode c - 48
    
    encodeNumericDigits :: Array Int -> BS.BitStream -> BS.BitStream
    encodeNumericDigits digits acc =
      case length digits of
        0 -> acc
        1 -> 
          let d = fromMaybe 0 (index digits 0)
          in BS.writeInt d 4 acc
        2 ->
          let 
            d1 = fromMaybe 0 (index digits 0)
            d2 = fromMaybe 0 (index digits 1)
            val = d1 * 10 + d2
          in BS.writeInt val 7 acc
        _ ->
          let
            d1 = fromMaybe 0 (index digits 0)
            d2 = fromMaybe 0 (index digits 1)
            d3 = fromMaybe 0 (index digits 2)
            val = d1 * 100 + d2 * 10 + d3
            remaining = dropInts 3 digits
            newAcc = BS.writeInt val 10 acc
          in
            encodeNumericDigits remaining newAcc
    
    dropInts :: Int -> Array Int -> Array Int
    dropInts n arr = 
      let len = length arr
      in if n >= len then []
         else map (\i -> fromMaybe 0 (index arr (i + n))) (0 .. (len - n - 1))

encodeAlphanumeric :: String -> BS.BitStream
encodeAlphanumeric str =
  let
    chars = toCharArray str
    values = map alphanumericValue chars
  in
    encodeAlphanumericValues values BS.empty
  where
    encodeAlphanumericValues :: Array Int -> BS.BitStream -> BS.BitStream
    encodeAlphanumericValues vals acc =
      case length vals of
        0 -> acc
        1 ->
          let v = fromMaybe 0 (index vals 0)
          in BS.writeInt v 6 acc
        _ ->
          let
            v1 = fromMaybe 0 (index vals 0)
            v2 = fromMaybe 0 (index vals 1)
            combined = v1 * 45 + v2
            remaining = dropInts 2 vals
            newAcc = BS.writeInt combined 11 acc
          in
            encodeAlphanumericValues remaining newAcc
    
    dropInts :: Int -> Array Int -> Array Int
    dropInts n arr = 
      let len = length arr
      in if n >= len then []
         else map (\i -> fromMaybe 0 (index arr (i + n))) (0 .. (len - n - 1))

encodeByte :: String -> BS.BitStream
encodeByte str =
  let
    chars = toCharArray str
    bytes = map toCharCode chars
  in
    foldl (\acc b -> BS.writeByte b acc) BS.empty bytes

encodeKanji :: String -> BS.BitStream
encodeKanji str = encodeByte str
