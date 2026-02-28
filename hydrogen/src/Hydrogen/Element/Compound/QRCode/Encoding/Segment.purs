-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // element // qrcode // encoding // segment
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Segment — Data segmentation and mode-specific encoding.
-- |
-- | This is an orchestrating module that re-exports from:
-- | - Segment.Encoding — Mode-specific data encoding
-- | - Segment.CharTable — Character lookup tables
-- | - Segment.Accumulator — Incremental segment building

module Hydrogen.Element.Compound.QRCode.Encoding.Segment
  ( module Encoding
  , module CharTable
  , module Accumulator
  , Segment
  , mkSegment
  , segmentMode
  , segmentData
  , segmentCharCount
  , segmentBitLength
  , showSegment
  , segmentsEqual
  , compareSegmentsByEfficiency
  , isValidSegment
  , segmentEfficiency
  , encodeString
  , encodeSegment
  , encodeSegments
  , detectOptimalMode
  , canEncodeInMode
  , characterCountBits
  , segmentCapacity
  , fitsInVersion
  , minVersionForData
  , hasCapacityForData
  , exceedsMaxCapacity
  , modesDiffer
  , modeRank
  , compareModes
  , moreEfficientMode
  , lessEfficientMode
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (==)
  , (/=)
  , (&&)
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
  , compare
  , Ordering(LT, EQ, GT)
  )

import Data.Array (foldl, length, filter, head, (..))
import Data.Maybe (Maybe(Just, Nothing), fromMaybe, isJust)
import Data.String.CodeUnits (toCharArray)

import Hydrogen.Element.Compound.QRCode.Types 
  ( EncodingMode(ModeNumeric, ModeAlphanumeric, ModeByte, ModeKanji, ModeECI)
  , QRVersion
  , ErrorCorrection
  , versionToInt
  , mkVersion
  , modeIndicator
  , getCapacity
  )
import Hydrogen.Element.Compound.QRCode.Encoding.BitStream as BS

import Hydrogen.Element.Compound.QRCode.Encoding.Segment.Encoding
  ( encodeData
  , encodeNumeric
  , encodeAlphanumeric
  , encodeByte
  , encodeKanji
  , dataBitLength
  ) as Encoding

import Hydrogen.Element.Compound.QRCode.Encoding.Segment.CharTable
  ( alphanumericValue
  , isAlphanumericChar
  , isNumericChar
  , charToString
  ) as CharTable

import Hydrogen.Element.Compound.QRCode.Encoding.Segment.Accumulator
  ( SegmentAccumulator
  , emptyAccumulator
  , addCharToAccumulator
  , flushAccumulator
  , finalizeAccumulator
  ) as Accumulator

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // segment
-- ═════════════════════════════════════════════════════════════════════════════

type Segment =
  { mode :: EncodingMode
  , data :: String
  , charCount :: Int
  }

mkSegment :: EncodingMode -> String -> Segment
mkSegment mode str =
  { mode
  , data: str
  , charCount: length (toCharArray str)
  }

segmentMode :: Segment -> EncodingMode
segmentMode seg = seg.mode

segmentData :: Segment -> String
segmentData seg = seg.data

segmentCharCount :: Segment -> Int
segmentCharCount seg = seg.charCount

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // segment utilities
-- ═════════════════════════════════════════════════════════════════════════════

showSegment :: Segment -> String
showSegment seg =
  "Segment(" <> show seg.mode <> ", \"" <> seg.data <> "\", " <> show seg.charCount <> ")"

segmentsEqual :: Segment -> Segment -> Boolean
segmentsEqual a b =
  a.mode == b.mode && a.data == b.data && a.charCount == b.charCount

compareSegmentsByEfficiency :: Segment -> Segment -> Ordering
compareSegmentsByEfficiency a b = compare (segmentEfficiency a) (segmentEfficiency b)

segmentEfficiency :: Segment -> Number
segmentEfficiency seg =
  if seg.charCount == 0 then 0.0
  else
    let
      defaultVersion = mkVersion 1
      totalBits = segmentBitLength defaultVersion seg
    in
      intToNumber totalBits / intToNumber seg.charCount

intToNumber :: Int -> Number
intToNumber n = 
  if n < 0 then 0.0 - intToNumberPos (0 - n)
  else intToNumberPos n
  where
    intToNumberPos :: Int -> Number
    intToNumberPos i = buildNumber i 0.0
    
    buildNumber :: Int -> Number -> Number
    buildNumber remaining acc
      | remaining == 0 = acc
      | remaining > 1000 = buildNumber (remaining - 1000) (acc + 1000.0)
      | remaining > 100 = buildNumber (remaining - 100) (acc + 100.0)
      | remaining > 10 = buildNumber (remaining - 10) (acc + 10.0)
      | otherwise = buildNumber (remaining - 1) (acc + 1.0)

isValidSegment :: Segment -> Boolean
isValidSegment seg =
  seg.charCount /= 0 &&
  canEncodeInMode seg.mode seg.data &&
  seg.charCount == length (toCharArray seg.data)

segmentBitLength :: QRVersion -> Segment -> Int
segmentBitLength version seg =
  let
    modeLen = 4
    countLen = characterCountBits version seg.mode
    dataLen = Encoding.dataBitLength seg.mode seg.charCount
  in
    modeLen + countLen + dataLen

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // encoding
-- ═════════════════════════════════════════════════════════════════════════════

encodeString :: QRVersion -> String -> BS.BitStream
encodeString version str =
  let
    mode = detectOptimalMode str
    segment = mkSegment mode str
  in
    encodeSegment version segment

encodeSegment :: QRVersion -> Segment -> BS.BitStream
encodeSegment version seg =
  let
    modeStream = BS.fromInt (modeIndicator seg.mode) 4
    countBits = characterCountBits version seg.mode
    countStream = BS.fromInt seg.charCount countBits
    dataStream = Encoding.encodeData seg.mode seg.data
  in
    BS.concat [modeStream, countStream, dataStream]

encodeSegments :: QRVersion -> Array Segment -> BS.BitStream
encodeSegments version segments =
  foldl (\acc seg -> BS.append acc (encodeSegment version seg)) BS.empty segments

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // mode detection
-- ═════════════════════════════════════════════════════════════════════════════

detectOptimalMode :: String -> EncodingMode
detectOptimalMode str =
  let chars = toCharArray str
  in
    if allNumeric chars then ModeNumeric
    else if allAlphanumeric chars then ModeAlphanumeric
    else ModeByte
  where
    allNumeric :: Array Char -> Boolean
    allNumeric chars = length (filter CharTable.isNumericChar chars) == length chars
    
    allAlphanumeric :: Array Char -> Boolean
    allAlphanumeric chars = length (filter CharTable.isAlphanumericChar chars) == length chars

canEncodeInMode :: EncodingMode -> String -> Boolean
canEncodeInMode mode str =
  let chars = toCharArray str
  in case mode of
    ModeNumeric -> length (filter CharTable.isNumericChar chars) == length chars
    ModeAlphanumeric -> length (filter CharTable.isAlphanumericChar chars) == length chars
    ModeByte -> true
    ModeKanji -> false
    ModeECI -> true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // character count
-- ═════════════════════════════════════════════════════════════════════════════

characterCountBits :: QRVersion -> EncodingMode -> Int
characterCountBits version mode =
  let v = versionToInt version
  in case mode of
    ModeNumeric
      | v <= 9 -> 10
      | v <= 26 -> 12
      | otherwise -> 14
    ModeAlphanumeric
      | v <= 9 -> 9
      | v <= 26 -> 11
      | otherwise -> 13
    ModeByte
      | v <= 9 -> 8
      | otherwise -> 16
    ModeKanji
      | v <= 9 -> 8
      | v <= 26 -> 10
      | otherwise -> 12
    ModeECI -> 8

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // capacity
-- ═════════════════════════════════════════════════════════════════════════════

segmentCapacity :: QRVersion -> ErrorCorrection -> Int
segmentCapacity version ec =
  let cap = getCapacity version ec
  in cap.byte * 8

fitsInVersion :: QRVersion -> ErrorCorrection -> String -> Boolean
fitsInVersion version ec str =
  let
    segment = mkSegment (detectOptimalMode str) str
    neededBits = segmentBitLength version segment
    capacity = segmentCapacity version ec
  in
    neededBits <= capacity

minVersionForData :: ErrorCorrection -> String -> Maybe QRVersion
minVersionForData ec str =
  let
    versions = map mkVersion (1 .. 40)
    fitting = filter (\v -> fitsInVersion v ec str) versions
  in
    head fitting

hasCapacityForData :: ErrorCorrection -> String -> Boolean
hasCapacityForData ec str = isJust (minVersionForData ec str)

exceedsMaxCapacity :: ErrorCorrection -> String -> Boolean
exceedsMaxCapacity ec str = case minVersionForData ec str of
  Nothing -> true
  Just _ -> false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // mode utilities
-- ═════════════════════════════════════════════════════════════════════════════

modesDiffer :: EncodingMode -> EncodingMode -> Boolean
modesDiffer a b = a /= b

modeRank :: EncodingMode -> Int
modeRank mode = case mode of
  ModeNumeric -> 4
  ModeAlphanumeric -> 3
  ModeByte -> 2
  ModeKanji -> 1
  ModeECI -> 0

compareModes :: EncodingMode -> EncodingMode -> Ordering
compareModes a b = compare (modeRank a) (modeRank b)

moreEfficientMode :: EncodingMode -> EncodingMode -> Boolean
moreEfficientMode a b = modeRank a > modeRank b

lessEfficientMode :: EncodingMode -> EncodingMode -> Boolean
lessEfficientMode a b = modeRank a < modeRank b
