-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--        // hydrogen // element // qrcode // encoding // segment // accumulator
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Segment accumulator for building segments incrementally.

module Hydrogen.Element.Compound.QRCode.Encoding.Segment.Accumulator
  ( SegmentAccumulator
  , Segment
  , emptyAccumulator
  , addCharToAccumulator
  , flushAccumulator
  , finalizeAccumulator
  , mkSegmentInternal
  ) where

import Prelude
  ( (==)
  , (<>)
  )

import Data.Array (length, snoc)
import Data.String.CodeUnits (toCharArray)

import Hydrogen.Element.Compound.QRCode.Types (EncodingMode)
import Hydrogen.Element.Compound.QRCode.Encoding.Segment.CharTable (charToString)

type Segment =
  { mode :: EncodingMode
  , data :: String
  , charCount :: Int
  }

type SegmentAccumulator =
  { segments :: Array Segment
  , currentMode :: EncodingMode
  , buffer :: String
  }

emptyAccumulator :: EncodingMode -> SegmentAccumulator
emptyAccumulator mode =
  { segments: []
  , currentMode: mode
  , buffer: ""
  }

addCharToAccumulator :: Char -> SegmentAccumulator -> SegmentAccumulator
addCharToAccumulator c acc =
  let charStr = charToString c
  in acc { buffer = acc.buffer <> charStr }

flushAccumulator :: SegmentAccumulator -> SegmentAccumulator
flushAccumulator acc =
  if acc.buffer == "" then acc
  else
    let
      seg = mkSegmentInternal acc.currentMode acc.buffer
      newSegments = snoc acc.segments seg
    in
      acc { segments = newSegments, buffer = "" }

finalizeAccumulator :: SegmentAccumulator -> Array Segment
finalizeAccumulator acc =
  let flushed = flushAccumulator acc
  in flushed.segments

mkSegmentInternal :: EncodingMode -> String -> Segment
mkSegmentInternal mode str =
  { mode
  , data: str
  , charCount: length (toCharArray str)
  }
