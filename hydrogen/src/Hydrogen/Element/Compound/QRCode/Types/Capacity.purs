-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // element // qrcode // types // capacity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Capacity — Character capacity lookup table.
-- |
-- | ## Capacity Table (ISO/IEC 18004)
-- |
-- | Specifies how many characters can be encoded for each:
-- | - Version (1-40)
-- | - Error correction level (L/M/Q/H)
-- | - Encoding mode (Numeric/Alphanumeric/Byte/Kanji)
-- |
-- | ## Dependencies
-- |
-- | - Prelude (basic operations)
-- | - Data.EuclideanRing (division)

module Hydrogen.Element.Compound.QRCode.Types.Capacity
  ( -- * Capacity Type
    Capacity
  , getCapacity
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (*)
  )

import Data.EuclideanRing (div)

import Hydrogen.Element.Compound.QRCode.Types.Version (QRVersion(QRVersion))
import Hydrogen.Element.Compound.QRCode.Types.ErrorCorrection (ErrorCorrection(ECLow, ECMedium, ECQuartile, ECHigh))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // capacity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Capacity information for a version/EC combination.
-- |
-- | Specifies how many characters can be encoded.
type Capacity =
  { numeric :: Int        -- ^ Max numeric characters
  , alphanumeric :: Int   -- ^ Max alphanumeric characters
  , byte :: Int           -- ^ Max byte characters
  , kanji :: Int          -- ^ Max kanji characters
  }

-- | Get capacity for a version and error correction level.
-- |
-- | This is a lookup table based on ISO/IEC 18004.
-- | Returns capacity for Version 1-10 (most common).
-- | Larger versions follow the same pattern with more capacity.
getCapacity :: QRVersion -> ErrorCorrection -> Capacity
getCapacity (QRVersion v) ec = case v of
  1 -> case ec of
    ECLow -> { numeric: 41, alphanumeric: 25, byte: 17, kanji: 10 }
    ECMedium -> { numeric: 34, alphanumeric: 20, byte: 14, kanji: 8 }
    ECQuartile -> { numeric: 27, alphanumeric: 16, byte: 11, kanji: 7 }
    ECHigh -> { numeric: 17, alphanumeric: 10, byte: 7, kanji: 4 }
  2 -> case ec of
    ECLow -> { numeric: 77, alphanumeric: 47, byte: 32, kanji: 20 }
    ECMedium -> { numeric: 63, alphanumeric: 38, byte: 26, kanji: 16 }
    ECQuartile -> { numeric: 48, alphanumeric: 29, byte: 20, kanji: 12 }
    ECHigh -> { numeric: 34, alphanumeric: 20, byte: 14, kanji: 8 }
  3 -> case ec of
    ECLow -> { numeric: 127, alphanumeric: 77, byte: 53, kanji: 32 }
    ECMedium -> { numeric: 101, alphanumeric: 61, byte: 42, kanji: 26 }
    ECQuartile -> { numeric: 77, alphanumeric: 47, byte: 32, kanji: 20 }
    ECHigh -> { numeric: 58, alphanumeric: 35, byte: 24, kanji: 15 }
  4 -> case ec of
    ECLow -> { numeric: 187, alphanumeric: 114, byte: 78, kanji: 48 }
    ECMedium -> { numeric: 149, alphanumeric: 90, byte: 62, kanji: 38 }
    ECQuartile -> { numeric: 111, alphanumeric: 67, byte: 46, kanji: 28 }
    ECHigh -> { numeric: 82, alphanumeric: 50, byte: 34, kanji: 21 }
  5 -> case ec of
    ECLow -> { numeric: 255, alphanumeric: 154, byte: 106, kanji: 65 }
    ECMedium -> { numeric: 202, alphanumeric: 122, byte: 84, kanji: 52 }
    ECQuartile -> { numeric: 144, alphanumeric: 87, byte: 60, kanji: 37 }
    ECHigh -> { numeric: 106, alphanumeric: 64, byte: 44, kanji: 27 }
  6 -> case ec of
    ECLow -> { numeric: 322, alphanumeric: 195, byte: 134, kanji: 82 }
    ECMedium -> { numeric: 255, alphanumeric: 154, byte: 106, kanji: 65 }
    ECQuartile -> { numeric: 178, alphanumeric: 108, byte: 74, kanji: 45 }
    ECHigh -> { numeric: 139, alphanumeric: 84, byte: 58, kanji: 36 }
  7 -> case ec of
    ECLow -> { numeric: 370, alphanumeric: 224, byte: 154, kanji: 95 }
    ECMedium -> { numeric: 293, alphanumeric: 178, byte: 122, kanji: 75 }
    ECQuartile -> { numeric: 207, alphanumeric: 125, byte: 86, kanji: 53 }
    ECHigh -> { numeric: 154, alphanumeric: 93, byte: 64, kanji: 39 }
  8 -> case ec of
    ECLow -> { numeric: 461, alphanumeric: 279, byte: 192, kanji: 118 }
    ECMedium -> { numeric: 365, alphanumeric: 221, byte: 152, kanji: 93 }
    ECQuartile -> { numeric: 259, alphanumeric: 157, byte: 108, kanji: 66 }
    ECHigh -> { numeric: 202, alphanumeric: 122, byte: 84, kanji: 52 }
  9 -> case ec of
    ECLow -> { numeric: 552, alphanumeric: 335, byte: 230, kanji: 141 }
    ECMedium -> { numeric: 432, alphanumeric: 262, byte: 180, kanji: 111 }
    ECQuartile -> { numeric: 312, alphanumeric: 189, byte: 130, kanji: 80 }
    ECHigh -> { numeric: 235, alphanumeric: 143, byte: 98, kanji: 60 }
  10 -> case ec of
    ECLow -> { numeric: 652, alphanumeric: 395, byte: 271, kanji: 167 }
    ECMedium -> { numeric: 513, alphanumeric: 311, byte: 213, kanji: 131 }
    ECQuartile -> { numeric: 364, alphanumeric: 221, byte: 151, kanji: 93 }
    ECHigh -> { numeric: 288, alphanumeric: 174, byte: 119, kanji: 74 }
  -- Default fallback for versions > 10 (simplified estimate)
  _ ->
    let
      baseCapacity = case ec of
        ECLow -> 652 + (v - 10) * 60
        ECMedium -> 513 + (v - 10) * 45
        ECQuartile -> 364 + (v - 10) * 32
        ECHigh -> 288 + (v - 10) * 25
    in
      { numeric: baseCapacity
      , alphanumeric: div (baseCapacity * 6) 10
      , byte: div (baseCapacity * 4) 10
      , kanji: div (baseCapacity * 25) 100
      }
