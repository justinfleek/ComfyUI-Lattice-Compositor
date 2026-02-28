-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // element // qr-code // types // encoding-mode
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Encoding Mode — Character set and bit efficiency modes.
-- |
-- | ## Modes
-- |
-- | Different modes have different character sets and bit efficiencies:
-- | - Numeric: 0-9 only, 10 bits per 3 digits
-- | - Alphanumeric: 0-9, A-Z, space, $%*+-./: — 11 bits per 2 chars
-- | - Byte: Any byte, 8 bits per character
-- | - Kanji: Shift-JIS double-byte, 13 bits per character
-- | - ECI: Extended Channel Interpretation (for other encodings)
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Data.Char (character codes)
-- | - Data.Array (all)

module Hydrogen.Element.Compound.QRCode.Types.EncodingMode
  ( -- * Encoding Mode
    EncodingMode(ModeNumeric, ModeAlphanumeric, ModeByte, ModeKanji, ModeECI)
  , modeIndicator
  , detectMode
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , map
  , (>=)
  , (<=)
  , (==)
  , (||)
  , (&&)
  , Ordering(LT, EQ, GT)
  )

import Data.Char (toCharCode)
import Data.Array (all) as Array
import Data.String.CodeUnits (toCharArray)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // encoding mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Data encoding mode.
-- |
-- | Different modes have different character sets and bit efficiencies:
-- | - Numeric: 0-9 only, 10 bits per 3 digits
-- | - Alphanumeric: 0-9, A-Z, space, $%*+-./: — 11 bits per 2 chars
-- | - Byte: Any byte (UTF-8, Latin-1, etc.)
-- | - Kanji: Shift-JIS kanji
-- | - ECI: Extended channel interpretation
data EncodingMode
  = ModeNumeric       -- ^ 0-9 only
  | ModeAlphanumeric  -- ^ 0-9, A-Z, space, $%*+-./:
  | ModeByte          -- ^ Any byte (UTF-8, Latin-1, etc.)
  | ModeKanji         -- ^ Shift-JIS kanji
  | ModeECI           -- ^ Extended channel interpretation

derive instance eqEncodingMode :: Eq EncodingMode

instance ordEncodingMode :: Ord EncodingMode where
  compare ModeNumeric ModeNumeric = EQ
  compare ModeNumeric _ = LT
  compare ModeAlphanumeric ModeNumeric = GT
  compare ModeAlphanumeric ModeAlphanumeric = EQ
  compare ModeAlphanumeric _ = LT
  compare ModeByte ModeKanji = LT
  compare ModeByte ModeECI = LT
  compare ModeByte ModeByte = EQ
  compare ModeByte _ = GT
  compare ModeKanji ModeECI = LT
  compare ModeKanji ModeKanji = EQ
  compare ModeKanji _ = GT
  compare ModeECI ModeECI = EQ
  compare ModeECI _ = GT

instance showEncodingMode :: Show EncodingMode where
  show ModeNumeric = "Numeric"
  show ModeAlphanumeric = "Alphanumeric"
  show ModeByte = "Byte"
  show ModeKanji = "Kanji"
  show ModeECI = "ECI"

-- | Mode indicator bits (4 bits in QR code)
modeIndicator :: EncodingMode -> Int
modeIndicator = case _ of
  ModeNumeric -> 1       -- 0001
  ModeAlphanumeric -> 2  -- 0010
  ModeByte -> 4          -- 0100
  ModeKanji -> 8         -- 1000
  ModeECI -> 7           -- 0111

-- | Detect the most efficient encoding mode for a string.
-- |
-- | Checks characters to find the smallest mode that can encode the input:
-- | Numeric < Alphanumeric < Byte
detectMode :: String -> EncodingMode
detectMode str =
  let
    -- Convert Char to Int values for comparison
    charCodes = map toCharCode (toCharArray str)
    
    isNumeric :: Int -> Boolean
    isNumeric cp = cp >= 48 && cp <= 57  -- '0' to '9'
    
    isAlphanumeric :: Int -> Boolean
    isAlphanumeric cp =
      isNumeric cp ||
      (cp >= 65 && cp <= 90) ||  -- 'A' to 'Z'
      cp == 32 ||  -- space
      cp == 36 ||  -- $
      cp == 37 ||  -- %
      cp == 42 ||  -- *
      cp == 43 ||  -- +
      cp == 45 ||  -- -
      cp == 46 ||  -- .
      cp == 47 ||  -- /
      cp == 58     -- :
    
    allNumeric = Array.all isNumeric charCodes
    allAlphanumeric = Array.all isAlphanumeric charCodes
  in
    if allNumeric then ModeNumeric
    else if allAlphanumeric then ModeAlphanumeric
    else ModeByte
