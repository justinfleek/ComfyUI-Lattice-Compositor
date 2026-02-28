-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // element // qr-code // types // code-word
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Codeword — 8-bit values in the QR data stream.
-- |
-- | ## Purpose
-- |
-- | Codewords are the fundamental unit of data in QR codes:
-- | 1. Data is encoded into codewords
-- | 2. Error correction codewords are added
-- | 3. All codewords are placed in the matrix
-- |
-- | ## Bounds
-- |
-- | Values are bounded to 0-255 (8 bits). Use `mkCodeword` for
-- | safe construction with automatic clamping.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show, Bounded)
-- | - Data.EuclideanRing (div)

module Hydrogen.Element.Compound.QRCode.Types.Codeword
  ( -- * Codeword Type
    Codeword(Codeword)
  , mkCodeword
  , codewordValue
  , minCodeword
  , maxCodeword
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Bounded
  , show
  , (<>)
  , (<)
  , (>)
  , (-)
  , (*)
  , (==)
  , otherwise
  , top
  , bottom
  )

import Data.EuclideanRing (div)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // codeword
-- ═════════════════════════════════════════════════════════════════════════════

-- | A codeword (8-bit value) in the QR data stream.
-- |
-- | Codewords are the fundamental unit of data in QR codes.
-- | The data is encoded into codewords, then error correction
-- | codewords are added, and finally they're placed in the matrix.
-- |
-- | Values are bounded to 0-255 (8 bits). Use `mkCodeword` for
-- | safe construction with automatic clamping.
newtype Codeword = Codeword Int

derive instance eqCodeword :: Eq Codeword
derive instance ordCodeword :: Ord Codeword

instance showCodeword :: Show Codeword where
  show (Codeword c) = "0x" <> toHex c
    where
      toHex :: Int -> String
      toHex n =
        let
          hexDigit d
            | d < 10 = show d
            | d == 10 = "A"
            | d == 11 = "B"
            | d == 12 = "C"
            | d == 13 = "D"
            | d == 14 = "E"
            | otherwise = "F"
          high = div n 16
          low = n - (high * 16)
        in
          hexDigit high <> hexDigit low

instance boundedCodeword :: Bounded Codeword where
  top = Codeword 255
  bottom = Codeword 0

-- | Create a codeword, clamping to valid range [0, 255].
-- |
-- | ```purescript
-- | mkCodeword 128   -- Codeword 128
-- | mkCodeword (-5)  -- Codeword 0 (clamped)
-- | mkCodeword 300   -- Codeword 255 (clamped)
-- | ```
mkCodeword :: Int -> Codeword
mkCodeword n
  | n < 0 = Codeword 0
  | n > 255 = Codeword 255
  | otherwise = Codeword n

-- | Extract codeword value as Int (0-255)
codewordValue :: Codeword -> Int
codewordValue (Codeword c) = c

-- | Minimum codeword value (0x00)
minCodeword :: Codeword
minCodeword = bottom

-- | Maximum codeword value (0xFF)
maxCodeword :: Codeword
maxCodeword = top
