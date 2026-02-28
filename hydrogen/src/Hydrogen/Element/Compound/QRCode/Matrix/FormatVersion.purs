-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // element // qr-code // matrix // format-version
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Code Format and Version Information — BCH encoding and placement.
-- |
-- | ## Format Information
-- |
-- | Format info encodes EC level (2 bits) and mask pattern (3 bits):
-- | - 5 data bits + 10 BCH error correction bits = 15 bits total
-- | - XOR'd with mask 101010000010010 (0x5412)
-- | - Placed near all three finder patterns
-- |
-- | ## Version Information (Version 7+)
-- |
-- | Version info encodes the QR version number:
-- | - 6 data bits + 12 BCH error correction bits = 18 bits total
-- | - Placed in two 3×6 blocks near top-right and bottom-left finders
-- |
-- | ## BCH Encoding
-- |
-- | Uses BCH (Bose-Chaudhuri-Hocquenghem) codes for error correction:
-- | - Format: BCH(15,5) with generator x^10 + x^8 + x^5 + x^4 + x^2 + x + 1
-- | - Version: BCH(18,6) with generator 1111100100101

module Hydrogen.Element.Compound.QRCode.Matrix.FormatVersion
  ( encodeFormatInfo
  , placeFormatInfo
  , encodeVersionInfo
  , placeVersionInfo
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( otherwise
  , (/=)
  , (+)
  , (-)
  , (*)
  , (<)
  )

import Data.Array (foldl, index, (..))
import Data.EuclideanRing (div, mod)
import Data.Int.Bits (xor, shr, and)
import Data.Maybe (fromMaybe)

import Hydrogen.Element.Compound.QRCode.Types
  ( QRVersion
  , QRMatrix
  , ErrorCorrection(ECLow, ECMedium, ECQuartile, ECHigh)
  , Module(Dark, Light)
  , ModuleType(FormatModule, VersionModule)
  , matrixSize
  , setModule
  , versionToInt
  )

import Hydrogen.Element.Compound.QRCode.Matrix.Mask (MaskPattern, maskPatternIndex)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // format information
-- ═════════════════════════════════════════════════════════════════════════════

-- | Encode format information (EC level + mask pattern).
-- |
-- | Format info is 5 bits (2 EC + 3 mask) with 10 BCH error correction bits,
-- | then XOR'd with mask 101010000010010.
encodeFormatInfo :: ErrorCorrection -> MaskPattern -> Int
encodeFormatInfo ec mask =
  let
    ecBits = ecIndicator ec
    maskBits = maskPatternIndex mask
    data5 = ecBits * 8 + maskBits  -- 5-bit value
    -- BCH(15,5) encoding
    bch = bchEncode data5
    -- XOR with mask
    masked = xor bch 0x5412  -- 101010000010010
  in
    masked
  where
    ecIndicator :: ErrorCorrection -> Int
    ecIndicator = case _ of
      ECLow -> 1      -- 01
      ECMedium -> 0   -- 00
      ECQuartile -> 3 -- 11
      ECHigh -> 2     -- 10
    
    bchEncode :: Int -> Int
    bchEncode dat =
      let
        -- Generator polynomial for BCH(15,5): G(x) = x^10 + x^8 + x^5 + x^4 + x^2 + x + 1
        -- = 10100110111 = 0x537
        gen = 0x537
        shifted = dat * 1024  -- shift left by 10 bits
      in
        bchDivide shifted gen
    
    bchDivide :: Int -> Int -> Int
    bchDivide dividend generator =
      divideLoop dividend 14
      where
        divideLoop :: Int -> Int -> Int
        divideLoop d bit
          | bit < 10 = d
          | otherwise =
              if and (shr d bit) 1 /= 0
                then divideLoop (xor d (generator * pow2 (bit - 10))) (bit - 1)
                else divideLoop d (bit - 1)

-- | Place format information in the matrix.
placeFormatInfo :: ErrorCorrection -> MaskPattern -> QRMatrix -> QRMatrix
placeFormatInfo ec mask matrix =
  let
    format = encodeFormatInfo ec mask
    size = matrixSize matrix
    m1 = placeFormatBitsTopLeft format matrix
    m2 = placeFormatBitsOther format size m1
  in
    m2
  where
    placeFormatBitsTopLeft :: Int -> QRMatrix -> QRMatrix
    placeFormatBitsTopLeft fmt m =
      -- Bits 0-5 go in col 8, rows 0-5 (skip row 6)
      -- Bit 6 goes in col 8, row 7
      -- Bit 7 goes in col 8, row 8
      -- Bits 8-14 go in row 8, cols 7-0 (skip col 6)
      let
        positions = [
          { row: 0, col: 8 }, { row: 1, col: 8 }, { row: 2, col: 8 },
          { row: 3, col: 8 }, { row: 4, col: 8 }, { row: 5, col: 8 },
          { row: 7, col: 8 }, { row: 8, col: 8 },
          { row: 8, col: 7 }, { row: 8, col: 5 }, { row: 8, col: 4 },
          { row: 8, col: 3 }, { row: 8, col: 2 }, { row: 8, col: 1 }, { row: 8, col: 0 }
        ]
      in
        foldl (\acc i ->
          let
            pos = fromMaybe { row: 0, col: 0 } (index positions i)
            bit = and (shr fmt (14 - i)) 1
            modVal = if bit /= 0 then Dark FormatModule else Light FormatModule
          in
            setModule pos.row pos.col modVal acc
        ) m (0 .. 14)
    
    placeFormatBitsOther :: Int -> Int -> QRMatrix -> QRMatrix
    placeFormatBitsOther fmt size m =
      -- Second copy: row 8 cols (size-8) to (size-1), and col 8 rows (size-7) to (size-1)
      let
        -- Row 8, cols size-8 to size-1 (bits 0-7)
        m1 = foldl (\acc i ->
          let
            col = size - 8 + i
            bit = and (shr fmt (14 - i)) 1
            modVal = if bit /= 0 then Dark FormatModule else Light FormatModule
          in
            setModule 8 col modVal acc
        ) m (0 .. 7)
        -- Col 8, rows size-7 to size-1 (bits 8-14), plus dark module at (size-8, 8)
        m2 = foldl (\acc i ->
          let
            row = size - 7 + i
            bit = and (shr fmt (6 - i)) 1
            modVal = if bit /= 0 then Dark FormatModule else Light FormatModule
          in
            setModule row 8 modVal acc
        ) m1 (0 .. 6)
        -- Dark module always at (size-8, 8)
        m3 = setModule (size - 8) 8 (Dark FormatModule) m2
      in
        m3

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // version information
-- ═════════════════════════════════════════════════════════════════════════════

-- | Encode version information (version 7+).
-- |
-- | Version info is 6 bits + 12 BCH error correction bits.
encodeVersionInfo :: QRVersion -> Int
encodeVersionInfo version =
  let
    v = versionToInt version
  in
    if v < 7 then 0
    else
      let
        -- BCH(18,6) encoding with generator 1111100100101 = 0x1F25
        gen = 0x1F25
        shifted = v * 4096  -- shift left by 12 bits
      in
        bchDivideVersion shifted gen v
  where
    bchDivideVersion :: Int -> Int -> Int -> Int
    bchDivideVersion dividend generator ver =
      let remainder = divideLoopV dividend generator 17
      in ver * 4096 + remainder
    
    divideLoopV :: Int -> Int -> Int -> Int
    divideLoopV d gen bit
      | bit < 12 = and d 0xFFF  -- Keep only 12 bits
      | otherwise =
          if and (shr d bit) 1 /= 0
            then divideLoopV (xor d (gen * pow2 (bit - 12))) gen (bit - 1)
            else divideLoopV d gen (bit - 1)

-- | Place version information (version 7+).
placeVersionInfo :: QRVersion -> QRMatrix -> QRMatrix
placeVersionInfo version matrix =
  let v = versionToInt version
  in if v < 7 then matrix
     else placeVersionBits version matrix
  where
    placeVersionBits :: QRVersion -> QRMatrix -> QRMatrix
    placeVersionBits ver m =
      let
        info = encodeVersionInfo ver
        size = matrixSize m
        -- Block 1: rows 0-5, cols (size-11) to (size-9)
        m1 = foldl (\acc i ->
          let
            row = div i 3
            col = size - 11 + mod i 3
            bit = and (shr info i) 1
            modVal = if bit /= 0 then Dark VersionModule else Light VersionModule
          in
            setModule row col modVal acc
        ) m (0 .. 17)
        -- Block 2: rows (size-11) to (size-9), cols 0-5
        m2 = foldl (\acc i ->
          let
            row = size - 11 + mod i 3
            col = div i 3
            bit = and (shr info i) 1
            modVal = if bit /= 0 then Dark VersionModule else Light VersionModule
          in
            setModule row col modVal acc
        ) m1 (0 .. 17)
      in
        m2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Power of 2
pow2 :: Int -> Int
pow2 0 = 1
pow2 n = 2 * pow2 (n - 1)
