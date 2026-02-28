-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // element // qrcode // matrix // patterns
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Code Pattern Placement — Finder, timing, alignment, and format areas.
-- |
-- | ## Pattern Types
-- |
-- | 1. **Finder patterns** — 7×7 patterns in three corners (TL, TR, BL)
-- | 2. **Separators** — 1-module white border around finders
-- | 3. **Timing patterns** — Alternating dark/light from finder to finder
-- | 4. **Alignment patterns** — 5×5 patterns (version 2+)
-- | 5. **Format/version areas** — Reserved for encoding metadata
-- |
-- | ## Alignment Pattern Positions
-- |
-- | Each QR version (2-40) has specific alignment pattern center positions
-- | defined in ISO 18004. Version 1 has no alignment patterns.

module Hydrogen.Element.Compound.QRCode.Matrix.Patterns
  ( initializeMatrix
  , placeFinderPatterns
  , placeSeparators
  , placeTimingPatterns
  , placeAlignmentPatterns
  , alignmentPatternPositions
  , reserveFormatAreas
  , reserveVersionAreas
  , hasAlignmentPatterns
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( map
  , not
  , negate
  , (==)
  , (/=)
  , (+)
  , (-)
  , (>=)
  , (<=)
  , (&&)
  , (||)
  , (<)
  )

import Data.Array as Array
import Data.Array (foldl, filter, (..))
import Data.EuclideanRing (mod)
import Data.Ord (abs)

import Hydrogen.Element.Compound.QRCode.Types
  ( QRVersion
  , QRMatrix
  , Module(Dark, Light, Reserved)
  , ModuleType(FinderModule, QuietModule, TimingModule, AlignmentModule)
  , mkMatrix
  , matrixSize
  , setModule
  , versionSize
  , versionToInt
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // matrix initialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Initialize empty matrix for a version.
initializeMatrix :: QRVersion -> QRMatrix
initializeMatrix version = mkMatrix (versionSize version)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // finder patterns
-- ═════════════════════════════════════════════════════════════════════════════

-- | Place the three finder patterns in corners.
-- |
-- | Finder patterns are 7x7 with structure:
-- | ███████
-- | █░░░░░█
-- | █░███░█
-- | █░███░█
-- | █░███░█
-- | █░░░░░█
-- | ███████
placeFinderPatterns :: QRMatrix -> QRMatrix
placeFinderPatterns matrix =
  let
    size = matrixSize matrix
    -- Top-left at (0, 0)
    m1 = placeFinderPattern 0 0 matrix
    -- Top-right at (0, size-7)
    m2 = placeFinderPattern 0 (size - 7) m1
    -- Bottom-left at (size-7, 0)
    m3 = placeFinderPattern (size - 7) 0 m2
  in
    m3

-- | Place a single 7x7 finder pattern at (row, col).
placeFinderPattern :: Int -> Int -> QRMatrix -> QRMatrix
placeFinderPattern startRow startCol matrix =
  foldl placeRow matrix (0 .. 6)
  where
    placeRow :: QRMatrix -> Int -> QRMatrix
    placeRow m r = foldl (placeCell r) m (0 .. 6)
    
    placeCell :: Int -> QRMatrix -> Int -> QRMatrix
    placeCell r m c =
      let
        row = startRow + r
        col = startCol + c
        isDark = isFinderDark r c
        modVal = if isDark then Dark FinderModule else Light FinderModule
      in
        setModule row col modVal m
    
    -- Determine if position in finder is dark
    isFinderDark :: Int -> Int -> Boolean
    isFinderDark r c =
      -- Outer ring is dark
      r == 0 || r == 6 || c == 0 || c == 6 ||
      -- Inner 3x3 is dark
      (r >= 2 && r <= 4 && c >= 2 && c <= 4)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // separators
-- ═════════════════════════════════════════════════════════════════════════════

-- | Place separators (white border) around finder patterns.
-- |
-- | Separators are single-module-wide white areas.
placeSeparators :: QRMatrix -> QRMatrix
placeSeparators matrix =
  let
    size = matrixSize matrix
    m1 = placeSeparatorTL matrix          -- Top-left
    m2 = placeSeparatorTR size m1         -- Top-right
    m3 = placeSeparatorBL size m2         -- Bottom-left
  in
    m3
  where
    -- Top-left: row 7 (0-7) and col 7 (0-7)
    placeSeparatorTL :: QRMatrix -> QRMatrix
    placeSeparatorTL m =
      let
        m1 = foldl (\acc c -> setModule 7 c (Light QuietModule) acc) m (0 .. 7)
        m2 = foldl (\acc r -> setModule r 7 (Light QuietModule) acc) m1 (0 .. 6)
      in
        m2
    
    -- Top-right: row 7 and col (size-8)
    placeSeparatorTR :: Int -> QRMatrix -> QRMatrix
    placeSeparatorTR size m =
      let
        col = size - 8
        m1 = foldl (\acc c -> setModule 7 c (Light QuietModule) acc) m ((size - 8) .. (size - 1))
        m2 = foldl (\acc r -> setModule r col (Light QuietModule) acc) m1 (0 .. 6)
      in
        m2
    
    -- Bottom-left: row (size-8) and col 7
    placeSeparatorBL :: Int -> QRMatrix -> QRMatrix
    placeSeparatorBL size m =
      let
        row = size - 8
        m1 = foldl (\acc c -> setModule row c (Light QuietModule) acc) m (0 .. 7)
        m2 = foldl (\acc r -> setModule r 7 (Light QuietModule) acc) m1 ((size - 7) .. (size - 1))
      in
        m2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // timing patterns
-- ═════════════════════════════════════════════════════════════════════════════

-- | Place timing patterns.
-- |
-- | Timing patterns are alternating dark/light stripes:
-- | - Horizontal: row 6, from col 8 to col (size-9)
-- | - Vertical: col 6, from row 8 to row (size-9)
placeTimingPatterns :: QRMatrix -> QRMatrix
placeTimingPatterns matrix =
  let
    size = matrixSize matrix
    -- Horizontal timing pattern
    m1 = foldl (placeHorizontal) matrix (8 .. (size - 9))
    -- Vertical timing pattern
    m2 = foldl (placeVertical) m1 (8 .. (size - 9))
  in
    m2
  where
    placeHorizontal :: QRMatrix -> Int -> QRMatrix
    placeHorizontal m col =
      let isDark = mod col 2 == 0
          modVal = if isDark then Dark TimingModule else Light TimingModule
      in setModule 6 col modVal m
    
    placeVertical :: QRMatrix -> Int -> QRMatrix
    placeVertical m row =
      let isDark = mod row 2 == 0
          modVal = if isDark then Dark TimingModule else Light TimingModule
      in setModule row 6 modVal m

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // alignment patterns
-- ═════════════════════════════════════════════════════════════════════════════

-- | Place alignment patterns for version 2+.
-- |
-- | Alignment patterns are 5x5:
-- | █████
-- | █░░░█
-- | █░█░█
-- | █░░░█
-- | █████
placeAlignmentPatterns :: QRVersion -> QRMatrix -> QRMatrix
placeAlignmentPatterns version matrix =
  let
    positions = alignmentPatternPositions version
    -- Generate all center positions
    centers = Array.concatMap (\r -> map (\c -> { row: r, col: c }) positions) positions
    -- Filter out positions that overlap with finders
    size = matrixSize matrix
    validCenters = filter (\p -> not (overlapsWithFinder p.row p.col size)) centers
  in
    foldl (\m p -> placeAlignmentPattern p.row p.col m) matrix validCenters
  where
    overlapsWithFinder :: Int -> Int -> Int -> Boolean
    overlapsWithFinder row col size =
      -- Top-left finder region (0-8, 0-8)
      (row <= 8 && col <= 8) ||
      -- Top-right finder region (0-8, size-9 to size-1)
      (row <= 8 && col >= size - 9) ||
      -- Bottom-left finder region (size-9 to size-1, 0-8)
      (row >= size - 9 && col <= 8)

-- | Place a single 5x5 alignment pattern centered at (row, col).
placeAlignmentPattern :: Int -> Int -> QRMatrix -> QRMatrix
placeAlignmentPattern centerRow centerCol matrix =
  foldl placeRow matrix ((-2) .. 2)
  where
    placeRow :: QRMatrix -> Int -> QRMatrix
    placeRow m dr = foldl (placeCell dr) m ((-2) .. 2)
    
    placeCell :: Int -> QRMatrix -> Int -> QRMatrix
    placeCell dr m dc =
      let
        row = centerRow + dr
        col = centerCol + dc
        isDark = isAlignmentDark dr dc
        modVal = if isDark then Dark AlignmentModule else Light AlignmentModule
      in
        setModule row col modVal m
    
    isAlignmentDark :: Int -> Int -> Boolean
    isAlignmentDark dr dc =
      -- Outer ring or center dot
      abs dr == 2 || abs dc == 2 || (dr == 0 && dc == 0)

-- | Get alignment pattern center positions for a version.
-- |
-- | These are defined in the QR specification per version.
alignmentPatternPositions :: QRVersion -> Array Int
alignmentPatternPositions version =
  let v = versionToInt version
  in case v of
    1 -> []  -- Version 1 has no alignment patterns
    2 -> [6, 18]
    3 -> [6, 22]
    4 -> [6, 26]
    5 -> [6, 30]
    6 -> [6, 34]
    7 -> [6, 22, 38]
    8 -> [6, 24, 42]
    9 -> [6, 26, 46]
    10 -> [6, 28, 50]
    11 -> [6, 30, 54]
    12 -> [6, 32, 58]
    13 -> [6, 34, 62]
    14 -> [6, 26, 46, 66]
    15 -> [6, 26, 48, 70]
    16 -> [6, 26, 50, 74]
    17 -> [6, 30, 54, 78]
    18 -> [6, 30, 56, 82]
    19 -> [6, 30, 58, 86]
    20 -> [6, 34, 62, 90]
    21 -> [6, 28, 50, 72, 94]
    22 -> [6, 26, 50, 74, 98]
    23 -> [6, 30, 54, 78, 102]
    24 -> [6, 28, 54, 80, 106]
    25 -> [6, 32, 58, 84, 110]
    26 -> [6, 30, 58, 86, 114]
    27 -> [6, 34, 62, 90, 118]
    28 -> [6, 26, 50, 74, 98, 122]
    29 -> [6, 30, 54, 78, 102, 126]
    30 -> [6, 26, 52, 78, 104, 130]
    31 -> [6, 30, 56, 82, 108, 134]
    32 -> [6, 34, 60, 86, 112, 138]
    33 -> [6, 30, 58, 86, 114, 142]
    34 -> [6, 34, 62, 90, 118, 146]
    35 -> [6, 30, 54, 78, 102, 126, 150]
    36 -> [6, 24, 50, 76, 102, 128, 154]
    37 -> [6, 28, 54, 80, 106, 132, 158]
    38 -> [6, 32, 58, 84, 110, 136, 162]
    39 -> [6, 26, 54, 82, 110, 138, 166]
    40 -> [6, 30, 58, 86, 114, 142, 170]
    _ -> []

-- | Check if a QR version has alignment patterns.
-- |
-- | Version 1 has no alignment patterns; all other versions do.
hasAlignmentPatterns :: QRVersion -> Boolean
hasAlignmentPatterns version =
  not (Array.null (alignmentPatternPositions version))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // format/version areas
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reserve areas for format information (15 bits, placed twice).
reserveFormatAreas :: QRMatrix -> QRMatrix
reserveFormatAreas matrix =
  let
    size = matrixSize matrix
    -- Format info is placed:
    -- 1. Around top-left finder (row 8, cols 0-8; col 8, rows 0-8)
    -- 2. Below top-right finder and right of bottom-left finder
    m1 = reserveTopLeftFormat matrix
    m2 = reserveOtherFormat size m1
  in
    m2
  where
    reserveTopLeftFormat :: QRMatrix -> QRMatrix
    reserveTopLeftFormat m =
      let
        -- Row 8, cols 0-8 (skip col 6 - timing)
        m1 = foldl (\acc c -> 
          if c /= 6 then setModule 8 c Reserved acc else acc
        ) m (0 .. 8)
        -- Col 8, rows 0-8 (skip row 6 - timing)
        m2 = foldl (\acc r ->
          if r /= 6 then setModule r 8 Reserved acc else acc
        ) m1 (0 .. 8)
      in
        m2
    
    reserveOtherFormat :: Int -> QRMatrix -> QRMatrix
    reserveOtherFormat size m =
      let
        -- Below top-right: col (size-8) to (size-1), row 8
        m1 = foldl (\acc c -> setModule 8 c Reserved acc) m ((size - 8) .. (size - 1))
        -- Right of bottom-left: row (size-7) to (size-1), col 8
        m2 = foldl (\acc r -> setModule r 8 Reserved acc) m1 ((size - 7) .. (size - 1))
      in
        m2

-- | Reserve areas for version information (version 7+).
-- |
-- | Version info is 18 bits, placed:
-- | 1. Below top-right finder (rows 0-5, cols size-11 to size-9)
-- | 2. Right of bottom-left finder (rows size-11 to size-9, cols 0-5)
reserveVersionAreas :: QRVersion -> QRMatrix -> QRMatrix
reserveVersionAreas version matrix =
  let v = versionToInt version
  in if v < 7 then matrix
     else reserveVersionBlocks matrix
  where
    reserveVersionBlocks :: QRMatrix -> QRMatrix
    reserveVersionBlocks m =
      let
        size = matrixSize m
        -- Block 1: rows 0-5, cols (size-11) to (size-9)
        m1 = foldl (\acc r ->
          foldl (\acc' c -> setModule r c Reserved acc') acc ((size - 11) .. (size - 9))
        ) m (0 .. 5)
        -- Block 2: rows (size-11) to (size-9), cols 0-5
        m2 = foldl (\acc r ->
          foldl (\acc' c -> setModule r c Reserved acc') acc (0 .. 5)
        ) m1 ((size - 11) .. (size - 9))
      in
        m2
