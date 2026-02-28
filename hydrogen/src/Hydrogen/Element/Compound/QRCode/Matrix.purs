-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // qrcode // matrix
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Matrix Construction — Complete matrix generation and orchestration.
-- |
-- | ## Module Structure
-- |
-- | This is the orchestrating module that re-exports from sub-modules:
-- |
-- | - **Matrix.Patterns** — Finder, timing, alignment pattern placement
-- | - **Matrix.Data** — Data bit placement in zigzag pattern
-- | - **Matrix.Mask** — Mask pattern types and application
-- | - **Matrix.Penalty** — Penalty calculation for mask selection
-- | - **Matrix.FormatVersion** — Format/version info encoding
-- |
-- | ## Complete Generation Pipeline
-- |
-- | 1. Initialize matrix for version
-- | 2. Place finder patterns and separators
-- | 3. Place timing patterns
-- | 4. Place alignment patterns (version 2+)
-- | 5. Reserve format/version areas
-- | 6. Place data in zigzag pattern
-- | 7. Select best mask by minimum penalty
-- | 8. Apply mask to data modules
-- | 9. Place format and version information

module Hydrogen.Element.Compound.QRCode.Matrix
  ( -- * Matrix Construction (from Patterns)
    module Patterns
  
  -- * Data Placement (from Data)
  , module MatrixData
  
  -- * Masking (from Mask)
  , module Mask
  
  -- * Penalty Calculation (from Penalty)
  , module Penalty
  
  -- * Format/Version Info (from FormatVersion)
  , module FormatVersion
  
  -- * Complete Matrix Generation
  , generateMatrix
  
  -- * Matrix Inspection
  , showMaskResult
  , isEmptyMatrix
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , show
  , not
  , (<>)
  , (-)
  )

import Data.Array as Array
import Data.Array (foldl, (..))

import Hydrogen.Element.Compound.QRCode.Types
  ( QRVersion
  , QRMatrix
  , ErrorCorrection
  , Module(Dark, Light)
  , ModuleType
    ( FinderModule
    , TimingModule
    , AlignmentModule
    , DataModule
    , FormatModule
    , VersionModule
    , QuietModule
    )
  , matrixSize
  , getModule
  )

-- Re-export from sub-modules (aliased for module re-export)
import Hydrogen.Element.Compound.QRCode.Matrix.Patterns as Patterns
import Hydrogen.Element.Compound.QRCode.Matrix.Data as MatrixData
import Hydrogen.Element.Compound.QRCode.Matrix.Mask as Mask
import Hydrogen.Element.Compound.QRCode.Matrix.Penalty as Penalty
import Hydrogen.Element.Compound.QRCode.Matrix.FormatVersion as FormatVersion

-- Direct imports for use in this module's functions
import Hydrogen.Element.Compound.QRCode.Matrix.Patterns
  ( initializeMatrix
  , placeFinderPatterns
  , placeSeparators
  , placeTimingPatterns
  , placeAlignmentPatterns
  , reserveFormatAreas
  , reserveVersionAreas
  )

import Hydrogen.Element.Compound.QRCode.Matrix.Data
  ( placeDataBits
  )

import Hydrogen.Element.Compound.QRCode.Matrix.Mask
  ( MaskPattern(Mask0, Mask1, Mask2, Mask3, Mask4, Mask5, Mask6, Mask7)
  , applyMask
  , selectBestMask
  )

import Hydrogen.Element.Compound.QRCode.Matrix.FormatVersion
  ( placeFormatInfo
  , placeVersionInfo
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // complete matrix generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate complete QR matrix from data bits.
-- |
-- | This is the main entry point for matrix construction.
-- |
-- | ## Pipeline
-- |
-- | 1. Initialize and place function patterns
-- | 2. Place data bits in zigzag order
-- | 3. Select best mask by minimum penalty
-- | 4. Apply mask to data modules
-- | 5. Place format and version information
generateMatrix :: QRVersion -> ErrorCorrection -> Array Int -> QRMatrix
generateMatrix version ec dataBits =
  let
    -- Step 1: Initialize and place function patterns
    m1 = initializeMatrix version
    m2 = placeFinderPatterns m1
    m3 = placeSeparators m2
    m4 = placeTimingPatterns m3
    m5 = placeAlignmentPatterns version m4
    m6 = reserveFormatAreas m5
    m7 = reserveVersionAreas version m6
    
    -- Step 2: Place data
    m8 = placeDataBits dataBits m7
    
    -- Step 3: Select best mask
    bestMask = selectBestMask m8
    
    -- Step 4: Apply mask
    m9 = applyMask bestMask.mask m8
    
    -- Step 5: Place format and version info
    m10 = placeFormatInfo ec bestMask.mask m9
    m11 = placeVersionInfo version m10
  in
    m11

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // matrix inspection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Display mask selection result as a human-readable string.
-- |
-- | Useful for debugging and logging which mask was selected.
showMaskResult :: { mask :: MaskPattern, score :: Int } -> String
showMaskResult result =
  "MaskResult { mask: " <> show result.mask <> ", score: " <> show result.score <> " }"

-- | Check if a matrix is empty (all modules Reserved).
-- |
-- | An empty matrix has no placed finder, timing, alignment,
-- | or data modules - only Reserved placeholders.
isEmptyMatrix :: QRMatrix -> Boolean
isEmptyMatrix matrix =
  let
    size = matrixSize matrix
    -- Check if any non-Reserved module exists
    hasPlacedModule = foldl (checkRow size matrix) false (0 .. (size - 1))
  in
    not hasPlacedModule
  where
    checkRow :: Int -> QRMatrix -> Boolean -> Int -> Boolean
    checkRow sz m found row =
      if found then true
      else foldl (checkCell row m) false (0 .. (sz - 1))
    
    checkCell :: Int -> QRMatrix -> Boolean -> Int -> Boolean
    checkCell row m found col =
      if found then true
      else
        let modVal = getModule row col m
        in Array.elem modVal 
          [ Dark FinderModule, Light FinderModule
          , Dark TimingModule, Light TimingModule
          , Dark AlignmentModule, Light AlignmentModule
          , Dark DataModule, Light DataModule
          , Dark FormatModule, Light FormatModule
          , Dark VersionModule, Light VersionModule
          , Dark QuietModule, Light QuietModule
          ]
