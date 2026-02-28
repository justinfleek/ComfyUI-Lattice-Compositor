-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // element // qrcode // matrix // data
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Code Data Placement — Zigzag pattern for data modules.
-- |
-- | ## Data Placement Algorithm
-- |
-- | Data bits are placed in a zigzag pattern:
-- |
-- | 1. Start from bottom-right corner
-- | 2. Move upward in 2-column strips
-- | 3. Alternate direction (up/down) for each strip
-- | 4. Skip column 6 (timing pattern)
-- | 5. Skip all function pattern positions
-- |
-- | ## Module Ordering
-- |
-- | Within each 2-column strip, process right column then left column
-- | for each row in the current direction.

module Hydrogen.Element.Compound.QRCode.Matrix.Data
  ( getDataModulePositions
  , placeDataBits
  , collectDataPositions
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( map
  , (/=)
  , (==)
  , (+)
  , (-)
  , (*)
  , (>)
  , (<>)
  , (&&)
  )

import Data.Array as Array
import Data.Array (foldl, filter, reverse, index, snoc, (..))
import Data.EuclideanRing (div, mod)
import Data.Maybe (fromMaybe)

import Hydrogen.Element.Compound.QRCode.Types
  ( QRMatrix
  , Module(Dark, Light, Reserved)
  , ModuleType(DataModule)
  , matrixSize
  , getModule
  , setModule
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // position generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get positions for data modules in zigzag order.
-- |
-- | Data is placed in a zigzag pattern starting from bottom-right,
-- | moving upward in 2-column strips, alternating direction.
getDataModulePositions :: QRMatrix -> Array { row :: Int, col :: Int }
getDataModulePositions matrix =
  let
    size = matrixSize matrix
    -- Start from right side, moving left in 2-column strips
    columns = reverse (filter (\c -> c /= 6) (map (\i -> size - 1 - i * 2) (0 .. (div size 2))))
  in
    Array.concatMap (getStripPositions size matrix) columns
  where
    getStripPositions :: Int -> QRMatrix -> Int -> Array { row :: Int, col :: Int }
    getStripPositions size m startCol =
      let
        -- Determine direction: odd strip index goes up, even goes down
        stripIndex = div (size - 1 - startCol) 2
        goingUp = mod stripIndex 2 == 0
        rows = if goingUp then reverse (0 .. (size - 1)) else (0 .. (size - 1))
      in
        Array.concatMap (\row -> getRowPositions m row startCol) rows
    
    getRowPositions :: QRMatrix -> Int -> Int -> Array { row :: Int, col :: Int }
    getRowPositions m row col =
      let
        -- Check right column then left column
        pos1 = { row, col }
        pos2 = { row, col: col - 1 }
        valid1 = isDataPosition m pos1.row pos1.col
        valid2 = col > 0 && isDataPosition m pos2.row pos2.col
      in
        (if valid1 then [pos1] else []) <> (if valid2 then [pos2] else [])
    
    isDataPosition :: QRMatrix -> Int -> Int -> Boolean
    isDataPosition m row col =
      case getModule row col m of
        Reserved -> true  -- Available for data
        _ -> false        -- Already occupied

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // data placement
-- ═════════════════════════════════════════════════════════════════════════════

-- | Place data bits into the matrix.
-- |
-- | Takes array of bits (0 or 1) and places them in zigzag order.
placeDataBits :: Array Int -> QRMatrix -> QRMatrix
placeDataBits bits matrix =
  let
    positions = getDataModulePositions matrix
  in
    placeBitsAtPositions bits positions matrix
  where
    placeBitsAtPositions :: Array Int -> Array { row :: Int, col :: Int } -> QRMatrix -> QRMatrix
    placeBitsAtPositions dataBits ps m =
      let
        result = foldl (placeOne dataBits) { matrix: m, bitIndex: 0 } ps
      in
        result.matrix
    
    placeOne :: Array Int -> { matrix :: QRMatrix, bitIndex :: Int } -> { row :: Int, col :: Int } -> { matrix :: QRMatrix, bitIndex :: Int }
    placeOne dataBits state pos =
      let
        bit = fromMaybe 0 (index dataBits state.bitIndex)
        modVal = if bit /= 0 then Dark DataModule else Light DataModule
        newMatrix = setModule pos.row pos.col modVal state.matrix
      in
        { matrix: newMatrix, bitIndex: state.bitIndex + 1 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // position collection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Collect data module positions incrementally using snoc.
-- |
-- | Alternative to getDataModulePositions that builds the array
-- | using snoc for incremental accumulation. Useful for streaming
-- | position collection.
collectDataPositions :: QRMatrix -> Array { row :: Int, col :: Int }
collectDataPositions matrix =
  let
    size = matrixSize matrix
    columns = reverse (filter (\c -> c /= 6) (map (\i -> size - 1 - i * 2) (0 .. (div size 2))))
  in
    foldl (collectFromStrip size matrix) [] columns
  where
    collectFromStrip :: Int -> QRMatrix -> Array { row :: Int, col :: Int } -> Int -> Array { row :: Int, col :: Int }
    collectFromStrip size m acc startCol =
      let
        stripIndex = div (size - 1 - startCol) 2
        goingUp = mod stripIndex 2 == 0
        rows = if goingUp then reverse (0 .. (size - 1)) else (0 .. (size - 1))
      in
        foldl (collectFromRow m startCol) acc rows
    
    collectFromRow :: QRMatrix -> Int -> Array { row :: Int, col :: Int } -> Int -> Array { row :: Int, col :: Int }
    collectFromRow m col acc row =
      let
        pos1 = { row, col }
        pos2 = { row, col: col - 1 }
        acc1 = if isDataPos m pos1.row pos1.col then snoc acc pos1 else acc
        acc2 = if col > 0 && isDataPos m pos2.row pos2.col then snoc acc1 pos2 else acc1
      in
        acc2
    
    isDataPos :: QRMatrix -> Int -> Int -> Boolean
    isDataPos m row col =
      case getModule row col m of
        Reserved -> true
        _ -> false
