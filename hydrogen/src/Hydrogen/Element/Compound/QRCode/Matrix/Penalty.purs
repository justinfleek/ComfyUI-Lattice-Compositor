-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // element // qrcode // matrix // penalty
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Code Penalty Calculation — Evaluate mask quality.
-- |
-- | ## Penalty Rules
-- |
-- | QR codes use four penalty rules to evaluate mask pattern quality:
-- |
-- | 1. **Rule 1**: Consecutive same-color modules (horizontal/vertical)
-- |    - 5+ consecutive = (count - 2) penalty
-- |
-- | 2. **Rule 2**: 2×2 blocks of same color
-- |    - Each block = 3 penalty
-- |
-- | 3. **Rule 3**: Finder-like patterns
-- |    - Pattern 10111010000 or reverse = 40 penalty each
-- |
-- | 4. **Rule 4**: Dark/light ratio deviation from 50%
-- |    - Every 5% deviation = 10 penalty
-- |
-- | The mask with minimum total penalty is selected.

module Hydrogen.Element.Compound.QRCode.Matrix.Penalty
  ( calculatePenalty
  , penaltyRule1
  , penaltyRule2
  , penaltyRule3
  , penaltyRule4
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( map
  , otherwise
  , (==)
  , (+)
  , (-)
  , (*)
  , (>=)
  , (<)
  , (&&)
  , (||)
  )

import Data.Array (length, index, foldl, (..))
import Data.EuclideanRing (div, mod)
import Data.Maybe (fromMaybe)
import Data.Ord (abs)

import Hydrogen.Element.Compound.QRCode.Types
  ( QRMatrix
  , Module(Dark, Light)
  , matrixSize
  , getModule
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // penalty calculation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate total penalty score for a matrix.
calculatePenalty :: QRMatrix -> Int
calculatePenalty matrix =
  penaltyRule1 matrix +
  penaltyRule2 matrix +
  penaltyRule3 matrix +
  penaltyRule4 matrix

-- | Rule 1: Consecutive modules of same color.
-- |
-- | 5+ consecutive same-color modules = (count - 2) penalty.
penaltyRule1 :: QRMatrix -> Int
penaltyRule1 matrix =
  let
    size = matrixSize matrix
    -- Check rows
    rowPenalty = foldl (\acc r -> acc + checkLine (getRow r matrix)) 0 (0 .. (size - 1))
    -- Check columns
    colPenalty = foldl (\acc c -> acc + checkLine (getCol c matrix)) 0 (0 .. (size - 1))
  in
    rowPenalty + colPenalty
  where
    getRow :: Int -> QRMatrix -> Array Boolean
    getRow row m =
      let sz = matrixSize m
      in map (\c -> isDarkModule (getModule row c m)) (0 .. (sz - 1))
    
    getCol :: Int -> QRMatrix -> Array Boolean
    getCol col m =
      let sz = matrixSize m
      in map (\r -> isDarkModule (getModule r col m)) (0 .. (sz - 1))
    
    isDarkModule :: Module -> Boolean
    isDarkModule (Dark _) = true
    isDarkModule _ = false
    
    checkLine :: Array Boolean -> Int
    checkLine line =
      let result = foldl countRuns { count: 0, current: false, runLength: 0, penalty: 0 } line
      in result.penalty + (if result.runLength >= 5 then result.runLength - 2 else 0)
    
    countRuns :: { count :: Int, current :: Boolean, runLength :: Int, penalty :: Int } -> Boolean -> { count :: Int, current :: Boolean, runLength :: Int, penalty :: Int }
    countRuns state isDark =
      if state.count == 0 then
        { count: 1, current: isDark, runLength: 1, penalty: 0 }
      else if isDark == state.current then
        { count: state.count + 1, current: isDark, runLength: state.runLength + 1, penalty: state.penalty }
      else
        let addPenalty = if state.runLength >= 5 then state.runLength - 2 else 0
        in { count: state.count + 1, current: isDark, runLength: 1, penalty: state.penalty + addPenalty }

-- | Rule 2: 2x2 blocks of same color.
-- |
-- | Each 2x2 block of same color = 3 penalty.
penaltyRule2 :: QRMatrix -> Int
penaltyRule2 matrix =
  let
    size = matrixSize matrix
  in
    foldl (\acc r -> acc + checkRow r matrix size) 0 (0 .. (size - 2))
  where
    checkRow :: Int -> QRMatrix -> Int -> Int
    checkRow row m size =
      foldl (\acc c -> acc + checkBlock row c m) 0 (0 .. (size - 2))
    
    checkBlock :: Int -> Int -> QRMatrix -> Int
    checkBlock row col m =
      let
        tl = isDark (getModule row col m)
        tr = isDark (getModule row (col + 1) m)
        bl = isDark (getModule (row + 1) col m)
        br = isDark (getModule (row + 1) (col + 1) m)
      in
        if tl == tr && tl == bl && tl == br then 3 else 0
    
    isDark :: Module -> Boolean
    isDark (Dark _) = true
    isDark _ = false

-- | Rule 3: Finder-like patterns.
-- |
-- | Pattern 10111010000 or 00001011101 = 40 penalty each.
penaltyRule3 :: QRMatrix -> Int
penaltyRule3 matrix =
  let
    size = matrixSize matrix
    -- Check rows
    rowPenalty = foldl (\acc r -> acc + checkLineForFinderPattern (getRow r matrix)) 0 (0 .. (size - 1))
    -- Check columns
    colPenalty = foldl (\acc c -> acc + checkLineForFinderPattern (getCol c matrix)) 0 (0 .. (size - 1))
  in
    rowPenalty + colPenalty
  where
    getRow :: Int -> QRMatrix -> Array Int
    getRow row m =
      let sz = matrixSize m
      in map (\c -> if isDark (getModule row c m) then 1 else 0) (0 .. (sz - 1))
    
    getCol :: Int -> QRMatrix -> Array Int
    getCol col m =
      let sz = matrixSize m
      in map (\r -> if isDark (getModule r col m) then 1 else 0) (0 .. (sz - 1))
    
    isDark :: Module -> Boolean
    isDark (Dark _) = true
    isDark _ = false
    
    -- Pattern: 1,0,1,1,1,0,1,0,0,0,0 or 0,0,0,0,1,0,1,1,1,0,1
    pattern1 :: Array Int
    pattern1 = [1,0,1,1,1,0,1,0,0,0,0]
    
    pattern2 :: Array Int
    pattern2 = [0,0,0,0,1,0,1,1,1,0,1]
    
    checkLineForFinderPattern :: Array Int -> Int
    checkLineForFinderPattern line =
      let len = length line
      in if len < 11 then 0
         else foldl (\acc i -> acc + checkAt i line) 0 (0 .. (len - 11))
    
    checkAt :: Int -> Array Int -> Int
    checkAt startIdx line =
      let
        slice = map (\i -> fromMaybe 0 (index line (startIdx + i))) (0 .. 10)
        matches1 = slice == pattern1
        matches2 = slice == pattern2
      in
        if matches1 || matches2 then 40 else 0

-- | Rule 4: Dark/light ratio deviation.
-- |
-- | For every 5% deviation from 50%, add 10 penalty.
penaltyRule4 :: QRMatrix -> Int
penaltyRule4 matrix =
  let
    size = matrixSize matrix
    total = size * size
    darkCount = countDarkModules matrix
    percent = div (darkCount * 100) total
    deviation = abs (percent - 50)
    -- Penalty: (deviation / 5) * 10
    penaltyUnits = div deviation 5
  in
    penaltyUnits * 10
  where
    countDarkModules :: QRMatrix -> Int
    countDarkModules m =
      let sz = matrixSize m
      in foldl (\acc r -> acc + countRowDark r m sz) 0 (0 .. (sz - 1))
    
    countRowDark :: Int -> QRMatrix -> Int -> Int
    countRowDark row m sz =
      foldl (\acc c -> if isDark (getModule row c m) then acc + 1 else acc) 0 (0 .. (sz - 1))
    
    isDark :: Module -> Boolean
    isDark (Dark _) = true
    isDark _ = false
