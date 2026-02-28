-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // element // qrcode // matrix // mask
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Code Mask Patterns — Data module masking for optimal readability.
-- |
-- | ## Purpose
-- |
-- | QR codes use one of 8 mask patterns to break up large areas of
-- | same-colored modules, improving scanner reliability. Only data
-- | modules are masked; function patterns (finders, timing, etc.) are not.
-- |
-- | ## Mask Pattern Formulas
-- |
-- | Each mask is a function of (row, col) that returns whether to flip:
-- |
-- | - Mask 0: (row + col) mod 2 == 0
-- | - Mask 1: row mod 2 == 0
-- | - Mask 2: col mod 3 == 0
-- | - Mask 3: (row + col) mod 3 == 0
-- | - Mask 4: (floor(row/2) + floor(col/3)) mod 2 == 0
-- | - Mask 5: (row*col) mod 2 + (row*col) mod 3 == 0
-- | - Mask 6: ((row*col) mod 2 + (row*col) mod 3) mod 2 == 0
-- | - Mask 7: ((row+col) mod 2 + (row*col) mod 3) mod 2 == 0
-- |
-- | ## Selection
-- |
-- | The best mask is selected by evaluating penalty scores for all 8
-- | patterns and choosing the one with minimum penalty.

module Hydrogen.Element.Compound.QRCode.Matrix.Mask
  ( MaskPattern(Mask0, Mask1, Mask2, Mask3, Mask4, Mask5, Mask6, Mask7)
  , maskPatternIndex
  , allMaskPatterns
  , shouldMaskModule
  , applyMask
  , selectBestMask
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , map
  , otherwise
  , (==)
  , (+)
  , (-)
  , (*)
  , (<)
  )

import Data.Array (foldl, head, (..))
import Data.EuclideanRing (div, mod)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)

import Hydrogen.Element.Compound.QRCode.Types
  ( QRMatrix
  , Module(Dark, Light)
  , ModuleType(DataModule)
  , matrixSize
  , getModule
  , setModule
  )

import Hydrogen.Element.Compound.QRCode.Matrix.Penalty (calculatePenalty)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // mask pattern type
-- ═════════════════════════════════════════════════════════════════════════════

-- | The 8 mask patterns defined in QR specification.
-- |
-- | Each pattern determines whether to flip a data module based on position.
data MaskPattern
  = Mask0  -- ^ (row + col) mod 2 == 0
  | Mask1  -- ^ row mod 2 == 0
  | Mask2  -- ^ col mod 3 == 0
  | Mask3  -- ^ (row + col) mod 3 == 0
  | Mask4  -- ^ (row/2 + col/3) mod 2 == 0
  | Mask5  -- ^ (row*col) mod 2 + (row*col) mod 3 == 0
  | Mask6  -- ^ ((row*col) mod 2 + (row*col) mod 3) mod 2 == 0
  | Mask7  -- ^ ((row+col) mod 2 + (row*col) mod 3) mod 2 == 0

derive instance eqMaskPattern :: Eq MaskPattern
derive instance ordMaskPattern :: Ord MaskPattern

instance showMaskPattern :: Show MaskPattern where
  show Mask0 = "Mask0"
  show Mask1 = "Mask1"
  show Mask2 = "Mask2"
  show Mask3 = "Mask3"
  show Mask4 = "Mask4"
  show Mask5 = "Mask5"
  show Mask6 = "Mask6"
  show Mask7 = "Mask7"

-- | Get mask pattern index (0-7)
maskPatternIndex :: MaskPattern -> Int
maskPatternIndex = case _ of
  Mask0 -> 0
  Mask1 -> 1
  Mask2 -> 2
  Mask3 -> 3
  Mask4 -> 4
  Mask5 -> 5
  Mask6 -> 6
  Mask7 -> 7

-- | All mask patterns
allMaskPatterns :: Array MaskPattern
allMaskPatterns = [Mask0, Mask1, Mask2, Mask3, Mask4, Mask5, Mask6, Mask7]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // mask evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a module at (row, col) should be masked.
-- |
-- | Returns true if the mask function evaluates to true for this position.
shouldMaskModule :: MaskPattern -> Int -> Int -> Boolean
shouldMaskModule pattern row col = case pattern of
  Mask0 -> mod (row + col) 2 == 0
  Mask1 -> mod row 2 == 0
  Mask2 -> mod col 3 == 0
  Mask3 -> mod (row + col) 3 == 0
  Mask4 -> mod (div row 2 + div col 3) 2 == 0
  Mask5 -> mod (row * col) 2 + mod (row * col) 3 == 0
  Mask6 -> mod (mod (row * col) 2 + mod (row * col) 3) 2 == 0
  Mask7 -> mod (mod (row + col) 2 + mod (row * col) 3) 2 == 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // mask application
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply a mask pattern to data modules only.
-- |
-- | Finder, timing, alignment, and format modules are NOT masked.
applyMask :: MaskPattern -> QRMatrix -> QRMatrix
applyMask pattern matrix =
  let
    size = matrixSize matrix
  in
    foldl (applyMaskToRow pattern size) matrix (0 .. (size - 1))
  where
    applyMaskToRow :: MaskPattern -> Int -> QRMatrix -> Int -> QRMatrix
    applyMaskToRow p sz m row =
      foldl (applyMaskToCell p row) m (0 .. (sz - 1))
    
    applyMaskToCell :: MaskPattern -> Int -> QRMatrix -> Int -> QRMatrix
    applyMaskToCell p row m col =
      let
        modVal = getModule row col m
      in
        case modVal of
          Dark DataModule ->
            if shouldMaskModule p row col
              then setModule row col (Light DataModule) m
              else m
          Light DataModule ->
            if shouldMaskModule p row col
              then setModule row col (Dark DataModule) m
              else m
          _ -> m  -- Don't mask non-data modules

-- | Select best mask by minimum penalty score.
selectBestMask :: QRMatrix -> { mask :: MaskPattern, score :: Int }
selectBestMask matrix =
  let
    results = map (\p -> 
      let masked = applyMask p matrix
          score = calculatePenalty masked
      in { mask: p, score }
    ) allMaskPatterns
  in
    fromMaybe { mask: Mask0, score: 0 } (findMinimum results)
  where
    findMinimum :: Array { mask :: MaskPattern, score :: Int } -> Maybe { mask :: MaskPattern, score :: Int }
    findMinimum arr = case head arr of
      Nothing -> Nothing
      Just first -> Just (foldl (\best r -> if r.score < best.score then r else best) first arr)
