-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // element // qrcode // types // matrix
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Matrix — 2D grid of modules.
-- |
-- | ## Storage
-- |
-- | Stored as a flat array for efficiency, with size tracking.
-- | Access is row-major: index = row * size + col
-- |
-- | ## Operations
-- |
-- | - mkMatrix: Create empty matrix
-- | - getModule: Read module at position
-- | - setModule: Write module at position
-- | - rowToArray: Get a row as array
-- | - toNestedArray: Convert to 2D array for rendering
-- |
-- | ## Dependencies
-- |
-- | - Types.Module (Module type)
-- | - Data.Array (array operations)

module Hydrogen.Element.Compound.QRCode.Types.Matrix
  ( -- * QR Matrix
    QRMatrix
  , mkMatrix
  , matrixSize
  , getModule
  , setModule
  , rowToArray
  , toNestedArray
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (*)
  , (<)
  , (>=)
  , (||)
  , otherwise
  )

import Data.Array (replicate, index, updateAt, (..))
import Data.Array (mapMaybe) as Array
import Data.Maybe (Maybe(Just), fromMaybe)

import Hydrogen.Element.Compound.QRCode.Types.Module (Module(Reserved))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // qr matrix
-- ═════════════════════════════════════════════════════════════════════════════

-- | QR code matrix — 2D grid of modules.
-- |
-- | Stored as a flat array for efficiency, with size tracking.
-- | Access is row-major: index = row * size + col
type QRMatrix =
  { size :: Int
  , modules :: Array Module
  }

-- | Create an empty matrix of given size (filled with Reserved)
mkMatrix :: Int -> QRMatrix
mkMatrix size =
  { size
  , modules: replicate (size * size) Reserved
  }

-- | Get matrix size (width = height)
matrixSize :: QRMatrix -> Int
matrixSize m = m.size

-- | Get module at position (row, col)
-- |
-- | Returns Reserved for out-of-bounds access.
getModule :: Int -> Int -> QRMatrix -> Module
getModule row col matrix
  | row < 0 || row >= matrix.size = Reserved
  | col < 0 || col >= matrix.size = Reserved
  | otherwise =
      let idx = row * matrix.size + col
      in fromMaybe Reserved (index matrix.modules idx)

-- | Set module at position (row, col)
-- |
-- | Returns unchanged matrix for out-of-bounds access.
setModule :: Int -> Int -> Module -> QRMatrix -> QRMatrix
setModule row col mod matrix
  | row < 0 || row >= matrix.size = matrix
  | col < 0 || col >= matrix.size = matrix
  | otherwise =
      let
        idx = row * matrix.size + col
        newModules = fromMaybe matrix.modules (updateAt idx mod matrix.modules)
      in
        matrix { modules = newModules }

-- | Get a row as an array
rowToArray :: Int -> QRMatrix -> Array Module
rowToArray row matrix
  | row < 0 || row >= matrix.size = []
  | otherwise =
      let
        startIdx = row * matrix.size
        indices = startIdx .. (startIdx + matrix.size - 1)
      in
        Array.mapMaybe (\i -> index matrix.modules i) indices

-- | Convert to nested array (for rendering/debugging)
toNestedArray :: QRMatrix -> Array (Array Module)
toNestedArray matrix =
  Array.mapMaybe (\row -> Just (rowToArray row matrix)) (0 .. (matrix.size - 1))
