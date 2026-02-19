-- | Compatibility shim for the removed Global module (PureScript 0.15+).
-- | Re-exports functions that moved to Data.Number.

module Global
  ( infinity
  , isFinite
  , isNaN
  , readFloat
  , readInt
  ) where

import Prelude
import Data.Maybe (fromMaybe)
import Data.Number (infinity, isFinite, isNaN, fromString) as N
import Data.Int as Int

infinity :: Number
infinity = N.infinity

isFinite :: Number -> Boolean
isFinite = N.isFinite

isNaN :: Number -> Boolean
isNaN = N.isNaN

-- | Parse a float from string, returns NaN on failure
readFloat :: String -> Number
readFloat s = fromMaybe N.nan (N.fromString s)
  where
    nan = 0.0 / 0.0

-- | Parse an integer in given radix from string
readInt :: Int -> String -> Number
readInt radix s = fromMaybe nan (Int.toNumber <$> Int.fromStringAs (toRadix radix) s)
  where
    nan = 0.0 / 0.0
    toRadix r
      | r == 2 = Int.binary
      | r == 8 = Int.octal
      | r == 16 = Int.hexadecimal
      | otherwise = Int.decimal
