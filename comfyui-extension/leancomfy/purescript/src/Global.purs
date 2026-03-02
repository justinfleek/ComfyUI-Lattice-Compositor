-- | Compatibility shim for the removed Global module (PureScript 0.15+).
-- | Re-exports functions that moved to Data.Number.

module Global
  ( infinity
  , isFinite
  , isNaN
  , readFloat
  , readInt
  ) where

import Data.Number (infinity, isFinite, isNaN) as N

infinity :: Number
infinity = N.infinity

isFinite :: Number -> Boolean
isFinite = N.isFinite

isNaN :: Number -> Boolean
isNaN = N.isNaN

foreign import readFloat :: String -> Number
foreign import readInt :: Int -> String -> Number
