-- | Compatibility shim for the removed Math module (PureScript 0.15+).
-- | Uses direct foreign imports to avoid re-export issues.

module Math
  ( abs, acos, asin, atan, atan2, ceil, cos, exp, floor
  , log, max, min, pi, pow, round, sin, sqrt, tan
  ) where

foreign import abs :: Number -> Number
foreign import acos :: Number -> Number
foreign import asin :: Number -> Number
foreign import atan :: Number -> Number
foreign import atan2 :: Number -> Number -> Number
foreign import ceil :: Number -> Number
foreign import cos :: Number -> Number
foreign import exp :: Number -> Number
foreign import floor :: Number -> Number
foreign import log :: Number -> Number
foreign import max :: Number -> Number -> Number
foreign import min :: Number -> Number -> Number
foreign import pow :: Number -> Number -> Number
foreign import round :: Number -> Number
foreign import sin :: Number -> Number
foreign import sqrt :: Number -> Number
foreign import tan :: Number -> Number

pi :: Number
pi = 3.141592653589793
