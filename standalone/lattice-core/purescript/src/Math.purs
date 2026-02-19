-- | Compatibility shim for the removed Math module (PureScript 0.15+).
-- | Re-exports from Data.Number.

module Math
  ( abs, acos, asin, atan, atan2, ceil, cos, exp, floor
  , log, max, min, pi, pow, round, sin, sqrt, tan, trunc
  ) where

import Data.Number as N

abs :: Number -> Number
abs = N.abs

acos :: Number -> Number
acos = N.acos

asin :: Number -> Number
asin = N.asin

atan :: Number -> Number
atan = N.atan

atan2 :: Number -> Number -> Number
atan2 = N.atan2

ceil :: Number -> Number
ceil = N.ceil

cos :: Number -> Number
cos = N.cos

exp :: Number -> Number
exp = N.exp

floor :: Number -> Number
floor = N.floor

log :: Number -> Number
log = N.log

max :: Number -> Number -> Number
max = N.max

min :: Number -> Number -> Number
min = N.min

pow :: Number -> Number -> Number
pow = N.pow

round :: Number -> Number
round = N.round

sin :: Number -> Number
sin = N.sin

sqrt :: Number -> Number
sqrt = N.sqrt

tan :: Number -> Number
tan = N.tan

trunc :: Number -> Number
trunc = N.trunc

pi :: Number
pi = N.pi
