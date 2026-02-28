-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // color // channel16
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Channel16 — 16-bit color channel atom.
-- |
-- | **HIGH BIT-DEPTH COLOR:**
-- | 16-bit color channels provide 65536 levels per channel vs 256 for 8-bit.
-- | This extra precision is essential for:
-- | - HDR imaging (high dynamic range)
-- | - Professional color grading
-- | - Linear light calculations
-- | - Avoiding banding in gradients
-- |
-- | **When to use 16-bit:**
-- | - Medical imaging
-- | - Scientific visualization
-- | - Film/VFX production
-- | - Any workflow requiring precision

module Hydrogen.Schema.Color.Channel16
  ( -- * Type
    Channel16
  
  -- * Constructors
  , channel16
  , channel16Safe
  
  -- * Unwrapper
  , unwrap
  
  -- * Operations
  , add
  , subtract
  , blend
  , invert
  , scale
  
  -- * Comparison
  , isZero
  , isMax
  , isEqual
  , isNotEqual
  , isLessThan
  , isGreaterThan
  , inRange
  , isAtBoundary
  
  -- * Conversions
  , toUnitInterval
  , fromUnitInterval
  , toChannel8
  , fromChannel8
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (&&)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , (==)
  , (/=)
  , (||)
  , (<>)
  )

import Data.Int (round, toNumber)
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Color.Channel (Channel, channel, unwrap) as Ch

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // channel16
-- ═════════════════════════════════════════════════════════════════════════════

-- | 16-bit color channel (0-65535)
-- |
-- | A single channel in a 16-bit per channel color space.
-- | 0 = minimum intensity, 65535 = maximum intensity.
newtype Channel16 = Channel16 Int

derive instance eqChannel16 :: Eq Channel16
derive instance ordChannel16 :: Ord Channel16

instance showChannel16 :: Show Channel16 where
  show (Channel16 n) = "Channel16 " <> show n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a 16-bit channel value (clamped to 0-65535)
-- |
-- | ```purescript
-- | channel16 32768   -- Middle gray
-- | channel16 0       -- Black
-- | channel16 65535   -- Maximum intensity
-- | channel16 100000  -- Clamped to 65535
-- | ```
channel16 :: Int -> Channel16
channel16 n = Channel16 (Bounded.clampInt 0 65535 n)

-- | Create a 16-bit channel value with validation
-- |
-- | Returns Nothing if value is out of range.
channel16Safe :: Int -> Maybe Channel16
channel16Safe n
  | n >= 0 && n <= 65535 = Just (Channel16 n)
  | otherwise = Nothing

-- | Extract raw value
unwrap :: Channel16 -> Int
unwrap (Channel16 n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add two channels (clamped at 65535)
add :: Channel16 -> Channel16 -> Channel16
add (Channel16 a) (Channel16 b) = channel16 (a + b)

-- | Blend two channels with a weight (0.0 = first, 1.0 = second)
blend :: Number -> Channel16 -> Channel16 -> Channel16
blend weight (Channel16 a) (Channel16 b) =
  let w = Bounded.clampNumber 0.0 1.0 weight
      result = toNumber a * (1.0 - w) + toNumber b * w
  in channel16 (round result)

-- | Invert the channel (65535 - value)
invert :: Channel16 -> Channel16
invert (Channel16 n) = Channel16 (65535 - n)

-- | Scale the channel by a factor
scale :: Number -> Channel16 -> Channel16
scale factor (Channel16 n) =
  channel16 (round (toNumber n * factor))

-- | Subtract two channels (clamped at 0)
subtract :: Channel16 -> Channel16 -> Channel16
subtract (Channel16 a) (Channel16 b) = channel16 (a - b)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if channel is zero (minimum intensity)
isZero :: Channel16 -> Boolean
isZero (Channel16 n) = n == 0

-- | Check if channel is at maximum intensity
isMax :: Channel16 -> Boolean
isMax (Channel16 n) = n == 65535

-- | Check if two channels are equal
isEqual :: Channel16 -> Channel16 -> Boolean
isEqual (Channel16 a) (Channel16 b) = a == b

-- | Check if first channel is less than second
isLessThan :: Channel16 -> Channel16 -> Boolean
isLessThan (Channel16 a) (Channel16 b) = a < b

-- | Check if first channel is greater than second
isGreaterThan :: Channel16 -> Channel16 -> Boolean
isGreaterThan (Channel16 a) (Channel16 b) = a > b

-- | Check if channel is within a range (inclusive)
inRange :: Int -> Int -> Channel16 -> Boolean
inRange minVal maxVal (Channel16 n) = n >= minVal && n <= maxVal

-- | Check if channel is NOT equal to another
isNotEqual :: Channel16 -> Channel16 -> Boolean
isNotEqual (Channel16 a) (Channel16 b) = a /= b

-- | Check if channel is either zero or max (at boundary)
isAtBoundary :: Channel16 -> Boolean
isAtBoundary c = isZero c || isMax c

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to unit interval (0.0-1.0)
toUnitInterval :: Channel16 -> Number
toUnitInterval (Channel16 n) = toNumber n / 65535.0

-- | Convert from unit interval (0.0-1.0)
fromUnitInterval :: Number -> Channel16
fromUnitInterval n =
  let clamped = Bounded.clampNumber 0.0 1.0 n
  in channel16 (round (clamped * 65535.0))

-- | Convert to 8-bit channel (loses precision)
toChannel8 :: Channel16 -> Ch.Channel
toChannel8 (Channel16 n) = Ch.channel (n / 256)

-- | Convert from 8-bit channel
fromChannel8 :: Ch.Channel -> Channel16
fromChannel8 ch = channel16 (Ch.unwrap ch * 256 + Ch.unwrap ch)
