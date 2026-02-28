-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // color // channel
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Channel - a single RGB color channel.
-- |
-- | An 8-bit unsigned value from 0 to 255:
-- | - **0**: No contribution from this channel
-- | - **128**: Half intensity
-- | - **255**: Full intensity
-- |
-- | RGB colors are composed of three channels: red, green, and blue.
-- | Each channel contributes light to the final perceived color.

module Hydrogen.Schema.Color.Channel
  ( Channel
  , channel
  , unsafeChannel
  , unwrap
  , scale
  , invert
  , add
  , blend
  , bounds
  , toNumber
  , toUnitInterval
  , fromUnitInterval
  ) where

import Prelude (class Eq, class Ord, class Show, show, (+), (-), (*), (/))

import Data.Int (round, toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // channel
-- ═════════════════════════════════════════════════════════════════════════════

-- | RGB channel value (0-255)
-- |
-- | Represents the intensity of a single color component (red, green, or blue)
-- | in the standard 8-bit per channel color model.
newtype Channel = Channel Int

derive instance eqChannel :: Eq Channel
derive instance ordChannel :: Ord Channel

instance showChannel :: Show Channel where
  show (Channel c) = show c

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a channel, clamping to 0-255
channel :: Int -> Channel
channel n = Channel (Bounded.clampInt 0 255 n)

-- | Create a channel without clamping
-- |
-- | Use only when you know the value is valid.
unsafeChannel :: Int -> Channel
unsafeChannel = Channel

-- | Create a channel from unit interval (0.0-1.0)
fromUnitInterval :: Number -> Channel
fromUnitInterval n = channel (Int.round (Bounded.clampNumber 0.0 1.0 n * 255.0))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale channel by a factor
scale :: Number -> Channel -> Channel
scale factor (Channel c) = 
  channel (Int.round (Int.toNumber c * factor))

-- | Invert channel (255 - value)
invert :: Channel -> Channel
invert (Channel c) = Channel (255 - c)

-- | Add two channels (clamped)
add :: Channel -> Channel -> Channel
add (Channel a) (Channel b) = channel (a + b)

-- | Blend two channels with weight (0.0 = all first, 1.0 = all second)
blend :: Number -> Channel -> Channel -> Channel
blend weight (Channel a) (Channel b) =
  let 
    w = Bounded.clampNumber 0.0 1.0 weight
    result = Int.toNumber a * (1.0 - w) + Int.toNumber b * w
  in channel (Int.round result)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Int value
unwrap :: Channel -> Int
unwrap (Channel c) = c

-- | Convert to Number for calculations
toNumber :: Channel -> Number
toNumber (Channel c) = Int.toNumber c

-- | Convert to unit interval (0.0-1.0)
toUnitInterval :: Channel -> Number
toUnitInterval (Channel c) = Int.toNumber c / 255.0

-- | Bounds documentation for this type
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 0 255 "channel" "8-bit color channel intensity"
