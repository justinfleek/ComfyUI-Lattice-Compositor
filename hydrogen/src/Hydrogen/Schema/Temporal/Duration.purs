-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // temporal // duration
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Duration — Molecule for time durations with unit semantics.
-- |
-- | Represents a span of time, independent of when it starts.
-- | Used for animation durations, delays, timeouts, and temporal intervals.
-- |
-- | ## Design Philosophy
-- |
-- | Duration is unit-agnostic internally (stored as milliseconds) but provides
-- | smart constructors for different units. This ensures:
-- | - No unit confusion in calculations
-- | - Easy conversion between units
-- | - Type-safe duration arithmetic

module Hydrogen.Schema.Temporal.Duration
  ( Duration
  -- * Constructors
  , fromNanoseconds
  , fromMicroseconds
  , fromMilliseconds
  , fromSeconds
  , fromMinutes
  , fromHours
  , fromFrames
  
  -- * Aliases (short names)
  , ns
  , us
  , ms
  , sec
  , min
  , hrs
  
  -- * Accessors
  , toNanoseconds
  , toMicroseconds
  , toMilliseconds
  , toSeconds
  , toMinutes
  , toHours
  , toFrames
  
  -- * Operations
  , add
  , subtract
  , scale
  , isZero
  , isPositive
  
  -- * CSS Export
  , toLegacyCss
  
  -- * Common Durations
  , zero
  , instant
  , veryFast
  , fast
  , normal
  , slow
  , verySlow
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (<)
  , (>)
  , (<=)
  , (==)
  )

import Data.Int (floor, toNumber) as Int
import Hydrogen.Schema.Temporal.FPS (FPS, unwrap) as FPS

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // duration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Duration stored internally as milliseconds
-- |
-- | Non-negative by construction. Represents a time span.
newtype Duration = Duration Number

derive instance eqDuration :: Eq Duration
derive instance ordDuration :: Ord Duration

instance showDuration :: Show Duration where
  show (Duration ms') = "(Duration " <> show ms' <> "ms)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create Duration from nanoseconds
fromNanoseconds :: Number -> Duration
fromNanoseconds n
  | n < 0.0 = Duration 0.0
  | otherwise = Duration (n / 1000000.0)

-- | Create Duration from microseconds
fromMicroseconds :: Number -> Duration
fromMicroseconds u
  | u < 0.0 = Duration 0.0
  | otherwise = Duration (u / 1000.0)

-- | Create Duration from milliseconds
fromMilliseconds :: Number -> Duration
fromMilliseconds m
  | m < 0.0 = Duration 0.0
  | otherwise = Duration m

-- | Create Duration from seconds
fromSeconds :: Number -> Duration
fromSeconds s
  | s < 0.0 = Duration 0.0
  | otherwise = Duration (s * 1000.0)

-- | Create Duration from minutes
fromMinutes :: Number -> Duration
fromMinutes m
  | m < 0.0 = Duration 0.0
  | otherwise = Duration (m * 60000.0)

-- | Create Duration from hours
fromHours :: Number -> Duration
fromHours h
  | h < 0.0 = Duration 0.0
  | otherwise = Duration (h * 3600000.0)

-- | Create Duration from frame count at given FPS
fromFrames :: FPS.FPS -> Int -> Duration
fromFrames fps f
  | f < 0 = Duration 0.0
  | otherwise = Duration (Int.toNumber f * 1000.0 / FPS.unwrap fps)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // aliases
-- ═════════════════════════════════════════════════════════════════════════════

-- | Short alias for nanoseconds
ns :: Number -> Duration
ns = fromNanoseconds

-- | Short alias for microseconds
us :: Number -> Duration
us = fromMicroseconds

-- | Short alias for milliseconds
ms :: Number -> Duration
ms = fromMilliseconds

-- | Short alias for seconds
sec :: Number -> Duration
sec = fromSeconds

-- | Short alias for minutes
min :: Number -> Duration
min = fromMinutes

-- | Short alias for hours
hrs :: Number -> Duration
hrs = fromHours

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to nanoseconds
toNanoseconds :: Duration -> Number
toNanoseconds (Duration ms') = ms' * 1000000.0

-- | Convert to microseconds
toMicroseconds :: Duration -> Number
toMicroseconds (Duration ms') = ms' * 1000.0

-- | Convert to milliseconds
toMilliseconds :: Duration -> Number
toMilliseconds (Duration ms') = ms'

-- | Convert to seconds
toSeconds :: Duration -> Number
toSeconds (Duration ms') = ms' / 1000.0

-- | Convert to minutes
toMinutes :: Duration -> Number
toMinutes (Duration ms') = ms' / 60000.0

-- | Convert to hours
toHours :: Duration -> Number
toHours (Duration ms') = ms' / 3600000.0

-- | Convert to frames at given FPS (truncates)
toFrames :: FPS.FPS -> Duration -> Int
toFrames fps (Duration ms') = Int.floor (ms' * FPS.unwrap fps / 1000.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add two durations
add :: Duration -> Duration -> Duration
add (Duration a) (Duration b) = Duration (a + b)

-- | Subtract durations (clamps to zero)
subtract :: Duration -> Duration -> Duration
subtract (Duration a) (Duration b) =
  let result = a - b
  in if result < 0.0 then Duration 0.0 else Duration result

-- | Scale a duration by a factor
scale :: Number -> Duration -> Duration
scale factor (Duration ms')
  | factor < 0.0 = Duration 0.0
  | otherwise = Duration (ms' * factor)

-- | Check if duration is zero
isZero :: Duration -> Boolean
isZero (Duration ms') = ms' == 0.0

-- | Check if duration is positive (non-zero)
isPositive :: Duration -> Boolean
isPositive (Duration ms') = ms' > 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css export
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format for CSS for legacy system interop.
-- |
-- | **NOTE:** Hydrogen renders via WebGPU, NOT CSS. This function exists only
-- | for exporting to legacy systems that require CSS format.
-- |
-- | Returns milliseconds for short durations, seconds for longer:
-- | - < 1000ms: "250ms"
-- | - >= 1000ms: "1.5s"
toLegacyCss :: Duration -> String
toLegacyCss (Duration ms')
  | ms' < 1000.0 = show ms' <> "ms"
  | otherwise = show (ms' / 1000.0) <> "s"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // common durations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Zero duration
zero :: Duration
zero = Duration 0.0

-- | Instant: 0ms (alias for zero, semantic difference)
instant :: Duration
instant = Duration 0.0

-- | Very fast: 100ms (micro-interactions)
veryFast :: Duration
veryFast = Duration 100.0

-- | Fast: 200ms (button feedback, toggles)
fast :: Duration
fast = Duration 200.0

-- | Normal: 300ms (standard transitions)
normal :: Duration
normal = Duration 300.0

-- | Slow: 500ms (emphasis, important changes)
slow :: Duration
slow = Duration 500.0

-- | Very slow: 1000ms (dramatic reveals)
verySlow :: Duration
verySlow = Duration 1000.0
