-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // dimension // temporal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Temporal units - measurements of time and duration.
-- |
-- | Used for:
-- | - Animation durations
-- | - Transition timing
-- | - Frame-based animation
-- | - Video/audio synchronization
-- | - Physics simulation timesteps
-- |
-- | ## Base Unit
-- |
-- | The base unit is **Seconds** (SI standard). All other units convert
-- | through seconds.
-- |
-- | ## Frame-Based Time
-- |
-- | Frame-based timing requires a frame rate context. A "frame" has no
-- | inherent duration - it depends on whether you're at 24fps (film),
-- | 30fps (NTSC), 60fps (games), or 120fps (high refresh displays).

module Hydrogen.Schema.Dimension.Temporal
  ( -- * Core Types
    Seconds(Seconds)
  , Milliseconds(Milliseconds)
  , Microseconds(Microseconds)
  , Nanoseconds(Nanoseconds)
  , Minutes(Minutes)
  , Hours(Hours)
  
  -- * Frame-Based Types
  , Frames(Frames)
  , FrameRate(FrameRate)
  
  -- * Type Class
  , class TemporalUnit
  , toSeconds
  , fromSeconds
  
  -- * Constructors
  , seconds
  , sec
  , milliseconds
  , ms
  , microseconds
  , us
  , nanoseconds
  , ns
  , minutes
  , min
  , hours
  , hr
  , frames
  , fps
  
  -- * Conversions
  , convertTime
  , framesToSeconds
  , secondsToFrames
  
  -- * Operations
  , addSeconds
  , subtractSeconds
  , scaleSeconds
  , negateSeconds
  , absSeconds
  
  -- * Common Frame Rates
  , fps24
  , fps25
  , fps30
  , fps48
  , fps60
  , fps120
  , fps24Drop
  , fps30Drop
  
  -- * Common Durations
  , instant
  , fast
  , normal
  , slow
  , glacial
  
  -- * Accessors
  , unwrapSeconds
  , unwrapMilliseconds
  , unwrapMicroseconds
  , unwrapNanoseconds
  , unwrapMinutes
  , unwrapHours
  , unwrapFrames
  , unwrapFps
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Ring
  , class Semiring
  , class Show
  , identity
  , negate
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (<<<)
  )

import Hydrogen.Math.Core as Math

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Seconds - SI base unit of time
newtype Seconds = Seconds Number

derive instance eqSeconds :: Eq Seconds
derive instance ordSeconds :: Ord Seconds

instance showSeconds :: Show Seconds where
  show (Seconds n) = show n <> "s"

instance semiringSeconds :: Semiring Seconds where
  add (Seconds a) (Seconds b) = Seconds (a + b)
  zero = Seconds 0.0
  mul (Seconds a) (Seconds b) = Seconds (a * b)
  one = Seconds 1.0

instance ringSeconds :: Ring Seconds where
  sub (Seconds a) (Seconds b) = Seconds (a - b)

-- | Milliseconds - 1/1000 of a second
-- | Common for UI animations (150-300ms typical)
newtype Milliseconds = Milliseconds Number

derive instance eqMilliseconds :: Eq Milliseconds
derive instance ordMilliseconds :: Ord Milliseconds

instance showMilliseconds :: Show Milliseconds where
  show (Milliseconds n) = show n <> "ms"

-- | Microseconds - 1/1,000,000 of a second
-- | Used for high-precision timing
newtype Microseconds = Microseconds Number

derive instance eqMicroseconds :: Eq Microseconds
derive instance ordMicroseconds :: Ord Microseconds

instance showMicroseconds :: Show Microseconds where
  show (Microseconds n) = show n <> "µs"

-- | Nanoseconds - 1/1,000,000,000 of a second
-- | Used for CPU-level timing
newtype Nanoseconds = Nanoseconds Number

derive instance eqNanoseconds :: Eq Nanoseconds
derive instance ordNanoseconds :: Ord Nanoseconds

instance showNanoseconds :: Show Nanoseconds where
  show (Nanoseconds n) = show n <> "ns"

-- | Minutes - 60 seconds
newtype Minutes = Minutes Number

derive instance eqMinutes :: Eq Minutes
derive instance ordMinutes :: Ord Minutes

instance showMinutes :: Show Minutes where
  show (Minutes n) = show n <> " min"

-- | Hours - 3600 seconds
newtype Hours = Hours Number

derive instance eqHours :: Eq Hours
derive instance ordHours :: Ord Hours

instance showHours :: Show Hours where
  show (Hours n) = show n <> " hr"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // frame-based types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Frames - discrete unit of animation/video
-- | Duration depends on frame rate context
newtype Frames = Frames Number

derive instance eqFrames :: Eq Frames
derive instance ordFrames :: Ord Frames

instance showFrames :: Show Frames where
  show (Frames n) = show n <> " frames"

-- | Frame rate - frames per second
-- | Required context for frame <-> second conversion
newtype FrameRate = FrameRate Number

derive instance eqFrameRate :: Eq FrameRate
derive instance ordFrameRate :: Ord FrameRate

instance showFrameRate :: Show FrameRate where
  show (FrameRate n) = show n <> " fps"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // type class
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type class for temporal units
-- | All conversions go through Seconds as the canonical representation
class TemporalUnit a where
  toSeconds :: a -> Seconds
  fromSeconds :: Seconds -> a

instance temporalUnitSeconds :: TemporalUnit Seconds where
  toSeconds = identity
  fromSeconds = identity

instance temporalUnitMilliseconds :: TemporalUnit Milliseconds where
  toSeconds (Milliseconds ms') = Seconds (ms' / 1000.0)
  fromSeconds (Seconds s) = Milliseconds (s * 1000.0)

instance temporalUnitMicroseconds :: TemporalUnit Microseconds where
  toSeconds (Microseconds us') = Seconds (us' / 1000000.0)
  fromSeconds (Seconds s) = Microseconds (s * 1000000.0)

instance temporalUnitNanoseconds :: TemporalUnit Nanoseconds where
  toSeconds (Nanoseconds ns') = Seconds (ns' / 1000000000.0)
  fromSeconds (Seconds s) = Nanoseconds (s * 1000000000.0)

instance temporalUnitMinutes :: TemporalUnit Minutes where
  toSeconds (Minutes m) = Seconds (m * 60.0)
  fromSeconds (Seconds s) = Minutes (s / 60.0)

instance temporalUnitHours :: TemporalUnit Hours where
  toSeconds (Hours h) = Seconds (h * 3600.0)
  fromSeconds (Seconds s) = Hours (s / 3600.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a Seconds value
seconds :: Number -> Seconds
seconds = Seconds

-- | Alias for seconds
sec :: Number -> Seconds
sec = Seconds

-- | Create a Milliseconds value
milliseconds :: Number -> Milliseconds
milliseconds = Milliseconds

-- | Alias for milliseconds
ms :: Number -> Milliseconds
ms = Milliseconds

-- | Create a Microseconds value
microseconds :: Number -> Microseconds
microseconds = Microseconds

-- | Alias for microseconds
us :: Number -> Microseconds
us = Microseconds

-- | Create a Nanoseconds value
nanoseconds :: Number -> Nanoseconds
nanoseconds = Nanoseconds

-- | Alias for nanoseconds
ns :: Number -> Nanoseconds
ns = Nanoseconds

-- | Create a Minutes value
minutes :: Number -> Minutes
minutes = Minutes

-- | Alias for minutes
min :: Number -> Minutes
min = Minutes

-- | Create an Hours value
hours :: Number -> Hours
hours = Hours

-- | Alias for hours
hr :: Number -> Hours
hr = Hours

-- | Create a Frames value
frames :: Number -> Frames
frames = Frames

-- | Create a FrameRate value
fps :: Number -> FrameRate
fps = FrameRate

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert between any two temporal units
convertTime :: forall a b. TemporalUnit a => TemporalUnit b => a -> b
convertTime = fromSeconds <<< toSeconds

-- | Convert frames to seconds given a frame rate
framesToSeconds :: FrameRate -> Frames -> Seconds
framesToSeconds (FrameRate rate) (Frames f) = Seconds (f / rate)

-- | Convert seconds to frames given a frame rate
secondsToFrames :: FrameRate -> Seconds -> Frames
secondsToFrames (FrameRate rate) (Seconds s) = Frames (s * rate)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add two Seconds values
addSeconds :: Seconds -> Seconds -> Seconds
addSeconds (Seconds a) (Seconds b) = Seconds (a + b)

-- | Subtract two Seconds values
subtractSeconds :: Seconds -> Seconds -> Seconds
subtractSeconds (Seconds a) (Seconds b) = Seconds (a - b)

-- | Scale a Seconds value by a dimensionless factor
scaleSeconds :: Number -> Seconds -> Seconds
scaleSeconds factor (Seconds n) = Seconds (n * factor)

-- | Negate a Seconds value
negateSeconds :: Seconds -> Seconds
negateSeconds (Seconds n) = Seconds (negate n)

-- | Absolute value of Seconds
absSeconds :: Seconds -> Seconds
absSeconds (Seconds n) = Seconds (Math.abs n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // common frame rates
-- ═════════════════════════════════════════════════════════════════════════════

-- | 24 fps - Film standard
fps24 :: FrameRate
fps24 = FrameRate 24.0

-- | 25 fps - PAL video standard
fps25 :: FrameRate
fps25 = FrameRate 25.0

-- | 30 fps - NTSC video standard (actually 30000/1001 ≈ 29.97)
fps30 :: FrameRate
fps30 = FrameRate 30.0

-- | 48 fps - High frame rate film (The Hobbit)
fps48 :: FrameRate
fps48 = FrameRate 48.0

-- | 60 fps - Common game/UI target
fps60 :: FrameRate
fps60 = FrameRate 60.0

-- | 120 fps - High refresh rate displays
fps120 :: FrameRate
fps120 = FrameRate 120.0

-- | 23.976 fps - NTSC film (24000/1001)
fps24Drop :: FrameRate
fps24Drop = FrameRate (24000.0 / 1001.0)

-- | 29.97 fps - NTSC video drop frame (30000/1001)
fps30Drop :: FrameRate
fps30Drop = FrameRate (30000.0 / 1001.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // common durations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Instant - imperceptible (0-50ms)
instant :: Milliseconds
instant = Milliseconds 50.0

-- | Fast - quick but noticeable (100-150ms)
fast :: Milliseconds
fast = Milliseconds 150.0

-- | Normal - standard UI timing (200-300ms)
normal :: Milliseconds
normal = Milliseconds 250.0

-- | Slow - deliberate, emphasized (400-500ms)
slow :: Milliseconds
slow = Milliseconds 450.0

-- | Glacial - very slow, dramatic (800-1000ms)
glacial :: Milliseconds
glacial = Milliseconds 900.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number from Seconds
unwrapSeconds :: Seconds -> Number
unwrapSeconds (Seconds n) = n

-- | Extract the raw Number from Milliseconds
unwrapMilliseconds :: Milliseconds -> Number
unwrapMilliseconds (Milliseconds n) = n

-- | Extract the raw Number from Microseconds
unwrapMicroseconds :: Microseconds -> Number
unwrapMicroseconds (Microseconds n) = n

-- | Extract the raw Number from Nanoseconds
unwrapNanoseconds :: Nanoseconds -> Number
unwrapNanoseconds (Nanoseconds n) = n

-- | Extract the raw Number from Minutes
unwrapMinutes :: Minutes -> Number
unwrapMinutes (Minutes n) = n

-- | Extract the raw Number from Hours
unwrapHours :: Hours -> Number
unwrapHours (Hours n) = n

-- | Extract the raw Number from Frames
unwrapFrames :: Frames -> Number
unwrapFrames (Frames n) = n

-- | Extract the raw Number from FrameRate
unwrapFps :: FrameRate -> Number
unwrapFps (FrameRate n) = n
