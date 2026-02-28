-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // temporal // frames
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Frames — Frame count atom for frame-based animation timing.
-- |
-- | Represents discrete frame counts for animation and video work.
-- | Used in motion graphics, video editing, and game loop timing.
-- |
-- | ## Design Philosophy
-- |
-- | Frames are the atomic unit of discrete time in visual media.
-- | Unlike continuous time (seconds, milliseconds), frames are always
-- | integers — you cannot have half a frame.
-- |
-- | Combined with FPS, frames convert to/from wall-clock time.

module Hydrogen.Schema.Temporal.Frames
  ( Frames
  , frames
  , unsafeFrames
  , unwrap
  , toInt
  , toNumber
  , add
  , subtract
  , scale
  , toSeconds
  , fromSeconds
  , bounds
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
  )

import Data.Int (toNumber, floor) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // frames
-- ═════════════════════════════════════════════════════════════════════════════

-- | Frame count (0 or greater)
-- |
-- | Bounded by construction. Negative frame counts cannot exist.
-- | No upper bound — animations can be arbitrarily long.
newtype Frames = Frames Int

derive instance eqFrames :: Eq Frames
derive instance ordFrames :: Ord Frames

instance showFrames :: Show Frames where
  show (Frames f) = "(Frames " <> show f <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create Frames, clamping negative values to 0
-- |
-- | ```purescript
-- | frames 60    -- Frames 60
-- | frames (-10) -- Frames 0 (clamped)
-- | ```
frames :: Int -> Frames
frames f
  | f < 0 = Frames 0
  | otherwise = Frames f

-- | Create Frames without bounds checking
-- |
-- | Use only when you know the value is non-negative.
unsafeFrames :: Int -> Frames
unsafeFrames = Frames

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract raw Int from Frames
unwrap :: Frames -> Int
unwrap (Frames f) = f

-- | Alias for unwrap
toInt :: Frames -> Int
toInt = unwrap

-- | Convert to Number for calculations
toNumber :: Frames -> Number
toNumber (Frames f) = Int.toNumber f

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add two frame counts
-- |
-- | ```purescript
-- | add (frames 30) (frames 45)  -- Frames 75
-- | ```
add :: Frames -> Frames -> Frames
add (Frames a) (Frames b) = frames (a + b)

-- | Subtract frame counts (clamps to 0)
-- |
-- | ```purescript
-- | subtract (frames 30) (frames 10)  -- Frames 20
-- | subtract (frames 10) (frames 30)  -- Frames 0 (clamped)
-- | ```
subtract :: Frames -> Frames -> Frames
subtract (Frames a) (Frames b) = frames (a - b)

-- | Scale frames by a factor (truncates)
-- |
-- | ```purescript
-- | scale 2.0 (frames 30)  -- Frames 60
-- | scale 0.5 (frames 30)  -- Frames 15
-- | ```
scale :: Number -> Frames -> Frames
scale factor (Frames f) = frames (Int.floor (Int.toNumber f * factor))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert frames to seconds at given FPS
-- |
-- | ```purescript
-- | toSeconds 60.0 (frames 120)  -- 2.0 (120 frames at 60fps = 2 seconds)
-- | toSeconds 24.0 (frames 48)   -- 2.0 (48 frames at 24fps = 2 seconds)
-- | ```
toSeconds :: Number -> Frames -> Number
toSeconds fps (Frames f)
  | fps < 0.01 = 0.0  -- Avoid division by near-zero
  | otherwise = Int.toNumber f / fps

-- | Convert seconds to frames at given FPS (truncates)
-- |
-- | ```purescript
-- | fromSeconds 60.0 2.5  -- Frames 150 (2.5 seconds at 60fps)
-- | fromSeconds 24.0 1.0  -- Frames 24 (1 second at 24fps)
-- | ```
fromSeconds :: Number -> Number -> Frames
fromSeconds fps secs
  | fps < 0.01 = Frames 0
  | secs < 0.0 = Frames 0
  | otherwise = frames (Int.floor (secs * fps))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Frames
-- |
-- | Min: 0
-- | Max: unbounded (represented as maxBound Int)
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 0 2147483647 "frames" 
  "Frame count (0 or greater, no practical upper bound)"
