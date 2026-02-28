-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // temporal // fps
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FPS — Frames per second atom for animation and video timing.
-- |
-- | Represents the rate at which frames are displayed or processed.
-- | Used in motion graphics, video editing, game loops, and animation.
-- |
-- | ## Common Frame Rates
-- |
-- | - **24 fps**: Cinema standard
-- | - **25 fps**: PAL television
-- | - **29.97 fps**: NTSC television (drop-frame timecode)
-- | - **30 fps**: NTSC simplified / web video
-- | - **48 fps**: High frame rate cinema (HFR)
-- | - **50 fps**: PAL high-quality
-- | - **59.94 fps**: NTSC high-quality
-- | - **60 fps**: Games, smooth animation
-- | - **120 fps**: High-end displays, VR
-- | - **144/240/360 fps**: Gaming monitors

module Hydrogen.Schema.Temporal.FPS
  ( FPS
  , fps
  , unsafeFPS
  , unwrap
  , toNumber
  , frameDuration
  , framesPerMinute
  , framesPerHour
  -- * Standard Presets
  , cinema
  , pal
  , ntsc
  , ntscDropFrame
  , web30
  , web60
  , gaming120
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
  , (*)
  , (/)
  , (<>)
  , (<)
  )

import Data.Int (floor) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // fps
-- ═════════════════════════════════════════════════════════════════════════════

-- | Frames per second (> 0)
-- |
-- | Bounded by construction. Zero or negative FPS cannot exist.
-- | Minimum is 0.01 fps (one frame per 100 seconds).
newtype FPS = FPS Number

derive instance eqFPS :: Eq FPS
derive instance ordFPS :: Ord FPS

instance showFPS :: Show FPS where
  show (FPS f) = "(FPS " <> show f <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create FPS, clamping to minimum of 0.01
-- |
-- | ```purescript
-- | fps 60.0    -- FPS 60.0
-- | fps 0.0     -- FPS 0.01 (clamped)
-- | fps (-24.0) -- FPS 0.01 (clamped)
-- | ```
fps :: Number -> FPS
fps f
  | f < 0.01 = FPS 0.01
  | otherwise = FPS f

-- | Create FPS without bounds checking
-- |
-- | Use only when you know the value is positive.
unsafeFPS :: Number -> FPS
unsafeFPS = FPS

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract raw Number from FPS
unwrap :: FPS -> Number
unwrap (FPS f) = f

-- | Alias for unwrap
toNumber :: FPS -> Number
toNumber = unwrap

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // calculations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Duration of a single frame in seconds
-- |
-- | ```purescript
-- | frameDuration (fps 60.0)  -- 0.01666... (16.67ms per frame)
-- | frameDuration (fps 24.0)  -- 0.04166... (41.67ms per frame)
-- | ```
frameDuration :: FPS -> Number
frameDuration (FPS f) = 1.0 / f

-- | Number of frames in one minute
-- |
-- | ```purescript
-- | framesPerMinute (fps 24.0)  -- 1440
-- | framesPerMinute (fps 60.0)  -- 3600
-- | ```
framesPerMinute :: FPS -> Int
framesPerMinute (FPS f) = Int.floor (f * 60.0)

-- | Number of frames in one hour
-- |
-- | ```purescript
-- | framesPerHour (fps 24.0)  -- 86400
-- | framesPerHour (fps 60.0)  -- 216000
-- | ```
framesPerHour :: FPS -> Int
framesPerHour (FPS f) = Int.floor (f * 3600.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cinema standard: 24 fps
cinema :: FPS
cinema = FPS 24.0

-- | PAL television: 25 fps
pal :: FPS
pal = FPS 25.0

-- | NTSC simplified: 30 fps
ntsc :: FPS
ntsc = FPS 30.0

-- | NTSC actual (drop-frame): 29.97 fps
ntscDropFrame :: FPS
ntscDropFrame = FPS 29.97

-- | Web video standard: 30 fps
web30 :: FPS
web30 = FPS 30.0

-- | Smooth web/game: 60 fps
web60 :: FPS
web60 = FPS 60.0

-- | High-end gaming/VR: 120 fps
gaming120 :: FPS
gaming120 = FPS 120.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for FPS
-- |
-- | Min: 0.01 (one frame per 100 seconds)
-- | Max: practical limit around 1000 fps for most displays
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.01 1000.0 "fps" 
  "Frames per second (0.01 minimum, practical max ~1000)"
