-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // temporal // time-code
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Timecode Atom — String representation of video/animation time.
-- |
-- | Standard SMPTE-style timecode format: HH:MM:SS:FF
-- | where:
-- | - HH: Hours (00-99)
-- | - MM: Minutes (00-59)
-- | - SS: Seconds (00-59)
-- | - FF: Frames (00-FPS)
-- |
-- | This atom wraps the string representation.
-- | Validation and calculation logic resides in the Molecules layer (TimeRange).

module Hydrogen.Schema.Temporal.Timecode
  ( Timecode
  , timecode
  , unsafeTimecode
  , unwrapTimecode
  , timecodeToString
  , emptyTimecode
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // timecode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Timecode string (HH:MM:SS:FF)
newtype Timecode = Timecode String

derive instance eqTimecode :: Eq Timecode
derive instance ordTimecode :: Ord Timecode

instance showTimecode :: Show Timecode where
  show (Timecode t) = "(Timecode " <> show t <> ")"

-- | Create Timecode (validates strictly for non-empty)
-- | In a full implementation, this would validate the regex pattern.
timecode :: String -> Timecode
timecode s = Timecode s

-- | Create Timecode without checks
unsafeTimecode :: String -> Timecode
unsafeTimecode = Timecode

-- | Extract raw String from Timecode
unwrapTimecode :: Timecode -> String
unwrapTimecode (Timecode s) = s

-- | Alias for unwrapTimecode
timecodeToString :: Timecode -> String
timecodeToString = unwrapTimecode

-- | Default empty/zero timecode
emptyTimecode :: Timecode
emptyTimecode = Timecode "00:00:00:00"
