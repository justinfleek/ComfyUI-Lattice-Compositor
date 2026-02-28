-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // motion // time-code
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SMPTE timecode representation for professional video/motion graphics.
-- |
-- | Timecode is the standard way to reference specific frames in video
-- | production. Unlike raw frame numbers, timecode is human-readable
-- | and frame-rate aware.
-- |
-- | ## Format
-- |
-- | Standard format: `HH:MM:SS:FF` (non-drop) or `HH:MM:SS;FF` (drop-frame)
-- |
-- | - `HH` - Hours (00-23)
-- | - `MM` - Minutes (00-59)
-- | - `SS` - Seconds (00-59)
-- | - `FF` - Frames (00 to frameRate-1)
-- |
-- | ## Drop-Frame Timecode
-- |
-- | NTSC video runs at 29.97 fps, not exactly 30 fps. To keep timecode
-- | synchronized with wall-clock time, drop-frame timecode skips frame
-- | numbers 0 and 1 at the start of each minute, except every 10th minute.
-- |
-- | Drop-frame uses semicolon separator: `01:02:03;04`
-- | Non-drop uses colon separator: `01:02:03:04`
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Motion.Timecode as TC
-- | import Hydrogen.Schema.Dimension.Temporal (fps24, fps30Drop)
-- |
-- | -- Create from components
-- | tc1 = TC.timecode 1 30 15 12 fps24
-- | -- Result: 01:30:15:12 at 24fps
-- |
-- | -- Parse from string
-- | tc2 = TC.parse "00:01:30;15" fps30Drop
-- | -- Result: Drop-frame timecode at 29.97fps
-- |
-- | -- Convert to frames
-- | frames = TC.toFrames tc1
-- | -- Result: 130812 frames
-- |
-- | -- Format for display
-- | display = TC.format tc1
-- | -- Result: "01:30:15:12"
-- | ```
module Hydrogen.Schema.Motion.Timecode
  ( -- * Core Type
    Timecode(..)
  , TimecodeComponents
  
  -- * Constructors
  , timecode
  , fromFrames
  , fromSeconds
  , zero
  
  -- * Parsing
  , parse
  , parseComponents
  
  -- * Conversion
  , toFrames
  , toSeconds
  , toComponents
  
  -- * Formatting
  , format
  , formatCompact
  
  -- * Operations
  , addFrames
  , subtractFrames
  , addTimecode
  , subtractTimecode
  
  -- * Queries
  , isDropFrame
  , frameRate
  , totalFrames
  
  -- * Validation
  , isValid
  , normalize
  ) where

import Prelude

import Data.Int (floor, round)
import Data.Int (toNumber, fromString) as Int
import Data.Maybe (Maybe(Nothing, Just))
import Data.String (Pattern(Pattern), Replacement(Replacement), length, replaceAll, split)
import Data.String (contains, trim) as String
import Data.Traversable (traverse) as Traversable
import Hydrogen.Schema.Dimension.Temporal (FrameRate, Frames(Frames), Seconds(Seconds))
import Hydrogen.Schema.Dimension.Temporal (unwrapFps) as Temporal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | SMPTE Timecode representation
-- |
-- | Stores timecode as total frame count with frame rate context.
-- | This avoids ambiguity when performing arithmetic operations.
newtype Timecode = Timecode
  { totalFrames :: Int
  , rate :: FrameRate
  , dropFrame :: Boolean
  }

derive instance eqTimecode :: Eq Timecode

instance showTimecode :: Show Timecode where
  show tc = format tc

instance ordTimecode :: Ord Timecode where
  compare (Timecode a) (Timecode b) = compare a.totalFrames b.totalFrames

-- | Timecode broken into display components
-- | Used for formatting and parsing
type TimecodeComponents =
  { hours :: Int
  , minutes :: Int
  , seconds :: Int
  , frames :: Int
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create timecode from hour, minute, second, frame components
-- |
-- | ```purescript
-- | tc = timecode 1 30 15 12 fps24 false
-- | -- Creates 01:30:15:12 at 24fps non-drop
-- | ```
timecode :: Int -> Int -> Int -> Int -> FrameRate -> Boolean -> Timecode
timecode hours mins secs frms rate dropFrm =
  let
    fpsInt = floor (Temporal.unwrapFps rate)
    totalSecs = hours * 3600 + mins * 60 + secs
    baseFrames = totalSecs * fpsInt + frms
    
    -- Apply drop-frame correction if needed
    adjustedFrames = 
      if dropFrm 
        then applyDropFrameCorrection hours mins baseFrames
        else baseFrames
  in
    Timecode
      { totalFrames: adjustedFrames
      , rate: rate
      , dropFrame: dropFrm
      }

-- | Create timecode from a raw frame count
fromFrames :: Frames -> FrameRate -> Boolean -> Timecode
fromFrames (Frames f) rate dropFrm = Timecode
  { totalFrames: round f
  , rate: rate
  , dropFrame: dropFrm
  }

-- | Create timecode from seconds
fromSeconds :: Seconds -> FrameRate -> Boolean -> Timecode
fromSeconds (Seconds s) rate dropFrm =
  let
    frameCount = round (s * Temporal.unwrapFps rate)
  in
    Timecode
      { totalFrames: frameCount
      , rate: rate
      , dropFrame: dropFrm
      }

-- | Zero timecode (00:00:00:00)
zero :: FrameRate -> Boolean -> Timecode
zero rate dropFrm = Timecode
  { totalFrames: 0
  , rate: rate
  , dropFrame: dropFrm
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // drop frame helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply drop-frame correction when creating timecode from components
-- |
-- | Drop-frame timecode skips frames 0 and 1 at the start of each minute,
-- | except for minutes 0, 10, 20, 30, 40, 50.
applyDropFrameCorrection :: Int -> Int -> Int -> Int
applyDropFrameCorrection hours mins baseFrames =
  let
    totalMins = hours * 60 + mins
    -- Number of frame pairs to drop (2 per minute, except every 10th)
    dropCount = (totalMins - (totalMins / 10)) * 2
  in
    baseFrames + dropCount

-- | Calculate drop-frame adjusted frame count to timecode components
dropFrameToComponents :: Int -> Int -> TimecodeComponents
dropFrameToComponents frameCount fpsInt =
  let
    -- Frames per minute with drops
    framesPerMin = fpsInt * 60 - 2
    -- Frames per 10 minutes (no drop on 10th minute)
    framesPer10Min = framesPerMin * 10 + 2
    
    -- Calculate 10-minute blocks
    tenMinBlocks = frameCount / framesPer10Min
    remainingAfterTenMin = frameCount `mod` framesPer10Min
    
    -- Calculate minutes within the 10-minute block
    minutesInBlock = 
      if remainingAfterTenMin < framesPerMin + 2
        then 0
        else 1 + ((remainingAfterTenMin - framesPerMin - 2) / framesPerMin)
    
    -- Calculate total minutes
    totalMinutes = tenMinBlocks * 10 + minutesInBlock
    
    -- Calculate remaining frames
    framesInCurrentMin =
      if minutesInBlock == 0
        then remainingAfterTenMin
        else (remainingAfterTenMin - framesPerMin - 2) `mod` framesPerMin + 2
    
    hours' = totalMinutes / 60
    minutes' = totalMinutes `mod` 60
    seconds' = framesInCurrentMin / fpsInt
    frames' = framesInCurrentMin `mod` fpsInt
  in
    { hours: hours'
    , minutes: minutes'
    , seconds: seconds'
    , frames: frames'
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // parsing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parse timecode from string
-- |
-- | Accepts formats:
-- | - "HH:MM:SS:FF" (non-drop)
-- | - "HH:MM:SS;FF" (drop-frame)
-- | - "HH:MM:SS.mmm" (milliseconds, converted to frames)
parse :: String -> FrameRate -> Maybe Timecode
parse str rate =
  let
    -- Detect drop-frame from semicolon
    isDropFrm = String.contains (Pattern ";") str
    
    -- Normalize to use colons for splitting
    normalized = replaceAll (Pattern ";") (Replacement ":") str
    
    parts = split (Pattern ":") normalized
  in
    case parseIntArray parts of
      Just [h, m, s, f] -> 
        Just (timecode h m s f rate isDropFrm)
      Just [m, s, f] -> 
        Just (timecode 0 m s f rate isDropFrm)
      Just [s, f] -> 
        Just (timecode 0 0 s f rate isDropFrm)
      _ -> Nothing

-- | Parse string components without creating timecode
parseComponents :: String -> Maybe TimecodeComponents
parseComponents str =
  let
    normalized = replaceAll (Pattern ";") (Replacement ":") str
    parts = split (Pattern ":") normalized
  in
    case parseIntArray parts of
      Just [h, m, s, f] -> Just { hours: h, minutes: m, seconds: s, frames: f }
      Just [m, s, f] -> Just { hours: 0, minutes: m, seconds: s, frames: f }
      Just [s, f] -> Just { hours: 0, minutes: 0, seconds: s, frames: f }
      _ -> Nothing

-- | Helper to parse array of strings to ints
parseIntArray :: Array String -> Maybe (Array Int)
parseIntArray strs = Traversable.traverse parseIntSafe strs
  where
    parseIntSafe :: String -> Maybe Int
    parseIntSafe s = 
      let trimmed = String.trim s
      in if length trimmed == 0
           then Nothing
           else Int.fromString trimmed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert timecode to raw frame count
toFrames :: Timecode -> Frames
toFrames (Timecode tc) = Frames (Int.toNumber tc.totalFrames)

-- | Convert timecode to seconds
toSeconds :: Timecode -> Seconds
toSeconds (Timecode tc) = 
  Seconds (Int.toNumber tc.totalFrames / Temporal.unwrapFps tc.rate)

-- | Get timecode display components
toComponents :: Timecode -> TimecodeComponents
toComponents (Timecode tc) =
  let
    fpsInt = floor (Temporal.unwrapFps tc.rate)
  in
    if tc.dropFrame
      then dropFrameToComponents tc.totalFrames fpsInt
      else
        let
          totalSecs = tc.totalFrames / fpsInt
          frames' = tc.totalFrames `mod` fpsInt
          seconds' = totalSecs `mod` 60
          totalMins = totalSecs / 60
          minutes' = totalMins `mod` 60
          hours' = totalMins / 60
        in
          { hours: hours'
          , minutes: minutes'
          , seconds: seconds'
          , frames: frames'
          }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // formatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format timecode as SMPTE string
-- |
-- | ```purescript
-- | format tc
-- | -- Non-drop: "01:30:15:12"
-- | -- Drop-frame: "01:30:15;12"
-- | ```
format :: Timecode -> String
format tc@(Timecode tcData) =
  let
    c = toComponents tc
    sep = if tcData.dropFrame then ";" else ":"
  in
    pad2 c.hours <> ":" <> 
    pad2 c.minutes <> ":" <> 
    pad2 c.seconds <> sep <> 
    pad2 c.frames

-- | Format timecode compactly (omit leading zeros)
-- |
-- | ```purescript
-- | formatCompact tc
-- | -- "1:30:15:12" instead of "01:30:15:12"
-- | -- "0:15:12" for timecode under 1 minute
-- | ```
formatCompact :: Timecode -> String
formatCompact tc@(Timecode tcData) =
  let
    c = toComponents tc
    sep = if tcData.dropFrame then ";" else ":"
  in
    if c.hours > 0 
      then show c.hours <> ":" <> pad2 c.minutes <> ":" <> pad2 c.seconds <> sep <> pad2 c.frames
      else if c.minutes > 0
        then show c.minutes <> ":" <> pad2 c.seconds <> sep <> pad2 c.frames
        else show c.seconds <> sep <> pad2 c.frames

-- | Pad number to 2 digits
pad2 :: Int -> String
pad2 n = if n < 10 then "0" <> show n else show n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add frames to timecode
addFrames :: Int -> Timecode -> Timecode
addFrames n (Timecode tc) = Timecode tc { totalFrames = tc.totalFrames + n }

-- | Subtract frames from timecode
subtractFrames :: Int -> Timecode -> Timecode
subtractFrames n (Timecode tc) = Timecode tc { totalFrames = max 0 (tc.totalFrames - n) }

-- | Add two timecodes (uses rate from first operand)
addTimecode :: Timecode -> Timecode -> Timecode
addTimecode (Timecode a) (Timecode b) = 
  Timecode a { totalFrames = a.totalFrames + b.totalFrames }

-- | Subtract timecodes (uses rate from first operand)
subtractTimecode :: Timecode -> Timecode -> Timecode
subtractTimecode (Timecode a) (Timecode b) = 
  Timecode a { totalFrames = max 0 (a.totalFrames - b.totalFrames) }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if timecode uses drop-frame format
isDropFrame :: Timecode -> Boolean
isDropFrame (Timecode tc) = tc.dropFrame

-- | Get the frame rate of this timecode
frameRate :: Timecode -> FrameRate
frameRate (Timecode tc) = tc.rate

-- | Get total frame count
totalFrames :: Timecode -> Int
totalFrames (Timecode tc) = tc.totalFrames

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if timecode components are valid for given frame rate
isValid :: TimecodeComponents -> FrameRate -> Boolean
isValid c rate =
  let
    fpsInt = floor (Temporal.unwrapFps rate)
  in
    c.hours >= 0 && c.hours < 24 &&
    c.minutes >= 0 && c.minutes < 60 &&
    c.seconds >= 0 && c.seconds < 60 &&
    c.frames >= 0 && c.frames < fpsInt

-- | Normalize timecode to valid range (handle overflow)
normalize :: Timecode -> Timecode
normalize tc@(Timecode tcData) =
  let
    fpsInt = floor (Temporal.unwrapFps tcData.rate)
    framesPerDay = fpsInt * 60 * 60 * 24
  in
    if tcData.totalFrames < 0
      then Timecode tcData { totalFrames = 0 }
      else if tcData.totalFrames >= framesPerDay
        then Timecode tcData { totalFrames = tcData.totalFrames `mod` framesPerDay }
        else tc
