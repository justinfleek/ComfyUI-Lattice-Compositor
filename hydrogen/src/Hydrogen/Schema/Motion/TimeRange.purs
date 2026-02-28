-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // motion // time-range
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Time range (in/out points) for motion graphics.
-- |
-- | Represents a span of time defined by in and out points. Used for:
-- | - Layer duration in timeline
-- | - Work area selection
-- | - Clip trimming
-- | - Loop regions
-- |
-- | ## Invariants
-- |
-- | - `inPoint <= outPoint` (enforced by smart constructors)
-- | - Both points are non-negative
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Motion.TimeRange as TR
-- | import Hydrogen.Schema.Dimension.Temporal (frames)
-- |
-- | -- Create a time range
-- | range = TR.timeRange (frames 100.0) (frames 500.0)
-- |
-- | -- Get duration
-- | dur = TR.duration range  -- 400 frames
-- |
-- | -- Check if frame is within range
-- | inRange = TR.contains (frames 250.0) range  -- true
-- |
-- | -- Trim range
-- | trimmed = TR.trim (frames 150.0) (frames 400.0) range
-- | ```
module Hydrogen.Schema.Motion.TimeRange
  ( -- * Core Type
    TimeRange(..)
  
  -- * Constructors
  , timeRange
  , fromDuration
  , empty
  , infinite
  
  -- * Accessors
  , inPoint
  , outPoint
  , duration
  
  -- * Predicates
  , contains
  , containsRange
  , overlaps
  , isEmpty
  
  -- * Operations
  , setInPoint
  , setOutPoint
  , shift
  , scale
  , trim
  , expand
  , intersect
  , union
  
  -- * Transformations
  , normalize
  , clamp
  ) where

import Prelude

import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Schema.Dimension.Temporal (Frames(Frames), unwrapFrames)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // core type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Time range defined by in and out points
-- |
-- | The newtype ensures invariants:
-- | - inPoint <= outPoint
-- | - Both points >= 0
newtype TimeRange = TimeRange
  { inPoint :: Frames
  , outPoint :: Frames
  }

derive instance eqTimeRange :: Eq TimeRange

instance showTimeRange :: Show TimeRange where
  show (TimeRange r) = 
    "[" <> show r.inPoint <> " - " <> show r.outPoint <> "]"

instance ordTimeRange :: Ord TimeRange where
  compare (TimeRange a) (TimeRange b) =
    case compare a.inPoint b.inPoint of
      EQ -> compare a.outPoint b.outPoint
      other -> other

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a time range from in and out points
-- |
-- | Points are automatically ordered (smaller becomes inPoint)
-- | Negative values are clamped to 0
timeRange :: Frames -> Frames -> TimeRange
timeRange (Frames a) (Frames b) =
  let
    clampedA = max 0.0 a
    clampedB = max 0.0 b
    minVal = min clampedA clampedB
    maxVal = max clampedA clampedB
  in
    TimeRange
      { inPoint: Frames minVal
      , outPoint: Frames maxVal
      }

-- | Create a time range from a start point and duration
-- |
-- | ```purescript
-- | range = fromDuration (frames 100.0) (frames 400.0)
-- | -- Creates range [100 - 500]
-- | ```
fromDuration :: Frames -> Frames -> TimeRange
fromDuration start (Frames dur) =
  let
    Frames s = start
    clampedStart = max 0.0 s
    clampedDur = max 0.0 dur
  in
    TimeRange
      { inPoint: Frames clampedStart
      , outPoint: Frames (clampedStart + clampedDur)
      }

-- | Empty range at frame 0
empty :: TimeRange
empty = TimeRange
  { inPoint: Frames 0.0
  , outPoint: Frames 0.0
  }

-- | Infinite range (for unbounded content)
-- |
-- | Uses a large value rather than actual infinity for numeric safety
infinite :: TimeRange
infinite = TimeRange
  { inPoint: Frames 0.0
  , outPoint: Frames 999999999.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the in point
inPoint :: TimeRange -> Frames
inPoint (TimeRange r) = r.inPoint

-- | Get the out point
outPoint :: TimeRange -> Frames
outPoint (TimeRange r) = r.outPoint

-- | Get the duration (outPoint - inPoint)
duration :: TimeRange -> Frames
duration (TimeRange r) = 
  let
    Frames a = r.inPoint
    Frames b = r.outPoint
  in
    Frames (b - a)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a frame is within the range (inclusive)
contains :: Frames -> TimeRange -> Boolean
contains (Frames f) (TimeRange r) =
  let
    Frames inP = r.inPoint
    Frames outP = r.outPoint
  in
    f >= inP && f <= outP

-- | Check if one range fully contains another
containsRange :: TimeRange -> TimeRange -> Boolean
containsRange (TimeRange inner) (TimeRange outer) =
  let
    Frames innerIn = inner.inPoint
    Frames innerOut = inner.outPoint
    Frames outerIn = outer.inPoint
    Frames outerOut = outer.outPoint
  in
    outerIn <= innerIn && innerOut <= outerOut

-- | Check if two ranges overlap
overlaps :: TimeRange -> TimeRange -> Boolean
overlaps (TimeRange a) (TimeRange b) =
  let
    Frames aIn = a.inPoint
    Frames aOut = a.outPoint
    Frames bIn = b.inPoint
    Frames bOut = b.outPoint
  in
    aIn <= bOut && bIn <= aOut

-- | Check if range has zero duration
isEmpty :: TimeRange -> Boolean
isEmpty range = unwrapFrames (duration range) == 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the in point (clamped to not exceed out point)
setInPoint :: Frames -> TimeRange -> TimeRange
setInPoint (Frames newIn) (TimeRange r) =
  let
    Frames outP = r.outPoint
    clampedIn = max 0.0 (min newIn outP)
  in
    TimeRange r { inPoint = Frames clampedIn }

-- | Set the out point (clamped to not be less than in point)
setOutPoint :: Frames -> TimeRange -> TimeRange
setOutPoint (Frames newOut) (TimeRange r) =
  let
    Frames inP = r.inPoint
    clampedOut = max inP newOut
  in
    TimeRange r { outPoint = Frames clampedOut }

-- | Shift the entire range by a frame offset
-- |
-- | ```purescript
-- | shifted = shift (frames 100.0) range
-- | -- Moves both in and out points by 100 frames
-- | ```
shift :: Frames -> TimeRange -> TimeRange
shift (Frames offset) (TimeRange r) =
  let
    Frames inP = r.inPoint
    Frames outP = r.outPoint
    newIn = max 0.0 (inP + offset)
    -- Preserve duration
    dur = outP - inP
    newOut = newIn + dur
  in
    TimeRange
      { inPoint: Frames newIn
      , outPoint: Frames newOut
      }

-- | Scale the range duration from the in point
-- |
-- | ```purescript
-- | scaled = scale 2.0 range
-- | -- Doubles the duration (out point moves)
-- | ```
scale :: Number -> TimeRange -> TimeRange
scale factor (TimeRange r) =
  let
    Frames inP = r.inPoint
    Frames outP = r.outPoint
    dur = outP - inP
    newDur = max 0.0 (dur * factor)
  in
    TimeRange r { outPoint = Frames (inP + newDur) }

-- | Trim range to fit within bounds
-- |
-- | ```purescript
-- | trimmed = trim (frames 50.0) (frames 200.0) range
-- | -- Clamps both in and out points to [50, 200]
-- | ```
trim :: Frames -> Frames -> TimeRange -> TimeRange
trim (Frames minBound) (Frames maxBound) (TimeRange r) =
  let
    Frames inP = r.inPoint
    Frames outP = r.outPoint
    newIn = max minBound (min inP maxBound)
    newOut = max newIn (min outP maxBound)
  in
    TimeRange
      { inPoint: Frames newIn
      , outPoint: Frames newOut
      }

-- | Expand range by an amount on each side
-- |
-- | ```purescript
-- | expanded = expand (frames 10.0) range
-- | -- Adds 10 frames to start and end
-- | ```
expand :: Frames -> TimeRange -> TimeRange
expand (Frames amount) (TimeRange r) =
  let
    Frames inP = r.inPoint
    Frames outP = r.outPoint
    newIn = max 0.0 (inP - amount)
    newOut = outP + amount
  in
    TimeRange
      { inPoint: Frames newIn
      , outPoint: Frames newOut
      }

-- | Get intersection of two ranges
-- |
-- | Returns Nothing if ranges don't overlap
intersect :: TimeRange -> TimeRange -> Maybe TimeRange
intersect (TimeRange a) (TimeRange b) =
  let
    Frames aIn = a.inPoint
    Frames aOut = a.outPoint
    Frames bIn = b.inPoint
    Frames bOut = b.outPoint
    newIn = max aIn bIn
    newOut = min aOut bOut
  in
    if newIn <= newOut
      then Just (TimeRange { inPoint: Frames newIn, outPoint: Frames newOut })
      else Nothing

-- | Get union of two ranges (smallest range containing both)
union :: TimeRange -> TimeRange -> TimeRange
union (TimeRange a) (TimeRange b) =
  let
    Frames aIn = a.inPoint
    Frames aOut = a.outPoint
    Frames bIn = b.inPoint
    Frames bOut = b.outPoint
  in
    TimeRange
      { inPoint: Frames (min aIn bIn)
      , outPoint: Frames (max aOut bOut)
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transformations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ensure range invariants (in <= out, both >= 0)
normalize :: TimeRange -> TimeRange
normalize (TimeRange r) =
  let
    Frames inP = r.inPoint
    Frames outP = r.outPoint
    clampedIn = max 0.0 inP
    clampedOut = max 0.0 outP
  in
    TimeRange
      { inPoint: Frames (min clampedIn clampedOut)
      , outPoint: Frames (max clampedIn clampedOut)
      }

-- | Clamp a frame to be within the range
clamp :: Frames -> TimeRange -> Frames
clamp (Frames f) (TimeRange r) =
  let
    Frames inP = r.inPoint
    Frames outP = r.outPoint
  in
    Frames (max inP (min f outP))
