-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | TimelinePanel Helpers
-- |
-- | Utility functions for timeline calculations and formatting.
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.TimelinePanel.Helpers
  ( elem
  , formatTimecode
  , parseIntDefault
  , parseNumberDefault
  , calculatePixelsPerFrame
  , calculateTimelineWidth
  , calculateMajorStep
  ) where

import Prelude

import Data.Array (filter, length)
import Data.Int as Int
import Data.Maybe (Maybe(..))

import Lattice.UI.Components.TimelinePanel.Types (State)

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // array helpers
-- ════════════════════════════════════════════════════════════════════════════

elem :: forall a. Eq a => a -> Array a -> Boolean
elem x arr = length (filter (_ == x) arr) > 0

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // time formatting
-- ════════════════════════════════════════════════════════════════════════════

formatTimecode :: Int -> Int -> String
formatTimecode frame fps =
  let
    totalSeconds = Int.toNumber frame / Int.toNumber fps
    hours = Int.floor (totalSeconds / 3600.0)
    hoursNum = Int.toNumber hours
    minutes = Int.floor ((totalSeconds - hoursNum * 3600.0) / 60.0)
    minutesNum = Int.toNumber minutes
    seconds = Int.floor (totalSeconds - hoursNum * 3600.0 - minutesNum * 60.0)
    frames = if fps > 0 then frame `mod` fps else 0
  in
  padZero hours <> ";" <> padZero minutes <> ";" <> padZero seconds <> ";" <> padZero frames
  where
    padZero n = if n < 10 then "0" <> show n else show n

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // parsing helpers
-- ════════════════════════════════════════════════════════════════════════════

parseIntDefault :: String -> Int -> Int
parseIntDefault s def = 
  case Int.fromString s of
    Just n -> n
    Nothing -> def

parseNumberDefault :: String -> Number -> Number
parseNumberDefault s def =
  case Int.fromString s of
    Just n -> Int.toNumber n
    Nothing -> def

-- ════════════════════════════════════════════════════════════════════════════
--                                                  // timeline calculations
-- ════════════════════════════════════════════════════════════════════════════

calculatePixelsPerFrame :: State -> Number
calculatePixelsPerFrame state =
  let
    minPpf = state.viewportWidth / Int.toNumber state.totalFrames
    maxPpf = 80.0
  in
  minPpf + (state.zoomPercent / 100.0) * (maxPpf - minPpf)

calculateTimelineWidth :: State -> Number
calculateTimelineWidth state =
  if state.zoomPercent == 0.0
    then state.viewportWidth
    else Int.toNumber state.totalFrames * calculatePixelsPerFrame state

calculateMajorStep :: Number -> Int
calculateMajorStep ppf =
  if ppf < 5.0 then 10
  else if ppf < 10.0 then 5
  else 1
