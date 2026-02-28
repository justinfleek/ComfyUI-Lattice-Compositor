-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // motion // timeline
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Timeline — Frame-based animation timing and layer coordination.
-- |
-- | ## Design Philosophy
-- |
-- | The Timeline is the master clock for all animation. It coordinates:
-- |
-- | - **Frame rate**: 24fps (film), 30fps (NTSC), 60fps (games)
-- | - **Layer timing**: When each layer starts, ends, and plays
-- | - **Time remap**: Variable speed playback per layer
-- | - **Path motion**: Position along motion paths per frame
-- |
-- | This module provides the calculations needed to render any frame:
-- |
-- | 1. Given global frame number
-- | 2. Calculate local time for each layer (accounting for offsets, remap)
-- | 3. Evaluate motion paths at that local time
-- | 4. Return positions, rotations, properties for rendering
-- |
-- | ## Frame vs Time
-- |
-- | - **Frame**: Integer unit (frame 0, frame 1, frame 30)
-- | - **Time**: Continuous unit in seconds (0.0s, 0.033s, 1.0s)
-- | - Conversion: frame = time × fps
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Motion.Timeline as TL
-- |
-- | -- Create timeline at 30fps
-- | timeline = TL.timeline TL.fps30 300  -- 300 frames = 10 seconds
-- |
-- | -- Add a layer
-- | layer = TL.addLayer "hero" 0 100 timeline
-- |
-- | -- Get local time for layer at global frame 50
-- | localTime = TL.layerTimeAtFrame "hero" 50 timeline
-- |
-- | -- Evaluate path at this time
-- | pos = PM.positionAtTime localTime motionPath
-- | ```

module Hydrogen.Schema.Motion.Timeline
  ( -- * Core Types
    Timeline(Timeline)
  , TimelineLayer(TimelineLayer)
  , FrameRate
  
  -- * Construction
  , timeline
  , emptyTimeline
  , fromDuration
  
  -- * Frame Rates
  , fps24
  , fps25
  , fps30
  , fps48
  , fps60
  , fps120
  , customFps
  
  -- * Layer Management
  , addLayer
  , removeLayer
  , getLayer
  , setLayerTiming
  , setLayerTimeRemap
  
  -- * Frame Calculation
  , globalToLocal
  , localToGlobal
  , layerTimeAtFrame
  , frameAtLayerTime
  , isLayerActiveAtFrame
  
  -- * Time Conversion
  , frameToSeconds
  , secondsToFrame
  , progressAtFrame
  , frameAtProgress
  
  -- * Duration
  , totalFrames
  , totalSeconds
  , setTotalFrames
  , setTotalSeconds
  
  -- * Playback
  , clampFrame
  , wrapFrame
  , pingPongFrame
  
  -- * Batch Operations
  , activeLayersAtFrame
  , layerTimesAtFrame
  , evaluateFrame
  
  -- * Analysis
  , timelineFrameRate
  , layerDuration
  , layerStartFrame
  , layerEndFrame
  
  -- * Layer Access
  , getLayerByIndex
  , layerCount
  , hasLayer
  
  -- * Advanced Timing
  , reverseTimeline
  , clearTimeRemap
  , isLayerRemapped
  , isFramePlayable
  , seekToLayerFrame
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (==)
  , (/=)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (&&)
  , (||)
  , otherwise
  , negate
  , min
  , max
  , map
  )

import Data.Array (length, index, snoc, foldl, filter)
import Data.Maybe (Maybe(..))
import Data.Number (floor)
import Data.Int (toNumber) as Int

import Hydrogen.Schema.Motion.TimeRemap (TimeRemap, identity, apply, applyInverse)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Frame rate (frames per second).
type FrameRate = Number

-- | A layer in the timeline with timing information.
newtype TimelineLayer = TimelineLayer
  { name :: String
  , startFrame :: Number        -- When layer begins (global frame)
  , endFrame :: Number          -- When layer ends (global frame)
  , inPoint :: Number           -- Where to start in source (local frame)
  , outPoint :: Number          -- Where to end in source (local frame)
  , timeRemap :: Maybe TimeRemap -- Optional time remapping
  , enabled :: Boolean
  }

derive instance eqTimelineLayer :: Eq TimelineLayer

instance showTimelineLayer :: Show TimelineLayer where
  show (TimelineLayer l) = "(TimelineLayer " <> l.name 
    <> " [" <> show l.startFrame <> "-" <> show l.endFrame <> "])"

-- | Complete timeline with frame rate and layers.
newtype Timeline = Timeline
  { frameRate :: FrameRate
  , totalFrames :: Number
  , layers :: Array TimelineLayer
  , looping :: Boolean
  , pingPong :: Boolean
  }

derive instance eqTimeline :: Eq Timeline

instance showTimeline :: Show Timeline where
  show (Timeline t) = "(Timeline " <> show t.frameRate <> "fps " 
    <> show t.totalFrames <> " frames, " 
    <> show (length t.layers) <> " layers)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a timeline with frame rate and duration.
timeline :: FrameRate -> Number -> Timeline
timeline fps frames = Timeline
  { frameRate: fps
  , totalFrames: frames
  , layers: []
  , looping: false
  , pingPong: false
  }

-- | Create empty timeline with default settings.
emptyTimeline :: Timeline
emptyTimeline = timeline fps30 0.0

-- | Create timeline from duration in seconds.
fromDuration :: FrameRate -> Number -> Timeline
fromDuration fps seconds = timeline fps (seconds * fps)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // frame rates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Film (24fps)
fps24 :: FrameRate
fps24 = 24.0

-- | PAL (25fps)
fps25 :: FrameRate
fps25 = 25.0

-- | NTSC (30fps)
fps30 :: FrameRate
fps30 = 30.0

-- | High frame rate film (48fps)
fps48 :: FrameRate
fps48 = 48.0

-- | Games/UI (60fps)
fps60 :: FrameRate
fps60 = 60.0

-- | High refresh (120fps)
fps120 :: FrameRate
fps120 = 120.0

-- | Custom frame rate
customFps :: Number -> FrameRate
customFps = clampFps

-- | Clamp frame rate to valid range
clampFps :: Number -> Number
clampFps fps = max 1.0 (min 240.0 fps)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // layer management
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add a layer to the timeline.
addLayer :: String -> Number -> Number -> Timeline -> Timeline
addLayer name startF endF (Timeline t) =
  let 
    layer = TimelineLayer
      { name: name
      , startFrame: startF
      , endFrame: endF
      , inPoint: 0.0
      , outPoint: endF - startF
      , timeRemap: Nothing
      , enabled: true
      }
  in Timeline (t { layers = snoc t.layers layer })

-- | Remove a layer by name.
removeLayer :: String -> Timeline -> Timeline
removeLayer name (Timeline t) = Timeline
  (t { layers = filter (\(TimelineLayer l) -> l.name /= name) t.layers })

-- | Get layer by name.
getLayer :: String -> Timeline -> Maybe TimelineLayer
getLayer name (Timeline t) =
  foldl (\acc layer@(TimelineLayer l) ->
    case acc of
      Just _ -> acc
      Nothing -> if l.name == name then Just layer else Nothing
  ) Nothing t.layers

-- | Set layer timing.
setLayerTiming :: String -> Number -> Number -> Timeline -> Timeline
setLayerTiming name startF endF (Timeline t) = Timeline
  (t { layers = map (\layer@(TimelineLayer l) ->
    if l.name == name then TimelineLayer (l { startFrame = startF, endFrame = endF })
    else layer
  ) t.layers })

-- | Set time remap for a layer.
setLayerTimeRemap :: String -> TimeRemap -> Timeline -> Timeline
setLayerTimeRemap name remap (Timeline t) = Timeline
  (t { layers = map (\layer@(TimelineLayer l) ->
    if l.name == name then TimelineLayer (l { timeRemap = Just remap })
    else layer
  ) t.layers })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // frame calculation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert global frame to local frame for a layer.
-- |
-- | Accounts for layer offset and time remapping.
globalToLocal :: Number -> TimelineLayer -> Number
globalToLocal globalFrame (TimelineLayer l) =
  let
    -- Offset by layer start
    relativeFrame = globalFrame - l.startFrame
    
    -- Clamp to layer duration
    clampedFrame = clampNumber 0.0 (l.endFrame - l.startFrame) relativeFrame
    
    -- Apply time remap if present
    remappedFrame = case l.timeRemap of
      Nothing -> clampedFrame
      Just remap -> apply clampedFrame remap
    
    -- Add in-point offset
    localFrame = l.inPoint + remappedFrame
  in
    localFrame

-- | Convert local frame to global frame.
-- |
-- | This is the inverse of `globalToLocal`. For layers with time remapping,
-- | this uses numerical inversion which may have small errors for complex
-- | speed curves.
localToGlobal :: Number -> TimelineLayer -> Number
localToGlobal localFrame (TimelineLayer l) =
  let
    -- Remove in-point offset
    relativeLocal = localFrame - l.inPoint
    
    -- Apply inverse time remap if present
    unremappedFrame = case l.timeRemap of
      Nothing -> relativeLocal
      Just remap -> applyInverse relativeLocal remap
    
    -- Add layer start
    globalFrame = l.startFrame + unremappedFrame
  in
    globalFrame

-- | Get layer local time at global frame.
layerTimeAtFrame :: String -> Number -> Timeline -> Maybe Number
layerTimeAtFrame name globalFrame tl =
  case getLayer name tl of
    Nothing -> Nothing
    Just layer -> Just (globalToLocal globalFrame layer)

-- | Get global frame at layer local time.
frameAtLayerTime :: String -> Number -> Timeline -> Maybe Number
frameAtLayerTime name localTime tl =
  case getLayer name tl of
    Nothing -> Nothing
    Just layer -> Just (localToGlobal localTime layer)

-- | Check if layer is active at global frame.
isLayerActiveAtFrame :: String -> Number -> Timeline -> Boolean
isLayerActiveAtFrame name globalFrame tl =
  case getLayer name tl of
    Nothing -> false
    Just (TimelineLayer l) ->
      l.enabled && globalFrame >= l.startFrame && globalFrame <= l.endFrame

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // time conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert frame to seconds.
frameToSeconds :: Number -> Timeline -> Number
frameToSeconds frame (Timeline t) =
  if t.frameRate < epsilon then 0.0
  else frame / t.frameRate

-- | Convert seconds to frame.
secondsToFrame :: Number -> Timeline -> Number
secondsToFrame seconds (Timeline t) = seconds * t.frameRate

-- | Get progress (0-1) at frame.
progressAtFrame :: Number -> Timeline -> Number
progressAtFrame frame (Timeline t) =
  if t.totalFrames < epsilon then 0.0
  else clamp01 (frame / t.totalFrames)

-- | Get frame at progress (0-1).
frameAtProgress :: Number -> Timeline -> Number
frameAtProgress progress (Timeline t) = clamp01 progress * t.totalFrames

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // duration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get total frames.
totalFrames :: Timeline -> Number
totalFrames (Timeline t) = t.totalFrames

-- | Get total duration in seconds.
totalSeconds :: Timeline -> Number
totalSeconds tl@(Timeline t) = frameToSeconds t.totalFrames tl

-- | Set total frames.
setTotalFrames :: Number -> Timeline -> Timeline
setTotalFrames frames (Timeline t) = Timeline (t { totalFrames = frames })

-- | Set total duration in seconds.
setTotalSeconds :: Number -> Timeline -> Timeline
setTotalSeconds seconds tl = setTotalFrames (secondsToFrame seconds tl) tl

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // playback
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp frame to timeline range.
clampFrame :: Number -> Timeline -> Number
clampFrame frame (Timeline t) = clampNumber 0.0 t.totalFrames frame

-- | Wrap frame for looping playback.
wrapFrame :: Number -> Timeline -> Number
wrapFrame frame (Timeline t) =
  if t.totalFrames < epsilon then 0.0
  else
    let wrapped = frame - t.totalFrames * floor (frame / t.totalFrames)
    in if wrapped < 0.0 then wrapped + t.totalFrames else wrapped

-- | Ping-pong frame (forward then backward).
pingPongFrame :: Number -> Timeline -> Number
pingPongFrame frame (Timeline t) =
  if t.totalFrames < epsilon then 0.0
  else
    let 
      cycle = frame / t.totalFrames
      cycleInt = floor cycle
      frac = cycle - cycleInt
      isReverse = floorInt cycleInt `mod` 2 == 1
    in
      if isReverse then t.totalFrames * (1.0 - frac)
      else t.totalFrames * frac

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // batch operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all layers active at frame.
activeLayersAtFrame :: Number -> Timeline -> Array TimelineLayer
activeLayersAtFrame frame (Timeline t) =
  filter (\(TimelineLayer l) ->
    l.enabled && frame >= l.startFrame && frame <= l.endFrame
  ) t.layers

-- | Get local times for all active layers at frame.
-- |
-- | Returns array of { name, localTime } records.
layerTimesAtFrame :: Number -> Timeline -> Array { name :: String, localTime :: Number }
layerTimesAtFrame frame tl =
  let activeLayers = activeLayersAtFrame frame tl
  in map (\layer@(TimelineLayer l) ->
    { name: l.name
    , localTime: globalToLocal frame layer
    }
  ) activeLayers

-- | Evaluate all layers at frame.
-- |
-- | Returns complete state for rendering.
evaluateFrame :: Number -> Timeline -> 
  { frame :: Number
  , time :: Number
  , progress :: Number
  , layers :: Array { name :: String, localTime :: Number, progress :: Number }
  }
evaluateFrame frame tl@(Timeline t) =
  let
    processedFrame = 
      if t.looping then wrapFrame frame tl
      else if t.pingPong then pingPongFrame frame tl
      else clampFrame frame tl
    
    activeLayers = activeLayersAtFrame processedFrame tl
    
    layerData = map (\layer@(TimelineLayer l) ->
      let 
        localT = globalToLocal processedFrame layer
        layerDur = l.endFrame - l.startFrame
        prog = if layerDur < epsilon then 0.0 else (localT - l.inPoint) / layerDur
      in
        { name: l.name
        , localTime: localT
        , progress: clamp01 prog
        }
    ) activeLayers
  in
    { frame: processedFrame
    , time: frameToSeconds processedFrame tl
    , progress: progressAtFrame processedFrame tl
    , layers: layerData
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // analysis
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get timeline frame rate.
timelineFrameRate :: Timeline -> FrameRate
timelineFrameRate (Timeline t) = t.frameRate

-- | Get layer duration in frames.
layerDuration :: String -> Timeline -> Maybe Number
layerDuration name tl =
  case getLayer name tl of
    Nothing -> Nothing
    Just (TimelineLayer l) -> Just (l.endFrame - l.startFrame)

-- | Get layer start frame.
layerStartFrame :: String -> Timeline -> Maybe Number
layerStartFrame name tl =
  case getLayer name tl of
    Nothing -> Nothing
    Just (TimelineLayer l) -> Just l.startFrame

-- | Get layer end frame.
layerEndFrame :: String -> Timeline -> Maybe Number
layerEndFrame name tl =
  case getLayer name tl of
    Nothing -> Nothing
    Just (TimelineLayer l) -> Just l.endFrame

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // layer access
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get layer by index (0-based).
getLayerByIndex :: Int -> Timeline -> Maybe TimelineLayer
getLayerByIndex idx (Timeline t) = index t.layers idx

-- | Get number of layers in timeline.
layerCount :: Timeline -> Int
layerCount (Timeline t) = length t.layers

-- | Check if timeline has a layer with given name.
hasLayer :: String -> Timeline -> Boolean
hasLayer name tl = 
  case getLayer name tl of
    Nothing -> false
    Just _ -> true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // advanced timing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reverse timeline by negating all time calculations.
-- |
-- | Creates a timeline where playback runs backward:
-- | - Frame 0 shows what was at totalFrames
-- | - Frame totalFrames shows what was at 0
reverseTimeline :: Timeline -> Timeline
reverseTimeline (Timeline t) = Timeline
  (t { layers = map reverseLayer t.layers })
  where
    reverseLayer :: TimelineLayer -> TimelineLayer
    reverseLayer (TimelineLayer l) = TimelineLayer
      (l { startFrame = negate l.endFrame + t.totalFrames
         , endFrame = negate l.startFrame + t.totalFrames
         , inPoint = l.outPoint
         , outPoint = l.inPoint
         })

-- | Clear time remap from a layer, resetting to identity (linear time).
clearTimeRemap :: String -> Timeline -> Timeline
clearTimeRemap name (Timeline t) = Timeline
  (t { layers = map (\layer@(TimelineLayer l) ->
    if l.name == name 
    then 
      let layerDur = l.endFrame - l.startFrame
      in TimelineLayer (l { timeRemap = Just (identity layerDur) })
    else layer
  ) t.layers })

-- | Check if a layer has time remapping applied.
-- |
-- | Returns true if layer exists and has non-identity time remap,
-- | false if layer doesn't exist or has no remap.
isLayerRemapped :: String -> Timeline -> Boolean
isLayerRemapped name tl =
  case getLayer name tl of
    Nothing -> false
    Just (TimelineLayer l) -> 
      case l.timeRemap of
        Nothing -> false
        Just _ -> true

-- | Check if frame is within playable range or any layer is active.
-- |
-- | Returns true if either:
-- | - Frame is within timeline bounds (0 to totalFrames), OR
-- | - Any layer is active at this frame
isFramePlayable :: Number -> Timeline -> Boolean
isFramePlayable frame tl@(Timeline t) =
  let
    inBounds = frame >= 0.0 && frame <= t.totalFrames
    hasActiveLayers = length (activeLayersAtFrame frame tl) > 0
  in
    inBounds || hasActiveLayers

-- | Seek to frame by layer index with optional offset.
-- |
-- | Given a layer index, returns the start frame of that layer
-- | plus an optional frame offset. Useful for seeking to specific
-- | layers in a multi-layer composition.
seekToLayerFrame :: Int -> Int -> Timeline -> Maybe Number
seekToLayerFrame layerIdx frameOffset tl =
  case getLayerByIndex layerIdx tl of
    Nothing -> Nothing
    Just (TimelineLayer l) -> Just (l.startFrame + Int.toNumber frameOffset)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp to [0, 1]
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | otherwise = n

-- | Clamp to range
-- | Named clampNumber to avoid shadowing Prelude.clamp
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi n
  | n < lo = lo
  | n > hi = hi
  | otherwise = n

-- | Floor to Int
floorInt :: Number -> Int
floorInt n = 
  if n >= 0.0 then truncateToInt n
  else truncateToInt n - 1

truncateToInt :: Number -> Int
truncateToInt n = truncateImpl n 0

truncateImpl :: Number -> Int -> Int
truncateImpl n acc =
  if n < 1.0 then acc
  else truncateImpl (n - 1.0) (acc + 1)

-- | Integer modulo
mod :: Int -> Int -> Int
mod a b = a - (a / b) * b

-- | Small epsilon
epsilon :: Number
epsilon = 1.0e-10
