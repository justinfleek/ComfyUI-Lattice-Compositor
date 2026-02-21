-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // enhanced-layer-track // snap
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- |
-- | Snap functionality for timeline layer bar drag operations.
-- |
-- | Shift+drag enables snapping to:
-- | - Playhead position
-- | - Other layer in/out points
-- | - Composition bounds (frame 0, last frame)
-- | - Timeline markers
-- |
-- | System F/Omega: snapToNearest :: Int -> Array Int -> Int
-- |
module Lattice.UI.Components.EnhancedLayerTrack.Snap
  ( snapTolerance
  , getSnapTargets
  , snapToNearest
  , intAbs
  , clampInt
  , roundToInt
  ) where

import Prelude

import Data.Array (concatMap, nub)
import Data.Foldable (foldl)
import Data.Int as Int

import Lattice.UI.Components.EnhancedLayerTrack.Types (State)

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // constants
-- ════════════════════════════════════════════════════════════════════════════

-- | Snap tolerance in frames (Shift+drag enables snapping)
snapTolerance :: Int
snapTolerance = 5

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // snap // targets
-- ════════════════════════════════════════════════════════════════════════════

-- | Build array of snap target frames from all layers, playhead, markers,
-- | and composition bounds.
-- |
-- | n.b. excludes current layer's own in/out points to avoid self-snapping
getSnapTargets :: State -> Array Int
getSnapTargets state =
  let
    -- playhead position
    playhead = [ state.currentFrame ]
    
    -- all other layer in/out points (excluding self)
    layerTargets = concatMap
      (\l -> if l.id == state.layer.id 
             then [] 
             else [ l.inPoint, l.outPoint ])
      state.allLayers
    
    -- composition start/end
    compBounds = [ 0, state.frameCount - 1 ]
    
    -- markers
    markerFrames = map _.frame state.markers
  in
  nub (playhead <> layerTargets <> compBounds <> markerFrames)

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // snap // algorithm
-- ════════════════════════════════════════════════════════════════════════════

-- | Snap a value to the nearest target if within tolerance.
-- |
-- | Returns the snapped value if any target is within `snapTolerance` frames,
-- | otherwise returns the original value unchanged.
snapToNearest :: Int -> Array Int -> Int
snapToNearest value targets =
  let
    findNearest :: { nearest :: Int, minDist :: Int } -> Int -> { nearest :: Int, minDist :: Int }
    findNearest acc target =
      let dist = intAbs (value - target)
      in if dist < acc.minDist
         then { nearest: target, minDist: dist }
         else acc
    
    initial = { nearest: value, minDist: snapTolerance + 1 }
    result = foldl findNearest initial targets
  in
  if result.minDist <= snapTolerance then result.nearest else value

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // utilities
-- ════════════════════════════════════════════════════════════════════════════

-- | Absolute value for Int
intAbs :: Int -> Int
intAbs n = if n < 0 then -n else n

-- | Clamp an Int between min and max (inclusive)
clampInt :: Int -> Int -> Int -> Int
clampInt minVal maxVal val = max minVal (min maxVal val)

-- | Round a Number to the nearest Int
roundToInt :: Number -> Int
roundToInt n = Int.round n
