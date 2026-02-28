-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // gestural // gesture // pinch
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pinch - two-finger pinch-to-zoom gesture recognition.
-- |
-- | Models pinch gestures for zoom and scale interactions.
-- | Tracks scale factor, center point, and gesture phase.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Gestural.Gesture.Phase
-- | - Hydrogen.Math.Core (sqrt)
-- |
-- | ## Dependents
-- | - Component.Image (pinch to zoom)
-- | - Component.Map (map zoom)
-- | - Component.Canvas (viewport scaling)

module Hydrogen.Schema.Gestural.Gesture.Pinch
  ( -- * Pinch Config
    PinchConfig
  , pinchConfig
  , defaultPinchConfig
  , pinchMinScale
  , pinchMaxScale
    -- * Pinch Gesture State
  , PinchGesture
  , pinchGesture
  , noPinchGesture
  , beginPinch
  , updatePinch
  , endPinch
  , cancelPinch
    -- * Accessors
  , pinchGestureScale
  , pinchGestureCenter
  , pinchGestureVelocity
  , isPinchActive
  , isPinchEnded
    -- * Scale Bounds
  , clampScale
  , scaleProgress
  ) where

import Prelude

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Gestural.Gesture.Phase (GesturePhase(Possible, Began, Changed, Ended, Cancelled))
import Hydrogen.Math.Core (sqrt)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // pinch config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for pinch gesture
type PinchConfig =
  { minScale :: Number          -- ^ Minimum allowed scale (e.g., 0.5 = 50%)
  , maxScale :: Number          -- ^ Maximum allowed scale (e.g., 4.0 = 400%)
  , velocityThreshold :: Number -- ^ Minimum velocity to register gesture (px/s)
  , distanceThreshold :: Number -- ^ Minimum finger distance change to register (px)
  }

-- | Create pinch config
pinchConfig :: Number -> Number -> Number -> Number -> PinchConfig
pinchConfig minScale maxScale velocityThreshold distanceThreshold =
  { minScale: max 0.01 minScale
  , maxScale: max minScale maxScale
  , velocityThreshold
  , distanceThreshold
  }

-- | Default pinch config
-- |
-- | Scale: 0.25x to 10x
-- | Thresholds: 10 px/s velocity, 5 px distance
defaultPinchConfig :: PinchConfig
defaultPinchConfig = pinchConfig 0.25 10.0 10.0 5.0

-- | Get minimum scale
pinchMinScale :: PinchConfig -> Number
pinchMinScale pc = pc.minScale

-- | Get maximum scale
pinchMaxScale :: PinchConfig -> Number
pinchMaxScale pc = pc.maxScale

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // pinch gesture state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete pinch gesture state
type PinchGesture =
  { phase :: GesturePhase        -- ^ Gesture lifecycle phase
  , scale :: Number              -- ^ Current scale factor (1.0 = no change)
  , initialScale :: Number       -- ^ Scale when gesture began
  , centerX :: Number            -- ^ Center X between fingers
  , centerY :: Number            -- ^ Center Y between fingers
  , initialDistance :: Number    -- ^ Initial distance between fingers
  , currentDistance :: Number    -- ^ Current distance between fingers
  , velocity :: Number           -- ^ Scale change velocity (scale/s)
  , config :: PinchConfig        -- ^ Configuration
  }

-- | Create pinch gesture state
pinchGesture :: PinchConfig -> PinchGesture
pinchGesture config =
  { phase: Possible
  , scale: 1.0
  , initialScale: 1.0
  , centerX: 0.0
  , centerY: 0.0
  , initialDistance: 0.0
  , currentDistance: 0.0
  , velocity: 0.0
  , config
  }

-- | No active pinch gesture
noPinchGesture :: PinchGesture
noPinchGesture = pinchGesture defaultPinchConfig

-- | Begin pinch gesture
beginPinch 
  :: Number -> Number  -- ^ Finger 1 position
  -> Number -> Number  -- ^ Finger 2 position
  -> Number            -- ^ Current content scale
  -> PinchGesture 
  -> PinchGesture
beginPinch x1 y1 x2 y2 currentScale pg =
  let
    dx = x2 - x1
    dy = y2 - y1
    dist = sqrt (dx * dx + dy * dy)
    cx = (x1 + x2) / 2.0
    cy = (y1 + y2) / 2.0
  in pg
    { phase = Began
    , scale = currentScale
    , initialScale = currentScale
    , centerX = cx
    , centerY = cy
    , initialDistance = dist
    , currentDistance = dist
    , velocity = 0.0
    }

-- | Update pinch gesture
updatePinch 
  :: Number -> Number  -- ^ Finger 1 position
  -> Number -> Number  -- ^ Finger 2 position
  -> Number            -- ^ Time delta (ms)
  -> PinchGesture 
  -> PinchGesture
updatePinch x1 y1 x2 y2 dt pg =
  let
    dx = x2 - x1
    dy = y2 - y1
    dist = sqrt (dx * dx + dy * dy)
    cx = (x1 + x2) / 2.0
    cy = (y1 + y2) / 2.0
    
    -- Calculate new scale based on distance ratio
    scaleRatio = if pg.initialDistance > 0.0 
      then dist / pg.initialDistance 
      else 1.0
    newScale = clampScale pg.config (pg.initialScale * scaleRatio)
    
    -- Calculate velocity
    scaleDelta = newScale - pg.scale
    vel = if dt > 0.0 then (scaleDelta / dt) * 1000.0 else 0.0
  in pg
    { phase = Changed
    , scale = newScale
    , centerX = cx
    , centerY = cy
    , currentDistance = dist
    , velocity = vel
    }

-- | End pinch gesture
endPinch :: PinchGesture -> PinchGesture
endPinch pg = pg { phase = Ended }

-- | Cancel pinch gesture
cancelPinch :: PinchGesture -> PinchGesture
cancelPinch pg = pg 
  { phase = Cancelled
  , scale = pg.initialScale  -- Revert to initial scale
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current scale
pinchGestureScale :: PinchGesture -> Number
pinchGestureScale pg = pg.scale

-- | Get center point
pinchGestureCenter :: PinchGesture -> { x :: Number, y :: Number }
pinchGestureCenter pg = { x: pg.centerX, y: pg.centerY }

-- | Get scale velocity
pinchGestureVelocity :: PinchGesture -> Number
pinchGestureVelocity pg = pg.velocity

-- | Is pinch currently active?
isPinchActive :: PinchGesture -> Boolean
isPinchActive pg = pg.phase == Began || pg.phase == Changed

-- | Has pinch ended?
isPinchEnded :: PinchGesture -> Boolean
isPinchEnded pg = pg.phase == Ended || pg.phase == Cancelled

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // scale helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp scale to configured bounds
clampScale :: PinchConfig -> Number -> Number
clampScale config s = max config.minScale (min config.maxScale s)

-- | Get scale progress within bounds (0.0 to 1.0)
scaleProgress :: PinchConfig -> Number -> Number
scaleProgress config s =
  let
    clamped = clampScale config s
    range = config.maxScale - config.minScale
  in if range > 0.0 
    then (clamped - config.minScale) / range 
    else 0.0
