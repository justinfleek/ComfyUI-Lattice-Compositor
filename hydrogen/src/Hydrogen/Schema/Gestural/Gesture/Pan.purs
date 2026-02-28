-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // gestural // gesture // pan
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pan - continuous drag gesture recognition.
-- |
-- | Models continuous drag movements with velocity tracking.
-- | Unlike swipe, pan fires continuously while dragging.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Hydrogen.Math.Core (sqrt)
-- | - Gestural.Gesture.Phase (GesturePhase, isActive)
-- |
-- | ## Dependents
-- | - Gestural.Gesture (re-exports)
-- | - Component.* (pan-enabled components)
-- | - Interaction.Draggable (uses PanState)

module Hydrogen.Schema.Gestural.Gesture.Pan
  ( -- * Pan State
    PanState
  , panState
  , noPan
  , updatePanPosition
  , panTranslation
  , panVelocity
  , isPanning
  , panDistance
  ) where

import Prelude

import Hydrogen.Math.Core (sqrt)
import Hydrogen.Schema.Gestural.Gesture.Phase 
  ( GesturePhase(Possible)
  , isActive
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // pan // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State of a pan (drag) gesture recognizer
-- |
-- | Pan is a continuous gesture tracking finger/cursor movement.
-- | Unlike swipe, pan fires continuously while dragging.
type PanState =
  { phase :: GesturePhase       -- ^ Current recognition phase
  , startX :: Number            -- ^ Start X position
  , startY :: Number            -- ^ Start Y position
  , currentX :: Number          -- ^ Current X position
  , currentY :: Number          -- ^ Current Y position
  , translationX :: Number      -- ^ Total X translation from start
  , translationY :: Number      -- ^ Total Y translation from start
  , velocityX :: Number         -- ^ Current X velocity (px/ms)
  , velocityY :: Number         -- ^ Current Y velocity (px/ms)
  , timestamp :: Number         -- ^ Last update timestamp
  }

-- | Create pan state
panState :: GesturePhase -> Number -> Number -> PanState
panState phase startX startY =
  { phase
  , startX
  , startY
  , currentX: startX
  , currentY: startY
  , translationX: 0.0
  , translationY: 0.0
  , velocityX: 0.0
  , velocityY: 0.0
  , timestamp: 0.0
  }

-- | No pan active
noPan :: PanState
noPan =
  { phase: Possible
  , startX: 0.0
  , startY: 0.0
  , currentX: 0.0
  , currentY: 0.0
  , translationX: 0.0
  , translationY: 0.0
  , velocityX: 0.0
  , velocityY: 0.0
  , timestamp: 0.0
  }

-- | Update pan position
updatePanPosition :: Number -> Number -> Number -> PanState -> PanState
updatePanPosition x y ts ps =
  let dt = ts - ps.timestamp
      vx = if dt > 0.0 then (x - ps.currentX) / dt else 0.0
      vy = if dt > 0.0 then (y - ps.currentY) / dt else 0.0
  in ps 
    { currentX = x
    , currentY = y
    , translationX = x - ps.startX
    , translationY = y - ps.startY
    , velocityX = vx
    , velocityY = vy
    , timestamp = ts
    }

-- | Get pan translation
panTranslation :: PanState -> { x :: Number, y :: Number }
panTranslation ps = { x: ps.translationX, y: ps.translationY }

-- | Get pan velocity magnitude
panVelocity :: PanState -> Number
panVelocity ps = sqrt (ps.velocityX * ps.velocityX + ps.velocityY * ps.velocityY)

-- | Is pan gesture active?
isPanning :: PanState -> Boolean
isPanning ps = isActive ps.phase

-- | Get distance traveled during pan
panDistance :: PanState -> Number
panDistance ps = sqrt (ps.translationX * ps.translationX + ps.translationY * ps.translationY)
