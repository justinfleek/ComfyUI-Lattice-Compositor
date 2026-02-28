-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // element // tour // motion // choreography
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tooltip Choreography — Entrance, exit, and follow animations.
-- |
-- | ## Overview
-- |
-- | Tooltips don't just "appear" — they're choreographed to create spatial
-- | continuity and guide the user's attention. This module defines the
-- | complete animation lifecycle for tour tooltips.
-- |
-- | ## Design Philosophy
-- |
-- | - Entry: Tooltip slides in from the direction of its arrow
-- | - Exit: Tooltip anticipates the next target's direction
-- | - Follow: Tooltip smoothly tracks scrolling targets
-- | - Micro-interactions: Buttons respond to hover and focus
-- |
-- | Each preset is tuned for different contexts:
-- | - Default: Balanced for most use cases
-- | - Minimal: Fast, for reduced motion or power users
-- | - Dramatic: Attention-grabbing for onboarding

module Hydrogen.Element.Compound.Tour.Motion.Choreography
  ( -- * Configuration
    TooltipChoreography
  , MicroInteractionConfig
  
    -- * Phases
  , ChoreographyPhase(..)
  
    -- * Presets
  , defaultChoreography
  , minimalChoreography
  , dramaticChoreography
  , defaultMicroInteractions
  
    -- * Computation
  , computeEntryAnimation
  , computeExitAnimation
  , computeFollowBehavior
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , negate
  , show
  , (*)
  , (+)
  , (-)
  , (<>)
  , (>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Math.Core as Math
import Hydrogen.Element.Compound.Tour.Types 
  ( Placement
  , Side(SideTop, SideRight, SideBottom, SideLeft)
  , placementToSide
  )
import Hydrogen.Element.Compound.Tour.Motion.Spring
  ( SpringParams
  , snappySpring
  , bouncySpring
  , smoothSpring
  , preciseSpring
  , criticallyDamped
  , springToCss
  , springDuration
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete choreography configuration for tooltip animations.
-- |
-- | Controls every aspect of tooltip animation lifecycle.
type TooltipChoreography =
  { entryDuration :: Number
    -- ^ Entry animation duration (ms)
  , exitDuration :: Number
    -- ^ Exit animation duration (ms)
  , entryDelay :: Number
    -- ^ Delay before entry starts (ms) — allows spotlight to settle
  , entrySpring :: SpringParams
    -- ^ Spring for entry animation
  , exitSpring :: SpringParams
    -- ^ Spring for exit animation
  , entryDistance :: Number
    -- ^ Starting offset distance (px)
  , scaleFrom :: Number
    -- ^ Initial scale (1.0 = no scale, 0.8 = scale up from 80%)
  , opacityDuration :: Number
    -- ^ Fade duration, independent of transform (ms)
  , arrowAnimates :: Boolean
    -- ^ Whether arrow animates separately
  , arrowDelay :: Number
    -- ^ Arrow animation delay after body (ms)
  , followScroll :: Boolean
    -- ^ Whether tooltip follows target during scroll
  , followSpring :: SpringParams
    -- ^ Spring for scroll-following
  , microInteractions :: MicroInteractionConfig
    -- ^ Button hover states, etc.
  }

-- | Micro-interaction configuration for tooltip buttons and controls.
type MicroInteractionConfig =
  { buttonHoverScale :: Number
    -- ^ Button scale on hover (1.02 = subtle)
  , buttonActiveScale :: Number
    -- ^ Button scale when pressed (0.98 = subtle press)
  , buttonTransition :: Number
    -- ^ Button transition duration (ms)
  , focusRingSpread :: Number
    -- ^ Focus ring spread animation (px)
  , focusRingDuration :: Number
    -- ^ Focus ring animation duration (ms)
  }

-- | Animation phase for choreography state tracking.
data ChoreographyPhase
  = PhaseIdle           -- ^ Not animating
  | PhaseEntering       -- ^ Entry animation in progress
  | PhaseVisible        -- ^ Fully visible, awaiting interaction
  | PhaseExiting        -- ^ Exit animation in progress
  | PhaseFollowing      -- ^ Following scroll/resize

derive instance eqChoreographyPhase :: Eq ChoreographyPhase

instance showChoreographyPhase :: Show ChoreographyPhase where
  show PhaseIdle = "idle"
  show PhaseEntering = "entering"
  show PhaseVisible = "visible"
  show PhaseExiting = "exiting"
  show PhaseFollowing = "following"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default choreography — balanced and professional.
defaultChoreography :: TooltipChoreography
defaultChoreography =
  { entryDuration: 350.0
  , exitDuration: 250.0
  , entryDelay: 100.0
  , entrySpring: smoothSpring
  , exitSpring: snappySpring
  , entryDistance: 16.0
  , scaleFrom: 0.95
  , opacityDuration: 200.0
  , arrowAnimates: true
  , arrowDelay: 50.0
  , followScroll: true
  , followSpring: preciseSpring
  , microInteractions: defaultMicroInteractions
  }

-- | Minimal choreography — for reduced motion or fast tours.
minimalChoreography :: TooltipChoreography
minimalChoreography =
  { entryDuration: 150.0
  , exitDuration: 100.0
  , entryDelay: 0.0
  , entrySpring: criticallyDamped
  , exitSpring: criticallyDamped
  , entryDistance: 0.0
  , scaleFrom: 1.0
  , opacityDuration: 150.0
  , arrowAnimates: false
  , arrowDelay: 0.0
  , followScroll: true
  , followSpring: preciseSpring
  , microInteractions: minimalMicroInteractions
  }

-- | Dramatic choreography — for first-time onboarding.
dramaticChoreography :: TooltipChoreography
dramaticChoreography =
  { entryDuration: 500.0
  , exitDuration: 350.0
  , entryDelay: 200.0
  , entrySpring: bouncySpring
  , exitSpring: smoothSpring
  , entryDistance: 24.0
  , scaleFrom: 0.85
  , opacityDuration: 300.0
  , arrowAnimates: true
  , arrowDelay: 100.0
  , followScroll: true
  , followSpring: smoothSpring
  , microInteractions: dramaticMicroInteractions
  }

-- | Default micro-interactions.
defaultMicroInteractions :: MicroInteractionConfig
defaultMicroInteractions =
  { buttonHoverScale: 1.02
  , buttonActiveScale: 0.98
  , buttonTransition: 150.0
  , focusRingSpread: 3.0
  , focusRingDuration: 200.0
  }

-- | Minimal micro-interactions (for reduced motion).
minimalMicroInteractions :: MicroInteractionConfig
minimalMicroInteractions =
  { buttonHoverScale: 1.0
  , buttonActiveScale: 1.0
  , buttonTransition: 0.0
  , focusRingSpread: 2.0
  , focusRingDuration: 0.0
  }

-- | Dramatic micro-interactions (for onboarding).
dramaticMicroInteractions :: MicroInteractionConfig
dramaticMicroInteractions =
  { buttonHoverScale: 1.05
  , buttonActiveScale: 0.95
  , buttonTransition: 200.0
  , focusRingSpread: 4.0
  , focusRingDuration: 300.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // computation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute entry animation properties based on placement.
-- |
-- | The tooltip slides in from the direction opposite its arrow.
computeEntryAnimation
  :: Placement
  -> TooltipChoreography
  -> { translateX :: Number, translateY :: Number, scale :: Number, opacity :: Number }
computeEntryAnimation placement choreo =
  let
    distance = choreo.entryDistance
    
    -- Direction based on placement side
    translate = case extractSide placement of
      SideTop -> { x: 0.0, y: distance }        -- Slides down from above
      SideBottom -> { x: 0.0, y: negate distance } -- Slides up from below
      SideLeft -> { x: distance, y: 0.0 }       -- Slides right from left
      SideRight -> { x: negate distance, y: 0.0 }  -- Slides left from right
  in
    { translateX: translate.x
    , translateY: translate.y
    , scale: choreo.scaleFrom
    , opacity: 0.0
    }

-- | Compute exit animation based on next step's direction.
-- |
-- | If there's a next target, exit toward it. Otherwise, exit based on placement.
computeExitAnimation
  :: Placement                           -- ^ Current tooltip placement
  -> Maybe { x :: Number, y :: Number }  -- ^ Next target position (Nothing = tour ending)
  -> TooltipChoreography
  -> { translateX :: Number, translateY :: Number, scale :: Number, opacity :: Number }
computeExitAnimation currentPlacement nextTarget choreo =
  case nextTarget of
    -- Exit toward next target
    Just target ->
      let
        dirX = if target.x > 0.0 then negate 8.0 else 8.0
        dirY = if target.y > 0.0 then negate 8.0 else 8.0
      in
        { translateX: dirX
        , translateY: dirY
        , scale: 0.98
        , opacity: 0.0
        }
    -- Tour ending — exit based on placement
    Nothing ->
      let
        distance = choreo.entryDistance * 0.5
        translate = case extractSide currentPlacement of
          SideTop -> { x: 0.0, y: negate distance }
          SideBottom -> { x: 0.0, y: distance }
          SideLeft -> { x: negate distance, y: 0.0 }
          SideRight -> { x: distance, y: 0.0 }
      in
        { translateX: translate.x
        , translateY: translate.y
        , scale: 0.95
        , opacity: 0.0
        }

-- | Compute follow behavior during scroll.
-- |
-- | Returns the target position and an optimized CSS transition string.
-- | The transition is dampened based on the distance moved to prevent
-- | overly bouncy behavior during rapid scroll events.
computeFollowBehavior
  :: { targetX :: Number, targetY :: Number }
  -> { currentX :: Number, currentY :: Number }
  -> TooltipChoreography
  -> { x :: Number, y :: Number, transition :: String }
computeFollowBehavior target current choreo =
  let
    spring = choreo.followSpring
    
    -- Calculate distance for adaptive dampening
    dx = target.targetX - current.currentX
    dy = target.targetY - current.currentY
    distance = Math.sqrt (dx * dx + dy * dy)
    
    -- For large movements, use faster transition to prevent lag
    adaptedDuration = if distance > 100.0
      then springDuration spring * 0.6
      else springDuration spring
    
    easing = springToCss spring
  in
    { x: target.targetX
    , y: target.targetY
    , transition: "transform " <> show adaptedDuration <> "ms " <> easing
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract side from placement.
extractSide :: Placement -> Side
extractSide = placementToSide
