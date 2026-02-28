-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // gestural // hover
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hover - hover state, intent detection, and hover zones.
-- |
-- | Models hover interactions with delay for intent detection.
-- | Prevents flicker from accidental hover and enables preview UX.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Data.Maybe (Maybe)
-- | - Hydrogen.Math.Core (sqrt)
-- |
-- | ## Dependents
-- | - Component.Tooltip (delayed tooltips)
-- | - Component.Dropdown (hover-to-open)
-- | - Component.Preview (hover previews)
-- | - Gestural.Trigger (hover triggers)

module Hydrogen.Schema.Gestural.Hover
  ( -- * Hover Phase
    HoverPhase(HoverNone, HoverEnter, HoverIntent, HoverActive, HoverLeave)
  , isHovering
  , hasHoverIntent
    -- * Hover Intent Config
  , HoverIntentConfig
  , defaultHoverIntent
  , hoverIntentConfig
  , intentDelay
  , intentSensitivity
  , intentInterval
    -- * Hover Zone
  , HoverZone
  , hoverZone
  , expandedZone
  , zoneContainsPoint
  , zonePadding
    -- * Hover Group
  , HoverGroup
  , hoverGroup
  , groupId
  , groupElements
  , groupDelay
  , addToGroup
  , removeFromGroup
  , isGroupHovered
    -- * Pointer Tracking
  , PointerTrack
  , initialTrack
  , updateTrack
  , trackVelocity
  , trackDirection
  , isPointerSlowing
  , isPointerStopped
    -- * Hover State
  , HoverState
  , initialHoverState
  , currentHover
  , hoverPhase
  , hoverDuration
  , isHoverActive
  , enterHover
  , confirmHoverIntent
  , leaveHover
  , cancelHover
  ) where

import Prelude

import Data.Array (elem, filter, length, snoc)
import Data.Maybe (Maybe(Just, Nothing), isJust)
import Hydrogen.Math.Core (sqrt)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // hover // phase
-- ═════════════════════════════════════════════════════════════════════════════

-- | Phase of hover interaction
data HoverPhase
  = HoverNone     -- ^ Not hovering
  | HoverEnter    -- ^ Just entered, waiting for intent
  | HoverIntent   -- ^ Intent delay passed, hover confirmed
  | HoverActive   -- ^ Actively hovering
  | HoverLeave    -- ^ Leaving (grace period)

derive instance eqHoverPhase :: Eq HoverPhase
derive instance ordHoverPhase :: Ord HoverPhase

instance showHoverPhase :: Show HoverPhase where
  show HoverNone = "none"
  show HoverEnter = "enter"
  show HoverIntent = "intent"
  show HoverActive = "active"
  show HoverLeave = "leave"

-- | Is currently hovering (any active phase)?
isHovering :: HoverPhase -> Boolean
isHovering HoverNone = false
isHovering HoverLeave = false
isHovering _ = true

-- | Has hover intent been confirmed?
hasHoverIntent :: HoverPhase -> Boolean
hasHoverIntent HoverIntent = true
hasHoverIntent HoverActive = true
hasHoverIntent _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // hover // intent config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for hover intent detection
-- |
-- | Based on hoverIntent jQuery plugin algorithm:
-- | - Track pointer movement over interval
-- | - Compare against sensitivity threshold
-- | - Trigger intent after delay if movement is slow
type HoverIntentConfig =
  { delay :: Number         -- ^ Delay before confirming intent (ms)
  , sensitivity :: Number   -- ^ Movement threshold (pixels)
  , interval :: Number      -- ^ Check interval (ms)
  , leaveDelay :: Number    -- ^ Grace period on leave (ms)
  }

-- | Default hover intent config
defaultHoverIntent :: HoverIntentConfig
defaultHoverIntent =
  { delay: 200.0
  , sensitivity: 7.0
  , interval: 100.0
  , leaveDelay: 200.0
  }

-- | Create custom hover intent config
hoverIntentConfig :: Number -> Number -> Number -> Number -> HoverIntentConfig
hoverIntentConfig delay sensitivity interval leaveDelay =
  { delay, sensitivity, interval, leaveDelay }

-- | Get intent delay
intentDelay :: HoverIntentConfig -> Number
intentDelay hic = hic.delay

-- | Get sensitivity threshold
intentSensitivity :: HoverIntentConfig -> Number
intentSensitivity hic = hic.sensitivity

-- | Get check interval
intentInterval :: HoverIntentConfig -> Number
intentInterval hic = hic.interval

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // hover // zone
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extended hover zone around element
type HoverZone =
  { x :: Number           -- ^ Zone left edge
  , y :: Number           -- ^ Zone top edge
  , width :: Number       -- ^ Zone width
  , height :: Number      -- ^ Zone height
  , padding :: Number     -- ^ Extra padding beyond element
  }

-- | Create hover zone from element bounds
hoverZone :: Number -> Number -> Number -> Number -> HoverZone
hoverZone x y width height =
  { x, y, width, height, padding: 0.0 }

-- | Create expanded hover zone with padding
expandedZone :: Number -> Number -> Number -> Number -> Number -> HoverZone
expandedZone x y width height padding =
  { x: x - padding
  , y: y - padding
  , width: width + padding * 2.0
  , height: height + padding * 2.0
  , padding
  }

-- | Does zone contain point?
zoneContainsPoint :: { x :: Number, y :: Number } -> HoverZone -> Boolean
zoneContainsPoint p hz =
  p.x >= hz.x && p.x <= hz.x + hz.width
  && p.y >= hz.y && p.y <= hz.y + hz.height

-- | Get zone padding
zonePadding :: HoverZone -> Number
zonePadding hz = hz.padding

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // hover // group
-- ═════════════════════════════════════════════════════════════════════════════

-- | Group of elements that share hover state
-- |
-- | Used for menus where hovering submenu should maintain parent hover.
type HoverGroup =
  { id :: String              -- ^ Group identifier
  , elements :: Array String  -- ^ Element IDs in group
  , delay :: Number           -- ^ Delay before closing on leave
  , hoveredElement :: Maybe String  -- ^ Currently hovered element
  }

-- | Create hover group
hoverGroup :: String -> Number -> HoverGroup
hoverGroup id delay =
  { id
  , elements: []
  , delay
  , hoveredElement: Nothing
  }

-- | Get group ID
groupId :: HoverGroup -> String
groupId hg = hg.id

-- | Get group elements
groupElements :: HoverGroup -> Array String
groupElements hg = hg.elements

-- | Get group delay
groupDelay :: HoverGroup -> Number
groupDelay hg = hg.delay

-- | Add element to group
addToGroup :: String -> HoverGroup -> HoverGroup
addToGroup elemId hg =
  hg { elements = snoc hg.elements elemId }

-- | Remove element from group
removeFromGroup :: String -> HoverGroup -> HoverGroup
removeFromGroup elemId hg =
  hg { elements = filter (_ /= elemId) hg.elements }

-- | Is any element in group hovered?
isGroupHovered :: HoverGroup -> Boolean
isGroupHovered hg = isJust hg.hoveredElement

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // pointer // tracking
-- ═════════════════════════════════════════════════════════════════════════════

-- | Track pointer position for velocity calculation
type PointerTrack =
  { prevX :: Number       -- ^ Previous X position
  , prevY :: Number       -- ^ Previous Y position
  , currentX :: Number    -- ^ Current X position
  , currentY :: Number    -- ^ Current Y position
  , prevTime :: Number    -- ^ Previous timestamp
  , currentTime :: Number -- ^ Current timestamp
  }

-- | Initial pointer track
initialTrack :: Number -> Number -> Number -> PointerTrack
initialTrack x y time =
  { prevX: x
  , prevY: y
  , currentX: x
  , currentY: y
  , prevTime: time
  , currentTime: time
  }

-- | Update pointer track
updateTrack :: Number -> Number -> Number -> PointerTrack -> PointerTrack
updateTrack x y time pt =
  { prevX: pt.currentX
  , prevY: pt.currentY
  , currentX: x
  , currentY: y
  , prevTime: pt.currentTime
  , currentTime: time
  }

-- | Calculate pointer velocity (pixels/ms)
trackVelocity :: PointerTrack -> Number
trackVelocity pt =
  let
    dx = pt.currentX - pt.prevX
    dy = pt.currentY - pt.prevY
    dt = pt.currentTime - pt.prevTime
  in if dt > 0.0
    then sqrt (dx * dx + dy * dy) / dt
    else 0.0

-- | Calculate pointer direction (radians)
trackDirection :: PointerTrack -> Number
trackDirection pt =
  let
    dx = pt.currentX - pt.prevX
    dy = pt.currentY - pt.prevY
  in atan2Approx dy dx
  where
    -- Simple atan2 approximation
    atan2Approx :: Number -> Number -> Number
    atan2Approx y x
      | x > 0.0 = atanApprox (y / x)
      | x < 0.0 && y >= 0.0 = atanApprox (y / x) + 3.14159
      | x < 0.0 && y < 0.0 = atanApprox (y / x) - 3.14159
      | x == 0.0 && y > 0.0 = 1.5708
      | x == 0.0 && y < 0.0 = (-1.5708)
      | otherwise = 0.0
    atanApprox :: Number -> Number
    atanApprox z = z / (1.0 + 0.28 * z * z)

-- | Is pointer slowing down?
isPointerSlowing :: Number -> PointerTrack -> Boolean
isPointerSlowing threshold pt = trackVelocity pt < threshold

-- | Is pointer essentially stopped?
isPointerStopped :: PointerTrack -> Boolean
isPointerStopped pt = trackVelocity pt < 0.01

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // hover // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete hover state
type HoverState =
  { phase :: HoverPhase             -- ^ Current hover phase
  , elementId :: Maybe String       -- ^ Currently hovered element
  , enterTime :: Number             -- ^ When hover started
  , lastMoveTime :: Number          -- ^ Last pointer movement
  , config :: HoverIntentConfig     -- ^ Intent detection config
  , track :: Maybe PointerTrack     -- ^ Pointer tracking
  }

-- | Initial hover state
initialHoverState :: HoverIntentConfig -> HoverState
initialHoverState config =
  { phase: HoverNone
  , elementId: Nothing
  , enterTime: 0.0
  , lastMoveTime: 0.0
  , config
  , track: Nothing
  }

-- | Get currently hovered element
currentHover :: HoverState -> Maybe String
currentHover hs = hs.elementId

-- | Get current hover phase
hoverPhase :: HoverState -> HoverPhase
hoverPhase hs = hs.phase

-- | Get hover duration (ms since enter)
hoverDuration :: Number -> HoverState -> Number
hoverDuration currentTime hs =
  if hs.phase == HoverNone then 0.0
  else currentTime - hs.enterTime

-- | Is hover currently active?
isHoverActive :: HoverState -> Boolean
isHoverActive hs = hasHoverIntent hs.phase

-- | Enter hover on element
enterHover :: String -> Number -> Number -> Number -> HoverState -> HoverState
enterHover elemId x y time hs =
  hs { phase = HoverEnter
     , elementId = Just elemId
     , enterTime = time
     , lastMoveTime = time
     , track = Just (initialTrack x y time)
     }

-- | Confirm hover intent (after delay)
confirmHoverIntent :: Number -> HoverState -> HoverState
confirmHoverIntent time hs =
  hs { phase = HoverActive, lastMoveTime = time }

-- | Leave hover
leaveHover :: Number -> HoverState -> HoverState
leaveHover time hs =
  hs { phase = HoverLeave, lastMoveTime = time }

-- | Cancel hover completely
cancelHover :: HoverState -> HoverState
cancelHover hs =
  hs { phase = HoverNone
     , elementId = Nothing
     , track = Nothing
     }
