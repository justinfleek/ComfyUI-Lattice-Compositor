-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // element // treeview // animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Animation — Motion and transitions for tree visualization.
-- |
-- | ## Animation Categories
-- |
-- | **Node Transitions**:
-- | - Expand/collapse with smooth height animation
-- | - Selection highlight transitions
-- | - Focus movement between nodes
-- |
-- | **Layout Transitions**:
-- | - Node position changes when tree restructures
-- | - Zoom and pan with inertia
-- | - Layout algorithm switches
-- |
-- | **State Transitions**:
-- | - Loading states (skeleton, spinner)
-- | - Drag-drop visual feedback
-- | - Connection line animations (draw, flow)
-- |
-- | ## Dependencies
-- |
-- | - Schema.Motion (Timecode, Easing)
-- | - Schema.Graph.Connection (ConnectionAnimation)

module Hydrogen.Element.Compound.TreeView.Animation
  ( -- * Animation State
    AnimationState
  , animationState
  , initialAnimation
  , isAnimating
  , animationProgress
  
  -- * Expand/Collapse Animation
  , ExpandAnimation
  , expandAnimation
  , collapseAnimation
  , toggleAnimation
  , expandProgress
  , isExpandComplete
  
  -- * Position Animation
  , PositionAnimation
  , positionAnimation
  , animatePosition
  , currentPosition
  , targetPosition
  , positionProgress
  
  -- * Selection Animation
  , SelectionAnimation
  , selectAnimation
  , deselectAnimation
  , selectionOpacity
  
  -- * Focus Animation
  , FocusAnimation
  , focusAnimation
  , focusProgress
  , focusRingScale
  
  -- * Layout Transition
  , LayoutTransition
  , layoutTransition
  , transitionProgress
  , interpolatePosition
  
  -- * Animation Config
  , AnimationConfig
  , animationConfig
  , defaultAnimationConfig
  , fastAnimations
  , slowAnimations
  , noAnimations
  , withDuration
  , withEasing
  
  -- * Easing Functions
  , Easing(Linear, EaseIn, EaseOut, EaseInOut, EaseSpring, EaseBounce, EaseElastic)
  , easeLinear
  , easeInOut
  , easeOut
  , easeSpring
  , applyEasing
  
  -- * Animation Updates
  , updateAnimations
  , stepAnimation
  , cancelAnimation
  , completeAnimation
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (-)
  , (+)
  , (/)
  , (*)
  , (>)
  , (>=)
  , (<)
  , (&&)
  , max
  , min
  )

import Hydrogen.Element.Compound.TreeView.Types
  ( NodeId
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // easing types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Easing function type
data Easing
  = Linear              -- ^ Constant speed
  | EaseIn              -- ^ Start slow, end fast
  | EaseOut             -- ^ Start fast, end slow
  | EaseInOut           -- ^ Slow at both ends
  | EaseSpring Number   -- ^ Spring physics with tension
  | EaseBounce          -- ^ Bounce at end
  | EaseElastic         -- ^ Elastic overshoot

derive instance eqEasing :: Eq Easing

instance showEasing :: Show Easing where
  show Linear = "linear"
  show EaseIn = "ease-in"
  show EaseOut = "ease-out"
  show EaseInOut = "ease-in-out"
  show (EaseSpring t) = "spring(" <> show t <> ")"
  show EaseBounce = "bounce"
  show EaseElastic = "elastic"

-- | Linear easing
easeLinear :: Easing
easeLinear = Linear

-- | Ease in-out (smooth)
easeInOut :: Easing
easeInOut = EaseInOut

-- | Ease out (decelerate)
easeOut :: Easing
easeOut = EaseOut

-- | Spring physics
easeSpring :: Number -> Easing
easeSpring = EaseSpring

-- | Apply easing function to progress value (0-1)
applyEasing :: Easing -> Number -> Number
applyEasing easing t =
  let
    clampedT = max 0.0 (min 1.0 t)
  in
    case easing of
      Linear -> clampedT
      EaseIn -> clampedT * clampedT
      EaseOut -> 1.0 - (1.0 - clampedT) * (1.0 - clampedT)
      EaseInOut ->
        if clampedT < 0.5
          then 2.0 * clampedT * clampedT
          else 1.0 - 2.0 * (1.0 - clampedT) * (1.0 - clampedT)
      EaseSpring tension ->
        -- Simplified spring approximation
        let overshoot = 1.0 + tension * 0.1 * (1.0 - clampedT)
        in clampedT * overshoot
      EaseBounce ->
        -- Simplified bounce
        if clampedT < 0.9
          then clampedT / 0.9
          else 1.0 - (clampedT - 0.9) * 2.0 * (1.0 - clampedT) * 10.0
      EaseElastic ->
        -- Simplified elastic
        if clampedT >= 1.0
          then 1.0
          else clampedT * (1.0 + 0.3 * (1.0 - clampedT))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // animation state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generic animation state
type AnimationState =
  { active :: Boolean
  , progress :: Number      -- ^ 0.0 to 1.0
  , duration :: Number      -- ^ Total duration in ms
  , elapsed :: Number       -- ^ Elapsed time in ms
  , easing :: Easing
  }

-- | Create animation state
animationState :: Number -> Easing -> AnimationState
animationState duration easing =
  { active: true
  , progress: 0.0
  , duration
  , elapsed: 0.0
  , easing
  }

-- | Initial (not animating) state
initialAnimation :: AnimationState
initialAnimation =
  { active: false
  , progress: 1.0
  , duration: 0.0
  , elapsed: 0.0
  , easing: Linear
  }

-- | Check if animation is active
isAnimating :: AnimationState -> Boolean
isAnimating a = a.active && a.progress < 1.0

-- | Get eased progress value
animationProgress :: AnimationState -> Number
animationProgress a = applyEasing a.easing a.progress

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // expand/collapse animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation for expand/collapse
type ExpandAnimation =
  { nodeId :: NodeId
  , expanding :: Boolean    -- ^ true = expanding, false = collapsing
  , animation :: AnimationState
  }

-- | Create expand animation
expandAnimation :: NodeId -> Number -> ExpandAnimation
expandAnimation nodeId duration =
  { nodeId
  , expanding: true
  , animation: animationState duration EaseOut
  }

-- | Create collapse animation
collapseAnimation :: NodeId -> Number -> ExpandAnimation
collapseAnimation nodeId duration =
  { nodeId
  , expanding: false
  , animation: animationState duration EaseOut
  }

-- | Toggle between expand and collapse
toggleAnimation :: Boolean -> NodeId -> Number -> ExpandAnimation
toggleAnimation expanding nodeId duration =
  if expanding
    then expandAnimation nodeId duration
    else collapseAnimation nodeId duration

-- | Get expand progress (0 = collapsed, 1 = expanded)
expandProgress :: ExpandAnimation -> Number
expandProgress ea =
  let
    rawProgress = animationProgress ea.animation
  in
    if ea.expanding then rawProgress else 1.0 - rawProgress

-- | Check if expand animation is complete
isExpandComplete :: ExpandAnimation -> Boolean
isExpandComplete ea = ea.animation.progress >= 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // position animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation for node position changes
type PositionAnimation =
  { nodeId :: NodeId
  , fromX :: Number
  , fromY :: Number
  , toX :: Number
  , toY :: Number
  , animation :: AnimationState
  }

-- | Create position animation
positionAnimation :: NodeId -> Number -> Number -> Number -> Number -> Number -> PositionAnimation
positionAnimation nodeId fromX fromY toX toY duration =
  { nodeId
  , fromX
  , fromY
  , toX
  , toY
  , animation: animationState duration EaseInOut
  }

-- | Start animating to a new position
animatePosition :: NodeId -> Number -> Number -> Number -> PositionAnimation -> PositionAnimation
animatePosition _nodeId newX newY duration pa =
  -- Use current interpolated position as new start
  let
    current = currentPosition pa
  in
    { nodeId: pa.nodeId
    , fromX: current.x
    , fromY: current.y
    , toX: newX
    , toY: newY
    , animation: animationState duration EaseInOut
    }

-- | Get current interpolated position
currentPosition :: PositionAnimation -> { x :: Number, y :: Number }
currentPosition pa =
  let
    t = animationProgress pa.animation
    x = pa.fromX + (pa.toX - pa.fromX) * t
    y = pa.fromY + (pa.toY - pa.fromY) * t
  in
    { x, y }

-- | Get target position
targetPosition :: PositionAnimation -> { x :: Number, y :: Number }
targetPosition pa = { x: pa.toX, y: pa.toY }

-- | Get raw position progress
positionProgress :: PositionAnimation -> Number
positionProgress pa = animationProgress pa.animation

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // selection animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation for selection state changes
type SelectionAnimation =
  { nodeId :: NodeId
  , selecting :: Boolean    -- ^ true = selecting, false = deselecting
  , animation :: AnimationState
  }

-- | Create select animation
selectAnimation :: NodeId -> Number -> SelectionAnimation
selectAnimation nodeId duration =
  { nodeId
  , selecting: true
  , animation: animationState duration EaseOut
  }

-- | Create deselect animation
deselectAnimation :: NodeId -> Number -> SelectionAnimation
deselectAnimation nodeId duration =
  { nodeId
  , selecting: false
  , animation: animationState duration EaseOut
  }

-- | Get selection opacity (for highlight)
selectionOpacity :: SelectionAnimation -> Number
selectionOpacity sa =
  let
    rawProgress = animationProgress sa.animation
  in
    if sa.selecting then rawProgress else 1.0 - rawProgress

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // focus animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation for focus ring
type FocusAnimation =
  { nodeId :: NodeId
  , animation :: AnimationState
  }

-- | Create focus animation
focusAnimation :: NodeId -> Number -> FocusAnimation
focusAnimation nodeId duration =
  { nodeId
  , animation: animationState duration EaseOut
  }

-- | Get focus progress
focusProgress :: FocusAnimation -> Number
focusProgress fa = animationProgress fa.animation

-- | Get focus ring scale (for pulse effect)
focusRingScale :: FocusAnimation -> Number
focusRingScale fa =
  let
    t = animationProgress fa.animation
  in
    1.0 + 0.1 * t  -- Scale from 1.0 to 1.1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // layout transition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transition between layout states
type LayoutTransition =
  { animation :: AnimationState
  }

-- | Create layout transition
layoutTransition :: Number -> LayoutTransition
layoutTransition duration =
  { animation: animationState duration EaseInOut }

-- | Get transition progress
transitionProgress :: LayoutTransition -> Number
transitionProgress lt = animationProgress lt.animation

-- | Interpolate between old and new position
interpolatePosition ::
  LayoutTransition ->
  { x :: Number, y :: Number } ->  -- old position
  { x :: Number, y :: Number } ->  -- new position
  { x :: Number, y :: Number }     -- interpolated
interpolatePosition lt oldPos newPos =
  let
    t = transitionProgress lt
    x = oldPos.x + (newPos.x - oldPos.x) * t
    y = oldPos.y + (newPos.y - oldPos.y) * t
  in
    { x, y }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // animation config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for animation timing
type AnimationConfig =
  { expandDuration :: Number        -- ^ ms for expand/collapse
  , selectDuration :: Number        -- ^ ms for selection highlight
  , focusDuration :: Number         -- ^ ms for focus ring
  , layoutDuration :: Number        -- ^ ms for layout transitions
  , positionDuration :: Number      -- ^ ms for node position changes
  , defaultEasing :: Easing
  , enabled :: Boolean              -- ^ false = skip all animations
  }

-- | Create animation config
animationConfig :: Number -> Easing -> AnimationConfig
animationConfig duration easing =
  { expandDuration: duration
  , selectDuration: duration * 0.5
  , focusDuration: duration * 0.3
  , layoutDuration: duration * 2.0
  , positionDuration: duration
  , defaultEasing: easing
  , enabled: true
  }

-- | Default animation config (200ms, ease-out)
defaultAnimationConfig :: AnimationConfig
defaultAnimationConfig = animationConfig 200.0 EaseOut

-- | Fast animations (100ms)
fastAnimations :: AnimationConfig
fastAnimations = animationConfig 100.0 EaseOut

-- | Slow animations (400ms)
slowAnimations :: AnimationConfig
slowAnimations = animationConfig 400.0 EaseInOut

-- | Disable all animations
noAnimations :: AnimationConfig
noAnimations = (animationConfig 0.0 Linear) { enabled = false }

-- | Set duration
withDuration :: Number -> AnimationConfig -> AnimationConfig
withDuration d c = c
  { expandDuration = d
  , selectDuration = d * 0.5
  , focusDuration = d * 0.3
  , layoutDuration = d * 2.0
  , positionDuration = d
  }

-- | Set easing
withEasing :: Easing -> AnimationConfig -> AnimationConfig
withEasing e c = c { defaultEasing = e }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // animation updates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Update an animation by delta time
updateAnimations :: Number -> AnimationState -> AnimationState
updateAnimations deltaMs a =
  if a.active && a.progress < 1.0
    then
      let
        newElapsed = a.elapsed + deltaMs
        newProgress = if a.duration > 0.0 
                      then min 1.0 (newElapsed / a.duration)
                      else 1.0
        newActive = newProgress < 1.0
      in
        a { elapsed = newElapsed
          , progress = newProgress
          , active = newActive
          }
    else
      a

-- | Step animation (same as updateAnimations)
stepAnimation :: Number -> AnimationState -> AnimationState
stepAnimation = updateAnimations

-- | Cancel animation (reset to start)
cancelAnimation :: AnimationState -> AnimationState
cancelAnimation a = a { active = false, progress = 0.0, elapsed = 0.0 }

-- | Complete animation immediately
completeAnimation :: AnimationState -> AnimationState
completeAnimation a = a { active = false, progress = 1.0, elapsed = a.duration }
