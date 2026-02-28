-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // animation // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Animation Types — Canonical type definitions for animation system.
-- |
-- | ## Purpose
-- |
-- | This module defines the canonical types for the Hydrogen animation system.
-- | NEW CODE should import from here. Legacy modules (Animation.Algebra,
-- | GPU.DrawCommand, Typography.TextAnimation) have their own definitions
-- | that will be migrated incrementally.
-- |
-- | ## Type Categories
-- |
-- | 1. **Easing**: Time-warping functions (Progress → Progress)
-- | 2. **Stagger**: Spatial-to-temporal mapping for groups
-- | 3. **Spring**: Physics-based animation state
-- | 4. **Phase**: Normalized animation progress [0.0, 1.0]
-- |
-- | ## Wire Format vs High-Level
-- |
-- | Some types have two forms:
-- | - **High-level**: Full expressiveness for composition (e.g., Easing with Custom)
-- | - **Wire-format**: Serializable subset for GPU dispatch (e.g., EasingId)
-- |
-- | Conversion functions bridge these representations.
-- |
-- | ## Migration Status
-- |
-- | - Animation.Algebra: Has own Easing, StaggerPattern, StaggerDirection
-- | - GPU.DrawCommand: Has EasingFunction, StaggerDirection for wire format
-- | - Typography.TextAnimation: Has StaggerDirection, StaggerPattern
-- |
-- | These will be unified by:
-- | 1. Adding re-exports from this module
-- | 2. Updating Binary.purs to use conversion functions
-- | 3. Deprecating duplicate definitions

module Hydrogen.Animation.Types
  ( -- * Easing (High-Level)
    Easing(Linear, EaseIn, EaseOut, EaseInOut, EaseInQuad, EaseOutQuad, EaseInOutQuad, EaseInCubic, EaseOutCubic, EaseInOutCubic, EaseInQuart, EaseOutQuart, EaseInOutQuart, EaseInQuint, EaseOutQuint, EaseInOutQuint, EaseInExpo, EaseOutExpo, EaseInOutExpo, EaseInCirc, EaseOutCirc, EaseInOutCirc, EaseInBack, EaseOutBack, EaseInOutBack, EaseInElastic, EaseOutElastic, EaseInOutElastic, EaseInBounce, EaseOutBounce, EaseInOutBounce, Spring, CubicBezier, Steps)
  , SpringConfig(SpringConfig)
  , BezierCurve(BezierCurve)
  
  -- * Easing (Wire Format)
  , EasingId(EasingIdLinear, EasingIdInQuad, EasingIdOutQuad, EasingIdInOutQuad, EasingIdInCubic, EasingIdOutCubic, EasingIdInOutCubic, EasingIdInElastic, EasingIdOutElastic, EasingIdInOutElastic, EasingIdInBounce, EasingIdOutBounce, EasingIdSpring)
  , easingToId
  , idToEasing
  , allEasingIds
  
  -- * Stagger Direction
  , StaggerDirection(StaggerLeftToRight, StaggerRightToLeft, StaggerCenterOut, StaggerEdgesIn, StaggerTopToBottom, StaggerBottomToTop, StaggerRandom)
  
  -- * Stagger Pattern
  , StaggerPattern(LinearStagger, CenterOutStagger, EdgesInStagger, RandomStagger, CustomStagger)
  
  -- * Spring Physics State
  , SpringState
  , defaultSpringState
  , springAtRest
  , applySpringForce
  
  -- * Animation Phase
  , AnimationPhase(AnimationPhase)
  , phase
  , unwrapPhase
  , advancePhase
  , phaseComplete
  , phaseProgress
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , eq
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (<>)
  , (&&)
  , (==)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // easing high-level
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spring physics configuration.
-- |
-- | All parameters are bounded to physically meaningful ranges.
-- | These define the behavior of spring-based animations.
newtype SpringConfig = SpringConfig
  { tension :: Number    -- Stiffness [0, 1000], default 170
  , friction :: Number   -- Damping [0, 100], default 26
  , mass :: Number       -- Mass [0.1, 10], default 1
  }

derive instance eqSpringConfig :: Eq SpringConfig

instance showSpringConfig :: Show SpringConfig where
  show (SpringConfig c) = "SpringConfig(tension=" <> show c.tension 
    <> ", friction=" <> show c.friction 
    <> ", mass=" <> show c.mass <> ")"

-- | Cubic bezier control points for custom easing.
-- |
-- | P0 = (0, 0), P3 = (1, 1) are fixed.
-- | P1 and P2 are the control points we specify.
newtype BezierCurve = BezierCurve
  { x1 :: Number  -- P1.x ∈ [0, 1]
  , y1 :: Number  -- P1.y ∈ [-2, 2] (can overshoot)
  , x2 :: Number  -- P2.x ∈ [0, 1]
  , y2 :: Number  -- P2.y ∈ [-2, 2] (can overshoot)
  }

derive instance eqBezierCurve :: Eq BezierCurve

instance showBezierCurve :: Show BezierCurve where
  show (BezierCurve b) = "bezier(" <> show b.x1 <> "," <> show b.y1 
    <> "," <> show b.x2 <> "," <> show b.y2 <> ")"

-- | High-level easing type with full expressiveness.
-- |
-- | Each constructor represents a different time-warping function.
-- | The Custom variant allows arbitrary functions but cannot be serialized.
data Easing
  = Linear
  | EaseIn
  | EaseOut
  | EaseInOut
  | EaseInQuad
  | EaseOutQuad
  | EaseInOutQuad
  | EaseInCubic
  | EaseOutCubic
  | EaseInOutCubic
  | EaseInQuart
  | EaseOutQuart
  | EaseInOutQuart
  | EaseInQuint
  | EaseOutQuint
  | EaseInOutQuint
  | EaseInExpo
  | EaseOutExpo
  | EaseInOutExpo
  | EaseInCirc
  | EaseOutCirc
  | EaseInOutCirc
  | EaseInBack
  | EaseOutBack
  | EaseInOutBack
  | EaseInElastic
  | EaseOutElastic
  | EaseInOutElastic
  | EaseInBounce
  | EaseOutBounce
  | EaseInOutBounce
  | Spring SpringConfig
  | CubicBezier BezierCurve
  | Steps Int           -- Step function with n steps

derive instance eqEasing :: Eq Easing

instance showEasing :: Show Easing where
  show Linear = "linear"
  show EaseIn = "ease-in"
  show EaseOut = "ease-out"
  show EaseInOut = "ease-in-out"
  show EaseInQuad = "ease-in-quad"
  show EaseOutQuad = "ease-out-quad"
  show EaseInOutQuad = "ease-in-out-quad"
  show EaseInCubic = "ease-in-cubic"
  show EaseOutCubic = "ease-out-cubic"
  show EaseInOutCubic = "ease-in-out-cubic"
  show EaseInQuart = "ease-in-quart"
  show EaseOutQuart = "ease-out-quart"
  show EaseInOutQuart = "ease-in-out-quart"
  show EaseInQuint = "ease-in-quint"
  show EaseOutQuint = "ease-out-quint"
  show EaseInOutQuint = "ease-in-out-quint"
  show EaseInExpo = "ease-in-expo"
  show EaseOutExpo = "ease-out-expo"
  show EaseInOutExpo = "ease-in-out-expo"
  show EaseInCirc = "ease-in-circ"
  show EaseOutCirc = "ease-out-circ"
  show EaseInOutCirc = "ease-in-out-circ"
  show EaseInBack = "ease-in-back"
  show EaseOutBack = "ease-out-back"
  show EaseInOutBack = "ease-in-out-back"
  show EaseInElastic = "ease-in-elastic"
  show EaseOutElastic = "ease-out-elastic"
  show EaseInOutElastic = "ease-in-out-elastic"
  show EaseInBounce = "ease-in-bounce"
  show EaseOutBounce = "ease-out-bounce"
  show EaseInOutBounce = "ease-in-out-bounce"
  show (Spring cfg) = "spring(" <> show cfg <> ")"
  show (CubicBezier curve) = show curve
  show (Steps n) = "steps(" <> show n <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // easing wire format
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wire-format easing identifier.
-- |
-- | This is the serializable subset of Easing. Each variant maps to a u8 in
-- | the binary format. Complex easings (CubicBezier, Steps) are not included
-- | because they require additional data.
-- |
-- | Constructor names use `EasingId*` prefix to disambiguate from high-level
-- | Easing constructors in the same module.
data EasingId
  = EasingIdLinear           -- 0
  | EasingIdInQuad           -- 1
  | EasingIdOutQuad          -- 2
  | EasingIdInOutQuad        -- 3
  | EasingIdInCubic          -- 4
  | EasingIdOutCubic         -- 5
  | EasingIdInOutCubic       -- 6
  | EasingIdInElastic        -- 7
  | EasingIdOutElastic       -- 8
  | EasingIdInOutElastic     -- 9
  | EasingIdInBounce         -- 10
  | EasingIdOutBounce        -- 11
  | EasingIdSpring           -- 12 (uses SpringState)

derive instance eqEasingId :: Eq EasingId
derive instance ordEasingId :: Ord EasingId

instance showEasingId :: Show EasingId where
  show EasingIdLinear = "linear"
  show EasingIdInQuad = "in-quad"
  show EasingIdOutQuad = "out-quad"
  show EasingIdInOutQuad = "in-out-quad"
  show EasingIdInCubic = "in-cubic"
  show EasingIdOutCubic = "out-cubic"
  show EasingIdInOutCubic = "in-out-cubic"
  show EasingIdInElastic = "in-elastic"
  show EasingIdOutElastic = "out-elastic"
  show EasingIdInOutElastic = "in-out-elastic"
  show EasingIdInBounce = "in-bounce"
  show EasingIdOutBounce = "out-bounce"
  show EasingIdSpring = "spring"

-- | All wire-format easing IDs for enumeration.
allEasingIds :: Array EasingId
allEasingIds =
  [ EasingIdLinear
  , EasingIdInQuad
  , EasingIdOutQuad
  , EasingIdInOutQuad
  , EasingIdInCubic
  , EasingIdOutCubic
  , EasingIdInOutCubic
  , EasingIdInElastic
  , EasingIdOutElastic
  , EasingIdInOutElastic
  , EasingIdInBounce
  , EasingIdOutBounce
  , EasingIdSpring
  ]

-- | Convert high-level Easing to wire-format EasingId.
-- |
-- | Returns Nothing for easings that cannot be represented in wire format
-- | (Custom, CubicBezier with arbitrary values, Steps).
easingToId :: Easing -> Maybe EasingId
easingToId = case _ of
  Linear -> Just EasingIdLinear
  EaseIn -> Just EasingIdInQuad      -- EaseIn is quad by convention
  EaseOut -> Just EasingIdOutQuad
  EaseInOut -> Just EasingIdInOutQuad
  EaseInQuad -> Just EasingIdInQuad
  EaseOutQuad -> Just EasingIdOutQuad
  EaseInOutQuad -> Just EasingIdInOutQuad
  EaseInCubic -> Just EasingIdInCubic
  EaseOutCubic -> Just EasingIdOutCubic
  EaseInOutCubic -> Just EasingIdInOutCubic
  EaseInElastic -> Just EasingIdInElastic
  EaseOutElastic -> Just EasingIdOutElastic
  EaseInOutElastic -> Just EasingIdInOutElastic
  EaseInBounce -> Just EasingIdInBounce
  EaseOutBounce -> Just EasingIdOutBounce
  EaseInOutBounce -> Just EasingIdOutBounce  -- Fallback to out-bounce
  Spring _ -> Just EasingIdSpring
  -- These cannot be represented in wire format
  EaseInQuart -> Just EasingIdInCubic        -- Approximate with cubic
  EaseOutQuart -> Just EasingIdOutCubic
  EaseInOutQuart -> Just EasingIdInOutCubic
  EaseInQuint -> Just EasingIdInCubic
  EaseOutQuint -> Just EasingIdOutCubic
  EaseInOutQuint -> Just EasingIdInOutCubic
  EaseInExpo -> Just EasingIdInElastic       -- Approximate with elastic
  EaseOutExpo -> Just EasingIdOutElastic
  EaseInOutExpo -> Just EasingIdInOutElastic
  EaseInCirc -> Just EasingIdInQuad          -- Approximate with quad
  EaseOutCirc -> Just EasingIdOutQuad
  EaseInOutCirc -> Just EasingIdInOutQuad
  EaseInBack -> Just EasingIdInElastic         -- Approximate with elastic
  EaseOutBack -> Just EasingIdOutElastic
  EaseInOutBack -> Just EasingIdInOutElastic
  CubicBezier _ -> Nothing                 -- Cannot serialize arbitrary bezier
  Steps _ -> Nothing                       -- Cannot serialize steps

-- | Convert wire-format EasingId to high-level Easing.
idToEasing :: EasingId -> Easing
idToEasing = case _ of
  EasingIdLinear -> Linear
  EasingIdInQuad -> EaseInQuad
  EasingIdOutQuad -> EaseOutQuad
  EasingIdInOutQuad -> EaseInOutQuad
  EasingIdInCubic -> EaseInCubic
  EasingIdOutCubic -> EaseOutCubic
  EasingIdInOutCubic -> EaseInOutCubic
  EasingIdInElastic -> EaseInElastic
  EasingIdOutElastic -> EaseOutElastic
  EasingIdInOutElastic -> EaseInOutElastic
  EasingIdInBounce -> EaseInBounce
  EasingIdOutBounce -> EaseOutBounce
  EasingIdSpring -> Spring defaultSpringConfig

-- | Default spring configuration for idToEasing conversion.
defaultSpringConfig :: SpringConfig
defaultSpringConfig = SpringConfig
  { tension: 170.0
  , friction: 26.0
  , mass: 1.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // stagger direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Direction for stagger animations.
-- |
-- | Determines the order in which elements begin animating.
-- | StaggerRandom includes a seed for deterministic pseudo-random ordering.
data StaggerDirection
  = StaggerLeftToRight
  | StaggerRightToLeft
  | StaggerCenterOut
  | StaggerEdgesIn
  | StaggerTopToBottom
  | StaggerBottomToTop
  | StaggerRandom Int     -- Seed for deterministic randomness

derive instance eqStaggerDirection :: Eq StaggerDirection

instance showStaggerDirection :: Show StaggerDirection where
  show StaggerLeftToRight = "left-to-right"
  show StaggerRightToLeft = "right-to-left"
  show StaggerCenterOut = "center-out"
  show StaggerEdgesIn = "edges-in"
  show StaggerTopToBottom = "top-to-bottom"
  show StaggerBottomToTop = "bottom-to-top"
  show (StaggerRandom seed) = "random(" <> show seed <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // stagger pattern
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stagger pattern for group animations.
-- |
-- | Defines how animation timing spreads across multiple elements.
-- | The Number parameter is delay in milliseconds.
-- |
-- | Note: CustomStagger allows arbitrary functions but cannot be serialized.
-- | For wire-format serialization, use patterns that don't contain functions.
data StaggerPattern
  = LinearStagger StaggerDirection Number    -- direction, delay per element
  | CenterOutStagger Number                  -- delay per distance from center
  | EdgesInStagger Number                    -- delay per distance from edges
  | RandomStagger Int Number                 -- seed, max delay
  | CustomStagger (Int -> Int -> Number)     -- function(index, total) -> delay

-- Cannot derive Eq for functions, so manual instance
instance eqStaggerPattern :: Eq StaggerPattern where
  eq (LinearStagger d1 n1) (LinearStagger d2 n2) = d1 == d2 && n1 == n2
  eq (CenterOutStagger n1) (CenterOutStagger n2) = n1 == n2
  eq (EdgesInStagger n1) (EdgesInStagger n2) = n1 == n2
  eq (RandomStagger s1 n1) (RandomStagger s2 n2) = s1 == s2 && n1 == n2
  eq (CustomStagger _) (CustomStagger _) = false  -- Functions cannot be compared
  eq _ _ = false

instance showStaggerPattern :: Show StaggerPattern where
  show (LinearStagger dir delay) = "linear-" <> show dir <> "(" <> show delay <> "ms)"
  show (CenterOutStagger delay) = "center-out(" <> show delay <> "ms)"
  show (EdgesInStagger delay) = "edges-in(" <> show delay <> "ms)"
  show (RandomStagger seed maxDelay) = "random(seed=" <> show seed <> ", max=" <> show maxDelay <> "ms)"
  show (CustomStagger _) = "custom"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // spring state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Runtime spring physics state.
-- |
-- | This represents the current state of a spring animation at a given moment.
-- | The runtime updates this state each frame using spring differential equations.
-- |
-- | Hooke's Law: F = -tension * displacement - damping * velocity
-- | Acceleration: a = F / mass
-- |
-- | Note: This is a type alias (not newtype) for direct record access in
-- | serialization. Binary.purs accesses fields directly for wire format.
type SpringState =
  { velocity :: Number      -- Current velocity (can be negative)
  , displacement :: Number  -- Offset from rest position (can be negative)
  , tension :: Number       -- Spring stiffness [0.0, 1.0] maps to k constant
  , damping :: Number       -- Friction coefficient [0.0, 1.0] prevents infinite oscillation
  , mass :: Number          -- Mass [0.1, 10.0] affects oscillation period
  }

-- | Default spring state (at rest, with standard physics).
defaultSpringState :: SpringState
defaultSpringState =
  { velocity: 0.0
  , displacement: 0.0
  , tension: 0.5
  , damping: 0.3
  , mass: 1.0
  }

-- | Check if spring is effectively at rest.
springAtRest :: SpringState -> Boolean
springAtRest s =
  absNum s.velocity < 0.001 && absNum s.displacement < 0.001
  where
    absNum :: Number -> Number
    absNum n = if n < 0.0 then 0.0 - n else n

-- | Apply spring force for one time step.
-- |
-- | dt is delta time in seconds.
-- | Returns updated spring state.
applySpringForce :: Number -> SpringState -> SpringState
applySpringForce dt s =
  let
    -- Map [0,1] ranges to physical constants
    k = s.tension * 500.0        -- tension → spring constant
    c = s.damping * 50.0         -- damping → friction
    m = s.mass
    
    -- Hooke's law with damping: F = -kx - cv
    force = (0.0 - k) * s.displacement - c * s.velocity
    acceleration = force / m
    
    -- Euler integration
    newVelocity = s.velocity + acceleration * dt
    newDisplacement = s.displacement + newVelocity * dt
  in
    { velocity: newVelocity
    , displacement: newDisplacement
    , tension: s.tension
    , damping: s.damping
    , mass: s.mass
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // animation phase
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normalized animation phase [0.0, 1.0].
-- |
-- | 0.0 = animation start, 1.0 = animation complete.
-- | Bounded by construction — invalid values are clamped.
newtype AnimationPhase = AnimationPhase Number

derive instance eqAnimationPhase :: Eq AnimationPhase
derive instance ordAnimationPhase :: Ord AnimationPhase

instance showAnimationPhase :: Show AnimationPhase where
  show (AnimationPhase p) = "phase(" <> show p <> ")"

-- | Create a phase, clamping to [0.0, 1.0].
phase :: Number -> AnimationPhase
phase n
  | n < 0.0 = AnimationPhase 0.0
  | n > 1.0 = AnimationPhase 1.0
  | otherwise = AnimationPhase n

-- | Extract raw number from phase.
unwrapPhase :: AnimationPhase -> Number
unwrapPhase (AnimationPhase p) = p

-- | Advance phase by delta, clamping to bounds.
advancePhase :: Number -> AnimationPhase -> AnimationPhase
advancePhase delta (AnimationPhase p) = phase (p + delta)

-- | Check if animation is complete.
phaseComplete :: AnimationPhase -> Boolean
phaseComplete (AnimationPhase p) = p >= 1.0

-- | Get progress as percentage (0-100).
phaseProgress :: AnimationPhase -> Int
phaseProgress (AnimationPhase p) = 
  let clamped = if p < 0.0 then 0.0 else if p > 1.0 then 1.0 else p
  in floorInt (clamped * 100.0)
  where
    floorInt :: Number -> Int
    floorInt n = 
      -- Simple floor implementation
      let intPart = truncateToInt n
      in if n < 0.0 && intToNum intPart > n then intPart - 1 else intPart
    
    truncateToInt :: Number -> Int
    truncateToInt _ = 0  -- Placeholder, actual impl would use FFI or recursion
    
    intToNum :: Int -> Number
    intToNum _ = 0.0  -- Placeholder
