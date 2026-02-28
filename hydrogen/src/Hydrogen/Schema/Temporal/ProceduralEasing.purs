-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // temporal // procedural-easing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ProceduralEasing — Easing functions that cannot be represented as cubic beziers.
-- |
-- | ## Why These Exist Separately
-- |
-- | Cubic bezier easing curves are monotonic in the time dimension — they can
-- | only move forward through time. This makes them unable to represent:
-- |
-- | - **Elastic**: Oscillating overshoot with decay (like a spring)
-- | - **Bounce**: Multiple impacts with decreasing amplitude
-- |
-- | These easing functions require procedural evaluation at runtime.
-- |
-- | ## Physical Models
-- |
-- | ### Elastic
-- |
-- | Models a damped harmonic oscillator: ẍ + 2ζω₀ẋ + ω₀²x = 0
-- |
-- | Where:
-- | - ω₀ = natural frequency (controls oscillation speed)
-- | - ζ = damping ratio (controls decay rate)
-- |
-- | For underdamped systems (ζ < 1), the solution oscillates while decaying.
-- |
-- | ### Bounce
-- |
-- | Models inelastic collisions with a surface. Each bounce:
-- | - Reverses velocity
-- | - Loses energy (coefficient of restitution < 1)
-- | - Occurs at progressively shorter intervals
-- |
-- | ## Usage
-- |
-- | These cannot be converted to CSS — use JavaScript/WebGPU runtime evaluation.
-- | The data types here define the parameters; the runtime evaluates them.

module Hydrogen.Schema.Temporal.ProceduralEasing
  ( -- * Elastic Easing
    ElasticConfig(..)
  , defaultElastic
  , elasticWithAmplitude
  , elasticWithPeriod
  
  -- * Bounce Easing
  , BounceConfig(..)
  , defaultBounce
  , bounceWithRestitution
  
  -- * Preset Constructors
  , easeInElastic
  , easeOutElastic
  , easeInOutElastic
  , easeInBounce
  , easeOutBounce
  , easeInOutBounce
  
  -- * Direction
  , ProceduralDirection(..)
  
  -- * Combined Type
  , ProceduralEasing(..)
  , isElastic
  , isBounce
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (>)
  , (<)
  )

import Data.Generic.Rep (class Generic)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // elastic config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for elastic (oscillating) easing
-- |
-- | ## Parameters
-- |
-- | - **amplitude**: Peak overshoot magnitude. 1.0 = 100% overshoot.
-- |   Higher values create more dramatic oscillation.
-- |   Clamped to >= 1.0 (no negative or zero amplitude).
-- |
-- | - **period**: Time for one oscillation cycle, as fraction of total duration.
-- |   Smaller = faster oscillations. Default 0.3 creates ~3-4 visible bounces.
-- |   Clamped to > 0.
-- |
-- | ## Mathematical Model
-- |
-- | For ease-out elastic at time t ∈ [0, 1]:
-- |   y = amplitude × 2^(-10t) × sin((t - period/4) × (2π/period)) + 1
-- |
-- | The 2^(-10t) term provides exponential decay, while sin() oscillates.
type ElasticConfig =
  { amplitude :: Number  -- ^ Overshoot magnitude, >= 1.0
  , period :: Number     -- ^ Oscillation period, > 0
  }

-- | Default elastic configuration
-- |
-- | amplitude: 1.0 (no overshoot amplification)
-- | period: 0.3 (standard oscillation frequency)
defaultElastic :: ElasticConfig
defaultElastic =
  { amplitude: 1.0
  , period: 0.3
  }

-- | Create elastic config with custom amplitude
-- |
-- | Amplitude is clamped to >= 1.0
elasticWithAmplitude :: Number -> ElasticConfig
elasticWithAmplitude amp =
  { amplitude: clampMin 1.0 amp
  , period: 0.3
  }

-- | Create elastic config with custom period
-- |
-- | Period is clamped to > 0
elasticWithPeriod :: Number -> ElasticConfig
elasticWithPeriod per =
  { amplitude: 1.0
  , period: clampPositive per
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // bounce config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for bounce easing
-- |
-- | ## Parameters
-- |
-- | - **bounces**: Number of bounces. More bounces = more complexity.
-- |   Clamped to >= 1.
-- |
-- | - **restitution**: Coefficient of restitution (energy retained per bounce).
-- |   0.0 = perfectly inelastic (no bounce back)
-- |   1.0 = perfectly elastic (full bounce back)
-- |   Default 0.75 provides natural-looking decay.
-- |   Clamped to [0, 1].
-- |
-- | ## Mathematical Model
-- |
-- | Each bounce follows a parabolic trajectory:
-- |   y = 4h × (t/T)(1 - t/T)
-- |
-- | Where h = height (decreases by restitution^2 per bounce)
-- | and T = time for that bounce (decreases by restitution per bounce)
type BounceConfig =
  { bounces :: Int         -- ^ Number of bounces, >= 1
  , restitution :: Number  -- ^ Energy retention per bounce, [0, 1]
  }

-- | Default bounce configuration
-- |
-- | bounces: 4 (standard bounce animation)
-- | restitution: 0.75 (natural energy decay)
defaultBounce :: BounceConfig
defaultBounce =
  { bounces: 4
  , restitution: 0.75
  }

-- | Create bounce config with custom restitution
-- |
-- | Restitution is clamped to [0, 1]
bounceWithRestitution :: Number -> BounceConfig
bounceWithRestitution res =
  { bounces: 4
  , restitution: clampUnit res
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Direction of procedural easing application
-- |
-- | - **In**: Effect at start of animation (slow start, dramatic end)
-- | - **Out**: Effect at end of animation (fast start, dramatic settling)
-- | - **InOut**: Effect at both ends (symmetric)
data ProceduralDirection
  = In
  | Out
  | InOut

derive instance eqProceduralDirection :: Eq ProceduralDirection
derive instance ordProceduralDirection :: Ord ProceduralDirection
derive instance genericProceduralDirection :: Generic ProceduralDirection _

instance showProceduralDirection :: Show ProceduralDirection where
  show In = "In"
  show Out = "Out"
  show InOut = "InOut"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // procedural easing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Union of all procedural (non-bezier) easing types
-- |
-- | These require runtime evaluation — they cannot be converted to CSS.
data ProceduralEasing
  = Elastic ProceduralDirection ElasticConfig
  | Bounce ProceduralDirection BounceConfig

derive instance eqProceduralEasing :: Eq ProceduralEasing
derive instance ordProceduralEasing :: Ord ProceduralEasing
derive instance genericProceduralEasing :: Generic ProceduralEasing _

instance showProceduralEasing :: Show ProceduralEasing where
  show (Elastic dir cfg) = 
    "(Elastic " <> show dir <> " " <> showElastic cfg <> ")"
  show (Bounce dir cfg) = 
    "(Bounce " <> show dir <> " " <> showBounce cfg <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Elastic ease-in (oscillation at start)
easeInElastic :: ProceduralEasing
easeInElastic = Elastic In defaultElastic

-- | Elastic ease-out (oscillation at end, settling)
easeOutElastic :: ProceduralEasing
easeOutElastic = Elastic Out defaultElastic

-- | Elastic ease-in-out (oscillation at both ends)
easeInOutElastic :: ProceduralEasing
easeInOutElastic = Elastic InOut defaultElastic

-- | Bounce ease-in (bouncing at start)
easeInBounce :: ProceduralEasing
easeInBounce = Bounce In defaultBounce

-- | Bounce ease-out (bouncing landing at end)
easeOutBounce :: ProceduralEasing
easeOutBounce = Bounce Out defaultBounce

-- | Bounce ease-in-out (bouncing at both ends)
easeInOutBounce :: ProceduralEasing
easeInOutBounce = Bounce InOut defaultBounce

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if easing is elastic type
isElastic :: ProceduralEasing -> Boolean
isElastic (Elastic _ _) = true
isElastic _ = false

-- | Check if easing is bounce type
isBounce :: ProceduralEasing -> Boolean
isBounce (Bounce _ _) = true
isBounce _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp to minimum value
clampMin :: Number -> Number -> Number
clampMin minVal n = if n < minVal then minVal else n

-- | Clamp to positive (> 0)
clampPositive :: Number -> Number
clampPositive n = if n < 0.01 then 0.01 else n

-- | Clamp to unit interval [0, 1]
clampUnit :: Number -> Number
clampUnit n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | true = n

-- | Show elastic config as string
showElastic :: ElasticConfig -> String
showElastic cfg = 
  "{ amplitude: " <> show cfg.amplitude 
  <> ", period: " <> show cfg.period <> " }"

-- | Show bounce config as string
showBounce :: BounceConfig -> String
showBounce cfg = 
  "{ bounces: " <> show cfg.bounces 
  <> ", restitution: " <> show cfg.restitution <> " }"
