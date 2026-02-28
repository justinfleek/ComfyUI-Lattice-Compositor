-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // element // component // confetti
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Confetti — Pure particle celebration effects.
-- |
-- | ## Design Philosophy
-- |
-- | Confetti is a particle system description — pure data that tells the
-- | runtime how to animate celebration particles. No FFI, no canvas
-- | manipulation, just declarative particle configuration.
-- |
-- | ## Architecture
-- |
-- | ```
-- | ConfettiConfig → confetti → Element msg
-- |                              ↓
-- |                     GPU DrawParticle commands
-- |                              ↓
-- |                     WebGL point sprites
-- | ```
-- |
-- | The Element embeds particle system metadata as data attributes.
-- | The Hydrogen runtime interprets these and dispatches to GPU.
-- |
-- | ## Effect Types
-- |
-- | - **Burst**: Radial explosion from center point
-- | - **Cannon**: Directional spray with angle/velocity
-- | - **Fireworks**: Sequential bursts at random positions
-- | - **Snow**: Gentle downward drift
-- | - **Emoji**: Text/emoji particles instead of shapes
-- |
-- | ## Particle Shapes
-- |
-- | - **Square**: Classic square confetti
-- | - **Circle**: Round particles
-- | - **Star**: 5-pointed stars
-- | - **Triangle**: Triangular pieces
-- | - **Ribbon**: Elongated streamer shapes
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Confetti as Confetti
-- |
-- | -- Simple burst
-- | celebration = Confetti.confetti Confetti.defaultConfig
-- |
-- | -- Custom cannon effect
-- | cannon = Confetti.confetti
-- |   Confetti.defaultConfig
-- |     { effect = Confetti.Cannon
-- |     , origin = { x: 0.0, y: 1.0 }
-- |     , angle = 60.0
-- |     , spread = 55.0
-- |     , particleCount = 100
-- |     }
-- |
-- | -- Emoji confetti
-- | party = Confetti.confettiEmoji
-- |   Confetti.defaultConfig
-- |   ["🎉", "🎊", "✨", "🥳"]
-- | ```

module Hydrogen.Element.Compound.Confetti
  ( -- * Component
    confetti
  , confettiEmoji
  , confettiContainer
  
  -- * Configuration
  , ConfettiConfig
  , defaultConfig
  
  -- * Effect Types
  , ConfettiEffect
      ( Burst
      , Cannon
      , Fireworks
      , Snow
      )
  
  -- * Particle Shapes
  , ParticleShape
      ( Square
      , Circle
      , Star
      , Triangle
      , Ribbon
      )
  
  -- * Origin Point
  , Origin
  , centerOrigin
  , topCenterOrigin
  , bottomLeftOrigin
  , bottomRightOrigin
  
  -- * Presets
  , celebrationBurst
  , victoryCannon
  , gentleSnow
  , fireworksShow
  
  -- * Config Helpers
  , withColors
  , withShapes
  , withGravity
  , withDuration
  , withVelocity
  , withTicks
  , withDrift
  , withDecay
  , withParticleCount
  , withSpread
  , withAngle
  , withOrigin
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , map
  , (<>)
  )

import Data.Array (intercalate)
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Confetti effect type — determines the emission pattern.
data ConfettiEffect
  = Burst       -- ^ Radial explosion from center
  | Cannon      -- ^ Directional spray with angle
  | Fireworks   -- ^ Sequential random bursts
  | Snow        -- ^ Gentle downward drift

derive instance eqConfettiEffect :: Eq ConfettiEffect
derive instance ordConfettiEffect :: Ord ConfettiEffect

instance showConfettiEffect :: Show ConfettiEffect where
  show Burst = "burst"
  show Cannon = "cannon"
  show Fireworks = "fireworks"
  show Snow = "snow"

-- | Particle shape — the visual form of each confetti piece.
data ParticleShape
  = Square      -- ^ Classic square confetti
  | Circle      -- ^ Round particles
  | Star        -- ^ 5-pointed stars
  | Triangle    -- ^ Triangular pieces
  | Ribbon      -- ^ Elongated streamers

derive instance eqParticleShape :: Eq ParticleShape
derive instance ordParticleShape :: Ord ParticleShape

instance showParticleShape :: Show ParticleShape where
  show Square = "square"
  show Circle = "circle"
  show Star = "star"
  show Triangle = "triangle"
  show Ribbon = "ribbon"

-- | Origin point for particle emission (0.0 to 1.0 normalized coordinates).
type Origin =
  { x :: Number  -- ^ 0.0 = left, 1.0 = right
  , y :: Number  -- ^ 0.0 = top, 1.0 = bottom
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // origin presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Center of the viewport.
centerOrigin :: Origin
centerOrigin = { x: 0.5, y: 0.5 }

-- | Top center (for snow effects).
topCenterOrigin :: Origin
topCenterOrigin = { x: 0.5, y: 0.0 }

-- | Bottom left corner (for cannon effects).
bottomLeftOrigin :: Origin
bottomLeftOrigin = { x: 0.0, y: 1.0 }

-- | Bottom right corner (for cannon effects).
bottomRightOrigin :: Origin
bottomRightOrigin = { x: 1.0, y: 1.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete confetti configuration.
-- |
-- | All physics and visual parameters for the particle system.
type ConfettiConfig =
  { effect :: ConfettiEffect
  , particleCount :: Int
  , spread :: Number         -- ^ Spread angle in degrees
  , angle :: Number          -- ^ Emission angle in degrees (for Cannon)
  , origin :: Origin
  , colors :: Array String   -- ^ Hex color codes
  , shapes :: Array ParticleShape
  , duration :: Int          -- ^ Duration in milliseconds
  , gravity :: Number        -- ^ Gravity multiplier (1.0 = normal)
  , drift :: Number          -- ^ Horizontal drift (-1.0 to 1.0)
  , decay :: Number          -- ^ Velocity decay per frame (0.9 - 0.99)
  , scalar :: Number         -- ^ Size multiplier
  , startVelocity :: Number  -- ^ Initial velocity
  , ticks :: Int             -- ^ Animation frames
  , className :: String
  }

-- | Sensible defaults for a celebration burst.
defaultConfig :: ConfettiConfig
defaultConfig =
  { effect: Burst
  , particleCount: 100
  , spread: 70.0
  , angle: 90.0
  , origin: centerOrigin
  , colors: rainbowColors
  , shapes: [ Square, Circle ]
  , duration: 3000
  , gravity: 1.0
  , drift: 0.0
  , decay: 0.94
  , scalar: 1.0
  , startVelocity: 45.0
  , ticks: 200
  , className: ""
  }

-- | Rainbow color palette.
rainbowColors :: Array String
rainbowColors =
  [ "#ff0000"  -- Red
  , "#ff7f00"  -- Orange
  , "#ffff00"  -- Yellow
  , "#00ff00"  -- Green
  , "#0000ff"  -- Blue
  , "#4b0082"  -- Indigo
  , "#9400d3"  -- Violet
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // config helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set custom colors.
withColors :: Array String -> ConfettiConfig -> ConfettiConfig
withColors c cfg = cfg { colors = c }

-- | Set particle shapes.
withShapes :: Array ParticleShape -> ConfettiConfig -> ConfettiConfig
withShapes s cfg = cfg { shapes = s }

-- | Set gravity multiplier.
withGravity :: Number -> ConfettiConfig -> ConfettiConfig
withGravity g cfg = cfg { gravity = g }

-- | Set effect duration.
withDuration :: Int -> ConfettiConfig -> ConfettiConfig
withDuration d cfg = cfg { duration = d }

-- | Set initial velocity.
withVelocity :: Number -> ConfettiConfig -> ConfettiConfig
withVelocity v cfg = cfg { startVelocity = v }

-- | Set animation ticks (frame count).
withTicks :: Int -> ConfettiConfig -> ConfettiConfig
withTicks t cfg = cfg { ticks = t }

-- | Set horizontal drift (-1.0 to 1.0).
withDrift :: Number -> ConfettiConfig -> ConfettiConfig
withDrift d cfg = cfg { drift = d }

-- | Set velocity decay per frame (0.9 - 0.99).
withDecay :: Number -> ConfettiConfig -> ConfettiConfig
withDecay d cfg = cfg { decay = d }

-- | Set particle count.
withParticleCount :: Int -> ConfettiConfig -> ConfettiConfig
withParticleCount n cfg = cfg { particleCount = n }

-- | Set spread angle in degrees.
withSpread :: Number -> ConfettiConfig -> ConfettiConfig
withSpread s cfg = cfg { spread = s }

-- | Set emission angle in degrees (for Cannon effect).
withAngle :: Number -> ConfettiConfig -> ConfettiConfig
withAngle a cfg = cfg { angle = a }

-- | Set emission origin point.
withOrigin :: Origin -> ConfettiConfig -> ConfettiConfig
withOrigin o cfg = cfg { origin = o }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Classic celebration burst from center.
celebrationBurst :: ConfettiConfig
celebrationBurst = defaultConfig

-- | Victory cannon from bottom corners.
victoryCannon :: ConfettiConfig
victoryCannon = defaultConfig
  { effect = Cannon
  , origin = bottomLeftOrigin
  , angle = 60.0
  , spread = 55.0
  , particleCount = 150
  , startVelocity = 55.0
  }

-- | Gentle snowfall effect.
gentleSnow :: ConfettiConfig
gentleSnow = defaultConfig
  { effect = Snow
  , origin = topCenterOrigin
  , particleCount = 50
  , shapes = [ Circle ]
  , colors = [ "#ffffff", "#e0e0e0", "#c0c0c0" ]
  , gravity = 0.3
  , drift = 0.5
  , decay = 0.99
  , startVelocity = 10.0
  , ticks = 500
  }

-- | Fireworks display.
fireworksShow :: ConfettiConfig
fireworksShow = defaultConfig
  { effect = Fireworks
  , particleCount = 200
  , duration = 5000
  , spread = 360.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a confetti effect as a pure Element.
-- |
-- | The Element contains all particle system configuration as data attributes.
-- | The Hydrogen runtime interprets these and dispatches GPU particle commands.
confetti :: forall msg. ConfettiConfig -> E.Element msg
confetti cfg =
  E.div_
    [ E.class_ ("confetti-system " <> cfg.className)
    , E.attr "data-confetti" "true"
    , E.attr "data-effect" (show cfg.effect)
    , E.attr "data-particle-count" (show cfg.particleCount)
    , E.attr "data-spread" (show cfg.spread)
    , E.attr "data-angle" (show cfg.angle)
    , E.attr "data-origin-x" (show cfg.origin.x)
    , E.attr "data-origin-y" (show cfg.origin.y)
    , E.attr "data-duration" (show cfg.duration)
    , E.attr "data-gravity" (show cfg.gravity)
    , E.attr "data-drift" (show cfg.drift)
    , E.attr "data-decay" (show cfg.decay)
    , E.attr "data-scalar" (show cfg.scalar)
    , E.attr "data-start-velocity" (show cfg.startVelocity)
    , E.attr "data-ticks" (show cfg.ticks)
    , E.attr "data-colors" (intercalate "," cfg.colors)
    , E.attr "data-shapes" (intercalate "," (map show cfg.shapes))
    , E.attr "aria-hidden" "true"
    ]
    []

-- | Render emoji confetti.
-- |
-- | Uses text/emoji characters as particles instead of shapes.
confettiEmoji :: forall msg. ConfettiConfig -> Array String -> E.Element msg
confettiEmoji cfg emojis =
  E.div_
    [ E.class_ ("confetti-system confetti-emoji " <> cfg.className)
    , E.attr "data-confetti" "true"
    , E.attr "data-effect" (show cfg.effect)
    , E.attr "data-particle-count" (show cfg.particleCount)
    , E.attr "data-spread" (show cfg.spread)
    , E.attr "data-angle" (show cfg.angle)
    , E.attr "data-origin-x" (show cfg.origin.x)
    , E.attr "data-origin-y" (show cfg.origin.y)
    , E.attr "data-duration" (show cfg.duration)
    , E.attr "data-gravity" (show cfg.gravity)
    , E.attr "data-drift" (show cfg.drift)
    , E.attr "data-decay" (show cfg.decay)
    , E.attr "data-scalar" (show cfg.scalar)
    , E.attr "data-start-velocity" (show cfg.startVelocity)
    , E.attr "data-ticks" (show cfg.ticks)
    , E.attr "data-emojis" (intercalate "," emojis)
    , E.attr "aria-hidden" "true"
    ]
    []

-- | Confetti container overlay.
-- |
-- | Place at app root for confetti rendering. The runtime uses this as the
-- | render target for particle GPU commands.
confettiContainer :: forall msg. E.Element msg
confettiContainer =
  E.div_
    [ E.class_ "confetti-container fixed inset-0 pointer-events-none z-50"
    , E.attr "id" "confetti-container"
    , E.attr "aria-hidden" "true"
    ]
    []
