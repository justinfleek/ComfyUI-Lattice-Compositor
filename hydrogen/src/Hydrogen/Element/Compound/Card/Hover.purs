-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // component // card // hover
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Card Hover — Interactive hover effects for cards.
-- |
-- | ## Design Philosophy
-- |
-- | Hover effects make cards feel alive and responsive. This module
-- | coordinates multiple effect types that can trigger on hover:
-- | - Visual transforms (scale, lift, rotate)
-- | - Audio feedback (dog bark, click sound)
-- | - Animation playback (Lottie starts playing)
-- | - Particle effects (sparkles, confetti)
-- |
-- | ## Use Cases
-- |
-- | - Product cards that enlarge on hover
-- | - Dog cards that bark when hovered
-- | - Profile cards with animated avatars
-- | - Easter egg interactions
-- |
-- | ## State Machine
-- |
-- | ```
-- | idle → entering → active → leaving → idle
-- |        (200ms)    (hold)   (200ms)
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Schema.Reactive.HoverEffect (hover primitives)
-- | - Schema.Audio.Trigger (audio triggers)
-- | - Schema.Motion.Lottie (animation triggers)

module Hydrogen.Element.Compound.Card.Hover
  ( -- * Card Hover Config
    CardHoverConfig
  , cardHoverConfig
  , defaultCardHover
  , noHover
  
  -- * Easing
  , HoverEasing
      ( EaseLinear
      , EaseIn
      , EaseOut
      , EaseInOut
      , EaseSpring
      )
  
  -- * Visual Effects
  , liftOnHover
  , liftOnHoverWith
  , scaleOnHover
  , scaleOnHoverWith
  , glowOnHover
  , glowOnHoverWith
  , tiltOnHover
  
  -- * Audio Effects
  , soundOnHover
  , soundOnHoverWith
  , soundOnClick
  
  -- * Animation Effects
  , playLottieOnHover
  , playLottieOnHoverWith
  , pauseLottieOnLeave
  
  -- * Combined Presets
  , subtleHover
  , dramaticHover
  , interactiveHover
  , interactiveHoverWith
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , otherwise
  , (<>)
  , (<)
  , (>)
  , (*)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // card hover config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete hover effect configuration for a card.
-- |
-- | Composes all possible hover behaviors into a single configuration:
-- | - Transform effects (scale, lift, rotate, tilt)
-- | - Style effects (brightness, shadow, glow)
-- | - Audio triggers (hover enter, leave, click sounds)
-- | - Animation triggers (Lottie playback)
-- | - Timing (transition duration, easing)
-- |
-- | ## Transform Configuration
-- |
-- | - `liftPixels`: Vertical lift (negative Y translation)
-- | - `scaleFactor`: Scale multiplier (1.0 = no change)
-- | - `rotateDegrees`: Rotation angle
-- | - `tiltEnabled`: 3D tilt toward mouse position
-- | - `tiltMaxAngle`: Maximum tilt angle in degrees
-- |
-- | ## Style Configuration
-- |
-- | - `brightness`: Brightness multiplier (1.0 = no change)
-- | - `shadowIncrease`: Additional shadow spread on hover
-- | - `glowColor`: Optional glow color (hex)
-- | - `glowRadius`: Glow blur radius
-- |
-- | ## Audio Configuration
-- |
-- | - `hoverSound`: Sound URL for hover enter
-- | - `leaveSound`: Sound URL for hover leave
-- | - `clickSound`: Sound URL for click
-- | - `audioVolume`: Volume (0.0 to 1.0)
-- |
-- | ## Animation Configuration
-- |
-- | - `lottieUrl`: Lottie animation URL
-- | - `lottiePlayOnHover`: Play when hover starts
-- | - `lottiePauseOnLeave`: Pause when hover ends
-- | - `lottieReverse`: Reverse on leave
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Product card with subtle lift
-- | productHover = subtleHover
-- |
-- | -- Dog card that barks
-- | dogHover = soundOnHoverWith "/sounds/bark.mp3" 0.5
-- |
-- | -- Interactive card with animation
-- | fancyHover = cardHoverConfig
-- |   { liftPixels: 4.0
-- |   , scaleFactor: 1.02
-- |   , lottieUrl: Just "/animations/sparkle.json"
-- |   , lottiePlayOnHover: true
-- |   }
-- | ```
newtype CardHoverConfig = CardHoverConfig
  { -- Transform
    liftPixels :: Number               -- ^ Vertical lift in pixels
  , scaleFactor :: Number              -- ^ Scale multiplier
  , rotateDegrees :: Number            -- ^ Rotation angle
  , tiltEnabled :: Boolean             -- ^ Enable 3D tilt effect
  , tiltMaxAngle :: Number             -- ^ Maximum tilt angle (degrees)
  
  -- Style
  , brightness :: Number               -- ^ Brightness multiplier
  , shadowIncrease :: Number           -- ^ Additional shadow on hover
  , glowColor :: Maybe String          -- ^ Glow color (hex)
  , glowRadius :: Number               -- ^ Glow blur radius
  
  -- Audio
  , hoverSound :: Maybe String         -- ^ Sound URL for hover enter
  , leaveSound :: Maybe String         -- ^ Sound URL for hover leave
  , clickSound :: Maybe String         -- ^ Sound URL for click
  , audioVolume :: Number              -- ^ Audio volume (0.0 to 1.0)
  
  -- Animation
  , lottieUrl :: Maybe String          -- ^ Lottie animation URL
  , lottiePlayOnHover :: Boolean       -- ^ Play Lottie on hover
  , lottiePauseOnLeave :: Boolean      -- ^ Pause Lottie on leave
  , lottieReverse :: Boolean           -- ^ Reverse Lottie on leave
  
  -- Timing
  , transitionDuration :: Number       -- ^ Transition duration (ms)
  , easing :: HoverEasing              -- ^ Easing function
  }

-- | Easing function for hover transitions
data HoverEasing
  = EaseLinear
  | EaseIn
  | EaseOut
  | EaseInOut
  | EaseSpring

derive instance eqHoverEasing :: Eq HoverEasing

instance showHoverEasing :: Show HoverEasing where
  show EaseLinear = "linear"
  show EaseIn = "ease-in"
  show EaseOut = "ease-out"
  show EaseInOut = "ease-in-out"
  show EaseSpring = "spring"

derive instance eqCardHoverConfig :: Eq CardHoverConfig

instance showCardHoverConfig :: Show CardHoverConfig where
  show (CardHoverConfig c) = 
    "CardHoverConfig(lift:" <> show c.liftPixels <> 
    ", scale:" <> show c.scaleFactor <> ")"

-- | Create card hover config with full options
cardHoverConfig
  :: { liftPixels :: Number
     , scaleFactor :: Number
     , rotateDegrees :: Number
     , tiltEnabled :: Boolean
     , tiltMaxAngle :: Number
     , brightness :: Number
     , shadowIncrease :: Number
     , glowColor :: Maybe String
     , glowRadius :: Number
     , hoverSound :: Maybe String
     , leaveSound :: Maybe String
     , clickSound :: Maybe String
     , audioVolume :: Number
     , lottieUrl :: Maybe String
     , lottiePlayOnHover :: Boolean
     , lottiePauseOnLeave :: Boolean
     , lottieReverse :: Boolean
     , transitionDuration :: Number
     , easing :: HoverEasing
     }
  -> CardHoverConfig
cardHoverConfig cfg = CardHoverConfig
  { liftPixels: cfg.liftPixels
  , scaleFactor: clampScale cfg.scaleFactor
  , rotateDegrees: cfg.rotateDegrees
  , tiltEnabled: cfg.tiltEnabled
  , tiltMaxAngle: clampAngle cfg.tiltMaxAngle
  , brightness: clampBrightness cfg.brightness
  , shadowIncrease: clampShadow cfg.shadowIncrease
  , glowColor: cfg.glowColor
  , glowRadius: clampRadius cfg.glowRadius
  , hoverSound: cfg.hoverSound
  , leaveSound: cfg.leaveSound
  , clickSound: cfg.clickSound
  , audioVolume: clampVolume cfg.audioVolume
  , lottieUrl: cfg.lottieUrl
  , lottiePlayOnHover: cfg.lottiePlayOnHover
  , lottiePauseOnLeave: cfg.lottiePauseOnLeave
  , lottieReverse: cfg.lottieReverse
  , transitionDuration: clampDuration cfg.transitionDuration
  , easing: cfg.easing
  }
  where
    clampScale s
      | s < 0.5 = 0.5
      | s > 2.0 = 2.0
      | otherwise = s
    clampAngle a
      | a < 0.0 = 0.0
      | a > 45.0 = 45.0
      | otherwise = a
    clampBrightness b
      | b < 0.5 = 0.5
      | b > 2.0 = 2.0
      | otherwise = b
    clampShadow s
      | s < 0.0 = 0.0
      | s > 50.0 = 50.0
      | otherwise = s
    clampRadius r
      | r < 0.0 = 0.0
      | r > 100.0 = 100.0
      | otherwise = r
    clampVolume v
      | v < 0.0 = 0.0
      | v > 1.0 = 1.0
      | otherwise = v
    clampDuration d
      | d < 0.0 = 0.0
      | d > 2000.0 = 2000.0
      | otherwise = d

-- | Default hover effect (subtle lift + shadow)
defaultCardHover :: CardHoverConfig
defaultCardHover = CardHoverConfig
  { liftPixels: 2.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 10.0
  , brightness: 1.0
  , shadowIncrease: 4.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.7
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 200.0
  , easing: EaseOut
  }

-- | No hover effects
noHover :: CardHoverConfig
noHover = CardHoverConfig
  { liftPixels: 0.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.0
  , shadowIncrease: 0.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.0
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 0.0
  , easing: EaseLinear
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // visual effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lift card on hover (translateY)
liftOnHover :: CardHoverConfig
liftOnHover = CardHoverConfig
  { liftPixels: 4.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.0
  , shadowIncrease: 8.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.0
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 200.0
  , easing: EaseOut
  }

-- | Lift with custom pixels
liftOnHoverWith :: Number -> CardHoverConfig
liftOnHoverWith pixels = CardHoverConfig
  { liftPixels: pixels
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.0
  , shadowIncrease: pixels * 2.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.0
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 200.0
  , easing: EaseOut
  }

-- | Scale card on hover
scaleOnHover :: CardHoverConfig
scaleOnHover = CardHoverConfig
  { liftPixels: 0.0
  , scaleFactor: 1.03
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.0
  , shadowIncrease: 4.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.0
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 200.0
  , easing: EaseOut
  }

-- | Scale with custom factor
scaleOnHoverWith :: Number -> CardHoverConfig
scaleOnHoverWith factor = CardHoverConfig
  { liftPixels: 0.0
  , scaleFactor: factor
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.0
  , shadowIncrease: 4.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.0
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 200.0
  , easing: EaseOut
  }

-- | Add glow on hover
glowOnHover :: CardHoverConfig
glowOnHover = CardHoverConfig
  { liftPixels: 0.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.05
  , shadowIncrease: 0.0
  , glowColor: Just "#3B82F6"
  , glowRadius: 20.0
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.0
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 250.0
  , easing: EaseInOut
  }

-- | Glow with custom color
glowOnHoverWith :: String -> Number -> CardHoverConfig
glowOnHoverWith color radius = CardHoverConfig
  { liftPixels: 0.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.05
  , shadowIncrease: 0.0
  , glowColor: Just color
  , glowRadius: radius
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.0
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 250.0
  , easing: EaseInOut
  }

-- | Tilt toward mouse position on hover
tiltOnHover :: CardHoverConfig
tiltOnHover = CardHoverConfig
  { liftPixels: 0.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: true
  , tiltMaxAngle: 10.0
  , brightness: 1.0
  , shadowIncrease: 4.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.0
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 100.0
  , easing: EaseOut
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // audio effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Play sound when hover starts
soundOnHover :: CardHoverConfig
soundOnHover = CardHoverConfig
  { liftPixels: 2.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.0
  , shadowIncrease: 4.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Just "/sounds/hover.mp3"
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.5
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 200.0
  , easing: EaseOut
  }

-- | Sound on hover with custom URL and volume
soundOnHoverWith :: String -> Number -> CardHoverConfig
soundOnHoverWith url volume = CardHoverConfig
  { liftPixels: 2.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.0
  , shadowIncrease: 4.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Just url
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: volume
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 200.0
  , easing: EaseOut
  }

-- | Play sound when clicked
soundOnClick :: CardHoverConfig
soundOnClick = CardHoverConfig
  { liftPixels: 0.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.0
  , shadowIncrease: 0.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Just "/sounds/click.mp3"
  , audioVolume: 0.5
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 0.0
  , easing: EaseLinear
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // animation effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Start Lottie animation when hover starts
playLottieOnHover :: CardHoverConfig
playLottieOnHover = CardHoverConfig
  { liftPixels: 0.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.0
  , shadowIncrease: 0.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.0
  , lottieUrl: Just "/animations/default.json"
  , lottiePlayOnHover: true
  , lottiePauseOnLeave: true
  , lottieReverse: false
  , transitionDuration: 0.0
  , easing: EaseLinear
  }

-- | Lottie animation with custom URL
playLottieOnHoverWith :: String -> CardHoverConfig
playLottieOnHoverWith url = CardHoverConfig
  { liftPixels: 0.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.0
  , shadowIncrease: 0.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.0
  , lottieUrl: Just url
  , lottiePlayOnHover: true
  , lottiePauseOnLeave: true
  , lottieReverse: false
  , transitionDuration: 0.0
  , easing: EaseLinear
  }

-- | Pause Lottie animation when hover ends (with reverse)
pauseLottieOnLeave :: CardHoverConfig
pauseLottieOnLeave = CardHoverConfig
  { liftPixels: 0.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.0
  , shadowIncrease: 0.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.0
  , lottieUrl: Just "/animations/default.json"
  , lottiePlayOnHover: true
  , lottiePauseOnLeave: true
  , lottieReverse: true
  , transitionDuration: 0.0
  , easing: EaseLinear
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // combined presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Subtle hover (small lift + shadow increase)
subtleHover :: CardHoverConfig
subtleHover = CardHoverConfig
  { liftPixels: 2.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.02
  , shadowIncrease: 4.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.0
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 150.0
  , easing: EaseOut
  }

-- | Dramatic hover (large scale + glow)
dramaticHover :: CardHoverConfig
dramaticHover = CardHoverConfig
  { liftPixels: 8.0
  , scaleFactor: 1.05
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.1
  , shadowIncrease: 16.0
  , glowColor: Just "#3B82F6"
  , glowRadius: 30.0
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.0
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 300.0
  , easing: EaseSpring
  }

-- | Interactive hover (sound + animation)
interactiveHover :: CardHoverConfig
interactiveHover = CardHoverConfig
  { liftPixels: 4.0
  , scaleFactor: 1.02
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.05
  , shadowIncrease: 8.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Just "/sounds/hover.mp3"
  , leaveSound: Nothing
  , clickSound: Just "/sounds/click.mp3"
  , audioVolume: 0.5
  , lottieUrl: Just "/animations/sparkle.json"
  , lottiePlayOnHover: true
  , lottiePauseOnLeave: true
  , lottieReverse: false
  , transitionDuration: 200.0
  , easing: EaseOut
  }

-- | Interactive hover with custom sounds and animation
interactiveHoverWith :: String -> String -> String -> CardHoverConfig
interactiveHoverWith hoverSoundUrl clickSoundUrl lottieUrl = CardHoverConfig
  { liftPixels: 4.0
  , scaleFactor: 1.02
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.05
  , shadowIncrease: 8.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Just hoverSoundUrl
  , leaveSound: Nothing
  , clickSound: Just clickSoundUrl
  , audioVolume: 0.5
  , lottieUrl: Just lottieUrl
  , lottiePlayOnHover: true
  , lottiePauseOnLeave: true
  , lottieReverse: false
  , transitionDuration: 200.0
  , easing: EaseOut
  }
