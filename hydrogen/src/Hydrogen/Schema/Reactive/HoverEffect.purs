-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // reactive // hover-effect
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HoverEffect — Interactive hover behaviors for UI elements.
-- |
-- | ## Design Philosophy
-- |
-- | Hover effects are declarative descriptions of what happens when a user
-- | hovers over an element. The runtime interprets these into actual
-- | event handlers and animations.
-- |
-- | ## Effect Categories
-- |
-- | - **Transform**: Scale, translate, rotate on hover
-- | - **Style**: Color, opacity, filter changes
-- | - **Audio**: Sound triggers on enter/leave
-- | - **Animation**: Lottie/CSS animation triggers
-- | - **Particle**: Particle burst effects
-- |
-- | ## State Machine
-- |
-- | ```
-- | idle → entering → hovering → leaving → idle
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Schema.Dimension.Temporal (timing)
-- | - Schema.Color.RGB (color changes)
-- | - Schema.Motion.Easing (transition curves)

module Hydrogen.Schema.Reactive.HoverEffect
  ( -- * Hover State
    HoverState
      ( HoverIdle
      , HoverEntering
      , HoverActive
      , HoverLeaving
      )
  
  -- * Transform Effects
  , HoverTransform(..)
  , TransformOrigin(..)
  , hoverTransform
  , identityTransform
  , defaultHoverTransform
  , liftTransform
  , pressTransform
  , scaleUpTransform
  , elevatedHoverTransform
  
  -- * Style Effects
  , HoverStyle(..)
  , OpacityChange(..)
  , hoverStyle
  , identityStyle
  , defaultHoverStyle
  , subtleHoverStyle
  , prominentHoverStyle
  , glowHoverStyle
  , dimHoverStyle
  
  -- * Audio Trigger
  , HoverAudio(..)
  , HoverAudioSource(..)
  , hoverAudio
  , noHoverAudio
  , hoverAudioEnter
  , hoverAudioEnterLeave
  , hoverAudioLoop
  
  -- * Animation Trigger
  , HoverAnimation(..)
  , HoverAnimationType(..)
  , HoverSpringConfig
  , hoverAnimation
  , noHoverAnimation
  , hoverAnimationLottie
  , hoverAnimationCss
  , hoverAnimationSpring
  , defaultSpringConfig
  
  -- * Particle Trigger
  , HoverParticle(..)
  , ParticleType(..)
  , EmissionMode(..)
  , hoverParticle
  , noHoverParticle
  , hoverParticleBurst
  , hoverParticleContinuous
  , hoverParticleTrail
  
  -- * Combined Hover Effect
  , HoverEffect(..)
  , hoverEffect
  , noHoverEffect
  , defaultHoverEffect
  , subtleHoverEffect
  , prominentHoverEffect
  , glowHoverEffect
  , audioHoverEffect
  , animatedHoverEffect
  , sparkleHoverEffect
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , otherwise
  , (<>)
  , (<)
  , (>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // hover state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Current hover state of an element
data HoverState
  = HoverIdle       -- ^ Not being hovered
  | HoverEntering   -- ^ Mouse just entered, transition starting
  | HoverActive     -- ^ Actively being hovered
  | HoverLeaving    -- ^ Mouse just left, transition ending

derive instance eqHoverState :: Eq HoverState
derive instance ordHoverState :: Ord HoverState

instance showHoverState :: Show HoverState where
  show HoverIdle = "idle"
  show HoverEntering = "entering"
  show HoverActive = "active"
  show HoverLeaving = "leaving"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // hover transform
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transform applied on hover
-- |
-- | Based on research from Linear, Vercel, and Apple design systems:
-- | - Best timing: 100-200ms
-- | - Optimal hover lift: translateY(-1px) + subtle shadow increase
-- | - Active state: scale(0.98) for tactile feedback
-- | - Use easeOut for enter, easeIn for exit
-- |
-- | ## Transform Properties
-- |
-- | - **translateX/Y**: Pixel offset (negative Y = lift effect)
-- | - **scale**: Uniform scale factor (1.0 = no change)
-- | - **scaleX/Y**: Non-uniform scale
-- | - **rotate**: Rotation in degrees
-- | - **skewX/Y**: Skew angles in degrees
newtype HoverTransform = HoverTransform
  { translateX :: Number     -- ^ Horizontal offset in pixels
  , translateY :: Number     -- ^ Vertical offset in pixels (negative = lift)
  , scale :: Number          -- ^ Uniform scale factor (1.0 = normal)
  , scaleX :: Number         -- ^ Horizontal scale factor
  , scaleY :: Number         -- ^ Vertical scale factor
  , rotate :: Number         -- ^ Rotation in degrees
  , skewX :: Number          -- ^ Horizontal skew in degrees
  , skewY :: Number          -- ^ Vertical skew in degrees
  , transformOrigin :: TransformOrigin -- ^ Origin point for transforms
  }

derive instance eqHoverTransform :: Eq HoverTransform

instance showHoverTransform :: Show HoverTransform where
  show (HoverTransform t) = 
    "HoverTransform(" <>
    "translateY:" <> show t.translateY <>
    ", scale:" <> show t.scale <> ")"

-- | Transform origin point
data TransformOrigin
  = OriginCenter        -- ^ Center of element (default)
  | OriginTop           -- ^ Top center
  | OriginBottom        -- ^ Bottom center
  | OriginLeft          -- ^ Left center
  | OriginRight         -- ^ Right center
  | OriginTopLeft       -- ^ Top left corner
  | OriginTopRight      -- ^ Top right corner
  | OriginBottomLeft    -- ^ Bottom left corner
  | OriginBottomRight   -- ^ Bottom right corner
  | OriginCustom Number Number -- ^ Custom X Y percentages (0-100)

derive instance eqTransformOrigin :: Eq TransformOrigin

instance showTransformOrigin :: Show TransformOrigin where
  show OriginCenter = "center"
  show OriginTop = "top"
  show OriginBottom = "bottom"
  show OriginLeft = "left"
  show OriginRight = "right"
  show OriginTopLeft = "top-left"
  show OriginTopRight = "top-right"
  show OriginBottomLeft = "bottom-left"
  show OriginBottomRight = "bottom-right"
  show (OriginCustom x y) = show x <> "% " <> show y <> "%"

-- | Identity transform (no change)
identityTransform :: HoverTransform
identityTransform = HoverTransform
  { translateX: 0.0
  , translateY: 0.0
  , scale: 1.0
  , scaleX: 1.0
  , scaleY: 1.0
  , rotate: 0.0
  , skewX: 0.0
  , skewY: 0.0
  , transformOrigin: OriginCenter
  }

-- | Create hover transform with specified values
hoverTransform 
  :: { translateY :: Number, scale :: Number } 
  -> HoverTransform
hoverTransform { translateY: ty, scale: s } = HoverTransform
  { translateX: 0.0
  , translateY: ty
  , scale: s
  , scaleX: 1.0
  , scaleY: 1.0
  , rotate: 0.0
  , skewX: 0.0
  , skewY: 0.0
  , transformOrigin: OriginCenter
  }

-- | Default hover transform (slight lift - Linear/Vercel style)
-- |
-- | Research finding: translateY(-1px) provides subtle lift effect
-- | that feels tactile without being jarring
defaultHoverTransform :: HoverTransform
defaultHoverTransform = hoverTransform { translateY: (-1.0), scale: 1.0 }

-- | Lift transform for button hover (raises element)
liftTransform :: HoverTransform
liftTransform = hoverTransform { translateY: (-2.0), scale: 1.0 }

-- | Press transform for active state (slight scale down)
-- |
-- | Research finding: scale(0.98) provides tactile press feedback
pressTransform :: HoverTransform
pressTransform = hoverTransform { translateY: 0.0, scale: 0.98 }

-- | Scale up transform (grow on hover)
scaleUpTransform :: HoverTransform
scaleUpTransform = hoverTransform { translateY: 0.0, scale: 1.02 }

-- | Combined lift and scale for elevated buttons
elevatedHoverTransform :: HoverTransform
elevatedHoverTransform = hoverTransform { translateY: (-2.0), scale: 1.01 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // hover style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Style changes on hover
-- |
-- | Describes visual property changes that occur during hover:
-- | - Opacity adjustments
-- | - Background color changes
-- | - Border color changes
-- | - Shadow intensity changes
-- | - Filter effects (brightness, saturation)
-- |
-- | ## Layered Shadows on Hover
-- |
-- | Research finding: best hover shadows use multiple layers:
-- | - Base shadow stays constant
-- | - Additional "lift" shadow appears on hover
-- | - Creates more realistic depth perception
newtype HoverStyle = HoverStyle
  { opacity :: OpacityChange        -- ^ Opacity adjustment
  , brightness :: Number            -- ^ Filter brightness (1.0 = normal)
  , saturation :: Number            -- ^ Filter saturation (1.0 = normal)
  , contrast :: Number              -- ^ Filter contrast (1.0 = normal)
  , shadowIntensity :: Number       -- ^ Shadow opacity multiplier (1.0 = normal)
  , shadowSpread :: Number          -- ^ Additional shadow spread in pixels
  , backgroundLighten :: Number     -- ^ Background lightness adjustment (-100 to 100)
  , borderLighten :: Number         -- ^ Border lightness adjustment (-100 to 100)
  }

derive instance eqHoverStyle :: Eq HoverStyle

instance showHoverStyle :: Show HoverStyle where
  show (HoverStyle s) = 
    "HoverStyle(brightness:" <> show s.brightness <> 
    ", shadowIntensity:" <> show s.shadowIntensity <> ")"

-- | Opacity change modes
data OpacityChange
  = OpacityAbsolute Number  -- ^ Set to specific opacity (0.0-1.0)
  | OpacityRelative Number  -- ^ Multiply current opacity
  | OpacityUnchanged        -- ^ Keep current opacity

derive instance eqOpacityChange :: Eq OpacityChange

instance showOpacityChange :: Show OpacityChange where
  show (OpacityAbsolute v) = "opacity:" <> show v
  show (OpacityRelative v) = "opacity*" <> show v
  show OpacityUnchanged = "opacity:unchanged"

-- | Create hover style with common options
hoverStyle 
  :: { brightness :: Number, shadowIntensity :: Number }
  -> HoverStyle
hoverStyle { brightness: b, shadowIntensity: si } = HoverStyle
  { opacity: OpacityUnchanged
  , brightness: b
  , saturation: 1.0
  , contrast: 1.0
  , shadowIntensity: si
  , shadowSpread: 0.0
  , backgroundLighten: 0.0
  , borderLighten: 0.0
  }

-- | Identity style (no visual changes)
identityStyle :: HoverStyle
identityStyle = HoverStyle
  { opacity: OpacityUnchanged
  , brightness: 1.0
  , saturation: 1.0
  , contrast: 1.0
  , shadowIntensity: 1.0
  , shadowSpread: 0.0
  , backgroundLighten: 0.0
  , borderLighten: 0.0
  }

-- | Default hover style (subtle brightness increase + shadow lift)
-- |
-- | Research finding: 5-10% brightness increase is perceptible
-- | but not jarring. Shadow increase of 20-30% adds depth.
defaultHoverStyle :: HoverStyle
defaultHoverStyle = HoverStyle
  { opacity: OpacityUnchanged
  , brightness: 1.05
  , saturation: 1.0
  , contrast: 1.0
  , shadowIntensity: 1.25
  , shadowSpread: 2.0
  , backgroundLighten: 3.0
  , borderLighten: 0.0
  }

-- | Subtle hover style (minimal change)
subtleHoverStyle :: HoverStyle
subtleHoverStyle = HoverStyle
  { opacity: OpacityUnchanged
  , brightness: 1.02
  , saturation: 1.0
  , contrast: 1.0
  , shadowIntensity: 1.1
  , shadowSpread: 1.0
  , backgroundLighten: 2.0
  , borderLighten: 0.0
  }

-- | Prominent hover style (more noticeable)
prominentHoverStyle :: HoverStyle
prominentHoverStyle = HoverStyle
  { opacity: OpacityUnchanged
  , brightness: 1.1
  , saturation: 1.05
  , contrast: 1.0
  , shadowIntensity: 1.5
  , shadowSpread: 4.0
  , backgroundLighten: 5.0
  , borderLighten: 5.0
  }

-- | Glow hover style (emissive appearance)
glowHoverStyle :: HoverStyle
glowHoverStyle = HoverStyle
  { opacity: OpacityUnchanged
  , brightness: 1.15
  , saturation: 1.1
  , contrast: 1.0
  , shadowIntensity: 2.0
  , shadowSpread: 8.0
  , backgroundLighten: 0.0
  , borderLighten: 10.0
  }

-- | Dim hover style (for secondary elements)
dimHoverStyle :: HoverStyle
dimHoverStyle = HoverStyle
  { opacity: OpacityRelative 0.7
  , brightness: 0.95
  , saturation: 0.9
  , contrast: 1.0
  , shadowIntensity: 0.8
  , shadowSpread: 0.0
  , backgroundLighten: (-3.0)
  , borderLighten: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // hover audio
-- ═════════════════════════════════════════════════════════════════════════════

-- | Audio triggered on hover.
-- |
-- | Describes sounds to play when hovering over an element:
-- | - Enter sound (mouse enters)
-- | - Leave sound (mouse exits)
-- | - Loop while hovering
-- |
-- | ## Audio Sources
-- |
-- | Audio can come from URL or inline base64 data.
-- | Volume is normalized 0.0 to 1.0.
-- |
-- | ## Fade Behavior
-- |
-- | Fades smooth out abrupt audio starts/stops:
-- | - fadeInMs: gradual volume increase on enter
-- | - fadeOutMs: gradual volume decrease on leave
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Dog card plays bark on hover
-- | dogBark = hoverAudioEnter (HoverAudioUrl "/sounds/bark.mp3") 0.5
-- |
-- | -- Ambient loop while hovering
-- | ambientHover = hoverAudioLoop (HoverAudioUrl "/sounds/ambient.ogg") 0.3
-- | ```
newtype HoverAudio = HoverAudio
  { enterSound :: HoverAudioSource     -- ^ Sound on mouse enter
  , leaveSound :: HoverAudioSource     -- ^ Sound on mouse leave  
  , loopSound :: HoverAudioSource      -- ^ Sound looped while hovering
  , volume :: Number                   -- ^ Master volume (0.0 to 1.0)
  , fadeInMs :: Number                 -- ^ Fade in duration (milliseconds)
  , fadeOutMs :: Number                -- ^ Fade out duration (milliseconds)
  }

-- | Audio source for hover sounds
data HoverAudioSource
  = HoverAudioNone                    -- ^ No audio
  | HoverAudioUrl String              -- ^ URL to audio file
  | HoverAudioInline String           -- ^ Base64-encoded audio data

derive instance eqHoverAudioSource :: Eq HoverAudioSource

instance showHoverAudioSource :: Show HoverAudioSource where
  show HoverAudioNone = "none"
  show (HoverAudioUrl _) = "url"
  show (HoverAudioInline _) = "inline"

derive instance eqHoverAudio :: Eq HoverAudio

instance showHoverAudio :: Show HoverAudio where
  show (HoverAudio a) = 
    "HoverAudio(vol:" <> show a.volume <> ")"

-- | Create hover audio with full configuration
hoverAudio 
  :: { enterSound :: HoverAudioSource
     , leaveSound :: HoverAudioSource
     , loopSound :: HoverAudioSource
     , volume :: Number
     , fadeInMs :: Number
     , fadeOutMs :: Number
     }
  -> HoverAudio
hoverAudio cfg = HoverAudio
  { enterSound: cfg.enterSound
  , leaveSound: cfg.leaveSound
  , loopSound: cfg.loopSound
  , volume: clampVolume cfg.volume
  , fadeInMs: clampMs cfg.fadeInMs
  , fadeOutMs: clampMs cfg.fadeOutMs
  }
  where
    clampVolume v
      | v < 0.0 = 0.0
      | v > 1.0 = 1.0
      | otherwise = v
    clampMs ms
      | ms < 0.0 = 0.0
      | otherwise = ms

-- | No hover audio
noHoverAudio :: HoverAudio
noHoverAudio = HoverAudio
  { enterSound: HoverAudioNone
  , leaveSound: HoverAudioNone
  , loopSound: HoverAudioNone
  , volume: 0.0
  , fadeInMs: 0.0
  , fadeOutMs: 0.0
  }

-- | Play sound on hover enter only
hoverAudioEnter :: HoverAudioSource -> Number -> HoverAudio
hoverAudioEnter src vol = HoverAudio
  { enterSound: src
  , leaveSound: HoverAudioNone
  , loopSound: HoverAudioNone
  , volume: vol
  , fadeInMs: 50.0
  , fadeOutMs: 0.0
  }

-- | Play sound on both enter and leave
hoverAudioEnterLeave :: HoverAudioSource -> HoverAudioSource -> Number -> HoverAudio
hoverAudioEnterLeave enter leave vol = HoverAudio
  { enterSound: enter
  , leaveSound: leave
  , loopSound: HoverAudioNone
  , volume: vol
  , fadeInMs: 50.0
  , fadeOutMs: 50.0
  }

-- | Loop sound while hovering
hoverAudioLoop :: HoverAudioSource -> Number -> HoverAudio
hoverAudioLoop src vol = HoverAudio
  { enterSound: HoverAudioNone
  , leaveSound: HoverAudioNone
  , loopSound: src
  , volume: vol
  , fadeInMs: 100.0
  , fadeOutMs: 100.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // hover animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation triggered on hover.
-- |
-- | Describes animations to play when hovering:
-- | - Lottie animations (JSON-based vector animation)
-- | - CSS keyframe animation names
-- | - Spring-based transform animations
-- |
-- | ## Animation Timing
-- |
-- | - `playOnEnter`: Start animation when mouse enters
-- | - `playOnLeave`: Play reverse/exit animation when leaving
-- | - `loopWhileHovering`: Continuously loop while hovered
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Play Lottie animation on hover
-- | dogWag = hoverAnimationLottie "/animations/dog-wag.json"
-- |
-- | -- CSS animation
-- | pulse = hoverAnimationCss "pulse" 300.0
-- | ```
newtype HoverAnimation = HoverAnimation
  { animationType :: HoverAnimationType  -- ^ Type of animation
  , playOnEnter :: Boolean               -- ^ Play when mouse enters
  , playOnLeave :: Boolean               -- ^ Play when mouse leaves
  , loopWhileHovering :: Boolean         -- ^ Loop while hovered
  , durationMs :: Number                 -- ^ Animation duration (milliseconds)
  , delayMs :: Number                    -- ^ Delay before starting (milliseconds)
  }

-- | Type of hover animation
data HoverAnimationType
  = HoverAnimNone                       -- ^ No animation
  | HoverAnimLottie String              -- ^ Lottie JSON URL
  | HoverAnimLottieInline String        -- ^ Inline Lottie JSON
  | HoverAnimCss String                 -- ^ CSS animation name
  | HoverAnimSpring HoverSpringConfig   -- ^ Spring physics animation

-- | Spring animation configuration
type HoverSpringConfig =
  { stiffness :: Number      -- ^ Spring stiffness (higher = faster)
  , damping :: Number        -- ^ Damping ratio (1.0 = critically damped)
  , mass :: Number           -- ^ Virtual mass (affects momentum)
  }

derive instance eqHoverAnimationType :: Eq HoverAnimationType

instance showHoverAnimationType :: Show HoverAnimationType where
  show HoverAnimNone = "none"
  show (HoverAnimLottie _) = "lottie"
  show (HoverAnimLottieInline _) = "lottie-inline"
  show (HoverAnimCss name) = "css:" <> name
  show (HoverAnimSpring _) = "spring"

derive instance eqHoverAnimation :: Eq HoverAnimation

instance showHoverAnimation :: Show HoverAnimation where
  show (HoverAnimation a) = 
    "HoverAnimation(" <> show a.animationType <> 
    ", " <> show a.durationMs <> "ms)"

-- | Create hover animation with full configuration
hoverAnimation
  :: { animationType :: HoverAnimationType
     , playOnEnter :: Boolean
     , playOnLeave :: Boolean
     , loopWhileHovering :: Boolean
     , durationMs :: Number
     , delayMs :: Number
     }
  -> HoverAnimation
hoverAnimation cfg = HoverAnimation
  { animationType: cfg.animationType
  , playOnEnter: cfg.playOnEnter
  , playOnLeave: cfg.playOnLeave
  , loopWhileHovering: cfg.loopWhileHovering
  , durationMs: clampMs cfg.durationMs
  , delayMs: clampMs cfg.delayMs
  }
  where
    clampMs ms
      | ms < 0.0 = 0.0
      | otherwise = ms

-- | No hover animation
noHoverAnimation :: HoverAnimation
noHoverAnimation = HoverAnimation
  { animationType: HoverAnimNone
  , playOnEnter: false
  , playOnLeave: false
  , loopWhileHovering: false
  , durationMs: 0.0
  , delayMs: 0.0
  }

-- | Play Lottie animation on hover
hoverAnimationLottie :: String -> HoverAnimation
hoverAnimationLottie url = HoverAnimation
  { animationType: HoverAnimLottie url
  , playOnEnter: true
  , playOnLeave: false
  , loopWhileHovering: false
  , durationMs: 1000.0
  , delayMs: 0.0
  }

-- | Play CSS animation on hover
hoverAnimationCss :: String -> Number -> HoverAnimation
hoverAnimationCss name duration = HoverAnimation
  { animationType: HoverAnimCss name
  , playOnEnter: true
  , playOnLeave: false
  , loopWhileHovering: false
  , durationMs: duration
  , delayMs: 0.0
  }

-- | Spring physics animation on hover
hoverAnimationSpring :: HoverSpringConfig -> HoverAnimation
hoverAnimationSpring spring = HoverAnimation
  { animationType: HoverAnimSpring spring
  , playOnEnter: true
  , playOnLeave: true
  , loopWhileHovering: false
  , durationMs: 500.0
  , delayMs: 0.0
  }

-- | Default spring config (snappy, Apple-like feel)
defaultSpringConfig :: HoverSpringConfig
defaultSpringConfig =
  { stiffness: 300.0
  , damping: 20.0
  , mass: 1.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // hover particle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Particle effect triggered on hover.
-- |
-- | Describes particle systems that emit on hover:
-- | - Sparkles, confetti, dust, bubbles
-- | - Emit from element center or follow cursor
-- | - Customizable colors, sizes, and behaviors
-- |
-- | ## Emission Modes
-- |
-- | - `EmitBurst`: Single burst on enter
-- | - `EmitContinuous`: Continuous emission while hovered
-- | - `EmitOnMove`: Emit particles following cursor movement
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Sparkle burst on hover
-- | sparkles = hoverParticleBurst SparkleParticle 20
-- |
-- | -- Continuous snow while hovering
-- | snow = hoverParticleContinuous SnowParticle 5
-- | ```
newtype HoverParticle = HoverParticle
  { particleType :: ParticleType        -- ^ Visual style of particles
  , emissionMode :: EmissionMode        -- ^ How particles are emitted
  , count :: Int                        -- ^ Particles per emission
  , lifetimeMs :: Number                -- ^ How long each particle lives
  , spread :: Number                    -- ^ Spread angle in degrees (0-360)
  , speed :: Number                     -- ^ Initial velocity (pixels/second)
  , gravity :: Number                   -- ^ Downward acceleration (pixels/s²)
  , fadeOut :: Boolean                  -- ^ Fade opacity as particle ages
  , shrink :: Boolean                   -- ^ Shrink size as particle ages
  }

-- | Visual type of particle
data ParticleType
  = NoParticle                          -- ^ No particles
  | SparkleParticle                     -- ^ Star-shaped sparkles
  | ConfettiParticle                    -- ^ Rectangular confetti
  | DustParticle                        -- ^ Small circular dust
  | BubbleParticle                      -- ^ Translucent bubbles
  | SnowParticle                        -- ^ Snowflake shapes
  | HeartParticle                       -- ^ Heart shapes
  | StarParticle                        -- ^ Star shapes
  | CustomParticle String               -- ^ Custom SVG path

derive instance eqParticleType :: Eq ParticleType

instance showParticleType :: Show ParticleType where
  show NoParticle = "none"
  show SparkleParticle = "sparkle"
  show ConfettiParticle = "confetti"
  show DustParticle = "dust"
  show BubbleParticle = "bubble"
  show SnowParticle = "snow"
  show HeartParticle = "heart"
  show StarParticle = "star"
  show (CustomParticle _) = "custom"

-- | How particles are emitted
data EmissionMode
  = EmitNone                            -- ^ No emission
  | EmitBurst                           -- ^ Single burst on hover enter
  | EmitContinuous                      -- ^ Continuous while hovering
  | EmitOnMove                          -- ^ Emit following cursor
  | EmitOnLeave                         -- ^ Burst when mouse leaves

derive instance eqEmissionMode :: Eq EmissionMode

instance showEmissionMode :: Show EmissionMode where
  show EmitNone = "none"
  show EmitBurst = "burst"
  show EmitContinuous = "continuous"
  show EmitOnMove = "on-move"
  show EmitOnLeave = "on-leave"

derive instance eqHoverParticle :: Eq HoverParticle

instance showHoverParticle :: Show HoverParticle where
  show (HoverParticle p) = 
    "HoverParticle(" <> show p.particleType <> 
    ", " <> show p.emissionMode <> 
    ", count:" <> show p.count <> ")"

-- | Create hover particle with full configuration
hoverParticle
  :: { particleType :: ParticleType
     , emissionMode :: EmissionMode
     , count :: Int
     , lifetimeMs :: Number
     , spread :: Number
     , speed :: Number
     , gravity :: Number
     , fadeOut :: Boolean
     , shrink :: Boolean
     }
  -> HoverParticle
hoverParticle cfg = HoverParticle
  { particleType: cfg.particleType
  , emissionMode: cfg.emissionMode
  , count: clampCount cfg.count
  , lifetimeMs: clampMs cfg.lifetimeMs
  , spread: clampSpread cfg.spread
  , speed: clampPositive cfg.speed
  , gravity: cfg.gravity
  , fadeOut: cfg.fadeOut
  , shrink: cfg.shrink
  }
  where
    clampCount c
      | c < 0 = 0
      | c > 1000 = 1000
      | otherwise = c
    clampMs ms
      | ms < 0.0 = 0.0
      | otherwise = ms
    clampSpread s
      | s < 0.0 = 0.0
      | s > 360.0 = 360.0
      | otherwise = s
    clampPositive v
      | v < 0.0 = 0.0
      | otherwise = v

-- | No hover particles
noHoverParticle :: HoverParticle
noHoverParticle = HoverParticle
  { particleType: NoParticle
  , emissionMode: EmitNone
  , count: 0
  , lifetimeMs: 0.0
  , spread: 0.0
  , speed: 0.0
  , gravity: 0.0
  , fadeOut: false
  , shrink: false
  }

-- | Burst of particles on hover enter
hoverParticleBurst :: ParticleType -> Int -> HoverParticle
hoverParticleBurst pType count = HoverParticle
  { particleType: pType
  , emissionMode: EmitBurst
  , count: count
  , lifetimeMs: 1000.0
  , spread: 360.0
  , speed: 100.0
  , gravity: 50.0
  , fadeOut: true
  , shrink: true
  }

-- | Continuous particles while hovering
hoverParticleContinuous :: ParticleType -> Int -> HoverParticle
hoverParticleContinuous pType countPerSecond = HoverParticle
  { particleType: pType
  , emissionMode: EmitContinuous
  , count: countPerSecond
  , lifetimeMs: 2000.0
  , spread: 180.0
  , speed: 50.0
  , gravity: 20.0
  , fadeOut: true
  , shrink: false
  }

-- | Particles following cursor movement
hoverParticleTrail :: ParticleType -> HoverParticle
hoverParticleTrail pType = HoverParticle
  { particleType: pType
  , emissionMode: EmitOnMove
  , count: 3
  , lifetimeMs: 500.0
  , spread: 45.0
  , speed: 30.0
  , gravity: 0.0
  , fadeOut: true
  , shrink: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // hover effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combined hover effect configuration.
-- |
-- | Composes all hover effect types into a single configuration:
-- | - Transform (scale, translate, rotate)
-- | - Style (brightness, shadows, filters)
-- | - Audio (enter/leave/loop sounds)
-- | - Animation (Lottie, CSS, spring)
-- | - Particle (sparkles, confetti, etc.)
-- |
-- | ## Timing
-- |
-- | All effects share common timing parameters:
-- | - `transitionDurationMs`: How long transitions take
-- | - `transitionDelay`: Delay before starting
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Basic hover with lift and shadow
-- | basicHover = defaultHoverEffect
-- |
-- | -- Complex hover with audio and particles
-- | fancyHover = hoverEffect
-- |   { transform: liftTransform
-- |   , style: glowHoverStyle
-- |   , audio: hoverAudioEnter (HoverAudioUrl "/click.mp3") 0.5
-- |   , animation: noHoverAnimation
-- |   , particle: hoverParticleBurst SparkleParticle 10
-- |   , transitionDurationMs: 200.0
-- |   , transitionDelay: 0.0
-- |   }
-- | ```
newtype HoverEffect = HoverEffect
  { transform :: HoverTransform          -- ^ Transform on hover
  , style :: HoverStyle                  -- ^ Style changes on hover
  , audio :: HoverAudio                  -- ^ Audio triggers
  , animation :: HoverAnimation          -- ^ Animation triggers
  , particle :: HoverParticle            -- ^ Particle effects
  , transitionDurationMs :: Number       -- ^ Duration of transitions
  , transitionDelay :: Number            -- ^ Delay before transition starts
  }

derive instance eqHoverEffect :: Eq HoverEffect

instance showHoverEffect :: Show HoverEffect where
  show (HoverEffect e) = 
    "HoverEffect(duration:" <> show e.transitionDurationMs <> "ms)"

-- | Create hover effect with full configuration
hoverEffect
  :: { transform :: HoverTransform
     , style :: HoverStyle
     , audio :: HoverAudio
     , animation :: HoverAnimation
     , particle :: HoverParticle
     , transitionDurationMs :: Number
     , transitionDelay :: Number
     }
  -> HoverEffect
hoverEffect cfg = HoverEffect
  { transform: cfg.transform
  , style: cfg.style
  , audio: cfg.audio
  , animation: cfg.animation
  , particle: cfg.particle
  , transitionDurationMs: clampMs cfg.transitionDurationMs
  , transitionDelay: clampMs cfg.transitionDelay
  }
  where
    clampMs ms
      | ms < 0.0 = 0.0
      | otherwise = ms

-- | No hover effect (completely inert)
noHoverEffect :: HoverEffect
noHoverEffect = HoverEffect
  { transform: identityTransform
  , style: identityStyle
  , audio: noHoverAudio
  , animation: noHoverAnimation
  , particle: noHoverParticle
  , transitionDurationMs: 0.0
  , transitionDelay: 0.0
  }

-- | Default hover effect (subtle lift + brightness).
-- |
-- | Research-based defaults:
-- | - 150ms duration (optimal for perceived responsiveness)
-- | - Slight Y translation (-1px lift)
-- | - 5% brightness increase
-- | - 25% shadow intensity increase
defaultHoverEffect :: HoverEffect
defaultHoverEffect = HoverEffect
  { transform: defaultHoverTransform
  , style: defaultHoverStyle
  , audio: noHoverAudio
  , animation: noHoverAnimation
  , particle: noHoverParticle
  , transitionDurationMs: 150.0
  , transitionDelay: 0.0
  }

-- | Subtle hover (minimal visual feedback)
subtleHoverEffect :: HoverEffect
subtleHoverEffect = HoverEffect
  { transform: identityTransform
  , style: subtleHoverStyle
  , audio: noHoverAudio
  , animation: noHoverAnimation
  , particle: noHoverParticle
  , transitionDurationMs: 100.0
  , transitionDelay: 0.0
  }

-- | Prominent hover (more noticeable feedback)
prominentHoverEffect :: HoverEffect
prominentHoverEffect = HoverEffect
  { transform: liftTransform
  , style: prominentHoverStyle
  , audio: noHoverAudio
  , animation: noHoverAnimation
  , particle: noHoverParticle
  , transitionDurationMs: 200.0
  , transitionDelay: 0.0
  }

-- | Glow hover (emissive appearance)
glowHoverEffect :: HoverEffect
glowHoverEffect = HoverEffect
  { transform: scaleUpTransform
  , style: glowHoverStyle
  , audio: noHoverAudio
  , animation: noHoverAnimation
  , particle: noHoverParticle
  , transitionDurationMs: 250.0
  , transitionDelay: 0.0
  }

-- | Interactive hover with audio feedback
audioHoverEffect :: HoverAudioSource -> Number -> HoverEffect
audioHoverEffect audioSrc volume = HoverEffect
  { transform: defaultHoverTransform
  , style: defaultHoverStyle
  , audio: hoverAudioEnter audioSrc volume
  , animation: noHoverAnimation
  , particle: noHoverParticle
  , transitionDurationMs: 150.0
  , transitionDelay: 0.0
  }

-- | Animated hover with Lottie
animatedHoverEffect :: String -> HoverEffect
animatedHoverEffect lottieUrl = HoverEffect
  { transform: identityTransform
  , style: identityStyle
  , audio: noHoverAudio
  , animation: hoverAnimationLottie lottieUrl
  , particle: noHoverParticle
  , transitionDurationMs: 0.0
  , transitionDelay: 0.0
  }

-- | Particle hover with sparkles
sparkleHoverEffect :: HoverEffect
sparkleHoverEffect = HoverEffect
  { transform: scaleUpTransform
  , style: glowHoverStyle
  , audio: noHoverAudio
  , animation: noHoverAnimation
  , particle: hoverParticleBurst SparkleParticle 15
  , transitionDurationMs: 200.0
  , transitionDelay: 0.0
  }
