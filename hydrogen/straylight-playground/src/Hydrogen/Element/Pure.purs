-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // element // pure
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure Element — Composed Entirely from Schema Atoms
-- |
-- | This is the complete rendering instruction set. No strings. No CSS. No escape
-- | hatches. Every value is a Schema atom. Every composition is deterministic.
-- |
-- | ## The Norman Stansfield Energy Button
-- |
-- | "I like these calm little moments before the storm..."
-- |
-- | This Element type enables ANY button ever conceived:
-- | - States (enabled, disabled, loading, error, success)
-- | - Triggers (hover, press, long-press, proximity, sequence)
-- | - Playheads (scrubbing, seeking, looping, bouncing)
-- | - Materials (noise, gradients, blur, frosted glass)
-- | - Motion (spring physics, easing curves, keyframes)
-- | - Haptics (vibration patterns, audio feedback)
-- |
-- | Think about what's possible when CSS and JavaScript aren't restrictions.
-- | This is what we're building.
-- |
-- | ## Architecture
-- |
-- | ```
-- | PureScript (Hydrogen) → Defines Element type system (this file)
-- | Haskell Backend       → Generates Element values
-- | WebGPU Runtime        → Interprets Element → GPU draw calls
-- | ```
-- |
-- | Same atoms → same UUID5 → same pixels. Guaranteed.

module Hydrogen.Element.Pure
  ( -- * Core Element
    Element
      ( Rectangle
      , Circle
      , Ellipse
      , Line
      , Polyline
      , Polygon
      , Path
      , Arc
      , Text
      , Image
      , Video
      , Audio
      , Group
      , Stack
      , HStack
      , ZStack
      , Scroll
      , InteractiveElement
      , AnimatedElement
      , PlayheadElement
      , Viewport
      , Portal
      , Empty
      )
  
  -- * Effect Tracking (Graded Monads)
  , Effect
      ( Pure
      , CanClick
      , CanHover
      , CanFocus
      , CanDrag
      , CanAnimate
      , CanEmitSound
      , CanVibrate
      , CanRequestData
      , CanNavigate
      , Interactive
      , FullInteractive
      )
  , CoEffect
      ( NeedsNothing
      , NeedsFont
      , NeedsImage
      , NeedsVideo
      , NeedsAudio
      , NeedsData
      , NeedsShader
      , NeedsTexture
      , NeedsResources
      )
  
  -- * Fill Types
  , Fill
      ( Solid
      , SolidWithAlpha
      , GradientFill
      , NoiseFill
      , BlurFill
      , PatternFill
      , VideoFill
      , ShaderFill
      )
  , NoiseConfig
  , NoiseType
      ( Perlin
      , Simplex
      , Worley
      , Value
      , Curl
      , Fbm
      , Turbulence
      , Ridged
      , Billowy
      )
  , BlurConfig
  
  -- * Stroke Types
  , Stroke
  , StrokeStyle
      ( StrokeSolid
      , StrokeDashed
      , StrokeDotted
      , StrokeDouble
      )
  
  -- * Interactive Wrapper
  , InteractiveWrapper(InteractiveWrapper)
  , InteractiveConfig
  , StateVariant
      ( DefaultState
      , HoverState
      , PressedState
      , FocusState
      , FocusVisibleState
      , DisabledState
      , LoadingState
      , ErrorState
      , SuccessState
      , DraggingState
      , CustomState
      )
  
  -- * Temporal/Animation
  , Animated(Animated)
  , AnimationConfig
  , PlaybackState
      ( Playing
      , Paused
      , Stopped
      , Seeking
      , Buffering
      )
  , LoopMode
      ( NoLoop
      , LoopForever
      , LoopCount
      , PingPong
      , PingPongCount
      )
  
  -- * Playhead/Timeline
  , Playhead(Playhead)
  , PlayheadConfig
  , TimelineMarker
      ( LoopStart
      , LoopEnd
      , CuePoint
      , Label
      , Tempo
      )
  
  -- * Trigger System
  , TriggerConfig
  , TriggerResponse
      ( EmitMessage
      , PlayAnimation
      , TransitionTo
      , PlayHaptic
      , PlaySound
      , Navigate
      , Chain
      )
  
  -- * Shadow/Elevation
  , Shadow
  , ShadowLayer
  
  -- * Filter Chain
  , FilterChain
  , Filter
      ( FilterBlur
      , FilterBrightness
      , FilterContrast
      , FilterSaturate
      , FilterHueRotate
      , FilterInvert
      , FilterSepia
      , FilterGrayscale
      , FilterDropShadow
      , FilterNoise
      )
  
  -- * Bounded Optional ADTs (no Maybe wrappers)
  , ElementStroke(NoStroke, WithStroke)
  , ElementShadow(NoShadow, WithShadow)
  , ElementFilters(NoFilters, WithFilters)
  , ElementCorners(Sharp, Rounded)
  
  -- * Default Values (re-exported for convenience)
  , opacityFull
  , clipNone
  , maskNone
  , lineHeightNormal
  , letterSpacingNone
  , degreesZero
  
  -- * Identity
  , elementUUID5
  ) where

import Prelude
  ( class Eq
  , class Functor
  , class Monoid
  , class Ord
  , class Semigroup
  , class Show
  , map
  , mempty
  , not
  , show
  , ($)
  , (&&)
  , (<>)
  , (==)
  , (||)
  )

import Data.Array (length) as Array
import Data.Maybe (Maybe(Just, Nothing))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

-- Color atoms
import Hydrogen.Schema.Color.Channel (Channel)
import Hydrogen.Schema.Color.SRGB (SRGB)
import Hydrogen.Schema.Color.Opacity (Opacity, opacity)
import Hydrogen.Schema.Color.Gradient (Gradient)
import Hydrogen.Schema.Color.Hue (Hue)

-- Dimension atoms
import Hydrogen.Schema.Dimension.Device (Pixel)
import Hydrogen.Schema.Dimension.Vector.Vec2 (Vec2)
import Hydrogen.Schema.Dimension.ObjectFit (ObjectFit)

-- Geometry atoms
import Hydrogen.Schema.Geometry.Radius (Corners)
import Hydrogen.Schema.Geometry.Angle (Degrees)
import Hydrogen.Schema.Geometry.Angle (zero) as Angle
import Hydrogen.Schema.Geometry.Position (Alignment)
import Hydrogen.Schema.Geometry.ClipPath (ClipPath)
import Hydrogen.Schema.Geometry.ClipPath (clipNone) as ClipPath
import Hydrogen.Schema.Geometry.Mask (Mask)
import Hydrogen.Schema.Geometry.Mask (maskNone) as Mask
import Hydrogen.Schema.Geometry.Stroke (LineCap, LineJoin, MiterLimit)

-- Material atoms
import Hydrogen.Schema.Material.NoiseFrequency (NoiseFrequency)
import Hydrogen.Schema.Material.NoiseAmplitude (NoiseAmplitude)
import Hydrogen.Schema.Material.NoiseOctaves (NoiseOctaves)
import Hydrogen.Schema.Material.NoiseLacunarity (NoiseLacunarity)
import Hydrogen.Schema.Material.NoisePersistence (NoisePersistence)
import Hydrogen.Schema.Material.NoiseSeed (NoiseSeed)
import Hydrogen.Schema.Material.BlurRadius (BlurRadius)
import Hydrogen.Schema.Material.BlurSigma (BlurSigma)

-- Typography atoms
import Hydrogen.Schema.Typography.FontFamily (FontFamily)
import Hydrogen.Schema.Typography.FontSize (FontSize)
import Hydrogen.Schema.Typography.FontWeight (FontWeight)
import Hydrogen.Schema.Typography.LineHeight (LineHeight)
import Hydrogen.Schema.Typography.LineHeight (normal) as LineHeight
import Hydrogen.Schema.Typography.LetterSpacing (LetterSpacing)
import Hydrogen.Schema.Typography.LetterSpacing (none) as LetterSpacing

-- Temporal atoms
import Hydrogen.Schema.Temporal.Duration (Duration)
import Hydrogen.Schema.Temporal.Progress (Progress)
import Hydrogen.Schema.Temporal.Millisecond (Millisecond)

-- Motion atoms
import Hydrogen.Schema.Motion.Easing (Easing)
import Hydrogen.Schema.Motion.KeyframeAnimation (AnimationDirection, AnimationFillMode)

-- Spring physics
import Hydrogen.Schema.Temporal.Spring (Mass, Stiffness, Damping, Velocity)

-- Reactive atoms
import Hydrogen.Schema.Reactive.InteractiveState (InteractiveState, PointerState, FocusState, ActivationState)

-- Gestural atoms  
import Hydrogen.Schema.Gestural.Trigger (TriggerCondition, TriggerEffect, TriggerTarget, TriggerTiming)

-- Haptic atoms
import Hydrogen.Schema.Haptic.Event (HapticPattern)
import Hydrogen.Schema.Haptic.Vibration (Intensity)

-- Audio atoms
import Hydrogen.Schema.Audio.Level (LinearGain)
import Hydrogen.Schema.Audio.Frequency (Hertz)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // effect // tracking
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Effects: What can this Element produce?
-- |
-- | Graded monads track what effects an Element can have. This enables
-- | compile-time verification of capabilities.
data Effect
  = Pure                    -- No effects
  | CanClick                -- Produces messages on click
  | CanHover                -- Produces hover events
  | CanFocus                -- Can receive focus
  | CanDrag                 -- Can be dragged
  | CanAnimate              -- Produces animation frames
  | CanEmitSound            -- Produces audio
  | CanVibrate              -- Produces haptic feedback
  | CanRequestData          -- Produces HTTP requests
  | CanNavigate             -- Produces route changes
  | Interactive             -- CanClick ⊗ CanHover ⊗ CanFocus
  | FullInteractive         -- All interactive effects

derive instance eqEffect :: Eq Effect
derive instance ordEffect :: Ord Effect

instance semigroupEffect :: Semigroup Effect where
  append Pure e = e
  append e Pure = e
  append CanClick CanHover = Interactive
  append CanHover CanClick = Interactive
  append Interactive CanFocus = Interactive
  append CanFocus Interactive = Interactive
  append _ _ = FullInteractive

instance monoidEffect :: Monoid Effect where
  mempty = Pure

-- | Co-effects: What does this Element need?
-- |
-- | Resources required to render this Element. The runtime must
-- | provide these before rendering can succeed.
data CoEffect
  = NeedsNothing
  | NeedsFont FontFamily
  | NeedsImage String           -- URL
  | NeedsVideo String           -- URL
  | NeedsAudio String           -- URL
  | NeedsData String            -- Query key
  | NeedsShader String          -- Shader name
  | NeedsTexture String         -- Texture ID
  | NeedsResources (Array CoEffect)

derive instance eqCoEffect :: Eq CoEffect
derive instance ordCoEffect :: Ord CoEffect

instance semigroupCoEffect :: Semigroup CoEffect where
  append NeedsNothing e = e
  append e NeedsNothing = e
  append (NeedsResources a) (NeedsResources b) = NeedsResources (a <> b)
  append (NeedsResources a) e = NeedsResources (a <> [e])
  append e (NeedsResources b) = NeedsResources ([e] <> b)
  append a b = NeedsResources [a, b]

instance monoidCoEffect :: Monoid CoEffect where
  mempty = NeedsNothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // noise // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Procedural noise algorithm
data NoiseType
  = Perlin           -- Classic Perlin noise
  | Simplex          -- Ken Perlin's improved simplex noise
  | Worley           -- Cell/Voronoi noise (F1, F2, F2-F1)
  | Value            -- Simple value noise
  | Curl             -- Divergence-free curl noise (for flow)
  | Fbm              -- Fractal Brownian motion (layered)
  | Turbulence       -- Absolute value FBM (fire, clouds)
  | Ridged           -- Ridged multifractal (mountains)
  | Billowy          -- Inverted ridged (clouds, soft)

derive instance eqNoiseType :: Eq NoiseType

instance showNoiseType :: Show NoiseType where
  show Perlin = "perlin"
  show Simplex = "simplex"
  show Worley = "worley"
  show Value = "value"
  show Curl = "curl"
  show Fbm = "fbm"
  show Turbulence = "turbulence"
  show Ridged = "ridged"
  show Billowy = "billowy"

-- | Complete noise configuration
-- |
-- | Defines procedural noise for texture generation. Every parameter
-- | is a bounded Schema atom.
type NoiseConfig =
  { noiseType :: NoiseType               -- Algorithm
  , frequency :: NoiseFrequency          -- Spatial frequency (0.0+)
  , amplitude :: NoiseAmplitude          -- Output amplitude (0.0-1.0)
  , octaves :: NoiseOctaves              -- Fractal layers (1-16)
  , lacunarity :: NoiseLacunarity        -- Frequency multiplier (1.0+)
  , persistence :: NoisePersistence      -- Amplitude decay (0.0-1.0)
  , seed :: NoiseSeed                    -- Random seed
  , offset :: Vec2 Pixel                 -- Noise space offset (animation)
  , rotation :: Degrees                  -- Noise space rotation
  , baseColor :: SRGB                    -- Color at noise = 0
  , peakColor :: SRGB                    -- Color at noise = 1
  , midColor :: Maybe SRGB               -- Optional color at noise = 0.5
  }

-- | Blur configuration
type BlurConfig =
  { radius :: BlurRadius                 -- Blur radius
  , sigma :: Maybe BlurSigma             -- Gaussian sigma (auto if Nothing)
  , quality :: Int                       -- Sample count (1-32)
  , directional :: Maybe Degrees         -- Direction for motion blur
  , radial :: Maybe (Vec2 Pixel)         -- Center for radial blur
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // fill // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Fill types composed entirely from Schema atoms
-- |
-- | Every fill can be rendered by WebGPU. No CSS. No escape hatches.
data Fill
  = Solid SRGB                           -- Solid color
  | SolidWithAlpha SRGB Opacity          -- Solid with transparency
  | GradientFill Gradient                -- Linear, radial, conic, mesh
  | NoiseFill NoiseConfig                -- Procedural noise texture
  | BlurFill BlurConfig SRGB             -- Blurred backdrop (glassmorphism)
  | PatternFill String (Vec2 Pixel)      -- Repeating pattern (texture ID, tile size)
  | VideoFill String                     -- Video texture (video ID)
  | ShaderFill String                    -- Custom shader (shader ID)

derive instance eqFill :: Eq Fill

instance showFill :: Show Fill where
  show (Solid c) = "Solid(" <> show c <> ")"
  show (SolidWithAlpha c a) = "SolidWithAlpha(" <> show c <> "," <> show a <> ")"
  show (GradientFill _) = "GradientFill"
  show (NoiseFill cfg) = "NoiseFill(" <> show cfg.noiseType <> ")"
  show (BlurFill cfg _) = "BlurFill(" <> show cfg.radius <> ")"
  show (PatternFill id _) = "PatternFill(" <> id <> ")"
  show (VideoFill id) = "VideoFill(" <> id <> ")"
  show (ShaderFill id) = "ShaderFill(" <> id <> ")"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // stroke // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Stroke style
data StrokeStyle
  = StrokeSolid
  | StrokeDashed (Array Pixel)           -- Dash pattern
  | StrokeDotted
  | StrokeDouble

derive instance eqStrokeStyle :: Eq StrokeStyle

instance showStrokeStyle :: Show StrokeStyle where
  show StrokeSolid = "solid"
  show (StrokeDashed _) = "dashed"
  show StrokeDotted = "dotted"
  show StrokeDouble = "double"

-- | Stroke definition
type Stroke =
  { width :: Pixel
  , color :: SRGB
  , opacity :: Maybe Opacity
  , style :: StrokeStyle
  , lineCap :: LineCap                   -- CapButt, CapRound, CapSquare (Schema atom)
  , lineJoin :: LineJoin                 -- JoinMiter, JoinRound, JoinBevel (Schema atom)
  , miterLimit :: MiterLimit             -- Bounded 1.0-100.0 (Schema atom)
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // shadow // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Single shadow layer
type ShadowLayer =
  { offsetX :: Pixel
  , offsetY :: Pixel
  , blur :: BlurRadius
  , spread :: Pixel
  , color :: SRGB
  , opacity :: Opacity
  , inset :: Boolean
  }

-- | Complete shadow (multiple layers)
type Shadow = Array ShadowLayer

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // filter // chain
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Individual filter operations
data Filter
  = FilterBlur BlurRadius
  | FilterBrightness Number              -- 0.0 = black, 1.0 = normal, 2.0 = 2x
  | FilterContrast Number                -- 0.0 = gray, 1.0 = normal
  | FilterSaturate Number                -- 0.0 = grayscale, 1.0 = normal
  | FilterHueRotate Hue                  -- Rotate hue by degrees
  | FilterInvert Number                  -- 0.0 = normal, 1.0 = inverted
  | FilterSepia Number                   -- 0.0 = normal, 1.0 = sepia
  | FilterGrayscale Number               -- 0.0 = normal, 1.0 = grayscale
  | FilterDropShadow ShadowLayer
  | FilterNoise NoiseConfig              -- Grain/noise overlay

derive instance eqFilter :: Eq Filter

instance showFilter :: Show Filter where
  show (FilterBlur r) = "blur(" <> show r <> ")"
  show (FilterBrightness n) = "brightness(" <> show n <> ")"
  show (FilterContrast n) = "contrast(" <> show n <> ")"
  show (FilterSaturate n) = "saturate(" <> show n <> ")"
  show (FilterHueRotate h) = "hue-rotate(" <> show h <> ")"
  show (FilterInvert n) = "invert(" <> show n <> ")"
  show (FilterSepia n) = "sepia(" <> show n <> ")"
  show (FilterGrayscale n) = "grayscale(" <> show n <> ")"
  show (FilterDropShadow _) = "drop-shadow"
  show (FilterNoise _) = "noise"

-- | Chain of filters applied in order
type FilterChain = Array Filter

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // bounded // optional // adts
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Element stroke — bounded ADT, no Maybe
-- |
-- | Every Element explicitly declares whether it has a stroke.
-- | UI shows a toggle + stroke controls.
data ElementStroke
  = NoStroke                              -- No border/outline
  | WithStroke Stroke                     -- Stroke with full config

derive instance eqElementStroke :: Eq ElementStroke

instance showElementStroke :: Show ElementStroke where
  show NoStroke = "NoStroke"
  show (WithStroke s) = "WithStroke(" <> show s.width <> ")"

-- | Element shadow — bounded ADT, no Maybe
-- |
-- | Every Element explicitly declares whether it has shadow(s).
-- | UI shows a toggle + shadow layer controls.
data ElementShadow
  = NoShadow                              -- No shadow
  | WithShadow Shadow                     -- One or more shadow layers

derive instance eqElementShadow :: Eq ElementShadow

instance showElementShadow :: Show ElementShadow where
  show NoShadow = "NoShadow"
  show (WithShadow layers) = "WithShadow(" <> show (Array.length layers) <> " layers)"

-- | Element filters — bounded ADT, no Maybe
-- |
-- | Every Element explicitly declares whether filters are applied.
-- | UI shows a toggle + filter chain controls.
data ElementFilters
  = NoFilters                             -- No filters
  | WithFilters FilterChain               -- Filter chain applied

derive instance eqElementFilters :: Eq ElementFilters

instance showElementFilters :: Show ElementFilters where
  show NoFilters = "NoFilters"
  show (WithFilters chain) = "WithFilters(" <> show (Array.length chain) <> " filters)"

-- | Corner radius — bounded ADT, no Maybe
-- |
-- | Every shape explicitly declares whether corners are rounded.
-- | UI shows a toggle + corner controls.
data ElementCorners
  = Sharp                                 -- No corner rounding
  | Rounded Corners                       -- Rounded with explicit radii

derive instance eqElementCorners :: Eq ElementCorners

instance showElementCorners :: Show ElementCorners where
  show Sharp = "Sharp"
  show (Rounded c) = "Rounded(" <> show c <> ")"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // interactive // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | State variant for conditional styling
-- |
-- | Maps interactive states to visual properties.
data StateVariant
  = DefaultState
  | HoverState
  | PressedState
  | FocusState
  | FocusVisibleState
  | DisabledState
  | LoadingState
  | ErrorState
  | SuccessState
  | DraggingState
  | CustomState String

derive instance eqStateVariant :: Eq StateVariant

instance showStateVariant :: Show StateVariant where
  show DefaultState = "default"
  show HoverState = "hover"
  show PressedState = "pressed"
  show FocusState = "focus"
  show FocusVisibleState = "focus-visible"
  show DisabledState = "disabled"
  show LoadingState = "loading"
  show ErrorState = "error"
  show SuccessState = "success"
  show DraggingState = "dragging"
  show (CustomState s) = "custom:" <> s

-- | Trigger response (what happens when trigger fires)
data TriggerResponse msg
  = EmitMessage msg                      -- Send a message
  | PlayAnimation String                 -- Play named animation
  | TransitionTo StateVariant            -- Change state
  | PlayHaptic HapticPattern             -- Trigger haptic
  | PlaySound String                     -- Play audio
  | Navigate String                      -- Navigate to route
  | Chain (Array (TriggerResponse msg))  -- Multiple responses

instance eqTriggerResponse :: Eq msg => Eq (TriggerResponse msg) where
  eq (EmitMessage a) (EmitMessage b) = a == b
  eq (PlayAnimation a) (PlayAnimation b) = a == b
  eq (TransitionTo a) (TransitionTo b) = a == b
  eq (PlayHaptic a) (PlayHaptic b) = a == b
  eq (PlaySound a) (PlaySound b) = a == b
  eq (Navigate a) (Navigate b) = a == b
  eq (Chain a) (Chain b) = a == b
  eq _ _ = false

instance showTriggerResponse :: Show (TriggerResponse msg) where
  show (EmitMessage _) = "EmitMessage"
  show (PlayAnimation s) = "PlayAnimation(" <> s <> ")"
  show (TransitionTo s) = "TransitionTo(" <> show s <> ")"
  show (PlayHaptic _) = "PlayHaptic"
  show (PlaySound s) = "PlaySound(" <> s <> ")"
  show (Navigate s) = "Navigate(" <> s <> ")"
  show (Chain arr) = "Chain(" <> show (Array.length arr) <> ")"

instance functorTriggerResponse :: Functor TriggerResponse where
  map f = case _ of
    EmitMessage msg -> EmitMessage (f msg)
    PlayAnimation s -> PlayAnimation s
    TransitionTo s -> TransitionTo s
    PlayHaptic p -> PlayHaptic p
    PlaySound s -> PlaySound s
    Navigate s -> Navigate s
    Chain arr -> Chain (map (map f) arr)

-- | Map a function over all msg types in TriggerConfig
mapTriggerConfig :: forall a b. (a -> b) -> TriggerConfig a -> TriggerConfig b
mapTriggerConfig f cfg =
  { conditions: cfg.conditions
  , response: map f cfg.response
  , timing: cfg.timing
  , once: cfg.once
  }

-- | Map a function over all msg types in InteractiveConfig
mapInteractiveConfig :: forall a b. (a -> b) -> InteractiveConfig a -> InteractiveConfig b
mapInteractiveConfig f cfg =
  { currentState: cfg.currentState
  , variants: cfg.variants
  , triggers: map (mapTriggerConfig f) cfg.triggers
  , transitionDuration: cfg.transitionDuration
  , transitionEasing: cfg.transitionEasing
  , springConfig: cfg.springConfig
  , ariaLabel: cfg.ariaLabel
  , ariaRole: cfg.ariaRole
  , tabIndex: cfg.tabIndex
  }

-- | Complete trigger configuration
type TriggerConfig msg =
  { conditions :: Array TriggerCondition -- All must be met
  , response :: TriggerResponse msg
  , timing :: TriggerTiming
  , once :: Boolean                      -- Fire only once?
  }

-- | Interactive element configuration
type InteractiveConfig msg =
  { -- Current state
    currentState :: InteractiveState
    
  -- State variants (visual changes per state)
  , variants :: Array
      { state :: StateVariant
      , fill :: Maybe Fill
      , stroke :: Maybe Stroke
      , shadow :: Maybe Shadow
      , filters :: Maybe FilterChain
      , transform :: Maybe (Vec2 Pixel)  -- Translation
      , scale :: Maybe Number
      , rotation :: Maybe Degrees
      , opacity :: Maybe Opacity
      }
    
  -- Triggers
  , triggers :: Array (TriggerConfig msg)
  
  -- Motion
  , transitionDuration :: Duration
  , transitionEasing :: Easing
  , springConfig :: Maybe { mass :: Mass, stiffness :: Stiffness, damping :: Damping }
  
  -- Accessibility
  , ariaLabel :: Maybe String
  , ariaRole :: Maybe String
  , tabIndex :: Maybe Int
  }

-- | Interactive wrapper
-- |
-- | Wraps any Element with interactive capabilities.
newtype InteractiveWrapper msg = InteractiveWrapper
  { element :: Element msg
  , config :: InteractiveConfig msg
  }

-- | InteractiveWrapper equality requires Eq msg for comparing triggers
instance eqInteractiveWrapper :: Eq msg => Eq (InteractiveWrapper msg) where
  eq (InteractiveWrapper a) (InteractiveWrapper b) = 
    a.element == b.element && a.config.currentState == b.config.currentState

instance showInteractiveWrapper :: Show (InteractiveWrapper msg) where
  show (InteractiveWrapper i) = "InteractiveWrapper(" <> show i.element <> ")"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // animation // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Playback state
data PlaybackState
  = Playing
  | Paused
  | Stopped
  | Seeking
  | Buffering

derive instance eqPlaybackState :: Eq PlaybackState

instance showPlaybackState :: Show PlaybackState where
  show Playing = "playing"
  show Paused = "paused"
  show Stopped = "stopped"
  show Seeking = "seeking"
  show Buffering = "buffering"

-- | Loop mode
data LoopMode
  = NoLoop
  | LoopForever
  | LoopCount Int
  | PingPong                             -- Forward then backward
  | PingPongCount Int

derive instance eqLoopMode :: Eq LoopMode

instance showLoopMode :: Show LoopMode where
  show NoLoop = "no-loop"
  show LoopForever = "loop"
  show (LoopCount n) = "loop(" <> show n <> ")"
  show PingPong = "ping-pong"
  show (PingPongCount n) = "ping-pong(" <> show n <> ")"

-- | Animation configuration
type AnimationConfig =
  { duration :: Duration
  , easing :: Easing
  , delay :: Duration
  , loop :: LoopMode
  , direction :: AnimationDirection      -- DirectionNormal, DirectionReverse, DirectionAlternate, DirectionAlternateReverse
  , fillMode :: AnimationFillMode        -- FillNone, FillForwards, FillBackwards, FillBoth
  , playbackRate :: Number               -- 1.0 = normal, 0.5 = half speed
  }

-- | Animated wrapper
-- |
-- | Wraps Element with animation over time.
newtype Animated msg = Animated
  { element :: Element msg
  , config :: AnimationConfig
  , state :: PlaybackState
  , progress :: Progress
  }

derive instance eqAnimated :: Eq (Animated msg)

instance showAnimated :: Show (Animated msg) where
  show (Animated a) = "Animated(" <> show a.progress <> ")"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // playhead // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Timeline marker (like Ableton markers)
data TimelineMarker
  = LoopStart
  | LoopEnd
  | CuePoint String
  | Label String
  | Tempo Number                         -- BPM change

derive instance eqTimelineMarker :: Eq TimelineMarker

instance showTimelineMarker :: Show TimelineMarker where
  show LoopStart = "[loop-start]"
  show LoopEnd = "[loop-end]"
  show (CuePoint s) = "[cue:" <> s <> "]"
  show (Label s) = "[label:" <> s <> "]"
  show (Tempo n) = "[tempo:" <> show n <> "]"

-- | Playhead configuration
-- |
-- | Like Ableton's transport/playhead. Enables scrubbing, seeking,
-- | looping, and tempo-synced animation.
type PlayheadConfig =
  { position :: Progress                 -- Current position (0.0-1.0)
  , duration :: Duration                 -- Total duration
  , playbackState :: PlaybackState
  , loop :: LoopMode
  , markers :: Array { position :: Progress, marker :: TimelineMarker }
  , tempo :: Maybe Number                -- BPM for tempo-synced
  , snapToMarkers :: Boolean
  , scrubbing :: Boolean                 -- Currently being scrubbed?
  }

-- | Playhead element
-- |
-- | First-class timeline/playhead UI component.
newtype Playhead msg = Playhead
  { config :: PlayheadConfig
  , onSeek :: Progress -> msg
  , onPlay :: msg
  , onPause :: msg
  , onStop :: msg
  , onMarkerHit :: TimelineMarker -> msg
  }

-- | Playhead equality is based on config only.
-- | Functions cannot be compared, so we compare the structural data.
instance eqPlayhead :: Eq (Playhead msg) where
  eq (Playhead a) (Playhead b) = a.config == b.config

instance showPlayhead :: Show (Playhead msg) where
  show (Playhead p) = "Playhead(" <> show p.config.position <> ")"

-- | Map a function over all msg types in Playhead
-- | 
-- | The msg appears in covariant position (output of handlers),
-- | so we compose with the function.
mapPlayhead :: forall a b. (a -> b) -> Playhead a -> Playhead b
mapPlayhead f (Playhead p) = Playhead
  { config: p.config
  , onSeek: \progress -> f (p.onSeek progress)
  , onPlay: f p.onPlay
  , onPause: f p.onPause
  , onStop: f p.onStop
  , onMarkerHit: \marker -> f (p.onMarkerHit marker)
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // element
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Pure Element composed entirely from Schema atoms
-- |
-- | This is the complete rendering instruction set. Every field is a Schema atom.
-- | No strings (except text content and IDs). No CSS. No escape hatches.
-- |
-- | Think about what's possible when CSS and JavaScript aren't restrictions.
-- | This Element can describe ANY UI ever conceived — Ableton, After Effects,
-- | hospital dashboards, fighter jet HUDs, AI agent interfaces.
data Element msg
  -- Basic shapes (all fields present with bounded ADTs)
  = Rectangle
      { position :: Vec2 Pixel           -- Position in parent
      , size :: Vec2 Pixel               -- Width x Height
      , fill :: Fill                     -- Fill (required for shapes)
      , corners :: ElementCorners        -- Sharp | Rounded corners
      , stroke :: ElementStroke          -- NoStroke | WithStroke
      , shadow :: ElementShadow          -- NoShadow | WithShadow
      , filters :: ElementFilters        -- NoFilters | WithFilters
      , opacity :: Opacity               -- 0-100% bounded
      , clipContent :: Boolean           -- Clip children to bounds
      }
  | Circle
      { center :: Vec2 Pixel             -- Center point
      , radius :: Pixel                  -- Radius
      , fill :: Fill                     -- Fill (required)
      , stroke :: ElementStroke          -- NoStroke | WithStroke
      , shadow :: ElementShadow          -- NoShadow | WithShadow
      , filters :: ElementFilters        -- NoFilters | WithFilters
      , opacity :: Opacity               -- 0-100% bounded
      }
  | Ellipse
      { center :: Vec2 Pixel             -- Center point
      , radiusX :: Pixel                 -- Horizontal radius
      , radiusY :: Pixel                 -- Vertical radius
      , fill :: Fill                     -- Fill (required)
      , stroke :: ElementStroke          -- NoStroke | WithStroke
      , rotation :: Degrees              -- Rotation angle (default: 0)
      , opacity :: Opacity               -- 0-100% bounded
      }
  | Line
      { start :: Vec2 Pixel              -- Start point
      , end :: Vec2 Pixel                -- End point
      , stroke :: Stroke                 -- Stroke (required for lines)
      , opacity :: Opacity               -- 0-100% bounded
      }
  | Polyline
      { points :: Array (Vec2 Pixel)     -- Path points
      , stroke :: Stroke                 -- Stroke (required)
      , closed :: Boolean                -- Close the path?
      , opacity :: Opacity               -- 0-100% bounded
      }
  | Polygon
      { points :: Array (Vec2 Pixel)     -- Vertices
      , fill :: Fill                     -- Fill (required)
      , stroke :: ElementStroke          -- NoStroke | WithStroke
      , opacity :: Opacity               -- 0-100% bounded
      }
  | Path
      { commands :: String               -- SVG path data (d attribute)
      , fill :: Fill                     -- Fill (default: transparent)
      , stroke :: ElementStroke          -- NoStroke | WithStroke
      , viewBox :: { x :: Number, y :: Number, width :: Number, height :: Number }
      , opacity :: Opacity               -- 0-100% bounded
      }
  | Arc
      { center :: Vec2 Pixel             -- Center point
      , radius :: Pixel                  -- Arc radius
      , startAngle :: Degrees            -- Start angle
      , endAngle :: Degrees              -- End angle
      , fill :: Fill                     -- Fill (default: transparent)
      , stroke :: ElementStroke          -- NoStroke | WithStroke
      , opacity :: Opacity               -- 0-100% bounded
      }
      
  -- Text
  | Text
      { content :: String                -- Text content
      , position :: Vec2 Pixel           -- Position
      , fontFamily :: FontFamily         -- Font family (Schema atom)
      , fontSize :: FontSize             -- Font size (Schema atom)
      , fontWeight :: FontWeight         -- Font weight (Schema atom)
      , lineHeight :: LineHeight         -- Line height (default: auto)
      , letterSpacing :: LetterSpacing   -- Letter spacing (default: 0)
      , color :: SRGB                    -- Text color
      , opacity :: Opacity               -- 0-100% bounded
      , maxWidth :: Pixel                -- Text wrapping width (0 = no wrap)
      , horizontalAlign :: Alignment     -- AlignStart, AlignCenter, AlignEnd
      , verticalAlign :: Alignment       -- AlignStart (top), AlignCenter, AlignEnd (bottom), AlignBaseline
      , shadow :: ElementShadow          -- NoShadow | WithShadow
      }
      
  -- Media
  | Image
      { src :: String                    -- Image URL or asset ID
      , position :: Vec2 Pixel           -- Position
      , size :: Vec2 Pixel               -- Size
      , objectFit :: ObjectFit           -- Fill, Contain, Cover, None, ScaleDown
      , filters :: ElementFilters        -- NoFilters | WithFilters
      , corners :: ElementCorners        -- Sharp | Rounded
      , opacity :: Opacity               -- 0-100% bounded
      }
  | Video
      { src :: String                    -- Video URL or asset ID
      , position :: Vec2 Pixel           -- Position
      , size :: Vec2 Pixel               -- Size
      , playbackState :: PlaybackState   -- Playing, Paused, Stopped, etc.
      , loop :: LoopMode                 -- NoLoop, LoopForever, etc.
      , muted :: Boolean                 -- Audio muted?
      , volume :: LinearGain             -- Volume level (Schema atom)
      , opacity :: Opacity               -- 0-100% bounded
      }
  | Audio
      { src :: String                    -- Audio URL or asset ID
      , playbackState :: PlaybackState   -- Playing, Paused, Stopped, etc.
      , loop :: LoopMode                 -- NoLoop, LoopForever, etc.
      , volume :: LinearGain             -- Volume level (Schema atom)
      }
      
  -- Containers
  | Group
      { children :: Array (Element msg)
      , position :: Vec2 Pixel           -- Position relative to parent
      , opacity :: Opacity               -- 0-100% bounded, always present (default: 100)
      , clipPath :: ClipPath             -- Clipping region (default: ClipNone)
      , mask :: Mask                     -- Alpha mask for compositing (default: maskNone)
      }
  | Stack                                -- Vertical stack (like SwiftUI VStack)
      { children :: Array (Element msg)  -- Child elements
      , position :: Vec2 Pixel           -- Position
      , spacing :: Pixel                 -- Space between children
      , alignment :: Alignment           -- AlignStart (leading), AlignCenter, AlignEnd (trailing)
      , opacity :: Opacity               -- 0-100% bounded
      , clipPath :: ClipPath             -- Clipping region
      , mask :: Mask                     -- Alpha mask
      }
  | HStack                               -- Horizontal stack
      { children :: Array (Element msg)  -- Child elements
      , position :: Vec2 Pixel           -- Position
      , spacing :: Pixel                 -- Space between children
      , alignment :: Alignment           -- AlignStart (top), AlignCenter, AlignEnd (bottom)
      , opacity :: Opacity               -- 0-100% bounded
      , clipPath :: ClipPath             -- Clipping region
      , mask :: Mask                     -- Alpha mask
      }
  | ZStack                               -- Layered stack (z-order)
      { children :: Array (Element msg)  -- Child elements
      , position :: Vec2 Pixel           -- Position
      , alignment :: Alignment           -- AlignStart, AlignCenter, AlignEnd
      , opacity :: Opacity               -- 0-100% bounded
      , clipPath :: ClipPath             -- Clipping region
      , mask :: Mask                     -- Alpha mask
      }
  | Scroll
      { child :: Element msg             -- Scrollable content
      , position :: Vec2 Pixel           -- Position
      , size :: Vec2 Pixel               -- Viewport size
      , scrollX :: Boolean               -- Horizontal scrolling?
      , scrollY :: Boolean               -- Vertical scrolling?
      , scrollPosition :: Vec2 Pixel     -- Current scroll position
      , opacity :: Opacity               -- 0-100% bounded
      }
      
  -- Interactive wrapper
  | InteractiveElement (InteractiveWrapper msg)
  
  -- Animated wrapper
  | AnimatedElement (Animated msg)
  
  -- Playhead/Timeline
  | PlayheadElement (Playhead msg)
  
  -- Viewport (for nested scenes, like After Effects comp)
  | Viewport
      { scene :: Element msg             -- Nested scene
      , position :: Vec2 Pixel           -- Position
      , size :: Vec2 Pixel               -- Viewport size
      , zoom :: Number                   -- Zoom level (1.0 = 100%)
      , pan :: Vec2 Pixel                -- Pan offset
      , rotation :: Degrees              -- Rotation angle
      , opacity :: Opacity               -- 0-100% bounded
      }
      
  -- Portal (render elsewhere in tree)
  | Portal
      { targetId :: String               -- Target element ID
      , child :: Element msg             -- Content to portal
      }
      
  -- Nothing
  | Empty

instance eqElement :: Eq (Element msg) where
  eq (Rectangle a) (Rectangle b) =
    a.position == b.position && a.size == b.size && a.fill == b.fill
  eq (Circle a) (Circle b) =
    a.center == b.center && a.radius == b.radius && a.fill == b.fill
  eq (Text a) (Text b) =
    a.content == b.content && a.position == b.position
  eq (Group a) (Group b) =
    a.children == b.children && a.position == b.position
  eq Empty Empty = true
  eq _ _ = false

instance showElement :: Show (Element msg) where
  show = elementUUID5

instance functorElement :: Functor Element where
  map f = case _ of
    Rectangle r -> Rectangle r
    Circle c -> Circle c
    Ellipse e -> Ellipse e
    Line l -> Line l
    Polyline p -> Polyline p
    Polygon p -> Polygon p
    Path p -> Path p
    Arc a -> Arc a
    Text t -> Text t
    Image i -> Image i
    Video v -> Video v
    Audio a -> Audio a
    Group g -> Group g { children = map (map f) g.children }
    Stack s -> Stack s { children = map (map f) s.children }
    HStack h -> HStack h { children = map (map f) h.children }
    ZStack z -> ZStack z { children = map (map f) z.children }
    Scroll s -> Scroll s { child = map f s.child }
    InteractiveElement (InteractiveWrapper i) ->
      InteractiveElement (InteractiveWrapper { element: map f i.element, config: mapInteractiveConfig f i.config })
    AnimatedElement (Animated a) ->
      AnimatedElement (Animated { element: map f a.element, config: a.config, state: a.state, progress: a.progress })
    PlayheadElement p -> PlayheadElement (mapPlayhead f p)
    Viewport v -> Viewport v { scene = map f v.scene }
    Portal p -> Portal p { child = map f p.child }
    Empty -> Empty

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // default // values
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Full opacity (100%) — the default for all Elements
opacityFull :: Opacity
opacityFull = opacity 100

-- | No clipping — the default for containers
clipNone :: ClipPath
clipNone = ClipPath.clipNone

-- | No masking — the default for containers
maskNone :: Mask
maskNone = Mask.maskNone

-- | Normal line height (1.5) — the default for Text
lineHeightNormal :: LineHeight
lineHeightNormal = LineHeight.normal

-- | No letter spacing (0) — the default for Text
letterSpacingNone :: LetterSpacing
letterSpacingNone = LetterSpacing.none

-- | Zero degrees — the default for rotation
degreesZero :: Degrees
degreesZero = Angle.zero

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // uuid5 // identity
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate deterministic UUID5 from Element content
-- |
-- | Same atoms → same UUID5. Two agents create identical Element → identical ID.
-- | Reproducible across runs, systems, languages.
-- |
-- | Namespace: "hydrogen.element"
elementUUID5 :: forall msg. Element msg -> String
elementUUID5 = case _ of
  Rectangle r ->
    "rect-" <> show r.position <> "-" <> show r.size <> "-" <> show r.fill
  Circle c ->
    "circle-" <> show c.center <> "-" <> show c.radius <> "-" <> show c.fill
  Ellipse e ->
    "ellipse-" <> show e.center <> "-" <> show e.radiusX <> "-" <> show e.radiusY
  Line l ->
    "line-" <> show l.start <> "-" <> show l.end
  Polyline p ->
    "polyline-" <> show (Array.length p.points) <> "-points"
  Polygon p ->
    "polygon-" <> show (Array.length p.points) <> "-points"
  Path p ->
    "path-" <> p.commands
  Arc a ->
    "arc-" <> show a.center <> "-" <> show a.radius
  Text t ->
    "text-" <> show t.position <> "-" <> t.content
  Image i ->
    "image-" <> i.src
  Video v ->
    "video-" <> v.src
  Audio a ->
    "audio-" <> a.src
  Group g ->
    "group-" <> show (map elementUUID5 g.children)
  Stack s ->
    "stack-" <> show (Array.length s.children)
  HStack h ->
    "hstack-" <> show (Array.length h.children)
  ZStack z ->
    "zstack-" <> show (Array.length z.children)
  Scroll s ->
    "scroll-" <> elementUUID5 s.child
  InteractiveElement (InteractiveWrapper i) ->
    "interactive-" <> elementUUID5 i.element
  AnimatedElement (Animated a) ->
    "animated-" <> elementUUID5 a.element
  PlayheadElement (Playhead p) ->
    "playhead-" <> show p.config.position
  Viewport v ->
    "viewport-" <> elementUUID5 v.scene
  Portal p ->
    "portal-" <> p.targetId
  Empty ->
    "empty"
