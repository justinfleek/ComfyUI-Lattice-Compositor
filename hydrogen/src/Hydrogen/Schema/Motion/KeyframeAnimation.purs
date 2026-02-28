-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // motion // keyframe // animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | KeyframeAnimation — Complete animation sequences for UI components.
-- |
-- | ## Design Philosophy
-- |
-- | A KeyframeAnimation is a **complete animation specification** as pure data:
-- | - Sequence of keyframes defining property values at specific times
-- | - Duration, iteration count, direction, fill mode
-- | - Can target any animatable property (opacity, transform, color, etc.)
-- |
-- | This is NOT CSS `@keyframes` (though it can export to that format).
-- | This is a Schema atom that describes animation **semantically**.
-- |
-- | ## Use Cases
-- |
-- | - Button hover effects (scale up, glow)
-- | - Loading spinners (rotation, pulse)
-- | - Enter/exit transitions (fade, slide)
-- | - Attention animations (shake, bounce, wiggle)
-- | - Success/error feedback (checkmark draw, error shake)
-- |
-- | ## Composition
-- |
-- | Animations compose:
-- | - `sequence`: Play animations one after another
-- | - `parallel`: Play animations simultaneously
-- | - `stagger`: Play with delay between each
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Same KeyframeAnimation = same visual output. Deterministic.
-- | UUID5 derived from animation content ensures identity.

module Hydrogen.Schema.Motion.KeyframeAnimation
  ( -- * Core Types
    KeyframeAnimation
  , AnimationId
  , AnimationProperty
      ( PropOpacity
      , PropTranslateX
      , PropTranslateY
      , PropTranslateZ
      , PropRotate
      , PropRotateX
      , PropRotateY
      , PropRotateZ
      , PropScale
      , PropScaleX
      , PropScaleY
      , PropSkewX
      , PropSkewY
      , PropBackgroundColor
      , PropBorderColor
      , PropShadowColor
      , PropBlur
      , PropBrightness
      , PropSaturate
      , PropCustom
      )
  , AnimationDirection
      ( DirectionNormal
      , DirectionReverse
      , DirectionAlternate
      , DirectionAlternateReverse
      )
  , allAnimationDirections
  , AnimationFillMode
      ( FillNone
      , FillForwards
      , FillBackwards
      , FillBoth
      )
  , allAnimationFillModes
  , AnimationPlayState
      ( PlayStatePlaying
      , PlayStatePaused
      )
  , allAnimationPlayStates
  , PropertyKeyframe
  
  -- * Constructors
  , keyframeAnimation
  , simpleAnimation
  , animationId
  
  -- * Property Keyframe Builders
  , propertyKeyframe
  , opacityKeyframe
  , translateXKeyframe
  , translateYKeyframe
  , rotateKeyframe
  , scaleKeyframe
  , colorKeyframe
  
  -- * Animation Builders
  , withDuration
  , withDelay
  , withIterations
  , withInfinite
  , withDirection
  , withFillMode
  , withEasing
  , withProperty
  , addKeyframe
  
  -- * Presets: Attention
  , bounce
  , flash
  , pulse
  , rubberBand
  , shake
  , swing
  , tada
  , wobble
  , jello
  , heartBeat
  
  -- * Presets: Enter
  , fadeIn
  , fadeInUp
  , fadeInDown
  , fadeInLeft
  , fadeInRight
  , slideInUp
  , slideInDown
  , slideInLeft
  , slideInRight
  , zoomIn
  , bounceIn
  
  -- * Presets: Exit
  , fadeOut
  , fadeOutUp
  , fadeOutDown
  , fadeOutLeft
  , fadeOutRight
  , slideOutUp
  , slideOutDown
  , slideOutLeft
  , slideOutRight
  , zoomOut
  , bounceOut
  
  -- * Presets: Loading
  , spin
  , spinReverse
  , pingPong
  , breathe
  
  -- * Accessors
  , duration
  , delay
  , iterations
  , direction
  , fillMode
  , keyframes
  , property
  
  -- * Predicates
  , isInfinite
  , isPaused
  , hasKeyframes
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (<>)
  , (<)
  , (>)
  , ($)
  , (+)
  , (*)
  , negate
  , otherwise
  )

import Data.Array (length, snoc)
import Hydrogen.Schema.Motion.Easing (Easing, easeInOut, easeOut, linear)
import Hydrogen.Schema.Temporal.Duration (Duration, fromMilliseconds)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // animation id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for an animation.
-- |
-- | Generated deterministically from animation content (UUID5).
newtype AnimationId = AnimationId String

derive instance eqAnimationId :: Eq AnimationId
derive instance ordAnimationId :: Ord AnimationId

instance showAnimationId :: Show AnimationId where
  show (AnimationId id) = "AnimationId(" <> id <> ")"

-- | Create animation ID from name.
animationId :: String -> AnimationId
animationId = AnimationId

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // animation property
-- ═════════════════════════════════════════════════════════════════════════════

-- | Properties that can be animated.
-- |
-- | These map to transform, opacity, filter, and color properties.
data AnimationProperty
  = PropOpacity           -- ^ 0.0 - 1.0
  | PropTranslateX        -- ^ Pixels
  | PropTranslateY        -- ^ Pixels
  | PropTranslateZ        -- ^ Pixels
  | PropRotate            -- ^ Degrees (2D rotation)
  | PropRotateX           -- ^ Degrees (3D)
  | PropRotateY           -- ^ Degrees (3D)
  | PropRotateZ           -- ^ Degrees (3D)
  | PropScale             -- ^ Uniform scale factor
  | PropScaleX            -- ^ X scale factor
  | PropScaleY            -- ^ Y scale factor
  | PropSkewX             -- ^ Degrees
  | PropSkewY             -- ^ Degrees
  | PropBackgroundColor   -- ^ OKLCH color
  | PropBorderColor       -- ^ OKLCH color
  | PropShadowColor       -- ^ OKLCH color
  | PropBlur              -- ^ Pixels
  | PropBrightness        -- ^ 0.0 - 2.0 (1.0 = normal)
  | PropSaturate          -- ^ 0.0 - 2.0 (1.0 = normal)
  | PropCustom String     -- ^ Custom property name

derive instance eqAnimationProperty :: Eq AnimationProperty
derive instance ordAnimationProperty :: Ord AnimationProperty

instance showAnimationProperty :: Show AnimationProperty where
  show PropOpacity = "opacity"
  show PropTranslateX = "translateX"
  show PropTranslateY = "translateY"
  show PropTranslateZ = "translateZ"
  show PropRotate = "rotate"
  show PropRotateX = "rotateX"
  show PropRotateY = "rotateY"
  show PropRotateZ = "rotateZ"
  show PropScale = "scale"
  show PropScaleX = "scaleX"
  show PropScaleY = "scaleY"
  show PropSkewX = "skewX"
  show PropSkewY = "skewY"
  show PropBackgroundColor = "backgroundColor"
  show PropBorderColor = "borderColor"
  show PropShadowColor = "shadowColor"
  show PropBlur = "blur"
  show PropBrightness = "brightness"
  show PropSaturate = "saturate"
  show (PropCustom name) = name

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // animation direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation playback direction.
data AnimationDirection
  = DirectionNormal           -- ^ Play forward
  | DirectionReverse          -- ^ Play backward
  | DirectionAlternate        -- ^ Forward, then backward
  | DirectionAlternateReverse -- ^ Backward, then forward

derive instance eqAnimationDirection :: Eq AnimationDirection
derive instance ordAnimationDirection :: Ord AnimationDirection

instance showAnimationDirection :: Show AnimationDirection where
  show DirectionNormal = "normal"
  show DirectionReverse = "reverse"
  show DirectionAlternate = "alternate"
  show DirectionAlternateReverse = "alternate-reverse"

-- | All animation directions for enumeration
allAnimationDirections :: Array AnimationDirection
allAnimationDirections =
  [ DirectionNormal
  , DirectionReverse
  , DirectionAlternate
  , DirectionAlternateReverse
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // animation fill mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | How animation applies styles before/after playing.
data AnimationFillMode
  = FillNone      -- ^ No styles applied outside animation
  | FillForwards  -- ^ Retain final keyframe styles
  | FillBackwards -- ^ Apply initial keyframe before start
  | FillBoth      -- ^ Both forwards and backwards

derive instance eqAnimationFillMode :: Eq AnimationFillMode
derive instance ordAnimationFillMode :: Ord AnimationFillMode

instance showAnimationFillMode :: Show AnimationFillMode where
  show FillNone = "none"
  show FillForwards = "forwards"
  show FillBackwards = "backwards"
  show FillBoth = "both"

-- | All animation fill modes for enumeration
allAnimationFillModes :: Array AnimationFillMode
allAnimationFillModes =
  [ FillNone
  , FillForwards
  , FillBackwards
  , FillBoth
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // animation play state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation play state.
data AnimationPlayState
  = PlayStatePlaying  -- ^ Animation is running
  | PlayStatePaused   -- ^ Animation is paused

derive instance eqAnimationPlayState :: Eq AnimationPlayState
derive instance ordAnimationPlayState :: Ord AnimationPlayState

instance showAnimationPlayState :: Show AnimationPlayState where
  show PlayStatePlaying = "running"
  show PlayStatePaused = "paused"

-- | All animation play states for enumeration
allAnimationPlayStates :: Array AnimationPlayState
allAnimationPlayStates =
  [ PlayStatePlaying
  , PlayStatePaused
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // property keyframe
-- ═════════════════════════════════════════════════════════════════════════════

-- | A keyframe for a specific property at a specific progress (0-100%).
-- |
-- | The value is a Number interpreted based on the property:
-- | - Opacity: 0.0 - 1.0
-- | - Translate: pixels
-- | - Rotate: degrees
-- | - Scale: factor (1.0 = 100%)
-- | - Color: packed OKLCH (L * 1000000 + C * 1000 + H)
type PropertyKeyframe =
  { progress :: Number    -- ^ 0.0 = start, 100.0 = end
  , value :: Number       -- ^ Property value
  , easing :: Easing      -- ^ Easing to next keyframe
  }

-- | Create a property keyframe.
propertyKeyframe :: Number -> Number -> Easing -> PropertyKeyframe
propertyKeyframe progress value easing =
  { progress: clampProgress progress
  , value
  , easing
  }
  where
    clampProgress p 
      | p < 0.0 = 0.0
      | p > 100.0 = 100.0
      | otherwise = p

-- | Create opacity keyframe.
opacityKeyframe :: Number -> Number -> PropertyKeyframe
opacityKeyframe progress opacity =
  propertyKeyframe progress (clampOpacity opacity) easeOut
  where
    clampOpacity o
      | o < 0.0 = 0.0
      | o > 1.0 = 1.0
      | otherwise = o

-- | Create translateX keyframe.
translateXKeyframe :: Number -> Number -> PropertyKeyframe
translateXKeyframe progress pixels =
  propertyKeyframe progress pixels easeOut

-- | Create translateY keyframe.
translateYKeyframe :: Number -> Number -> PropertyKeyframe
translateYKeyframe progress pixels =
  propertyKeyframe progress pixels easeOut

-- | Create rotation keyframe.
rotateKeyframe :: Number -> Number -> PropertyKeyframe
rotateKeyframe progress degrees =
  propertyKeyframe progress degrees easeInOut

-- | Create scale keyframe.
scaleKeyframe :: Number -> Number -> PropertyKeyframe
scaleKeyframe progress scale =
  propertyKeyframe progress scale easeOut

-- | Create color keyframe (packed OKLCH).
colorKeyframe :: Number -> Number -> Number -> Number -> PropertyKeyframe
colorKeyframe progress l c h =
  propertyKeyframe progress (packOKLCH l c h) easeOut
  where
    packOKLCH :: Number -> Number -> Number -> Number
    packOKLCH lightness chroma hue =
      lightness * 1000000.0 + chroma * 1000.0 + hue

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // keyframe animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete keyframe animation specification.
-- |
-- | Pure data describing an animation. Render targets interpret this
-- | as CSS @keyframes, GSAP timeline, or WebGPU shader animation.
newtype KeyframeAnimation = KeyframeAnimation
  { id :: AnimationId
  , name :: String
  , property :: AnimationProperty
  , keyframes :: Array PropertyKeyframe
  , duration :: Duration
  , delay :: Duration
  , iterations :: Number          -- ^ < 0 = infinite
  , direction :: AnimationDirection
  , fillMode :: AnimationFillMode
  , playState :: AnimationPlayState
  , easing :: Easing              -- ^ Overall easing
  }

derive instance eqKeyframeAnimation :: Eq KeyframeAnimation

instance showKeyframeAnimation :: Show KeyframeAnimation where
  show (KeyframeAnimation a) =
    "KeyframeAnimation(" <> a.name <> " " 
    <> show a.duration <> " "
    <> show (length a.keyframes) <> " keyframes)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a keyframe animation with full control.
keyframeAnimation
  :: String                    -- ^ Animation name
  -> AnimationProperty         -- ^ Target property
  -> Array PropertyKeyframe    -- ^ Keyframes
  -> Duration                  -- ^ Duration
  -> KeyframeAnimation
keyframeAnimation name prop kfs dur = KeyframeAnimation
  { id: AnimationId ("anim-" <> name)
  , name
  , property: prop
  , keyframes: kfs
  , duration: dur
  , delay: fromMilliseconds 0.0
  , iterations: 1.0
  , direction: DirectionNormal
  , fillMode: FillBoth
  , playState: PlayStatePlaying
  , easing: easeOut
  }

-- | Create a simple two-keyframe animation.
simpleAnimation
  :: String              -- ^ Name
  -> AnimationProperty   -- ^ Property
  -> Number              -- ^ Start value
  -> Number              -- ^ End value
  -> Duration            -- ^ Duration
  -> KeyframeAnimation
simpleAnimation name prop startVal endVal dur =
  keyframeAnimation name prop
    [ propertyKeyframe 0.0 startVal easeOut
    , propertyKeyframe 100.0 endVal easeOut
    ]
    dur

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // animation builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set animation duration.
withDuration :: Duration -> KeyframeAnimation -> KeyframeAnimation
withDuration d (KeyframeAnimation a) = KeyframeAnimation a { duration = d }

-- | Set animation delay.
withDelay :: Duration -> KeyframeAnimation -> KeyframeAnimation
withDelay d (KeyframeAnimation a) = KeyframeAnimation a { delay = d }

-- | Set iteration count.
withIterations :: Number -> KeyframeAnimation -> KeyframeAnimation
withIterations n (KeyframeAnimation a) = KeyframeAnimation a { iterations = n }

-- | Set to infinite iterations.
withInfinite :: KeyframeAnimation -> KeyframeAnimation
withInfinite = withIterations (negate 1.0)

-- | Set animation direction.
withDirection :: AnimationDirection -> KeyframeAnimation -> KeyframeAnimation
withDirection d (KeyframeAnimation a) = KeyframeAnimation a { direction = d }

-- | Set fill mode.
withFillMode :: AnimationFillMode -> KeyframeAnimation -> KeyframeAnimation
withFillMode m (KeyframeAnimation a) = KeyframeAnimation a { fillMode = m }

-- | Set overall easing.
withEasing :: Easing -> KeyframeAnimation -> KeyframeAnimation
withEasing e (KeyframeAnimation a) = KeyframeAnimation a { easing = e }

-- | Set target property.
withProperty :: AnimationProperty -> KeyframeAnimation -> KeyframeAnimation
withProperty p (KeyframeAnimation a) = KeyframeAnimation a { property = p }

-- | Add a keyframe.
addKeyframe :: PropertyKeyframe -> KeyframeAnimation -> KeyframeAnimation
addKeyframe kf (KeyframeAnimation a) = 
  KeyframeAnimation a { keyframes = snoc a.keyframes kf }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get animation duration.
duration :: KeyframeAnimation -> Duration
duration (KeyframeAnimation a) = a.duration

-- | Get animation delay.
delay :: KeyframeAnimation -> Duration
delay (KeyframeAnimation a) = a.delay

-- | Get iteration count.
iterations :: KeyframeAnimation -> Number
iterations (KeyframeAnimation a) = a.iterations

-- | Get animation direction.
direction :: KeyframeAnimation -> AnimationDirection
direction (KeyframeAnimation a) = a.direction

-- | Get fill mode.
fillMode :: KeyframeAnimation -> AnimationFillMode
fillMode (KeyframeAnimation a) = a.fillMode

-- | Get keyframes.
keyframes :: KeyframeAnimation -> Array PropertyKeyframe
keyframes (KeyframeAnimation a) = a.keyframes

-- | Get target property.
property :: KeyframeAnimation -> AnimationProperty
property (KeyframeAnimation a) = a.property

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if animation runs infinitely.
isInfinite :: KeyframeAnimation -> Boolean
isInfinite (KeyframeAnimation a) = a.iterations < 0.0

-- | Check if animation is paused.
isPaused :: KeyframeAnimation -> Boolean
isPaused (KeyframeAnimation a) = a.playState == PlayStatePaused

-- | Check if animation has keyframes.
hasKeyframes :: KeyframeAnimation -> Boolean
hasKeyframes (KeyframeAnimation a) = length a.keyframes > 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // presets: attention
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounce attention animation.
bounce :: KeyframeAnimation
bounce = keyframeAnimation "bounce" PropTranslateY
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 20.0 0.0 easeOut
  , propertyKeyframe 40.0 (negate 30.0) easeOut
  , propertyKeyframe 43.0 (negate 30.0) easeOut
  , propertyKeyframe 53.0 0.0 easeOut
  , propertyKeyframe 70.0 (negate 15.0) easeOut
  , propertyKeyframe 80.0 0.0 easeOut
  , propertyKeyframe 90.0 (negate 4.0) easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 1000.0)

-- | Flash attention animation.
flash :: KeyframeAnimation
flash = keyframeAnimation "flash" PropOpacity
  [ propertyKeyframe 0.0 1.0 linear
  , propertyKeyframe 25.0 0.0 linear
  , propertyKeyframe 50.0 1.0 linear
  , propertyKeyframe 75.0 0.0 linear
  , propertyKeyframe 100.0 1.0 linear
  ]
  (fromMilliseconds 1000.0)

-- | Pulse attention animation.
pulse :: KeyframeAnimation
pulse = keyframeAnimation "pulse" PropScale
  [ propertyKeyframe 0.0 1.0 easeInOut
  , propertyKeyframe 50.0 1.05 easeInOut
  , propertyKeyframe 100.0 1.0 easeInOut
  ]
  (fromMilliseconds 1000.0)

-- | Rubber band attention animation.
rubberBand :: KeyframeAnimation
rubberBand = keyframeAnimation "rubberBand" PropScaleX
  [ propertyKeyframe 0.0 1.0 easeOut
  , propertyKeyframe 30.0 1.25 easeOut
  , propertyKeyframe 40.0 0.75 easeOut
  , propertyKeyframe 50.0 1.15 easeOut
  , propertyKeyframe 65.0 0.95 easeOut
  , propertyKeyframe 75.0 1.05 easeOut
  , propertyKeyframe 100.0 1.0 easeOut
  ]
  (fromMilliseconds 1000.0)

-- | Shake attention animation.
shake :: KeyframeAnimation
shake = keyframeAnimation "shake" PropTranslateX
  [ propertyKeyframe 0.0 0.0 linear
  , propertyKeyframe 10.0 (negate 10.0) linear
  , propertyKeyframe 20.0 10.0 linear
  , propertyKeyframe 30.0 (negate 10.0) linear
  , propertyKeyframe 40.0 10.0 linear
  , propertyKeyframe 50.0 (negate 10.0) linear
  , propertyKeyframe 60.0 10.0 linear
  , propertyKeyframe 70.0 (negate 10.0) linear
  , propertyKeyframe 80.0 10.0 linear
  , propertyKeyframe 90.0 (negate 10.0) linear
  , propertyKeyframe 100.0 0.0 linear
  ]
  (fromMilliseconds 1000.0)

-- | Swing attention animation.
swing :: KeyframeAnimation
swing = keyframeAnimation "swing" PropRotate
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 20.0 15.0 easeOut
  , propertyKeyframe 40.0 (negate 10.0) easeOut
  , propertyKeyframe 60.0 5.0 easeOut
  , propertyKeyframe 80.0 (negate 5.0) easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 1000.0)

-- | Tada attention animation.
tada :: KeyframeAnimation
tada = keyframeAnimation "tada" PropScale
  [ propertyKeyframe 0.0 1.0 easeOut
  , propertyKeyframe 10.0 0.9 easeOut
  , propertyKeyframe 20.0 0.9 easeOut
  , propertyKeyframe 30.0 1.1 easeOut
  , propertyKeyframe 40.0 1.1 easeOut
  , propertyKeyframe 50.0 1.1 easeOut
  , propertyKeyframe 60.0 1.1 easeOut
  , propertyKeyframe 70.0 1.1 easeOut
  , propertyKeyframe 80.0 1.1 easeOut
  , propertyKeyframe 90.0 1.1 easeOut
  , propertyKeyframe 100.0 1.0 easeOut
  ]
  (fromMilliseconds 1000.0)

-- | Wobble attention animation.
wobble :: KeyframeAnimation
wobble = keyframeAnimation "wobble" PropTranslateX
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 15.0 (negate 25.0) easeOut
  , propertyKeyframe 30.0 20.0 easeOut
  , propertyKeyframe 45.0 (negate 15.0) easeOut
  , propertyKeyframe 60.0 10.0 easeOut
  , propertyKeyframe 75.0 (negate 5.0) easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 1000.0)

-- | Jello attention animation.
jello :: KeyframeAnimation
jello = keyframeAnimation "jello" PropSkewX
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 11.1 0.0 easeOut
  , propertyKeyframe 22.2 (negate 12.5) easeOut
  , propertyKeyframe 33.3 6.25 easeOut
  , propertyKeyframe 44.4 (negate 3.125) easeOut
  , propertyKeyframe 55.5 1.5625 easeOut
  , propertyKeyframe 66.6 (negate 0.78125) easeOut
  , propertyKeyframe 77.7 0.390625 easeOut
  , propertyKeyframe 88.8 (negate 0.1953125) easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 1000.0)

-- | Heart beat attention animation.
heartBeat :: KeyframeAnimation
heartBeat = keyframeAnimation "heartBeat" PropScale
  [ propertyKeyframe 0.0 1.0 easeInOut
  , propertyKeyframe 14.0 1.3 easeInOut
  , propertyKeyframe 28.0 1.0 easeInOut
  , propertyKeyframe 42.0 1.3 easeInOut
  , propertyKeyframe 70.0 1.0 easeInOut
  , propertyKeyframe 100.0 1.0 easeInOut
  ]
  (fromMilliseconds 1300.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // presets: enter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fade in animation.
fadeIn :: KeyframeAnimation
fadeIn = simpleAnimation "fadeIn" PropOpacity 0.0 1.0 (fromMilliseconds 300.0)

-- | Fade in from above.
fadeInUp :: KeyframeAnimation
fadeInUp = keyframeAnimation "fadeInUp" PropTranslateY
  [ propertyKeyframe 0.0 20.0 easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 300.0)

-- | Fade in from below.
fadeInDown :: KeyframeAnimation
fadeInDown = keyframeAnimation "fadeInDown" PropTranslateY
  [ propertyKeyframe 0.0 (negate 20.0) easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 300.0)

-- | Fade in from left.
fadeInLeft :: KeyframeAnimation
fadeInLeft = keyframeAnimation "fadeInLeft" PropTranslateX
  [ propertyKeyframe 0.0 (negate 20.0) easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 300.0)

-- | Fade in from right.
fadeInRight :: KeyframeAnimation
fadeInRight = keyframeAnimation "fadeInRight" PropTranslateX
  [ propertyKeyframe 0.0 20.0 easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 300.0)

-- | Slide in from below.
slideInUp :: KeyframeAnimation
slideInUp = keyframeAnimation "slideInUp" PropTranslateY
  [ propertyKeyframe 0.0 100.0 easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 400.0)

-- | Slide in from above.
slideInDown :: KeyframeAnimation
slideInDown = keyframeAnimation "slideInDown" PropTranslateY
  [ propertyKeyframe 0.0 (negate 100.0) easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 400.0)

-- | Slide in from left.
slideInLeft :: KeyframeAnimation
slideInLeft = keyframeAnimation "slideInLeft" PropTranslateX
  [ propertyKeyframe 0.0 (negate 100.0) easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 400.0)

-- | Slide in from right.
slideInRight :: KeyframeAnimation
slideInRight = keyframeAnimation "slideInRight" PropTranslateX
  [ propertyKeyframe 0.0 100.0 easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 400.0)

-- | Zoom in animation.
zoomIn :: KeyframeAnimation
zoomIn = keyframeAnimation "zoomIn" PropScale
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 100.0 1.0 easeOut
  ]
  (fromMilliseconds 300.0)

-- | Bounce in animation.
bounceIn :: KeyframeAnimation
bounceIn = keyframeAnimation "bounceIn" PropScale
  [ propertyKeyframe 0.0 0.3 easeOut
  , propertyKeyframe 20.0 1.1 easeOut
  , propertyKeyframe 40.0 0.9 easeOut
  , propertyKeyframe 60.0 1.03 easeOut
  , propertyKeyframe 80.0 0.97 easeOut
  , propertyKeyframe 100.0 1.0 easeOut
  ]
  (fromMilliseconds 750.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // presets: exit
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fade out animation.
fadeOut :: KeyframeAnimation
fadeOut = simpleAnimation "fadeOut" PropOpacity 1.0 0.0 (fromMilliseconds 300.0)

-- | Fade out upward.
fadeOutUp :: KeyframeAnimation
fadeOutUp = keyframeAnimation "fadeOutUp" PropTranslateY
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 100.0 (negate 20.0) easeOut
  ]
  (fromMilliseconds 300.0)

-- | Fade out downward.
fadeOutDown :: KeyframeAnimation
fadeOutDown = keyframeAnimation "fadeOutDown" PropTranslateY
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 100.0 20.0 easeOut
  ]
  (fromMilliseconds 300.0)

-- | Fade out to left.
fadeOutLeft :: KeyframeAnimation
fadeOutLeft = keyframeAnimation "fadeOutLeft" PropTranslateX
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 100.0 (negate 20.0) easeOut
  ]
  (fromMilliseconds 300.0)

-- | Fade out to right.
fadeOutRight :: KeyframeAnimation
fadeOutRight = keyframeAnimation "fadeOutRight" PropTranslateX
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 100.0 20.0 easeOut
  ]
  (fromMilliseconds 300.0)

-- | Slide out upward.
slideOutUp :: KeyframeAnimation
slideOutUp = keyframeAnimation "slideOutUp" PropTranslateY
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 100.0 (negate 100.0) easeOut
  ]
  (fromMilliseconds 400.0)

-- | Slide out downward.
slideOutDown :: KeyframeAnimation
slideOutDown = keyframeAnimation "slideOutDown" PropTranslateY
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 100.0 100.0 easeOut
  ]
  (fromMilliseconds 400.0)

-- | Slide out to left.
slideOutLeft :: KeyframeAnimation
slideOutLeft = keyframeAnimation "slideOutLeft" PropTranslateX
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 100.0 (negate 100.0) easeOut
  ]
  (fromMilliseconds 400.0)

-- | Slide out to right.
slideOutRight :: KeyframeAnimation
slideOutRight = keyframeAnimation "slideOutRight" PropTranslateX
  [ propertyKeyframe 0.0 0.0 easeOut
  , propertyKeyframe 100.0 100.0 easeOut
  ]
  (fromMilliseconds 400.0)

-- | Zoom out animation.
zoomOut :: KeyframeAnimation
zoomOut = keyframeAnimation "zoomOut" PropScale
  [ propertyKeyframe 0.0 1.0 easeOut
  , propertyKeyframe 100.0 0.0 easeOut
  ]
  (fromMilliseconds 300.0)

-- | Bounce out animation.
bounceOut :: KeyframeAnimation
bounceOut = keyframeAnimation "bounceOut" PropScale
  [ propertyKeyframe 0.0 1.0 easeOut
  , propertyKeyframe 20.0 0.9 easeOut
  , propertyKeyframe 50.0 1.1 easeOut
  , propertyKeyframe 55.0 1.1 easeOut
  , propertyKeyframe 100.0 0.3 easeOut
  ]
  (fromMilliseconds 750.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // presets: loading
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spin loading animation.
spin :: KeyframeAnimation
spin = withInfinite $ keyframeAnimation "spin" PropRotate
  [ propertyKeyframe 0.0 0.0 linear
  , propertyKeyframe 100.0 360.0 linear
  ]
  (fromMilliseconds 1000.0)

-- | Reverse spin loading animation.
spinReverse :: KeyframeAnimation
spinReverse = withInfinite $ keyframeAnimation "spinReverse" PropRotate
  [ propertyKeyframe 0.0 360.0 linear
  , propertyKeyframe 100.0 0.0 linear
  ]
  (fromMilliseconds 1000.0)

-- | Ping pong loading animation.
pingPong :: KeyframeAnimation
pingPong = withInfinite $ withDirection DirectionAlternate $
  keyframeAnimation "pingPong" PropTranslateX
    [ propertyKeyframe 0.0 (negate 20.0) easeInOut
    , propertyKeyframe 100.0 20.0 easeInOut
    ]
    (fromMilliseconds 800.0)

-- | Breathe loading animation (subtle scale pulse).
breathe :: KeyframeAnimation
breathe = withInfinite $ keyframeAnimation "breathe" PropScale
  [ propertyKeyframe 0.0 1.0 easeInOut
  , propertyKeyframe 50.0 1.08 easeInOut
  , propertyKeyframe 100.0 1.0 easeInOut
  ]
  (fromMilliseconds 2000.0)
