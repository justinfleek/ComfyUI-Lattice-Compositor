-- | Lattice.Services.Video.Transitions - Video transition effects
-- |
-- | Professional video transition effects with multiple blend modes.
-- | Inspired by filliptm's ComfyUI_Fill-Nodes/FL_VideoCrossfade
-- |
-- | Source: ui/src/services/video/transitions.ts

module Lattice.Services.Video.Transitions
  ( -- * Types
    TransitionBlendMode(..)
  , TransitionEasing(..)
  , TransitionConfig
  , TransitionState
  , TransitionPresets
  , CanvasElement
    -- * Easing Functions (Pure)
  , applyEasing
  , easeIn
  , easeOut
  , easeInOut
  , bounce
    -- * Blend Functions (Pure)
  , blendMultiply
  , blendScreen
  , blendOverlay
  , blendSoftLight
  , blendAdd
  , blendSubtract
    -- * Transition Rendering (FFI)
  , renderTransition
    -- * Progress Calculation
  , getTransitionProgress
  , isInTransition
    -- * Presets
  , defaultTransition
  , getPreset
  , getAllModes
  , getModeName
  , defaultPresets
    -- * Parsing
  , stringToBlendMode
  ) where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe(..))
import Data.Int (toNumber)
import Data.Tuple (Tuple(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Foreign.Object (Object)
import Foreign.Object as Obj

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Transition blend modes
data TransitionBlendMode
  = BlendNormal      -- Linear crossfade
  | BlendMultiply    -- Darker, dramatic
  | BlendScreen      -- Lighter, ethereal
  | BlendOverlay     -- High contrast
  | BlendSoftLight   -- Subtle contrast
  | BlendAdd         -- Bright flash
  | BlendSubtract    -- Dark flash
  | BlendDissolve    -- Randomized fade
  | WipeLeft         -- Directional wipe
  | WipeRight
  | WipeUp
  | WipeDown
  | RadialWipe       -- Circular reveal
  | IrisIn           -- Circle expanding
  | IrisOut          -- Circle contracting
  | CrossZoom        -- Zoom blur transition

derive instance Eq TransitionBlendMode
derive instance Ord TransitionBlendMode
derive instance Generic TransitionBlendMode _
instance Show TransitionBlendMode where show = genericShow

-- | Transition easing functions
data TransitionEasing
  = EasingLinear
  | EasingEaseIn
  | EasingEaseOut
  | EasingEaseInOut
  | EasingBounce

derive instance Eq TransitionEasing
derive instance Ord TransitionEasing
derive instance Generic TransitionEasing _
instance Show TransitionEasing where show = genericShow

-- | Transition configuration
type TransitionConfig =
  { blendMode :: TransitionBlendMode
  , duration :: Int           -- Duration in frames
  , easing :: TransitionEasing
  , direction :: Maybe Number -- 0-360 for wipes (degrees)
  , softness :: Number        -- 0-1 edge softness
  , centerX :: Number         -- 0-1 for radial effects
  , centerY :: Number         -- 0-1 for radial effects
  }

-- | Transition state for rendering
type TransitionState =
  { progress :: Number        -- 0-1 transition progress
  , fromCanvasId :: String    -- Source canvas element ID
  , toCanvasId :: String      -- Target canvas element ID
  , config :: TransitionConfig
  }

-- | Collection of transition presets
type TransitionPresets = Object TransitionConfig

--------------------------------------------------------------------------------
-- FFI Types
--------------------------------------------------------------------------------

-- | Canvas element handle
foreign import data CanvasElement :: Type

--------------------------------------------------------------------------------
-- FFI Imports
--------------------------------------------------------------------------------

-- | Render transition between two canvases
foreign import renderTransitionImpl
  :: String   -- fromCanvasId
  -> String   -- toCanvasId
  -> Number   -- progress (0-1)
  -> String   -- blendMode string
  -> Number   -- softness
  -> Number   -- centerX
  -> Number   -- centerY
  -> Int      -- seed for dissolve
  -> Effect CanvasElement

--------------------------------------------------------------------------------
-- Easing Functions (Pure)
--------------------------------------------------------------------------------

-- | Apply easing function to progress value
applyEasing :: TransitionEasing -> Number -> Number
applyEasing easing t = case easing of
  EasingLinear -> t
  EasingEaseIn -> easeIn t
  EasingEaseOut -> easeOut t
  EasingEaseInOut -> easeInOut t
  EasingBounce -> bounce t

-- | Quadratic ease-in
easeIn :: Number -> Number
easeIn t = t * t

-- | Quadratic ease-out
easeOut :: Number -> Number
easeOut t = 1.0 - (1.0 - t) * (1.0 - t)

-- | Quadratic ease-in-out
easeInOut :: Number -> Number
easeInOut t =
  if t < 0.5
    then 2.0 * t * t
    else 1.0 - ((-2.0 * t + 2.0) `pow` 2.0) / 2.0

-- | Bounce easing
bounce :: Number -> Number
bounce t =
  let n1 = 7.5625
      d1 = 2.75
  in if t < 1.0 / d1
       then n1 * t * t
       else if t < 2.0 / d1
         then let t' = t - 1.5 / d1 in n1 * t' * t' + 0.75
         else if t < 2.5 / d1
           then let t' = t - 2.25 / d1 in n1 * t' * t' + 0.9375
           else let t' = t - 2.625 / d1 in n1 * t' * t' + 0.984375

--------------------------------------------------------------------------------
-- Blend Functions (Pure - operate on 0-255 channel values)
--------------------------------------------------------------------------------

-- | Multiply blend: darker, dramatic
blendMultiply :: Number -> Number -> Number
blendMultiply a b = (a * b) / 255.0

-- | Screen blend: lighter, ethereal
blendScreen :: Number -> Number -> Number
blendScreen a b = 255.0 - ((255.0 - a) * (255.0 - b)) / 255.0

-- | Overlay blend: high contrast
blendOverlay :: Number -> Number -> Number
blendOverlay a b =
  if a < 128.0
    then (2.0 * a * b) / 255.0
    else 255.0 - (2.0 * (255.0 - a) * (255.0 - b)) / 255.0

-- | Soft light blend: subtle contrast
blendSoftLight :: Number -> Number -> Number
blendSoftLight a b =
  let t = (b / 255.0) * a + ((255.0 - b) / 255.0) * blendScreen a a
  in t

-- | Additive blend: bright flash
blendAdd :: Number -> Number -> Number
blendAdd a b = min 255.0 (a + b)

-- | Subtractive blend: dark flash
blendSubtract :: Number -> Number -> Number
blendSubtract a b = max 0.0 (a - b)

--------------------------------------------------------------------------------
-- Transition Rendering
--------------------------------------------------------------------------------

-- | Render transition between two canvases
renderTransition :: TransitionState -> Effect CanvasElement
renderTransition state =
  let easedProgress = applyEasing state.config.easing state.progress
      blendModeStr = blendModeToString state.config.blendMode
  in renderTransitionImpl
       state.fromCanvasId
       state.toCanvasId
       easedProgress
       blendModeStr
       state.config.softness
       state.config.centerX
       state.config.centerY
       12345  -- seed for dissolve

--------------------------------------------------------------------------------
-- Progress Calculation
--------------------------------------------------------------------------------

-- | Calculate transition progress for a frame within a transition
-- | Returns Nothing if frame is outside transition range
getTransitionProgress :: Int -> Int -> Int -> Maybe Number
getTransitionProgress currentFrame transitionStartFrame transitionDuration =
  if currentFrame < transitionStartFrame then Nothing
  else if currentFrame >= transitionStartFrame + transitionDuration then Nothing
  else Just $ toNumber (currentFrame - transitionStartFrame) / toNumber transitionDuration

-- | Check if a frame is within a transition
isInTransition :: Int -> Int -> Int -> Boolean
isInTransition currentFrame transitionStartFrame transitionDuration =
  currentFrame >= transitionStartFrame &&
  currentFrame < transitionStartFrame + transitionDuration

--------------------------------------------------------------------------------
-- Presets
--------------------------------------------------------------------------------

-- | Default transition configuration
defaultTransition :: TransitionConfig
defaultTransition =
  { blendMode: BlendNormal
  , duration: 16  -- 1 second at 16fps
  , easing: EasingEaseInOut
  , direction: Nothing
  , softness: 0.1
  , centerX: 0.5
  , centerY: 0.5
  }

-- | Get preset by name
getPreset :: String -> Maybe TransitionConfig
getPreset name = Obj.lookup name defaultPresets

-- | Get all available blend modes
getAllModes :: Array TransitionBlendMode
getAllModes =
  [ BlendNormal, BlendMultiply, BlendScreen, BlendOverlay
  , BlendSoftLight, BlendAdd, BlendSubtract, BlendDissolve
  , WipeLeft, WipeRight, WipeUp, WipeDown
  , RadialWipe, IrisIn, IrisOut, CrossZoom
  ]

-- | Get human-readable name for a blend mode
getModeName :: TransitionBlendMode -> String
getModeName = case _ of
  BlendNormal -> "Crossfade"
  BlendMultiply -> "Multiply Fade"
  BlendScreen -> "Screen Fade"
  BlendOverlay -> "Overlay Fade"
  BlendSoftLight -> "Soft Light"
  BlendAdd -> "Additive Flash"
  BlendSubtract -> "Subtractive"
  BlendDissolve -> "Dissolve"
  WipeLeft -> "Wipe Left"
  WipeRight -> "Wipe Right"
  WipeUp -> "Wipe Up"
  WipeDown -> "Wipe Down"
  RadialWipe -> "Clock Wipe"
  IrisIn -> "Iris In"
  IrisOut -> "Iris Out"
  CrossZoom -> "Cross Zoom"

-- | Convert blend mode to API string
blendModeToString :: TransitionBlendMode -> String
blendModeToString = case _ of
  BlendNormal -> "normal"
  BlendMultiply -> "multiply"
  BlendScreen -> "screen"
  BlendOverlay -> "overlay"
  BlendSoftLight -> "soft-light"
  BlendAdd -> "add"
  BlendSubtract -> "subtract"
  BlendDissolve -> "dissolve"
  WipeLeft -> "wipe-left"
  WipeRight -> "wipe-right"
  WipeUp -> "wipe-up"
  WipeDown -> "wipe-down"
  RadialWipe -> "radial-wipe"
  IrisIn -> "iris-in"
  IrisOut -> "iris-out"
  CrossZoom -> "cross-zoom"

-- | Parse string to blend mode
stringToBlendMode :: String -> Maybe TransitionBlendMode
stringToBlendMode = case _ of
  "normal" -> Just BlendNormal
  "multiply" -> Just BlendMultiply
  "screen" -> Just BlendScreen
  "overlay" -> Just BlendOverlay
  "soft-light" -> Just BlendSoftLight
  "add" -> Just BlendAdd
  "subtract" -> Just BlendSubtract
  "dissolve" -> Just BlendDissolve
  "wipe-left" -> Just WipeLeft
  "wipe-right" -> Just WipeRight
  "wipe-up" -> Just WipeUp
  "wipe-down" -> Just WipeDown
  "radial-wipe" -> Just RadialWipe
  "iris-in" -> Just IrisIn
  "iris-out" -> Just IrisOut
  "cross-zoom" -> Just CrossZoom
  _ -> Nothing

-- | Default transition presets
defaultPresets :: TransitionPresets
defaultPresets = Obj.fromFoldable
  [ Tuple "fade" fadePreset
  , Tuple "flash-fade" flashFadePreset
  , Tuple "dark-fade" darkFadePreset
  , Tuple "dreamy" dreamyPreset
  , Tuple "dramatic" dramaticPreset
  , Tuple "soft-cut" softCutPreset
  , Tuple "dissolve" dissolvePreset
  , Tuple "wipe-left" wipeLeftPreset
  , Tuple "wipe-right" wipeRightPreset
  , Tuple "iris-reveal" irisRevealPreset
  , Tuple "iris-close" irisClosePreset
  , Tuple "clock-wipe" clockWipePreset
  ]

fadePreset :: TransitionConfig
fadePreset = defaultTransition

flashFadePreset :: TransitionConfig
flashFadePreset = defaultTransition
  { blendMode = BlendAdd
  , duration = 8
  , easing = EasingEaseOut
  }

darkFadePreset :: TransitionConfig
darkFadePreset = defaultTransition
  { blendMode = BlendMultiply }

dreamyPreset :: TransitionConfig
dreamyPreset = defaultTransition
  { blendMode = BlendScreen
  , duration = 24
  , easing = EasingEaseOut
  , softness = 0.2
  }

dramaticPreset :: TransitionConfig
dramaticPreset = defaultTransition
  { blendMode = BlendOverlay }

softCutPreset :: TransitionConfig
softCutPreset = defaultTransition
  { blendMode = BlendSoftLight
  , duration = 8
  , easing = EasingLinear
  }

dissolvePreset :: TransitionConfig
dissolvePreset = defaultTransition
  { blendMode = BlendDissolve
  , easing = EasingLinear
  }

wipeLeftPreset :: TransitionConfig
wipeLeftPreset = defaultTransition
  { blendMode = WipeLeft }

wipeRightPreset :: TransitionConfig
wipeRightPreset = defaultTransition
  { blendMode = WipeRight }

irisRevealPreset :: TransitionConfig
irisRevealPreset = defaultTransition
  { blendMode = IrisIn
  , duration = 24
  , easing = EasingEaseOut
  , softness = 0.15
  }

irisClosePreset :: TransitionConfig
irisClosePreset = defaultTransition
  { blendMode = IrisOut
  , duration = 24
  , easing = EasingEaseIn
  , softness = 0.15
  }

clockWipePreset :: TransitionConfig
clockWipePreset = defaultTransition
  { blendMode = RadialWipe
  , duration = 24
  , easing = EasingLinear
  , softness = 0.05
  }

--------------------------------------------------------------------------------
-- Internal Helpers
--------------------------------------------------------------------------------

pow :: Number -> Number -> Number
pow base exponent = js_pow base exponent

foreign import js_pow :: Number -> Number -> Number

min :: Number -> Number -> Number
min a b = if a < b then a else b

max :: Number -> Number -> Number
max a b = if a > b then a else b
