-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // element // input // slider
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Slider — Pure Element for bounded value selection.
-- |
-- | A Slider is NOT a component with event handlers and DOM manipulation.
-- | A Slider IS a pure view function: bounded value → Element.
-- |
-- | The type system carries the bounds. A Hue slider (0-359, wrapping) uses
-- | the exact same code as an Opacity slider (0.0-1.0, clamping) — the TYPE
-- | determines the behavior.
-- |
-- | ## Design Philosophy
-- |
-- | The runtime interprets gestures and maps them to value changes.
-- | The component declares WHAT it is, not HOW it responds to events.
-- |
-- | ```
-- | slider :: forall a msg. BoundedValue a => a -> (a -> msg) -> Element msg
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Input.Slider as Slider
-- | import Hydrogen.Schema.Color.Hue (Hue)
-- | import Hydrogen.Schema.Spatial.Opacity (Opacity)
-- |
-- | -- Same function, different types, different bounds
-- | hueSlider :: Hue -> Element Msg
-- | hueSlider h = Slider.slider h SetHue
-- |
-- | opacitySlider :: Opacity -> Element Msg  
-- | opacitySlider o = Slider.slider o SetOpacity
-- | ```
-- |
-- | ## Runtime Interpretation
-- |
-- | The runtime sees:
-- | - Track geometry (position, size)
-- | - Thumb position (normalized 0.0-1.0)
-- | - Gesture semantics (drag, keyboard arrows)
-- |
-- | The runtime computes:
-- | - Gesture → Percent → denormalize to type's bounds → msg
-- |
-- | The component NEVER handles events. NEVER touches coordinates.

module Hydrogen.Element.Input.Slider
  ( -- * Core Slider
    slider
  , sliderWith
  
  -- * Slider Configuration
  , SliderConfig
  , defaultConfig
  , horizontal
  , vertical
  , withStep
  , withTrackClass
  , withThumbClass
  
  -- * BoundedValue Typeclass
  , class BoundedValue
  , minValue
  , maxValue
  , normalize
  , denormalize
  , stepValue
  
  -- * Types
  , Orientation(Horizontal, Vertical)
  , Percent
  , mkPercent
  , unwrapPercent
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (/)
  , (*)
  , (<>)
  , (>=)
  , (<=)
  )

import Data.Int (toNumber, round) as Int
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Sat
import Hydrogen.Schema.Color.Lightness as Light

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // percent
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normalized percentage (0.0 to 1.0)
-- |
-- | This is the universal currency for slider position.
-- | Every bounded value normalizes to Percent for rendering.
newtype Percent = Percent Number

derive instance eqPercent :: Eq Percent
derive instance ordPercent :: Ord Percent

instance showPercent :: Show Percent where
  show (Percent p) = show (p * 100.0) <> "%"

-- | Smart constructor clamping to 0.0-1.0
mkPercent :: Number -> Percent
mkPercent n = Percent (clamp 0.0 1.0 n)
  where
  clamp lo hi x
    | x <= lo = lo
    | x >= hi = hi
    | otherwise = x

-- | Extract raw number
unwrapPercent :: Percent -> Number
unwrapPercent (Percent p) = p

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // bounded value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Typeclass for values that can be shown on a slider.
-- |
-- | The slider doesn't know about specific bounds — the TYPE knows.
-- | This typeclass extracts that knowledge for rendering.
-- |
-- | ## Laws
-- |
-- | - `denormalize (normalize a) = a` (round-trip, within step precision)
-- | - `normalize minValue = Percent 0.0`
-- | - `normalize maxValue = Percent 1.0`
class BoundedValue a where
  -- | Minimum value for this type
  minValue :: a
  
  -- | Maximum value for this type
  maxValue :: a
  
  -- | Convert to normalized percentage (0.0-1.0)
  normalize :: a -> Percent
  
  -- | Convert from percentage back to bounded value
  denormalize :: Percent -> a
  
  -- | Step increment (for keyboard navigation, optional granularity)
  -- | Default: 1 for Int types, 0.01 for Number types
  stepValue :: a -> Number

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // orientation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Slider orientation
data Orientation
  = Horizontal
  | Vertical

derive instance eqOrientation :: Eq Orientation

instance showOrientation :: Show Orientation where
  show Horizontal = "Horizontal"
  show Vertical = "Vertical"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Slider visual configuration
-- |
-- | This is APPEARANCE only. Bounds come from the type.
type SliderConfig =
  { orientation :: Orientation
  , trackClass :: String
  , thumbClass :: String
  , containerClass :: String
  , step :: Maybe Number  -- Override type's default step
  }

-- | Default slider configuration
defaultConfig :: SliderConfig
defaultConfig =
  { orientation: Horizontal
  , trackClass: "slider-track"
  , thumbClass: "slider-thumb"
  , containerClass: "slider"
  , step: Nothing
  }

-- | Horizontal orientation
horizontal :: SliderConfig -> SliderConfig
horizontal cfg = cfg { orientation = Horizontal }

-- | Vertical orientation
vertical :: SliderConfig -> SliderConfig
vertical cfg = cfg { orientation = Vertical }

-- | Set step increment
withStep :: Number -> SliderConfig -> SliderConfig
withStep s cfg = cfg { step = Just s }

-- | Set track CSS class
withTrackClass :: String -> SliderConfig -> SliderConfig
withTrackClass c cfg = cfg { trackClass = c }

-- | Set thumb CSS class
withThumbClass :: String -> SliderConfig -> SliderConfig
withThumbClass c cfg = cfg { thumbClass = c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // slider
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a slider for any bounded value.
-- |
-- | The slider is pure data. It declares:
-- | - Current thumb position (derived from value)
-- | - Orientation
-- | - What message to emit when value changes
-- |
-- | The RUNTIME handles:
-- | - Gesture detection (drag, click, keyboard)
-- | - Coordinate → Percent mapping
-- | - Percent → value via `denormalize`
-- | - Message dispatch
-- |
-- | ```purescript
-- | slider myHue SetHue      -- Hue slider: 0-359, wrapping
-- | slider myOpacity SetOpacity  -- Opacity: 0.0-1.0, clamping
-- | slider myGain SetGain    -- Gain: -96dB to +12dB
-- | ```
slider :: forall a msg. BoundedValue a => a -> (a -> msg) -> E.Element msg
slider value toMsg = sliderWith defaultConfig value toMsg

-- | Create a slider with custom configuration.
sliderWith 
  :: forall a msg
   . BoundedValue a 
  => SliderConfig 
  -> a 
  -> (a -> msg) 
  -> E.Element msg
sliderWith cfg value _toMsg =
  let
    -- Normalize value to percentage for positioning
    (Percent pct) = normalize value
    
    -- Thumb position as percentage string
    thumbPosition = show (pct * 100.0) <> "%"
    
    -- Orientation-specific styles
    trackStyle = case cfg.orientation of
      Horizontal -> "width: 100%; height: 8px"
      Vertical -> "width: 8px; height: 100%"
    
    thumbStyle = case cfg.orientation of
      Horizontal -> "left: " <> thumbPosition <> "; top: 50%; transform: translate(-50%, -50%)"
      Vertical -> "bottom: " <> thumbPosition <> "; left: 50%; transform: translate(-50%, 50%)"
    
    -- Accessibility attributes
    ariaAttrs = 
      [ E.role "slider"
      , E.ariaLabel "slider"
      , E.attr "aria-valuemin" "0"
      , E.attr "aria-valuemax" "100"
      , E.attr "aria-valuenow" (show (pct * 100.0))
      , E.tabIndex 0
      ]
    
    -- Data attributes for runtime interpretation
    dataAttrs =
      [ E.dataAttr "slider" "true"
      , E.dataAttr "orientation" (show cfg.orientation)
      , E.dataAttr "value" (show pct)
      ]
  in
    E.div_ 
      ([ E.class_ cfg.containerClass
       , E.style "position" "relative"
       ] <> ariaAttrs <> dataAttrs)
      [ -- Track
        E.div_
          [ E.class_ cfg.trackClass
          , E.style "position" "relative"
          , E.attr "style" trackStyle
          , E.dataAttr "track" "true"
          ]
          [ -- Thumb
            E.div_
              [ E.class_ cfg.thumbClass
              , E.style "position" "absolute"
              , E.attr "style" thumbStyle
              , E.dataAttr "thumb" "true"
              ]
              []
          ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // bounded value instances
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hue: 0-359 degrees on the color wheel.
-- |
-- | Note: Hue WRAPS (360° = 0°), but the slider shows linear 0-359.
-- | Wrapping behavior is in the Hue type's smart constructor.
instance boundedValueHue :: BoundedValue Hue.Hue where
  minValue = Hue.hue 0
  maxValue = Hue.hue 359
  
  normalize h = 
    let degrees = Int.toNumber (Hue.unwrap h)
    in mkPercent (degrees / 359.0)
  
  denormalize pct = 
    let degrees = Int.round (unwrapPercent pct * 359.0)
    in Hue.hue degrees
  
  stepValue _ = 1.0

-- | Saturation: 0-100% color intensity.
instance boundedValueSaturation :: BoundedValue Sat.Saturation where
  minValue = Sat.saturation 0
  maxValue = Sat.saturation 100
  
  normalize s = 
    let pctVal = Int.toNumber (Sat.unwrap s)
    in mkPercent (pctVal / 100.0)
  
  denormalize pct = 
    let value = Int.round (unwrapPercent pct * 100.0)
    in Sat.saturation value
  
  stepValue _ = 1.0

-- | Lightness: 0-100% light level.
instance boundedValueLightness :: BoundedValue Light.Lightness where
  minValue = Light.lightness 0
  maxValue = Light.lightness 100
  
  normalize l = 
    let pctVal = Int.toNumber (Light.unwrap l)
    in mkPercent (pctVal / 100.0)
  
  denormalize pct = 
    let value = Int.round (unwrapPercent pct * 100.0)
    in Light.lightness value
  
  stepValue _ = 1.0
