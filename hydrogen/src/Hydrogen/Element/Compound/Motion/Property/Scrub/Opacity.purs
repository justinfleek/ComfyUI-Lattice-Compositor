-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // motion // property // scrub // opacity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Opacity Scrubable Input — Alpha transparency control (0-100%)
-- |
-- | A motion graphics numeric input specialized for opacity values.
-- | 0% = fully transparent, 100% = fully opaque.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Motion.Property.Scrub.Opacity as OpacityScrub
-- | import Hydrogen.Schema.Color.Opacity (Opacity)
-- |
-- | myOpacityInput :: Opacity -> Element Msg
-- | myOpacityInput o = OpacityScrub.opacityScrub o
-- |   [ OpacityScrub.label "Opacity"
-- |   , OpacityScrub.onChange SetOpacity
-- |   ]
-- | ```
-- |
-- | ## Bounds
-- |
-- | | Property  | Value | Notes |
-- | |-----------|-------|-------|
-- | | Min       | 0%    | Fully transparent |
-- | | Max       | 100%  | Fully opaque |
-- | | Step      | 1%    | Integer percentage |
-- | | Precision | 0     | No decimal places |
-- | | Unit      | "%"   | Percent symbol |
-- | | Clamping  | Yes   | Values clamped to 0-100 |

module Hydrogen.Element.Compound.Motion.Property.Scrub.Opacity
  ( -- * Component
    opacityScrub
    
  -- * Props
  , OpacityScrubProp
  , label
  , sensitivity
  , defaultValue
  , scrubDisabled
  , showReset
  , onChange
  , onScrubStart
  , onScrubEnd
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Element.Compound.Motion.Property.ScrubableInput as Scrub

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Opacity-specific prop modifier
type OpacityScrubProp msg = Scrub.ScrubableInputProp Opacity.Opacity msg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set label text
label :: forall msg. String -> OpacityScrubProp msg
label = Scrub.label

-- | Set scrub sensitivity
sensitivity :: forall msg. Number -> OpacityScrubProp msg
sensitivity = Scrub.sensitivity

-- | Set default value for reset
defaultValue :: forall msg. Opacity.Opacity -> OpacityScrubProp msg
defaultValue = Scrub.defaultValue

-- | Disable the input
scrubDisabled :: forall msg. Boolean -> OpacityScrubProp msg
scrubDisabled = Scrub.scrubDisabled

-- | Show reset button
showReset :: forall msg. Boolean -> OpacityScrubProp msg
showReset = Scrub.showReset

-- | Set change handler
onChange :: forall msg. (Opacity.Opacity -> msg) -> OpacityScrubProp msg
onChange = Scrub.onChange

-- | Called when scrub begins
onScrubStart :: forall msg. msg -> OpacityScrubProp msg
onScrubStart = Scrub.onScrubStart

-- | Called when scrub ends
onScrubEnd :: forall msg. msg -> OpacityScrubProp msg
onScrubEnd = Scrub.onScrubEnd

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Opacity scrubable input
-- |
-- | A motion graphics numeric input specialized for opacity values.
-- | Uses the Opacity Schema atom for type-safe transparency.
-- |
-- | ```purescript
-- | opacityScrub (Opacity.opacity 75)
-- |   [ label "Layer Opacity"
-- |   , onChange SetLayerOpacity
-- |   ]
-- | ```
opacityScrub :: forall msg. Opacity.Opacity -> Array (OpacityScrubProp msg) -> E.Element msg
opacityScrub = Scrub.scrubableInput

