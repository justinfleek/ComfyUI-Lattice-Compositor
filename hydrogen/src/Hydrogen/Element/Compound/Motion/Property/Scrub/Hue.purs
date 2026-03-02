-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // motion // property // scrub // hue
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hue Scrubable Input — Color wheel position control (0-359°)
-- |
-- | A motion graphics numeric input specialized for hue values.
-- | Wraps around at 360° (359° + 1° = 0°).
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Motion.Property.Scrub.Hue as HueScrub
-- | import Hydrogen.Schema.Color.Hue (Hue)
-- |
-- | myHueInput :: Hue -> Element Msg
-- | myHueInput h = HueScrub.hueScrub h
-- |   [ HueScrub.label "Hue"
-- |   , HueScrub.onChange SetHue
-- |   ]
-- | ```
-- |
-- | ## Bounds
-- |
-- | | Property  | Value | Notes |
-- | |-----------|-------|-------|
-- | | Min       | 0°    | Red   |
-- | | Max       | 359°  | Almost red (wraps to 0) |
-- | | Step      | 1°    | Integer degrees |
-- | | Precision | 0     | No decimal places |
-- | | Unit      | "°"   | Degree symbol |
-- | | Wrapping  | Yes   | 360° becomes 0° |

module Hydrogen.Element.Compound.Motion.Property.Scrub.Hue
  ( -- * Component
    hueScrub
    
  -- * Props
  , HueScrubProp
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
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Element.Compound.Motion.Property.ScrubableInput as Scrub

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hue-specific prop modifier
type HueScrubProp msg = Scrub.ScrubableInputProp Hue.Hue msg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set label text
label :: forall msg. String -> HueScrubProp msg
label = Scrub.label

-- | Set scrub sensitivity
sensitivity :: forall msg. Number -> HueScrubProp msg
sensitivity = Scrub.sensitivity

-- | Set default value for reset
defaultValue :: forall msg. Hue.Hue -> HueScrubProp msg
defaultValue = Scrub.defaultValue

-- | Disable the input
scrubDisabled :: forall msg. Boolean -> HueScrubProp msg
scrubDisabled = Scrub.scrubDisabled

-- | Show reset button
showReset :: forall msg. Boolean -> HueScrubProp msg
showReset = Scrub.showReset

-- | Set change handler
onChange :: forall msg. (Hue.Hue -> msg) -> HueScrubProp msg
onChange = Scrub.onChange

-- | Called when scrub begins
onScrubStart :: forall msg. msg -> HueScrubProp msg
onScrubStart = Scrub.onScrubStart

-- | Called when scrub ends
onScrubEnd :: forall msg. msg -> HueScrubProp msg
onScrubEnd = Scrub.onScrubEnd

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hue scrubable input
-- |
-- | A motion graphics numeric input specialized for hue values.
-- | Uses the Hue Schema atom for type-safe color wheel position.
-- |
-- | ```purescript
-- | hueScrub (Hue.hue 180)
-- |   [ label "Fill Hue"
-- |   , onChange SetFillHue
-- |   ]
-- | ```
hueScrub :: forall msg. Hue.Hue -> Array (HueScrubProp msg) -> E.Element msg
hueScrub = Scrub.scrubableInput

