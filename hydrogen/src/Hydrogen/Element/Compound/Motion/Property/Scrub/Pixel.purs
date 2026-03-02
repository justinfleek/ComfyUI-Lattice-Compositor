-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // motion // property // scrub // pixel
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pixel Scrubable Input — Position/dimension control (px)
-- |
-- | A motion graphics numeric input specialized for pixel values.
-- | Practical range of ±10000px for UI purposes.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Motion.Property.Scrub.Pixel as PixelScrub
-- | import Hydrogen.Schema.Dimension.Device (Pixel)
-- |
-- | myPositionInput :: Pixel -> Element Msg
-- | myPositionInput p = PixelScrub.pixelScrub p
-- |   [ PixelScrub.label "Position X"
-- |   , PixelScrub.onChange SetPositionX
-- |   ]
-- | ```
-- |
-- | ## Bounds
-- |
-- | | Property  | Value   | Notes |
-- | |-----------|---------|-------|
-- | | Min       | -10000  | Practical UI limit |
-- | | Max       | 10000   | Practical UI limit |
-- | | Step      | 1       | Integer pixels |
-- | | Precision | 1       | One decimal place |
-- | | Unit      | "px"    | Pixel unit |
-- | | Clamping  | No      | Values beyond range allowed |

module Hydrogen.Element.Compound.Motion.Property.Scrub.Pixel
  ( -- * Component
    pixelScrub
    
  -- * Props
  , PixelScrubProp
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
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Element.Compound.Motion.Property.ScrubableInput as Scrub

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═══════════════════════════════════════════════════════════���═════════════════

-- | Pixel-specific prop modifier
type PixelScrubProp msg = Scrub.ScrubableInputProp Device.Pixel msg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set label text
label :: forall msg. String -> PixelScrubProp msg
label = Scrub.label

-- | Set scrub sensitivity
sensitivity :: forall msg. Number -> PixelScrubProp msg
sensitivity = Scrub.sensitivity

-- | Set default value for reset
defaultValue :: forall msg. Device.Pixel -> PixelScrubProp msg
defaultValue = Scrub.defaultValue

-- | Disable the input
scrubDisabled :: forall msg. Boolean -> PixelScrubProp msg
scrubDisabled = Scrub.scrubDisabled

-- | Show reset button
showReset :: forall msg. Boolean -> PixelScrubProp msg
showReset = Scrub.showReset

-- | Set change handler
onChange :: forall msg. (Device.Pixel -> msg) -> PixelScrubProp msg
onChange = Scrub.onChange

-- | Called when scrub begins
onScrubStart :: forall msg. msg -> PixelScrubProp msg
onScrubStart = Scrub.onScrubStart

-- | Called when scrub ends
onScrubEnd :: forall msg. msg -> PixelScrubProp msg
onScrubEnd = Scrub.onScrubEnd

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pixel scrubable input
-- |
-- | A motion graphics numeric input specialized for pixel values.
-- | Uses the Pixel Schema atom for type-safe dimensional measurement.
-- |
-- | ```purescript
-- | pixelScrub (Device.px 100.0)
-- |   [ label "Position X"
-- |   , onChange SetPositionX
-- |   ]
-- | ```
pixelScrub :: forall msg. Device.Pixel -> Array (PixelScrubProp msg) -> E.Element msg
pixelScrub = Scrub.scrubableInput

