-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // motion // property // scrub // angle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Angle Scrubable Input — Rotation control (0-360°)
-- |
-- | A motion graphics numeric input specialized for angular rotation.
-- | Wraps around at 360° (360° becomes 0°).
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Motion.Property.Scrub.Angle as AngleScrub
-- | import Hydrogen.Schema.Geometry.Angle (Degrees)
-- |
-- | myAngleInput :: Degrees -> Element Msg
-- | myAngleInput a = AngleScrub.angleScrub a
-- |   [ AngleScrub.label "Rotation"
-- |   , AngleScrub.onChange SetRotation
-- |   ]
-- | ```
-- |
-- | ## Bounds
-- |
-- | | Property  | Value | Notes |
-- | |-----------|-------|-------|
-- | | Min       | 0°    | Right (3 o'clock) |
-- | | Max       | 360°  | Full rotation (wraps to 0) |
-- | | Step      | 1°    | Integer degrees |
-- | | Precision | 1     | One decimal place |
-- | | Unit      | "°"   | Degree symbol |
-- | | Wrapping  | Yes   | 360° becomes 0° |

module Hydrogen.Element.Compound.Motion.Property.Scrub.Angle
  ( -- * Component
    angleScrub
    
  -- * Props
  , AngleScrubProp
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
import Hydrogen.Schema.Geometry.Angle as Angle
import Hydrogen.Element.Compound.Motion.Property.ScrubableInput as Scrub

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Angle-specific prop modifier (using Degrees)
type AngleScrubProp msg = Scrub.ScrubableInputProp Angle.Degrees msg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set label text
label :: forall msg. String -> AngleScrubProp msg
label = Scrub.label

-- | Set scrub sensitivity
sensitivity :: forall msg. Number -> AngleScrubProp msg
sensitivity = Scrub.sensitivity

-- | Set default value for reset
defaultValue :: forall msg. Angle.Degrees -> AngleScrubProp msg
defaultValue = Scrub.defaultValue

-- | Disable the input
scrubDisabled :: forall msg. Boolean -> AngleScrubProp msg
scrubDisabled = Scrub.scrubDisabled

-- | Show reset button
showReset :: forall msg. Boolean -> AngleScrubProp msg
showReset = Scrub.showReset

-- | Set change handler
onChange :: forall msg. (Angle.Degrees -> msg) -> AngleScrubProp msg
onChange = Scrub.onChange

-- | Called when scrub begins
onScrubStart :: forall msg. msg -> AngleScrubProp msg
onScrubStart = Scrub.onScrubStart

-- | Called when scrub ends
onScrubEnd :: forall msg. msg -> AngleScrubProp msg
onScrubEnd = Scrub.onScrubEnd

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═══════════════════════════════════��═════════════════════════════════════════

-- | Angle scrubable input
-- |
-- | A motion graphics numeric input specialized for angular rotation.
-- | Uses the Degrees Schema atom for type-safe angular measurement.
-- |
-- | ```purescript
-- | angleScrub (Angle.degrees 45.0)
-- |   [ label "Rotation"
-- |   , onChange SetRotation
-- |   ]
-- | ```
angleScrub :: forall msg. Angle.Degrees -> Array (AngleScrubProp msg) -> E.Element msg
angleScrub = Scrub.scrubableInput

