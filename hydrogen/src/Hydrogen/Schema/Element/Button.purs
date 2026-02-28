-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // element // button
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Button — STACKED compound composing atoms from all pillars.
-- |
-- | A button is a bounded region of space-time where AI communicates
-- | intent, state, and need. This compound includes EVERY atom a button
-- | could ever need, enabling agents to compose any variant by selection.
-- |
-- | ## Sub-modules
-- |
-- | - Geometry: size, padding, corner radii
-- | - Appearance: fill, border, shadow, opacity
-- | - Behavior: haptic, audio, timing
-- | - Semantics: purpose, identity, accessibility
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | myButton = button
-- |   { geometry: defaultGeometry
-- |   , appearance: defaultAppearance
-- |   , behavior: defaultBehavior
-- |   , semantics: actionSemantics "Click me"
-- |   }
-- | ```

module Hydrogen.Schema.Element.Button
  ( -- * Button Compound Type
    Button
  , button
  , defaultButton
    -- * Re-exports from sub-modules
  , module Hydrogen.Schema.Element.Button.Geometry
  , module Hydrogen.Schema.Element.Button.Appearance
  , module Hydrogen.Schema.Element.Button.Behavior
  , module Hydrogen.Schema.Element.Button.Semantics
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Element.Button.Geometry
  ( ButtonGeometry
  , defaultGeometry
  , mkGeometry
  , geoWidth
  , geoHeight
  , geoPadding
  , geoCornerRadii
  )

import Hydrogen.Schema.Element.Button.Appearance
  ( ButtonAppearance
  , defaultAppearance
  , appFill
  , appShadow
  , appBorderWidth
  , appBorderColor
  , appOpacity
  )

import Hydrogen.Schema.Element.Button.Behavior
  ( ButtonBehavior
  , defaultBehavior
  , behHapticPress
  , behHapticRelease
  , behAudioClick
  , behLongPressMs
  )

import Hydrogen.Schema.Element.Button.Semantics
  ( ButtonSemantics
  , defaultSemantics
  , actionSemantics
  , submitSemantics
  , toggleSemantics
  , semPurpose
  , semLabel
  , semToggleState
  , semDisabled
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // button type
-- ═══════════════════════════════════════════════════════════════════════════════

-- | STACKED Button compound — complete button with all pillar atoms.
-- |
-- | Composes:
-- | - Geometry (spatial layout)
-- | - Appearance (visual surface)
-- | - Behavior (interaction response)
-- | - Semantics (purpose and accessibility)
type Button =
  { geometry :: ButtonGeometry
  , appearance :: ButtonAppearance
  , behavior :: ButtonBehavior
  , semantics :: ButtonSemantics
  }

-- | Create a button with all properties.
button
  :: ButtonGeometry
  -> ButtonAppearance
  -> ButtonBehavior
  -> ButtonSemantics
  -> Button
button geo app beh sem =
  { geometry: geo
  , appearance: app
  , behavior: beh
  , semantics: sem
  }

-- | Default button with sensible defaults.
-- |
-- | Blue fill, 8px corners, light haptic, "Button" label.
defaultButton :: Button
defaultButton =
  { geometry: defaultGeometry
  , appearance: defaultAppearance
  , behavior: defaultBehavior
  , semantics: defaultSemantics "Button"
  }
