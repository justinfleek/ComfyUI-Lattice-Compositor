-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // element // qrcode // document // label
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Document Label — Label/description box configuration for QR codes.
-- |
-- | ## Label Options
-- |
-- | - Position: below, above, left, right
-- | - Content: title, description, timestamps
-- | - Style: colors, padding, border radius
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)

module Hydrogen.Element.Compound.QRCode.Document.Label
  ( -- * Label Position
    LabelPosition(..)
  
  -- * Label Configuration
  , LabelConfig
  , defaultLabel
  , labelWithTitle
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // label position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Label position relative to QR code.
data LabelPosition
  = LabelBelow
  | LabelAbove
  | LabelRight
  | LabelLeft

derive instance eqLabelPosition :: Eq LabelPosition

instance showLabelPosition :: Show LabelPosition where
  show LabelBelow = "below"
  show LabelAbove = "above"
  show LabelRight = "right"
  show LabelLeft = "left"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // label config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Label/description box configuration.
type LabelConfig =
  { show :: Boolean
  , position :: LabelPosition
  , showTitle :: Boolean
  , showDescription :: Boolean
  , showCreatedAt :: Boolean
  , showExpiresAt :: Boolean
  , backgroundColor :: String
  , textColor :: String
  , padding :: Number
  , borderRadius :: Number
  }

-- | Default label configuration
defaultLabel :: LabelConfig
defaultLabel =
  { show: false
  , position: LabelBelow
  , showTitle: true
  , showDescription: true
  , showCreatedAt: false
  , showExpiresAt: false
  , backgroundColor: "#f5f5f5"
  , textColor: "#333333"
  , padding: 12.0
  , borderRadius: 8.0
  }

-- | Label showing title only
labelWithTitle :: LabelConfig
labelWithTitle = defaultLabel { show = true, showDescription = false }
