-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // typography // text-transform
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TextTransform - typographic case transformation.
-- |
-- | Controls how text case is rendered, independent of source text:
-- | - **None**: Preserve original case
-- | - **Uppercase**: TRANSFORM TO ALL CAPS
-- | - **Lowercase**: transform to all lowercase
-- | - **Capitalize**: Transform To Title Case (first letter of each word)
-- |
-- | Note: Uppercase text requires increased letter-spacing (tracking) for
-- | readability. See LetterSpacing.uppercase for the standard adjustment.

module Hydrogen.Schema.Typography.TextTransform
  ( TextTransform(..)
  , toLegacyCss
  , requiresTracking
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // text transform
-- ═════════════════════════════════════════════════════════════════════════════

-- | Text case transformation
-- |
-- | Applied via CSS text-transform property. The transformation is visual
-- | only — underlying text content is preserved.
data TextTransform
  = None       -- ^ Preserve original case
  | Uppercase  -- ^ TRANSFORM TO ALL CAPS
  | Lowercase  -- ^ transform to all lowercase
  | Capitalize -- ^ Transform To Title Case

derive instance eqTextTransform :: Eq TextTransform
derive instance ordTextTransform :: Ord TextTransform

instance showTextTransform :: Show TextTransform where
  show None = "None"
  show Uppercase = "Uppercase"
  show Lowercase = "Lowercase"
  show Capitalize = "Capitalize"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- NOT an FFI boundary - pure string generation.
-- | Convert to CSS text-transform value
toLegacyCss :: TextTransform -> String
toLegacyCss None = "none"
toLegacyCss Uppercase = "uppercase"
toLegacyCss Lowercase = "lowercase"
toLegacyCss Capitalize = "capitalize"

-- | Does this transform require additional letter-spacing?
-- |
-- | Uppercase text needs tracking because:
-- | - All letters have uniform height (no ascenders/descenders)
-- | - Visual density is higher
-- | - Letters "crowd" each other without extra space
requiresTracking :: TextTransform -> Boolean
requiresTracking Uppercase = true
requiresTracking _ = false
