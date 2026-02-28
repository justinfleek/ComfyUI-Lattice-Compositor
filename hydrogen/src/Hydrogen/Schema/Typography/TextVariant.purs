-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // typography // text-variant
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TextVariant - typographic case variants beyond simple transforms.
-- |
-- | While TextTransform changes case at render time, TextVariant uses
-- | OpenType features to access variant glyphs designed for specific uses:
-- |
-- | - **SmallCaps**: Uppercase forms at lowercase height
-- | - **AllSmallCaps**: All letters as small capitals
-- | - **PetiteCaps**: Even smaller capitals (between x-height and cap-height)
-- | - **AllPetiteCaps**: All letters as petite capitals
-- | - **Unicase**: Mixed uppercase/lowercase forms
-- | - **TitlingCaps**: Capitals optimized for large display sizes
-- |
-- | ## Why variants matter
-- |
-- | Small capitals are not simply "shrunk uppercase" — they are distinct
-- | glyphs with adjusted stroke weights to match the visual weight of
-- | lowercase letters. A proper small-cap 'A' has thicker strokes than
-- | a regular 'A' reduced to the same height.
-- |
-- | ## CSS Mapping
-- |
-- | Maps to `font-variant-caps` and related OpenType features.

module Hydrogen.Schema.Typography.TextVariant
  ( -- * Types
    CapsVariant(..)
  , TextVariant(..)
  
  -- * Constructors
  , normal
  , smallCaps
  , allSmallCaps
  , petiteCaps
  , allPetiteCaps
  , unicase
  , titlingCaps
  
  -- * Predicates
  , usesSmallCaps
  , usesPetiteCaps
  , affectsLowercase
  , affectsUppercase
  
  -- * CSS Output
  , toLegacyCss
  , toFontFeatureSettings
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // caps variant
-- ═════════════════════════════════════════════════════════════════════════════

-- | Capital letter variants
-- |
-- | These are distinct from TextTransform — they use actual variant glyphs
-- | rather than transforming existing letters.
data CapsVariant
  = CapsNormal       -- ^ No variant, use default capitals
  | SmallCaps        -- ^ Lowercase → small capitals
  | AllSmallCaps     -- ^ All letters → small capitals
  | PetiteCaps       -- ^ Lowercase → petite capitals (smaller than small-caps)
  | AllPetiteCaps    -- ^ All letters → petite capitals
  | Unicase          -- ^ Mixed case forms (uppercase/lowercase unified)
  | TitlingCaps      -- ^ Titling capitals (optimized for large display)

derive instance eqCapsVariant :: Eq CapsVariant
derive instance ordCapsVariant :: Ord CapsVariant

instance showCapsVariant :: Show CapsVariant where
  show CapsNormal = "CapsNormal"
  show SmallCaps = "SmallCaps"
  show AllSmallCaps = "AllSmallCaps"
  show PetiteCaps = "PetiteCaps"
  show AllPetiteCaps = "AllPetiteCaps"
  show Unicase = "Unicase"
  show TitlingCaps = "TitlingCaps"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // text variant
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete text variant specification
-- |
-- | Wraps CapsVariant with potential for future expansion
-- | (e.g., combining with other variant features).
newtype TextVariant = TextVariant
  { caps :: CapsVariant
  }

derive instance eqTextVariant :: Eq TextVariant
derive instance ordTextVariant :: Ord TextVariant

instance showTextVariant :: Show TextVariant where
  show (TextVariant tv) = "TextVariant { caps: " <> show tv.caps <> " }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normal text (no variants)
normal :: TextVariant
normal = TextVariant { caps: CapsNormal }

-- | Small capitals for lowercase letters
-- |
-- | "The Quick Brown Fox" → "The QUICK BROWN FOX" (with small-cap forms)
-- | Uppercase letters remain full-size capitals.
smallCaps :: TextVariant
smallCaps = TextVariant { caps: SmallCaps }

-- | All letters as small capitals
-- |
-- | "The Quick Brown Fox" → all letters in small-cap forms
-- | Both uppercase and lowercase become small capitals.
allSmallCaps :: TextVariant
allSmallCaps = TextVariant { caps: AllSmallCaps }

-- | Petite capitals for lowercase letters
-- |
-- | Petite caps are smaller than small caps — typically at x-height
-- | rather than between x-height and cap-height.
petiteCaps :: TextVariant
petiteCaps = TextVariant { caps: PetiteCaps }

-- | All letters as petite capitals
allPetiteCaps :: TextVariant
allPetiteCaps = TextVariant { caps: AllPetiteCaps }

-- | Unicase (mixed case forms)
-- |
-- | Uses glyphs that blend uppercase and lowercase characteristics.
-- | The visual distinction between cases is minimized.
unicase :: TextVariant
unicase = TextVariant { caps: Unicase }

-- | Titling capitals
-- |
-- | Capitals optimized for large display sizes. These typically have
-- | finer details and lighter stroke weights than text capitals.
titlingCaps :: TextVariant
titlingCaps = TextVariant { caps: TitlingCaps }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Does this variant use small capitals?
usesSmallCaps :: TextVariant -> Boolean
usesSmallCaps (TextVariant { caps: SmallCaps }) = true
usesSmallCaps (TextVariant { caps: AllSmallCaps }) = true
usesSmallCaps _ = false

-- | Does this variant use petite capitals?
usesPetiteCaps :: TextVariant -> Boolean
usesPetiteCaps (TextVariant { caps: PetiteCaps }) = true
usesPetiteCaps (TextVariant { caps: AllPetiteCaps }) = true
usesPetiteCaps _ = false

-- | Does this variant affect lowercase letters?
affectsLowercase :: TextVariant -> Boolean
affectsLowercase (TextVariant { caps: CapsNormal }) = false
affectsLowercase (TextVariant { caps: TitlingCaps }) = false
affectsLowercase _ = true

-- | Does this variant affect uppercase letters?
affectsUppercase :: TextVariant -> Boolean
affectsUppercase (TextVariant { caps: AllSmallCaps }) = true
affectsUppercase (TextVariant { caps: AllPetiteCaps }) = true
affectsUppercase (TextVariant { caps: Unicase }) = true
affectsUppercase (TextVariant { caps: TitlingCaps }) = true
affectsUppercase _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- NOT an FFI boundary — pure string generation.
-- | Convert to CSS font-variant-caps value
toLegacyCss :: TextVariant -> String
toLegacyCss (TextVariant { caps }) = case caps of
  CapsNormal -> "font-variant-caps: normal;"
  SmallCaps -> "font-variant-caps: small-caps;"
  AllSmallCaps -> "font-variant-caps: all-small-caps;"
  PetiteCaps -> "font-variant-caps: petite-caps;"
  AllPetiteCaps -> "font-variant-caps: all-petite-caps;"
  Unicase -> "font-variant-caps: unicase;"
  TitlingCaps -> "font-variant-caps: titling-caps;"

-- | Convert to font-feature-settings value
-- |
-- | For browsers that don't support font-variant-caps, or when you need
-- | explicit OpenType feature control.
toFontFeatureSettings :: TextVariant -> String
toFontFeatureSettings (TextVariant { caps }) = case caps of
  CapsNormal -> "font-feature-settings: normal;"
  SmallCaps -> "font-feature-settings: \"smcp\" 1;"
  AllSmallCaps -> "font-feature-settings: \"smcp\" 1, \"c2sc\" 1;"
  PetiteCaps -> "font-feature-settings: \"pcap\" 1;"
  AllPetiteCaps -> "font-feature-settings: \"pcap\" 1, \"c2pc\" 1;"
  Unicase -> "font-feature-settings: \"unic\" 1;"
  TitlingCaps -> "font-feature-settings: \"titl\" 1;"
