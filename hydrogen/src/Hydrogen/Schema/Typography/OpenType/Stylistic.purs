-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // typography // opentype // stylistic
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Stylistic - OpenType stylistic alternates and sets.
-- |
-- | OpenType provides multiple ways to access alternate glyph designs:
-- |
-- | ## Stylistic Sets (ss01-ss20)
-- |
-- | Named collections of alternate glyphs. The specific alternates vary by font.
-- | Common uses:
-- | - ss01: Alternate 'a' or 'g' forms
-- | - ss02: Different numeral styles
-- | - ss03-ss20: Font-specific alternates
-- |
-- | ## Stylistic Alternates (salt)
-- |
-- | Generic alternate forms (font decides which glyphs to substitute).
-- |
-- | ## Swash (swsh)
-- |
-- | Decorative flourishes on letters, typically for display text.
-- | Example: Elegant capitals with ornamental strokes.
-- |
-- | ## Contextual Alternates (calt)
-- |
-- | Alternates that depend on surrounding characters.
-- | Common in script fonts for natural connections.
-- |
-- | ## Character Variants (cv01-cv99)
-- |
-- | Per-character alternate selection. More granular than stylistic sets.
-- |
-- | ## CSS Mapping
-- |
-- | Maps to `font-feature-settings` (no high-level CSS property exists).

module Hydrogen.Schema.Typography.OpenType.Stylistic
  ( -- * Types
    StylisticSet(..)
  , CharacterVariant(..)
  , Stylistic(..)
  
  -- * Constructors
  , none
  , alternates
  , swash
  , contextual
  , stylisticSet
  , characterVariant
  , custom
  
  -- * Accessors
  , setNumber
  , variantNumber
  
  -- * Modifiers
  , withAlternates
  , withSwash
  , withContextual
  , addStylisticSet
  , removeStylisticSet
  , addCharacterVariant
  
  -- * Predicates
  , hasAlternates
  , hasSwash
  , hasContextual
  , hasStylisticSet
  , hasCharacterVariant
  , isDefault
  
  -- * CSS Output
  , toFontFeatureSettings
  ) where

import Prelude

import Data.Array (elem, filter, intercalate, snoc)
import Data.Foldable (any)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // stylistic set
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stylistic set identifier (ss01-ss20)
-- |
-- | OpenType supports 20 stylistic sets. The actual alternates are font-specific.
newtype StylisticSet = StylisticSet Int

derive instance eqStylisticSet :: Eq StylisticSet
derive instance ordStylisticSet :: Ord StylisticSet

instance showStylisticSet :: Show StylisticSet where
  show (StylisticSet n) = "StylisticSet " <> show n

-- | Create a stylistic set, clamping to valid range 1-20
mkStylisticSet :: Int -> StylisticSet
mkStylisticSet n
  | n < 1 = StylisticSet 1
  | n > 20 = StylisticSet 20
  | otherwise = StylisticSet n

-- | Get the set number (1-20)
setNumber :: StylisticSet -> Int
setNumber (StylisticSet n) = n

-- | Convert to OpenType tag (ss01, ss02, etc.)
setToTag :: StylisticSet -> String
setToTag (StylisticSet n) =
  let padded = if n < 10 then "0" <> show n else show n
  in "ss" <> padded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // character variant
-- ═════════════════════════════════════════════════════════════════════════════

-- | Character variant identifier (cv01-cv99)
-- |
-- | Per-character alternate selection. More granular than stylistic sets.
newtype CharacterVariant = CharacterVariant Int

derive instance eqCharacterVariant :: Eq CharacterVariant
derive instance ordCharacterVariant :: Ord CharacterVariant

instance showCharacterVariant :: Show CharacterVariant where
  show (CharacterVariant n) = "CharacterVariant " <> show n

-- | Create a character variant, clamping to valid range 1-99
mkCharacterVariant :: Int -> CharacterVariant
mkCharacterVariant n
  | n < 1 = CharacterVariant 1
  | n > 99 = CharacterVariant 99
  | otherwise = CharacterVariant n

-- | Get the variant number (1-99)
variantNumber :: CharacterVariant -> Int
variantNumber (CharacterVariant n) = n

-- | Convert to OpenType tag (cv01, cv02, etc.)
variantToTag :: CharacterVariant -> String
variantToTag (CharacterVariant n) =
  let padded = if n < 10 then "0" <> show n else show n
  in "cv" <> padded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // stylistic
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete stylistic configuration
-- |
-- | Combines all stylistic features into a single compound.
newtype Stylistic = Stylistic
  { alternates :: Boolean           -- ^ salt feature
  , swash :: Boolean                -- ^ swsh feature
  , contextual :: Boolean           -- ^ calt feature
  , stylisticSets :: Array StylisticSet      -- ^ ss01-ss20
  , characterVariants :: Array CharacterVariant  -- ^ cv01-cv99
  }

derive instance eqStylistic :: Eq Stylistic

instance showStylistic :: Show Stylistic where
  show (Stylistic s) =
    "Stylistic { alternates: " <> show s.alternates <>
    ", swash: " <> show s.swash <>
    ", contextual: " <> show s.contextual <>
    ", stylisticSets: " <> show s.stylisticSets <>
    ", characterVariants: " <> show s.characterVariants <> " }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | No stylistic features (defaults)
none :: Stylistic
none = Stylistic
  { alternates: false
  , swash: false
  , contextual: false
  , stylisticSets: []
  , characterVariants: []
  }

-- | Enable stylistic alternates (salt)
alternates :: Stylistic
alternates = Stylistic
  { alternates: true
  , swash: false
  , contextual: false
  , stylisticSets: []
  , characterVariants: []
  }

-- | Enable swash (swsh)
swash :: Stylistic
swash = Stylistic
  { alternates: false
  , swash: true
  , contextual: false
  , stylisticSets: []
  , characterVariants: []
  }

-- | Enable contextual alternates (calt)
-- |
-- | Usually enabled by default in most fonts. This makes it explicit.
contextual :: Stylistic
contextual = Stylistic
  { alternates: false
  , swash: false
  , contextual: true
  , stylisticSets: []
  , characterVariants: []
  }

-- | Enable a specific stylistic set
-- |
-- | @stylisticSet 1@ enables ss01
stylisticSet :: Int -> Stylistic
stylisticSet n = Stylistic
  { alternates: false
  , swash: false
  , contextual: false
  , stylisticSets: [mkStylisticSet n]
  , characterVariants: []
  }

-- | Enable a specific character variant
-- |
-- | @characterVariant 1@ enables cv01
characterVariant :: Int -> Stylistic
characterVariant n = Stylistic
  { alternates: false
  , swash: false
  , contextual: false
  , stylisticSets: []
  , characterVariants: [mkCharacterVariant n]
  }

-- | Custom stylistic configuration
custom
  :: { alternates :: Boolean
     , swash :: Boolean
     , contextual :: Boolean
     , stylisticSets :: Array Int
     , characterVariants :: Array Int
     }
  -> Stylistic
custom cfg = Stylistic
  { alternates: cfg.alternates
  , swash: cfg.swash
  , contextual: cfg.contextual
  , stylisticSets: map mkStylisticSet cfg.stylisticSets
  , characterVariants: map mkCharacterVariant cfg.characterVariants
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enable stylistic alternates
withAlternates :: Stylistic -> Stylistic
withAlternates (Stylistic s) = Stylistic s { alternates = true }

-- | Enable swash
withSwash :: Stylistic -> Stylistic
withSwash (Stylistic s) = Stylistic s { swash = true }

-- | Enable contextual alternates
withContextual :: Stylistic -> Stylistic
withContextual (Stylistic s) = Stylistic s { contextual = true }

-- | Add a stylistic set
addStylisticSet :: Int -> Stylistic -> Stylistic
addStylisticSet n (Stylistic s) =
  let newSet = mkStylisticSet n
  in if elem newSet s.stylisticSets
     then Stylistic s
     else Stylistic s { stylisticSets = snoc s.stylisticSets newSet }

-- | Remove a stylistic set
removeStylisticSet :: Int -> Stylistic -> Stylistic
removeStylisticSet n (Stylistic s) =
  let targetSet = mkStylisticSet n
  in Stylistic s { stylisticSets = filter (_ /= targetSet) s.stylisticSets }

-- | Add a character variant
addCharacterVariant :: Int -> Stylistic -> Stylistic
addCharacterVariant n (Stylistic s) =
  let newVar = mkCharacterVariant n
  in if elem newVar s.characterVariants
     then Stylistic s
     else Stylistic s { characterVariants = snoc s.characterVariants newVar }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Are stylistic alternates enabled?
hasAlternates :: Stylistic -> Boolean
hasAlternates (Stylistic { alternates: true }) = true
hasAlternates _ = false

-- | Is swash enabled?
hasSwash :: Stylistic -> Boolean
hasSwash (Stylistic { swash: true }) = true
hasSwash _ = false

-- | Are contextual alternates enabled?
hasContextual :: Stylistic -> Boolean
hasContextual (Stylistic { contextual: true }) = true
hasContextual _ = false

-- | Is a specific stylistic set enabled?
hasStylisticSet :: Int -> Stylistic -> Boolean
hasStylisticSet n (Stylistic s) = any (\(StylisticSet m) -> m == n) s.stylisticSets

-- | Is a specific character variant enabled?
hasCharacterVariant :: Int -> Stylistic -> Boolean
hasCharacterVariant n (Stylistic s) = any (\(CharacterVariant m) -> m == n) s.characterVariants

-- | Are all features at default (nothing enabled)?
isDefault :: Stylistic -> Boolean
isDefault (Stylistic s) =
  not s.alternates &&
  not s.swash &&
  not s.contextual &&
  s.stylisticSets == [] &&
  s.characterVariants == []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- NOT an FFI boundary — pure string generation.
-- | Convert to font-feature-settings value
-- |
-- | Note: There is no high-level CSS property for stylistic features,
-- | so we must use font-feature-settings directly.
toFontFeatureSettings :: Stylistic -> String
toFontFeatureSettings (Stylistic s) =
  let
    features =
      (if s.alternates then ["\"salt\" 1"] else []) <>
      (if s.swash then ["\"swsh\" 1"] else []) <>
      (if s.contextual then ["\"calt\" 1"] else []) <>
      map (\ss -> "\"" <> setToTag ss <> "\" 1") s.stylisticSets <>
      map (\cv -> "\"" <> variantToTag cv <> "\" 1") s.characterVariants
  in case features of
    [] -> "font-feature-settings: normal;"
    _ -> "font-feature-settings: " <> intercalate ", " features <> ";"
