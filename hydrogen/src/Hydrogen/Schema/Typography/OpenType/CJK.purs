-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // typography // opentype // cjk
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CJK - OpenType features for Chinese, Japanese, and Korean typography.
-- |
-- | East Asian typography has unique requirements that Western typography
-- | does not address. This module provides control over CJK-specific features.
-- |
-- | ## Writing Direction
-- |
-- | - **Horizontal**: Standard left-to-right (or right-to-left)
-- | - **Vertical**: Top-to-bottom, columns right-to-left
-- |
-- | ## Ruby (Annotations)
-- |
-- | Small annotations above/beside characters for pronunciation (furigana in
-- | Japanese, zhuyin in Chinese). Critical for language learning and accessibility.
-- |
-- | ## Glyph Forms
-- |
-- | - **Traditional**: Complex traditional Chinese characters (繁體字)
-- | - **Simplified**: Simplified Chinese characters (简体字)
-- | - **JIS78**: Japanese JIS X 0208-1978 forms
-- | - **JIS83**: Japanese JIS X 0208-1983 forms
-- | - **JIS90**: Japanese JIS X 0208-1990 forms
-- | - **JIS2004**: Japanese JIS X 0213:2004 forms
-- | - **Expert**: Expert/scholarly forms
-- |
-- | ## Punctuation
-- |
-- | - **Full-width**: Square punctuation for vertical text
-- | - **Half-width**: Narrow punctuation for horizontal text
-- | - **Proportional**: Natural widths
-- |
-- | ## CSS Mapping
-- |
-- | Maps to `writing-mode`, `text-orientation`, `ruby-position`,
-- | `font-variant-east-asian`, and `font-feature-settings`.

module Hydrogen.Schema.Typography.OpenType.CJK
  ( -- * Types
    WritingMode(..)
  , TextOrientation(..)
  , RubyPosition(..)
  , EastAsianVariant(..)
  , EastAsianWidth(..)
  , CJKFeatures(..)
  
  -- * Constructors
  , horizontal
  , vertical
  , verticalRuby
  , traditionalChinese
  , simplifiedChinese
  , japaneseModern
  , japaneseTraditional
  , custom
  
  -- * Modifiers
  , withWritingMode
  , withTextOrientation
  , withRubyPosition
  , withVariant
  , withWidth
  
  -- * Predicates
  , isVertical
  , isHorizontal
  , hasRuby
  , isTraditional
  , isSimplified
  
  -- * CSS Output
  , toLegacyCss
  , toFontFeatureSettings
  ) where

import Prelude

import Data.Array (intercalate)
import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // writing mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Writing direction
-- |
-- | Controls the primary direction of text flow.
data WritingMode
  = HorizontalTB  -- ^ Horizontal, top-to-bottom (standard)
  | VerticalRL    -- ^ Vertical, right-to-left (traditional CJK)
  | VerticalLR    -- ^ Vertical, left-to-right (Mongolian)

derive instance eqWritingMode :: Eq WritingMode
derive instance ordWritingMode :: Ord WritingMode

instance showWritingMode :: Show WritingMode where
  show HorizontalTB = "HorizontalTB"
  show VerticalRL = "VerticalRL"
  show VerticalLR = "VerticalLR"

-- | Convert writing mode to CSS value
writingModeToLegacyCss :: WritingMode -> String
writingModeToLegacyCss HorizontalTB = "horizontal-tb"
writingModeToLegacyCss VerticalRL = "vertical-rl"
writingModeToLegacyCss VerticalLR = "vertical-lr"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // text orientation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Character orientation in vertical text
-- |
-- | Controls how characters are rotated in vertical writing.
data TextOrientation
  = Mixed     -- ^ Rotate horizontal scripts, keep vertical scripts upright
  | Upright   -- ^ Keep all characters upright
  | Sideways  -- ^ Rotate all characters 90 degrees

derive instance eqTextOrientation :: Eq TextOrientation
derive instance ordTextOrientation :: Ord TextOrientation

instance showTextOrientation :: Show TextOrientation where
  show Mixed = "Mixed"
  show Upright = "Upright"
  show Sideways = "Sideways"

-- | Convert text orientation to CSS value
orientationToLegacyCss :: TextOrientation -> String
orientationToLegacyCss Mixed = "mixed"
orientationToLegacyCss Upright = "upright"
orientationToLegacyCss Sideways = "sideways"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // ruby position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Position of ruby annotations
-- |
-- | Ruby annotations (furigana, zhuyin) can be positioned in different ways.
data RubyPosition
  = RubyOver          -- ^ Above horizontal text / right of vertical text
  | RubyUnder         -- ^ Below horizontal text / left of vertical text
  | RubyInterCharacter -- ^ Between base characters (bopomofo style)

derive instance eqRubyPosition :: Eq RubyPosition
derive instance ordRubyPosition :: Ord RubyPosition

instance showRubyPosition :: Show RubyPosition where
  show RubyOver = "RubyOver"
  show RubyUnder = "RubyUnder"
  show RubyInterCharacter = "RubyInterCharacter"

-- | Convert ruby position to CSS value
rubyPositionToLegacyCss :: RubyPosition -> String
rubyPositionToLegacyCss RubyOver = "over"
rubyPositionToLegacyCss RubyUnder = "under"
rubyPositionToLegacyCss RubyInterCharacter = "inter-character"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // east asian variant
-- ═════════════════════════════════════════════════════════════════════════════

-- | East Asian glyph variant
-- |
-- | Controls which regional/historical glyph forms are used.
data EastAsianVariant
  = VariantNormal       -- ^ Use font's default forms
  | VariantTraditional  -- ^ Traditional Chinese (trad)
  | VariantSimplified   -- ^ Simplified Chinese (smpl)
  | VariantJIS78        -- ^ JIS X 0208-1978 (jp78)
  | VariantJIS83        -- ^ JIS X 0208-1983 (jp83)
  | VariantJIS90        -- ^ JIS X 0208-1990 (jp90)
  | VariantJIS04        -- ^ JIS X 0213:2004 (jp04)
  | VariantExpert       -- ^ Expert/scholarly forms (expt)
  | VariantRuby         -- ^ Ruby-optimized forms (ruby) - smaller, simpler

derive instance eqEastAsianVariant :: Eq EastAsianVariant
derive instance ordEastAsianVariant :: Ord EastAsianVariant

instance showEastAsianVariant :: Show EastAsianVariant where
  show VariantNormal = "VariantNormal"
  show VariantTraditional = "VariantTraditional"
  show VariantSimplified = "VariantSimplified"
  show VariantJIS78 = "VariantJIS78"
  show VariantJIS83 = "VariantJIS83"
  show VariantJIS90 = "VariantJIS90"
  show VariantJIS04 = "VariantJIS04"
  show VariantExpert = "VariantExpert"
  show VariantRuby = "VariantRuby"

-- | Convert variant to CSS font-variant-east-asian value
variantToLegacyCss :: EastAsianVariant -> String
variantToLegacyCss VariantNormal = "normal"
variantToLegacyCss VariantTraditional = "traditional"
variantToLegacyCss VariantSimplified = "simplified"
variantToLegacyCss VariantJIS78 = "jis78"
variantToLegacyCss VariantJIS83 = "jis83"
variantToLegacyCss VariantJIS90 = "jis90"
variantToLegacyCss VariantJIS04 = "jis04"
variantToLegacyCss VariantExpert = "expert"
variantToLegacyCss VariantRuby = "ruby"

-- | Convert variant to OpenType tag
variantToTag :: EastAsianVariant -> Maybe String
variantToTag VariantNormal = Nothing
variantToTag VariantTraditional = Just "trad"
variantToTag VariantSimplified = Just "smpl"
variantToTag VariantJIS78 = Just "jp78"
variantToTag VariantJIS83 = Just "jp83"
variantToTag VariantJIS90 = Just "jp90"
variantToTag VariantJIS04 = Just "jp04"
variantToTag VariantExpert = Just "expt"
variantToTag VariantRuby = Just "ruby"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // east asian width
-- ═════════════════════════════════════════════════════════════════════════════

-- | East Asian character widths
-- |
-- | Controls whether full-width or proportional forms are used.
data EastAsianWidth
  = WidthNormal         -- ^ Use font's default widths
  | WidthFullWidth      -- ^ Full-width forms (fwid)
  | WidthProportional   -- ^ Proportional-width forms (pwid)

derive instance eqEastAsianWidth :: Eq EastAsianWidth
derive instance ordEastAsianWidth :: Ord EastAsianWidth

instance showEastAsianWidth :: Show EastAsianWidth where
  show WidthNormal = "WidthNormal"
  show WidthFullWidth = "WidthFullWidth"
  show WidthProportional = "WidthProportional"

-- | Convert width to CSS font-variant-east-asian value
widthToLegacyCss :: EastAsianWidth -> String
widthToLegacyCss WidthNormal = ""
widthToLegacyCss WidthFullWidth = "full-width"
widthToLegacyCss WidthProportional = "proportional-width"

-- | Convert width to OpenType tag
widthToTag :: EastAsianWidth -> Maybe String
widthToTag WidthNormal = Nothing
widthToTag WidthFullWidth = Just "fwid"
widthToTag WidthProportional = Just "pwid"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // cjk features
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete CJK typography configuration
-- |
-- | Combines all East Asian typography features.
newtype CJKFeatures = CJKFeatures
  { writingMode :: WritingMode
  , textOrientation :: TextOrientation
  , rubyPosition :: Maybe RubyPosition
  , variant :: EastAsianVariant
  , width :: EastAsianWidth
  }

derive instance eqCJKFeatures :: Eq CJKFeatures

instance showCJKFeatures :: Show CJKFeatures where
  show (CJKFeatures c) =
    "CJKFeatures { writingMode: " <> show c.writingMode <>
    ", textOrientation: " <> show c.textOrientation <>
    ", rubyPosition: " <> show c.rubyPosition <>
    ", variant: " <> show c.variant <>
    ", width: " <> show c.width <> " }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Horizontal writing (standard web default)
horizontal :: CJKFeatures
horizontal = CJKFeatures
  { writingMode: HorizontalTB
  , textOrientation: Mixed
  , rubyPosition: Nothing
  , variant: VariantNormal
  , width: WidthNormal
  }

-- | Vertical writing (traditional CJK)
vertical :: CJKFeatures
vertical = CJKFeatures
  { writingMode: VerticalRL
  , textOrientation: Mixed
  , rubyPosition: Nothing
  , variant: VariantNormal
  , width: WidthNormal
  }

-- | Vertical writing with ruby annotations
verticalRuby :: CJKFeatures
verticalRuby = CJKFeatures
  { writingMode: VerticalRL
  , textOrientation: Mixed
  , rubyPosition: Just RubyOver
  , variant: VariantRuby
  , width: WidthNormal
  }

-- | Traditional Chinese typography
traditionalChinese :: CJKFeatures
traditionalChinese = CJKFeatures
  { writingMode: HorizontalTB
  , textOrientation: Mixed
  , rubyPosition: Nothing
  , variant: VariantTraditional
  , width: WidthNormal
  }

-- | Simplified Chinese typography
simplifiedChinese :: CJKFeatures
simplifiedChinese = CJKFeatures
  { writingMode: HorizontalTB
  , textOrientation: Mixed
  , rubyPosition: Nothing
  , variant: VariantSimplified
  , width: WidthNormal
  }

-- | Modern Japanese typography (JIS2004)
japaneseModern :: CJKFeatures
japaneseModern = CJKFeatures
  { writingMode: HorizontalTB
  , textOrientation: Mixed
  , rubyPosition: Nothing
  , variant: VariantJIS04
  , width: WidthNormal
  }

-- | Traditional Japanese typography (vertical with JIS78)
japaneseTraditional :: CJKFeatures
japaneseTraditional = CJKFeatures
  { writingMode: VerticalRL
  , textOrientation: Mixed
  , rubyPosition: Just RubyOver
  , variant: VariantJIS78
  , width: WidthNormal
  }

-- | Custom CJK configuration
custom
  :: { writingMode :: WritingMode
     , textOrientation :: TextOrientation
     , rubyPosition :: Maybe RubyPosition
     , variant :: EastAsianVariant
     , width :: EastAsianWidth
     }
  -> CJKFeatures
custom = CJKFeatures

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set writing mode
withWritingMode :: WritingMode -> CJKFeatures -> CJKFeatures
withWritingMode wm (CJKFeatures c) = CJKFeatures c { writingMode = wm }

-- | Set text orientation
withTextOrientation :: TextOrientation -> CJKFeatures -> CJKFeatures
withTextOrientation to (CJKFeatures c) = CJKFeatures c { textOrientation = to }

-- | Set ruby position
withRubyPosition :: RubyPosition -> CJKFeatures -> CJKFeatures
withRubyPosition rp (CJKFeatures c) = CJKFeatures c { rubyPosition = Just rp }

-- | Set glyph variant
withVariant :: EastAsianVariant -> CJKFeatures -> CJKFeatures
withVariant v (CJKFeatures c) = CJKFeatures c { variant = v }

-- | Set width variant
withWidth :: EastAsianWidth -> CJKFeatures -> CJKFeatures
withWidth w (CJKFeatures c) = CJKFeatures c { width = w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is vertical writing mode?
isVertical :: CJKFeatures -> Boolean
isVertical (CJKFeatures { writingMode: VerticalRL }) = true
isVertical (CJKFeatures { writingMode: VerticalLR }) = true
isVertical _ = false

-- | Is horizontal writing mode?
isHorizontal :: CJKFeatures -> Boolean
isHorizontal (CJKFeatures { writingMode: HorizontalTB }) = true
isHorizontal _ = false

-- | Has ruby annotations enabled?
hasRuby :: CJKFeatures -> Boolean
hasRuby (CJKFeatures { rubyPosition: Just _ }) = true
hasRuby _ = false

-- | Is traditional variant?
isTraditional :: CJKFeatures -> Boolean
isTraditional (CJKFeatures { variant: VariantTraditional }) = true
isTraditional _ = false

-- | Is simplified variant?
isSimplified :: CJKFeatures -> Boolean
isSimplified (CJKFeatures { variant: VariantSimplified }) = true
isSimplified _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- NOT an FFI boundary — pure string generation.
-- | Convert to CSS declarations
toLegacyCss :: CJKFeatures -> String
toLegacyCss (CJKFeatures c) =
  "writing-mode: " <> writingModeToLegacyCss c.writingMode <> ";\n" <>
  "text-orientation: " <> orientationToLegacyCss c.textOrientation <> ";" <>
  rubyLine <>
  variantLine
  where
  rubyLine :: String
  rubyLine = case c.rubyPosition of
    Nothing -> ""
    Just rp -> "\nruby-position: " <> rubyPositionToLegacyCss rp <> ";"

  variantLine :: String
  variantLine =
    let
      variantPart = variantToLegacyCss c.variant
      widthPart = widthToLegacyCss c.width
      combined = case variantPart, widthPart of
        "normal", "" -> ""
        v, "" -> v
        "normal", w -> w
        v, w -> v <> " " <> w
    in case combined of
      "" -> ""
      val -> "\nfont-variant-east-asian: " <> val <> ";"

-- | Convert to font-feature-settings value
-- |
-- | Complete control via OpenType feature tags.
toFontFeatureSettings :: CJKFeatures -> String
toFontFeatureSettings (CJKFeatures c) =
  let
    features =
      (case variantToTag c.variant of
        Nothing -> []
        Just tag -> ["\"" <> tag <> "\" 1"]) <>
      (case widthToTag c.width of
        Nothing -> []
        Just tag -> ["\"" <> tag <> "\" 1"])
  in case features of
    [] -> "font-feature-settings: normal;"
    _ -> "font-feature-settings: " <> intercalate ", " features <> ";"
