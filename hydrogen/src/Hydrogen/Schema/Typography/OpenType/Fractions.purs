-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // typography // opentype // fractions
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Fractions - OpenType fraction features for typographic refinement.
-- |
-- | OpenType fonts can automatically render fractions in two styles:
-- |
-- | ## Diagonal Fractions (frac)
-- |
-- | Standard diagonal slash: ½ ⅓ ¼ ⅔ ¾ ⅛ ⅜ ⅝ ⅞
-- | The numerator is superscript, denominator is subscript,
-- | with a diagonal slash between them.
-- | Best for: General use, body text, recipes
-- |
-- | ## Stacked Fractions (afrc)
-- |
-- | Numerator stacked above denominator with horizontal line:
-- |   1
-- |  ───
-- |   2
-- | Best for: Technical documents, mathematics, formal typography
-- |
-- | ## How it works
-- |
-- | When enabled, the font automatically converts sequences like "1/2"
-- | into proper fraction glyphs. The font must support this feature.
-- |
-- | ## CSS Mapping
-- |
-- | Maps to `font-variant-numeric` and `font-feature-settings`.

module Hydrogen.Schema.Typography.OpenType.Fractions
  ( -- * Types
    FractionStyle(..)
  , Fractions(..)
  
  -- * Constructors
  , normal
  , diagonal
  , stacked
  
  -- * Predicates
  , isDiagonal
  , isStacked
  , isEnabled
  
  -- * CSS Output
  , toLegacyCss
  , toFontFeatureSettings
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // fraction style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fraction rendering style
-- |
-- | Controls how sequences like "1/2" are rendered.
data FractionStyle
  = FractionNormal   -- ^ No automatic fraction rendering
  | FractionDiagonal -- ^ Diagonal fractions (½ style)
  | FractionStacked  -- ^ Stacked/horizontal fractions

derive instance eqFractionStyle :: Eq FractionStyle
derive instance ordFractionStyle :: Ord FractionStyle

instance showFractionStyle :: Show FractionStyle where
  show FractionNormal = "FractionNormal"
  show FractionDiagonal = "FractionDiagonal"
  show FractionStacked = "FractionStacked"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // fractions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fraction configuration
-- |
-- | Simple wrapper around FractionStyle for consistency with other OpenType modules.
newtype Fractions = Fractions
  { style :: FractionStyle
  }

derive instance eqFractions :: Eq Fractions

instance showFractions :: Show Fractions where
  show (Fractions f) = "Fractions { style: " <> show f.style <> " }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normal (no automatic fraction rendering)
-- |
-- | Sequences like "1/2" remain as typed.
normal :: Fractions
normal = Fractions { style: FractionNormal }

-- | Diagonal fractions
-- |
-- | Sequences like "1/2" become proper diagonal fractions (½ style).
-- | Uses the 'frac' OpenType feature.
diagonal :: Fractions
diagonal = Fractions { style: FractionDiagonal }

-- | Stacked fractions
-- |
-- | Sequences like "1/2" become stacked fractions with horizontal bar.
-- | Uses the 'afrc' OpenType feature.
-- | Note: Less commonly supported than diagonal fractions.
stacked :: Fractions
stacked = Fractions { style: FractionStacked }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is diagonal fraction style set?
isDiagonal :: Fractions -> Boolean
isDiagonal (Fractions { style: FractionDiagonal }) = true
isDiagonal _ = false

-- | Is stacked fraction style set?
isStacked :: Fractions -> Boolean
isStacked (Fractions { style: FractionStacked }) = true
isStacked _ = false

-- | Is any fraction style enabled (not normal)?
isEnabled :: Fractions -> Boolean
isEnabled (Fractions { style: FractionNormal }) = false
isEnabled _ = true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- NOT an FFI boundary — pure string generation.
-- | Convert to CSS font-variant-numeric value
toLegacyCss :: Fractions -> String
toLegacyCss (Fractions { style }) = case style of
  FractionNormal -> "font-variant-numeric: normal;"
  FractionDiagonal -> "font-variant-numeric: diagonal-fractions;"
  FractionStacked -> "font-variant-numeric: stacked-fractions;"

-- | Convert to font-feature-settings value
-- |
-- | More explicit control using OpenType feature tags.
toFontFeatureSettings :: Fractions -> String
toFontFeatureSettings (Fractions { style }) = case style of
  FractionNormal -> "font-feature-settings: \"frac\" 0, \"afrc\" 0;"
  FractionDiagonal -> "font-feature-settings: \"frac\" 1;"
  FractionStacked -> "font-feature-settings: \"afrc\" 1;"
