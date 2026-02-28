-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // typography // opentype // numerals
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Numerals - OpenType numeral features for typographic refinement.
-- |
-- | OpenType fonts can contain multiple numeral styles for different contexts:
-- |
-- | ## Figure Style (Vertical Position)
-- |
-- | - **Lining**: Numbers aligned on the baseline with uniform height (1234567890)
-- |   Best for: Headlines, tabular data, all-caps text
-- |
-- | - **Oldstyle**: Numbers with varying heights and descenders (like lowercase)
-- |   Best for: Body text, running prose, elegant typography
-- |
-- | ## Figure Spacing (Horizontal Alignment)
-- |
-- | - **Proportional**: Each digit has natural width (1 is narrower than 0)
-- |   Best for: Body text, natural reading flow
-- |
-- | - **Tabular**: All digits have equal width for vertical alignment
-- |   Best for: Financial data, tables, prices, code
-- |
-- | ## Combinations
-- |
-- | The four combinations serve different purposes:
-- | - Proportional Oldstyle: Elegant body text
-- | - Proportional Lining: Headlines, display
-- | - Tabular Lining: Financial tables, prices
-- | - Tabular Oldstyle: Data tables in body text context
-- |
-- | ## CSS Mapping
-- |
-- | Maps to `font-variant-numeric` and `font-feature-settings`.

module Hydrogen.Schema.Typography.OpenType.Numerals
  ( -- * Types
    FigureStyle(..)
  , FigureSpacing(..)
  , SlashedZero(..)
  , Numerals(..)
  
  -- * Constructors
  , normal
  , liningProportional
  , liningTabular
  , oldstyleProportional
  , oldstyleTabular
  , tabular
  , slashedZero
  , custom
  
  -- * Modifiers
  , withLining
  , withOldstyle
  , withProportional
  , withTabular
  , withSlashedZero
  , withoutSlashedZero
  
  -- * Predicates
  , isLining
  , isOldstyle
  , isProportional
  , isTabular
  , hasSlashedZero
  
  -- * CSS Output
  , toLegacyCss
  , toFontFeatureSettings
  ) where

import Prelude

import Data.Array (intercalate)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // figure style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vertical style of numerals
-- |
-- | Controls whether numbers have uniform height (lining) or vary
-- | like lowercase letters (oldstyle).
data FigureStyle
  = StyleDefault   -- ^ Use font's default
  | StyleLining    -- ^ Uniform height, aligned to cap height
  | StyleOldstyle  -- ^ Varying height with descenders

derive instance eqFigureStyle :: Eq FigureStyle
derive instance ordFigureStyle :: Ord FigureStyle

instance showFigureStyle :: Show FigureStyle where
  show StyleDefault = "StyleDefault"
  show StyleLining = "StyleLining"
  show StyleOldstyle = "StyleOldstyle"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // figure spacing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Horizontal spacing of numerals
-- |
-- | Controls whether digits have natural widths (proportional) or
-- | uniform widths for tabular alignment (tabular).
data FigureSpacing
  = SpacingDefault      -- ^ Use font's default
  | SpacingProportional -- ^ Natural widths (1 narrower than 0)
  | SpacingTabular      -- ^ Equal widths for column alignment

derive instance eqFigureSpacing :: Eq FigureSpacing
derive instance ordFigureSpacing :: Ord FigureSpacing

instance showFigureSpacing :: Show FigureSpacing where
  show SpacingDefault = "SpacingDefault"
  show SpacingProportional = "SpacingProportional"
  show SpacingTabular = "SpacingTabular"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // slashed zero
-- ═════════════════════════════════════════════════════════════════════════════

-- | Slashed zero feature
-- |
-- | Adds a diagonal slash through zero to distinguish from letter O.
-- | Essential for technical contexts, code, serial numbers.
data SlashedZero
  = ZeroDefault  -- ^ Use font's default
  | ZeroSlashed  -- ^ Zero with diagonal slash
  | ZeroNormal   -- ^ Explicitly no slash

derive instance eqSlashedZero :: Eq SlashedZero
derive instance ordSlashedZero :: Ord SlashedZero

instance showSlashedZero :: Show SlashedZero where
  show ZeroDefault = "ZeroDefault"
  show ZeroSlashed = "ZeroSlashed"
  show ZeroNormal = "ZeroNormal"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // numerals
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete numeral configuration
-- |
-- | Combines figure style, spacing, and slashed zero settings.
newtype Numerals = Numerals
  { figureStyle :: FigureStyle
  , figureSpacing :: FigureSpacing
  , slashedZero :: SlashedZero
  }

derive instance eqNumerals :: Eq Numerals

instance showNumerals :: Show Numerals where
  show (Numerals n) =
    "Numerals { figureStyle: " <> show n.figureStyle <>
    ", figureSpacing: " <> show n.figureSpacing <>
    ", slashedZero: " <> show n.slashedZero <> " }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normal numerals (font defaults)
normal :: Numerals
normal = Numerals
  { figureStyle: StyleDefault
  , figureSpacing: SpacingDefault
  , slashedZero: ZeroDefault
  }

-- | Lining proportional numerals
-- |
-- | Best for: Headlines, display text, prices in running text
liningProportional :: Numerals
liningProportional = Numerals
  { figureStyle: StyleLining
  , figureSpacing: SpacingProportional
  , slashedZero: ZeroDefault
  }

-- | Lining tabular numerals
-- |
-- | Best for: Financial tables, spreadsheets, prices in columns
liningTabular :: Numerals
liningTabular = Numerals
  { figureStyle: StyleLining
  , figureSpacing: SpacingTabular
  , slashedZero: ZeroDefault
  }

-- | Oldstyle proportional numerals
-- |
-- | Best for: Body text, elegant prose, book typography
oldstyleProportional :: Numerals
oldstyleProportional = Numerals
  { figureStyle: StyleOldstyle
  , figureSpacing: SpacingProportional
  , slashedZero: ZeroDefault
  }

-- | Oldstyle tabular numerals
-- |
-- | Best for: Tables within body text, data that should blend with prose
oldstyleTabular :: Numerals
oldstyleTabular = Numerals
  { figureStyle: StyleOldstyle
  , figureSpacing: SpacingTabular
  , slashedZero: ZeroDefault
  }

-- | Tabular numerals (with default style)
-- |
-- | Convenience constructor for tabular spacing regardless of style.
tabular :: Numerals
tabular = Numerals
  { figureStyle: StyleDefault
  , figureSpacing: SpacingTabular
  , slashedZero: ZeroDefault
  }

-- | Numerals with slashed zero
-- |
-- | Use for code, serial numbers, technical contexts.
slashedZero :: Numerals
slashedZero = Numerals
  { figureStyle: StyleDefault
  , figureSpacing: SpacingDefault
  , slashedZero: ZeroSlashed
  }

-- | Custom numeral configuration
custom :: FigureStyle -> FigureSpacing -> SlashedZero -> Numerals
custom style spacing zero = Numerals
  { figureStyle: style
  , figureSpacing: spacing
  , slashedZero: zero
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set lining figure style
withLining :: Numerals -> Numerals
withLining (Numerals n) = Numerals n { figureStyle = StyleLining }

-- | Set oldstyle figure style
withOldstyle :: Numerals -> Numerals
withOldstyle (Numerals n) = Numerals n { figureStyle = StyleOldstyle }

-- | Set proportional spacing
withProportional :: Numerals -> Numerals
withProportional (Numerals n) = Numerals n { figureSpacing = SpacingProportional }

-- | Set tabular spacing
withTabular :: Numerals -> Numerals
withTabular (Numerals n) = Numerals n { figureSpacing = SpacingTabular }

-- | Enable slashed zero
withSlashedZero :: Numerals -> Numerals
withSlashedZero (Numerals n) = Numerals n { slashedZero = ZeroSlashed }

-- | Disable slashed zero
withoutSlashedZero :: Numerals -> Numerals
withoutSlashedZero (Numerals n) = Numerals n { slashedZero = ZeroNormal }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is lining style set?
isLining :: Numerals -> Boolean
isLining (Numerals { figureStyle: StyleLining }) = true
isLining _ = false

-- | Is oldstyle style set?
isOldstyle :: Numerals -> Boolean
isOldstyle (Numerals { figureStyle: StyleOldstyle }) = true
isOldstyle _ = false

-- | Is proportional spacing set?
isProportional :: Numerals -> Boolean
isProportional (Numerals { figureSpacing: SpacingProportional }) = true
isProportional _ = false

-- | Is tabular spacing set?
isTabular :: Numerals -> Boolean
isTabular (Numerals { figureSpacing: SpacingTabular }) = true
isTabular _ = false

-- | Is slashed zero enabled?
hasSlashedZero :: Numerals -> Boolean
hasSlashedZero (Numerals { slashedZero: ZeroSlashed }) = true
hasSlashedZero _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- NOT an FFI boundary — pure string generation.
-- | Convert to CSS font-variant-numeric value
toLegacyCss :: Numerals -> String
toLegacyCss (Numerals n) =
  let
    parts = styleToValue n.figureStyle <>
            spacingToValue n.figureSpacing <>
            zeroToValue n.slashedZero
  in case parts of
    [] -> "font-variant-numeric: normal;"
    _ -> "font-variant-numeric: " <> intercalate " " parts <> ";"
  where
  styleToValue :: FigureStyle -> Array String
  styleToValue StyleDefault = []
  styleToValue StyleLining = ["lining-nums"]
  styleToValue StyleOldstyle = ["oldstyle-nums"]

  spacingToValue :: FigureSpacing -> Array String
  spacingToValue SpacingDefault = []
  spacingToValue SpacingProportional = ["proportional-nums"]
  spacingToValue SpacingTabular = ["tabular-nums"]

  zeroToValue :: SlashedZero -> Array String
  zeroToValue ZeroDefault = []
  zeroToValue ZeroSlashed = ["slashed-zero"]
  zeroToValue ZeroNormal = []

-- | Convert to font-feature-settings value
-- |
-- | More explicit control using OpenType feature tags.
toFontFeatureSettings :: Numerals -> String
toFontFeatureSettings (Numerals n) =
  "font-feature-settings: " <>
  intercalate ", " (styleFeatures <> spacingFeatures <> zeroFeatures) <> ";"
  where
  styleFeatures :: Array String
  styleFeatures = case n.figureStyle of
    StyleDefault -> []
    StyleLining -> ["\"lnum\" 1"]
    StyleOldstyle -> ["\"onum\" 1"]

  spacingFeatures :: Array String
  spacingFeatures = case n.figureSpacing of
    SpacingDefault -> []
    SpacingProportional -> ["\"pnum\" 1"]
    SpacingTabular -> ["\"tnum\" 1"]

  zeroFeatures :: Array String
  zeroFeatures = case n.slashedZero of
    ZeroDefault -> []
    ZeroSlashed -> ["\"zero\" 1"]
    ZeroNormal -> ["\"zero\" 0"]
