-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // typography // text-decoration
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TextDecoration - typographic line decorations.
-- |
-- | Complete control over text decoration lines:
-- | - **Line**: underline, overline, line-through (strikethrough)
-- | - **Style**: solid, double, dotted, dashed, wavy
-- | - **Color**: independent of text color
-- | - **Thickness**: stroke width
-- | - **Offset**: distance from text baseline
-- |
-- | ## Accessibility considerations
-- |
-- | Underlines are the web's standard affordance for links. Using underlines
-- | for non-link text can confuse users. Consider:
-- | - Using underlines only for links
-- | - Using other decorations (line-through) for strikethrough
-- | - Using wavy underlines for spelling/grammar errors
-- |
-- | ## CSS Mapping
-- |
-- | Maps to `text-decoration`, `text-decoration-line`, `text-decoration-style`,
-- | `text-decoration-color`, `text-decoration-thickness`, `text-underline-offset`.

module Hydrogen.Schema.Typography.TextDecoration
  ( -- * Atoms
    DecorationLine(..)
  , DecorationStyle(..)
  , DecorationThickness(..)
  , UnderlineOffset(..)
  
  -- * Compound
  , TextDecoration(..)
  
  -- * Constructors
  , none
  , underline
  , overline
  , lineThrough
  , underlineWavy
  , underlineDouble
  , underlineDotted
  , underlineDashed
  , custom
  
  -- * Modifiers
  , withStyle
  , withThickness
  , withOffset
  , withColor
  
  -- * Predicates
  , hasUnderline
  , hasOverline
  , hasLineThrough
  , isVisible
  
  -- * CSS Output
  , toLegacyCss
  , toShorthand
  ) where

import Prelude

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // decoration line
-- ═════════════════════════════════════════════════════════════════════════════

-- | Which lines to draw
-- |
-- | Multiple lines can be combined (underline + overline).
data DecorationLine
  = LineNone        -- ^ No decoration
  | Underline       -- ^ Line below text
  | Overline        -- ^ Line above text
  | LineThrough     -- ^ Line through middle (strikethrough)
  | UnderlineOverline  -- ^ Both underline and overline

derive instance eqDecorationLine :: Eq DecorationLine
derive instance ordDecorationLine :: Ord DecorationLine

instance showDecorationLine :: Show DecorationLine where
  show LineNone = "LineNone"
  show Underline = "Underline"
  show Overline = "Overline"
  show LineThrough = "LineThrough"
  show UnderlineOverline = "UnderlineOverline"

-- | Convert line to CSS value
lineToLegacyCss :: DecorationLine -> String
lineToLegacyCss LineNone = "none"
lineToLegacyCss Underline = "underline"
lineToLegacyCss Overline = "overline"
lineToLegacyCss LineThrough = "line-through"
lineToLegacyCss UnderlineOverline = "underline overline"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // decoration style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Line style
-- |
-- | How the decoration line is rendered.
data DecorationStyle
  = StyleSolid    -- ^ Continuous line (default)
  | StyleDouble   -- ^ Two parallel lines
  | StyleDotted   -- ^ Series of dots
  | StyleDashed   -- ^ Series of dashes
  | StyleWavy     -- ^ Wavy/squiggly line (commonly used for errors)

derive instance eqDecorationStyle :: Eq DecorationStyle
derive instance ordDecorationStyle :: Ord DecorationStyle

instance showDecorationStyle :: Show DecorationStyle where
  show StyleSolid = "StyleSolid"
  show StyleDouble = "StyleDouble"
  show StyleDotted = "StyleDotted"
  show StyleDashed = "StyleDashed"
  show StyleWavy = "StyleWavy"

-- | Convert style to CSS value
styleToLegacyCss :: DecorationStyle -> String
styleToLegacyCss StyleSolid = "solid"
styleToLegacyCss StyleDouble = "double"
styleToLegacyCss StyleDotted = "dotted"
styleToLegacyCss StyleDashed = "dashed"
styleToLegacyCss StyleWavy = "wavy"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // decoration thickness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Line thickness
-- |
-- | Controls the stroke width of the decoration line.
data DecorationThickness
  = ThicknessAuto       -- ^ Browser default (typically 1px or font-based)
  | ThicknessFromFont   -- ^ Use font's preferred underline thickness
  | ThicknessPixels Number  -- ^ Explicit pixel value (0+)
  | ThicknessEm Number      -- ^ Relative to font size (0+)
  | ThicknessPercent Number -- ^ Percentage of font size (0+)

derive instance eqDecorationThickness :: Eq DecorationThickness
derive instance ordDecorationThickness :: Ord DecorationThickness

instance showDecorationThickness :: Show DecorationThickness where
  show ThicknessAuto = "ThicknessAuto"
  show ThicknessFromFont = "ThicknessFromFont"
  show (ThicknessPixels n) = "ThicknessPixels " <> show n
  show (ThicknessEm n) = "ThicknessEm " <> show n
  show (ThicknessPercent n) = "ThicknessPercent " <> show n

-- | Convert thickness to CSS value
thicknessToLegacyCss :: DecorationThickness -> String
thicknessToLegacyCss ThicknessAuto = "auto"
thicknessToLegacyCss ThicknessFromFont = "from-font"
thicknessToLegacyCss (ThicknessPixels n) = show n <> "px"
thicknessToLegacyCss (ThicknessEm n) = show n <> "em"
thicknessToLegacyCss (ThicknessPercent n) = show n <> "%"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // underline offset
-- ═════════════════════════════════════════════════════════════════════════════

-- | Distance between text and underline
-- |
-- | Positive values move the underline down (further from text),
-- | negative values move it up (into descenders).
data UnderlineOffset
  = OffsetAuto         -- ^ Browser default
  | OffsetPixels Number    -- ^ Explicit pixels (can be negative)
  | OffsetEm Number        -- ^ Relative to font size (can be negative)
  | OffsetPercent Number   -- ^ Percentage (can be negative)

derive instance eqUnderlineOffset :: Eq UnderlineOffset
derive instance ordUnderlineOffset :: Ord UnderlineOffset

instance showUnderlineOffset :: Show UnderlineOffset where
  show OffsetAuto = "OffsetAuto"
  show (OffsetPixels n) = "OffsetPixels " <> show n
  show (OffsetEm n) = "OffsetEm " <> show n
  show (OffsetPercent n) = "OffsetPercent " <> show n

-- | Convert offset to CSS value
offsetToLegacyCss :: UnderlineOffset -> String
offsetToLegacyCss OffsetAuto = "auto"
offsetToLegacyCss (OffsetPixels n) = show n <> "px"
offsetToLegacyCss (OffsetEm n) = show n <> "em"
offsetToLegacyCss (OffsetPercent n) = show n <> "%"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // text decoration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete text decoration specification
-- |
-- | Combines all decoration properties into a single compound.
newtype TextDecoration = TextDecoration
  { line :: DecorationLine
  , style :: DecorationStyle
  , thickness :: DecorationThickness
  , offset :: UnderlineOffset
  , color :: Maybe String  -- CSS color string (or Nothing for currentColor)
  }

derive instance eqTextDecoration :: Eq TextDecoration

instance showTextDecoration :: Show TextDecoration where
  show (TextDecoration td) = 
    "TextDecoration { line: " <> show td.line <>
    ", style: " <> show td.style <>
    ", thickness: " <> show td.thickness <>
    ", offset: " <> show td.offset <>
    ", color: " <> show td.color <> " }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | No decoration
none :: TextDecoration
none = TextDecoration
  { line: LineNone
  , style: StyleSolid
  , thickness: ThicknessAuto
  , offset: OffsetAuto
  , color: Nothing
  }

-- | Simple underline (solid, auto thickness)
underline :: TextDecoration
underline = TextDecoration
  { line: Underline
  , style: StyleSolid
  , thickness: ThicknessAuto
  , offset: OffsetAuto
  , color: Nothing
  }

-- | Simple overline (solid, auto thickness)
overline :: TextDecoration
overline = TextDecoration
  { line: Overline
  , style: StyleSolid
  , thickness: ThicknessAuto
  , offset: OffsetAuto
  , color: Nothing
  }

-- | Simple strikethrough (solid, auto thickness)
lineThrough :: TextDecoration
lineThrough = TextDecoration
  { line: LineThrough
  , style: StyleSolid
  , thickness: ThicknessAuto
  , offset: OffsetAuto
  , color: Nothing
  }

-- | Wavy underline (commonly used for spelling/grammar errors)
underlineWavy :: TextDecoration
underlineWavy = TextDecoration
  { line: Underline
  , style: StyleWavy
  , thickness: ThicknessAuto
  , offset: OffsetAuto
  , color: Nothing
  }

-- | Double underline (commonly used for accounting totals)
underlineDouble :: TextDecoration
underlineDouble = TextDecoration
  { line: Underline
  , style: StyleDouble
  , thickness: ThicknessAuto
  , offset: OffsetAuto
  , color: Nothing
  }

-- | Dotted underline
underlineDotted :: TextDecoration
underlineDotted = TextDecoration
  { line: Underline
  , style: StyleDotted
  , thickness: ThicknessAuto
  , offset: OffsetAuto
  , color: Nothing
  }

-- | Dashed underline
underlineDashed :: TextDecoration
underlineDashed = TextDecoration
  { line: Underline
  , style: StyleDashed
  , thickness: ThicknessAuto
  , offset: OffsetAuto
  , color: Nothing
  }

-- | Custom decoration with all parameters
custom 
  :: DecorationLine 
  -> DecorationStyle 
  -> DecorationThickness 
  -> UnderlineOffset 
  -> Maybe String 
  -> TextDecoration
custom l s t o c = TextDecoration
  { line: l
  , style: s
  , thickness: t
  , offset: o
  , color: c
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Change the decoration style
withStyle :: DecorationStyle -> TextDecoration -> TextDecoration
withStyle s (TextDecoration td) = TextDecoration td { style = s }

-- | Change the decoration thickness
withThickness :: DecorationThickness -> TextDecoration -> TextDecoration
withThickness t (TextDecoration td) = TextDecoration td { thickness = t }

-- | Change the underline offset
withOffset :: UnderlineOffset -> TextDecoration -> TextDecoration
withOffset o (TextDecoration td) = TextDecoration td { offset = o }

-- | Change the decoration color
withColor :: String -> TextDecoration -> TextDecoration
withColor c (TextDecoration td) = TextDecoration td { color = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Does this decoration include an underline?
hasUnderline :: TextDecoration -> Boolean
hasUnderline (TextDecoration { line: Underline }) = true
hasUnderline (TextDecoration { line: UnderlineOverline }) = true
hasUnderline _ = false

-- | Does this decoration include an overline?
hasOverline :: TextDecoration -> Boolean
hasOverline (TextDecoration { line: Overline }) = true
hasOverline (TextDecoration { line: UnderlineOverline }) = true
hasOverline _ = false

-- | Does this decoration include a line-through?
hasLineThrough :: TextDecoration -> Boolean
hasLineThrough (TextDecoration { line: LineThrough }) = true
hasLineThrough _ = false

-- | Is this decoration visible (not none)?
isVisible :: TextDecoration -> Boolean
isVisible (TextDecoration { line: LineNone }) = false
isVisible _ = true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- NOT an FFI boundary — pure string generation.
-- | Convert to full CSS declarations
toLegacyCss :: TextDecoration -> String
toLegacyCss (TextDecoration td) = case td.line of
  LineNone -> "text-decoration: none;"
  _ ->
    "text-decoration-line: " <> lineToLegacyCss td.line <> ";\n" <>
    "text-decoration-style: " <> styleToLegacyCss td.style <> ";\n" <>
    "text-decoration-thickness: " <> thicknessToLegacyCss td.thickness <> ";\n" <>
    "text-underline-offset: " <> offsetToLegacyCss td.offset <> ";" <>
    case td.color of
      Nothing -> ""
      Just c -> "\ntext-decoration-color: " <> c <> ";"

-- | Convert to text-decoration shorthand
-- |
-- | Returns the shorthand form: `text-decoration: line style color;`
-- | Note: thickness and offset require separate properties.
toShorthand :: TextDecoration -> String
toShorthand (TextDecoration td) = case td.line of
  LineNone -> "text-decoration: none;"
  _ ->
    "text-decoration: " <> 
    lineToLegacyCss td.line <> " " <>
    styleToLegacyCss td.style <>
    case td.color of
      Nothing -> ";"
      Just c -> " " <> c <> ";"
