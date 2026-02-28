-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // style // typography
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Typography system
-- |
-- | Type-safe font sizes, weights, line heights, and text utilities.
-- | All values map to Tailwind CSS classes.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Style.Typography as Type
-- |
-- | -- Font sizes
-- | Type.fontSize Type.TextLg    -- "text-lg"
-- | Type.fontSize Type.Text2xl   -- "text-2xl"
-- |
-- | -- Font weights
-- | Type.fontWeight Type.Bold    -- "font-bold"
-- |
-- | -- Combined
-- | Type.textStyle Type.TextLg Type.Semibold Type.LeadingNormal
-- | -- "text-lg font-semibold leading-normal"
-- | ```
module Hydrogen.Style.Typography
  ( -- * Font Size
    FontSize(..)
  , fontSize
    -- * Font Weight
  , FontWeight(..)
  , fontWeight
    -- * Line Height
  , LineHeight(..)
  , lineHeight
    -- * Letter Spacing
  , LetterSpacing(..)
  , letterSpacing
    -- * Font Family
  , FontFamily(..)
  , fontFamily
    -- * Text Alignment
  , TextAlign(..)
  , textAlign
    -- * Text Transform
  , TextTransform(..)
  , textTransform
    -- * Text Decoration
  , TextDecoration(..)
  , textDecoration
    -- * Text Overflow
  , TextOverflow(..)
  , textOverflow
    -- * Whitespace
  , Whitespace(..)
  , whitespace
    -- * Word Break
  , WordBreak(..)
  , wordBreak
    -- * Combined Utilities
  , textStyle
  , heading
  , body
  , caption
  , prose
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // font size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Font size scale (maps to Tailwind text-* classes)
data FontSize
  = TextXs      -- 12px
  | TextSm      -- 14px
  | TextBase    -- 16px
  | TextLg      -- 18px
  | TextXl      -- 20px
  | Text2xl     -- 24px
  | Text3xl     -- 30px
  | Text4xl     -- 36px
  | Text5xl     -- 48px
  | Text6xl     -- 60px
  | Text7xl     -- 72px
  | Text8xl     -- 96px
  | Text9xl     -- 128px

derive instance eqFontSize :: Eq FontSize
derive instance ordFontSize :: Ord FontSize

-- | Convert font size to Tailwind class
fontSize :: FontSize -> String
fontSize = case _ of
  TextXs -> "text-xs"
  TextSm -> "text-sm"
  TextBase -> "text-base"
  TextLg -> "text-lg"
  TextXl -> "text-xl"
  Text2xl -> "text-2xl"
  Text3xl -> "text-3xl"
  Text4xl -> "text-4xl"
  Text5xl -> "text-5xl"
  Text6xl -> "text-6xl"
  Text7xl -> "text-7xl"
  Text8xl -> "text-8xl"
  Text9xl -> "text-9xl"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // font weight
-- ═════════════════════════════════════════════════════════════════════════════

-- | Font weight scale
data FontWeight
  = Thin        -- 100
  | Extralight  -- 200
  | Light       -- 300
  | Normal      -- 400
  | Medium      -- 500
  | Semibold    -- 600
  | Bold        -- 700
  | Extrabold   -- 800
  | Black       -- 900

derive instance eqFontWeight :: Eq FontWeight
derive instance ordFontWeight :: Ord FontWeight

-- | Convert font weight to Tailwind class
fontWeight :: FontWeight -> String
fontWeight = case _ of
  Thin -> "font-thin"
  Extralight -> "font-extralight"
  Light -> "font-light"
  Normal -> "font-normal"
  Medium -> "font-medium"
  Semibold -> "font-semibold"
  Bold -> "font-bold"
  Extrabold -> "font-extrabold"
  Black -> "font-black"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // line height
-- ═════════════════════════════════════════════════════════════════════════════

-- | Line height scale
data LineHeight
  = LeadingNone     -- 1
  | LeadingTight    -- 1.25
  | LeadingSnug     -- 1.375
  | LeadingNormal   -- 1.5
  | LeadingRelaxed  -- 1.625
  | LeadingLoose    -- 2
  | Leading3        -- 0.75rem
  | Leading4        -- 1rem
  | Leading5        -- 1.25rem
  | Leading6        -- 1.5rem
  | Leading7        -- 1.75rem
  | Leading8        -- 2rem
  | Leading9        -- 2.25rem
  | Leading10       -- 2.5rem

derive instance eqLineHeight :: Eq LineHeight
derive instance ordLineHeight :: Ord LineHeight

-- | Convert line height to Tailwind class
lineHeight :: LineHeight -> String
lineHeight = case _ of
  LeadingNone -> "leading-none"
  LeadingTight -> "leading-tight"
  LeadingSnug -> "leading-snug"
  LeadingNormal -> "leading-normal"
  LeadingRelaxed -> "leading-relaxed"
  LeadingLoose -> "leading-loose"
  Leading3 -> "leading-3"
  Leading4 -> "leading-4"
  Leading5 -> "leading-5"
  Leading6 -> "leading-6"
  Leading7 -> "leading-7"
  Leading8 -> "leading-8"
  Leading9 -> "leading-9"
  Leading10 -> "leading-10"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // letter spacing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Letter spacing scale
data LetterSpacing
  = TrackingTighter  -- -0.05em
  | TrackingTight    -- -0.025em
  | TrackingNormal   -- 0
  | TrackingWide     -- 0.025em
  | TrackingWider    -- 0.05em
  | TrackingWidest   -- 0.1em

derive instance eqLetterSpacing :: Eq LetterSpacing
derive instance ordLetterSpacing :: Ord LetterSpacing

-- | Convert letter spacing to Tailwind class
letterSpacing :: LetterSpacing -> String
letterSpacing = case _ of
  TrackingTighter -> "tracking-tighter"
  TrackingTight -> "tracking-tight"
  TrackingNormal -> "tracking-normal"
  TrackingWide -> "tracking-wide"
  TrackingWider -> "tracking-wider"
  TrackingWidest -> "tracking-widest"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // font family
-- ═════════════════════════════════════════════════════════════════════════════

-- | Font family
data FontFamily
  = FontSans
  | FontSerif
  | FontMono

derive instance eqFontFamily :: Eq FontFamily

-- | Convert font family to Tailwind class
fontFamily :: FontFamily -> String
fontFamily = case _ of
  FontSans -> "font-sans"
  FontSerif -> "font-serif"
  FontMono -> "font-mono"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // text alignment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Text alignment
data TextAlign
  = TextLeft
  | TextCenter
  | TextRight
  | TextJustify
  | TextStart
  | TextEnd

derive instance eqTextAlign :: Eq TextAlign

-- | Convert text alignment to Tailwind class
textAlign :: TextAlign -> String
textAlign = case _ of
  TextLeft -> "text-left"
  TextCenter -> "text-center"
  TextRight -> "text-right"
  TextJustify -> "text-justify"
  TextStart -> "text-start"
  TextEnd -> "text-end"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // text transform
-- ═════════════════════════════════════════════════════════════════════════════

-- | Text transform
data TextTransform
  = Uppercase
  | Lowercase
  | Capitalize
  | NormalCase

derive instance eqTextTransform :: Eq TextTransform

-- | Convert text transform to Tailwind class
textTransform :: TextTransform -> String
textTransform = case _ of
  Uppercase -> "uppercase"
  Lowercase -> "lowercase"
  Capitalize -> "capitalize"
  NormalCase -> "normal-case"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // text decoration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Text decoration
data TextDecoration
  = Underline
  | Overline
  | LineThrough
  | NoUnderline

derive instance eqTextDecoration :: Eq TextDecoration

-- | Convert text decoration to Tailwind class
textDecoration :: TextDecoration -> String
textDecoration = case _ of
  Underline -> "underline"
  Overline -> "overline"
  LineThrough -> "line-through"
  NoUnderline -> "no-underline"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // text overflow
-- ═════════════════════════════════════════════════════════════════════════════

-- | Text overflow handling
data TextOverflow
  = Truncate       -- Truncate with ellipsis
  | TextEllipsis   -- Just ellipsis
  | TextClip       -- Clip overflow

derive instance eqTextOverflow :: Eq TextOverflow

-- | Convert text overflow to Tailwind class
textOverflow :: TextOverflow -> String
textOverflow = case _ of
  Truncate -> "truncate"
  TextEllipsis -> "text-ellipsis"
  TextClip -> "text-clip"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // white-space
-- ═════════════════════════════════════════════════════════════════════════════

-- | Whitespace handling
data Whitespace
  = WhitespaceNormal
  | WhitespaceNowrap
  | WhitespacePre
  | WhitespacePreLine
  | WhitespacePreWrap
  | WhitespaceBreakSpaces

derive instance eqWhitespace :: Eq Whitespace

-- | Convert whitespace to Tailwind class
whitespace :: Whitespace -> String
whitespace = case _ of
  WhitespaceNormal -> "whitespace-normal"
  WhitespaceNowrap -> "whitespace-nowrap"
  WhitespacePre -> "whitespace-pre"
  WhitespacePreLine -> "whitespace-pre-line"
  WhitespacePreWrap -> "whitespace-pre-wrap"
  WhitespaceBreakSpaces -> "whitespace-break-spaces"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // word break
-- ═════════════════════════════════════════════════════════════════════════════

-- | Word break behavior
data WordBreak
  = BreakNormal
  | BreakWords
  | BreakAll
  | BreakKeep

derive instance eqWordBreak :: Eq WordBreak

-- | Convert word break to Tailwind class
wordBreak :: WordBreak -> String
wordBreak = case _ of
  BreakNormal -> "break-normal"
  BreakWords -> "break-words"
  BreakAll -> "break-all"
  BreakKeep -> "break-keep"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // combined utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combine text styles into a single class string
textStyle :: FontSize -> FontWeight -> LineHeight -> String
textStyle size weight leading =
  fontSize size <> " " <> fontWeight weight <> " " <> lineHeight leading

-- | Heading text style
-- |
-- | ```purescript
-- | heading 1  -- "text-4xl font-bold leading-tight tracking-tight"
-- | heading 2  -- "text-3xl font-semibold leading-tight tracking-tight"
-- | ```
heading :: Int -> String
heading level = case level of
  1 -> "text-4xl font-bold leading-tight tracking-tight"
  2 -> "text-3xl font-semibold leading-tight tracking-tight"
  3 -> "text-2xl font-semibold leading-snug"
  4 -> "text-xl font-semibold leading-snug"
  5 -> "text-lg font-medium leading-normal"
  6 -> "text-base font-medium leading-normal"
  _ -> "text-base font-medium leading-normal"

-- | Body text style
body :: String
body = "text-base font-normal leading-relaxed"

-- | Caption/small text style
caption :: String
caption = "text-sm font-normal leading-normal text-muted-foreground"

-- | Prose (long-form content) style
prose :: String
prose = "prose prose-neutral dark:prose-invert max-w-none"
