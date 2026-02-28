-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // typography // type-style
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TypeStyle - a complete typographic specification.
-- |
-- | A molecule combining typography atoms into a usable style:
-- | - FontFamily (or FontStack for fallbacks)
-- | - FontWeight
-- | - FontSize
-- | - LineHeight
-- | - LetterSpacing
-- | - TextTransform
-- |
-- | TypeStyles are the building blocks of a TypeHierarchy. Each semantic
-- | level (H1, H2, body, etc.) maps to a TypeStyle.
-- |
-- | Example from Sentience brand guide:
-- | - HL-H3: Archivo ExtraBold, UPPERCASE, tracking 25, line-height 1.3
-- | - Body: Poppins Regular, Normal case, tracking 40, line-height 1.6

module Hydrogen.Schema.Typography.TypeStyle
  ( TypeStyle
  , FontStack
  , typeStyle
  , typeStyleWithStack
  , fontStack
  , singleFont
  -- Accessors
  , family
  , families
  , weight
  , size
  , lineHeight
  , letterSpacing
  , transform
  -- Modifiers
  , withFamily
  , withWeight
  , withSize
  , withLineHeight
  , withLetterSpacing
  , withTransform
  , scale
  -- CSS
  , toLegacyCss
  , toInlineStyle
  ) where

import Prelude

import Data.Array (intercalate)
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Hydrogen.Schema.Typography.FontFamily (FontFamily)
import Hydrogen.Schema.Typography.FontFamily as FontFamily
import Hydrogen.Schema.Typography.FontSize (FontSize)
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight (FontWeight)
import Hydrogen.Schema.Typography.FontWeight as FontWeight
import Hydrogen.Schema.Typography.LetterSpacing (LetterSpacing)
import Hydrogen.Schema.Typography.LetterSpacing as LetterSpacing
import Hydrogen.Schema.Typography.LineHeight (LineHeight)
import Hydrogen.Schema.Typography.LineHeight as LineHeight
import Hydrogen.Schema.Typography.TextTransform (TextTransform)
import Hydrogen.Schema.Typography.TextTransform as TextTransform

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // font stack
-- ═════════════════════════════════════════════════════════════════════════════

-- | Font stack — ordered list of font families for fallback
-- |
-- | The first font is preferred; subsequent fonts are used if unavailable.
-- | Must have at least one font (NonEmptyArray).
-- |
-- | Example: ["Archivo", "Helvetica Neue", "sans-serif"]
newtype FontStack = FontStack (NonEmptyArray FontFamily)

derive instance eqFontStack :: Eq FontStack

instance showFontStack :: Show FontStack where
  show (FontStack fs) = "FontStack " <> show (NEA.toArray fs)

-- | Create a font stack from a non-empty array
fontStack :: NonEmptyArray FontFamily -> FontStack
fontStack = FontStack

-- | Create a font stack with a single font
singleFont :: FontFamily -> FontStack
singleFont f = FontStack (NEA.singleton f)

-- | Get all fonts in the stack
stackFamilies :: FontStack -> NonEmptyArray FontFamily
stackFamilies (FontStack fs) = fs

-- | Get the primary (first) font in the stack
primaryFont :: FontStack -> FontFamily
primaryFont (FontStack fs) = NEA.head fs

-- | Convert font stack to CSS font-family value
fontStackToLegacyCss :: FontStack -> String
fontStackToLegacyCss (FontStack fs) = 
  intercalate ", " (map FontFamily.toLegacyCss (NEA.toArray fs))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // type style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete typographic style specification
-- |
-- | Combines all typography atoms into a cohesive style that can be
-- | applied to text elements.
newtype TypeStyle = TypeStyle
  { families :: FontStack
  , weight :: FontWeight
  , size :: FontSize
  , lineHeight :: LineHeight
  , letterSpacing :: LetterSpacing
  , transform :: TextTransform
  }

derive instance eqTypeStyle :: Eq TypeStyle

instance showTypeStyle :: Show TypeStyle where
  show (TypeStyle ts) = "TypeStyle { " 
    <> "families: " <> show ts.families
    <> ", weight: " <> show ts.weight
    <> ", size: " <> show ts.size
    <> ", lineHeight: " <> show ts.lineHeight
    <> ", letterSpacing: " <> show ts.letterSpacing
    <> ", transform: " <> show ts.transform
    <> " }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a type style with a single font family
typeStyle 
  :: FontFamily 
  -> FontWeight 
  -> FontSize 
  -> LineHeight 
  -> LetterSpacing 
  -> TextTransform 
  -> TypeStyle
typeStyle fam w s lh ls tt = TypeStyle
  { families: singleFont fam
  , weight: w
  , size: s
  , lineHeight: lh
  , letterSpacing: ls
  , transform: tt
  }

-- | Create a type style with a font stack
typeStyleWithStack
  :: FontStack
  -> FontWeight
  -> FontSize
  -> LineHeight
  -> LetterSpacing
  -> TextTransform
  -> TypeStyle
typeStyleWithStack fs w s lh ls tt = TypeStyle
  { families: fs
  , weight: w
  , size: s
  , lineHeight: lh
  , letterSpacing: ls
  , transform: tt
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the primary font family
family :: TypeStyle -> FontFamily
family (TypeStyle ts) = primaryFont ts.families

-- | Get all font families in the stack
families :: TypeStyle -> NonEmptyArray FontFamily
families (TypeStyle ts) = stackFamilies ts.families

-- | Get the font weight
weight :: TypeStyle -> FontWeight
weight (TypeStyle ts) = ts.weight

-- | Get the font size
size :: TypeStyle -> FontSize
size (TypeStyle ts) = ts.size

-- | Get the line height
lineHeight :: TypeStyle -> LineHeight
lineHeight (TypeStyle ts) = ts.lineHeight

-- | Get the letter spacing
letterSpacing :: TypeStyle -> LetterSpacing
letterSpacing (TypeStyle ts) = ts.letterSpacing

-- | Get the text transform
transform :: TypeStyle -> TextTransform
transform (TypeStyle ts) = ts.transform

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Replace the font family (keeps existing fallbacks)
withFamily :: FontFamily -> TypeStyle -> TypeStyle
withFamily f (TypeStyle ts) = TypeStyle ts { families = singleFont f }

-- | Replace the font weight
withWeight :: FontWeight -> TypeStyle -> TypeStyle
withWeight w (TypeStyle ts) = TypeStyle ts { weight = w }

-- | Replace the font size
withSize :: FontSize -> TypeStyle -> TypeStyle
withSize s (TypeStyle ts) = TypeStyle ts { size = s }

-- | Replace the line height
withLineHeight :: LineHeight -> TypeStyle -> TypeStyle
withLineHeight lh (TypeStyle ts) = TypeStyle ts { lineHeight = lh }

-- | Replace the letter spacing
withLetterSpacing :: LetterSpacing -> TypeStyle -> TypeStyle
withLetterSpacing ls (TypeStyle ts) = TypeStyle ts { letterSpacing = ls }

-- | Replace the text transform
withTransform :: TextTransform -> TypeStyle -> TypeStyle
withTransform tt (TypeStyle ts) = TypeStyle ts { transform = tt }

-- | Scale the font size by a factor
-- |
-- | Used for type scale calculations. Other properties remain unchanged.
scale :: Number -> TypeStyle -> TypeStyle
scale factor (TypeStyle ts) = TypeStyle ts { size = FontSize.scale factor ts.size }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- NOT an FFI boundary - pure string generation.
-- | Convert to CSS declarations (for stylesheet)
toLegacyCss :: TypeStyle -> String
toLegacyCss (TypeStyle ts) = 
  "font-family: " <> fontStackToLegacyCss ts.families <> ";\n" <>
  "font-weight: " <> FontWeight.toLegacyCss ts.weight <> ";\n" <>
  "font-size: " <> FontSize.toLegacyCss ts.size <> ";\n" <>
  "line-height: " <> LineHeight.toLegacyCss ts.lineHeight <> ";\n" <>
  "letter-spacing: " <> LetterSpacing.toLegacyCss ts.letterSpacing <> ";\n" <>
  "text-transform: " <> TextTransform.toLegacyCss ts.transform <> ";"

-- | Convert to inline style attribute value
toInlineStyle :: TypeStyle -> String
toInlineStyle (TypeStyle ts) = 
  "font-family: " <> fontStackToLegacyCss ts.families <> "; " <>
  "font-weight: " <> FontWeight.toLegacyCss ts.weight <> "; " <>
  "font-size: " <> FontSize.toLegacyCss ts.size <> "; " <>
  "line-height: " <> LineHeight.toLegacyCss ts.lineHeight <> "; " <>
  "letter-spacing: " <> LetterSpacing.toLegacyCss ts.letterSpacing <> "; " <>
  "text-transform: " <> TextTransform.toLegacyCss ts.transform <> ";"
